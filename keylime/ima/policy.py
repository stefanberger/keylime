#!/usr/bin/env python

from abc import ABC, abstractmethod
from enum import Enum
from typing import Callable, Dict, Iterable, List, Optional, Pattern, Tuple, Type, cast

from keylime import keylime_logging
from keylime.common import validators
from keylime.failure import Component, Failure
from keylime.ima import ast, file_signatures, ima_dm
from keylime.ima.file_signatures import ImaKeyrings
from keylime.ima.types import RuntimePolicyType

logger = keylime_logging.init_logging("ima-policy")


class EvalResult(Enum):
    ACCEPT = 1
    REJECT = 2
    SKIP = 3  # move to next rules


class PolicyException(Exception):
    pass


def kvps_to_dict(
    kvps: str, allowed_keys: List[str], required_keys: Optional[List[str]], rulename: str
) -> Dict[str, str]:
    """Convert key-value pairs to a Dict"""
    res: List[map] = []  # type: ignore
    for kvp in kvps.split(" "):
        kvp = kvp.strip()
        if "=" in kvp:
            key, _ = kvp.split("=", 1)
            if key not in allowed_keys:
                raise PolicyException(f"Unsupported parameter {key} for {rulename}")
            if required_keys is not None and key in required_keys:
                required_keys.remove(key)
            res.append(map(str.strip, kvp.split("=", 1)))
        else:
            if kvp:
                raise PolicyException(f"{kvp} is not a valid key=value pair")
    if required_keys:
        raise PolicyException(f"Missing required attribute for {rulename}: {', '.join(required_keys)}")
    return dict(cast(Iterable[tuple[str, str]], res))


class CompiledRegexList:
    """A list of regular expressions"""

    compiled_regexs: List[Tuple[Pattern[str], EvalResult]]

    def __init__(self, compiled_regexs: List[Tuple[Pattern[str], EvalResult]]):
        self.compiled_regexs = compiled_regexs

    def __len__(self) -> int:
        return len(self.compiled_regexs)

    @staticmethod
    def __compile_rules(regex_list: List[str], eval_result: str) -> Tuple[Pattern[str], EvalResult]:
        compiled_regex, err_msg = validators.valid_exclude_list(regex_list)
        if err_msg:
            raise PolicyException(err_msg)
        if not compiled_regex:
            raise PolicyException(f"Could not get a compiled regex from regex list '{regex_list}'")
        er = {
            "ACCEPT": EvalResult.ACCEPT,
            "REJECT": EvalResult.REJECT,
        }[eval_result]
        return (compiled_regex, er)

    @staticmethod
    def from_excludelist(exclude_list: Optional[List[str]]) -> "CompiledRegexList":
        """
        Create a CompilleRegexList from an exclude list where none of the
        list items has the prefix 'ACCEPT'
        """
        if exclude_list and len(exclude_list) > 0:
            return CompiledRegexList([CompiledRegexList.__compile_rules(exclude_list, "ACCEPT")])
        return CompiledRegexList([])

    @staticmethod
    def from_list(rule_list: List[str]) -> "CompiledRegexList":
        """
        Create a CompiledRegexList from a list where each regex must be prefixed
        with either ACCEPT: or REJECT:. For more efficient processing bunch
        consecutive ACCEPT or REJECT regexs.
        """
        eval_result = "ACCEPT"
        rules: List[str] = []
        comp_rules: List[Tuple[Pattern[str], EvalResult]] = []

        for rule in rule_list:
            elems = rule.split(":", 1)
            if len(elems) != 2 or elems[0] not in ["ACCEPT", "REJECT"]:
                raise PolicyException("List element must start with 'ACCEPT:' or 'REJECT:'")

            if elems[0] != eval_result:
                if rules:
                    comp_rules.append(CompiledRegexList.__compile_rules(rules, eval_result))

                eval_result = elems[0]
                rules = []

            rules.append(elems[1])

        if rules:
            comp_rules.append(CompiledRegexList.__compile_rules(rules, eval_result))

        return CompiledRegexList(comp_rules)

    def eval(self, pathname: str) -> EvalResult:
        for regex, eval_result in self.compiled_regexs:
            if regex.match(pathname):
                return eval_result
        return EvalResult.SKIP


class ABCPolicy(ABC):
    @abstractmethod
    def get_regex_list(self, listname: str) -> Optional[CompiledRegexList]:
        pass

    @abstractmethod
    def get_map(self, mapname: str) -> Optional[Dict[str, List[str]]]:
        pass

    @abstractmethod
    def get_runtime_policy(self) -> Optional[RuntimePolicyType]:
        pass


class ABCRule(ABC):
    @staticmethod
    @abstractmethod
    def from_string(rule: str) -> "ABCRule":
        pass

    @abstractmethod
    def setup(self, policy: ABCPolicy) -> None:
        pass


class Evaluator:
    functions: Dict[Type["ABCRule"], Callable[..., Tuple[EvalResult, Optional[Failure]]]]

    def __init__(self, functions: Dict[Type["ABCRule"], Callable[..., Tuple[EvalResult, Optional[Failure]]]]):
        self.functions = functions

    def get_evaluator(self, class_type: Type["ABCRule"]) -> Callable[..., Tuple[EvalResult, Optional[Failure]]]:
        evaluator = self.functions.get(class_type, None)
        if evaluator is None:
            logger.warning("No evaluator was implemented for: %s. Using always false evaluator!", class_type)
            failure = Failure(Component.IMA, ["validation"])
            failure.add_event(
                "no_evaluator", f"No evaluator was implemented for: {class_type} . Using always false evaluator!", True
            )
            return lambda *_: (EvalResult.SKIP, failure)
        return evaluator


class RegexList(ABCRule):
    """
    RegexList represents a 'REGEX-LIST: <listname>' rule. The listname refers to a list
    where each entry is a regex prefixed by eiter ACCEPT: or REJECT:
    """

    listname: str
    comp_regex_list: Optional[CompiledRegexList]

    def __init__(self, listname: str):
        self.listname = listname
        self.comp_regex_list = None

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        return RegexList(rule)

    def setup(self, policy: ABCPolicy) -> None:
        self.comp_regex_list = policy.get_regex_list(self.listname)

    def eval(self, path: ast.Name) -> EvalResult:
        if not self.comp_regex_list:
            return EvalResult.SKIP
        return self.comp_regex_list.eval(path.name)


def regexlist_eval(
    _digest: ast.Digest,
    path: ast.Name,
    _signature: Optional[ast.Signature],
    _data: Optional[ast.Buffer],
    regexlist: RegexList,
) -> Tuple[EvalResult, Optional[Failure]]:
    return regexlist.eval(path), None


class AcceptRejectMap(ABCRule):
    mapname: str
    defresult: EvalResult
    map: Optional[Dict[str, List[str]]]

    def __init__(self, mapname: str, defresult: EvalResult):
        self.mapname = mapname
        self.defresult = defresult
        self.map = {}

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        raise PolicyException("Must call child class method")

    def setup(self, policy: ABCPolicy) -> None:
        self.map = policy.get_map(self.mapname)

    def eval(self, digest: ast.Digest, path: ast.Name) -> EvalResult:
        if not self.map:
            return EvalResult.SKIP

        accept_list = self.map.get(path.name, None)
        if not accept_list:
            return EvalResult.SKIP

        hex_hash = digest.hash.hex()
        if hex_hash in accept_list:
            return self.defresult
        return EvalResult.SKIP


class RejectMap(AcceptRejectMap):
    """RejectMap represents a 'REJECT-MAP: <mapname>' rule"""

    def __init__(self, mapname: str):
        super().__init__(mapname, EvalResult.REJECT)

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        return RejectMap(rule)


class AcceptMap(AcceptRejectMap):
    """AcceptMap represents a 'ACCEPT-MAP: <mapname>' rule"""

    def __init__(self, mapname: str):
        super().__init__(mapname, EvalResult.ACCEPT)

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        return AcceptMap(rule)


def acceptreject_map_eval(
    digest: ast.Digest,
    path: ast.Name,
    _signature: Optional[ast.Signature],
    _data: Optional[ast.Buffer],
    armap: AcceptRejectMap,
) -> Tuple[EvalResult, Optional[Failure]]:
    return armap.eval(digest, path), None


class AcceptImaSig(ABCRule):
    """AcceptImaSig represents an ACCEPT-IMASIG rule"""

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        if len(rule) > 0:
            raise PolicyException("ACCEPT-IMASIG does not support any parameters")
        return AcceptImaSig()

    def setup(self, policy: ABCPolicy) -> None:
        pass

    def eval(
        self,
        ima_keyrings: Optional[file_signatures.ImaKeyrings],
        digest: ast.Digest,
        path: ast.Name,
        signature: Optional[ast.Signature],
    ) -> EvalResult:
        if ima_keyrings and signature:
            if ima_keyrings.integrity_digsig_verify(signature.data, digest.hash, digest.algorithm):
                logger.debug("signature for file %s is good", path)
                return EvalResult.ACCEPT

        return EvalResult.SKIP


def accept_ima_sig_eval(
    ima_keyrings: Optional[file_signatures.ImaKeyrings],
    _dm_validator: Optional[ima_dm.DmIMAValidator],
    digest: ast.Digest,
    path: ast.Name,
    signature: Optional[ast.Signature],
    _data: Optional[ast.Buffer],
    rule: AcceptImaSig,
) -> Tuple[EvalResult, Optional[Failure]]:
    return rule.eval(ima_keyrings, digest, path, signature), None


class LearnKeys(ABCRule):
    """LearnKeys represents a 'LEARN-KEYS [ignore-list=<ignore-list>] [allowed-hashes=<hashes-list>]' rule"""

    parameters: Dict[str, str]
    ignored_keyrings: List[str]
    allowed_hashes: Dict[str, List[str]]  # a key's hash must be in this dict (key = keyring name)

    def __init__(self, parameters: Dict[str, str]) -> None:
        self.parameters = parameters
        self.ignored_keyrings = []
        self.allowed_hashes = {}

    @staticmethod
    def from_string(rule: str) -> ABCRule:
        parameters = kvps_to_dict(rule, ["ignore-keyrings", "allowed-hashes"], None, "LEARN-KEYS")
        return LearnKeys(parameters)

    def setup(self, policy: ABCPolicy) -> None:
        runtime_policy = policy.get_runtime_policy()
        if runtime_policy:
            ignore_keyrings = self.parameters.get("ignore-keyrings")
            if ignore_keyrings:
                ik = runtime_policy.get("ima", {}).get(ignore_keyrings, [])
                if not isinstance(ik, list):
                    raise PolicyException("Referenced ignore-keyrings {ignore_list} is not a list")
                self.ignored_keyrings = ik

            allowed_hashes = self.parameters.get("allowed-hashes")
            if allowed_hashes:
                ah = runtime_policy.get(allowed_hashes, [])
                if not isinstance(ah, dict):
                    raise PolicyException("Referenced allowed-hashes {allowed_hashes} is not a dictionary")
                self.allowed_hashes = ah


def learn_keys_eval(
    ima_keyrings: Optional[file_signatures.ImaKeyrings],
    digest: ast.Digest,
    path: ast.Name,
    _signature: Optional[ast.Signature],
    data: Optional[ast.Buffer],
    rule: LearnKeys,
) -> Tuple[EvalResult, Failure]:
    failure = Failure(Component.IMA)

    if not data:
        return EvalResult.SKIP, failure

    # Is data.data a key?
    try:
        pubkey, keyidv2 = file_signatures.get_pubkey(data.data)
    except ValueError as ve:
        failure.add_event("invalid_key", f"key from {path.name} does not have a supported key: {ve}", True)
        return EvalResult.SKIP, failure

    if pubkey:
        if "*" not in rule.ignored_keyrings and path.name not in rule.ignored_keyrings:
            accept_list = rule.allowed_hashes.get(path.name, None)
            if not accept_list:
                allowed_hashes = rule.parameters.get("allowed-hashes", "<allowed-hashes not given in rule>")
                failure.add_event("not_in_allowlist", f"Keyring not found in {allowed_hashes}: {path.name}", True)
                return EvalResult.REJECT, failure
            hex_hash = digest.hash.hex()
            if hex_hash not in accept_list:
                failure.add_event(
                    "runtime_policy_hash",
                    {
                        "message": "Hash for key not found in runtime policy",
                        "got": hex_hash,
                        "expected": accept_list,
                    },
                    True,
                )
                return EvalResult.REJECT, failure
            if ima_keyrings is not None:
                ima_keyrings.add_pubkey_to_keyring(pubkey, path.name, keyidv2=keyidv2)

    return EvalResult.SKIP, failure


class Policy(ABCPolicy):
    MAPPINGS: Dict[str, Type[ABCRule]] = {
        "ACCEPT-IMASIG": AcceptImaSig,
        "ACCEPT-MAP": AcceptMap,
        "LEARN-KEYS": LearnKeys,
        "REGEX-LIST": RegexList,
        "REJECT-MAP": RejectMap,
    }
    DEFAULT_POLICY_STR: str = (
        "LEARN-KEYS: ignore-keyrings=ignored_keyrings allowed-hashes=keyrings\n"
        "REGEX-LIST: exclude-list\n"
        "REJECT-MAP: reject-list\n"
        "ACCEPT-IMASIG\n"
        "ACCEPT-MAP: allow-list\n"
        "REGEX-LIST: filter-list"
    )

    rules: List[ABCRule]
    runtime_policy: Optional[RuntimePolicyType]
    regex_list: Dict[str, CompiledRegexList]

    def __init__(self, rules: List[ABCRule], runtime_policy: Optional[RuntimePolicyType]):
        self.rules = rules
        self.runtime_policy = runtime_policy
        self.regex_list = {}
        self.__setup_rules()

    def __setup_rules(self) -> None:
        """Call setup on all rules to detect errors early on"""
        for rule in self.rules:
            rule.setup(self)

    @staticmethod
    def from_string(policy: str, runtime_policy: Optional[RuntimePolicyType]) -> "Policy":
        rules: List[ABCRule] = []

        for rule in policy.split("\n"):
            rule = rule.strip()
            if not rule or rule.startswith("#"):
                continue

            r = rule.split(":")

            rule_type = r[0]
            rule_params = ""

            if len(r) > 1:
                _, rule_params = rule.split(":", 1)
                rule_params = rule_params.strip()

            c = Policy.MAPPINGS.get(rule_type)
            if not c:
                raise PolicyException(f"Policy does not support '{rule_type}' rule")
            rules.append(c.from_string(rule_params))
        return Policy(rules, runtime_policy)

    @staticmethod
    def from_runtime_policy(runtime_policy: Optional[RuntimePolicyType]) -> "Policy":
        # Currently RuntimePolicyType does not carry a policy with rules
        # so use the default built-in policy
        return Policy.from_string(Policy.DEFAULT_POLICY_STR, runtime_policy)

    def eval(
        self,
        evaluator: Evaluator,
        digest: ast.Digest,
        path: ast.Name,
        signature: Optional[ast.Signature],
        data: Optional[ast.Buffer],
        ima_keyrings: Optional[ImaKeyrings],
    ) -> Failure:
        """Evaluate the policy against an IMA log entry"""
        failure = Failure(Component.IMA, ["ima-policy"])

        for rule in self.rules:
            res, rule_failure = evaluator.get_evaluator(type(rule))(digest, path, signature, data, rule)
            if rule_failure:
                failure.merge(rule_failure)

            if res in [EvalResult.ACCEPT, EvalResult.REJECT]:
                return failure

        # None of the rules ACCEPT'ed or REJECT'ed the log entry, so if either
        # a runtime_policy or ima_keyrings is given leave an error message.
        # Without both the log entry would 'pass'.
        if self.runtime_policy:
            failure.add_event("not_in_policy", f"File not accepted by policy: {path.name}", True)
        if ima_keyrings:
            failure.add_event("invalid_signature", f"signature for file {path.name} could not be validated", True)

        return failure

    def get_regex_list(self, listname: str) -> Optional[CompiledRegexList]:
        """Get a regex list from the runtimepolicy using its implicit name"""
        if not self.regex_list.get(listname):
            regexlist = []
            if listname == "exclude-list":
                if self.runtime_policy:
                    regexlist = self.runtime_policy.get("excludes", [])
                self.regex_list[listname] = CompiledRegexList.from_excludelist(regexlist)
            elif listname == "filter-list":
                if self.runtime_policy:
                    regexlist = self.runtime_policy.get("filters", [])
                self.regex_list[listname] = CompiledRegexList.from_list(regexlist)
            else:
                raise PolicyException(f"A regex list with name {listname} is not available")
        return self.regex_list.get(listname)

    def get_map(self, mapname: str) -> Optional[Dict[str, List[str]]]:
        if mapname == "allow-list":
            if not self.runtime_policy:
                return {}
            return self.runtime_policy.get("digests", {})
        if mapname == "reject-list":
            if not self.runtime_policy:
                return {}
            return self.runtime_policy.get("rejects", {})
        raise PolicyException(f"A map with name {mapname} is not available")

    def get_runtime_policy(self) -> Optional[RuntimePolicyType]:
        return self.runtime_policy
