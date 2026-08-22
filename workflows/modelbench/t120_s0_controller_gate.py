"""Fixed controller-owned T120 S0 schema/statistic validation gate.

The gate binds frozen specifications, audits one pure candidate module, and
runs controller-owned mutations in a networkless read-only container.  It has
no BBP generator, production arithmetic route, launch path, CAS write, receipt
mint, or mathematical-result authority.
"""

from __future__ import annotations

import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import tempfile
from typing import Any

from workflows.modelbench import t120_s0_controller_oracle as oracle


GATE_ID = oracle.GATE_ID
ROOT = Path(__file__).resolve().parents[2]
PARENT_DIR = (
    ROOT
    / "workflows"
    / "modelbench"
    / "tasks"
    / "pi"
    / "planned"
    / "t120-q10-exact-diagnostic"
)
STAGE_DIR = PARENT_DIR / "stages" / "s0-controller-gate"
TASK_CONTRACT = STAGE_DIR / "TASK_CONTRACT.json"
CONTROLLER_TESTS = STAGE_DIR / "CONTROLLER_TESTS.json"
AGENT_GUIDANCE = STAGE_DIR / "AGENT_GUIDANCE.md"
HARNESS_PATH = Path(__file__).with_name("t120_s0_controller_harness.py")
ORACLE_PATH = Path(oracle.__file__)

PARENT_RAW_SHA256 = {
    "CONTRACT.json": "5e6ac96f7c3c8a003ffbfbf1b65e582b5583700a68c597968d903e70075ce327",
    "INTERFACE.md": "cd1eb2d91c02e866c9f0bf27e2aadeaa4f9c8e1774ccc4d6dfd1a4114f7d8fde",
    "TEST_PLAN.md": "ab7f0e1261d472a82789731b9db34ced32afea74f36d188e5b06308357f344ea",
}
CHILD_RAW_SHA256 = {
    "AGENT_GUIDANCE.md": "02017a5545c0b780e1516b163a09280a11fa8b8883b18313378cf3326c7f921b",
    "CONTROLLER_TESTS.json": "addb579617d7d7dcbf7c5bf08da5fefacb5aa397260ab57151280115ede28106",
}
SPEC_BUNDLE_SHA256 = oracle.SPEC_BUNDLE_SHA256
TASK_CONTRACT_SEMANTIC_SHA256 = "28596b02651feaac080246da855b6cc299b4b66a0f5ac9145413ccc7670c6a68"
SOURCE_FILE = "t120_s0_schema.py"
REPORT_FILE = "REPORT.md"
CONTROLLER_IMAGE_TAG = "localhost/allmath-research:latest"

CANDIDATE_SOURCE_MAX_BYTES = oracle.CANDIDATE_SOURCE_MAX_BYTES
REPORT_MAX_BYTES = oracle.REPORT_MAX_BYTES
ISOLATED_TIMEOUT_SECONDS = oracle.ISOLATED_TIMEOUT_SECONDS
ISOLATED_CPUS = oracle.ISOLATED_CPUS
ISOLATED_MEMORY_BYTES = oracle.ISOLATED_MEMORY_BYTES
ISOLATED_PIDS = oracle.ISOLATED_PIDS
ISOLATED_TMPFS_BYTES = oracle.ISOLATED_TMPFS_BYTES

REQUIRED_API = {
    "canonical_json_bytes",
    "decode_canonical_json",
    "validate_point",
    "recompute_window",
    "validate_window_bytes",
    "validate_cas_record",
    "validate_receipt",
}
FORBIDDEN_DELIVERABLES = {"self_test.py", "manifest.json", "receipt.json", "cas.json"}
ALLOWED_IMPORTS = {"__future__", "hashlib", "json", "re", "typing"}
FORBIDDEN_CALLS = {
    "open",
    "eval",
    "exec",
    "compile",
    "__import__",
    "input",
    "getattr",
    "setattr",
    "delattr",
    "globals",
    "locals",
    "vars",
    "dir",
    "help",
    "hasattr",
    "breakpoint",
    "print",
    "float",
    "complex",
    "round",
    "pow",
    "hash",
    "id",
    "exit",
    "quit",
}
FORBIDDEN_IDENTIFIERS = {
    "builtins",
    "ctypes",
    "decimal",
    "fraction",
    "fractions",
    "importlib",
    "inspect",
    "marshal",
    "multiprocessing",
    "numpy",
    "os",
    "pathlib",
    "pickle",
    "random",
    "requests",
    "resource",
    "signal",
    "socket",
    "subprocess",
    "sys",
    "threading",
    "time",
    "urllib",
}
FORBIDDEN_ARITHMETIC_TOKENS = {
    "bbp",
    "sampledbbporbit",
    "partialsum",
    "partial_sum",
    "compute_q",
    "compute_f",
    "combined_term",
    "literal_term",
}
IMMUTABLE_IMAGE_RE = re.compile(r"[0-9a-f]{64}\Z")

_TASK_TOP_LEVEL_KEYS = {
    "schema",
    "status",
    "claim_label",
    "active",
    "launch_authorized",
    "launch_authority_semantics",
    "controller_gate_id",
    "parent_experiment_id",
    "parent_spec_binding",
    "child_fixture_binding",
    "deliverables",
    "api_contract",
    "resource_limits",
    "scope",
    "canonical_raw_bytes",
    "frozen_acceptance",
    "schemas",
    "controller_recomputation",
    "controller_image_dispatch",
    "future_task_template",
    "nonclaims",
}
_EXPECTED_RESOURCE_LIMITS = {
    "candidate_source_max_bytes": 262_144,
    "report_max_bytes": 65_536,
    "canonical_raw_max_bytes": 268_435_456,
    "json_max_nesting_depth": 32,
    "json_max_array_items": 2_048,
    "json_max_object_keys": 64,
    "canonical_integer_string_max_digits": 2_000_000,
    "isolated_timeout_seconds": 120,
    "isolated_cpus": 1,
    "isolated_memory_bytes": 2_147_483_648,
    "isolated_pids": 64,
    "isolated_tmpfs_bytes": 1_073_741_824,
    "limit_semantics": (
        "limits are inclusive maxima except timeout; the controller tests each "
        "exact boundary and one-over rejection without allocating adversarial "
        "one-over fixtures larger than the stated byte cap"
    ),
}
_EXPECTED_SCOPE = {
    "allowed": [
        "strict canonical JSON byte parsing and serialization",
        "exact schema and binding validation",
        "integer-only recomputation from supplied normalized points",
        "SHA-256 digest calculation and validation",
    ],
    "forbidden": [
        "BBP terms, partial sums, Q/F/H/d/e/X/k/W/R generation, Fraction, or any production arithmetic",
        "filesystem writes, CAS storage, receipt minting, subprocesses, network, dynamic imports, reflection, or code execution",
        "candidate-authored tests, pass flags, manifests, receipts, or self-test authority",
        "floats, decimal approximations, random inputs, clock-dependent values, or environment-dependent behavior",
    ],
}
_EXPECTED_RECOMPUTATION = [
    "require exactly 256 ordered points whose n fields are the exact consecutive metadata start_n..end_exclusive_n-1; do not claim S0 authenticates T118 r,w provenance",
    "recompute n0..n9 and require their sum is 256",
    "recompute J=sum n_c^2 and j10_strict_pass=(9*J<65536)",
    "for every lag 1..255 recompute Delta, C_l, A_l, and Z_l",
    "require J=256+2*sum C_l, C_l<=A_l, and Z_l<=A_l",
    "recompute the raw maximum same-cell determinant ratio and lexicographically first witness",
    "recompute c_sum, a_sum, zero flag, and window13_action with the frozen priority rule",
    "never accept candidate-reported summaries or decisions without exact equality to recomputation",
]
_EXPECTED_IMAGE_DISPATCH = {
    "rule": (
        "the runner resolves the configured controller image once to a lowercase "
        "64-hex immutable image ID before candidate execution and passes that "
        "exact ID into the fixed S0 gate; the gate executes the same ID and never "
        "a mutable tag"
    ),
    "required_test": (
        "a fixed runner dispatch test must inject a sentinel immutable ID, assert "
        "the S0 run_gate call receives it, and assert the isolated pod command "
        "contains that ID and no mutable image tag"
    ),
    "isolation": (
        "network none, read-only root, dropped ALL capabilities, no-new-privileges, "
        "exact pids/cpu/memory/timeout limits, bounded nosuid,nodev tmpfs, candidate "
        "and harness mounted read-only without broad run-directory mounts"
    ),
}
_EXPECTED_NONCLAIMS = [
    "This is a planned task specification, not an implementation or active task.",
    "No CAS object or accepted controller receipt exists merely because its schema is specified.",
    "No BBP value, production window, J10 outcome, pair count, occupancy, density, cancellation, V1, or Pi result is computed or claimed.",
]


class S0GateError(RuntimeError):
    """A deterministic rejection by trusted T120 S0 controller code."""


def _sha256_path(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def _safe_regular(path: Path, label: str) -> None:
    if path.is_symlink() or not path.is_file():
        raise S0GateError(f"missing safe regular file {label}")


def _duplicate_rejector(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise S0GateError(f"duplicate key in controller fixture: {key!r}")
        result[key] = value
    return result


def _reject_number(token: str) -> Any:
    raise S0GateError(f"forbidden non-integer token in controller fixture: {token}")


def _load_unique_json(path: Path, label: str) -> Any:
    _safe_regular(path, label)
    try:
        return json.loads(
            path.read_bytes(),
            object_pairs_hook=_duplicate_rejector,
            parse_float=_reject_number,
            parse_constant=_reject_number,
        )
    except S0GateError:
        raise
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise S0GateError(f"invalid {label}: {exc}") from exc


def _parent_rows() -> list[dict[str, str]]:
    return [{"name": name, "sha256": digest} for name, digest in PARENT_RAW_SHA256.items()]


def _child_rows() -> list[dict[str, str]]:
    return [{"name": name, "sha256": digest} for name, digest in CHILD_RAW_SHA256.items()]


def _spec_bundle_digest() -> str:
    payload = json.dumps(
        _parent_rows(), sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return sha256(payload).hexdigest()


def _require_exact_json(actual: Any, expected: Any, label: str) -> None:
    if not oracle._exact_equal(actual, expected):
        raise S0GateError(label + " mismatch")


def validate_frozen_fixtures() -> None:
    """Bind every frozen parent/child input before candidate import."""
    for name, expected in PARENT_RAW_SHA256.items():
        path = PARENT_DIR / name
        _safe_regular(path, name)
        if _sha256_path(path) != expected:
            raise S0GateError(f"parent fixture hash mismatch: {name}")
    for name, expected in CHILD_RAW_SHA256.items():
        path = STAGE_DIR / name
        _safe_regular(path, name)
        if _sha256_path(path) != expected:
            raise S0GateError(f"child fixture hash mismatch: {name}")
    _safe_regular(TASK_CONTRACT, "TASK_CONTRACT.json")
    _safe_regular(HARNESS_PATH, HARNESS_PATH.name)
    if _spec_bundle_digest() != SPEC_BUNDLE_SHA256:
        raise S0GateError("parent spec bundle recomputation mismatch")

    task = _load_unique_json(TASK_CONTRACT, "TASK_CONTRACT.json")
    semantic_payload = json.dumps(
        task, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    if sha256(semantic_payload).hexdigest() != TASK_CONTRACT_SEMANTIC_SHA256:
        raise S0GateError("TASK_CONTRACT semantic digest mismatch")
    if type(task) is not dict or set(task) != _TASK_TOP_LEVEL_KEYS:
        raise S0GateError("TASK_CONTRACT has the wrong exact top-level key set")
    scalars = {
        "schema": "pi-t120-s0-controller-gate-task-v1",
        "status": "planned_inactive_unimplemented",
        "claim_label": "experiment",
        "active": False,
        "launch_authorized": False,
        "controller_gate_id": GATE_ID,
        "parent_experiment_id": oracle.EXPERIMENT_ID,
    }
    for key, expected in scalars.items():
        if type(task.get(key)) is not type(expected) or task[key] != expected:
            raise S0GateError(f"TASK_CONTRACT {key} mismatch")
    _require_exact_json(
        task["parent_spec_binding"],
        {
            "algorithm": "sha256",
            "ordered_payload_encoding": "compact sorted-key ensure_ascii JSON array of exact {name,sha256} pairs, without trailing LF",
            "files": _parent_rows(),
            "spec_bundle_sha256": SPEC_BUNDLE_SHA256,
            "noncircularity": "The three parent files contain no bundle hash; this child contract binds their already-frozen raw bytes.",
        },
        "parent spec binding",
    )
    _require_exact_json(
        task["child_fixture_binding"],
        {
            "algorithm": "sha256",
            "files": _child_rows(),
            "gate_rule": "The future fixed controller gate rejects before candidate execution if either raw fixture hash differs.",
            "noncircularity": "TASK_CONTRACT.json is intentionally excluded from this child fixture hash set and is bound separately by the runner task-contract digest when promoted.",
        },
        "child fixture binding",
    )
    deliverables = task["deliverables"]
    if type(deliverables) is not dict or set(deliverables) != {
        "exact_files",
        "forbidden_files",
        "boundary",
        "public_api_rule",
        "report_contract",
        "python_api",
    }:
        raise S0GateError("deliverable contract key set mismatch")
    if deliverables["exact_files"] != [SOURCE_FILE, REPORT_FILE]:
        raise S0GateError("candidate exact-file contract mismatch")
    if set(deliverables["forbidden_files"]) != FORBIDDEN_DELIVERABLES:
        raise S0GateError("candidate forbidden-file contract mismatch")
    expected_api = [
        "canonical_json_bytes(value)",
        "decode_canonical_json(raw)",
        "validate_point(value, expected_n)",
        "recompute_window(points, window_index, start_n, end_exclusive_n, spec_bundle_sha256)",
        "validate_window_bytes(raw, window_index, start_n, end_exclusive_n, spec_bundle_sha256)",
        "validate_cas_record(value, expected_bindings)",
        "validate_receipt(value, expected_bindings)",
    ]
    if deliverables["python_api"] != expected_api:
        raise S0GateError("candidate public API contract mismatch")
    for field in ("boundary", "public_api_rule", "report_contract"):
        if type(deliverables[field]) is not str or not deliverables[field]:
            raise S0GateError(f"missing deliverable {field} firewall")

    _require_exact_json(task["resource_limits"], _EXPECTED_RESOURCE_LIMITS, "resource limits")
    _require_exact_json(task["scope"], _EXPECTED_SCOPE, "scope/firewall")
    canonical = task["canonical_raw_bytes"]
    if type(canonical) is not dict or set(canonical) != {
        "accepted",
        "json_value_domain",
        "limit_measurement",
        "parser_requirements",
    }:
        raise S0GateError("canonical-byte contract key set mismatch")
    if canonical["accepted"] != (
        "json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('ascii') plus exactly one LF"
    ):
        raise S0GateError("canonical-byte serialization mismatch")
    required_parser_rules = {
        "input type is bytes and bounded by the controller",
        "UTF-8 without BOM; ASCII canonical output; LF only; exactly one final LF",
        "reject duplicate object keys with object_pairs_hook",
        "reject floats with parse_float and NaN/Infinity with parse_constant",
        "reject invalid UTF-8, BOM, CRLF, missing/folded/multiple final LF, whitespace, parsed-equivalent noncanonical bytes, excessive nesting, and excessive size",
        "after strict parse, raw bytes must equal canonical_json_bytes(parsed)",
    }
    if set(canonical["parser_requirements"]) != required_parser_rules:
        raise S0GateError("canonical parser requirements mismatch")
    if "exact built-in" not in canonical["json_value_domain"]:
        raise S0GateError("canonical JSON exact-type domain weakened")
    if "root scalar has nesting depth 0" not in canonical["limit_measurement"]:
        raise S0GateError("canonical limit measurement weakened")

    frozen = task["frozen_acceptance"]
    expected_windows = [
        {
            "window_index": index,
            "start_n": 512 + 256 * index,
            "end_exclusive_n": 768 + 256 * index,
        }
        for index in range(14)
    ]
    if (
        type(frozen) is not dict
        or set(frozen) != {"spec_bundle_sha256", "windows", "argument_rule", "index_scope"}
        or frozen["spec_bundle_sha256"] != SPEC_BUNDLE_SHA256
        or not oracle._exact_equal(frozen["windows"], expected_windows)
        or "arbitrary 256-index ranges" not in frozen["argument_rule"]
        or "cannot authenticate" not in frozen["index_scope"]
    ):
        raise S0GateError("frozen window acceptance mismatch")

    schemas = task["schemas"]
    if type(schemas) is not dict or set(schemas) != {
        "point",
        "lag_record",
        "maximum_determinant_ratio",
        "decision",
        "window_artifact",
        "cas_record",
        "receipt",
    }:
        raise S0GateError("schema collection mismatch")
    if schemas["point"]["exact_keys"] != ["n", "r", "w", "cell"]:
        raise S0GateError("point schema keys mismatch")
    if schemas["lag_record"]["laws"][-2:] != ["C_l<=A_l", "Z_l<=A_l"]:
        raise S0GateError("lag invariant schema mismatch")
    if schemas["maximum_determinant_ratio"]["laws"][-2:] != [
        "the ratio is maximal by integer cross multiplication over distinct same-cell pairs",
        "ties use lexicographically least (witness_n,witness_m)",
    ]:
        raise S0GateError("maximum-ratio schema weakened")
    if schemas["decision"].get("exact_actions") != [
        "stop_local_conjecture",
        "stop_audit_zero",
        "go_holdouts",
        "stop_determinant_route_pending_optional_refinement",
    ]:
        raise S0GateError("decision action schema mismatch")
    if schemas["cas_record"].get("expected_bindings_exact_keys") != [
        "artifact_sha256",
        "size_bytes",
        "experiment_id",
        "spec_bundle_sha256",
        "window_index",
        "start_n",
        "end_exclusive_n",
    ]:
        raise S0GateError("CAS expected-binding schema mismatch")
    if schemas["receipt"].get("expected_bindings_exact_keys") != [
        "experiment_id",
        "spec_bundle_sha256",
        "window_index",
        "start_n",
        "end_exclusive_n",
        "artifact_sha256",
        "generator_source_sha256",
        "verifier_source_sha256",
        "verifier_result",
        "controller_gate_id",
    ]:
        raise S0GateError("receipt expected-binding schema mismatch")
    if "not a production receipt authority" not in schemas["receipt"]["authority"]:
        raise S0GateError("receipt authority firewall weakened")

    _require_exact_json(
        task["controller_recomputation"], _EXPECTED_RECOMPUTATION, "controller recomputation"
    )
    _require_exact_json(
        task["controller_image_dispatch"], _EXPECTED_IMAGE_DISPATCH, "controller image dispatch"
    )
    _require_exact_json(task["nonclaims"], _EXPECTED_NONCLAIMS, "research nonclaims")
    if task["future_task_template"].get("controller_gate") != GATE_ID:
        raise S0GateError("future task dispatch ID mismatch")

    controller_tests = _load_unique_json(CONTROLLER_TESTS, "CONTROLLER_TESTS.json")
    if (
        type(controller_tests) is not dict
        or controller_tests.get("schema") != "pi-t120-s0-controller-tests-v1"
        or controller_tests.get("candidate_self_test_authority") is not False
    ):
        raise S0GateError("controller test authority contract mismatch")


def static_schema_check(path: Path) -> None:
    """Reject source that crosses the pure deterministic validation boundary."""
    _safe_regular(path, SOURCE_FILE)
    raw = path.read_bytes()
    if len(raw) > CANDIDATE_SOURCE_MAX_BYTES:
        raise S0GateError("candidate source exceeds frozen byte limit")
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw:
        raise S0GateError("candidate source must be UTF-8 LF text without BOM")
    try:
        source = raw.decode("utf-8", errors="strict")
        tree = ast.parse(source, filename=str(path))
    except (UnicodeError, SyntaxError) as exc:
        raise S0GateError(f"cannot parse {SOURCE_FILE}: {exc}") from exc

    imports: set[str] = set()
    public_top_level: set[str] = set()
    for statement in tree.body:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if not statement.name.startswith("_"):
                public_top_level.add(statement.name)
            if getattr(statement, "decorator_list", []):
                raise S0GateError("candidate source uses import-time decorators")
            if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defaults = list(statement.args.defaults) + [
                    item for item in statement.args.kw_defaults if item is not None
                ]
                if any(isinstance(item, (ast.List, ast.Dict, ast.Set, ast.Call)) for item in defaults):
                    raise S0GateError("candidate source uses stateful or computed defaults")
            elif isinstance(statement, ast.ClassDef):
                if not statement.name.startswith("_"):
                    raise S0GateError("candidate source exposes an extra class authority")
                if not statement.bases or any(
                    not isinstance(base, ast.Name) or base.id != "ValueError"
                    for base in statement.bases
                ):
                    raise S0GateError("candidate helper classes must only subclass ValueError")
                for class_statement in statement.body:
                    if isinstance(class_statement, ast.Pass):
                        continue
                    if (
                        isinstance(class_statement, ast.Expr)
                        and isinstance(class_statement.value, ast.Constant)
                        and type(class_statement.value.value) is str
                    ):
                        continue
                    raise S0GateError("candidate class body has import-time effects")
        elif isinstance(statement, (ast.Import, ast.ImportFrom)):
            pass
        elif isinstance(statement, (ast.Assign, ast.AnnAssign)):
            value = statement.value
            def immutable_constant(node: ast.AST) -> bool:
                return isinstance(node, ast.Constant) or (
                    isinstance(node, ast.Tuple)
                    and all(immutable_constant(item) for item in node.elts)
                )
            if value is None or not immutable_constant(value):
                raise S0GateError("candidate has mutable or computed module state")
        elif isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and type(statement.value.value) is str:
            pass
        else:
            raise S0GateError("candidate source has executable top-level effects")
    if public_top_level != REQUIRED_API:
        raise S0GateError(
            f"candidate has wrong exact public callable declarations {sorted(public_top_level)}"
        )

    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.add((node.module or "").split(".", 1)[0])
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id in FORBIDDEN_CALLS:
                raise S0GateError(f"schema uses forbidden call {node.func.id}")
        elif isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            raise S0GateError("schema contains a floating-point or complex literal")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            raise S0GateError("schema uses true division instead of integer arithmetic")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
            raise S0GateError("schema uses exponentiation that can construct floats")
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)):
            raise S0GateError("schema mutates an attribute")
        elif isinstance(node, (ast.Global, ast.Nonlocal, ast.Delete, ast.Lambda)):
            raise S0GateError("schema uses forbidden state or dynamic callable construction")
        elif isinstance(node, (ast.AsyncFunctionDef, ast.Await, ast.Yield, ast.YieldFrom)):
            raise S0GateError("schema uses asynchronous or generator execution")

        identifier: str | None = None
        if isinstance(node, ast.Name):
            identifier = node.id
        elif isinstance(node, ast.Attribute):
            identifier = node.attr
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            identifier = node.name
        if identifier is None:
            continue
        if identifier.startswith("__") and identifier != "__all__":
            raise S0GateError(f"schema uses forbidden reflective identifier {identifier}")
        if isinstance(node, ast.Name) and identifier in FORBIDDEN_CALLS:
            raise S0GateError(f"schema references forbidden capability {identifier}")
        lowered = identifier.lower().lstrip("_")
        if lowered in FORBIDDEN_IDENTIFIERS:
            raise S0GateError(f"schema uses forbidden capability identifier {identifier}")
        if any(token in lowered for token in FORBIDDEN_ARITHMETIC_TOKENS):
            raise S0GateError(
                f"schema crosses the production arithmetic boundary: {identifier}"
            )
        if identifier in {
            "mro",
            "f_globals",
            "f_locals",
            "f_builtins",
            "gi_frame",
            "cr_frame",
            "ag_frame",
            "tb_frame",
            "tb_next",
            "co_consts",
            "co_code",
            "co_names",
            "co_filename",
        }:
            raise S0GateError(f"schema uses forbidden reflective attribute {identifier}")

    unexpected = sorted(imports - ALLOWED_IMPORTS)
    if unexpected:
        raise S0GateError(f"schema imports unapproved modules {unexpected}")


def _validate_report(path: Path) -> None:
    _safe_regular(path, REPORT_FILE)
    raw = path.read_bytes()
    if len(raw) > REPORT_MAX_BYTES:
        raise S0GateError("REPORT.md exceeds frozen byte limit")
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw:
        raise S0GateError("REPORT.md must be UTF-8 LF text without BOM")
    if not raw.endswith(b"\n"):
        raise S0GateError("REPORT.md must end with LF")
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeError as exc:
        raise S0GateError("REPORT.md is not valid UTF-8") from exc
    if not text.startswith("Status: `experiment`"):
        raise S0GateError("REPORT.md must begin Status: `experiment`")
    lowered = text.lower()
    required = ("s0", "validation", "t118", "r,w", "deferred", "later disjoint arithmetic verifier")
    if any(token not in lowered for token in required):
        raise S0GateError("REPORT.md omits the S0/T118 provenance deferral")
    forbidden_patterns = (
        r"\bpass(?:ed)?\b",
        r"\bproduction\s+(?:result|outcome|window)\b",
        r"\bcas\s+(?:object\s+)?(?:exists|stored|written|created)\b",
        r"\breceipt\s+(?:exists|accepted|minted|created)\b",
        r"\bpi\s+(?:is|has|equals|result|proved|resolved)\b",
        r"\bdensity\s+(?:is|result|proved|resolved)\b",
        r"\bcancellation\s+(?:is|result|proved|resolved)\b",
        r"\bv1\s+(?:is|result|proved|resolved)\b",
    )
    if any(re.search(pattern, lowered) for pattern in forbidden_patterns):
        raise S0GateError("REPORT.md contains a forbidden authority or research claim")


def _controller_owned_top_level(path: Path) -> bool:
    name = path.name
    if name in {"AGENTS.md", "TASK_CONTRACT.md", "response.txt", "trace.jsonl"}:
        return True
    if name in {"inputs", ".modelbench-sandbox", ".sandbox-opencode-state", "logs"}:
        return path.is_dir() and not path.is_symlink()
    if name.startswith(("response-", "trace-")):
        return path.is_file() and not path.is_symlink()
    if re.fullmatch(r"(?:t120_s0_schema|REPORT)-.+-attempt-[0-9]+(?:\.py|\.md)", name):
        return path.is_file() and not path.is_symlink()
    return False


def _safe_candidate_files(work_dir: Path) -> tuple[Path, Path]:
    root = work_dir.resolve()
    source = root / SOURCE_FILE
    report = root / REPORT_FILE
    for path, label in ((source, SOURCE_FILE), (report, REPORT_FILE)):
        if root not in path.resolve().parents:
            raise S0GateError(f"unsafe candidate path for {label}")
        _safe_regular(path, label)
    controller_directories = {
        "inputs", ".modelbench-sandbox", ".sandbox-opencode-state", "logs"
    }
    for path in root.rglob("*"):
        relative = path.relative_to(root)
        if path.is_symlink():
            raise S0GateError(f"candidate/controller tree contains symlink {relative}")
        if not path.is_file() and not path.is_dir():
            raise S0GateError(f"candidate/controller tree contains special file {relative}")
        under_controller_directory = bool(
            relative.parts and relative.parts[0] in controller_directories
        )
        if path.name in FORBIDDEN_DELIVERABLES and not under_controller_directory:
            raise S0GateError(f"forbidden candidate deliverable {relative}")
    for path in root.iterdir():
        if path.name in {SOURCE_FILE, REPORT_FILE} or _controller_owned_top_level(path):
            continue
        raise S0GateError(f"undeclared candidate deliverable {path.name}")
    if source.stat().st_size > CANDIDATE_SOURCE_MAX_BYTES:
        raise S0GateError("candidate source exceeds frozen byte limit")
    _validate_report(report)
    return source, report


def _write_controller_fixture(path: Path, fixture_seed_hex: str) -> None:
    fixture = oracle.build_controller_fixture(SPEC_BUNDLE_SHA256, fixture_seed_hex)
    raw = oracle.canonical_json_bytes(fixture)
    if not oracle._exact_equal(oracle.decode_canonical_json(raw), fixture):
        raise S0GateError("internal controller fixture canonicalization mismatch")
    path.write_bytes(raw)


def _controller_bundle_digest(rows: list[dict[str, str]]) -> str:
    payload = json.dumps(
        rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return sha256(payload).hexdigest()


def _validate_controller_provenance(value: Any) -> dict[str, str]:
    if type(value) is not dict or set(value) != {"files", "bundle_sha256"}:
        raise S0GateError("missing exact controller source provenance")
    rows = value["files"]
    if type(rows) is not list or len(rows) != 3:
        raise S0GateError("controller source provenance has wrong file rows")
    expected_names = [
        "t120_s0_controller_gate.py",
        "t120_s0_controller_harness.py",
        "t120_s0_controller_oracle.py",
    ]
    local_paths = {
        "t120_s0_controller_gate.py": Path(__file__),
        "t120_s0_controller_harness.py": HARNESS_PATH,
        "t120_s0_controller_oracle.py": ORACLE_PATH,
    }
    expected: dict[str, str] = {}
    for index, row in enumerate(rows):
        if type(row) is not dict or set(row) != {"name", "sha256"}:
            raise S0GateError("controller source provenance row malformed")
        name = row["name"]
        digest = row["sha256"]
        if name != expected_names[index] or type(digest) is not str or IMMUTABLE_IMAGE_RE.fullmatch(digest) is None:
            raise S0GateError("controller source provenance row mismatch")
        path = local_paths[name]
        _safe_regular(path, name)
        if _sha256_path(path) != digest:
            raise S0GateError(f"controller source hash mismatch: {name}")
        expected[name] = digest
    bundle = value["bundle_sha256"]
    if (
        type(bundle) is not str
        or IMMUTABLE_IMAGE_RE.fullmatch(bundle) is None
        or _controller_bundle_digest(rows) != bundle
    ):
        raise S0GateError("controller source bundle digest mismatch")
    return expected


def _copy_controller_snapshot(destination: Path, expected: dict[str, str]) -> dict[str, Path]:
    sources = {
        "t120_s0_controller_gate.py": Path(__file__),
        "t120_s0_controller_harness.py": HARNESS_PATH,
        "t120_s0_controller_oracle.py": ORACLE_PATH,
    }
    destination.mkdir()
    copied: dict[str, Path] = {}
    for name, source in sources.items():
        target = destination / name
        shutil.copy2(source, target, follow_symlinks=False)
        _safe_regular(target, "copied " + name)
        if _sha256_path(target) != expected[name]:
            raise S0GateError(f"copied controller source hash mismatch: {name}")
        copied[name] = target
    return copied


def _require_immutable_image(image: Any) -> str:
    if type(image) is not str or IMMUTABLE_IMAGE_RE.fullmatch(image) is None:
        raise S0GateError("controller image must be a lowercase 64-hex immutable ID")
    return image


def _isolated_command(candidate: Path, harness: Path, fixture: Path, image: str) -> list[str]:
    return [
        "podman",
        "run",
        "--rm",
        "--network",
        "none",
        "--read-only",
        "--cap-drop",
        "ALL",
        "--security-opt",
        "no-new-privileges",
        "--pids-limit",
        str(ISOLATED_PIDS),
        "--tmpfs",
        f"/tmp:rw,nosuid,nodev,size={ISOLATED_TMPFS_BYTES}",
        "--cpus",
        str(ISOLATED_CPUS),
        "--memory",
        str(ISOLATED_MEMORY_BYTES),
        "--timeout",
        str(ISOLATED_TIMEOUT_SECONDS),
        "-v",
        f"{candidate.parent}:/candidate:ro",
        "-v",
        f"{harness.parent}:/controller:ro",
        "-v",
        f"{fixture.parent}:/fixture:ro",
        image,
        "python3",
        "-I",
        "-B",
        f"/controller/{harness.name}",
        f"/candidate/{SOURCE_FILE}",
        "/fixture/controller_fixture.json",
    ]


def _run_isolated(
    candidate_path: Path, *, image: str, controller_provenance: Any
) -> tuple[str, str]:
    image_id = _require_immutable_image(image)
    expected_sources = _validate_controller_provenance(controller_provenance)
    bundle_sha256 = controller_provenance["bundle_sha256"]
    fixture_seed_hex = secrets.token_hex(32)
    temp_dir = Path(tempfile.mkdtemp(prefix="t120-s0-controller-gate-"))
    try:
        candidate_dir = temp_dir / "candidate"
        controller_dir = temp_dir / "controller"
        fixture_dir = temp_dir / "fixture"
        candidate_dir.mkdir()
        fixture_dir.mkdir()
        candidate = candidate_dir / SOURCE_FILE
        controller_snapshot = _copy_controller_snapshot(
            controller_dir, expected_sources
        )
        harness = controller_snapshot["t120_s0_controller_harness.py"]
        fixture = fixture_dir / "controller_fixture.json"
        shutil.copy2(candidate_path, candidate, follow_symlinks=False)
        if _sha256_path(candidate) != _sha256_path(candidate_path):
            raise S0GateError("copied candidate source hash mismatch")
        _write_controller_fixture(fixture, fixture_seed_hex)
        command = _isolated_command(candidate, harness, fixture, image_id)
        try:
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                check=False,
                timeout=ISOLATED_TIMEOUT_SECONDS + 15,
            )
        except subprocess.TimeoutExpired as exc:
            raise S0GateError(
                f"isolated controller mutations timed out after {ISOLATED_TIMEOUT_SECONDS}s"
            ) from exc
        except OSError as exc:
            raise S0GateError(f"cannot start isolated controller mutations: {exc}") from exc
        output = f"{completed.stdout}\n{completed.stderr}"
        if completed.returncode != 0:
            raise S0GateError(f"isolated controller mutations failed: {output[-3000:]}")
        if "T120_S0_CONTROLLER_MUTATIONS_PASSED" not in completed.stdout:
            raise S0GateError("isolated controller mutations omitted pass marker")
        return fixture_seed_hex, bundle_sha256
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def run_gate(
    work_dir: Path,
    grading: dict[str, Any],
    *,
    controller_image: str | None = None,
    controller_provenance: Any = None,
) -> tuple[bool, str]:
    """Run the fixed gate; candidate/grading self-reports confer no authority."""
    del grading
    try:
        validate_frozen_fixtures()
        image_id = _require_immutable_image(controller_image)
        source, _report = _safe_candidate_files(work_dir)
        static_schema_check(source)
        fixture_seed_hex, controller_bundle_sha256 = _run_isolated(
            source,
            image=image_id,
            controller_provenance=controller_provenance,
        )
        return (
            True,
            f"{GATE_ID} passed strict bytes, schema, recomputation, CAS, receipt, and limit mutations; "
            f"controller_bundle_sha256={controller_bundle_sha256}; "
            f"fixture_seed={fixture_seed_hex}",
        )
    except (S0GateError, OSError, UnicodeError, ValueError) as exc:
        return False, f"{GATE_ID} rejected: {exc}"
