"""Deterministic controller gate for the bounded T117 S1 schema stage."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from typing import Any


GATE_ID = "t117_s1_schema_v1"
ROOT = Path(__file__).resolve().parents[2]
FIXTURE_DIR = (
    ROOT
    / "workflows"
    / "modelbench"
    / "tasks"
    / "pi"
    / "current"
    / "t117-census-staged"
    / "fixtures"
)
CONTRACT_FIXTURE = FIXTURE_DIR / "CONTRACT.production.json"
INTERFACE_FIXTURE = FIXTURE_DIR / "INTERFACE_V1.json"
SEMANTIC_FIXTURE = FIXTURE_DIR / "SEMANTIC_VECTORS.json"
FROZEN_FIXTURE_SHA256 = {
    "CONTRACT.production.json": "4e527ac2ada7708a55eb0e377d08bb58c4d0f7566cd705839b8fc275dd9a9511",
    "INTERFACE_V1.json": "5fe7db00bbd8fb5378f21699e0bdb68119fa122f71f11dd029327f0acc612eed",
    "SEMANTIC_VECTORS.json": "acb3fdd268e917be3d97a99ede7ba71ca6fc4c05af46bc7b306338826336cbf4",
}
IMAGE = "localhost/allmath-research:latest"
ALLOWED_IMPORTS = {"__future__", "hashlib", "json", "re", "typing"}
FORBIDDEN_IDENTIFIERS = {
    "bbp",
    "fraction",
    "normalize",
    "gcd",
    "combined_term",
    "literal_term",
    "compute_q",
    "compute_f",
    "law_k1",
    "law_k2",
    "checkpoint",
    "shard_generate",
    "shard_verify",
    "aggregate",
}
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
}


class S1GateError(RuntimeError):
    pass


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_shards() -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    start = 512
    for width, count in ((256, 2), (128, 8), (64, 32)):
        for _ in range(count):
            rows.append(
                {
                    "index": len(rows),
                    "start_n": start,
                    "end_exclusive_n": start + width,
                }
            )
            start += width
    return rows


def validate_frozen_fixtures() -> None:
    for path in (CONTRACT_FIXTURE, INTERFACE_FIXTURE, SEMANTIC_FIXTURE):
        expected = FROZEN_FIXTURE_SHA256[path.name]
        if _sha256(path) != expected:
            raise S1GateError(f"controller fixture hash mismatch: {path.name}")
    try:
        contract = json.loads(CONTRACT_FIXTURE.read_bytes())
        interface = json.loads(INTERFACE_FIXTURE.read_bytes())
        semantic_vectors = json.loads(SEMANTIC_FIXTURE.read_bytes())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise S1GateError(f"invalid controller fixture: {exc}") from exc
    if type(contract) is not dict or set(contract) != {
        "schema",
        "workflow",
        "status",
        "term_definition",
        "p_definition",
        "q_definition",
        "f_definition",
        "anchors",
        "laws",
        "semantics",
        "census",
        "shards",
    }:
        raise S1GateError("frozen production contract has wrong exact keys")
    expected_scalars = {
        "schema": "t117-normalized-census-contract-v1",
        "workflow": "t117-normalized-census",
        "status": "experiment",
        "term_definition": (
            "t_m=16^(-m)*(4/(8*m+1)-2/(8*m+4)-1/(8*m+5)-1/(8*m+6))"
        ),
        "p_definition": "P_N=sum_(m=0)^(7*N) t_m",
        "q_definition": "Q_N=10^N*P_N",
        "f_definition": "F_N=10^(N+1)*sum_(j=1)^7 t_(7*N+j)",
    }
    if any(type(contract.get(k)) is not str or contract[k] != v for k, v in expected_scalars.items()):
        raise S1GateError("frozen production definitions mismatch")
    if contract.get("anchors") != {
        "Q_0": "47/15",
        "Q_1": (
            "16331158360096799798177512637/"
            "519836915885323158521118720"
        ),
    }:
        raise S1GateError("frozen production anchors mismatch")
    if contract.get("laws") != {"K1": "k^2<=e", "K2": "k^2<=d*e"}:
        raise S1GateError("frozen production laws mismatch")
    if contract.get("semantics") != {
        "denominators": "D>0 and E>0",
        "K1_failure": "k^2>e",
        "K2_failure": "k^2>d*e",
        "failure_implication": "K2_failure=>K1_failure",
        "shard_endpoints": "[a,b) binds P_a and P_b",
        "tiny_natural_failures": "none on [0,8)",
    }:
        raise S1GateError("frozen production semantic metadata mismatch")
    if contract.get("census") != {"start_n": 512, "end_exclusive_n": 4096}:
        raise S1GateError("frozen production range mismatch")
    if contract.get("shards") != expected_shards():
        raise S1GateError("frozen production shard partition mismatch")
    if type(interface) is not dict or interface.get("schema") != "t117-s1-interface-v1":
        raise S1GateError("frozen S1 interface schema mismatch")
    if semantic_vectors != {
        "schema": "t117-semantic-vectors-v1",
        "tiny_natural_range_half_open": [0, 8],
        "tiny_natural_failures": [],
        "synthetic_normalization": [
            {"A": 1, "C": 1, "D": 4, "E": 1, "expected_fails": ["K1"]},
            {"A": 1, "C": 1, "D": 2, "E": 1, "expected_fails": ["K1", "K2"]},
        ],
    }:
        raise S1GateError("frozen semantic vectors mismatch")
    from workflows.modelbench.t117_controller_gate import trusted_record

    natural_failures: list[dict[str, Any]] = []
    for n in range(8):
        record = trusted_record(n)
        k = int(record["k"])
        e = int(record["e"])
        d = int(record["tuple"]["d"])
        fails = (["K1"] if k * k > e else []) + (["K2"] if k * k > d * e else [])
        if fails:
            natural_failures.append({"n": n, "fails": fails})
    if natural_failures != semantic_vectors["tiny_natural_failures"]:
        raise S1GateError("frozen tiny natural failure claim mismatch")
    for vector in semantic_vectors["synthetic_normalization"]:
        A, C, D, E = (vector[key] for key in ("A", "C", "D", "E"))
        from math import gcd

        H = gcd(D, E)
        d, e = D // H, E // H
        X = 10 * A * e + C * d
        k = gcd(abs(X), H * d)
        fails = (["K1"] if k * k > e else []) + (["K2"] if k * k > d * e else [])
        if fails != vector["expected_fails"]:
            raise S1GateError("frozen synthetic failure vector mismatch")


def static_schema_check(path: Path) -> None:
    try:
        source = path.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=str(path))
    except (OSError, UnicodeError, SyntaxError) as exc:
        raise S1GateError(f"cannot parse schema_v1.py: {exc}") from exc
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.add((node.module or "").split(".", 1)[0])
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id in FORBIDDEN_CALLS:
                raise S1GateError(f"schema uses forbidden call {node.func.id}")
        if isinstance(node, (ast.Name, ast.Attribute, ast.FunctionDef, ast.ClassDef)):
            if isinstance(node, ast.Attribute):
                identifier = node.attr
            else:
                identifier = node.id if isinstance(node, ast.Name) else node.name
            if identifier.startswith("__") and identifier != "__all__":
                raise S1GateError(
                    f"schema uses forbidden reflective identifier {identifier}"
                )
            lowered = identifier.lower()
            semantic_constants = {"_LAW_K1_V1", "_LAW_K2_V1"}
            if (
                identifier not in semantic_constants
                and any(token in lowered for token in FORBIDDEN_IDENTIFIERS)
            ):
                raise S1GateError(f"schema crosses arithmetic/orchestration boundary: {identifier}")
    unexpected = sorted(imports - ALLOWED_IMPORTS)
    if unexpected:
        raise S1GateError(f"schema imports unapproved modules {unexpected}")


HARNESS = r'''
import copy
import hashlib
import importlib.util
import json
import sys

schema_path, contract_path = sys.argv[1:3]
spec = importlib.util.spec_from_file_location("candidate_schema_v1", schema_path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

required = ("canonical_json", "sha256_hex_obj", "validate_contract", "validate_record")
for name in required:
    if not callable(getattr(module, name, None)):
        raise AssertionError("missing callable " + name)

def accepts(fn, value):
    fn(copy.deepcopy(value))

def rejects(fn, value):
    try:
        fn(copy.deepcopy(value))
    except Exception:
        return
    raise AssertionError("mutation accepted: " + repr(value)[:300])

with open(contract_path, "r", encoding="utf-8") as handle:
    contract = json.load(handle)
accepts(module.validate_contract, contract)

contract_mutations = []
def mutate(path, value):
    item = copy.deepcopy(contract)
    target = item
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value
    contract_mutations.append(item)

mutate(["shards", 0, "end_exclusive_n"], 769)
mutate(["shards", 1, "start_n"], 769)
swapped = copy.deepcopy(contract)
swapped["shards"][0], swapped["shards"][1] = swapped["shards"][1], swapped["shards"][0]
contract_mutations.append(swapped)
mutate(["shards", 0, "index"], True)
mutate(["f_definition"], "F_N=frac(Q_N)")
mutate(["q_definition"], "Q_N=P_N")
mutate(["p_definition"], "P_N=sum_(m=0)^(7*N-1) t_m")
mutate(["semantics", "denominators"], "D>=0 and E>=0")
semantic_extra = copy.deepcopy(contract); semantic_extra["semantics"]["F"] = "Fibonacci"; contract_mutations.append(semantic_extra)
extra = copy.deepcopy(contract); extra["extra"] = 1; contract_mutations.append(extra)
missing = copy.deepcopy(contract); del missing["laws"]; contract_mutations.append(missing)
for item in contract_mutations:
    rejects(module.validate_contract, item)

sample = {"b": 2, "a": 1}
want_json = '{"a":1,"b":2}'
if module.canonical_json(sample) != want_json:
    raise AssertionError("canonical_json mismatch")
want_hash = hashlib.sha256(want_json.encode("ascii")).hexdigest()
if module.sha256_hex_obj(sample) != want_hash:
    raise AssertionError("sha256_hex_obj mismatch")

compact = {
    "digest": "0" * 64, "e": "456", "e_bitlen": 0, "fails": [],
    "k": "123", "k_bitlen": 0, "n": 7,
}
accepts(module.validate_record, compact)
tpl = {
    "A":"1","C":"2","D":"3","E":"4","H":"1","U":"10","V":"12",
    "X":"10","d":"3","e":"4","g":"2","k":"2","n":"7",
}
failure = {
    "digest": hashlib.sha256(json.dumps(tpl, sort_keys=True, separators=(",",":"), ensure_ascii=True).encode("ascii")).hexdigest(),
    "e":"4", "e_bitlen":3, "fails":["K1","K2"], "k":"2", "k_bitlen":2,
    "n":7, "q_num":"1", "q_den":"3", "f_num":"2", "f_den":"4", "tuple":tpl,
}
accepts(module.validate_record, failure)

record_mutations = []
def record_change(base, path, value):
    item = copy.deepcopy(base); target = item
    for key in path[:-1]: target = target[key]
    target[path[-1]] = value; record_mutations.append(item)

record_change(compact, ["n"], True)
record_change(compact, ["k"], "01")
record_change(compact, ["e"], "0")
record_change(compact, ["digest"], "A" * 64)
extra_record = copy.deepcopy(compact); extra_record["extra"] = 1; record_mutations.append(extra_record)
record_change(failure, ["fails"], ["K2", "K1"])
record_change(failure, ["fails"], ["K1", "K1"])
record_change(failure, ["fails"], ["K3"])
record_change(failure, ["fails"], ["K2"])
record_change(failure, ["digest"], "0" * 64)
record_change(failure, ["q_num"], "9")
record_change(failure, ["tuple", "n"], "8")
record_change(failure, ["tuple", "k"], "9")
bad_q_den = copy.deepcopy(failure)
bad_q_den["q_den"] = bad_q_den["tuple"]["D"] = "0"
bad_q_den["digest"] = hashlib.sha256(json.dumps(bad_q_den["tuple"], sort_keys=True, separators=(",",":"), ensure_ascii=True).encode("ascii")).hexdigest()
record_mutations.append(bad_q_den)
bad_f_den = copy.deepcopy(failure)
bad_f_den["f_den"] = bad_f_den["tuple"]["E"] = "-4"
bad_f_den["digest"] = hashlib.sha256(json.dumps(bad_f_den["tuple"], sort_keys=True, separators=(",",":"), ensure_ascii=True).encode("ascii")).hexdigest()
record_mutations.append(bad_f_den)
no_tuple = copy.deepcopy(failure); del no_tuple["tuple"]; record_mutations.append(no_tuple)
extras_on_success = copy.deepcopy(failure); extras_on_success["fails"] = []; record_mutations.append(extras_on_success)
for item in record_mutations:
    rejects(module.validate_record, item)

print("T117_S1_CONTROLLER_GATE_PASSED")
'''


def _run_isolated(path: Path, timeout_s: int) -> None:
    temp_dir = Path(tempfile.mkdtemp(prefix="t117-s1-gate-"))
    try:
        candidate = temp_dir / "schema_v1.py"
        harness = temp_dir / "controller_harness.py"
        shutil.copy2(path, candidate)
        harness.write_text(HARNESS, encoding="utf-8")
        command = [
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
            "64",
            "--tmpfs",
            "/tmp:rw,nosuid,nodev,size=128m",
            "--cpus",
            "1",
            "--memory",
            "512m",
            "-v",
            f"{temp_dir}:/workspace:ro",
            "-v",
            f"{CONTRACT_FIXTURE}:/fixtures/CONTRACT.production.json:ro",
            IMAGE,
            "python3",
            "-I",
            "/workspace/controller_harness.py",
            "/workspace/schema_v1.py",
            "/fixtures/CONTRACT.production.json",
        ]
        try:
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired as exc:
            raise S1GateError(f"isolated S1 tests timed out after {timeout_s}s") from exc
        output = f"{completed.stdout}\n{completed.stderr}"
        if completed.returncode != 0:
            raise S1GateError(f"isolated S1 tests failed: {output[-1500:]}")
        if "T117_S1_CONTROLLER_GATE_PASSED" not in completed.stdout:
            raise S1GateError("isolated S1 tests omitted pass marker")
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def run_gate(work_dir: Path, grading: dict[str, Any]) -> tuple[bool, str]:
    try:
        validate_frozen_fixtures()
        artifact = (work_dir / "schema_v1.py").resolve()
        if work_dir.resolve() not in artifact.parents or not artifact.is_file() or artifact.is_symlink():
            raise S1GateError("missing safe schema_v1.py")
        static_schema_check(artifact)
        _run_isolated(artifact, int(grading.get("controller_timeout_s", 45)))
        return True, f"{GATE_ID} passed deterministic schema mutations"
    except (S1GateError, OSError, ValueError) as exc:
        return False, f"{GATE_ID} rejected: {exc}"
