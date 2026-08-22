"""Controller-owned executable gate for the T117 exact census workflow.

Candidate code runs only in a fresh, networkless repository sandbox.  The
candidate self-test must export two independently produced probe routes; this
module computes the expected arithmetic itself and compares the complete exact
records.  No candidate arithmetic is imported into the controller process.
"""

from __future__ import annotations

import ast
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import shutil
import subprocess
import tempfile
from typing import Any

from workflows.runtime.sandbox import (
    SandboxConfig,
    SandboxError,
    prepare_sandbox_workspace,
)


GATE_ID = "t117_normalized_census_v1"
PROBE_SCHEMA = "t117-controller-probe-v1"
PROBE_FILE = "controller_probe.json"
TUPLE_KEYS = ("A", "C", "D", "E", "H", "U", "V", "X", "d", "e", "g", "k", "n")
REQUIRED_FILES = (
    "README.md",
    "CONTRACT.json",
    "schema_utils.py",
    "build_checkpoints.py",
    "audit_checkpoints.py",
    "shard_generate.py",
    "shard_verify.py",
    "aggregate.py",
    "self_test.py",
)


class ControllerGateError(RuntimeError):
    """A deterministic T117 controller-gate rejection."""


def _sha256_bytes(data: bytes) -> str:
    return sha256(data).hexdigest()


def _canonical_json(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _bbp_term(k: int) -> Fraction:
    scale = 16**k
    return (
        Fraction(4, scale * (8 * k + 1))
        - Fraction(2, scale * (8 * k + 4))
        - Fraction(1, scale * (8 * k + 5))
        - Fraction(1, scale * (8 * k + 6))
    )


def trusted_record(n: int) -> dict[str, Any]:
    """Return the exact controller oracle record at one sampled index."""
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    s_n = sum((_bbp_term(j) for j in range(7 * n + 1)), Fraction())
    s_next = s_n + sum((_bbp_term(7 * n + j) for j in range(1, 8)), Fraction())
    q_n = (10**n) * s_n
    f_n = (10 ** (n + 1)) * (s_next - s_n)
    A, D = q_n.numerator, q_n.denominator
    C, E = f_n.numerator, f_n.denominator
    H = gcd(D, E)
    d, e = D // H, E // H
    X = 10 * A * e + C * d
    U = 10 * A * E + C * D
    V = D * E
    k = gcd(abs(X), H * d)
    g = gcd(abs(U), V)
    values = (A, C, D, E, H, U, V, X, d, e, g, k, n)
    exact_tuple = {key: str(value) for key, value in zip(TUPLE_KEYS, values)}
    return {
        "n": n,
        "q_num": str(A),
        "q_den": str(D),
        "f_num": str(C),
        "f_den": str(E),
        "tuple": exact_tuple,
        "digest": _sha256_bytes(_canonical_json(exact_tuple)),
        "k": str(k),
        "e": str(e),
    }


def expected_shard_table() -> list[dict[str, int]]:
    """Return the one controller-authorized ordered partition of [512,4096)."""
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
    assert len(rows) == 42 and start == 4096
    return rows


def validate_contract(document: Any) -> None:
    """Validate the fixed controller-owned core of CONTRACT.json."""
    if type(document) is not dict:
        raise ControllerGateError("CONTRACT must be a JSON object")
    required_top = {
        "schema": "t117-normalized-census-contract-v1",
        "workflow": "t117-normalized-census",
        "status": "experiment",
        "q_definition": "Q_N=10^N*S_N",
    }
    for key, expected in required_top.items():
        if type(document.get(key)) is not str or document[key] != expected:
            raise ControllerGateError(f"CONTRACT {key} mismatch")

    anchors = document.get("anchors")
    if type(anchors) is not dict or set(anchors) != {"Q_0", "Q_1"}:
        raise ControllerGateError("CONTRACT anchors have the wrong exact key set")
    if anchors != {
        "Q_0": "47/15",
        "Q_1": (
            "16331158360096799798177512637/"
            "519836915885323158521118720"
        ),
    }:
        raise ControllerGateError("CONTRACT Q anchors mismatch")

    laws = document.get("laws")
    if type(laws) is not dict or set(laws) != {"K1", "K2"}:
        raise ControllerGateError("CONTRACT laws have the wrong exact key set")
    if laws != {"K1": "k^2<=e", "K2": "k^2<=d*e"}:
        raise ControllerGateError("CONTRACT K1/K2 mismatch")

    census = document.get("census")
    if type(census) is not dict or set(census) != {"start_n", "end_exclusive_n"}:
        raise ControllerGateError("CONTRACT census has the wrong exact key set")
    if (
        type(census["start_n"]) is not int
        or type(census["end_exclusive_n"]) is not int
        or census != {"start_n": 512, "end_exclusive_n": 4096}
    ):
        raise ControllerGateError("CONTRACT census must be exact [512,4096)")

    shards = document.get("shards")
    if type(shards) is not list or len(shards) != 42:
        raise ControllerGateError("CONTRACT must contain exactly 42 shards")
    for index, row in enumerate(shards):
        if type(row) is not dict or set(row) != {
            "index",
            "start_n",
            "end_exclusive_n",
        }:
            raise ControllerGateError(f"CONTRACT shard {index} has wrong keys")
        if any(type(row[key]) is not int for key in row):
            raise ControllerGateError(f"CONTRACT shard {index} values must be JSON integers")
    if shards != expected_shard_table():
        raise ControllerGateError("CONTRACT shard table width/gap/order mismatch")


def _reject_known_unsafe_shapes(work_dir: Path) -> None:
    """Cheap rejection of the archived unscaled/sequential Ox candidate."""
    generator = work_dir / "shard_generate.py"
    try:
        source = generator.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=str(generator))
    except (OSError, UnicodeError, SyntaxError) as exc:
        raise ControllerGateError(f"cannot parse shard_generate.py: {exc}") from exc
    for node in ast.walk(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        value = node.value
        if (
            any(isinstance(target, ast.Name) and target.id == "Q" for target in targets)
            and isinstance(value, ast.Name)
            and value.id == "S"
        ):
            raise ControllerGateError("unscaled sampled value assignment Q = S")
    lowered = source.lower()
    if "previous shard" in lowered and "must be generated first" in lowered:
        raise ControllerGateError("shard generation depends on the previous shard")


def _validate_probe(
    probe: Any, *, expected_records: list[dict[str, Any]], contract_sha256: str
) -> None:
    if type(probe) is not dict or set(probe) != {
        "schema",
        "contract_sha256",
        "generator",
        "verifier",
        "shard1_without_shard0",
    }:
        raise ControllerGateError("controller probe has the wrong exact key set")
    if probe["schema"] != PROBE_SCHEMA:
        raise ControllerGateError("controller probe schema mismatch")
    if probe["contract_sha256"] != contract_sha256:
        raise ControllerGateError("controller probe CONTRACT hash mismatch")
    if probe["shard1_without_shard0"] is not True:
        raise ControllerGateError("self-test did not exercise shard 1 without shard 0")
    for route in ("generator", "verifier"):
        if _canonical_json(probe[route]) != _canonical_json(expected_records):
            raise ControllerGateError(f"{route} probe records disagree with trusted oracle")


def _run_networkless_self_test(
    work_dir: Path, *, hidden_n: int, timeout_s: int, image: str
) -> tuple[str, bytes, bytes]:
    run_dir = Path(tempfile.mkdtemp(prefix="t117-controller-gate-"))
    runtime = None
    cidfile = run_dir / "controller.cid"
    output_path = run_dir / "self_test.log"
    try:
        candidate_copy = run_dir / "candidate"
        candidate_copy.mkdir()
        for name in REQUIRED_FILES:
            shutil.copy2(work_dir / name, candidate_copy / name)
        inputs = work_dir / "inputs"
        if inputs.is_dir() and not inputs.is_symlink():
            for source in inputs.rglob("*"):
                if source.is_symlink():
                    raise ControllerGateError("candidate inputs contain a symlink")
                if source.is_file():
                    relative = source.relative_to(inputs)
                    target = candidate_copy / "inputs" / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source, target)
        runtime = prepare_sandbox_workspace(
            config=SandboxConfig(
                enabled=True,
                image=image,
                network=False,
                cpus=1,
                memory="1g",
                timeout_s=timeout_s,
            ),
            working_dir=candidate_copy,
            run_dir=run_dir,
        )
        command = runtime.build_podman_command(
            [
                "env",
                f"T117_CONTROLLER_PROBE_PATH={PROBE_FILE}",
                f"T117_CONTROLLER_PROBE_N={hidden_n}",
                "python3",
                "-I",
                "self_test.py",
            ],
            container_workdir=runtime.paths.container_working_dir,
            cidfile=cidfile,
        )
        # The generic agent sandbox exposes its whole run record at /run for
        # artifact export. This gate needs no exports, and removing those broad
        # mounts prevents candidate code from reaching the workspace through a
        # second path that would bypass the read-only CONTRACT bind below.
        narrowed: list[str] = []
        index = 0
        while index < len(command):
            if command[index] == "-v" and index + 1 < len(command):
                source = command[index + 1].split(":", 1)[0]
                if source == str(run_dir):
                    index += 2
                    continue
            narrowed.append(command[index])
            index += 1
        command = narrowed
        run_index = command.index("run") + 1
        command[run_index:run_index] = [
            "--read-only",
            "--cap-drop",
            "ALL",
            "--security-opt",
            "no-new-privileges",
            "--pids-limit",
            "128",
            "--tmpfs",
            "/tmp:rw,nosuid,nodev,size=256m",
        ]
        image_index = command.index(image)
        sandbox_contract = runtime.paths.workspace_host_path / "CONTRACT.json"
        command[image_index:image_index] = [
            "-v",
            f"{sandbox_contract}:{runtime.paths.container_working_dir / 'CONTRACT.json'}:ro",
        ]
        try:
            with output_path.open("wb") as output:
                completed = subprocess.run(
                    command,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    check=False,
                    timeout=timeout_s,
                )
        except subprocess.TimeoutExpired as exc:
            runtime.force_remove_container(cidfile)
            raise ControllerGateError(
                f"networkless self-test timed out after {timeout_s}s"
            ) from exc
        log = output_path.read_bytes()[-65536:].decode("utf-8", errors="replace")
        if completed.returncode != 0:
            raise ControllerGateError(
                f"networkless self-test exited {completed.returncode}: {log[-1000:]}"
            )
        if "SELF-TEST PASSED" not in log:
            raise ControllerGateError("networkless self-test omitted SELF-TEST PASSED")
        sandbox_work = runtime.paths.workspace_host_path
        contract_after = (sandbox_work / "CONTRACT.json").read_bytes()
        probe_path = sandbox_work / PROBE_FILE
        if probe_path.stat().st_size > 2 * 1024 * 1024:
            raise ControllerGateError("controller probe exceeds 2 MiB")
        probe_bytes = probe_path.read_bytes()
        return log, contract_after, probe_bytes
    finally:
        if runtime is not None and cidfile.exists():
            runtime.force_remove_container(cidfile)
        shutil.rmtree(run_dir, ignore_errors=True)


def run_gate(
    work_dir: Path,
    grading: dict[str, Any],
    *,
    controller_image: str | None = None,
) -> tuple[bool, str]:
    """Run the fixed T117 executable gate and return a runner verdict."""
    try:
        work_dir = work_dir.resolve()
        _reject_known_unsafe_shapes(work_dir)
        for name in REQUIRED_FILES:
            path = work_dir / name
            if not path.is_file() or path.is_symlink():
                raise ControllerGateError(f"missing safe required file {name}")
        contract_path = work_dir / "CONTRACT.json"
        contract_before = contract_path.read_bytes()
        try:
            contract_document = json.loads(contract_before)
        except (UnicodeError, json.JSONDecodeError) as exc:
            raise ControllerGateError(f"invalid CONTRACT JSON: {exc}") from exc
        validate_contract(contract_document)
        contract_hash = _sha256_bytes(contract_before)
        # The third index is deliberately controller-selected and absent from
        # the task prompt. It varies with the immutable candidate contract.
        hidden_n = 2 + int(contract_hash[:8], 16) % 15
        expected = [trusted_record(n) for n in (0, 1, hidden_n)]
        anchor = expected[1]
        if (anchor["q_num"], anchor["q_den"]) != (
            "16331158360096799798177512637",
            "519836915885323158521118720",
        ):
            raise ControllerGateError("internal Q_1 oracle anchor mismatch")
        _, sandbox_contract, probe_bytes = _run_networkless_self_test(
            work_dir,
            hidden_n=hidden_n,
            timeout_s=int(grading.get("controller_timeout_s", 180)),
            image=(
                controller_image
                if controller_image is not None
                else str(
                    grading.get(
                        "controller_image", "localhost/allmath-research:latest"
                    )
                )
            ),
        )
        if sandbox_contract != contract_before or contract_path.read_bytes() != contract_before:
            raise ControllerGateError("CONTRACT.json changed during controller execution")
        try:
            probe = json.loads(probe_bytes)
        except (UnicodeError, json.JSONDecodeError) as exc:
            raise ControllerGateError(f"invalid controller probe JSON: {exc}") from exc
        _validate_probe(probe, expected_records=expected, contract_sha256=contract_hash)
        return True, f"{GATE_ID} passed exact probes at N=0,1,{hidden_n}"
    except (ControllerGateError, SandboxError, OSError, ValueError) as exc:
        return False, f"{GATE_ID} rejected: {exc}"
