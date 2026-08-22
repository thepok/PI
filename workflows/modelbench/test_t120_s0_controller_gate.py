from __future__ import annotations

import copy
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from workflows.modelbench import t120_s0_controller_gate as gate
from workflows.modelbench import t120_s0_controller_oracle as oracle


IMMUTABLE_IMAGE = "a" * 64
FIXTURE_SEED = "b" * 64


@pytest.fixture(scope="module")
def controller_fixture() -> dict:
    return oracle.build_controller_fixture(oracle.SPEC_BUNDLE_SHA256, FIXTURE_SEED)


def _reference_candidate_source() -> str:
    source = Path(oracle.__file__).read_text(encoding="utf-8")
    return source.split("\ndef _round_robin_cells", 1)[0] + "\n"


def _valid_report() -> str:
    return (
        "Status: `experiment`\n"
        "This implements only the S0 strict-byte, schema, statistic, CAS-binding, "
        "and receipt-binding validation surface.\n"
        "T118 r,w provenance is deferred to the later disjoint arithmetic verifier.\n"
    )


def _write_candidate(root: Path, *, source: str | None = None, report: str | None = None) -> Path:
    candidate = root / gate.SOURCE_FILE
    candidate.write_text(source or _reference_candidate_source(), encoding="utf-8")
    (root / gate.REPORT_FILE).write_text(report or _valid_report(), encoding="utf-8")
    return candidate


def _write_fixture(path: Path, fixture: dict) -> None:
    path.write_bytes(oracle.canonical_json_bytes(fixture))


def _run_host_harness(candidate: Path, fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            "-I",
            "-B",
            str(gate.HARNESS_PATH),
            str(candidate),
            str(fixture),
        ],
        capture_output=True,
        text=True,
        check=False,
        timeout=180,
    )


def test_t120_s0_frozen_hashes_bundle_and_contract_semantics() -> None:
    gate.validate_frozen_fixtures()
    for name, digest in gate.PARENT_RAW_SHA256.items():
        assert sha256((gate.PARENT_DIR / name).read_bytes()).hexdigest() == digest
    for name, digest in gate.CHILD_RAW_SHA256.items():
        assert sha256((gate.STAGE_DIR / name).read_bytes()).hexdigest() == digest
    rows = [
        {"name": name, "sha256": digest}
        for name, digest in gate.PARENT_RAW_SHA256.items()
    ]
    payload = json.dumps(
        rows, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    assert sha256(payload).hexdigest() == oracle.SPEC_BUNDLE_SHA256
    assert gate.GATE_ID == "t120_s0_schema_v1"


def test_t120_s0_current_task_loads_and_binds_exact_planned_inputs(
    tmp_path: Path,
) -> None:
    from workflows.modelbench import runner

    task_dir = (
        gate.ROOT
        / "workflows/modelbench/tasks/pi/current/t120-s0-controller-gate"
    )
    tasks = runner.load_tasks(task_dir, None)
    assert len(tasks) == 1
    task = tasks[0]
    assert {
        "id": task["id"],
        "dimension": task["dimension"],
        "timeout_s": task["timeout_s"],
        "max_attempts": task["max_attempts"],
        "variant": task["variant"],
    } == {
        "id": "pi-t120-s0-controller-schema",
        "dimension": "exact_experiment",
        "timeout_s": 1800,
        "max_attempts": 6,
        "variant": "high",
    }
    assert task["grading"] == {
        "type": "artifact_contract",
        "controller_gate": gate.GATE_ID,
        "artifact": gate.SOURCE_FILE,
        "required_files": [gate.REPORT_FILE],
    }

    expected = {
        "inputs/parent/CONTRACT.json": "5e6ac96f7c3c8a003ffbfbf1b65e582b5583700a68c597968d903e70075ce327",
        "inputs/parent/INTERFACE.md": "cd1eb2d91c02e866c9f0bf27e2aadeaa4f9c8e1774ccc4d6dfd1a4114f7d8fde",
        "inputs/parent/TEST_PLAN.md": "ab7f0e1261d472a82789731b9db34ced32afea74f36d188e5b06308357f344ea",
        "inputs/s0/TASK_CONTRACT.json": "7e1250ab42de1430c674ef6fb98680ecc5b3d04982382fe3413d40e21c3a7cd5",
        "inputs/s0/PLANNED_AGENT_GUIDANCE.md": "02017a5545c0b780e1516b163a09280a11fa8b8883b18313378cf3326c7f921b",
        "inputs/s0/CONTROLLER_TESTS.json": "addb579617d7d7dcbf7c5bf08da5fefacb5aa397260ab57151280115ede28106",
    }
    fixture_rows = task["fixtures"]
    assert len(fixture_rows) == 7
    assert fixture_rows[0] == {
        "source": "workflows/modelbench/tasks/pi/current/t120-s0-controller-gate/AGENT_GUIDANCE.md",
        "destination": "AGENTS.md",
        "sha256": "a74fb4c7a038c7445465426bcfdaefce5af40d6c6bf8a07571125bf39b66c905",
    }
    assert {row["destination"] for row in fixture_rows[1:]} == set(expected)
    for row in fixture_rows[1:]:
        source = gate.ROOT / row["source"]
        assert row["sha256"] == expected[row["destination"]]
        assert sha256(source.read_bytes()).hexdigest() == row["sha256"]

    runner.prepare_fixtures(task, tmp_path)
    assert (tmp_path / "AGENTS.md").read_bytes() == (
        task_dir / "AGENT_GUIDANCE.md"
    ).read_bytes()
    for destination, digest in expected.items():
        assert sha256((tmp_path / destination).read_bytes()).hexdigest() == digest

    drifted_task = copy.deepcopy(task)
    drifted_task["fixtures"][1]["sha256"] = "0" * 64
    with pytest.raises(ValueError, match="fixture SHA-256 mismatch"):
        runner.prepare_fixtures(drifted_task, tmp_path / "drifted")



def test_t120_s0_task_contract_semantic_drift_fails_before_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    document = json.loads(gate.TASK_CONTRACT.read_text(encoding="utf-8"))
    document["resource_limits"]["json_max_object_keys"] += 1
    changed = tmp_path / "TASK_CONTRACT.json"
    changed.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    monkeypatch.setattr(gate, "TASK_CONTRACT", changed)
    with pytest.raises(gate.S0GateError, match="semantic digest mismatch"):
        gate.validate_frozen_fixtures()

def test_t120_s0_oracle_exact_api_returns_and_no_mutation(controller_fixture: dict) -> None:
    point = copy.deepcopy(controller_fixture["cases"]["balanced_go"]["points"][0])
    before = copy.deepcopy(point)
    assert oracle.validate_point(point, oracle.TEST_START_N) is None
    assert point == before

    case = controller_fixture["cases"]["balanced_go"]
    points = copy.deepcopy(case["points"])
    before_points = copy.deepcopy(points)
    recomputed = oracle.recompute_window(
        points,
        oracle.TEST_WINDOW_INDEX,
        oracle.TEST_START_N,
        oracle.TEST_END_EXCLUSIVE_N,
        oracle.SPEC_BUNDLE_SHA256,
    )
    assert oracle._exact_equal(recomputed, case["artifact"])
    assert points == before_points
    assert recomputed is not case["artifact"]
    assert recomputed["points"] is not points

    raw = case["raw_ascii"].encode("ascii")
    decoded = oracle.validate_window_bytes(
        raw,
        oracle.TEST_WINDOW_INDEX,
        oracle.TEST_START_N,
        oracle.TEST_END_EXCLUSIVE_N,
        oracle.SPEC_BUNDLE_SHA256,
    )
    assert oracle._exact_equal(decoded, case["artifact"])
    assert oracle.validate_cas_record(
        copy.deepcopy(controller_fixture["cas_record"]),
        copy.deepcopy(controller_fixture["cas_expected_bindings"]),
    ) is None
    assert oracle.validate_receipt(
        copy.deepcopy(controller_fixture["receipt"]),
        copy.deepcopy(controller_fixture["receipt_expected_bindings"]),
    ) is None


def test_t120_s0_all_fourteen_frozen_windows_are_allowlisted(controller_fixture: dict) -> None:
    assert len(controller_fixture["window_cases"]) == 14
    for expected_index, case in enumerate(controller_fixture["window_cases"]):
        assert case["window_index"] == expected_index
        assert case["start_n"] == 512 + 256 * expected_index
        assert case["end_exclusive_n"] == 768 + 256 * expected_index
        assert oracle._exact_equal(
            oracle.validate_window_bytes(
                case["raw_ascii"].encode("ascii"),
                case["window_index"],
                case["start_n"],
                case["end_exclusive_n"],
                oracle.SPEC_BUNDLE_SHA256,
            ),
            case["artifact"],
        )

    points = controller_fixture["window_cases"][0]["points"]
    with pytest.raises(ValueError, match="frozen row"):
        oracle.recompute_window(
            points, 0, 0, 256, oracle.SPEC_BUNDLE_SHA256
        )
    with pytest.raises(ValueError, match="frozen parent binding"):
        oracle.recompute_window(points, 0, 512, 768, "0" * 64)


def test_t120_s0_synthetic_cases_cover_decision_priority(controller_fixture: dict) -> None:
    cases = controller_fixture["cases"]
    balanced = cases["balanced_go"]["artifact"]
    refinement = cases["balanced_refinement_stop"]["artifact"]
    zero = cases["balanced_zero_stop"]["artifact"]
    full_support = cases["full_support_threshold_fail"]["artifact"]
    missing = cases["missing_cell_threshold_fail"]["artifact"]
    fail_zero = cases["threshold_fail_with_zero_priority"]["artifact"]

    assert balanced["cell_counts"] == {
        "n0": 26, "n1": 26, "n2": 26, "n3": 26, "n4": 26,
        "n5": 26, "n6": 25, "n7": 25, "n8": 25, "n9": 25,
    }
    assert balanced["j"] == 6556
    assert 9 * balanced["j"] == 59004
    assert balanced["decision"]["window13_action"] == "go_holdouts"
    assert refinement["decision"]["window13_action"] == (
        "stop_determinant_route_pending_optional_refinement"
    )
    assert zero["decision"]["window13_action"] == "stop_audit_zero"
    assert all(full_support["cell_counts"][f"n{cell}"] > 0 for cell in range(10))
    assert full_support["j10_strict_pass"] is False
    assert missing["j"] == 7284
    assert 9 * missing["j"] == 65556
    assert missing["cell_counts"]["n9"] == 0
    assert fail_zero["decision"]["has_zero_distinct_pair"] is True
    assert fail_zero["decision"]["window13_action"] == "stop_local_conjecture"

    for case in cases.values():
        artifact = case["artifact"]
        assert len(artifact["points"]) == 256
        assert len(artifact["lag_counts"]) == 255
        assert artifact["j"] == 256 + 2 * artifact["decision"]["c_sum"]
        assert artifact["decision"]["a_sum"] == sum(
            row["near_determinant_count"] for row in artifact["lag_counts"]
        )


def test_t120_s0_hidden_families_are_seed_bound_and_replayable() -> None:
    first = oracle.build_controller_fixture(oracle.SPEC_BUNDLE_SHA256, "1" * 64)
    replay = oracle.build_controller_fixture(oracle.SPEC_BUNDLE_SHA256, "1" * 64)
    second = oracle.build_controller_fixture(oracle.SPEC_BUNDLE_SHA256, "2" * 64)
    assert oracle._exact_equal(first, replay)
    assert first["fixture_seed_sha256"] != second["fixture_seed_sha256"]
    assert not oracle._exact_equal(first["hidden_cases"], second["hidden_cases"])
    assert len(first["hidden_cases"]) == 4
    for case in first["hidden_cases"]:
        assert oracle._exact_equal(
            oracle.recompute_window(
                copy.deepcopy(case["points"]),
                case["window_index"],
                case["start_n"],
                case["end_exclusive_n"],
                oracle.SPEC_BUNDLE_SHA256,
            ),
            case["artifact"],
        )


def test_t120_s0_hidden_family_statistics_match_independent_bruteforce() -> None:
    fixture = oracle.build_controller_fixture(oracle.SPEC_BUNDLE_SHA256, "3" * 64)
    artifact = fixture["hidden_cases"][0]["artifact"]
    points = artifact["points"]
    numeric = [
        (point["n"], int(point["r"]), int(point["w"]), point["cell"])
        for point in points
    ]
    cells = [(10 * r) // w for _n, r, w, _cell in numeric]
    assert cells == [point["cell"] for point in points]
    counts = [cells.count(cell) for cell in range(10)]
    assert artifact["cell_counts"] == {
        f"n{cell}": counts[cell] for cell in range(10)
    }
    assert artifact["j"] == sum(count * count for count in counts)

    lag_rows = []
    maximum = None
    for lag in range(1, 256):
        c_count = a_count = z_count = 0
        for offset in range(256 - lag):
            left_n, left_r, left_w, left_cell = numeric[offset]
            right_n, right_r, right_w, right_cell = numeric[offset + lag]
            delta = left_r * right_w - right_r * left_w
            numerator = 10 * abs(delta)
            denominator = left_w * right_w
            if left_cell == right_cell:
                c_count += 1
                candidate = (
                    numerator, denominator, left_n, right_n, lag, left_cell
                )
                if maximum is None or (
                    numerator * maximum[1] > maximum[0] * denominator
                    or (
                        numerator * maximum[1] == maximum[0] * denominator
                        and (left_n, right_n) < (maximum[2], maximum[3])
                    )
                ):
                    maximum = candidate
            if numerator < denominator:
                a_count += 1
            if delta == 0:
                z_count += 1
        lag_rows.append(
            {
                "lag": lag,
                "same_cell_count": c_count,
                "near_determinant_count": a_count,
                "zero_determinant_count": z_count,
            }
        )
    assert artifact["lag_counts"] == lag_rows
    assert maximum is not None
    num, den, witness_n, witness_m, lag, cell = maximum
    assert artifact["maximum_determinant_ratio"] == {
        "num": str(num),
        "den": str(den),
        "witness_n": witness_n,
        "witness_m": witness_m,
        "lag": lag,
        "cell": cell,
    }


def test_t120_s0_maximum_ratio_uses_raw_cross_products_and_lexicographic_ties(
    controller_fixture: dict,
) -> None:
    expected = controller_fixture["cases"]["balanced_go"]["artifact"][
        "maximum_determinant_ratio"
    ]
    vectors = controller_fixture["ratio_mutation_vectors"]
    tied = vectors["equal_maximum_nonlex"]
    reduced = vectors["reduced_surrogate"]
    assert int(expected["num"]) * int(tied["den"]) == (
        int(tied["num"]) * int(expected["den"])
    )
    assert (expected["witness_n"], expected["witness_m"]) < (
        tied["witness_n"], tied["witness_m"]
    )
    assert (reduced["num"], reduced["den"]) != (expected["num"], expected["den"])

    precision = controller_fixture["cases"]["precision_cross_product"]["artifact"][
        "maximum_determinant_ratio"
    ]
    loser = controller_fixture["precision_ratio_loser"]
    assert int(loser["num"]) * int(precision["den"]) < (
        int(precision["num"]) * int(loser["den"])
    )
    assert float(loser["num"]) / float(loser["den"]) == (
        float(precision["num"]) / float(precision["den"])
    )


@pytest.mark.parametrize(
    "raw",
    [
        b'{"a":1,"a":2}\n',
        b'{"a":{"x":1,"x":2}}\n',
        b'{"a":1.0}\n',
        b'{"a":1e0}\n',
        b'{"a":NaN}\n',
        b'\xef\xbb\xbf{}\n',
        b'{"a":"\xff"}\n',
        b'{}\r\n',
        b'{}',
        b'{}\n\n',
        b' {}\n',
        b'{ }\n',
        b'{"a":-0}\n',
        b'{"a":"\\/"}\n',
    ],
)
def test_t120_s0_oracle_rejects_noncanonical_raw_bytes(raw: bytes) -> None:
    with pytest.raises(ValueError):
        oracle.decode_canonical_json(raw)


def test_t120_s0_deep_parser_failure_is_valueerror() -> None:
    raw = b"[" * 5000 + b"0" + b"]" * 5000 + b"\n"
    with pytest.raises(ValueError):
        oracle.decode_canonical_json(raw)


def test_t120_s0_harness_counts_only_valueerror_as_rejection() -> None:
    from workflows.modelbench import t120_s0_controller_harness as harness

    with pytest.raises(AssertionError, match="mutation accepted"):
        harness._rejects(lambda: False, label="silent False is not rejection")
    with pytest.raises(AssertionError, match="not ValueError"):
        harness._rejects(
            lambda: (_ for _ in ()).throw(RuntimeError("wrong exception")),
            label="RuntimeError is not rejection",
        )


def test_t120_s0_exact_type_collection_and_depth_limits() -> None:
    class IntSubclass(int):
        pass

    for value in ((1, 2), {1, 2}, bytearray(b"x"), memoryview(b"x"), IntSubclass(1)):
        with pytest.raises(ValueError):
            oracle.canonical_json_bytes(value)
    assert oracle.decode_canonical_json(
        oracle.canonical_json_bytes([0] * oracle.JSON_MAX_ARRAY_ITEMS)
    ) == [0] * oracle.JSON_MAX_ARRAY_ITEMS
    with pytest.raises(ValueError, match="array"):
        oracle.canonical_json_bytes([0] * (oracle.JSON_MAX_ARRAY_ITEMS + 1))
    exact_depth: object = 0
    for _ in range(oracle.JSON_MAX_NESTING_DEPTH):
        exact_depth = [exact_depth]
    assert oracle.decode_canonical_json(oracle.canonical_json_bytes(exact_depth)) == exact_depth
    with pytest.raises(ValueError, match="nesting"):
        oracle.canonical_json_bytes([exact_depth])


def test_t120_s0_oracle_discards_candidate_summaries(controller_fixture: dict) -> None:
    artifact = copy.deepcopy(controller_fixture["cases"]["balanced_go"]["artifact"])
    mutations = [
        ("j", artifact["j"] + 2),
        ("j10_strict_pass", not artifact["j10_strict_pass"]),
    ]
    for key, replacement in mutations:
        changed = copy.deepcopy(artifact)
        changed[key] = replacement
        with pytest.raises(ValueError, match="trusted recomputation"):
            oracle.validate_window_bytes(
                oracle.canonical_json_bytes(changed),
                13,
                3840,
                4096,
                oracle.SPEC_BUNDLE_SHA256,
            )


def test_t120_s0_cas_and_receipt_expected_bindings_are_exact_subsets(
    controller_fixture: dict,
) -> None:
    assert set(controller_fixture["cas_expected_bindings"]) == {
        "artifact_sha256", "size_bytes", "experiment_id", "spec_bundle_sha256",
        "window_index", "start_n", "end_exclusive_n",
    }
    assert set(controller_fixture["receipt_expected_bindings"]) == {
        "experiment_id", "spec_bundle_sha256", "window_index", "start_n",
        "end_exclusive_n", "artifact_sha256", "generator_source_sha256",
        "verifier_source_sha256", "verifier_result", "controller_gate_id",
    }
    cas = copy.deepcopy(controller_fixture["cas_record"])
    cas_expected = copy.deepcopy(controller_fixture["cas_expected_bindings"])
    cas["artifact_sha256"] = "3" * 64
    with pytest.raises(ValueError, match="controller-supplied"):
        oracle.validate_cas_record(cas, cas_expected)
    cas_expected["schema"] = oracle.CAS_SCHEMA
    with pytest.raises(ValueError, match="exact key set"):
        oracle.validate_cas_record(controller_fixture["cas_record"], cas_expected)

    receipt = copy.deepcopy(controller_fixture["receipt"])
    receipt["controller_gate_id"] = oracle.GATE_ID
    matched = {key: receipt[key] for key in controller_fixture["receipt_expected_bindings"]}
    with pytest.raises(ValueError, match="not a production receipt authority"):
        oracle.validate_receipt(receipt, matched)


def test_t120_s0_static_gate_accepts_pure_reference(tmp_path: Path) -> None:
    candidate = tmp_path / gate.SOURCE_FILE
    candidate.write_text(_reference_candidate_source(), encoding="utf-8")
    gate.static_schema_check(candidate)


@pytest.mark.parametrize(
    "source,match",
    [
        (
            "import os\n" + "\n".join(
                f"def {name}(*a): return None" for name in sorted(gate.REQUIRED_API)
            ),
            "unapproved modules|forbidden capability",
        ),
        ("def canonical_json_bytes(value): return open('x')\n", "wrong exact|forbidden"),
        ("def canonical_json_bytes(value): return 1 / 2\n", "wrong exact|true division"),
        ("def canonical_json_bytes(value): return 2 ** -1\n", "wrong exact|exponentiation"),
        ("def canonical_json_bytes(value): return value.__class__\n", "wrong exact|reflective"),
        ("def canonical_json_bytes(value): return 0.5\n", "wrong exact|floating-point"),
        ("_state = []\n", "mutable or computed module state"),
        ("print('import effect')\n", "executable top-level effects"),
        (
            "class _Bad(ValueError):\n    print('class effect')\n",
            "class body has import-time effects",
        ),
        ("def compute_bbp_term(value): return value\n", "wrong exact|production arithmetic"),
        (
            "\n".join(f"def {name}(*a): return None" for name in sorted(gate.REQUIRED_API))
            + "\ndef extra_authority(): return True\n",
            "wrong exact public",
        ),
    ],
)
def test_t120_s0_static_gate_rejects_boundary_crossings(
    tmp_path: Path, source: str, match: str
) -> None:
    candidate = tmp_path / gate.SOURCE_FILE
    candidate.write_text(source + "\n", encoding="utf-8")
    with pytest.raises(gate.S0GateError, match=match):
        gate.static_schema_check(candidate)


def test_t120_s0_source_size_boundary_is_inclusive(tmp_path: Path) -> None:
    base = _reference_candidate_source().encode("utf-8")
    assert len(base) < gate.CANDIDATE_SOURCE_MAX_BYTES
    boundary = base + b"#" + b"x" * (gate.CANDIDATE_SOURCE_MAX_BYTES - len(base) - 2) + b"\n"
    assert len(boundary) == gate.CANDIDATE_SOURCE_MAX_BYTES
    candidate = tmp_path / gate.SOURCE_FILE
    candidate.write_bytes(boundary)
    gate.static_schema_check(candidate)
    candidate.write_bytes(boundary + b"#")
    with pytest.raises(gate.S0GateError, match="source exceeds"):
        gate.static_schema_check(candidate)


def test_t120_s0_report_contract_and_size_boundary(tmp_path: Path) -> None:
    report = tmp_path / gate.REPORT_FILE
    base = _valid_report().encode("utf-8")
    boundary = base[:-1] + b"x" * (gate.REPORT_MAX_BYTES - len(base)) + b"\n"
    assert len(boundary) == gate.REPORT_MAX_BYTES
    report.write_bytes(boundary)
    gate._validate_report(report)
    report.write_bytes(boundary + b"x")
    with pytest.raises(gate.S0GateError, match="REPORT.md exceeds"):
        gate._validate_report(report)

    for bad in (
        "bounded validation\n",
        _valid_report().replace("deferred", "checked here"),
        _valid_report() + "PASS\n",
        _valid_report() + "A production result exists.\n",
        _valid_report() + "A CAS object exists.\n",
        _valid_report() + "Pi is resolved.\n",
    ):
        report.write_text(bad, encoding="utf-8")
        with pytest.raises(gate.S0GateError):
            gate._validate_report(report)


def test_t120_s0_candidate_file_boundary_rejects_extra_symlink_and_special(
    tmp_path: Path,
) -> None:
    _write_candidate(tmp_path)
    (tmp_path / "extra.txt").write_text("candidate output\n", encoding="utf-8")
    with pytest.raises(gate.S0GateError, match="undeclared candidate deliverable"):
        gate._safe_candidate_files(tmp_path)
    (tmp_path / "extra.txt").unlink()

    (tmp_path / "receipt.json").write_text("{}\n", encoding="utf-8")
    with pytest.raises(gate.S0GateError, match="forbidden candidate deliverable"):
        gate._safe_candidate_files(tmp_path)
    (tmp_path / "receipt.json").unlink()

    (tmp_path / "link.py").symlink_to(tmp_path / gate.SOURCE_FILE)
    with pytest.raises(gate.S0GateError, match="symlink"):
        gate._safe_candidate_files(tmp_path)
    (tmp_path / "link.py").unlink()

    if hasattr(os, "mkfifo"):
        os.mkfifo(tmp_path / "pipe")
        with pytest.raises(gate.S0GateError, match="special file"):
            gate._safe_candidate_files(tmp_path)


def test_t120_s0_controller_owned_work_files_are_ignored(tmp_path: Path) -> None:
    _write_candidate(tmp_path)
    (tmp_path / "AGENTS.md").write_text("controller guidance\n", encoding="utf-8")
    (tmp_path / "TASK_CONTRACT.md").write_text("controller contract\n", encoding="utf-8")
    (tmp_path / "inputs").mkdir()
    (tmp_path / "inputs" / "fixture.json").write_text("{}\n", encoding="utf-8")
    (tmp_path / "inputs" / "receipt.json").write_text("{}\n", encoding="utf-8")
    gate._safe_candidate_files(tmp_path)


def test_t120_s0_isolated_command_uses_exact_limits_mounts_and_immutable_image(
    tmp_path: Path,
) -> None:
    candidate = tmp_path / "candidate" / gate.SOURCE_FILE
    harness = tmp_path / "controller" / "controller_harness.py"
    fixture = tmp_path / "fixture" / "controller_fixture.json"
    for path in (candidate, harness, fixture):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("x\n", encoding="utf-8")
    command = gate._isolated_command(candidate, harness, fixture, IMMUTABLE_IMAGE)
    assert command.count(IMMUTABLE_IMAGE) == 1
    assert gate.CONTROLLER_IMAGE_TAG not in command
    assert command[command.index("--network") + 1] == "none"
    assert "--read-only" in command
    assert command[command.index("--pids-limit") + 1] == str(gate.ISOLATED_PIDS)
    assert command[command.index("--cpus") + 1] == str(gate.ISOLATED_CPUS)
    assert command[command.index("--memory") + 1] == str(gate.ISOLATED_MEMORY_BYTES)
    assert command[command.index("--timeout") + 1] == str(gate.ISOLATED_TIMEOUT_SECONDS)
    mounts = [command[index + 1] for index, item in enumerate(command) if item == "-v"]
    assert len(mounts) == 3
    assert all(mount.endswith(":ro") for mount in mounts)
    assert len({mount.split(":", 1)[0] for mount in mounts}) == 3
    with pytest.raises(gate.S0GateError, match="immutable ID"):
        gate._require_immutable_image(gate.CONTROLLER_IMAGE_TAG)
    with pytest.raises(gate.S0GateError, match="immutable ID"):
        gate._require_immutable_image("A" * 64)


def test_t120_s0_controller_harness_runs_comprehensive_mutations(
    tmp_path: Path, controller_fixture: dict
) -> None:
    candidate = tmp_path / gate.SOURCE_FILE
    fixture = tmp_path / "controller_fixture.json"
    candidate.write_text(_reference_candidate_source(), encoding="utf-8")
    _write_fixture(fixture, controller_fixture)
    completed = _run_host_harness(candidate, fixture)
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "T120_S0_CONTROLLER_MUTATIONS_PASSED" in completed.stdout
    assert int(completed.stdout.strip().rsplit(":", 1)[1]) >= 360


@pytest.mark.parametrize(
    "extra_source",
    [
        (
            "import json\n"
            "def canonical_json_bytes(value): return json.dumps(value).encode() + b'\\n'\n"
            "def decode_canonical_json(raw): return json.loads(raw)\n"
            "def validate_point(value, expected_n): return value\n"
            "def recompute_window(points, *args): return {}\n"
            "def validate_window_bytes(raw, *args): return None\n"
            "def validate_cas_record(value, expected_bindings): return None\n"
            "def validate_receipt(value, expected_bindings): return None\n"
        ),
        _reference_candidate_source() + "\ndef extra_public(): return True\n",
    ],
)
def test_t120_s0_controller_harness_rejects_permissive_or_extra_api(
    tmp_path: Path, controller_fixture: dict, extra_source: str
) -> None:
    candidate = tmp_path / gate.SOURCE_FILE
    fixture = tmp_path / "controller_fixture.json"
    candidate.write_text(extra_source, encoding="utf-8")
    _write_fixture(fixture, controller_fixture)
    completed = _run_host_harness(candidate, fixture)
    assert completed.returncode != 0
    assert "T120_S0_CONTROLLER_MUTATIONS_PASSED" not in completed.stdout


def test_t120_s0_run_gate_host_integration_and_image_propagation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    candidate = _write_candidate(tmp_path)
    seen: list[tuple[Path, str]] = []

    def run_host(path: Path, *, image: str, controller_provenance: dict) -> tuple[str, str]:
        assert controller_provenance == runner.t120_s0_controller_provenance()
        seen.append((path, image))
        fixture = tmp_path / "host-controller-fixture.json"
        gate._write_controller_fixture(fixture, FIXTURE_SEED)
        completed = _run_host_harness(path, fixture)
        fixture.unlink()
        if completed.returncode != 0:
            raise gate.S0GateError(completed.stdout + completed.stderr)
        return FIXTURE_SEED, runner.t120_s0_controller_provenance()["bundle_sha256"]

    monkeypatch.setattr(gate, "_run_isolated", run_host)
    from workflows.modelbench import runner

    passed, reason = gate.run_gate(
        tmp_path,
        {},
        controller_image=IMMUTABLE_IMAGE,
        controller_provenance=runner.t120_s0_controller_provenance(),
    )
    assert passed is True, reason
    assert "passed strict bytes" in reason
    assert f"fixture_seed={FIXTURE_SEED}" in reason
    assert "controller_bundle_sha256=" in reason
    assert seen == [(candidate, IMMUTABLE_IMAGE)]


def test_t120_s0_run_gate_rejects_mutable_or_missing_image(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _write_candidate(tmp_path)
    monkeypatch.setattr(gate, "_run_isolated", lambda *args, **kwargs: None)
    for image in (None, gate.CONTROLLER_IMAGE_TAG, "A" * 64):
        passed, reason = gate.run_gate(
            tmp_path, {}, controller_image=image, controller_provenance={}
        )
        assert passed is False
        assert "immutable ID" in reason


def test_artifact_contract_dispatches_t120_with_resolved_image(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner_path = gate.ROOT / "workflows" / "modelbench" / "runner.py"
    if not runner_path.is_file():
        pytest.skip("partial checkout does not contain runner.py")
    from workflows.modelbench import runner

    (tmp_path / gate.SOURCE_FILE).write_text("schema", encoding="utf-8")
    called: list[tuple[Path, str, str]] = []

    def fake_gate(
        work_dir: Path,
        grading: dict,
        *,
        controller_image: str | None = None,
        controller_provenance: dict | None = None,
    ) -> tuple[bool, str]:
        assert controller_provenance == runner.t120_s0_controller_provenance()
        called.append((work_dir, grading["controller_gate"], str(controller_image)))
        return True, "T120 fixed gate passed"

    monkeypatch.setattr(gate, "run_gate", fake_gate)
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": gate.SOURCE_FILE,
            "controller_gate": gate.GATE_ID,
        }
    }
    assert runner.grade(
        task,
        "",
        tmp_path,
        tmp_path,
        controller_image=IMMUTABLE_IMAGE,
    ) == (True, "T120 fixed gate passed")
    assert called == [(tmp_path, gate.GATE_ID, IMMUTABLE_IMAGE)]


def test_artifact_contract_rejects_controller_source_drift_as_infrastructure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from workflows.modelbench import runner

    (tmp_path / gate.SOURCE_FILE).write_text("schema\n", encoding="utf-8")
    changed = dict(runner.T120_S0_CONTROLLER_RAW_SHA256)
    changed["t120_s0_controller_harness.py"] = "0" * 64
    monkeypatch.setattr(runner, "T120_S0_CONTROLLER_RAW_SHA256", changed)
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": gate.SOURCE_FILE,
            "controller_gate": gate.GATE_ID,
        }
    }
    passed, reason = runner.grade(
        task,
        "",
        tmp_path,
        tmp_path,
        controller_image=IMMUTABLE_IMAGE,
    )
    assert passed is False
    assert reason.startswith("non-repairable infrastructure failure:")
    assert "controller source hash mismatch" in reason


def test_t120_s0_podman_gate_when_available(tmp_path: Path) -> None:
    if shutil.which("podman") is None:
        pytest.skip("podman unavailable")
    inspect = subprocess.run(
        ["podman", "image", "inspect", "--format", "{{.Id}}", gate.CONTROLLER_IMAGE_TAG],
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    if inspect.returncode != 0:
        pytest.skip(f"controller image unavailable: {gate.CONTROLLER_IMAGE_TAG}")
    image_id = inspect.stdout.strip().removeprefix("sha256:")
    if gate.IMMUTABLE_IMAGE_RE.fullmatch(image_id) is None:
        pytest.skip("local controller image did not resolve to a 64-hex ID")
    _write_candidate(tmp_path)
    from workflows.modelbench import runner

    passed, reason = gate.run_gate(
        tmp_path,
        {},
        controller_image=image_id,
        controller_provenance=runner.t120_s0_controller_provenance(),
    )
    assert passed is True, reason


def test_t120_s0_controller_sources_are_runner_bound_and_copy_rechecked(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from workflows.modelbench import runner

    provenance = runner.t120_s0_controller_provenance()
    expected = gate._validate_controller_provenance(provenance)
    copied = gate._copy_controller_snapshot(tmp_path / "snapshot", expected)
    assert set(copied) == set(runner.T120_S0_CONTROLLER_RAW_SHA256)
    for name, path in copied.items():
        assert sha256(path.read_bytes()).hexdigest() == expected[name]

    altered = tmp_path / gate.HARNESS_PATH.name
    altered.write_bytes(gate.HARNESS_PATH.read_bytes() + b"# drift\n")
    monkeypatch.setattr(gate, "HARNESS_PATH", altered)
    with pytest.raises(gate.S0GateError, match="controller source hash mismatch"):
        gate._validate_controller_provenance(provenance)
