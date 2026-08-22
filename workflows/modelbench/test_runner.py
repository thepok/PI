from pathlib import Path
import json
import os
import shutil
import subprocess
import time

import pytest

from workflows.modelbench import runner
from workflows.modelbench import t117_controller_gate


def test_sandbox_api_is_repository_local() -> None:
    sandbox_config, prepare, finalize = runner._sandbox_api()

    assert sandbox_config.__module__ == "workflows.runtime.sandbox"
    assert prepare.__module__ == "workflows.runtime.sandbox"
    assert finalize.__module__ == "workflows.runtime.sandbox"


def test_artifact_contract_requires_declared_support_files(tmp_path: Path) -> None:
    (tmp_path / "EXPERIMENT.md").write_text(
        "Exact replay\nCollision witnesses\n" + "x" * 100,
        encoding="utf-8",
    )
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": "EXPERIMENT.md",
            "min_chars": 50,
            "required_markers": ["Exact replay", "Collision witnesses"],
            "required_files": ["replay.py", "epochs.csv"],
        }
    }

    passed, reason = runner.grade(task, "", tmp_path, tmp_path)

    assert passed is False
    assert reason == "artifact missing required files ['replay.py', 'epochs.csv']"


def test_artifact_contract_rejects_placeholder_markers(tmp_path: Path) -> None:
    (tmp_path / "EXPERIMENT.md").write_text(
        "Exact replay\nFirst collisions\n(filled after the run)\n" + "x" * 100,
        encoding="utf-8",
    )
    (tmp_path / "replay.py").write_text("print('ok')\n", encoding="utf-8")
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": "EXPERIMENT.md",
            "min_chars": 50,
            "required_markers": ["Exact replay", "First collisions"],
            "required_files": ["replay.py"],
            "forbidden_markers": ["filled after the run", "TODO"],
        }
    }

    passed, reason = runner.grade(task, "", tmp_path, tmp_path)

    assert passed is False
    assert reason == "artifact contains forbidden markers ['filled after the run']"


def test_artifact_contract_checks_json_values_and_ordered_sequences(
    tmp_path: Path,
) -> None:
    (tmp_path / "RESULT.md").write_text("exact result", encoding="utf-8")
    (tmp_path / "census.json").write_text(
        json.dumps({"records": [{"n": 0, "q_num": "47"}, {"n": 1}]}),
        encoding="utf-8",
    )
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": "RESULT.md",
            "required_files": ["census.json"],
            "required_json_values": [
                {
                    "file": "census.json",
                    "path": ["records", 0, "q_num"],
                    "equals": "47",
                }
            ],
            "required_json_sequences": [
                {
                    "file": "census.json",
                    "path": ["records"],
                    "key": "n",
                    "start": 0,
                    "end": 1,
                }
            ],
        }
    }

    assert runner.grade(task, "", tmp_path, tmp_path) == (
        True,
        "artifact contract satisfied; quality review still required",
    )

    (tmp_path / "census.json").write_text(
        json.dumps({"records": [{"n": 1, "q_num": "47"}, {"n": 0}]}),
        encoding="utf-8",
    )
    passed, reason = runner.grade(task, "", tmp_path, tmp_path)
    assert passed is False
    assert reason == (
        "JSON artifact census.json does not contain exact ordered n range 0..1"
    )


def test_t117_trusted_oracle_has_scaled_anchors_and_normalized_hidden_record() -> None:
    zero = t117_controller_gate.trusted_record(0)
    one = t117_controller_gate.trusted_record(1)
    hidden = t117_controller_gate.trusted_record(4)

    assert (zero["q_num"], zero["q_den"]) == ("47", "15")
    assert (one["q_num"], one["q_den"]) == (
        "16331158360096799798177512637",
        "519836915885323158521118720",
    )
    assert hidden["n"] == 4
    assert hidden["tuple"]["k"] == hidden["k"]
    assert hidden["tuple"]["e"] == hidden["e"]
    assert int(hidden["tuple"]["g"]) == int(hidden["tuple"]["H"]) * int(hidden["k"])


def _valid_t117_contract() -> dict:
    return {
        "schema": "t117-normalized-census-contract-v1",
        "workflow": "t117-normalized-census",
        "status": "experiment",
        "q_definition": "Q_N=10^N*S_N",
        "anchors": {
            "Q_0": "47/15",
            "Q_1": (
                "16331158360096799798177512637/"
                "519836915885323158521118720"
            ),
        },
        "laws": {"K1": "k^2<=e", "K2": "k^2<=d*e"},
        "census": {"start_n": 512, "end_exclusive_n": 4096},
        "shards": t117_controller_gate.expected_shard_table(),
        "additional_operational_field": {"allowed": True},
    }


def test_t117_contract_accepts_exact_42_shard_partition() -> None:
    contract = _valid_t117_contract()

    t117_controller_gate.validate_contract(contract)

    assert [row["index"] for row in contract["shards"]] == list(range(42))


@pytest.mark.parametrize("mutation", ["width", "gap", "reorder"])
def test_t117_contract_rejects_malformed_shard_partition(mutation: str) -> None:
    contract = _valid_t117_contract()
    if mutation == "width":
        contract["shards"][0]["end_exclusive_n"] = 769
    elif mutation == "gap":
        contract["shards"][1]["start_n"] = 769
    else:
        contract["shards"][0], contract["shards"][1] = (
            contract["shards"][1],
            contract["shards"][0],
        )

    with pytest.raises(
        t117_controller_gate.ControllerGateError,
        match="width/gap/order",
    ):
        t117_controller_gate.validate_contract(contract)


def test_t117_gate_rejects_archived_unscaled_sequential_candidate() -> None:
    archived = runner.ROOT / (
        "workflows/state/runs/t117-wave-a-ox-workflow-r0/work/"
        "ox-pi-t117-normalized-census-workflow"
    )
    passed, reason = t117_controller_gate.run_gate(archived, {})

    assert passed is False
    assert "unscaled sampled value assignment Q = S" in reason


def test_artifact_contract_dispatches_fixed_t117_controller_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "README.md").write_text("controller", encoding="utf-8")
    called = []

    def fake_gate(work_dir: Path, grading: dict) -> tuple[bool, str]:
        called.append((work_dir, grading["controller_gate"]))
        return True, "fixed gate passed"

    monkeypatch.setattr(t117_controller_gate, "run_gate", fake_gate)
    task = {
        "grading": {
            "type": "artifact_contract",
            "artifact": "README.md",
            "controller_gate": "t117_normalized_census_v1",
        }
    }

    assert runner.grade(task, "", tmp_path, tmp_path) == (True, "fixed gate passed")
    assert called == [(tmp_path, "t117_normalized_census_v1")]


def test_t117_probe_requires_both_exact_routes_and_independent_shard() -> None:
    records = [t117_controller_gate.trusted_record(n) for n in (0, 1, 3)]
    probe = {
        "schema": t117_controller_gate.PROBE_SCHEMA,
        "contract_sha256": "a" * 64,
        "generator": records,
        "verifier": records,
        "shard1_without_shard0": True,
    }
    t117_controller_gate._validate_probe(
        probe, expected_records=records, contract_sha256="a" * 64
    )

    probe["verifier"] = [*records[:-1], t117_controller_gate.trusted_record(2)]
    with pytest.raises(t117_controller_gate.ControllerGateError, match="verifier"):
        t117_controller_gate._validate_probe(
            probe, expected_records=records, contract_sha256="a" * 64
        )


def test_lean_artifact_contract_rejects_canonical_definition_replacement(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "Contribution.lean").write_text(
        "import Canonical.T92\n"
        "def ThreeLocalCongruent := True\n"
        "theorem bridge : True := by trivial\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (True, "compiled; axioms clean"),
    )
    task = {
        "grading": {
            "type": "agentic_lean_artifact",
            "artifact": "Contribution.lean",
            "required_markers": ["import Canonical.T92"],
            "forbidden_markers": ["def ThreeLocalCongruent"],
        }
    }

    passed, reason = runner.grade(task, "", tmp_path, tmp_path)

    assert passed is False
    assert reason == (
        "Lean artifact contains forbidden markers ['def ThreeLocalCongruent']"
    )


def _strict_lean_task(name: str = "OxGateNovel.target") -> dict:
    return {
        "grading": {
            "type": "agentic_lean_artifact",
            "artifact": "Contribution.lean",
            "theorem_names": [name],
            "expected_types": {name: "True"},
            "allowed_imports": ["Mathlib"],
            "required_imports": ["Mathlib"],
            "required_markers": ["theorem target"],
        }
    }


def test_lean_artifact_rejects_marker_and_declaration_spoofed_in_comment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "Contribution.lean").write_text(
        "import Mathlib\n/- theorem target : True := by trivial -/\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("spoof reached the Lean gate")
        ),
    )

    passed, reason = runner.grade(
        _strict_lean_task(), "", tmp_path, tmp_path
    )

    assert passed is False
    assert reason == "Lean artifact missing markers ['theorem target']"


def test_lean_artifact_rejects_preexisting_target_without_local_declaration(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    name = (
        "Theory.PiDigits.T106BBPForcedOrbit."
        "sampledBBPForcing_eq_cast_rat"
    )
    (tmp_path / "Contribution.lean").write_text(
        "import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit\n"
        "theorem unrelated : True := by trivial\n",
        encoding="utf-8",
    )
    task = _strict_lean_task(name)
    task["grading"]["allowed_imports"] = [
        "TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit"
    ]
    task["grading"]["required_imports"] = task["grading"]["allowed_imports"]
    task["grading"]["required_markers"] = []
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("preexisting theorem reached the Lean gate")
        ),
    )

    passed, reason = runner.grade(task, "", tmp_path, tmp_path)

    assert passed is False
    assert "does not locally declare" in reason


def test_lean_artifact_rejects_unapproved_import(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "Contribution.lean").write_text(
        "import Mathlib\nimport TheoryLib\n"
        "namespace OxGateNovel\n"
        "theorem target : True := by trivial\n"
        "end OxGateNovel\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(runner, "trusted_tree_declares_theorem", lambda _name: False)
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("unapproved import reached the Lean gate")
        ),
    )

    passed, reason = runner.grade(
        _strict_lean_task(), "", tmp_path, tmp_path
    )

    assert passed is False
    assert reason == "Lean artifact imports unapproved modules ['TheoryLib']"


def test_lean_artifact_rejects_helper_outside_contracted_namespace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "Contribution.lean").write_text(
        "import Mathlib\n"
        "namespace Trusted\n"
        "def alias : True := True.intro\n"
        "end Trusted\n"
        "namespace OxGateNovel\n"
        "theorem target : True := by trivial\n"
        "end OxGateNovel\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(runner, "trusted_tree_declares_theorem", lambda _name: False)
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("namespace escape reached the Lean gate")
        ),
    )

    passed, reason = runner.grade(
        _strict_lean_task(), "", tmp_path, tmp_path
    )

    assert passed is False
    assert reason == (
        "artifact declares helpers outside contracted namespaces "
        "[('Trusted', 'alias')]"
    )


def test_lean_artifact_allows_helpers_inside_contracted_namespace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "Contribution.lean").write_text(
        "import Mathlib\n"
        "namespace OxGateNovel\n"
        "private lemma helper : True := by trivial\n"
        "theorem target : True := helper\n"
        "end OxGateNovel\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(runner, "trusted_tree_declares_theorem", lambda _name: False)
    monkeypatch.setattr(
        runner,
        "grade_lean_gate",
        lambda *_args, **_kwargs: (True, "compiled; axioms clean"),
    )

    passed, reason = runner.grade(
        _strict_lean_task(), "", tmp_path, tmp_path
    )

    assert passed is True
    assert reason == "compiled; axioms clean"


def test_lean_gate_rejects_metaprogram_before_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(
        runner.subprocess,
        "run",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("metaprogram was executed")
        ),
    )
    response = "```lean\nimport Mathlib\nrun_cmd IO.println \"owned\"\n```"

    passed, reason = runner.grade_lean_gate(
        response, {"theorem_names": []}, tmp_path
    )

    assert passed is False
    assert reason.startswith("forbidden token")


def test_lean_gate_appends_exact_type_contract_and_never_host_preflights(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = tmp_path / "project"
    (project / "TheoryLib").mkdir(parents=True)
    for name in ("TheoryLib.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        (project / name).write_text("\n", encoding="utf-8")
    monkeypatch.setattr(runner, "ROOT", project)
    observed: list[list[str]] = []

    def fake_run(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess[str]:
        observed.append(command)
        candidate = tmp_path / "lean_gate" / "candidate.lean"
        text = candidate.read_text(encoding="utf-8")
        assert "example : True := by exact @OxGateNovel.target" in text
        return subprocess.CompletedProcess(
            command, 0,
            stdout="'OxGateNovel.target' does not depend on any axioms\n",
            stderr="",
        )

    monkeypatch.setattr(runner.subprocess, "run", fake_run)
    response = (
        "```lean\nimport Mathlib\nnamespace OxGateNovel\n"
        "theorem target : True := by trivial\nend OxGateNovel\n```"
    )

    passed, reason = runner.grade_lean_gate(
        response,
        {
            "theorem_names": ["OxGateNovel.target"],
            "expected_types": {"OxGateNovel.target": "True"},
        },
        tmp_path,
    )

    assert passed is True
    assert reason == "compiled; axioms clean"
    assert len(observed) == 1
    assert observed[0][:4] == ["podman", "run", "--rm", "--network"]
    assert observed[0][observed[0].index("--tmpfs") + 1] == runner.LEAN_GATE_TMPFS


def test_lean_gate_does_not_accept_suffix_axiom_result(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = tmp_path / "project"
    (project / "TheoryLib").mkdir(parents=True)
    for name in ("TheoryLib.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        (project / name).write_text("\n", encoding="utf-8")
    monkeypatch.setattr(runner, "ROOT", project)
    monkeypatch.setattr(
        runner.subprocess,
        "run",
        lambda command, **_kwargs: subprocess.CompletedProcess(
            command, 0,
            stdout="'Evil.OxGateNovel.target' does not depend on any axioms\n",
            stderr="",
        ),
    )

    passed, reason = runner.grade_lean_gate(
        "```lean\nimport Mathlib\ntheorem target : True := by trivial\n```",
        {
            "theorem_names": ["OxGateNovel.target"],
            "expected_types": {"OxGateNovel.target": "True"},
        },
        tmp_path,
    )

    assert passed is False
    assert reason == "theorem OxGateNovel.target not found in axiom report"


def test_cross_process_model_slot_exits_when_cancelled(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    cancel_file = tmp_path / "cancel"
    cancel_file.touch()

    with pytest.raises(runner.ModelSlotUnavailable, match="cancelled"):
        with runner.cross_process_model_slot("ox", cancel_file=cancel_file):
            pass


def test_cross_process_model_slot_has_bounded_wait(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")

    def always_busy(*_args: object, **_kwargs: object) -> None:
        raise BlockingIOError

    monkeypatch.setattr(runner.fcntl, "flock", always_busy)

    with pytest.raises(runner.ModelSlotUnavailable, match="timed out"):
        with runner.cross_process_model_slot(
            "ox", wait_timeout_s=0.01, poll_interval_s=0.001
        ):
            pass


def test_provider_slot_status_reads_the_runner_lock_state(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")

    with runner.cross_process_model_slot("ox") as held_slot:
        status = runner.provider_slot_status(["ox"])["ox"]

    assert status["capacity"] == 4
    assert status["occupied_slots"] == [held_slot]
    assert status["available_slots"] == [
        slot
        for slot in range(runner.MODEL_CALL_CAPACITIES["ox"])
        if slot != held_slot
    ]


def test_native_ox_provider_has_ten_independent_slots(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")

    status = runner.provider_slot_status(["ox", "oxzen"])

    assert status["ox"]["capacity"] == 4
    assert status["oxzen"]["capacity"] == 10
    assert status["oxzen"]["available_slots"] == list(range(10))


def test_active_model_call_is_terminated_and_partial_trace_is_preserved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    cancellation = runner.Cancellation()
    created: list[object] = []
    terminated: list[object] = []

    class FakeProcess:
        pid = 12345
        returncode: int | None = None

        def __init__(self, *_args: object, **kwargs: object) -> None:
            assert kwargs["start_new_session"] is True
            created.append(self)
            self.communicate_calls = 0

        def communicate(self, timeout: float | None = None) -> tuple[str, str]:
            self.communicate_calls += 1
            if self.communicate_calls == 1:
                cancellation.request("test cancellation")
                raise subprocess.TimeoutExpired("opencode", timeout or 0.25)
            return (
                '{"type":"text","part":{"text":"partial result"}}\n',
                "",
            )

    def fake_terminate(proc: object, grace_s: float = 5.0) -> None:
        del grace_s
        terminated.append(proc)
        proc.returncode = -15  # type: ignore[attr-defined]

    monkeypatch.setattr(runner.subprocess, "Popen", FakeProcess)
    monkeypatch.setattr(runner, "terminate_owned_process", fake_terminate)

    outcome = runner.run_model(
        "ox", "prompt", tmp_path, timeout_s=60, cancellation=cancellation
    )

    assert terminated == created
    assert outcome["error"] == "cancelled (test cancellation)"
    assert outcome["response"] == "partial result"
    assert "partial result" in outcome["trace"]


def test_owned_process_shutdown_targets_its_private_group(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    signals: list[tuple[int, int]] = []

    class FakeProcess:
        pid = 24680

        def poll(self) -> None:
            return None

        def wait(self, timeout: float | None = None) -> int:
            assert timeout == 5.0
            return -15

        def terminate(self) -> None:
            raise AssertionError("did not use the owned process group")

    monkeypatch.setattr(
        runner.os, "killpg", lambda pid, sig: signals.append((pid, sig))
    )

    runner.terminate_owned_process(FakeProcess())  # type: ignore[arg-type]

    assert signals == [(24680, runner.signal.SIGTERM)]


def test_cancelled_artifact_is_preserved_without_running_the_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    cancellation = runner.Cancellation()

    def fake_run_model(
        _model_key: str, _prompt: str, bench_dir: Path, **_kwargs: object
    ) -> dict[str, object]:
        (bench_dir / "Contribution.lean").write_text(
            "theorem partial : True := by trivial\n", encoding="utf-8"
        )
        cancellation.request("retired wave")
        return {
            "response": "partial response",
            "trace": '{"type":"text","part":{"text":"partial response"}}',
            "error": cancellation.error(),
            "duration_s": 0.0,
        }

    def gate_must_not_run(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("cancellation started an expensive Lean gate")

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    monkeypatch.setattr(runner, "grade", gate_must_not_run)
    task = {
        "id": "cancel-active-artifact",
        "prompt": "prompt",
        "dimension": "lean_research",
        "grading": {
            "type": "agentic_lean_artifact",
            "artifact": "Contribution.lean",
        },
    }

    entry = runner.run_pair(
        "ox",
        task,
        tmp_path / "out",
        tmp_path / "bench",
        cancellation=cancellation,
    )
    work = tmp_path / "out" / "work" / "ox-cancel-active-artifact"

    assert entry["passed"] is False
    assert entry["reason"] == "cancelled (retired wave)"
    assert (work / "Contribution.lean").is_file()
    assert "partial response" in (work / "trace.jsonl").read_text()


def test_sandbox_command_mounts_copy_not_host_workspace_or_home(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    execution_dir = tmp_path / "task"
    execution_dir.mkdir()
    (execution_dir / "input.txt").write_text("fixture\n", encoding="utf-8")
    monkeypatch.delenv("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH", raising=False)

    runtime, cidfile = runner.prepare_model_sandbox(
        execution_dir,
        runner.ModelSandboxSettings(image=runner.PODMAN_IMAGE),
        timeout_s=60,
    )
    try:
        command = runtime.build_podman_command(
            ["sh", "-lc", "true"],
            container_workdir=execution_dir.resolve(),
            cidfile=cidfile,
        )
        mounts = [command[index + 1] for index, item in enumerate(command) if item == "-v"]
        mount_sources = [item.split(":", 1)[0] for item in mounts]

        assert str(execution_dir.resolve()) not in mount_sources
        assert str(runner.ROOT.resolve()) not in mount_sources
        assert str(Path.home()) not in mount_sources
        assert any(
            item.startswith(f"{runtime.paths.workspace_host_path}:")
            and f":{execution_dir.resolve()}:rw" in item
            for item in mounts
        )
        assert command[command.index("--network") + 1] == "slirp4netns"
        assert command[command.index("--cpus") + 1] == "2"
        assert command[command.index("--memory") + 1] == "4g"
    finally:
        shutil.rmtree(runtime.paths.run_dir, ignore_errors=True)


def test_sandbox_lean_project_uses_image_snapshot_not_host_mount(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    execution_dir = tmp_path / "task"
    execution_dir.mkdir()
    monkeypatch.delenv("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH", raising=False)
    runtime, cidfile = runner.prepare_model_sandbox(
        execution_dir,
        runner.ModelSandboxSettings(image=runner.PODMAN_IMAGE),
        timeout_s=60,
        include_lean_project=True,
    )
    try:
        workspace = runtime.paths.workspace_host_path
        assert (workspace / "TheoryLib").readlink() == Path(
            "/opt/allmath-prebuilt/TheoryLib"
        )
        assert (workspace / ".lake").readlink() == Path(
            "/opt/allmath-prebuilt/.lake"
        )
        command = runtime.build_podman_command(
            ["sh", "-lc", "true"],
            container_workdir=execution_dir.resolve(),
            cidfile=cidfile,
        )
        mounts = [command[index + 1] for index, item in enumerate(command) if item == "-v"]
        assert all(
            not mount.startswith(f"{runner.ROOT.resolve()}:")
            for mount in mounts
        )
    finally:
        shutil.rmtree(runtime.paths.run_dir, ignore_errors=True)


def test_sandbox_credentials_are_provider_scoped_and_container_is_hardened(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    execution_dir = tmp_path / "task"
    home = tmp_path / "home"
    auth = home / ".local" / "share" / "opencode" / "auth.json"
    config = home / ".config" / "opencode"
    catalog = home / ".cache" / "opencode" / "models.json"
    execution_dir.mkdir()
    auth.parent.mkdir(parents=True)
    auth.write_text(
        json.dumps(
            {
                "openrouter": {"key": "router-secret"},
                "openai": {"key": "unrelated-openai-secret"},
                "minimax-coding-plan": {"key": "unrelated-minimax-secret"},
            }
        ),
        encoding="utf-8",
    )
    config.mkdir(parents=True)
    catalog.parent.mkdir(parents=True)
    catalog.write_text("{}\n", encoding="utf-8")
    monkeypatch.setattr(Path, "home", lambda: home)
    # Exercise stripping even when the shared helper's legacy broad opt-in is
    # present in the parent environment.
    monkeypatch.setenv("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH", "1")
    runtime, cidfile = runner.prepare_model_sandbox(
        execution_dir,
        runner.ModelSandboxSettings(image=runner.PODMAN_IMAGE),
        timeout_s=60,
    )
    try:
        raw = runtime.build_podman_command(
            ["opencode", "run"],
            container_workdir=execution_dir.resolve(),
            cidfile=cidfile,
        )
        zen = runner.harden_sandbox_command(runtime, raw, "oxzen")
        zen_mounts = [zen[index + 1] for index, item in enumerate(zen) if item == "-v"]

        assert str(auth) not in " ".join(zen)
        assert not any(
            ":/root/.local/share/opencode/auth.json:" in mount
            for mount in zen_mounts
        )
        assert f"{runtime.paths.root / 'opencode-cache'}:/root/.cache:rw" in zen_mounts
        assert f"{catalog}:/root/.cache/opencode/models.json:ro" in zen_mounts
        assert "--read-only" in zen
        assert zen[zen.index("--cap-drop") + 1] == "ALL"
        assert zen[zen.index("--security-opt") + 1] == "no-new-privileges"
        assert zen[zen.index("--pids-limit") + 1] == "512"
        assert zen[zen.index("--tmpfs") + 1] == runner.SANDBOX_TMPFS

        router = runner.harden_sandbox_command(runtime, raw, "ox")
        router_mounts = [
            router[index + 1]
            for index, item in enumerate(router)
            if item == "-v"
        ]
        auth_mount = next(
            mount
            for mount in router_mounts
            if ":/root/.local/share/opencode/auth.json:ro" in mount
        )
        scoped_auth = Path(auth_mount.split(":", 1)[0])
        scoped_payload = json.loads(scoped_auth.read_text(encoding="utf-8"))
        assert list(scoped_payload) == ["openrouter"]
        assert "router-secret" in scoped_auth.read_text(encoding="utf-8")
        assert "unrelated-openai-secret" not in scoped_auth.read_text(encoding="utf-8")
        assert "unrelated-minimax-secret" not in scoped_auth.read_text(encoding="utf-8")
        assert scoped_auth.stat().st_mode & 0o777 == 0o600
        assert str(auth) not in " ".join(router)
    finally:
        shutil.rmtree(runtime.paths.run_dir, ignore_errors=True)


def test_real_sandbox_cannot_write_host_sibling_and_only_declared_artifact_returns(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    if shutil.which("podman") is None:
        pytest.skip("podman unavailable")
    if subprocess.run(
        ["podman", "image", "exists", runner.PODMAN_IMAGE], check=False
    ).returncode != 0:
        pytest.skip("AllMath sandbox image unavailable")

    execution_dir = tmp_path / "task"
    canonical_dir = tmp_path / "canonical"
    execution_dir.mkdir()
    canonical_dir.mkdir()
    canonical = canonical_dir / "protected.txt"
    canonical.write_text("authoritative\n", encoding="utf-8")
    monkeypatch.delenv("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH", raising=False)
    runtime, cidfile = runner.prepare_model_sandbox(
        execution_dir,
        runner.ModelSandboxSettings(image=runner.PODMAN_IMAGE),
        timeout_s=60,
    )
    try:
        script = (
            "printf 'sandbox artifact\\n' > Contribution.lean; "
            f"printf 'attack\\n' > {canonical}; "
            f"ln -s {canonical} Escape.lean"
        )
        command = runtime.build_podman_command(
            ["sh", "-lc", script],
            container_workdir=execution_dir.resolve(),
            cidfile=cidfile,
        )
        completed = subprocess.run(command, capture_output=True, text=True, timeout=60)

        assert completed.returncode == 0, completed.stderr
        assert canonical.read_text(encoding="utf-8") == "authoritative\n"
        assert not (execution_dir / "Contribution.lean").exists()
        copied = runner.copy_sandbox_artifacts_back(
            runtime,
            execution_dir,
            ["Contribution.lean", "Escape.lean", "undeclared.txt"],
        )
        assert copied == ["Contribution.lean"]
        assert (execution_dir / "Contribution.lean").read_text() == "sandbox artifact\n"
        assert not (execution_dir / "Escape.lean").exists()
    finally:
        shutil.rmtree(runtime.paths.run_dir, ignore_errors=True)


def test_stale_owner_heartbeat_stops_term_ignoring_container(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    if shutil.which("podman") is None:
        pytest.skip("podman unavailable")
    if subprocess.run(
        ["podman", "image", "exists", runner.PODMAN_IMAGE], check=False
    ).returncode != 0:
        pytest.skip("AllMath sandbox image unavailable")

    execution_dir = tmp_path / "task"
    execution_dir.mkdir()
    monkeypatch.delenv("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH", raising=False)
    runtime, cidfile = runner.prepare_model_sandbox(
        execution_dir,
        runner.ModelSandboxSettings(image=runner.PODMAN_IMAGE),
        timeout_s=60,
    )
    try:
        raw = runtime.build_podman_command(
            ["sh", "-c", "trap '' TERM; sleep 60"],
            container_workdir=execution_dir.resolve(),
            cidfile=cidfile,
        )
        hardened = runner.harden_sandbox_command(runtime, raw, "oxzen")
        watched, heartbeat = runner.add_sandbox_owner_watchdog(
            runtime, hardened
        )
        container_name = f"modelbench-watchdog-test-{time.time_ns()}"
        image_index = watched.index(runtime.config.image)
        watched[image_index:image_index] = ["--name", container_name]
        heartbeat.path.touch()
        stale = time.time() - runner.SANDBOX_HEARTBEAT_STALE_S - 2
        os.utime(heartbeat.path, (stale, stale))

        completed = subprocess.run(
            watched, capture_output=True, text=True, timeout=15
        )

        assert completed.returncode != 0
        exists = subprocess.run(
            ["podman", "container", "exists", container_name], check=False
        )
        assert exists.returncode != 0
    finally:
        if "container_name" in locals():
            subprocess.run(
                ["podman", "rm", "-f", container_name],
                capture_output=True,
                check=False,
            )
        if cidfile.is_file():
            runtime.force_remove_container(cidfile)
        shutil.rmtree(runtime.paths.run_dir, ignore_errors=True)


def test_isolated_gate_code_137_is_an_infrastructure_failure() -> None:
    reason = runner.isolated_gate_resource_failure(
        "unrelated build target failed\nerror: Lean exited with code 137\n"
    )

    assert reason is not None
    assert runner.is_gate_infrastructure_failure(reason)
    assert "trusted snapshot" in reason


def test_lean_error_excerpt_preserves_error_before_axiom_recovery_noise() -> None:
    output = (
        "candidate.lean:208:2: error: Type mismatch\n"
        "  actual has type RHS (0 + 0)\n"
        "but expected RHS 0\n"
        + "sorryAx recovery output\n" * 300
    )

    excerpt = runner.lean_error_excerpt(output, limit=300)

    assert "Type mismatch" in excerpt
    assert "0 + 0" in excerpt


def test_run_pair_does_not_invoke_model_after_slot_cancellation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    cancel_file = tmp_path / "cancel"
    cancel_file.touch()

    def model_must_not_run(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("cancelled runner invoked a model")

    monkeypatch.setattr(runner, "run_model", model_must_not_run)
    task = {
        "id": "cancelled-slot",
        "prompt": "unused",
        "dimension": "schema",
        "grading": {"type": "answer_key"},
    }

    entry = runner.run_pair(
        "ox",
        task,
        tmp_path / "out",
        tmp_path / "bench",
        cancel_file=cancel_file,
    )

    assert entry["attempt_count"] == 1
    assert entry["error"] == "model slot acquisition cancelled for ox"


def test_failed_artifact_retries_in_the_same_opencode_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    calls: list[tuple[str, str | None]] = []
    grades = iter([(False, "host compile failed: exact Lean error"), (True, "compiled")])

    def fake_run_model(
        _model_key: str, prompt: str, bench_dir: Path, **kwargs: object
    ) -> dict[str, object]:
        calls.append((prompt, kwargs.get("session_id") if isinstance(kwargs.get("session_id"), str) else None))
        (bench_dir / "Contribution.lean").write_text("theorem t : True := by trivial\n")
        return {
            "response": "artifact written",
            "trace": '{"sessionID":"session-1"}',
            "error": "",
            "duration_s": 0.0,
        }

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    monkeypatch.setattr(runner, "grade", lambda *_args: next(grades))
    task = {
        "id": "artifact-retry",
        "prompt": "initial prompt",
        "resume_prompt": "resume prompt",
        "dimension": "lean_research",
        "max_attempts": 2,
        "grading": {"type": "agentic_lean_artifact", "artifact": "Contribution.lean"},
    }

    entry = runner.run_pair("ox", task, tmp_path / "out", tmp_path / "bench")

    assert entry["passed"] is True
    assert entry["attempt_count"] == 2
    assert entry["attempt_grades"] == [
        {"attempt": 1, "passed": False, "reason": "host compile failed: exact Lean error"},
        {"attempt": 2, "passed": True, "reason": "compiled"},
    ]
    assert calls[0] == ("initial prompt", None)
    assert calls[1][1] == "session-1"
    assert "resume prompt" in calls[1][0]
    assert "host compile failed: exact Lean error" in calls[1][0]


def test_zero_token_unknown_without_artifact_retries_fresh_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    calls: list[tuple[str, str | None]] = []
    delays: list[float] = []

    def fake_run_model(
        _model_key: str, prompt: str, bench_dir: Path, **kwargs: object
    ) -> dict[str, object]:
        session = kwargs.get("session_id")
        calls.append((prompt, session if isinstance(session, str) else None))
        if len(calls) == 1:
            return {
                "response": "",
                "trace": (
                    '{"type":"step_finish","sessionID":"dead-session",'
                    '"part":{"reason":"unknown","tokens":'
                    '{"input":0,"output":0,"reasoning":0}}}'
                ),
                "error": "",
                "duration_s": 0.0,
            }
        (bench_dir / "Contribution.lean").write_text(
            "theorem t : True := by trivial\n"
        )
        return {
            "response": "artifact written",
            "trace": '{"sessionID":"fresh-session"}',
            "error": "",
            "duration_s": 0.0,
        }

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    monkeypatch.setattr(
        runner, "zero_token_retry_delay_s", lambda _attempt: 7.5
    )
    monkeypatch.setattr(
        runner,
        "cancellation_aware_sleep",
        lambda delay, **_kwargs: delays.append(delay) or True,
    )
    monkeypatch.setattr(
        runner,
        "grade",
        lambda _task, _response, work_dir, _execution_dir: (
            (True, "compiled")
            if (work_dir / "Contribution.lean").is_file()
            else (False, "missing artifact Contribution.lean")
        ),
    )
    task = {
        "id": "artifact-fresh-retry",
        "prompt": "full original prompt",
        "dimension": "lean_research",
        "max_attempts": 2,
        "grading": {"type": "agentic_lean_artifact", "artifact": "Contribution.lean"},
    }

    entry = runner.run_pair("oxzen", task, tmp_path / "out", tmp_path / "bench")

    assert entry["passed"] is True
    assert calls == [
        ("full original prompt", None),
        ("full original prompt", None),
    ]
    assert delays == [7.5]


def test_zero_token_retry_delay_is_exponential_jittered_and_bounded() -> None:
    assert runner.zero_token_retry_delay_s(1, random_unit=0.0) == 3.75
    assert runner.zero_token_retry_delay_s(1, random_unit=0.5) == 5.0
    assert runner.zero_token_retry_delay_s(2, random_unit=0.5) == 10.0
    assert runner.zero_token_retry_delay_s(20, random_unit=1.0) == 60.0

    with pytest.raises(ValueError, match="positive"):
        runner.zero_token_retry_delay_s(0, random_unit=0.5)
    with pytest.raises(ValueError, match="between"):
        runner.zero_token_retry_delay_s(1, random_unit=1.1)


def test_zero_token_backoff_stops_promptly_when_cancelled() -> None:
    cancellation = runner.Cancellation()
    sleeps: list[float] = []

    def cancel_during_first_interval(delay: float) -> None:
        sleeps.append(delay)
        cancellation.request("retired during backoff")

    completed = runner.cancellation_aware_sleep(
        20.0,
        cancellation=cancellation,
        poll_interval_s=0.25,
        sleeper=cancel_during_first_interval,
    )

    assert completed is False
    assert sleeps == [0.25]


def test_zero_token_backoff_cancellation_prevents_fresh_call(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    cancellation = runner.Cancellation()
    calls = 0

    def zero_token_run(
        _model_key: str, _prompt: str, _bench_dir: Path, **_kwargs: object
    ) -> dict[str, object]:
        nonlocal calls
        calls += 1
        return {
            "response": "",
            "trace": (
                '{"type":"step_finish","sessionID":"dead-session",'
                '"part":{"reason":"unknown","tokens":'
                '{"input":0,"output":0,"reasoning":0}}}'
            ),
            "error": "",
            "duration_s": 0.0,
        }

    def cancel_backoff(_delay: float, **_kwargs: object) -> bool:
        cancellation.request("wave replaced")
        return False

    monkeypatch.setattr(runner, "run_model", zero_token_run)
    monkeypatch.setattr(runner, "grade", lambda *_args: (False, "missing artifact"))
    monkeypatch.setattr(runner, "cancellation_aware_sleep", cancel_backoff)
    task = {
        "id": "cancel-zero-token-backoff",
        "prompt": "full prompt",
        "dimension": "lean_research",
        "max_attempts": 3,
        "grading": {
            "type": "agentic_lean_artifact",
            "artifact": "Contribution.lean",
        },
    }

    entry = runner.run_pair(
        "oxzen",
        task,
        tmp_path / "out",
        tmp_path / "bench",
        cancellation=cancellation,
    )

    assert calls == 1
    assert entry["attempt_count"] == 1
    assert entry["reason"] == "cancelled (wave replaced)"


def test_passing_artifact_stops_without_a_second_attempt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    calls = 0

    def fake_run_model(
        _model_key: str, _prompt: str, bench_dir: Path, **_kwargs: object
    ) -> dict[str, object]:
        nonlocal calls
        calls += 1
        (bench_dir / "Contribution.lean").write_text("theorem t : True := by trivial\n")
        return {"response": "artifact written", "trace": "", "error": "", "duration_s": 0.0}

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    monkeypatch.setattr(runner, "grade", lambda *_args: (True, "compiled"))
    task = {
        "id": "artifact-pass",
        "prompt": "initial prompt",
        "dimension": "lean_research",
        "max_attempts": 2,
        "grading": {"type": "agentic_lean_artifact", "artifact": "Contribution.lean"},
    }

    entry = runner.run_pair("ox", task, tmp_path / "out", tmp_path / "bench")

    assert calls == 1
    assert entry["passed"] is True
    assert entry["attempt_count"] == 1


def test_run_pair_declares_support_files_for_sandbox_copyback(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    observed: tuple[str, ...] = ()

    def fake_run_model(
        _model_key: str, _prompt: str, bench_dir: Path, **kwargs: object
    ) -> dict[str, object]:
        nonlocal observed
        observed = tuple(kwargs["sandbox_copy_back"])  # type: ignore[arg-type]
        (bench_dir / "EXPERIMENT.md").write_text("Result\n" + "x" * 100)
        (bench_dir / "replay.py").write_text("print('ok')\n")
        return {"response": "done", "trace": "", "error": "", "duration_s": 0.0}

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    task = {
        "id": "artifact-support-files",
        "prompt": "write artifacts",
        "dimension": "research_audit",
        "max_attempts": 1,
        "grading": {
            "type": "artifact_contract",
            "artifact": "EXPERIMENT.md",
            "min_chars": 1,
            "required_markers": ["Result"],
            "required_files": ["replay.py"],
        },
    }

    entry = runner.run_pair("ox", task, tmp_path / "out", tmp_path / "bench")

    assert entry["passed"] is True
    assert observed == ("EXPERIMENT.md", "REPORT.md", "replay.py")


def test_resource_exhausted_gate_does_not_trigger_artifact_repair(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runner, "PROVIDER_SLOT_LOCK_ROOT", tmp_path / "slots")
    calls = 0

    def fake_run_model(
        _model_key: str, _prompt: str, bench_dir: Path, **_kwargs: object
    ) -> dict[str, object]:
        nonlocal calls
        calls += 1
        (bench_dir / "Contribution.lean").write_text(
            "theorem t : True := by trivial\n"
        )
        return {"response": "artifact written", "trace": "", "error": "", "duration_s": 0.0}

    monkeypatch.setattr(runner, "run_model", fake_run_model)
    failure = (
        "isolated gate resource failure: Lean exited with code 137 while "
        "rebuilding the trusted snapshot"
    )
    monkeypatch.setattr(runner, "grade", lambda *_args: (False, failure))
    task = {
        "id": "artifact-gate-resource-failure",
        "prompt": "initial prompt",
        "dimension": "lean_research",
        "max_attempts": 2,
        "grading": {"type": "agentic_lean_artifact", "artifact": "Contribution.lean"},
    }

    entry = runner.run_pair("ox", task, tmp_path / "out", tmp_path / "bench")

    assert calls == 1
    assert entry["passed"] is False
    assert entry["attempt_count"] == 1
    assert entry["reason"] == failure
