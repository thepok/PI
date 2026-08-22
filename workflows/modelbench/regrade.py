#!/usr/bin/env python3
"""Re-grade recorded responses without re-running models.

Used when a grading defect is fixed (e.g. the ACCEPT/answer-regex bug):
reads results.jsonl, re-grades every entry of the given dimensions from the
stored response.txt with the CURRENT grading code, and appends corrected
entries (the report generator takes the last entry per model x task)."""

from __future__ import annotations

import argparse
import json
import re
import time
from pathlib import Path

if __package__:
    from workflows.modelbench import runner
else:
    import runner  # type: ignore[no-redef]  # direct script execution

HERE = Path(__file__).resolve().parent


def lean_regrade_binding(
    task: dict, entry: dict
) -> tuple[str | None, str | None]:
    """Return immutable gate image/source bindings or reject unsafe regrade."""
    if task["grading"]["type"] not in {"agentic_lean_artifact", "lean_gate"}:
        return None, None
    image = entry.get("lean_gate_image_sha256") or entry.get(
        "sandbox_image_sha256"
    )
    source = entry.get("trusted_source_sha256")
    if not isinstance(image, str) or not re.fullmatch(r"[0-9a-f]{64}", image):
        raise ValueError(
            "Lean regrade lacks an immutable lean-gate image binding"
        )
    if not isinstance(source, str) or not re.fullmatch(r"[0-9a-f]{64}", source):
        raise ValueError("Lean regrade lacks a trusted source binding")
    return image, source


def controller_regrade_image(task: dict, entry: dict) -> str | None:
    """Return the immutable fixed-controller image or reject unsafe regrade."""
    grading = task["grading"]
    if (
        grading["type"] != "artifact_contract"
        or grading.get("controller_gate") is None
    ):
        return None
    image = entry.get("controller_image_sha256") or entry.get(
        "sandbox_image_sha256"
    )
    if not isinstance(image, str) or not re.fullmatch(r"[0-9a-f]{64}", image):
        raise ValueError(
            "fixed-controller regrade lacks an immutable image binding"
        )
    return image


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dimensions", required=True)
    parser.add_argument("--out", type=Path, default=HERE / "results")
    parser.add_argument("--tasks-dir", type=Path, default=HERE / "tasks")
    args = parser.parse_args()
    dims = {d.strip() for d in args.dimensions.split(",") if d.strip()}
    tasks = {
        t["id"]: t for t in runner.load_tasks(args.tasks_dir, dims)
    }
    results_path = args.out / "results.jsonl"
    entries = [
        json.loads(line)
        for line in results_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    latest: dict[tuple[str, str], dict] = {}
    for entry in entries:
        latest[(entry["model"], entry["task"])] = entry
    appended = 0
    for (model, task_id), entry in sorted(latest.items()):
        if entry["dimension"] not in dims or task_id not in tasks:
            continue
        try:
            lean_regrade_binding(tasks[task_id], entry)
            controller_regrade_image(tasks[task_id], entry)
        except ValueError as exc:
            raise SystemExit(
                f"refusing unsafe regrade for {model} x {task_id}: {exc}"
            ) from exc
    with results_path.open("a", encoding="utf-8") as stream:
        for (model, task_id), entry in sorted(latest.items()):
            if entry["dimension"] not in dims or task_id not in tasks:
                continue
            response_path = (
                args.out / "work" / f"{model}-{task_id}" / "response.txt"
            )
            if not response_path.is_file():
                continue
            response = response_path.read_text(encoding="utf-8")
            if not response.strip():
                continue
            work_dir = args.out / "work" / f"{model}-{task_id}"
            lean_gate_image, trusted_source = lean_regrade_binding(
                tasks[task_id], entry
            )
            controller_image = controller_regrade_image(
                tasks[task_id], entry
            )
            grade_bindings = {}
            if lean_gate_image is not None:
                grade_bindings.update(
                    lean_gate_image=lean_gate_image,
                    expected_trusted_source_sha256=trusted_source,
                )
            if controller_image is not None:
                grade_bindings["controller_image"] = controller_image
            passed, reason = runner.grade(
                tasks[task_id],
                response,
                work_dir,
                work_dir,
                **grade_bindings,
            )
            if runner.is_gate_infrastructure_failure(reason):
                raise SystemExit(
                    f"refusing unsafe regrade for {model} x {task_id}: "
                    f"{reason}"
                )
            if passed == entry["passed"]:
                continue
            corrected = {
                **entry,
                "passed": passed,
                "reason": f"regraded: {reason}",
                "recorded_at": time.strftime(
                    "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
                ),
                "lean_gate_image_sha256": lean_gate_image,
                "controller_image_sha256": controller_image,
            }
            stream.write(json.dumps(corrected, sort_keys=True) + "\n")
            appended += 1
            print(
                f"REGRADE {model} x {task_id}: "
                f"{entry['passed']} -> {passed} ({reason[:80]})"
            )
    print(f"{appended} entries corrected")
    runner.write_report(results_path, args.out / "report.md")


if __name__ == "__main__":
    main()
