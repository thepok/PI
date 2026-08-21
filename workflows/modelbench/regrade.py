#!/usr/bin/env python3
"""Re-grade recorded responses without re-running models.

Used when a grading defect is fixed (e.g. the ACCEPT/answer-regex bug):
reads results.jsonl, re-grades every entry of the given dimensions from the
stored response.txt with the CURRENT grading code, and appends corrected
entries (the report generator takes the last entry per model x task)."""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import runner  # noqa: E402  (same directory)

HERE = Path(__file__).resolve().parent


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
            passed, reason = runner.grade(
                tasks[task_id], response, work_dir, work_dir
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
