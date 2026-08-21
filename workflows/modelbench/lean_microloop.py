#!/usr/bin/env python3
"""Drive an existing OpenCode session through compiler-first Lean microsteps."""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import shutil
import subprocess
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FORBIDDEN_RE = re.compile(
    r"(\bsorry\b|\badmit\b|\bnative_decide\b|"
    r"^\s*(?:axiom|constant|opaque)\b|\bunsafe\b)",
    re.MULTILINE,
)


def first_error(output: str, limit: int = 6000) -> str:
    """Return the first compiler-error block, with enough local context."""
    lines = output.splitlines()
    start = next(
        (i for i, line in enumerate(lines) if ": error" in line),
        0,
    )
    end = min(len(lines), start + 55)
    for i in range(start + 1, end):
        if ": error" in lines[i]:
            end = i
            break
    return "\n".join(lines[start:end])[:limit]


def compile_candidate(candidate: Path, timeout_s: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(candidate)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )


def run_turn(
    session_id: str,
    work_dir: Path,
    candidate: Path,
    before_mtime_ns: int,
    variant: str,
    prompt: str,
    timeout_s: int,
) -> tuple[int | None, str, bool, bool]:
    """Run one repair turn and stop as soon as its atomic file edit lands."""
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout_file, \
            tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stderr_file:
        proc = subprocess.Popen(
            [
                "opencode", "run", "--session", session_id,
                "--format", "json", "--dir", str(work_dir),
                "--variant", variant, prompt,
            ],
            cwd=work_dir,
            text=True,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=True,
        )
        deadline = time.monotonic() + timeout_s
        changed = False
        timed_out = False
        while proc.poll() is None:
            if candidate.stat().st_mtime_ns != before_mtime_ns:
                changed = True
                break
            if time.monotonic() >= deadline:
                timed_out = True
                break
            time.sleep(1)
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait(timeout=5)
        stdout_file.seek(0)
        stderr_file.seek(0)
        trace = stdout_file.read()
        error = stderr_file.read()
        if error:
            trace += "\n" + error
        return proc.returncode, trace, timed_out, changed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--session", required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--candidate", default="Contribution.lean")
    parser.add_argument("--seed-file", type=Path)
    parser.add_argument("--variant", default="high")
    parser.add_argument("--max-steps", type=int, default=12)
    parser.add_argument("--turn-timeout", type=int, default=240)
    parser.add_argument("--compile-timeout", type=int, default=180)
    args = parser.parse_args()

    work_dir = args.work_dir.resolve()
    work_dir.mkdir(parents=True, exist_ok=True)
    candidate = work_dir / args.candidate
    if not candidate.exists() and args.seed_file:
        shutil.copy2(args.seed_file.resolve(), candidate)
    if not candidate.is_file():
        raise SystemExit(f"candidate does not exist: {candidate}")

    run_id = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_dir = work_dir / f"microloop-{run_id}"
    run_dir.mkdir(parents=True, exist_ok=False)
    summary: dict[str, object] = {
        "run_id": run_id,
        "session_id": args.session,
        "candidate": str(candidate),
        "variant": args.variant,
        "steps": [],
    }

    for step in range(args.max_steps + 1):
        compiled = compile_candidate(candidate, args.compile_timeout)
        compile_output = f"{compiled.stdout}\n{compiled.stderr}"
        (run_dir / f"compile-{step:02d}.log").write_text(
            compile_output, encoding="utf-8"
        )
        step_record: dict[str, object] = {
            "step": step,
            "compile_returncode": compiled.returncode,
        }
        cast_steps = summary["steps"]
        assert isinstance(cast_steps, list)
        cast_steps.append(step_record)
        print(
            f"compile {step}: rc={compiled.returncode}",
            flush=True,
        )
        if compiled.returncode == 0:
            code = candidate.read_text(encoding="utf-8")
            forbidden = FORBIDDEN_RE.search(code)
            summary["status"] = "forbidden-token" if forbidden else "compiled"
            summary["forbidden_match"] = forbidden.group(0) if forbidden else None
            (run_dir / "summary.json").write_text(
                json.dumps(summary, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            return 2 if forbidden else 0
        if step == args.max_steps:
            break

        blocker = first_error(compile_output)
        prompt = (
            f"Lean repair microstep {step + 1}/{args.max_steps}. "
            f"Work only on {candidate}. The controller compiled it and the "
            "first error is below. Fix this one error, or the smallest local "
            "dependency required for it, by editing the file. Do not perform "
            "a broad search, do not rewrite unrelated proved lemmas, and do "
            "not use sorry/admit/native_decide/axiom/constant/opaque/unsafe. "
            "Do not run Lean yourself; the controller will compile immediately "
            "after your edit. End the turn after the edit with MICROSTEP_DONE.\n\n"
            f"FIRST COMPILER ERROR:\n{blocker}"
        )
        before = candidate.stat().st_mtime_ns
        turn_returncode, trace, timed_out, stopped_after_edit = run_turn(
            args.session,
            work_dir,
            candidate,
            before,
            args.variant,
            prompt,
            args.turn_timeout,
        )
        (run_dir / f"turn-{step + 1:02d}.jsonl").write_text(
            trace, encoding="utf-8"
        )
        after = candidate.stat().st_mtime_ns
        step_record["turn_returncode"] = turn_returncode
        step_record["turn_timed_out"] = timed_out
        step_record["turn_stopped_after_edit"] = stopped_after_edit
        step_record["candidate_changed"] = after != before
        print(
            f"turn {step + 1}: changed={after != before} "
            f"timeout={timed_out} stopped_after_edit={stopped_after_edit}",
            flush=True,
        )
        if after == before:
            summary["status"] = "no-edit"
            break

    summary.setdefault("status", "step-limit")
    (run_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
