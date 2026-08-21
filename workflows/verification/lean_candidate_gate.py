#!/usr/bin/env python3
"""Deterministically check a proof body against a pinned Lean theorem template.

This is a scratch-candidate gate, not the TheoryLib promotion gate.  It never
changes the verified track and it never assigns a research claim label.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Collection


PROOF_HOLE = "-- ALLMATH_PROOF_HOLE"
def strip_lean_comments(text: str) -> str:
    """Remove Lean comments before token scanning: block comments (nesting
    approximated by repeated non-greedy removal) and line comments.  The
    kernel/axiom gate independently catches any real forbidden construct, so
    this only prevents prose false-positives."""
    previous = None
    while previous != text:
        previous = text
        text = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", " ", text)


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
MAX_PROOF_BYTES = 20_000
FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|"
    r"Lean\.trustCompiler)\b|^\s*(?:axiom|opaque|constant|unsafe)\b|#",
    re.MULTILINE,
)
THEOREM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


@dataclass(frozen=True)
class GateReport:
    accepted: bool
    reason: str
    template_sha256: str
    expected_template_sha256: str
    theorem_name: str
    candidate_path: str
    command: list[str]
    exit_code: int | None
    timed_out: bool
    axioms: list[str]
    disallowed_axioms: list[str]
    stdout: str
    stderr: str


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _base_report(
    *,
    reason: str,
    template_sha256: str,
    expected_template_sha256: str,
    theorem_name: str,
    candidate_path: Path,
) -> GateReport:
    return GateReport(
        accepted=False,
        reason=reason,
        template_sha256=template_sha256,
        expected_template_sha256=expected_template_sha256,
        theorem_name=theorem_name,
        candidate_path=str(candidate_path.resolve()),
        command=[],
        exit_code=None,
        timed_out=False,
        axioms=[],
        disallowed_axioms=[],
        stdout="",
        stderr="",
    )


def _extract_named_axioms(output: str, theorem_name: str) -> list[str] | None:
    quoted = re.escape(theorem_name)
    depends = re.search(
        rf"'{quoted}' depends on axioms:\s*\[([^\]]*)\]",
        output,
        flags=re.MULTILINE,
    )
    if depends:
        return sorted(
            {
                item.strip()
                for item in depends.group(1).split(",")
                if item.strip()
            }
        )
    no_axioms = re.search(
        rf"'{quoted}' does not depend on any axioms",
        output,
        flags=re.MULTILINE,
    )
    return [] if no_axioms else None


def _materialize_proof(template: str, proof: str) -> str | None:
    marker = re.compile(
        rf"^(?P<indent>[ \t]*){re.escape(PROOF_HOLE)}[ \t]*$",
        flags=re.MULTILINE,
    )
    matches = list(marker.finditer(template))
    if len(matches) != 1:
        return None
    indent = matches[0].group("indent")
    replacement = "\n".join(f"{indent}{line}" if line else "" for line in proof.splitlines())
    return marker.sub(lambda _match: replacement, template, count=1)


def _process_text(value: str | bytes | None) -> str:
    """Normalize subprocess output, including TimeoutExpired byte payloads."""

    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def gate_candidate(
    *,
    project_root: Path,
    template_path: Path,
    expected_template_sha256: str,
    proof: str,
    theorem_name: str,
    candidate_path: Path,
    timeout_seconds: int = 120,
    allowed_axioms: Collection[str] = ALLOWED_AXIOMS,
    command_builder: Callable[[list[str]], list[str]] | None = None,
) -> GateReport:
    """Materialize and kernel-check one candidate without trusting model output."""
    project_root = project_root.resolve()
    template_path = template_path.resolve()
    candidate_path = candidate_path.resolve()
    actual_hash = sha256_file(template_path) if template_path.is_file() else ""

    def reject(reason: str) -> GateReport:
        return _base_report(
            reason=reason,
            template_sha256=actual_hash,
            expected_template_sha256=expected_template_sha256,
            theorem_name=theorem_name,
            candidate_path=candidate_path,
        )

    if not template_path.is_file():
        return reject("template_missing")
    if not re.fullmatch(r"[0-9a-f]{64}", expected_template_sha256):
        return reject("invalid_expected_template_sha256")
    if actual_hash != expected_template_sha256:
        return reject("template_hash_mismatch")
    if not THEOREM_NAME_RE.fullmatch(theorem_name):
        return reject("invalid_theorem_name")
    if not isinstance(proof, str) or not proof.strip():
        return reject("empty_proof")
    if len(proof.encode("utf-8")) > MAX_PROOF_BYTES:
        return reject("proof_too_large")
    if "```" in proof:
        return reject("markdown_fence_in_proof")
    if FORBIDDEN_RE.search(strip_lean_comments(proof)):
        return reject("forbidden_construct")

    template = template_path.read_text(encoding="utf-8")
    if "#print axioms" in template:
        return reject("template_contains_axiom_query")

    candidate = _materialize_proof(template, proof)
    if candidate is None:
        return reject("template_must_have_exactly_one_proof_hole_line")
    candidate += f"\n\n#print axioms {theorem_name}\n"
    candidate_path.parent.mkdir(parents=True, exist_ok=True)
    candidate_path.write_text(candidate, encoding="utf-8")

    lean_command = ["lake", "env", "lean", str(candidate_path)]
    command = command_builder(lean_command) if command_builder else lean_command
    try:
        completed = subprocess.run(
            command,
            cwd=project_root,
            text=True,
            capture_output=True,
            timeout=max(1, timeout_seconds),
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        return GateReport(
            **{
                **asdict(reject("lean_timeout")),
                "command": command,
                "timed_out": True,
                "stdout": _process_text(exc.stdout),
                "stderr": _process_text(exc.stderr),
            }
        )

    stdout = _process_text(completed.stdout)
    stderr = _process_text(completed.stderr)
    combined = f"{stdout}\n{stderr}"
    if completed.returncode != 0:
        return GateReport(
            **{
                **asdict(reject("lean_compile_failed")),
                "command": command,
                "exit_code": completed.returncode,
                "stdout": stdout,
                "stderr": stderr,
            }
        )

    axioms = _extract_named_axioms(combined, theorem_name)
    if axioms is None:
        return GateReport(
            **{
                **asdict(reject("named_axiom_result_missing")),
                "command": command,
                "exit_code": completed.returncode,
                "stdout": stdout,
                "stderr": stderr,
            }
        )
    disallowed = sorted(set(axioms) - set(allowed_axioms))
    accepted = not disallowed
    return GateReport(
        accepted=accepted,
        reason="kernel_and_axiom_gate_passed" if accepted else "disallowed_axiom",
        template_sha256=actual_hash,
        expected_template_sha256=expected_template_sha256,
        theorem_name=theorem_name,
        candidate_path=str(candidate_path),
        command=command,
        exit_code=completed.returncode,
        timed_out=False,
        axioms=axioms,
        disallowed_axioms=disallowed,
        stdout=stdout,
        stderr=stderr,
    )


def _load_proof(path: Path) -> str:
    if path.suffix.lower() == ".json":
        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or not isinstance(payload.get("proof"), str):
            raise ValueError("candidate JSON must contain a string field named 'proof'")
        return payload["proof"]
    return path.read_text(encoding="utf-8")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--template", type=Path, required=True)
    parser.add_argument("--template-sha256", required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--theorem", required=True)
    parser.add_argument("--candidate-out", type=Path, required=True)
    parser.add_argument("--report-out", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        proof = _load_proof(args.proof)
        report = gate_candidate(
            project_root=args.project_root,
            template_path=args.template,
            expected_template_sha256=args.template_sha256,
            proof=proof,
            theorem_name=args.theorem,
            candidate_path=args.candidate_out,
            timeout_seconds=args.timeout_seconds,
        )
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        report = _base_report(
            reason=f"input_error: {exc}",
            template_sha256="",
            expected_template_sha256=args.template_sha256,
            theorem_name=args.theorem,
            candidate_path=args.candidate_out,
        )
    args.report_out.parent.mkdir(parents=True, exist_ok=True)
    args.report_out.write_text(
        json.dumps(asdict(report), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0 if report.accepted else 1


if __name__ == "__main__":
    sys.exit(main())
