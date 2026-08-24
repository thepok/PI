#!/usr/bin/env python3
"""Reject forbidden trust shortcuts in every tracked Lean source file."""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Iterable

FORBIDDEN = re.compile(
    r"\b(sorry|admit|native_decide|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler)\b"
    r"|^\s*(axiom|opaque|constant|unsafe)\b"
)


def mask_comments_and_strings(source: str) -> str:
    """Replace Lean comments and string contents with spaces, preserving lines."""
    masked: list[str] = []
    index = 0
    block_depth = 0
    in_string = False

    def mask(character: str) -> str:
        return "\n" if character == "\n" else " "

    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                masked.extend((" ", " "))
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                masked.extend((" ", " "))
                block_depth -= 1
                index += 2
            else:
                masked.append(mask(source[index]))
                index += 1
            continue

        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                masked.append(" ")
                masked.append(mask(source[index + 1]))
                index += 2
            else:
                character = source[index]
                masked.append(mask(character))
                index += 1
                if character == '"':
                    in_string = False
            continue

        if source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                masked.extend(" " for _ in source[index:])
                break
            masked.extend(" " for _ in source[index:newline])
            masked.append("\n")
            index = newline + 1
        elif source.startswith("/-", index):
            masked.extend((" ", " "))
            block_depth = 1
            index += 2
        elif source[index] == '"':
            masked.append(" ")
            in_string = True
            index += 1
        else:
            masked.append(source[index])
            index += 1

    return "".join(masked)


def tracked_lean_paths(root: Path) -> list[Path]:
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "*.lean"],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        detail = getattr(exc, "stderr", b"")
        message = os.fsdecode(detail).strip() if detail else str(exc)
        raise RuntimeError(f"could not enumerate tracked Lean files: {message}") from exc

    paths = [Path(os.fsdecode(raw)) for raw in result.stdout.split(b"\0") if raw]
    if not paths:
        raise RuntimeError("the repository contains no tracked Lean files to verify")

    missing = [path for path in paths if not (root / path).is_file()]
    if missing:
        joined = ", ".join(str(path) for path in missing)
        raise RuntimeError(f"tracked Lean files are missing from the checkout: {joined}")
    return paths


def forbidden_lines(root: Path, paths: Iterable[Path]) -> list[str]:
    findings: list[str] = []
    for relative in paths:
        source = (root / relative).read_text(encoding="utf-8")
        code = mask_comments_and_strings(source)
        for line_number, (source_line, code_line) in enumerate(
            zip(source.splitlines(), code.splitlines(), strict=True), start=1
        ):
            if FORBIDDEN.search(code_line):
                findings.append(f"{relative}:{line_number}: {source_line}")
    return findings


def self_test() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        (root / "TheoryLib").mkdir()
        (root / "TheoryLib.lean").write_text("import TheoryLib.Safe\n", encoding="utf-8")
        (root / "TheoryLib" / "Safe.lean").write_text(
            "/- axiom documented : True\n"
            "  /- nested unsafe def example -/\n"
            "-/\n"
            "-- `sorry` is forbidden in proof code.\n"
            'def quoted := "admit native_decide"\n'
            "theorem safe : True := by trivial\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "add", "TheoryLib.lean", "TheoryLib/Safe.lean"],
            cwd=root,
            check=True,
        )

        paths = tracked_lean_paths(root)
        expected = {Path("TheoryLib.lean"), Path("TheoryLib/Safe.lean")}
        if set(paths) != expected:
            raise AssertionError(f"unexpected tracked paths: {paths}")
        if findings := forbidden_lines(root, paths):
            raise AssertionError(f"comments or strings caused false positives: {findings}")

        untracked = root / "Untracked.lean"
        untracked.write_text("axiom bypass : True\n", encoding="utf-8")
        if Path("Untracked.lean") in tracked_lean_paths(root):
            raise AssertionError("an untracked Lean file entered the scan set")

        subprocess.run(["git", "add", "Untracked.lean"], cwd=root, check=True)
        findings = forbidden_lines(root, tracked_lean_paths(root))
        if len(findings) != 1 or not findings[0].startswith("Untracked.lean:1:"):
            raise AssertionError(f"tracked forbidden declaration was not rejected: {findings}")


def main(argv: list[str]) -> int:
    if argv == ["--self-test"]:
        self_test()
        print("PASS: tracked-Lean scanner self-test succeeded.")
        return 0
    if argv:
        print("usage: scan_tracked_lean.py [--self-test]", file=sys.stderr)
        return 2

    project_root = Path(__file__).resolve().parents[2]
    try:
        paths = tracked_lean_paths(project_root)
        findings = forbidden_lines(project_root, paths)
    except (RuntimeError, OSError, UnicodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    print(f"Scanning {len(paths)} tracked Lean files for forbidden trust shortcuts.")
    if findings:
        for finding in findings:
            print(finding, file=sys.stderr)
        print(
            "ERROR: forbidden placeholder, axiom, or compiler-trusting shortcut found.",
            file=sys.stderr,
        )
        return 1

    print("PASS: every tracked Lean file passed the shortcut scan.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
