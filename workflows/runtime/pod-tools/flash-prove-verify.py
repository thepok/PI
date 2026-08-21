#!/usr/bin/env python3
"""Verify an agentically-edited Lean candidate against its original.

Usage: flash-prove-verify.py ORIG.lean CAND.lean
Checks (independent of anything the agent claimed):
  1. CAND differs from ORIG only by replacing the single bare `sorry` line
     with a non-empty proof block (nothing else changed anywhere, imports
     included).
  2. The inserted region contains no banned construct
     (sorry/admit/native_decide/axiom/new imports/set_option/search tactics).
On success prints the inserted body between BEGIN_BODY/END_BODY, exit 0.
Compilation is checked separately by the caller.
"""
import re
import sys
from difflib import SequenceMatcher

orig_path, cand_path = sys.argv[1], sys.argv[2]
orig = open(orig_path).read().splitlines()
cand = open(cand_path).read().splitlines()

sorry_lines = [i for i, l in enumerate(orig) if re.fullmatch(r"\s*sorry\s*", l)]
if len(sorry_lines) != 1:
    sys.exit(
        "REJECT: original must contain exactly one bare sorry line, "
        f"found {len(sorry_lines)}"
    )
hole = sorry_lines[0]

ops = SequenceMatcher(None, orig, cand, autojunk=False).get_opcodes()
changes = [op for op in ops if op[0] != "equal"]
if len(changes) != 1:
    sys.exit(
        f"REJECT: expected exactly one changed region, found {len(changes)}: "
        f"{changes}"
    )
tag, i1, i2, j1, j2 = changes[0]
if not (i1 <= hole < i2):
    sys.exit(
        f"REJECT: change at orig lines {i1}-{i2} does not cover the sorry "
        f"line {hole + 1}"
    )
removed = orig[i1:i2]
if [l for l in removed if not re.fullmatch(r"\s*sorry\s*", l)]:
    sys.exit(f"REJECT: change removes original lines beyond the sorry: {removed}")
body = cand[j1:j2]
if not any(l.strip() for l in body):
    sys.exit("REJECT: empty replacement body")

banned = re.compile(
    r"\b(sorry|admit|native_decide)\b|^\s*(axiom|import|attribute|set_option)\b|"
    r"exact\?|apply\?|rw\?|simp\?", re.M)
m = banned.search("\n".join(body))
if m:
    sys.exit(f"REJECT: banned construct in body: {m.group(0)!r}")

print("BEGIN_BODY")
print("\n".join(body))
print("END_BODY")
