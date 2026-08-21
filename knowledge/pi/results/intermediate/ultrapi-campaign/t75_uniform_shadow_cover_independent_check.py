#!/usr/bin/env python3
"""Independent structural and kernel replay for T75.

The checker proves no BBP covering estimate.  It verifies only that the
abstract T75 implication is present, registered, free of forbidden proof
shortcuts, and independently rederived by the companion Lean audit.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
T75 = Path("TheoryLib/PiQuantitativeBlockHitting/T75T75UniformShadowCover.lean")
T72 = Path("TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean")
REPLAY = Path("work/ultrapi-resume/t75_uniform_shadow_cover_independent_replay.lean")

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    T72:
        "c5b59557d1d95a26c0c451d9cd8d62d073d3d7f918467e5b2b888233d2c83373",
    T75:
        "002cac6a91c36f1e23499c16c0fafd1c259d5d93b974697ffc512ca4d6e4cc9b",
    REPLAY:
        "c144ad045d93f433256ba3264a2d18be4af145ddc4c4f6969bd5b7bca18e24ee",
}

TARGETS = (
    "Theory.PiDigits.T75UniformShadowCover."
        "uniformShadowCover_implies_circleDenseArbitrarilyLate",
    "Theory.PiDigits.T75UniformShadowCover."
        "circleDenseArbitrarilyLate_implies_coloredRepunitReturns",
    "Theory.PiDigits.T75UniformShadowCover."
        "uniformShadowCover_implies_coloredRepunitReturns",
    "Theory.PiDigits.T75UniformShadowCover."
        "pi_uniformShadowCover_implies_canonicalV1",
)

REPLAY_TARGETS = (
    "T75UniformShadowCoverIndependentReplay."
        "replay_uniformShadowCover_implies_circleDenseArbitrarilyLate",
    "T75UniformShadowCoverIndependentReplay.replay_zero_endpoint_return",
    "T75UniformShadowCoverIndependentReplay.replay_interior_return",
    "T75UniformShadowCoverIndependentReplay."
        "replay_circleDenseArbitrarilyLate_implies_coloredRepunitReturns",
    "T75UniformShadowCoverIndependentReplay."
        "replay_pi_uniformShadowCover_implies_canonicalV1",
)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def run_lean(path: Path) -> str:
    result = subprocess.run(
        ["lake", "env", "lean", "--trust=0", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode:
        sys.stdout.write(result.stdout)
        raise AssertionError(f"Lean failed for {path}")
    return result.stdout


def assert_axioms(output: str, names: tuple[str, ...]) -> None:
    for name in names:
        match = re.search(
            rf"'{re.escape(name)}' depends on axioms: \[(.*?)\]",
            output,
            flags=re.DOTALL,
        )
        assert match is not None, f"missing #print axioms record for {name}"
        observed = {part.strip() for part in match.group(1).split(",")}
        assert observed == ALLOWED_AXIOMS, (name, observed)


def assert_no_forbidden(path: Path) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "axiom declaration": r"(?m)^\s*axiom\s+",
        "opaque declaration": r"(?m)^\s*opaque\s+",
        "unsafe declaration": r"(?m)^\s*unsafe\s+(?:def|theorem)\s+",
    }
    for label, pattern in patterns.items():
        assert re.search(pattern, text) is None, f"{label} found in {path}"


def main() -> None:
    for path, expected in PINS.items():
        actual = digest(path)
        assert actual == expected, f"hash mismatch for {path}: {actual}"

    assert_no_forbidden(T75)
    assert_no_forbidden(REPLAY)

    barrel = (ROOT / "TheoryLib.lean").read_text(encoding="utf-8")
    audit = (ROOT / "audit/AxiomAudit.lean").read_text(encoding="utf-8")
    import_line = (
        "import TheoryLib.PiQuantitativeBlockHitting."
        "T75T75UniformShadowCover"
    )
    assert barrel.count(import_line) == 1
    assert audit.count(import_line) == 1
    for name in TARGETS:
        assert audit.count(name) == 1, f"audit registration count for {name}"

    t75_output = run_lean(T75)
    assert_axioms(t75_output, TARGETS)

    replay_output = run_lean(REPLAY)
    assert_axioms(replay_output, REPLAY_TARGETS)

    run_lean(Path("TheoryLib.lean"))
    audit_output = run_lean(Path("audit/AxiomAudit.lean"))
    assert_axioms(audit_output, TARGETS)

    print(
        "PASS: T75 hashes, registrations, forbidden-pattern scan, trust=0 "
        "kernel builds, exact target axiom sets, and independent endpoint "
        "replay all succeeded; no BBP cover premise was asserted."
    )


if __name__ == "__main__":
    main()
