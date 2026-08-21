#!/usr/bin/env python3
"""Idempotently register T110 in the canonical import and axiom-audit surfaces."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
THEORYLIB = ROOT / "TheoryLib.lean"
AUDIT = ROOT / "audit" / "AxiomAudit.lean"

T109_IMPORT = (
    "import TheoryLib.PiQuantitativeBlockHitting."
    "T109T109BBPSymbolicPackaging"
)
T110_IMPORT = (
    "import TheoryLib.PiQuantitativeBlockHitting."
    "T110T110PostT17CancellationCriterion"
)
T110_AUDIT = (
    "#print axioms "
    "Theory.PiDigits.T110PostT17CancellationCriterion."
    "C1_of_tail_aggregatedFourierSum_lt_of_powerTenDiophantine"
)


def insert_after_unique(path: Path, marker: str, insertion: str) -> bool:
    text = path.read_text(encoding="utf-8")
    if insertion in text:
        return False
    if text.count(marker) != 1:
        raise RuntimeError(
            f"expected exactly one marker in {path}: {marker!r}; "
            f"found {text.count(marker)}"
        )
    path.write_text(text.replace(marker, marker + "\n" + insertion, 1), encoding="utf-8")
    return True


def append_unique(path: Path, line: str) -> bool:
    text = path.read_text(encoding="utf-8")
    if line in text:
        return False
    path.write_text(text.rstrip() + "\n" + line + "\n", encoding="utf-8")
    return True


def main() -> None:
    changed = []
    if insert_after_unique(THEORYLIB, T109_IMPORT, T110_IMPORT):
        changed.append(str(THEORYLIB.relative_to(ROOT)))
    if insert_after_unique(AUDIT, T109_IMPORT, T110_IMPORT):
        changed.append(str(AUDIT.relative_to(ROOT)) + " (import)")
    if append_unique(AUDIT, T110_AUDIT):
        changed.append(str(AUDIT.relative_to(ROOT)) + " (#print axioms)")

    if changed:
        print("registered T110:")
        for item in changed:
            print(f"- {item}")
    else:
        print("T110 was already registered; no changes")


if __name__ == "__main__":
    main()
