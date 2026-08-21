#!/usr/bin/env python3
"""Idempotently promote the staged GP-0002 T110 candidate.

Run only in a clean checkout. The script refuses to overwrite a different
canonical T110 module, copies the staged candidate into `TheoryLib/`, and then
registers it in the canonical import and central axiom-audit surfaces.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CANDIDATE = ROOT / "GPTPro" / "Deliverables" / "GP-0002" / "T110Candidate.lean"
TARGET = (
    ROOT
    / "TheoryLib"
    / "PiQuantitativeBlockHitting"
    / "T110T110PostT17CancellationCriterion.lean"
)
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


def install_candidate() -> bool:
    candidate_text = CANDIDATE.read_text(encoding="utf-8")
    if TARGET.exists():
        target_text = TARGET.read_text(encoding="utf-8")
        if target_text != candidate_text:
            raise RuntimeError(
                f"refusing to overwrite a different canonical module: {TARGET}"
            )
        return False
    TARGET.write_text(candidate_text, encoding="utf-8")
    return True


def insert_after_unique(path: Path, marker: str, insertion: str) -> bool:
    text = path.read_text(encoding="utf-8")
    if insertion in text:
        return False
    count = text.count(marker)
    if count != 1:
        raise RuntimeError(
            f"expected exactly one marker in {path}: {marker!r}; found {count}"
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
    if install_candidate():
        changed.append(str(TARGET.relative_to(ROOT)))
    if insert_after_unique(THEORYLIB, T109_IMPORT, T110_IMPORT):
        changed.append(str(THEORYLIB.relative_to(ROOT)))
    if insert_after_unique(AUDIT, T109_IMPORT, T110_IMPORT):
        changed.append(str(AUDIT.relative_to(ROOT)) + " (import)")
    if append_unique(AUDIT, T110_AUDIT):
        changed.append(str(AUDIT.relative_to(ROOT)) + " (#print axioms)")

    if changed:
        print("staged T110 promotion:")
        for item in changed:
            print(f"- {item}")
    else:
        print("T110 was already promoted; no changes")


if __name__ == "__main__":
    main()
