#!/usr/bin/env python3
"""Self-contained transcription checks for the T81 proof-sketch artifact.

Finite checks below audit hashes, source anchors, and exact integer algebra.
They are not evidence for canonical C1 or any universal mathematical claim.
"""

from __future__ import annotations

import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T73ManyChildResonance.lean": "34ec4af51b95e7e1e1a0a350357fedf4fb7c0427daaf8a53331c3767992727de",
    "T28AdjacentNodeCompatibility.lean": "f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "zeilberger-zudilin-2020.txt": "49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require_anchors(filename: str, anchors: tuple[str, ...]) -> None:
    text = (ROOT / filename).read_text(encoding="utf-8")
    for anchor in anchors:
        assert anchor in text, f"missing anchor in {filename}: {anchor!r}"


def require_line_contains(filename: str, line_number: int, anchor: str) -> None:
    # Preserve form-feed characters emitted by pdftotext so locators agree
    # with ordinary newline-based line numbering used by the source ledger.
    lines = (ROOT / filename).read_text(encoding="utf-8").split("\n")
    actual = lines[line_number - 1]
    assert anchor in actual, (filename, line_number, anchor, actual)


def parameters(a: int, n: int, children: int, residual: int) -> tuple[int, int, int, int]:
    d = 131072 * a * a * n * n
    e = 8 * d * d
    ambient = 16 * a * n * e * (children + residual + 3)
    harmonic_cap = 256 * a * n
    return d, e, ambient, harmonic_cap


def coefficient(h: int, r: int, s: int, j: int) -> int:
    return h * (10**r - 1) * (10**s - 1) * 10**j


def check_hashes_and_anchors() -> None:
    for filename, expected in EXPECTED_HASHES.items():
        actual = sha256(ROOT / filename)
        assert actual == expected, (filename, expected, actual)

    require_anchors(
        "canonical_statement.txt",
        (
            "pairs are ordered and the diagonal is included",
            "for every integer A >= 1",
            "there exists an integer N >= 1",
            "A*n*Q_pi(n,N) <= N^2",
        ),
    )
    require_anchors(
        "T73ManyChildResonance.lean",
        (
            "def goodMiddleShifts",
            "theorem goodMiddleShifts_card_lower",
            "3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2",
            "manyChildLengthThreshold (D children R : ℕ)",
            "literal_not_canonical_C1_implies_many_child_two_scale_resonances",
            "children ≤",
            "s ≤ N - r - R",
            "s ≠ r",
            "R ≤ N - r - s",
        ),
    )
    require_anchors(
        "T28AdjacentNodeCompatibility.lean",
        (
            "def AdjacentPairCompatible",
            "(Q0 : ℝ) * e1 + (U : ℝ) * (Q1 : ℝ) * e0 < 1",
            "def ExponentEightClosingBounds",
            "scaledIntegerError (chain.nodeCoefficient k) j0 s0 a0 *",
            "compatible_pair_contradicts_exponentEight",
        ),
    )
    require_anchors(
        "zeilberger-zudilin-2020.txt",
        (
            "irrationality measure",
            "7.10320533413700172750577342281",
            "World record",
        ),
    )
    require_line_contains("canonical_statement.txt", 2, "For real x write")
    require_line_contains("T73ManyChildResonance.lean", 305, "theorem literal_not_canonical_C1")
    require_line_contains("T73ManyChildResonance.lean", 313, "N = 16 * A * n")
    require_line_contains("T73ManyChildResonance.lean", 323, "children ≤")
    require_line_contains("T73ManyChildResonance.lean", 332, "s ≤ N - r - R")
    require_line_contains("T28AdjacentNodeCompatibility.lean", 91, "def AdjacentPairCompatible")
    require_line_contains("T28AdjacentNodeCompatibility.lean", 111, "def ExponentEightClosingBounds")
    require_line_contains("zeilberger-zudilin-2020.txt", 30, "irrationality measure")
    require_line_contains("zeilberger-zudilin-2020.txt", 676, "World record")
    require_line_contains("zeilberger-zudilin-2020.txt", 690, "7.10320533413700172750577342281")


def check_parameter_expansion() -> None:
    for a in range(1, 4):
        for n in range(1, 4):
            for children in range(1, 8):
                for residual in range(1, 8):
                    d, e, ambient, harmonic_cap = parameters(a, n, children, residual)
                    assert e == 8 * d**2
                    assert ambient == 128 * a * n * d**2 * (children + residual + 3)
                    assert harmonic_cap == 256 * a * n
                    assert ambient >= 128 * (children + residual + 3)
                    assert ambient >= 1


def check_coefficient_injectivity_and_height() -> None:
    # Bounded exact checks of the universal valuation argument in REPORT Sec. 7.
    for h in range(1, 5):
        for r in range(1, 6):
            ambient = 18
            seen: dict[int, tuple[int, int]] = {}
            for s in range(1, ambient - r):
                residual = ambient - r - s
                for j in range(residual):
                    q = coefficient(h, r, s, j)
                    assert q < h * 10 ** (ambient - 1)
                    assert q not in seen, (h, r, q, seen[q], (s, j))
                    seen[q] = (s, j)


def check_automatic_comparison() -> None:
    # Finite sanity checks only. REPORT (9.4)-(9.6) gives the universal proof.
    for a in range(1, 4):
        for n in range(1, 4):
            for children in range(1, 20):
                for residual in range(1, 20):
                    _d, e, ambient, harmonic_cap = parameters(a, n, children, residual)
                    assert children <= 2**children
                    assert residual <= 2**residual
                    assert children * residual <= 2 ** (children + residual)
                    assert ambient >= 128 * (children + residual + 3)
                    # Avoid materializing Q^7; compare decimal exponents exactly.
                    assert ambient - 1 >= children + residual + 2
                    assert 7 * (children + residual + 2) > children + residual
                    assert children * residual / e < 10 ** (children + residual + 2)
                    assert harmonic_cap >= 256


def check_greedy_thinning() -> None:
    # Exhaust finite subsets of a small coefficient interval.
    for cutoff in range(1, 6):
        universe = range(1, 11)
        for mask in range(1 << 10):
            values = [q for index, q in enumerate(universe) if mask & (1 << index)]
            retained: list[int] = []
            index = 0
            while index < len(values):
                q = values[index]
                retained.append(q)
                index += 1
                while index < len(values) and values[index] - q < cutoff:
                    index += 1
            assert len(values) <= cutoff * len(retained)
            assert all(
                b - a >= cutoff
                for a, b in zip(retained, retained[1:])
            )


def main() -> None:
    check_hashes_and_anchors()
    check_parameter_expansion()
    check_coefficient_injectivity_and_height()
    check_automatic_comparison()
    check_greedy_thinning()
    print("T81 artifact checks passed")
    print("label: finite transcription/algebra sanity checks only; not proof of C1")


if __name__ == "__main__":
    main()
