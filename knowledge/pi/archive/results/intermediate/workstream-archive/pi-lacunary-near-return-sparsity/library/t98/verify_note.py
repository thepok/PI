#!/usr/bin/env python3
"""Self-contained experiments and contract checks for the T98 note.

Finite enumeration is not evidence for the universal charging theorem. The
universal argument is the numbered paper proof in REPORT.md.
"""

from __future__ import annotations

import hashlib
import itertools
import pathlib
from fractions import Fraction


ROOT = pathlib.Path(__file__).resolve().parent
CANONICAL_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def charging_constant(base: int) -> Fraction:
    assert base >= 2
    return Fraction(25, 6) * (
        4 + Fraction(9 * base * base * (base + 1), (base - 1) ** 3)
    )


def collision_counts(word: tuple[int, ...], n: int, starts: int) -> tuple[int, int]:
    blocks = [word[i : i + n] for i in range(starts)]
    short = 0
    remote = 0
    for i in range(starts):
        for j in range(starts):
            if i == j or blocks[i] != blocks[j]:
                continue
            if abs(i - j) < n:
                short += 1
            else:
                remote += 1
    return short, remote


def exhaustive_binary_max(n: int) -> Fraction:
    starts = 2 ** (n // 2)
    length = starts + n - 1
    maximum = None
    for word in itertools.product(range(2), repeat=length):
        short, remote = collision_counts(word, n, starts)
        value = Fraction(2 * short - 3 * remote, 2 * starts)
        maximum = value if maximum is None else max(maximum, value)
    assert maximum is not None
    return maximum


def check_square_identity() -> None:
    # Bounded exact-rational sanity check of equation (5.7).
    for multiplicity in range(31):
        for occupancy in range(1, 31):
            lhs = (
                Fraction(25 * occupancy * occupancy, 6)
                - 5 * multiplicity * occupancy
                + Fraction(3 * multiplicity * multiplicity, 2)
            )
            rhs = Fraction((5 * occupancy - 3 * multiplicity) ** 2, 6)
            assert lhs == rhs >= 0


def check_period_word_count() -> None:
    # A period-p word is determined by exactly its first p symbols.
    for base in (2, 3):
        for n in range(1, 7):
            for period in range(1, n + 1):
                count = 0
                for word in itertools.product(range(base), repeat=n):
                    if all(word[t] == word[t + period] for t in range(n - period)):
                        count += 1
                assert count == base**period


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    imports = (ROOT / "T98StatisticImports.lean").read_text()
    required = [
        "only a cross-program soundness audit",
        "T67's terminal-ray comparator",
        "ordered and off-diagonal",
        "Lag `n` is long",
        "signed integer range is strict",
        "triangular boundary",
        "Vaaler majorant directly",
        "C_{10}=",
        "17800}{243",
        "18043}{81",
        r"\frac{15}{2}K",
        "not a fixed-`pi`",
        "not a claim about canonical A1, C1, or C2",
    ]
    for text in required:
        assert text in report, text
    for module in (
        "T83T83LiteralStatisticAudit",
        "T92T92ConstantRunDiscriminator",
        "T61T61VaalerAnalytic",
        "T2T2UniformLongLagResidual",
    ):
        assert module in imports
    assert "theorem " not in imports
    assert "def " not in imports


def main() -> None:
    assert sha256(ROOT / "canonical_statement.txt") == CANONICAL_SHA256
    check_report_contract()
    check_square_identity()
    check_period_word_count()

    c10 = charging_constant(10)
    assert c10 == Fraction(17800, 243)
    q_linear = 3 * (c10 + 1)
    assert q_linear == Fraction(18043, 81)
    assert 17 * q_linear == Fraction(306731, 81)

    observed = [exhaustive_binary_max(n) for n in range(1, 7)]
    expected = [
        Fraction(0),
        Fraction(1),
        Fraction(1),
        Fraction(3),
        Fraction(3),
        Fraction(41, 8),
    ]
    assert observed == expected, observed

    print("T98 replay passed")
    print(f"canonical SHA-256: {CANONICAL_SHA256}")
    print(f"C_10: {c10}")
    print(f"Q linear coefficient before residual-long term: {q_linear}")
    print("bounded binary normalized maxima n=1..6:", observed)
    print("universal source: numbered paper proof, not finite enumeration")


if __name__ == "__main__":
    main()
