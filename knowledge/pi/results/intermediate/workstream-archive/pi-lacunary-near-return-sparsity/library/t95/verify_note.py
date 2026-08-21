#!/usr/bin/env python3
"""Self-contained replay checks for the T95 exact-word note.

The exhaustive checks below are experiments only. The universal conclusion
rests on the numbered symbolic proof in REPORT.md.
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


def exhaustive_binary_max(n: int) -> tuple[int, int, int]:
    starts = 2 ** (n // 2)
    length = starts + n - 1
    best = (-10**9, 0, 0)
    for word in itertools.product(range(2), repeat=length):
        short, remote = collision_counts(word, n, starts)
        candidate = (2 * short - 3 * remote, short, remote)
        if candidate[0] > best[0]:
            best = candidate
    return best


def constant(base: int) -> Fraction:
    return Fraction(25, 6) * (
        4 + Fraction(9 * base * base * (base + 1), (base - 1) ** 3)
    )


def check_per_label_algebra() -> None:
    # Bounded exact-rational replay of the universally proved square identity.
    for m in range(21):
        for q in range(1, 21):
            square = Fraction((5 * q - 3 * m) ** 2, 6)
            difference = (
                Fraction(25 * q * q, 6)
                - 5 * m * q
                + Fraction(3 * m * m, 2)
            )
            assert square == difference >= 0


def check_period_counting() -> None:
    # A word with period p is determined by its first p symbols.
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
    imports = (ROOT / "T95StatisticImports.lean").read_text()
    required_report_text = [
        "ordered and off-diagonal",
        "The short range is strict",
        "remote range includes lag `n`",
        "exactly `L` starts",
        "length at least `L+n-1`",
        "constant depends only on the fixed base `b`",
        "only Review B's exact-word sibling",
        "It implies nothing",
        "about T56/C7",
        "canonical fixed-`pi` question",
        "C1, or C2",
    ]
    for text in required_report_text:
        assert text in report, text
    assert "T83T83LiteralStatisticAudit" in imports
    assert "T92T92ConstantRunDiscriminator" in imports
    assert "def " not in imports


def main() -> None:
    assert sha256(ROOT / "canonical_statement.txt") == CANONICAL_SHA256
    check_report_contract()
    check_per_label_algebra()
    check_period_counting()

    # These are bounded sanity checks, not evidence for the universal theorem.
    expected = [0, 4, 4, 24, 24, 82]
    observed = []
    for n, expected_numerator in enumerate(expected, start=1):
        numerator, short, remote = exhaustive_binary_max(n)
        assert numerator == expected_numerator, (n, numerator, short, remote)
        observed.append(numerator)

    assert constant(2) == Fraction(1400, 3)
    for base in range(2, 30):
        assert constant(base) > 0

    print("T95 replay passed")
    print(f"canonical SHA-256: {CANONICAL_SHA256}")
    print("bounded binary maxima n=1..6:", observed)
    print("C_2 from the universal proof:", constant(2))
    print("universal conclusion source: numbered symbolic proof, not finite search")


if __name__ == "__main__":
    main()
