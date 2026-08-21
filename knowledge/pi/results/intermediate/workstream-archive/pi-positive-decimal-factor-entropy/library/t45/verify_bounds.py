#!/usr/bin/env python3
"""Exact arithmetic replay for T45's displayed finite constants.

This script checks identities and finite samples only. The universal proof is
the prose argument in T45_FIBONACCI_FEJER_SEPARATION.md.
"""

from fractions import Fraction
from math import floor


def fibonacci_prefix(length: int) -> str:
    word = "0"
    while len(word) < length:
        word = "".join("01" if digit == "0" else "0" for digit in word)
    return word[:length]


def check_parameters(n: int) -> None:
    m = 10**n
    h = m // 2
    d = floor(n / 3) + 1
    ell = (m + d - 1) // d

    assert 2 * h == m
    assert d > Fraction(n, 3)
    assert Fraction(ell, m) <= Fraction(1, d) + Fraction(1, m)
    assert sum(10**r for r in range(n)) == (m - 1) // 9

    for r in range(n):
        assert 10**r < h


def check_finite_word(sample_length: int) -> None:
    word = fibonacci_prefix(sample_length)
    assert word.startswith("010010100100101001010010010100")

    # Finite replay only: detect literal fourth powers wholly in this prefix.
    for start in range(sample_length):
        max_period = (sample_length - start) // 4
        for period in range(1, max_period + 1):
            block = word[start : start + period]
            assert word[start : start + 4 * period] != block * 4


def main() -> None:
    for n in range(1, 31):
        check_parameters(n)
    check_finite_word(5000)
    print("T45 arithmetic replay passed for n=1..30")
    print("No fourth power found in the first 5000 generated digits (experiment only)")


if __name__ == "__main__":
    main()
