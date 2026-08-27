#!/usr/bin/env python3
"""Independent exact finite checks for T53's two-level carry identities.

Finite checks are experiments, not proofs.  This script deliberately
reimplements Lean's natural-number division-by-zero convention so it also
tests T53's unconditional reconstruction identity at degenerate factors.
"""

from fractions import Fraction


def nat_div(n: int, d: int) -> int:
    return 0 if d == 0 else n // d


def nat_mod(n: int, d: int) -> int:
    return n if d == 0 else n % d


def fine_carry(r: int, f: int) -> int:
    return nat_div(10 * r, f)


def next_fine(r: int, f: int) -> int:
    return nat_mod(10 * r, f)


def decimal_carry(c: int, r: int, f: int, d: int) -> int:
    return nat_div(10 * c + fine_carry(r, f), d)


def next_coarse(c: int, r: int, f: int, d: int) -> int:
    return nat_mod(10 * c + fine_carry(r, f), d)


def next_numerator(c: int, r: int, f: int, d: int) -> int:
    return f * next_coarse(c, r, f, d) + next_fine(r, f)


def main() -> None:
    reconstruction_cases = 0
    for f in range(26):
        for d in range(26):
            for c in range(26):
                for r in range(26):
                    b = f * c + r
                    carry = decimal_carry(c, r, f, d)
                    nxt = next_numerator(c, r, f, d)
                    assert 10 * b == (f * d) * carry + nxt
                    reconstruction_cases += 1

    canonical_cases = 0
    for f in range(1, 65):
        for d in range(1, 65):
            for c in range(d):
                for r in range(f):
                    b = f * c + r
                    k = fine_carry(r, f)
                    r_next = next_fine(r, f)
                    c_next = next_coarse(c, r, f, d)
                    carry = decimal_carry(c, r, f, d)
                    nxt = next_numerator(c, r, f, d)

                    assert b < f * d
                    assert 0 <= k < 10
                    assert 0 <= r_next < f
                    assert 0 <= c_next < d
                    assert 0 <= nxt < f * d
                    assert 10 * b == (f * d) * carry + nxt
                    assert carry == (10 * b) // (f * d)
                    assert nxt == (10 * b) % (f * d)
                    assert nxt % f == r_next
                    assert nxt // f == c_next
                    assert 0 <= carry < 10
                    canonical_cases += 1

    rational_cases = 0
    for f in range(1, 25):
        for d in range(1, 25):
            for c in range(25):
                for r in range(25):
                    x = Fraction(f * c + r, f * d)
                    assert x == Fraction(c, d) + Fraction(r, f * d)
                    assert d * x == c + Fraction(r, f)
                    rational_cases += 1

    euclidean_cases = 0
    for f in range(33):
        for b in range(2049):
            assert f * nat_div(b, f) + nat_mod(b, f) == b
            if f > 0:
                assert nat_mod(b, f) < f
            euclidean_cases += 1

    quotient_bound_cases = 0
    for f in range(1, 65):
        for d in range(1, 65):
            for b in range(f * d):
                assert b // f < d
                quotient_bound_cases += 1

    print(f"unconditional reconstruction cases: {reconstruction_cases}")
    print(f"canonical two-level carry cases: {canonical_cases}")
    print(f"exact rational split cases: {rational_cases}")
    print(f"Euclidean reconstruction cases: {euclidean_cases}")
    print(f"coarse quotient bound cases: {quotient_bound_cases}")
    print("all T53 independent exact finite checks passed")


if __name__ == "__main__":
    main()
