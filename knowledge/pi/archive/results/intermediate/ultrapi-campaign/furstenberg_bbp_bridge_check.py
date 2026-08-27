#!/usr/bin/env python3
"""Exact replay checks for furstenberg_bbp_bridge.md.

This script checks only rational/polynomial identities and finite recurrences.
It is an experiment under the repository claim vocabulary, not a proof of V1.
"""

from __future__ import annotations

from fractions import Fraction

import sympy as sp


def bbp_coefficient(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def partial_sum(n: int) -> Fraction:
    return sum((bbp_coefficient(k) / 16**k for k in range(n + 1)), Fraction())


def frac(x: Fraction) -> Fraction:
    return x - (x.numerator // x.denominator)


def symbolic_checks() -> None:
    k = sp.symbols("k", integer=True, nonnegative=True)
    original = (
        4 / (8 * k + 1)
        - 2 / (8 * k + 4)
        - 1 / (8 * k + 5)
        - 1 / (8 * k + 6)
    )
    numerator = 120 * k**2 + 151 * k + 47
    denominator = (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)
    simplified = numerator / denominator
    assert sp.cancel(original - simplified) == 0

    # For k >= 1 this positive-coefficient polynomial proves c_k <= 1/k^2.
    certificate = sp.Poly(sp.expand(denominator - k**2 * numerator), k)
    assert certificate.all_coeffs() == [392, 873, 665, 194, 15]
    assert all(coefficient > 0 for coefficient in certificate.all_coeffs())
    print("PASS symbolic BBP coefficient identity")
    print("PASS tail-majorant certificate:", certificate.as_expr())


def recurrence_checks(limit: int = 48) -> None:
    sums = [partial_sum(n) for n in range(limit + 1)]

    # Natural hexadecimal recurrence h_n = {16^n A_n}.
    h = [frac(16**n * sums[n]) for n in range(limit + 1)]
    for n in range(limit):
        expected = frac(16 * h[n] + bbp_coefficient(n + 1))
        assert h[n + 1] == expected

    # Decimal-reweighted recurrence u_n = {10^n A_n}.
    u = [frac(10**n * sums[n]) for n in range(limit + 1)]
    for n in range(limit):
        forcing = bbp_coefficient(n + 1) * Fraction(5, 8) ** (n + 1)
        expected = frac(10 * u[n] + forcing)
        assert u[n + 1] == expected

    # Finite-tail form of the exact coboundary identity.  Replacing pi by A_M
    # makes every quantity rational while leaving the algebra unchanged.
    total = sums[limit]
    decimal_tail = [10**n * (total - sums[n]) for n in range(limit + 1)]
    hexadecimal_tail = [16**n * (total - sums[n]) for n in range(limit + 1)]
    for n in range(limit):
        decimal_forcing = bbp_coefficient(n + 1) * Fraction(5, 8) ** (n + 1)
        assert decimal_forcing == 10 * decimal_tail[n] - decimal_tail[n + 1]
        assert frac(h[n] + hexadecimal_tail[n]) == frac(16**n * total)
        assert frac(u[n] + decimal_tail[n]) == frac(10**n * total)

    print(f"PASS exact hexadecimal and decimal recurrences through N={limit}")
    print(f"PASS exact finite-tail coboundary identities through N={limit}")


def arithmetic_checks() -> None:
    # If 10^a = 16^b with a,b > 0, comparison of 5-adic valuations forces a=0.
    # The loop is a finite sanity check; the valuation sentence is the proof sketch.
    assert all(10**a != 16**b for a in range(1, 65) for b in range(1, 65))
    for k in range(1, 200):
        c = bbp_coefficient(k)
        assert 0 < c <= Fraction(1, k * k)
    print("PASS finite multiplicative-independence sanity check (1 <= a,b <= 64)")
    print("PASS coefficient inequalities for 1 <= k < 200")


if __name__ == "__main__":
    symbolic_checks()
    recurrence_checks()
    arithmetic_checks()
    print("ALL CHECKS PASSED (experiment; not a proof of decimal disjunctivity)")
