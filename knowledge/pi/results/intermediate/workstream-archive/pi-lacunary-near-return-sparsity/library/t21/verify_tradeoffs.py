#!/usr/bin/env python3
"""Exact finite checks supporting T21's prose proof.

These checks replay rational examples, closed recursions, and rounding
identities. Finite computation is not a proof of the general theorem or A1.
"""

from fractions import Fraction
from itertools import combinations
def frac_part(x: Fraction) -> Fraction:
    return x - (x.numerator // x.denominator)


def orbit(beta: Fraction, length: int) -> list[Fraction]:
    return [frac_part(beta * 10**j) for j in range(length)]


def ceil_fraction(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def density(D: int, d: int) -> int:
    for _ in range(d):
        D = 8 * D * D
    return D


def threshold(D: int, K: int, q: int, d: int) -> int:
    if d == 0:
        return K
    residual = threshold(8 * D * D, K, q + 1, d - 1)
    return max(8 * D * D, 16 * (1 + q + residual) * D * D)


def check_recursions() -> None:
    for A in (1, 2, 5):
        for n in (1, 3):
            D0 = 2**17 * A * A * n * n
            for d in range(6):
                closed_D = 2 ** (20 * 2**d - 3) * (A * n) ** (2 ** (d + 1))
                assert density(D0, d) == closed_D
                C = 1
                E = 0
                prefix = 1
                for i in range(d):
                    lam = 16 * density(D0, i) ** 2
                    C *= lam
                    prefix *= lam
                    E += (i + 2) * prefix
                for K in (1, 2, 7):
                    assert threshold(D0, K, 1, d) == C * K + E


def check_rounding_frontiers() -> None:
    # Rational rho makes every ceiling and floor exact. Check the weak and
    # strict sharp uniform period bounds on a broad finite grid.
    for denominator in range(1, 41):
        for numerator in range(1, denominator + 1):
            rho = Fraction(numerator, denominator)
            # floor(2/rho)-1, written explicitly for exact arithmetic.
            weak_uniform = (2 * rho.denominator // rho.numerator) - 1
            for M in range(2, 301):
                g0 = ceil_fraction(rho * M)
                if g0 >= 2:
                    weak = (M - 1) // (g0 - 1)
                    assert weak <= weak_uniform

                strict_den = (rho * M).numerator // (rho * M).denominator
                if rho < 1 and strict_den >= 1:
                    strict = (M - 1) // strict_den
                    strict_uniform = ceil_fraction(2 / rho) - 2
                    assert strict <= strict_uniform


def check_combinatorial_pareto() -> None:
    # Exhaust all good-index sets in small windows and verify the first-ell
    # gap bounds used in (1.11)--(1.12).
    for M in range(2, 13):
        indices = range(M)
        for g in range(2, M + 1):
            for selected in combinations(indices, g):
                for g0 in range(2, g + 1):
                    for ell in range(1, g0):
                        b_ell = selected[ell]
                        assert b_ell <= M - g0 + ell
                        gaps = [selected[v + 1] - selected[v] for v in range(ell)]
                        s = min(gaps)
                        v = gaps.index(s)
                        j = selected[v]
                        period_bound = (M - g0 + ell) // ell
                        assert 1 <= s <= period_bound
                        assert j <= M - g0 + ell - 1
                        assert j + s <= M - g0 + ell


def check_examples() -> None:
    beta_9 = Fraction(1, 9)
    assert orbit(beta_9, 5) == [beta_9] * 5
    assert (10 - 1) * beta_9 == 1

    beta_99 = Fraction(1, 99)
    assert orbit(beta_99, 6) == [Fraction(1, 99), Fraction(10, 99)] * 3
    assert ((10 - 1) * beta_99).denominator != 1
    assert ((10**2 - 1) * beta_99).denominator == 1
    assert beta_99 < Fraction(1, 27)

    beta_11 = Fraction(1, 11)
    assert orbit(beta_11, 6) == [Fraction(1, 11), Fraction(10, 11)] * 3
    assert ((10 - 1) * beta_11).denominator != 1
    assert ((10**2 - 1) * beta_11).denominator == 1
    assert abs(beta_11 - Fraction(1, 9)) == Fraction(2, 99)
    assert Fraction(2, 99) < Fraction(1, 27)

    beta_20 = Fraction(1, 20)
    assert orbit(beta_20, 6) == [Fraction(1, 20), Fraction(1, 2), 0, 0, 0, 0]
    delta = Fraction(4, 5)
    tau = Fraction(2, 5)
    rho = (delta - tau) / (1 - tau)
    assert rho == Fraction(2, 3)
    assert ceil_fraction(rho * 20) == 14
    assert (rho * 20).numerator // (rho * 20).denominator + 1 == 14
    assert (20 - 1) // 13 == 1
    assert abs(9 - 20 * 0) == 9
    assert abs(9 - 20 * 1) == 11
    assert Fraction(9, 180) == Fraction(1, 20)
    assert 10**2 * (10 - 1) * beta_20 == 45


def check_t19_specialization() -> None:
    for D in range(1, 100):
        theta = Fraction(1, 2)
        rho = (1 - theta) / (D - theta)
        assert rho == Fraction(1, 2 * D - 1)
        # T19's weak threshold L>=2D implies ceil(L/(2D-1))>=2.
        L = 2 * D
        assert ceil_fraction(rho * L) >= 2
        weak_period = (L - 1) // (ceil_fraction(rho * L) - 1)
        assert weak_period <= 4 * D - 3
        # Strict T13 permits the endpoint L=2D-1.
        Ls = 2 * D - 1
        assert (rho * Ls).denominator == 1
        assert (rho * Ls) == 1
        assert (Ls - 1) // 1 == 2 * D - 2


def main() -> None:
    check_recursions()
    check_rounding_frontiers()
    check_combinatorial_pareto()
    check_examples()
    check_t19_specialization()
    print("T21 exact finite checks passed")
    print("checked T13 recursions, tau frontiers, Pareto gaps, and four examples")
    print("finite checks are not a proof of the general lemma or canonical A1")


if __name__ == "__main__":
    main()
