#!/usr/bin/env python3
"""Exact arithmetic checks for the T19 examples.

The analytic inequalities are proved in REPORT.md. This script checks only
the rational orbit, congruence, ceiling, and denominator arithmetic.
"""

from fractions import Fraction


def frac_part(x: Fraction) -> Fraction:
    return x - (x.numerator // x.denominator)


def orbit(beta: Fraction, length: int) -> list[Fraction]:
    return [frac_part(beta * 10**j) for j in range(length)]


def ceil_fraction(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def exact_period(beta: Fraction, s: int) -> bool:
    return ((10**s - 1) * beta).denominator == 1


def main() -> None:
    beta_9 = Fraction(1, 9)
    assert orbit(beta_9, 5) == [beta_9] * 5
    assert exact_period(beta_9, 1)

    beta_99 = Fraction(1, 99)
    assert orbit(beta_99, 6) == [Fraction(1, 99), Fraction(10, 99)] * 3
    assert not exact_period(beta_99, 1)
    assert exact_period(beta_99, 2)

    beta_11 = Fraction(1, 11)
    assert orbit(beta_11, 6) == [Fraction(1, 11), Fraction(10, 11)] * 3
    assert not exact_period(beta_11, 1)
    assert exact_period(beta_11, 2)

    beta_20 = Fraction(1, 20)
    assert orbit(beta_20, 6) == [Fraction(1, 20), Fraction(1, 2), 0, 0, 0, 0]

    delta = Fraction(4, 5)
    kappa = delta / (2 - delta)
    assert kappa == Fraction(2, 3)
    g0 = ceil_fraction(kappa * 20)
    s_star = (20 - 1) // (g0 - 1)
    assert g0 == 14
    assert s_star == 1

    # For a<=0, |9-20a|>=9; for a>=1, |9-20a|>=11. These
    # boundary values certify the two cases in the universal proof (27).
    assert abs(9 - 20 * 0) == 9
    assert abs(9 - 20 * 1) == 11
    assert Fraction(9, 180) == Fraction(1, 20)

    # Exact preperiod witness in (28).
    assert 10**2 * (10 - 1) * beta_20 == 45

    # Rational comparisons used in (22) and (24).
    assert Fraction(1, 99) < Fraction(1, 27)
    assert abs(Fraction(1, 11) - Fraction(1, 9)) == Fraction(2, 99)
    assert Fraction(2, 99) < Fraction(1, 27)

    print("T19 exact checks passed")
    print("1/9: period 1")
    print("1/99: least period 2")
    print("1/11: least period 2")
    print("1/20: preperiod 2, then fixed at 0")
    print("M=20, delta=4/5: g0=14, Sstar=1, witness (j,s,a)=(2,1,45)")


if __name__ == "__main__":
    main()
