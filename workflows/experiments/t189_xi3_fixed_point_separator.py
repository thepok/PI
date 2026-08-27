#!/usr/bin/env python3
"""Directed replay of the all-three fixed-point separator for T189.

For ``q=1000, A=334, d=3`` the decimal fixed orbit ``x_n=1/3`` cancels
the two digit characters in T189.  This script evaluates the remaining
single-step kernel with T142's exact piecewise coefficients and the existing
100-digit outward interval arithmetic.

This is an ``experiment`` artifact, not a Lean proof.
"""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction

from t170_signed_parent_334_interval import CIv, Iv, phase_interval


Q = 10_000
T = Fraction(-7, 6000)
ROBUST_XI3_THRESHOLD = Decimal("-1.6411755067")


def positive_coefficient(h: int) -> Iv:
    """T142's exact ``positiveBoundaryCoefficient Q h`` formula."""
    if not 1 <= h <= 2 * Q - 1:
        raise ValueError(h)
    if h <= Q:
        fejer = Fraction(
            4 * Q**3 + 2 * Q - 6 * Q * h**2 + 3 * h**3 - 3 * h,
            6 * Q**2,
        )
        edge = Fraction(3 * h - 2 * Q, 2 * Q**2)
    else:
        fejer = Fraction(
            (2 * Q - h - 1) * (2 * Q - h) * (2 * Q - h + 1),
            6 * Q**2,
        )
        edge = Fraction(2 * Q - h, 2 * Q**2)
    cos_pi_div_q = phase_interval(
        Fraction(1, 2 * Q), Fraction(1, 2 * Q)
    ).re
    return (Iv.point(1) - cos_pi_div_q) * fejer + edge


def fixed_point_step() -> Iv:
    total = CIv.zero()
    for r in range(1, 10):
        inner = CIv.zero()
        for ell in range(2000):
            inner += phase_interval(ell * T, ell * T) * positive_coefficient(
                10 * ell + r
            )
        total += (
            phase_interval(Fraction(r, 10) * T, Fraction(r, 10) * T)
            * inner
        ) * 10
    return total.re


def main() -> None:
    step = fixed_point_step()
    block_48 = 48 * step
    block_49 = 49 * step
    assert step.hi < Decimal("-0.034")
    assert block_48.lo > ROBUST_XI3_THRESHOLD
    assert block_49.hi < ROBUST_XI3_THRESHOLD
    print(f"K in [{step.lo}, {step.hi}]")
    print(f"48*K in [{block_48.lo}, {block_48.hi}]")
    print(f"49*K in [{block_49.lo}, {block_49.hi}]")


if __name__ == "__main__":
    main()
