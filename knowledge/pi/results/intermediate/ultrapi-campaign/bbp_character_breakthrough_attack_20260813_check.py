#!/usr/bin/env python3
"""Exact finite replay for the BBP scalar second-difference reduction.

All structural calculations use ``fractions.Fraction``.  The finite loops are
an experiment; the accompanying report contains the proofs for all indices.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems/local/pi-digits.txt"
PARENT = ROOT / "work/ultrapi-resume/bbp_one_character_return_attack.md"
PARENT_AUDIT = (
    ROOT / "work/ultrapi-resume/bbp_one_character_return_independent_audit.md"
)

PINS = {
    TARGET: "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    PARENT: "b49bfb3793dd87abf7b5dedaa820c87dfcf23ab3856e9fa67ef2462fbefecfab",
    PARENT_AUDIT: "b37b90d63fad6fb41e51397bf36373739e221eb8a85e65cb58bdfbceaeff7c80",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def a(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def b(k: int) -> Fraction:
    return a(k) / 16**k


def q(n: int) -> int:
    return 10**n - 16


def decreasing_numerator(k: int) -> int:
    return 3 * (
        40960 * k**5
        + 220672 * k**4
        + 453632 * k**3
        + 443480 * k**2
        + 206712 * k
        + 36903
    )


def decreasing_denominator(k: int) -> int:
    return (
        (2 * k + 1)
        * (2 * k + 3)
        * (4 * k + 3)
        * (4 * k + 7)
        * (8 * k + 1)
        * (8 * k + 5)
        * (8 * k + 9)
        * (8 * k + 13)
    )


def separator_r(n: int) -> Fraction:
    return Fraction(5, 8) ** n


def separator_error(n: int) -> Fraction:
    return Fraction(1, 3) * separator_r(n)


def separator_R(n: int) -> Fraction:
    return Fraction(q(n), 9) - separator_error(n)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=240)
    args = parser.parse_args()
    assert args.max_depth >= 8

    for path, expected in PINS.items():
        assert sha256(path) == expected, (path, sha256(path), expected)

    coefficient_checks = 0
    partial_sum_checks = 0
    scalar_checks = 0
    sign_checks = 0
    separator_checks = 0

    # The displayed positive polynomial proves a(k) > a(k+1) for every
    # k >= 0.  The loop only replays the identity at finite depth.
    for k in range(args.max_depth + 3):
        assert a(k) - a(k + 1) == Fraction(
            decreasing_numerator(k), decreasing_denominator(k)
        )
        assert a(k) > a(k + 1) > 0
        if k >= 1:
            assert a(k) < Fraction(1, k * k)
        coefficient_checks += 1

    B: list[Fraction] = []
    running = Fraction(0)
    for n in range(args.max_depth + 3):
        running += b(n)
        B.append(running)
        partial_sum_checks += 1

    R = [q(n) * B[n] for n in range(args.max_depth + 3)]
    C = [
        R[n + 1] - 10 * R[n]
        for n in range(args.max_depth + 2)
    ]

    for n in range(args.max_depth + 1):
        direct_C = 144 * B[n] + q(n + 1) * b(n + 1)
        direct_h = q(n + 2) * b(n + 2) + (160 - 10 ** (n + 1)) * b(n + 1)
        second_difference = R[n + 2] - 11 * R[n + 1] + 10 * R[n]
        assert C[n] == direct_C
        assert C[n + 1] - C[n] == direct_h == second_difference
        scalar_checks += 3

        if n == 0:
            assert direct_h == Fraction(20048317, 16336320) > 0
        elif n == 1:
            assert direct_h == Fraction(258249, 17353600) > 0
        else:
            # This is the rational inequality used in the all-index proof.
            upper = (Fraction(159) - Fraction(3, 8) * 10 ** (n + 1)) * b(n + 1)
            assert direct_h < upper < 0
        sign_checks += 1

    # Rational monotone-forcing separator.  R*_0 = -2 is integral, so the
    # partial products of its local phases are exactly e(R*_n); these remain
    # uniformly away from 1 after the initial index.
    previous_B_star: Fraction | None = None
    R_star_zero = separator_R(0)
    assert R_star_zero == -2
    for n in range(args.max_depth + 1):
        Rn = separator_R(n)
        Rn1 = separator_R(n + 1)
        Rn2 = separator_R(n + 2)
        Cn = Rn1 - 10 * Rn
        hn = Rn2 - 11 * Rn1 + 10 * Rn
        wn = Rn1 - Rn
        eps = separator_error(n)
        B_star = Rn / q(n)

        assert Cn == 16 + Fraction(25, 8) * separator_r(n)
        assert hn == -Fraction(75, 64) * separator_r(n)
        assert wn % 1 == Fraction(1, 8) * separator_r(n)
        assert (Rn - R_star_zero) % 1 == Rn % 1
        separator_checks += 4

        if n == 0:
            assert Rn % 1 == 0
            separator_checks += 1
        else:
            assert Rn % 1 == Fraction(1, 3) - eps
            assert eps <= Fraction(5, 24)
            assert min(Rn % 1, 1 - (Rn % 1)) >= Fraction(1, 8)
            separator_checks += 3

        if n >= 2:
            assert B_star < Fraction(1, 9)
            if previous_B_star is not None:
                assert B_star > previous_B_star
            previous_B_star = B_star
            separator_checks += 2

    print("status: PASS")
    print("claim_label: experiment")
    print(f"pinned_artifacts: {len(PINS)}")
    print(f"coefficient_checks: {coefficient_checks}")
    print(f"partial_sum_checks: {partial_sum_checks}")
    print(f"scalar_identity_checks: {scalar_checks}")
    print(f"sign_checks: {sign_checks}")
    print(f"separator_checks: {separator_checks}")
    print("exact_endpoint_signs: h_0>0,h_1>0,h_n<0_for_checked_n>=2")
    print("separator_gap_lower_bound: 1/8")
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all exact finite checks passed")


if __name__ == "__main__":
    main()
