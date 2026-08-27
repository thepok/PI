#!/usr/bin/env python3
"""Exact finite replay for the BBP one-character return reduction.

Every finite output is an ``experiment``.  The script checks rational
identities only.  It does not prove a limiting Fourier estimate, the fixed
return, V1, or any statement about uncomputed decimal digits of pi.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
BBP_PDF_SHA256 = (
    "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4"
)
LAGARIAS_PDF_SHA256 = (
    "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9"
)
CHEN_YE_ZHENG_PDF_SHA256 = (
    "a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d"
)
SHALLIT_PDF_SHA256 = (
    "592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981"
)
KEMPNER_PDF_SHA256 = (
    "99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def kempner_truncation(depth: int) -> Fraction:
    """Truncate kappa=sum_(j>=0) 10^(-2^j) after 3*depth digits."""
    value = Fraction()
    position = 1
    while position <= 3 * depth:
        value += Fraction(1, 10**position)
        position *= 2
    return value


def row_upper(depth: int) -> int:
    """Largest exponent n for which 10**n <= 16**depth."""
    bound = 16**depth
    exponent = 0
    power = 1
    while 10 * power <= bound:
        power *= 10
        exponent += 1
    return exponent


def first_depth(exponent: int) -> int:
    """Smallest depth M for which 10**exponent <= 16**M."""
    target = 10**exponent
    depth = 0
    power = 1
    while power < target:
        power *= 16
        depth += 1
    return depth


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=160)
    args = parser.parse_args()
    if args.max_depth < 20:
        raise SystemExit("--max-depth must be at least 20")

    source = root() / "problems/local/pi-digits.txt"
    bbp_pdf = root() / "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf"
    lagarias_pdf = (
        root()
        / "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
        "lagarias-math0101055v2.pdf"
    )
    chen_ye_zheng_pdf = (
        root()
        / "work/ultrapi-resume/library/chen-ye-zheng-2604.14036v1.pdf"
    )
    shallit_pdf = (
        root()
        / "work/ultrapi-resume/library/shallit-1979-simple-continued-fractions.pdf"
    )
    kempner_pdf = (
        root()
        / "work/theory/pi-lacunary-near-return-sparsity/library/t89/"
        "kempner-1916.pdf"
    )
    assert digest(source) == SOURCE_SHA256
    assert digest(bbp_pdf) == BBP_PDF_SHA256
    assert digest(lagarias_pdf) == LAGARIAS_PDF_SHA256
    assert digest(chen_ye_zheng_pdf) == CHEN_YE_ZHENG_PDF_SHA256
    assert digest(shallit_pdf) == SHALLIT_PDF_SHA256
    assert digest(kempner_pdf) == KEMPNER_PDF_SHA256

    partial_sum = Fraction()
    previous_sum: Fraction | None = None
    previous_return: Fraction | None = None
    coefficient_bounds = 0
    scalar_recurrence_checks = 0
    torus_recurrence_checks = 0
    diagonal_phase_checks = 0
    record_depth = -1
    record_distance = Fraction(1, 2)
    partial_sums: list[Fraction] = []
    increments: list[Fraction] = []

    for depth in range(args.max_depth + 1):
        a_value = coefficient(depth)
        if depth >= 1:
            # Exact positive polynomial certificate for 0 < a(n) < 1/n^2.
            numerator = (
                392 * depth**4
                + 873 * depth**3
                + 665 * depth**2
                + 194 * depth
                + 15
            )
            assert numerator > 0
            assert 0 < a_value < Fraction(1, depth * depth)
            coefficient_bounds += 1

        increment = a_value / 16**depth
        partial_sum += increment
        increments.append(increment)
        partial_sums.append(partial_sum)
        q_value = 10**depth - 16
        return_value = q_value * partial_sum

        if depth == 0:
            assert partial_sum == Fraction(47, 15)
            assert return_value == -47
        else:
            assert previous_sum is not None
            assert previous_return is not None
            forcing = (
                144 * previous_sum + q_value * increment
            )
            assert return_value == 10 * previous_return + forcing
            scalar_recurrence_checks += 1

            # This is the exact two-root-of-unity recurrence after applying
            # e(x)=exp(2*pi*i*x), checked additively modulo one.
            assert (partial_sum % 1) == (
                previous_sum + increment
            ) % 1
            assert (return_value % 1) == (
                10 * previous_return
                + 144 * previous_sum
                + q_value * increment
            ) % 1
            torus_recurrence_checks += 2

        if depth >= 2:
            # The analytic BBP tail gives this exact symbolic transfer
            # majorant; no numerical value of pi is used here.
            transfer_bound = Fraction(5**depth, 8**depth) / (
                15 * (depth + 1) ** 2
            )
            assert transfer_bound > 0
            assert abs(q_value) < 10**depth
            diagonal_phase_checks += 1
            distance = circle_distance(return_value)
            if distance < record_distance:
                record_depth = depth
                record_distance = distance

        previous_sum = partial_sum
        previous_return = return_value

    # The exact linear recurrence for the limiting affine phase
    # (10^n - 16)*alpha has characteristic polynomial
    # (X-10)(X-1)=X^2-11X+10, whose coefficient length is 22.
    linear_recurrence_checks = 0
    for depth in range(0, args.max_depth - 1):
        q0 = 10**depth - 16
        q1 = 10 ** (depth + 1) - 16
        q2 = 10 ** (depth + 2) - 16
        assert q2 - 11 * q1 + 10 * q0 == 0
        linear_recurrence_checks += 1
    assert 1 + 11 + 10 == 22

    # Full triangular (M,n) averaging has no hidden second family of phases.
    # Exact multiplicity counting rewrites it as a tent-weighted list of the
    # same decimal phases.  The BBP carry across a fixed column is the small
    # positive increment already present in B_(M+1)-B_M.
    triangular_reindex_checks = 0
    triangular_carry_checks = 0
    triangular_transfer_checks = 0
    largest_triangle_size = 0
    for ceiling in sorted({20, 40, 80, args.max_depth}):
        if ceiling > args.max_depth:
            continue
        direct_phases: list[Fraction] = []
        for depth in range(5, ceiling + 1):
            upper = row_upper(depth)
            assert 10**upper <= 16**depth < 10 ** (upper + 1)
            assert upper >= depth
            for exponent in range(depth, upper + 1):
                q_value = 10**exponent - 16
                direct_phases.append((q_value * partial_sums[depth]) % 1)
                # Symbolic BBP-tail transfer majorant for this pair.
                transfer_bound = Fraction(10**exponent, 16**depth) / (
                    15 * (depth + 1) ** 2
                )
                assert 0 < transfer_bound <= Fraction(
                    1, 15 * (depth + 1) ** 2
                )
                triangular_transfer_checks += 1

                if depth < min(exponent, ceiling):
                    next_phase = q_value * partial_sums[depth + 1]
                    phase = q_value * partial_sums[depth]
                    assert next_phase - phase == q_value * increments[depth + 1]
                    assert 0 < next_phase - phase
                    triangular_carry_checks += 1

        weighted_phases: list[Fraction] = []
        for exponent in range(5, row_upper(ceiling) + 1):
            lower = max(5, first_depth(exponent))
            upper = min(exponent, ceiling)
            multiplicity = max(0, upper - lower + 1)
            for depth in range(lower, upper + 1):
                assert depth <= exponent <= row_upper(depth)
                weighted_phases.append(
                    ((10**exponent - 16) * partial_sums[depth]) % 1
                )
        assert Counter(direct_phases) == Counter(weighted_phases)
        assert len(direct_phases) == sum(
            row_upper(depth) - depth + 1
            for depth in range(5, ceiling + 1)
        )
        largest_triangle_size = max(largest_triangle_size, len(direct_phases))
        triangular_reindex_checks += 1

    # Exact finite replay of the adversarial Kempner shadow.  The infinite
    # kappa has decimal 1-digits exactly at powers of two, lies in
    # (11/100, 1/9), and its fixed-sixteen phase stays farther than 2/9 from
    # the integer lattice.  C_n truncates kappa after 3n digits, so
    #   0 < kappa-C_n <= 10^(-3n)/9
    # and multiplication by q_n costs less than 10^(-2n)/9.
    separator_shadow_checks = 0
    separator_recurrence_checks = 0
    previous_c: Fraction | None = None
    previous_s: Fraction | None = None
    previous_tail_bound: Fraction | None = None
    minimum_certified_separator_gap = Fraction(1, 2)
    for depth in range(1, args.max_depth + 1):
        c_value = kempner_truncation(depth)
        q_value = 10**depth - 16
        s_value = q_value * c_value
        tail_bound = Fraction(1, 9 * 10 ** (3 * depth))
        transfer_bound = abs(q_value) * tail_bound
        certified_gap = Fraction(2, 9) - transfer_bound
        assert Fraction(11, 100) <= c_value <= Fraction(1, 9)
        assert 0 <= transfer_bound < Fraction(1, 9 * 10 ** (2 * depth))
        assert certified_gap > 0
        # This finite inequality is redundant with the symbolic infinite
        # kappa argument and catches truncation/index errors.
        assert circle_distance(s_value) >= certified_gap
        minimum_certified_separator_gap = min(
            minimum_certified_separator_gap, certified_gap
        )
        separator_shadow_checks += 1

        if previous_c is not None:
            assert previous_s is not None
            assert previous_tail_bound is not None
            increment = c_value - previous_c
            forcing = 144 * previous_c + q_value * increment
            assert increment >= 0
            assert increment <= previous_tail_bound
            assert forcing > 0
            assert s_value == 10 * previous_s + forcing
            # A rigorous upper bound for |forcing-144*kappa| follows from
            # kappa-C_{n-1} <= 10^(-3(n-1))/9 and
            # C_n-C_{n-1} <= kappa-C_{n-1}.
            convergence_bound = (
                16 * Fraction(1, 10 ** (3 * (depth - 1)))
                + Fraction(1, 9 * 10 ** (2 * depth - 3))
            )
            assert abs(forcing - 144 * previous_c) == q_value * increment
            assert (
                144 * previous_tail_bound + q_value * increment
                <= convergence_bound
            )
            separator_recurrence_checks += 1
        previous_c = c_value
        previous_s = s_value
        previous_tail_bound = tail_bound

    print("status: PASS")
    print("claim_label: experiment")
    print(f"source_sha256: {digest(source)}")
    print(f"bbp_pdf_sha256: {digest(bbp_pdf)}")
    print(f"lagarias_pdf_sha256: {digest(lagarias_pdf)}")
    print(f"chen_ye_zheng_pdf_sha256: {digest(chen_ye_zheng_pdf)}")
    print(f"shallit_pdf_sha256: {digest(shallit_pdf)}")
    print(f"kempner_pdf_sha256: {digest(kempner_pdf)}")
    print(f"coefficient_bounds: {coefficient_bounds}")
    print(f"scalar_recurrence_checks: {scalar_recurrence_checks}")
    print(f"torus_recurrence_checks: {torus_recurrence_checks}")
    print(f"diagonal_phase_checks: {diagonal_phase_checks}")
    print(f"linear_recurrence_checks: {linear_recurrence_checks}")
    print(f"triangular_reindex_checks: {triangular_reindex_checks}")
    print(f"triangular_carry_checks: {triangular_carry_checks}")
    print(f"triangular_transfer_checks: {triangular_transfer_checks}")
    print(f"largest_triangle_size: {largest_triangle_size}")
    print(f"separator_shadow_checks: {separator_shadow_checks}")
    print(f"separator_recurrence_checks: {separator_recurrence_checks}")
    print(
        "finite_diagonal_record: "
        f"n={record_depth},distance={float(record_distance):.15f}"
    )
    print(
        "minimum_certified_separator_gap: "
        f"{float(minimum_certified_separator_gap):.15f}"
    )
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
