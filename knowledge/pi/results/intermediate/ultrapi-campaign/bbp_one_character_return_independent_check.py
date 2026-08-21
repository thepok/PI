#!/usr/bin/env python3
"""Independent exact checks for the BBP one-character return audit.

Every finite output is an ``experiment``.  This file deliberately does not
import the primary checker.  It checks hashes and exact rational, indexing,
recurrence, finite combinatorial, and separator identities.  It does not
prove an infinite return, V1, a limit theorem, an asymptotic estimate, a
Mahler-measure bound, or any cited theorem.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path


EXPECTED_HASHES = {
    "problems/local/pi-digits.txt": (
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
    ),
    "work/ultrapi-resume/bbp_one_character_return_attack.md": (
        "b49bfb3793dd87abf7b5dedaa820c87dfcf23ab3856e9fa67ef2462fbefecfab"
    ),
    "work/ultrapi-resume/bbp_one_character_return_check.py": (
        "4d4cf5933f0d9751ea84fffaf2a7f1e25c84769e50e3e77b1b4083982a660372"
    ),
    "TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean": (
        "fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9"
    ),
    "work/ultrapi-resume/t69_fixed_sixteen_return_report.md": (
        "7094e4b4da2747b6e6f7ec4dc7c2390d4104f852f476098d8c6f9a3983fa8bf6"
    ),
    "work/ultrapi-resume/t69_fixed_sixteen_return_independent_audit.md": (
        "99dfa03eff652fba1dcfa3f21a2eae24d484bc611148af7b975d035a32ea0255"
    ),
    "work/theory/pi-positive-decimal-factor-entropy/library/t77/"
    "furstenberg-1967.pdf": (
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358"
    ),
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf": (
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4"
    ),
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf": (
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9"
    ),
    "work/ultrapi-resume/library/chen-ye-zheng-2604.14036v1.pdf": (
        "a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d"
    ),
    "work/ultrapi-resume/library/shallit-1979-simple-continued-fractions.pdf": (
        "592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981"
    ),
    "work/theory/pi-lacunary-near-return-sparsity/library/t89/"
    "kempner-1916.pdf": (
        "99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014"
    ),
}


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


def four_pole_coefficient(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def row_upper(depth: int) -> int:
    bound = 16**depth
    exponent = 0
    power = 1
    while 10 * power <= bound:
        power *= 10
        exponent += 1
    return exponent


def first_depth(exponent: int) -> int:
    target = 10**exponent
    depth = 0
    power = 1
    while power < target:
        power *= 16
        depth += 1
    return depth


def kempner_truncation(depth: int) -> Fraction:
    value = Fraction()
    position = 1
    while position <= 3 * depth:
        value += Fraction(1, 10**position)
        position *= 2
    return value


def polynomial_product(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    result = [Fraction() for _ in range(len(left) + len(right) - 1)]
    for i, left_coefficient in enumerate(left):
        for j, right_coefficient in enumerate(right):
            result[i + j] += left_coefficient * right_coefficient
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=120)
    args = parser.parse_args()
    if args.max_depth < 40:
        raise SystemExit("--max-depth must be at least 40")

    for relative, expected in EXPECTED_HASHES.items():
        assert digest(root() / relative) == expected, relative

    partial_sums: list[Fraction] = []
    increments: list[Fraction] = []
    partial_sum = Fraction()
    previous_return: Fraction | None = None
    coefficient_identity_checks = 0
    tail_majorant_checks = 0
    scalar_recurrence_checks = 0
    torus_recurrence_checks = 0
    frequency_shift_checks = 0

    for depth in range(args.max_depth + 1):
        a_value = coefficient(depth)
        assert a_value == four_pole_coefficient(depth)
        assert a_value > 0
        coefficient_identity_checks += 1
        if depth >= 1:
            denominator = (
                (2 * depth + 1)
                * (4 * depth + 3)
                * (8 * depth + 1)
                * (8 * depth + 5)
            )
            difference = denominator - depth * depth * (
                120 * depth * depth + 151 * depth + 47
            )
            expected_difference = (
                392 * depth**4
                + 873 * depth**3
                + 665 * depth**2
                + 194 * depth
                + 15
            )
            assert difference == expected_difference > 0
            assert a_value < Fraction(1, depth * depth)
            tail_majorant_checks += 1

        increment = a_value / 16**depth
        partial_sum += increment
        partial_sums.append(partial_sum)
        increments.append(increment)
        q_value = 10**depth - 16
        return_value = q_value * partial_sum

        if depth == 0:
            assert partial_sum == Fraction(47, 15)
            assert q_value == -15
            assert return_value == -47
        else:
            assert previous_return is not None
            forcing = 144 * partial_sums[depth - 1] + q_value * increment
            assert return_value == 10 * previous_return + forcing
            assert (return_value % 1) == (
                10 * previous_return
                + 144 * partial_sums[depth - 1]
                + q_value * increment
            ) % 1
            assert (partial_sum % 1) == (
                partial_sums[depth - 1] + increment
            ) % 1
            scalar_recurrence_checks += 1
            torus_recurrence_checks += 2

        if depth >= 2:
            transfer_bound = Fraction(5**depth, 8**depth) / (
                15 * (depth + 1) ** 2
            )
            assert 0 < transfer_bound
            assert 0 < q_value < 10**depth

        for shift in range(5):
            shifted_q = 10 ** (depth + shift) - 16
            assert shifted_q == 10**shift * q_value + 16 * (10**shift - 1)
            frequency_shift_checks += 1

        previous_return = return_value

    # The affine phase has P(T)=(T-10)(T-1), length 22.  Finite
    # collision-free multiset enumeration is only a diagnostic for the
    # general base-ten uniqueness argument in the independent audit.
    assert polynomial_product(
        [Fraction(-10), Fraction(1)], [Fraction(-1), Fraction(1)]
    ) == [Fraction(10), Fraction(-11), Fraction(1)]
    assert 10 + 11 + 1 == 22
    assert 10 * 1 + 1 * 100 == 11 * 10
    linear_recurrence_checks = 0
    for depth in range(args.max_depth - 1):
        q0 = 10**depth - 16
        q1 = 10 ** (depth + 1) - 16
        q2 = 10 ** (depth + 2) - 16
        assert q2 - 11 * q1 + 10 * q0 == 0
        linear_recurrence_checks += 1

    multiset_uniqueness_checks = 0
    for cardinality in range(1, 11):
        representations: dict[int, tuple[int, ...]] = {}
        for exponents in combinations_with_replacement(range(7), cardinality):
            value = sum(10**exponent for exponent in exponents)
            assert value not in representations, (
                cardinality,
                representations.get(value),
                exponents,
            )
            representations[value] = exponents
            multiset_uniqueness_checks += 1

    # Exact telescoping witnesses for ell(T-10) <= 10.
    reduced_length_witness_checks = 0
    for degree in range(21):
        witness = [Fraction(1, 10**index) for index in range(degree + 1)]
        product = polynomial_product([Fraction(-10), Fraction(1)], witness)
        expected = [Fraction(-10)] + [Fraction()] * degree + [
            Fraction(1, 10**degree)
        ]
        assert product == expected
        assert sum(abs(value) for value in product) == (
            Fraction(10) + Fraction(1, 10**degree)
        )
        reduced_length_witness_checks += 1

    triangular_reindex_checks = 0
    triangular_pair_checks = 0
    triangular_carry_span_checks = 0
    largest_triangle_size = 0
    for ceiling in sorted({20, 40, 80, args.max_depth}):
        if ceiling > args.max_depth:
            continue
        direct_pairs = [
            (depth, exponent)
            for depth in range(5, ceiling + 1)
            for exponent in range(depth, row_upper(depth) + 1)
        ]
        weighted_pairs: list[tuple[int, int]] = []
        for exponent in range(5, row_upper(ceiling) + 1):
            lower = max(5, first_depth(exponent))
            upper = min(exponent, ceiling)
            expected_weight = max(0, upper - lower + 1)
            column = [(depth, exponent) for depth in range(lower, upper + 1)]
            assert len(column) == expected_weight
            weighted_pairs.extend(column)
        assert Counter(direct_pairs) == Counter(weighted_pairs)
        assert len(direct_pairs) == sum(
            row_upper(depth) - depth + 1
            for depth in range(5, ceiling + 1)
        )

        for depth, exponent in direct_pairs:
            q_value = 10**exponent - 16
            assert 0 < q_value < 10**exponent <= 16**depth
            symbolic_error = Fraction(q_value, 16**depth) / (
                15 * (depth + 1) ** 2
            )
            assert 0 < symbolic_error <= Fraction(
                1, 15 * (depth + 1) ** 2
            )
            triangular_pair_checks += 1

        columns: dict[int, list[int]] = {}
        for depth, exponent in direct_pairs:
            columns.setdefault(exponent, []).append(depth)
        for exponent, depths in columns.items():
            if len(depths) < 2:
                continue
            first = min(depths)
            last = max(depths)
            q_value = 10**exponent - 16
            span = q_value * (partial_sums[last] - partial_sums[first])
            assert 0 < span < Fraction(1, 15 * (first + 1) ** 2)
            triangular_carry_span_checks += 1

        largest_triangle_size = max(largest_triangle_size, len(direct_pairs))
        triangular_reindex_checks += 1

    # The normalized Fejer expansion has coefficient (H-|h|)/H.  This
    # verifies the finite convolution count; the analytic kernel bound and
    # its limiting pigeonhole argument are proved in prose, not by replay.
    fejer_coefficient_checks = 0
    for order in range(2, 33):
        differences = Counter(
            left - right for left in range(order) for right in range(order)
        )
        for frequency in range(-(order - 1), order):
            assert differences[frequency] == order - abs(frequency)
            fejer_coefficient_checks += 1
        assert 2 * sum(Fraction(order - h, order) for h in range(1, order)) == (
            order - 1
        )

    # Exact endpoint arithmetic behind the Kempner separator.
    assert Fraction(19, 25) - Fraction(1, 9) > Fraction(2, 9)
    assert 1 - Fraction(7, 9) == Fraction(2, 9)
    separator_shadow_checks = 0
    separator_recurrence_checks = 0
    previous_c: Fraction | None = None
    previous_s: Fraction | None = None
    for depth in range(1, args.max_depth + 1):
        c_value = kempner_truncation(depth)
        q_value = 10**depth - 16
        s_value = q_value * c_value
        tail_bound = Fraction(1, 9 * 10 ** (3 * depth))
        transfer_bound = abs(q_value) * tail_bound
        assert Fraction(11, 100) <= c_value < Fraction(1, 9)
        assert 0 <= transfer_bound < Fraction(1, 9 * 10 ** (2 * depth))
        assert circle_distance(s_value) > Fraction(2, 9) - transfer_bound
        separator_shadow_checks += 1

        if previous_c is not None:
            assert previous_s is not None
            increment = c_value - previous_c
            forcing = 144 * previous_c + q_value * increment
            assert increment >= 0
            assert forcing > 0
            assert s_value == 10 * previous_s + forcing
            old_tail_bound = Fraction(1, 9 * 10 ** (3 * (depth - 1)))
            assert increment <= old_tail_bound
            convergence_bound = (
                16 * Fraction(1, 10 ** (3 * (depth - 1)))
                + Fraction(1, 9 * 10 ** (2 * depth - 3))
            )
            assert 144 * old_tail_bound + q_value * increment <= convergence_bound
            separator_recurrence_checks += 1
        previous_c = c_value
        previous_s = s_value

    print("status: PASS")
    print("claim_label: experiment")
    print(f"pinned_artifacts: {len(EXPECTED_HASHES)}")
    print(f"coefficient_identity_checks: {coefficient_identity_checks}")
    print(f"tail_majorant_checks: {tail_majorant_checks}")
    print(f"scalar_recurrence_checks: {scalar_recurrence_checks}")
    print(f"torus_recurrence_checks: {torus_recurrence_checks}")
    print(f"frequency_shift_checks: {frequency_shift_checks}")
    print(f"linear_recurrence_checks: {linear_recurrence_checks}")
    print(f"multiset_uniqueness_checks: {multiset_uniqueness_checks}")
    print(f"reduced_length_witness_checks: {reduced_length_witness_checks}")
    print(f"triangular_reindex_checks: {triangular_reindex_checks}")
    print(f"triangular_pair_checks: {triangular_pair_checks}")
    print(f"triangular_carry_span_checks: {triangular_carry_span_checks}")
    print(f"largest_triangle_size: {largest_triangle_size}")
    print(f"fejer_coefficient_checks: {fejer_coefficient_checks}")
    print(f"separator_shadow_checks: {separator_shadow_checks}")
    print(f"separator_recurrence_checks: {separator_recurrence_checks}")
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all independent exact checks passed")


if __name__ == "__main__":
    main()
