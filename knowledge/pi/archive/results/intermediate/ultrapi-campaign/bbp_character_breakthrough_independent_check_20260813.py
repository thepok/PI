#!/usr/bin/env python3
"""Independent exact replay for the BBP character scalarization audit.

This checker does not import the primary checker.  It uses exact rational and
integer polynomial arithmetic to replay the algebra, endpoints, separator,
and indexing.  Every bounded loop is only an ``experiment``; the all-index
arguments and source applicability are recorded in the independent audit.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

EXPECTED_HASHES = {
    "problems/local/pi-digits.txt": (
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
    ),
    "work/ultrapi-resume/bbp_character_breakthrough_attack_20260813.md": (
        "5a0e3027eb2b6c38b48e2b3ae075b4175b586bbd54ec1de68e6621cb0e03c264"
    ),
    "work/ultrapi-resume/bbp_character_breakthrough_attack_20260813_check.py": (
        "34bdc64f14eff57a23346bfc9924ff8f137efd8bdc8b1d87a1bbda5d7b88851f"
    ),
    "work/ultrapi-resume/bbp_one_character_return_attack.md": (
        "b49bfb3793dd87abf7b5dedaa820c87dfcf23ab3856e9fa67ef2462fbefecfab"
    ),
    "work/ultrapi-resume/bbp_one_character_return_check.py": (
        "4d4cf5933f0d9751ea84fffaf2a7f1e25c84769e50e3e77b1b4083982a660372"
    ),
    "work/ultrapi-resume/bbp_one_character_return_independent_audit.md": (
        "b37b90d63fad6fb41e51397bf36373739e221eb8a85e65cb58bdfbceaeff7c80"
    ),
    "work/ultrapi-resume/bbp_one_character_return_independent_check.py": (
        "75286116c6472445d40ba648696babea8ead2e90be8fe67b586c1e9ee107d577"
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
    "bailey-crandall-2001-bcrandom.pdf": (
        "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8"
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


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def poly_add(left: list[int], right: list[int]) -> list[int]:
    size = max(len(left), len(right))
    result = [0] * size
    for index in range(size):
        result[index] = (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
        )
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_scale(poly: list[int], scalar: int) -> list[int]:
    return [scalar * coefficient for coefficient in poly]


def poly_multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, left_coefficient in enumerate(left):
        for j, right_coefficient in enumerate(right):
            result[i + j] += left_coefficient * right_coefficient
    return result


def product(polynomials: list[list[int]]) -> list[int]:
    result = [1]
    for polynomial in polynomials:
        result = poly_multiply(result, polynomial)
    return result


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


def increment(index: int) -> Fraction:
    return coefficient(index) / 16**index


def q(index: int) -> int:
    return 10**index - 16


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def separator_r(index: int) -> Fraction:
    return Fraction(5, 8) ** index


def separator_error(index: int) -> Fraction:
    return Fraction(1, 3) * separator_r(index)


def separator_return(index: int) -> Fraction:
    return Fraction(q(index), 9) - separator_error(index)


def check_text_hygiene() -> int:
    relative_paths = [
        relative
        for relative in EXPECTED_HASHES
        if not relative.endswith(".pdf")
    ]
    relative_paths.append(
        "work/ultrapi-resume/bbp_character_breakthrough_independent_check_20260813.py"
    )
    audit_relative = (
        "work/ultrapi-resume/"
        "bbp_character_breakthrough_independent_audit_20260813.md"
    )
    if (ROOT / audit_relative).exists():
        relative_paths.append(audit_relative)

    for relative in relative_paths:
        data = (ROOT / relative).read_bytes()
        forbidden = [
            (offset, byte)
            for offset, byte in enumerate(data)
            if byte < 32 and byte not in (9, 10, 13)
        ]
        assert not forbidden, (relative, forbidden[:8])

    primary = (
        ROOT
        / "work/ultrapi-resume/bbp_character_breakthrough_attack_20260813.md"
    ).read_text(encoding="utf-8")
    assert "Canonical V1 remains a `conjecture`." in primary
    assert "No proof of (1) or V1 was obtained." in primary
    assert "Nothing here is\n`machine-checked`" in primary
    assert "asserts_v1: false" in primary
    assert "\\frac38,10" not in primary
    return len(relative_paths)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=180)
    args = parser.parse_args()
    if args.max_depth < 20:
        raise SystemExit("--max-depth must be at least 20")

    for relative, expected in EXPECTED_HASHES.items():
        observed = digest(ROOT / relative)
        assert observed == expected, (relative, observed, expected)

    c0_scanned = check_text_hygiene()

    # Symbolic coefficient identities.  Coefficients are stored in ascending
    # powers of k, so these are polynomial identities rather than samples.
    numerator_at_k = [47, 151, 120]
    numerator_at_k_plus_one = [318, 391, 120]
    denominator_at_k = product([[1, 2], [3, 4], [1, 8], [5, 8]])
    denominator_at_k_plus_one = product(
        [[3, 2], [7, 4], [9, 8], [13, 8]]
    )
    difference_numerator = poly_add(
        poly_multiply(numerator_at_k, denominator_at_k_plus_one),
        poly_scale(
            poly_multiply(numerator_at_k_plus_one, denominator_at_k), -1
        ),
    )
    expected_difference = poly_scale(
        [36903, 206712, 443480, 453632, 220672, 40960], 3
    )
    assert difference_numerator == expected_difference

    k_squared_numerator = [0, 0, 47, 151, 120]
    coefficient_majorant_difference = poly_add(
        denominator_at_k, poly_scale(k_squared_numerator, -1)
    )
    assert coefficient_majorant_difference == [15, 194, 665, 873, 392]
    symbolic_polynomial_checks = 2

    coefficient_checks = 0
    for index in range(args.max_depth + 4):
        value = coefficient(index)
        assert value == four_pole_coefficient(index) > 0
        assert value > coefficient(index + 1)
        if index >= 1:
            assert value < Fraction(1, index * index)
        assert increment(index + 1) < increment(index) / 16
        coefficient_checks += 4 if index >= 1 else 3

    partial_sums: list[Fraction] = []
    running = Fraction()
    for index in range(args.max_depth + 4):
        running += increment(index)
        partial_sums.append(running)

    returns = [q(index) * partial_sums[index] for index in range(args.max_depth + 4)]
    assert partial_sums[0] == Fraction(47, 15)
    assert returns[0] == -47

    scalar_checks = 0
    h_values: list[Fraction] = []
    for index in range(args.max_depth + 2):
        c_value = returns[index + 1] - 10 * returns[index]
        h_value = (
            returns[index + 2]
            - 11 * returns[index + 1]
            + 10 * returns[index]
        )
        direct_c = 144 * partial_sums[index] + q(index + 1) * increment(index + 1)
        direct_h = (
            q(index + 2) * increment(index + 2)
            + (160 - 10 ** (index + 1)) * increment(index + 1)
        )
        assert c_value == direct_c
        assert h_value == direct_h
        h_values.append(h_value)

        if index == 0:
            assert h_value == Fraction(20048317, 16336320) > 0
        elif index == 1:
            assert h_value == Fraction(258249, 17353600) > 0
        else:
            upper = (
                Fraction(159) - Fraction(3, 8) * 10 ** (index + 1)
            ) * increment(index + 1)
            assert h_value < upper < 0
            lower_coefficient = Fraction(10 ** (index + 1)) - Fraction(848, 5)
            assert lower_coefficient > 0
            assert (
                10 ** (index + 1) * increment(index + 1)
                < Fraction(5, 8) ** (index + 1) / (index + 1) ** 2
            )
        scalar_checks += 4

    # The all-index sign threshold in the report reduces to this endpoint;
    # powers of ten are increasing thereafter.
    assert 3 * 10**3 > 8 * 159

    for start in range(2, min(args.max_depth, 20)):
        finite_variation = sum(
            abs(value) for value in h_values[start : args.max_depth + 1]
        )
        claimed_infinite_upper = (
            Fraction(5, 8) ** (start + 1) / (start + 1) ** 2
        )
        assert finite_variation < claimed_infinite_upper

    # Affine expressions a*pi+b are represented as pairs (a,b).  This checks
    # the delta identities without using a numerical approximation to pi.
    affine_checks = 0
    deltas: list[tuple[Fraction, Fraction]] = []
    errors: list[tuple[Fraction, Fraction]] = []
    for index in range(args.max_depth + 3):
        errors.append((Fraction(q(index)), -returns[index]))
    assert errors[0] == (Fraction(-15), Fraction(47))

    for index in range(args.max_depth + 2):
        delta = (
            Fraction(-9 * 10**index),
            returns[index + 1] - returns[index],
        )
        error_difference = (
            errors[index][0] - errors[index + 1][0],
            errors[index][1] - errors[index + 1][1],
        )
        assert delta == error_difference
        deltas.append(delta)
        affine_checks += 1

    for index in range(args.max_depth + 1):
        delta_recurrence = (
            deltas[index + 1][0] - 10 * deltas[index][0],
            deltas[index + 1][1] - 10 * deltas[index][1],
        )
        assert delta_recurrence == (Fraction(), h_values[index])
        affine_checks += 1

    accumulated = (Fraction(), Fraction())
    for index in range(args.max_depth + 1):
        if index > 0:
            previous = deltas[index - 1]
            accumulated = (
                accumulated[0] + previous[0],
                accumulated[1] + previous[1],
            )
        expected = (
            errors[0][0] - errors[index][0],
            errors[0][1] - errors[index][1],
        )
        assert accumulated == expected
        phase_product = sum(
            returns[j + 1] - returns[j] for j in range(index)
        )
        assert phase_product == returns[index] - returns[0]
        assert phase_product % 1 == returns[index] % 1
        affine_checks += 3

    separator_checks = 0
    separator_zero = separator_return(0)
    assert separator_zero == -2
    previous_shadow: Fraction | None = None
    for index in range(args.max_depth + 1):
        r0 = separator_return(index)
        r1 = separator_return(index + 1)
        r2 = separator_return(index + 2)
        c_value = r1 - 10 * r0
        h_value = r2 - 11 * r1 + 10 * r0
        local_phase = (r1 - r0) % 1
        product_phase = (r0 - separator_zero) % 1

        assert c_value == 16 + Fraction(25, 8) * separator_r(index)
        assert h_value == -Fraction(75, 64) * separator_r(index)
        assert local_phase == Fraction(1, 8) * separator_r(index)
        assert product_phase == r0 % 1
        separator_checks += 4

        if index == 0:
            assert product_phase == 0
            separator_checks += 1
        else:
            assert product_phase == Fraction(1, 3) - separator_error(index)
            assert circle_distance(product_phase) >= Fraction(1, 8)
            separator_checks += 2

        if index >= 2:
            shadow = r0 / q(index)
            assert shadow < Fraction(1, 9)
            if previous_shadow is not None:
                assert shadow > previous_shadow
            previous_shadow = shadow
            assert Fraction(5, 8) * q(index) < q(index + 1)
            separator_checks += 3

    print("status: PASS")
    print("claim_label: experiment")
    print(f"pinned_artifacts: {len(EXPECTED_HASHES)}")
    print(f"c0_scanned_text_artifacts: {c0_scanned}")
    print(f"symbolic_polynomial_checks: {symbolic_polynomial_checks}")
    print(f"coefficient_checks: {coefficient_checks}")
    print(f"scalar_checks: {scalar_checks}")
    print(f"affine_pi_identity_checks: {affine_checks}")
    print(f"separator_checks: {separator_checks}")
    print("corrected_separator_initial_phase: R_star_0=-2")
    print("corrected_separator_gap_lower_bound: 1/8")
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all independent exact finite checks passed")


if __name__ == "__main__":
    main()
