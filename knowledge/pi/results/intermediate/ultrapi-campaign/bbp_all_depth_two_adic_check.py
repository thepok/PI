#!/usr/bin/env python3
"""Exact finite replay for the all-depth BBP two-adic report.

The output is an `experiment`.  It checks finite rational and polynomial
identities only; it does not certify the infinite p-adic argument or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from pathlib import Path


EXPECTED_SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def trim(poly: list[int]) -> list[int]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_add(left: list[int], right: list[int]) -> list[int]:
    size = max(len(left), len(right))
    answer = [0] * size
    for index in range(size):
        if index < len(left):
            answer[index] += left[index]
        if index < len(right):
            answer[index] += right[index]
    return trim(answer)


def poly_scale(value: int, poly: list[int]) -> list[int]:
    return trim([value * coefficient for coefficient in poly])


def poly_mul(left: list[int], right: list[int]) -> list[int]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] += a * b
    return trim(answer)


def v2_integer(value: int) -> int:
    assert value != 0
    value = abs(value)
    answer = 0
    while value % 2 == 0:
        value //= 2
        answer += 1
    return answer


def v2_rational(value: Fraction) -> int:
    assert value
    return v2_integer(value.numerator) - v2_integer(value.denominator)


def bbp_coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def split_bbp_coefficient(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def reflected_coefficient(index: int) -> Fraction:
    return (
        Fraction(1, 8 * index + 2)
        + Fraction(1, 8 * index + 3)
        + Fraction(2, 8 * index + 4)
        - Fraction(4, 8 * index + 7)
    )


def check_polynomial_identities() -> None:
    # Coefficients are in increasing degree order.
    x = [0, 1]
    x_minus_one = [-1, 1]
    two_x2_plus_one = [1, 0, 2]
    two_x2_plus_2x_plus_one = [1, 2, 2]
    two_x2_minus_one = [-1, 0, 2]
    two_x2_minus_2x_plus_one = [1, -2, 2]

    p = [0, 1, 1, 2, 0, 0, -4]
    p_factored = poly_scale(
        -1,
        poly_mul(
            poly_mul(x, x_minus_one),
            poly_mul(two_x2_plus_one, two_x2_plus_2x_plus_one),
        ),
    )
    assert p == p_factored

    denominator = [1] + [0] * 7 + [-16]
    denominator_factored = poly_scale(
        -1,
        poly_mul(
            poly_mul(two_x2_minus_one, two_x2_plus_one),
            poly_mul(
                two_x2_minus_2x_plus_one,
                two_x2_plus_2x_plus_one,
            ),
        ),
    )
    assert denominator == denominator_factored

    # Cross-multiplied derivative identity from equations (15)--(17).
    numerator_reduced = poly_mul(x, x_minus_one)
    cancelled_denominator = poly_mul(
        two_x2_minus_one, two_x2_minus_2x_plus_one
    )
    assert poly_mul(p, cancelled_denominator) == poly_mul(
        numerator_reduced, denominator
    )


def main() -> None:
    source_hash = sha256(source_path().read_bytes()).hexdigest()
    assert source_hash == EXPECTED_SOURCE_SHA256
    check_polynomial_identities()

    reflection_checks = 0
    for index in range(0, 1001):
        reflected = reflected_coefficient(index)
        assert reflected == bbp_coefficient(-1 - index)
        assert reflected.denominator % 2 == 1
        assert split_bbp_coefficient(index) == bbp_coefficient(index)
        reflection_checks += 1

    # Finite approaches to the two-adic null identity.  The report proves
    # convergence to zero; these exact checks only replay its visible effect.
    reverse_sum = Fraction()
    reverse_null_checks = 0
    for index in range(0, 401):
        reverse_sum += 16**index * reflected_coefficient(index)
        assert v2_rational(reverse_sum) >= 4 * (index + 1)
        reverse_null_checks += 1

    scaled_sum = Fraction()
    valuation_checks = 0
    fixed_sixteen_exclusions = 0
    for index in range(0, 401):
        scaled_sum = 16 * scaled_sum + bbp_coefficient(index)
        expected_scaled_v2 = v2_integer(index + 1)
        assert v2_rational(scaled_sum) == expected_scaled_v2

        shadow = scaled_sum / 16**index
        if index >= 1:
            expected_denominator_v2 = 4 * index - v2_integer(index + 1)
            assert v2_integer(shadow.denominator) == expected_denominator_v2
            valuation_checks += 1
            if index >= 2:
                assert expected_denominator_v2 > 4
                fixed_sixteen_exclusions += 1

    print("claim_status=experiment")
    print(f"source_sha256={source_hash}")
    print("polynomial_antiderivative_identities=3")
    print(f"reflected_coefficient_checks={reflection_checks}")
    print(f"finite_two_adic_null_checks={reverse_null_checks}")
    print(f"all_depth_denominator_valuation_checks={valuation_checks}")
    print(f"fixed_sixteen_exact_anchor_exclusions={fixed_sixteen_exclusions}")
    print(f"last_reverse_partial_v2={v2_rational(reverse_sum)}")
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
