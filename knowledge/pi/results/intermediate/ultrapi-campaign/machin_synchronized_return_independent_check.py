#!/usr/bin/env python3
"""Independent exact replay for the synchronized-Machin audit.

This intentionally does not import the primary checker.  It checks finite
integer/rational consequences only and reports `experiment` status.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import gcd, lcm, prod
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


IDENTITIES: list[tuple[str, dict[Fraction, int]]] = [
    ("Hutton", {Fraction(1, 3): 2, Fraction(1, 7): 1}),
    ("split-1", {Fraction(1, 7): 3, Fraction(2, 11): 2}),
    (
        "split-2",
        {Fraction(1, 11): 5, Fraction(2, 39): 5, Fraction(3, 79): 2},
    ),
    (
        "split-3",
        {
            Fraction(1, 23): 5,
            Fraction(6, 127): 5,
            Fraction(1, 39): 5,
            Fraction(39, 1523): 5,
            Fraction(1, 53): 2,
            Fraction(8, 419): 2,
        },
    ),
]


PRIVATE = {
    "Hutton": (Fraction(1, 7), 7),
    "split-1": (Fraction(2, 11), 11),
    "split-2": (Fraction(3, 79), 79),
    "split-3": (Fraction(6, 127), 127),
}


def v_p(value: int, prime: int) -> int:
    assert value != 0
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def chi4(odd: int) -> int:
    assert odd % 2
    return 1 if odd % 4 == 1 else -1


def gaussian_mul(first: tuple[int, int], second: tuple[int, int]) -> tuple[int, int]:
    a, b = first
    c, d = second
    return a * c - b * d, a * d + b * c


def gaussian_pow(value: tuple[int, int], exponent: int) -> tuple[int, int]:
    answer = (1, 0)
    base = value
    while exponent:
        if exponent & 1:
            answer = gaussian_mul(answer, base)
        base = gaussian_mul(base, base)
        exponent //= 2
    return answer


def gaussian_certificate(identity: dict[Fraction, int]) -> tuple[int, int]:
    answer = (1, 0)
    for x, coefficient in identity.items():
        answer = gaussian_mul(
            answer, gaussian_pow((x.denominator, x.numerator), coefficient)
        )
    return answer


def lower_shadow(identity: dict[Fraction, int], first_omitted: int) -> Fraction:
    assert first_omitted >= 5 and first_omitted % 4 == 1
    return 4 * sum(
        (
            coefficient
            * sum(
                (
                    Fraction(chi4(r), r) * x**r
                    for r in range(1, first_omitted - 1, 2)
                ),
                Fraction(),
            )
            for x, coefficient in identity.items()
        ),
        Fraction(),
    )


def error_lower(identity: dict[Fraction, int], first_omitted: int) -> Fraction:
    return Fraction(8, first_omitted * (first_omitted + 2)) * sum(
        (coefficient * x**first_omitted for x, coefficient in identity.items()),
        Fraction(),
    )


def odd_lcm(maximum: int) -> int:
    answer = 1
    for odd in range(1, maximum + 1, 2):
        answer = lcm(answer, odd)
    return answer


def safe_denominator(identity: dict[Fraction, int], first_omitted: int) -> int:
    maximum = first_omitted - 2
    return odd_lcm(maximum) * prod(x.denominator**maximum for x in identity)


def floor_log10(value: Fraction) -> int:
    assert value > 0
    numerator, denominator = value.numerator, value.denominator
    answer = len(str(numerator)) - len(str(denominator))
    if answer >= 0:
        while numerator < denominator * 10**answer:
            answer -= 1
        while numerator >= denominator * 10 ** (answer + 1):
            answer += 1
    else:
        while numerator * 10 ** (-answer) < denominator:
            answer -= 1
        while numerator * 10 ** (-answer - 1) >= denominator:
            answer += 1
    return answer


def generated_subgroup(base: int, prime: int) -> set[int]:
    assert gcd(base, prime) == 1
    answer: set[int] = set()
    value = 1
    while value not in answer:
        answer.add(value)
        value = value * base % prime
    assert value == 1
    return answer


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source_hash = sha256((root / "problems/local/pi-digits.txt").read_bytes()).hexdigest()
    assert source_hash == SOURCE_SHA256

    gaussian_checks = 0
    five_unit_checks = 0
    for _name, identity in IDENTITIES:
        real, imaginary = gaussian_certificate(identity)
        assert real == imaginary > 0
        assert sum(identity.values()) >= 1
        assert sum((coefficient * x for x, coefficient in identity.items()), Fraction()) < 1
        gaussian_checks += 3

        linear = sum((coefficient * x for x, coefficient in identity.items()), Fraction())
        assert linear.numerator % 5 and linear.denominator % 5
        five_unit_checks += 1

    primary_checks = 0
    for c in (1, 2, 3, 5, 7, 16, 40, 125, 700, 10**4):
        for prime in (2, 5):
            threshold = v_p(c, prime)
            for decimal_exponent in range(threshold + 1, threshold + 9):
                assert v_p(10**decimal_exponent - c, prime) == threshold
                primary_checks += 1

    five_depth_checks = 0
    for _name, identity in IDENTITIES:
        for exponent in range(1, 5):
            maximum_included = 5**exponent + 2
            shadow = lower_shadow(identity, maximum_included + 2)
            assert v_p(shadow.denominator, 5) == exponent
            five_depth_checks += 1

    natural_inequality_checks = 0
    for number_of_arguments in range(2, 10):
        for maximum in range(3, 100, 4):
            # P >= 2^J and AM-GM give this exact universal lower surrogate.
            first_omitted = maximum + 2
            bound = Fraction(
                8
                * number_of_arguments
                * 2 ** (maximum * (number_of_arguments - 1) - 2),
                first_omitted * (first_omitted + 2),
            )
            assert bound >= Fraction(32, 35)
            natural_inequality_checks += 1

    private_checks = 0
    private_rows: list[tuple[str, int, int, int]] = []
    for name, identity in IDENTITIES:
        private_argument, prime = PRIVATE[name]
        assert prime % 4 == 3
        assert private_argument in identity
        assert private_argument.denominator % prime == 0
        assert identity[private_argument] * private_argument.numerator % prime != 0
        assert all(
            x == private_argument or x.denominator % prime != 0 for x in identity
        )
        maximum_x = max(identity)
        assert prime * maximum_x > 1

        first_omitted = prime + 2
        shadow = lower_shadow(identity, first_omitted)
        beta = v_p(private_argument.denominator, prime)
        assert v_p(shadow.denominator, prime) == beta * prime + 1
        product_lower = shadow.denominator * error_lower(identity, first_omitted)
        assert product_lower > 1
        private_rows.append(
            (name, prime, v_p(shadow.denominator, prime), floor_log10(product_lower))
        )
        private_checks += 8

    scale_checks = 0
    expected_rows = {
        "Hutton": (133, 5, 91),
        "split-1": (176, 6, 113),
        "split-2": (387, 4, 300),
        "split-3": (1022, 6, 911),
    }
    for name, identity in IDENTITIES:
        shadow = lower_shadow(identity, 81)
        natural = safe_denominator(identity, 81)
        assert natural % shadow.denominator == 0
        row = (
            len(str(shadow.denominator)),
            len(str(natural // shadow.denominator)),
            floor_log10(shadow.denominator * error_lower(identity, 81)),
        )
        assert row == expected_rows[name]
        scale_checks += 4

    subgroup_checks = 0
    expected_membership = {7: True, 11: False, 79: False, 127: True}
    for prime, expected in expected_membership.items():
        assert ((16 % prime) in generated_subgroup(10, prime)) is expected
        subgroup_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={source_hash}")
    print(f"independent_gaussian_identity_checks={gaussian_checks}")
    print(f"independent_five_unit_checks={five_unit_checks}")
    print(f"independent_fixed_primary_checks={primary_checks}")
    print(f"independent_five_depth_checks={five_depth_checks}")
    print(f"independent_natural_inequality_checks={natural_inequality_checks}")
    print(f"independent_private_prime_checks={private_checks}")
    for name, prime, exponent, margin in private_rows:
        print(
            f"private name={name} p={prime} v_p_den={exponent} "
            f"floor_log10_q_error_lower={margin}"
        )
    print(f"independent_scale_checks={scale_checks}")
    print(f"independent_subgroup_checks={subgroup_checks}")
    print("all independent exact assertions passed")


if __name__ == "__main__":
    main()
