#!/usr/bin/env python3
"""Exact replay for ``machin_synchronized_return_attack.md``.

The script checks only finite rational and modular assertions.  In particular,
it does not numerically infer any statement about the decimal orbit of pi.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
Identity = dict[Fraction, int]


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100_000)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def chi4(odd: int) -> int:
    assert odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def split_argument(x: Fraction, u: Fraction) -> Fraction:
    assert 0 < u < x < 1
    v = (x - u) / (1 + x * u)
    assert 0 < v < x
    assert (u + v) / (1 - u * v) == x
    return v


def split_identity(identity: Identity, x: Fraction, u: Fraction) -> Identity:
    coefficient = identity[x]
    v = split_argument(x, u)
    answer = dict(identity)
    del answer[x]
    answer[u] = answer.get(u, 0) + coefficient
    answer[v] = answer.get(v, 0) + coefficient
    return answer


def identities() -> list[tuple[str, Identity]]:
    hutton: Identity = {Fraction(1, 3): 2, Fraction(1, 7): 1}
    first = split_identity(hutton, Fraction(1, 3), Fraction(1, 7))
    second = split_identity(first, Fraction(2, 11), Fraction(1, 7))
    second = split_identity(second, Fraction(1, 7), Fraction(1, 11))
    third = split_identity(second, Fraction(1, 11), Fraction(1, 23))
    third = split_identity(third, Fraction(2, 39), Fraction(1, 39))
    third = split_identity(third, Fraction(3, 79), Fraction(1, 53))
    return [
        ("Hutton", hutton),
        ("split-1", first),
        ("split-2", second),
        ("split-3", third),
    ]


def odd_taylor_prefix(x: Fraction, maximum_exponent: int) -> Fraction:
    assert maximum_exponent % 4 == 3
    return sum(
        (
            Fraction(chi4(exponent), exponent) * x**exponent
            for exponent in range(1, maximum_exponent + 1, 2)
        ),
        Fraction(),
    )


def lower_shadow(identity: Identity, first_omitted_exponent: int) -> Fraction:
    maximum_exponent = first_omitted_exponent - 2
    assert first_omitted_exponent % 4 == 1 and maximum_exponent >= 3
    return 4 * sum(
        (
            coefficient * odd_taylor_prefix(argument, maximum_exponent)
            for argument, coefficient in identity.items()
        ),
        Fraction(),
    )


def certified_error_lower(identity: Identity, first_omitted_exponent: int) -> Fraction:
    """Rational lower bound from the first two omitted alternating terms."""
    r = first_omitted_exponent
    return Fraction(8, r * (r + 2)) * sum(
        (coefficient * argument**r for argument, coefficient in identity.items()),
        Fraction(),
    )


def odd_lcm(maximum: int) -> int:
    answer = 1
    for odd in range(1, maximum + 1, 2):
        answer = math.lcm(answer, odd)
    return answer


def natural_denominator(identity: Identity, first_omitted_exponent: int) -> int:
    maximum_exponent = first_omitted_exponent - 2
    return odd_lcm(maximum_exponent) * math.prod(
        argument.denominator**maximum_exponent for argument in identity
    )


def valuation(value: int, prime: int) -> int:
    assert value > 0
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def floor_log10_fraction(value: Fraction) -> int:
    """Return floor(log_10(value)) exactly for positive ``value``."""
    assert value > 0
    numerator = value.numerator
    denominator = value.denominator
    guess = len(str(numerator)) - len(str(denominator))
    if guess >= 0:
        while numerator < denominator * 10**guess:
            guess -= 1
        while numerator >= denominator * 10 ** (guess + 1):
            guess += 1
    else:
        while numerator * 10 ** (-guess) < denominator:
            guess -= 1
        while numerator * 10 ** (-guess - 1) >= denominator:
            guess += 1
    return guess


def powers_mod(base: int, modulus: int) -> set[int]:
    assert math.gcd(base, modulus) == 1
    answer: set[int] = set()
    value = 1
    while value not in answer:
        answer.add(value)
        value = value * base % modulus
    assert value == 1
    return answer


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    named = identities()

    # Fixed-c primary valuations are eventually bounded exactly.
    primary_checks = 0
    for c in [1, 2, 3, 5, 7, 16, 40, 125, 700]:
        for prime in [2, 5]:
            for exponent in range(8, 15):
                assert valuation(abs(10**exponent - c), prime) == valuation(c, prime)
                primary_checks += 1

    # The generic natural-denominator lower bound is at least 32/35.
    natural_bound_checks = 0
    for number_of_arguments in range(2, 9):
        for maximum_exponent in range(3, 64, 4):
            r = maximum_exponent + 2
            lower = Fraction(
                8 * number_of_arguments * 2 ** (maximum_exponent * (number_of_arguments - 1) - 2),
                r * (r + 2),
            )
            assert lower >= Fraction(32, 35)
            natural_bound_checks += 1

    # For each fixed displayed identity, the 5-adic denominator is unbounded
    # on T=5^e+2 when its linear shadow is a 5-adic unit.
    five_adic_checks = 0
    for _, identity in named:
        linear = sum(
            (coefficient * argument for argument, coefficient in identity.items()),
            Fraction(),
        )
        assert valuation(linear.numerator, 5) == valuation(linear.denominator, 5) == 0
        for exponent in [1, 2, 3]:
            maximum = 5**exponent + 2
            lower = lower_shadow(identity, maximum + 2)
            assert valuation(lower.denominator, 5) == exponent
            five_adic_checks += 1

    # Private-prime height leakage.  In every named identity a private prime
    # forces a denominator much larger than the certified Taylor accuracy.
    private_data = [
        ("Hutton", 7, Fraction(1, 7)),
        ("split-1", 11, Fraction(2, 11)),
        ("split-2", 79, Fraction(3, 79)),
        ("split-3", 127, Fraction(6, 127)),
    ]
    private_checks = 0
    private_rows: list[tuple[str, int, int, int, int]] = []
    for (name, identity), (expected_name, prime, private_argument) in zip(
        named, private_data, strict=True
    ):
        assert name == expected_name
        assert prime % 4 == 3
        assert private_argument in identity
        assert all(
            argument == private_argument or argument.denominator % prime != 0
            for argument in identity
        )
        maximum = prime
        first_omitted = maximum + 2
        lower = lower_shadow(identity, first_omitted)
        error_lower = certified_error_lower(identity, first_omitted)
        assert valuation(lower.denominator, prime) == maximum + 1
        assert prime * max(identity) > 1
        assert lower.denominator * error_lower > 1
        margin_floor = floor_log10_fraction(lower.denominator * error_lower)
        private_rows.append(
            (name, prime, len(str(lower.denominator)), margin_floor, valuation(lower.denominator, prime))
        )
        private_checks += 6

    # Exact finite scale audit: reduced cancellation does not rescue any of
    # these four R=81 shadows.  The analytic meaning of the rational lower
    # bound is proved in the companion note, not inferred by this loop.
    scale_checks = 0
    scale_rows: list[tuple[str, int, int, int]] = []
    for name, identity in named:
        first_omitted = 81
        lower = lower_shadow(identity, first_omitted)
        error_lower = certified_error_lower(identity, first_omitted)
        natural = natural_denominator(identity, first_omitted)
        assert natural % lower.denominator == 0
        assert lower.denominator * error_lower > 1
        scale_rows.append(
            (
                name,
                len(str(lower.denominator)),
                len(str(natural // lower.denominator)),
                floor_log10_fraction(lower.denominator * error_lower),
            )
        )
        scale_checks += 2

    # For c=16, two private primes already fail the necessary discrete-log
    # condition.  The other two deliberately show that this modular filter is
    # not a universal obstruction.
    subgroup_checks = 0
    expected_membership = {7: True, 11: False, 79: False, 127: True}
    for prime, expected in expected_membership.items():
        assert (16 % prime in powers_mod(10, prime)) is expected
        subgroup_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"fixed_c_primary_valuation_exact_checks={primary_checks}")
    print(f"natural_denominator_lower_bound_exact_checks={natural_bound_checks}")
    print(f"fixed_identity_five_adic_exact_checks={five_adic_checks}")
    print(f"private_prime_height_exact_checks={private_checks}")
    for name, prime, denominator_digits, margin_floor, prime_exponent in private_rows:
        print(
            f"private name={name} p={prime} denominator_digits={denominator_digits} "
            f"floor_log10_q_error_lower={margin_floor} v_p_q={prime_exponent}"
        )
    print(f"reduced_denominator_scale_exact_checks={scale_checks}")
    for name, q_digits, cancellation_digits, margin_floor in scale_rows:
        print(
            f"scale name={name} R=81 q_digits={q_digits} "
            f"natural_over_reduced_digits={cancellation_digits} "
            f"floor_log10_q_error_lower={margin_floor}"
        )
    print(f"c16_private_prime_subgroup_exact_checks={subgroup_checks}")
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
