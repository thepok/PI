#!/usr/bin/env python3
"""Exact finite replay for the BBP high-prime-coordinate rigidity lemma.

Every computed row has label ``experiment``.  The script reconstructs the
four-pole BBP partial sums independently and checks the exact cofactor lattice
spacing.  It does not prove the prime-number-theorem asymptotic, the fixed
sixteen return, or canonical V1.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from math import gcd, log
from pathlib import Path


PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_short_orbit_return_attack.md":
        "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean":
        "fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9",
}


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def verify_pins() -> None:
    root = repository_root()
    for relative_path, expected in PINS.items():
        actual = hashlib.sha256((root / relative_path).read_bytes()).hexdigest()
        assert actual == expected, (relative_path, expected, actual)


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def factor_over_primes(integer: int, primes: list[int]) -> dict[int, int]:
    remaining = integer
    factors: dict[int, int] = {}
    for prime in primes:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            factors[prime] = exponent
        if remaining == 1:
            break
    assert remaining == 1, remaining
    return factors


def valuation_two(integer: int) -> int:
    assert integer > 0
    return (integer & -integer).bit_length() - 1


def valuation(integer: int, prime: int) -> int:
    assert integer > 0
    exponent = 0
    while integer % prime == 0:
        integer //= prime
        exponent += 1
    return exponent


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def additive_coordinate(numerator: int, odd_denominator: int, prime: int) -> int:
    assert odd_denominator % prime == 0
    complementary = odd_denominator // prime
    assert complementary % prime != 0
    return numerator * pow(complementary, -1, prime) % prime


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=180)
    args = parser.parse_args()
    assert args.max_depth >= 12

    verify_pins()
    primes = primes_through(8 * args.max_depth + 5)
    partial_sum = Fraction()

    split_checks = 0
    exponent_bound_checks = 0
    high_prime_coordinate_checks = 0
    lattice_spacing_checks = 0
    uniqueness_inequality_rows: list[tuple[int, bool]] = []
    last_log_cofactor_ratio = 0.0
    minimum_log_spacing_over_two_tail = float("inf")

    for depth in range(args.max_depth + 1):
        partial_sum += coefficient(depth) / 16**depth
        # From depth 12 onward, p > depth implies p^2 > 8*depth+5, so every
        # such possible denominator prime has exponent one in the source LCM.
        if depth < 12:
            continue

        denominator = partial_sum.denominator
        two_exponent = valuation_two(denominator)
        assert two_exponent == 4 * depth - valuation(depth + 1, 2)
        odd_denominator = denominator >> two_exponent
        dyadic_denominator = 1 << (two_exponent - 4)
        reduced_numerator = partial_sum.numerator
        assert gcd(reduced_numerator, 2 * odd_denominator) == 1
        assert partial_sum == Fraction(
            reduced_numerator,
            16 * dyadic_denominator * odd_denominator,
        )

        dyadic_coordinate = (
            reduced_numerator
            * pow(odd_denominator, -1, dyadic_denominator)
            % dyadic_denominator
        )
        odd_quotient_numerator, remainder = divmod(
            reduced_numerator - odd_denominator * dyadic_coordinate,
            dyadic_denominator,
        )
        assert remainder == 0
        assert gcd(odd_quotient_numerator, odd_denominator) == 1
        assert 16 * partial_sum == (
            Fraction(dyadic_coordinate, dyadic_denominator)
            + Fraction(odd_quotient_numerator, odd_denominator)
        )
        split_checks += 1

        factors = factor_over_primes(odd_denominator, primes)
        high_prime_product = 1
        for prime, exponent in factors.items():
            if prime > depth:
                assert exponent == 1
                high_prime_product *= prime
            elif prime > 5:
                assert exponent <= floor_log(prime, 8 * depth + 5)
                exponent_bound_checks += 1
            else:
                assert exponent <= 4 * floor_log(prime, 8 * depth + 5)
                exponent_bound_checks += 1

        cofactor = odd_denominator // high_prime_product
        assert gcd(high_prime_product, cofactor) == 1
        assert all(prime <= depth for prime in factor_over_primes(cofactor, primes))

        alternative_quotient = odd_quotient_numerator + high_prime_product
        for prime in factors:
            if prime <= depth:
                continue
            assert additive_coordinate(
                odd_quotient_numerator, odd_denominator, prime
            ) == additive_coordinate(
                alternative_quotient, odd_denominator, prime
            )
            high_prime_coordinate_checks += 1

        alternative_shadow = Fraction(
            odd_denominator * dyadic_coordinate
            + dyadic_denominator * alternative_quotient,
            16 * dyadic_denominator * odd_denominator,
        )
        spacing = Fraction(1, 16 * cofactor)
        assert alternative_shadow - partial_sum == spacing
        lattice_spacing_checks += 1

        bbp_tail_bound = Fraction(1, 15 * (depth + 1) ** 2 * 16**depth)
        unique_at_bbp_scale = 2 * bbp_tail_bound < spacing
        uniqueness_inequality_rows.append((depth, unique_at_bbp_scale))
        log_ratio = (
            depth * log(16)
            + log(15)
            + 2 * log(depth + 1)
            - log(32 * cofactor)
        )
        minimum_log_spacing_over_two_tail = min(
            minimum_log_spacing_over_two_tail, log_ratio
        )
        last_log_cofactor_ratio = log(cofactor) / depth

    permanent_onset = None
    for index, (depth, _) in enumerate(uniqueness_inequality_rows):
        if all(flag for _, flag in uniqueness_inequality_rows[index:]):
            permanent_onset = depth
            break
    assert permanent_onset is not None
    assert uniqueness_inequality_rows[-1][1]

    print(json.dumps({
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
        "claim_label": "experiment",
        "depths_checked": split_checks,
        "exact_small_prime_exponent_bound_checks": exponent_bound_checks,
        "high_prime_coordinate_preservation_checks": high_prime_coordinate_checks,
        "lattice_spacing_identity_checks": lattice_spacing_checks,
        "maximum_depth": args.max_depth,
        "minimum_log_spacing_over_two_tail": minimum_log_spacing_over_two_tail,
        "observed_permanent_uniqueness_onset": permanent_onset,
        "last_log_cofactor_over_depth": last_log_cofactor_ratio,
        "pinned_inputs": PINS,
        "status": "PASS",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
