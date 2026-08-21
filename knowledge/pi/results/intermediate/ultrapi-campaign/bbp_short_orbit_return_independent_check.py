#!/usr/bin/env python3
"""Independent exact replay for the BBP short-orbit audit.

All output has claim status ``experiment``.  This script deliberately does
not import the branch checker.  It checks finite rational shadows of the
recurrence, the 256-extra-bit two-adic coordinate, the two explicit odd-prime
bands used in the separator, and the separator's exact scaling.  It does not
prove a p-adic analytic identity, the PNT/AP asymptotic, Kanold's theorem, or
any return statement for pi.
"""

from __future__ import annotations

import hashlib
from fractions import Fraction
from math import factorial, gcd, log10
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def v_p(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("the finite replay never requests v_p(0)")
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def factor_over_primes(integer: int, primes: list[int]) -> dict[int, int]:
    remaining = integer
    answer: dict[int, int] = {}
    for prime in primes:
        if prime * prime > remaining:
            break
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            answer[prime] = exponent
    if remaining > 1:
        answer[remaining] = 1
    return answer


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def rational_mod_two_power(value: Fraction, bits: int) -> int:
    modulus = 1 << bits
    assert value.denominator & 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def reflected_f_mod(argument: int, bits: int) -> int:
    modulus = 1 << bits
    total = 0
    for offset in range((bits + 3) // 4):
        total += pow(16, offset, modulus) * rational_mod_two_power(
            coefficient(argument - 1 - offset), bits
        )
    return total % modulus


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def singular_occurrences(depth: int, prime: int) -> list[tuple[int, int]]:
    occurrences: list[tuple[int, int]] = []
    for index in range(depth + 1):
        factors = (2 * index + 1, 4 * index + 3, 8 * index + 1, 8 * index + 5)
        for slot, factor in enumerate(factors):
            if factor % prime == 0:
                occurrences.append((index, slot))
    return occurrences


def nearest_admissible_lift(
    target: Fraction, odd_modulus: int, old_quotient: int, bound: int
) -> tuple[int, int]:
    floor_target = target.numerator // target.denominator
    for distance in range(bound + 1):
        for candidate in (floor_target - distance, floor_target + 1 + distance):
            if gcd(old_quotient + 256 * candidate, odd_modulus) == 1:
                return candidate, distance + 1
    raise AssertionError("finite Kanold-bound shadow failed")


def main() -> None:
    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    assert digest == SOURCE_SHA256

    primes = primes_through(8 * 120 + 5)

    # F(X) = X + 2G(X) should be an isometry on each finite shadow.
    isometry_pair_checks = 0
    for bits in range(1, 9):
        modulus = 1 << bits
        values = [reflected_f_mod(argument, bits) for argument in range(modulus)]
        assert sorted(values) == list(range(modulus))
        for left in range(modulus):
            for right in range(left + 1, modulus):
                assert v_p(values[right] - values[left], 2) == v_p(
                    right - left, 2
                )
                isometry_pair_checks += 1

    partial_sum = Fraction()
    prior_partial_sum: Fraction | None = None
    valuation_checks = 0
    coordinate_checks = 0
    recurrence_checks = 0
    gcd_log_checks = 0
    quotient_split_checks = 0
    band_survival_checks = 0
    separator_checks = 0
    liouville_shadow_checks = 0
    largest_finite_lift_distance = 0

    for depth in range(121):
        prior_partial_sum = partial_sum
        partial_sum += coefficient(depth) / 16**depth
        if depth < 2:
            continue

        r = v_p(depth + 1, 2)
        k_exponent = 4 * depth - r
        assert v_p(partial_sum.denominator, 2) == k_exponent
        odd_denominator = partial_sum.denominator >> k_exponent
        numerator = partial_sum.numerator
        assert gcd(numerator, 2 * odd_denominator) == 1
        valuation_checks += 1

        dyadic_modulus = 1 << (k_exponent - 4)
        coordinate = numerator * pow(odd_denominator, -1, dyadic_modulus)
        coordinate %= dyadic_modulus
        assert coordinate & 1
        odd_quotient = (
            numerator - odd_denominator * coordinate
        ) // dyadic_modulus
        assert 16 * partial_sum == (
            Fraction(coordinate, dyadic_modulus)
            + Fraction(odd_quotient, odd_denominator)
        )
        quotient_split_checks += 1

        bits = 4 * (depth + 1)
        reflected = reflected_f_mod(depth + 1, bits)
        assert reflected % (1 << r) == 0
        precision = 1 << (bits - r)
        unit_coordinate = (reflected >> r) % precision
        actual_coordinate = numerator * pow(odd_denominator, -1, precision)
        actual_coordinate %= precision
        assert unit_coordinate == actual_coordinate
        assert precision == 256 * dyadic_modulus
        assert unit_coordinate % dyadic_modulus == coordinate
        assert (
            ((unit_coordinate - coordinate) // dyadic_modulus) % 256
            == odd_quotient * pow(odd_denominator, -1, 256) % 256
        )
        coordinate_checks += 1

        upper = int(log10(16) * depth)
        if upper >= 5:
            modulus = dyadic_modulus * odd_denominator
            previous_a: int | None = None
            previous_residue: int | None = None
            odd_factorization = factor_over_primes(odd_denominator, primes)
            assert all(prime <= 8 * depth + 5 for prime in odd_factorization)
            for decimal_exponent in range(5, upper + 1):
                a_value = (10**decimal_exponent - 16) // 16
                residue = a_value * numerator % modulus
                if previous_a is not None and previous_residue is not None:
                    assert a_value == 10 * previous_a + 9
                    assert residue == (10 * previous_residue + 9 * numerator) % modulus
                    recurrence_checks += 2
                previous_a = a_value
                previous_residue = residue

                odd_gcd = gcd(a_value, odd_denominator)
                reduced = Fraction(
                    a_value * numerator // odd_gcd,
                    dyadic_modulus * (odd_denominator // odd_gcd),
                )
                assert reduced == (10**decimal_exponent - 16) * partial_sum
                for prime, exponent in odd_factorization.items():
                    for power in range(1, exponent + 1):
                        prime_power = prime**power
                        assert (odd_gcd % prime_power == 0) == (
                            pow(10, decimal_exponent, prime_power)
                            == 16 % prime_power
                        )
                        gcd_log_checks += 1

        # Exact prime bands that repair the unsupported asymptotic sentence.
        if depth >= 3:
            band_one = [
                prime
                for prime in primes
                if (
                    4 * depth + 3 < prime <= 8 * depth + 1
                    and prime % 8 == 1
                )
                or (
                    4 * depth + 3 < prime <= 8 * depth + 5
                    and prime % 8 == 5
                )
            ]
            band_two = [
                prime
                for prime in primes
                if 3 * prime > 8 * depth + 5 and prime <= 4 * depth + 3
            ]
            assert not set(band_one) & set(band_two)
            for prime in band_one + band_two:
                occurrences = singular_occurrences(depth, prime)
                assert len(occurrences) == 1
                index, slot = occurrences[0]
                assert v_p(odd_denominator, prime) == 1
                numerator_mod_prime = (120 * index * index + 151 * index + 47) % prime
                assert numerator_mod_prime
                if slot == 1:
                    assert 4 * numerator_mod_prime % prime == 5 % prime
                elif slot == 2:
                    assert numerator_mod_prime == 30 % prime
                elif slot == 3:
                    assert 2 * numerator_mod_prime % prime == (-1) % prime
                else:
                    raise AssertionError("the clean bands must not use 2k+1")
                band_survival_checks += 1

        # Separator for beta=1/10.  The finite search is not Kanold's proof.
        factors = factor_over_primes(odd_denominator, primes)
        kanold_upper = 1 << len(factors)
        target = odd_denominator * (Fraction(1, 10) - partial_sum) / 16
        lift, finite_distance = nearest_admissible_lift(
            target, odd_denominator, odd_quotient, kanold_upper
        )
        largest_finite_lift_distance = max(
            largest_finite_lift_distance, finite_distance
        )
        new_quotient = odd_quotient + 256 * lift
        new_numerator = (
            odd_denominator * coordinate + dyadic_modulus * new_quotient
        )
        full_denominator = 16 * dyadic_modulus * odd_denominator
        new_shadow = Fraction(new_numerator, full_denominator)
        assert new_shadow.denominator == partial_sum.denominator
        assert new_shadow == partial_sum + Fraction(16 * lift, odd_denominator)
        assert new_quotient % 256 == odd_quotient % 256
        assert (
            new_numerator * pow(odd_denominator, -1, precision) % precision
            == unit_coordinate
        )
        scaled_change = 16**depth * (new_shadow - partial_sum)
        if scaled_change:
            assert v_p(scaled_change.numerator, 2) >= 4 * (depth + 1)
        error = abs(new_shadow - Fraction(1, 10))
        for decimal_exponent in range(5, upper + 1):
            multiplier = 10**decimal_exponent - 16
            assert circle_distance(multiplier * Fraction(1, 10)) == Fraction(2, 5)
            assert circle_distance(multiplier * new_shadow) >= Fraction(2, 5) - multiplier * error
            separator_checks += 1

        if prior_partial_sum is not None:
            assert (
                (10**max(5, upper) - 16) * (partial_sum - prior_partial_sum)
                == (10**max(5, upper) - 16)
                * coefficient(depth)
                / 16**depth
            )

    # A terminating finite shadow of the Liouville separator.  The report's
    # all-n and transcendence statements require the digit argument, not this
    # bounded replay.
    liouville_shadow = Fraction(1, 10) + sum(
        (Fraction(1, 10 ** factorial(index)) for index in range(2, 6)),
        Fraction(),
    )
    assert Fraction(11, 100) < liouville_shadow < Fraction(1, 9)
    sixteen_fractional = (16 * liouville_shadow) % 1
    assert Fraction(3, 5) < sixteen_fractional < Fraction(7, 9)
    for decimal_exponent in range(121):
        decimal_tail = (10**decimal_exponent * liouville_shadow) % 1
        assert 0 <= decimal_tail <= Fraction(1, 9)
        assert circle_distance(
            (10**decimal_exponent - 16) * liouville_shadow
        ) > Fraction(2, 9)
        liouville_shadow_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"isometry_pair_checks={isometry_pair_checks}")
    print(f"all_depth_valuation_checks={valuation_checks}")
    print(f"full_256_coordinate_checks={coordinate_checks}")
    print(f"quotient_split_checks={quotient_split_checks}")
    print(f"affine_recurrence_checks={recurrence_checks}")
    print(f"prime_power_discrete_log_checks={gcd_log_checks}")
    print(f"clean_prime_band_survival_checks={band_survival_checks}")
    print(f"separator_phase_checks={separator_checks}")
    print(f"largest_finite_lift_distance={largest_finite_lift_distance}")
    print(f"liouville_shadow_checks={liouville_shadow_checks}")
    print("all independent exact checks passed")


if __name__ == "__main__":
    main()
