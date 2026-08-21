#!/usr/bin/env python3
"""Independent exact replay for the fixed-multiplier return audit.

This checks finite rational and valuation assertions only.  It does not
certify any infinite product, series identity, prime-number theorem, or V1.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def valuation(value: int, prime: int) -> int:
    assert value != 0
    value = abs(value)
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def primes_through(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            sieve[prime * prime : bound + 1 : prime] = b"\x00" * (
                (bound - prime * prime) // prime + 1
            )
    return [prime for prime in range(2, bound + 1) if sieve[prime]]


def wallis(index: int) -> Fraction:
    answer = Fraction(2)
    for k in range(1, index + 1):
        answer *= Fraction(4 * k * k, 4 * k * k - 1)
    return answer


def ramanujan_scaled(index: int) -> int:
    return sum(
        (42 * k + 5)
        * math.comb(2 * k, k) ** 3
        * 2 ** (12 * (index - k))
        for k in range(index + 1)
    )


def ramanujan_shadow(index: int) -> Fraction:
    scaled = ramanujan_scaled(index)
    return Fraction(16 * 2 ** (12 * index), scaled)


def ramanujan_term(index: int) -> Fraction:
    return Fraction(
        (42 * index + 5) * math.comb(2 * index, index) ** 3,
        2 ** (12 * index),
    )


def bbp_coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == SOURCE_SHA256

    wallis_prime_checks = 0
    wallis_telescoping_checks = 0
    primes = primes_through(240)
    for index in range(2, 111):
        value = wallis(index)
        for prime in primes:
            if index < prime <= 2 * index:
                assert prime % 2 == 1
                assert valuation(value.denominator, prime) == 2
                wallis_prime_checks += 1
        for endpoint in [index + 1, index + 9, 3 * index + 7]:
            finite = sum(
                (
                    Fraction(1, 4 * k * k - 1)
                    for k in range(index + 1, endpoint + 1)
                ),
                Fraction(),
            )
            assert finite == Fraction(1, 4 * index + 2) - Fraction(
                1, 4 * endpoint + 2
            )
            wallis_telescoping_checks += 1

    central_binomial_checks = 0
    ramanujan_minimum_checks = 0
    ramanujan_denominator_checks = 0
    ramanujan_tail_checks = 0
    for index in range(0, 151):
        central = math.comb(2 * index, index)
        assert valuation(central, 2) == index.bit_count()
        central_binomial_checks += 1

        layer_valuations = [
            12 * (index - k) + 3 * k.bit_count() for k in range(index + 1)
        ]
        assert layer_valuations[-1] == 3 * index.bit_count()
        assert layer_valuations.count(min(layer_valuations)) == 1
        assert min(layer_valuations) == layer_valuations[-1]
        ramanujan_minimum_checks += 3

        scaled = ramanujan_scaled(index)
        expected_v2 = 3 * index.bit_count()
        assert valuation(scaled, 2) == expected_v2
        shadow = ramanujan_shadow(index)
        assert shadow.denominator == scaled // 2**expected_v2
        assert shadow.denominator >= Fraction(
            5 * 2 ** (12 * index), (index + 1) ** 3
        )
        ramanujan_denominator_checks += 3

        omitted = index + 1
        elementary_lower = Fraction(
            42 * omitted + 5,
            64**omitted * (2 * omitted + 1) ** 3,
        )
        assert math.comb(2 * omitted, omitted) * (2 * omitted + 1) >= 4**omitted
        assert ramanujan_term(omitted) >= elementary_lower
        ramanujan_tail_checks += 2

    # The all-depth BBP formula is deliberately recorded only as experiment.
    # The even-depth minimum argument below is the rigorous reusable part.
    bbp_observed_checks = 0
    bbp_even_minimum_checks = 0
    bbp_sum = Fraction()
    for index in range(0, 401):
        coefficient = bbp_coefficient(index)
        assert coefficient.denominator % 2 == 1
        bbp_sum += coefficient / 16**index
        if index >= 1:
            assert valuation(bbp_sum.denominator, 2) == (
                4 * index - valuation(index + 1, 2)
            )
            bbp_observed_checks += 1
        if index >= 2 and index % 2 == 0:
            assert coefficient.numerator % 2 == 1
            endpoint_valuation = -4 * index
            earlier_lower_bound = -4 * index + 4
            assert endpoint_valuation < earlier_lower_bound
            assert valuation(bbp_sum.denominator, 2) == 4 * index
            bbp_even_minimum_checks += 4

    fixed_primary_checks = 0
    for c in [1, 2, 3, 4, 16, 40, 125, 700]:
        for prime in [2, 5]:
            for exponent in range(8, 17):
                assert valuation(10**exponent - c, prime) == valuation(c, prime)
                fixed_primary_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"wallis_private_prime_exact_checks={wallis_prime_checks}")
    print(f"wallis_telescoping_exact_checks={wallis_telescoping_checks}")
    print(f"central_binomial_two_adic_exact_checks={central_binomial_checks}")
    print(f"ramanujan_unique_minimum_exact_checks={ramanujan_minimum_checks}")
    print(f"ramanujan_reduced_denominator_exact_checks={ramanujan_denominator_checks}")
    print(f"ramanujan_tail_lower_exact_checks={ramanujan_tail_checks}")
    print(f"bbp_all_depth_observed_checks={bbp_observed_checks}")
    print(f"bbp_even_depth_proved_pattern_checks={bbp_even_minimum_checks}")
    print(f"fixed_c_primary_valuation_exact_checks={fixed_primary_checks}")
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
