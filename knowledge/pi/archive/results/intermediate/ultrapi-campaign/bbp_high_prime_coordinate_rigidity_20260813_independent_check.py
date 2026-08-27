#!/usr/bin/env python3
"""Independent exact replay of the BBP high-prime rigidity argument.

This checker deliberately does not import ``fractions.Fraction`` or either
earlier checker.  Rational arithmetic is performed with normalized integer
pairs.  Every finite row has claim label ``experiment``; in particular this
script asserts neither the fixed-sixteen return nor canonical V1.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd, log
from pathlib import Path


PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813.md":
        "419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42",
    "work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_check.py":
        "b80afdebbcb75b4c45a30a11fb3f8cf618119124d4354c637e559730bf3ef157",
}


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def verify_pins() -> None:
    for relative, expected in PINS.items():
        actual = hashlib.sha256((root() / relative).read_bytes()).hexdigest()
        assert actual == expected, (relative, expected, actual)


def normalize(numerator: int, denominator: int) -> tuple[int, int]:
    assert denominator != 0
    if denominator < 0:
        numerator = -numerator
        denominator = -denominator
    divisor = gcd(abs(numerator), denominator)
    return numerator // divisor, denominator // divisor


def add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    shared = gcd(b, d)
    return normalize(a * (d // shared) + c * (b // shared), b * (d // shared))


def subtract(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return add(left, (-right[0], right[1]))


def lcm(left: int, right: int) -> int:
    return left // gcd(left, right) * right


def valuation(integer: int, prime: int) -> int:
    exponent = 0
    while integer % prime == 0:
        integer //= prime
        exponent += 1
    return exponent


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power <= value // base:
        power *= base
        exponent += 1
    return exponent


def primes_through(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for candidate in range(2, int(limit**0.5) + 1):
        if flags[candidate]:
            first = candidate * candidate
            flags[first : limit + 1 : candidate] = b"\x00" * (
                (limit - first) // candidate + 1
            )
    return [candidate for candidate in range(2, limit + 1) if flags[candidate]]


def factor(integer: int, primes: list[int]) -> dict[int, int]:
    assert integer > 0
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
        answer[remaining] = answer.get(remaining, 0) + 1
    return answer


def pole_values(index: int) -> tuple[int, int, int, int]:
    return 2 * index + 1, 4 * index + 3, 8 * index + 1, 8 * index + 5


def coefficient(index: int) -> tuple[int, int]:
    poles = pole_values(index)
    return normalize(
        120 * index * index + 151 * index + 47,
        poles[0] * poles[1] * poles[2] * poles[3],
    )


def term(index: int) -> tuple[int, int]:
    numerator, denominator = coefficient(index)
    return normalize(numerator, denominator * 16**index)


def coordinate(numerator: int, odd_denominator: int, prime: int) -> int:
    complementary = odd_denominator // prime
    assert odd_denominator % prime == 0
    assert gcd(complementary, prime) == 1
    return numerator * pow(complementary, -1, prime) % prime


def check_pairwise_resultants(primes: list[int]) -> list[int]:
    # For affine forms a*k+b and c*k+d, every common prime divisor divides
    # a*d-b*c.  The six values below independently expose the exceptional
    # primes; no odd prime above 5 can divide two poles at the same index.
    forms = ((2, 1), (4, 3), (8, 1), (8, 5))
    resultants: list[int] = []
    for left_index, (a, b) in enumerate(forms):
        for c, d in forms[left_index + 1 :]:
            determinant = abs(a * d - b * c)
            resultants.append(determinant)
            assert set(factor(determinant, primes)) <= {2, 3, 5}
    return resultants


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=180)
    args = parser.parse_args()
    assert args.max_depth >= 12

    verify_pins()
    primes = primes_through(8 * args.max_depth + 5)
    resultants = check_pairwise_resultants(primes)

    partial = (0, 1)
    ambient_odd_lcm = 1
    rows = 0
    coordinate_checks = 0
    spacing_checks = 0
    exponent_checks = 0
    cancellation_examples = 0
    uniqueness_flags: list[tuple[int, bool]] = []
    minimum_log_ratio = float("inf")
    final_log_cofactor_over_depth = 0.0

    for depth in range(args.max_depth + 1):
        coeff_numerator, coeff_denominator = coefficient(depth)
        assert coeff_numerator > 0
        if depth >= 1:
            # This is the termwise inequality behind the geometric BBP tail
            # estimate: a(k) <= 1/k^2.
            assert coeff_numerator * depth * depth <= coeff_denominator

        partial = add(partial, term(depth))
        pole_product = 1
        for value in pole_values(depth):
            pole_product *= value
        ambient_odd_lcm = lcm(ambient_odd_lcm, pole_product)

        if depth < 12:
            continue

        numerator, denominator = partial
        two_exponent = valuation(denominator, 2)
        assert two_exponent == 4 * depth - valuation(depth + 1, 2)
        odd_denominator = denominator >> two_exponent
        dyadic_denominator = 1 << (two_exponent - 4)
        assert denominator == 16 * dyadic_denominator * odd_denominator
        assert numerator % 2 == 1
        assert gcd(numerator, odd_denominator) == 1
        assert ambient_odd_lcm % odd_denominator == 0

        dyadic_coordinate = (
            numerator
            * pow(odd_denominator, -1, dyadic_denominator)
            % dyadic_denominator
        )
        assert dyadic_coordinate % 2 == 1
        quotient_difference = numerator - odd_denominator * dyadic_coordinate
        assert quotient_difference % dyadic_denominator == 0
        odd_quotient_numerator = quotient_difference // dyadic_denominator
        assert gcd(odd_quotient_numerator, odd_denominator) == 1

        factors = factor(odd_denominator, primes)
        assert 2 not in factors
        high_prime_product = 1
        for prime, exponent in factors.items():
            if prime > depth:
                # Both ingredients matter: p^2 exceeds every individual pole,
                # and the resultant test forbids p in two different poles.
                assert prime > 5
                assert prime * prime > 8 * depth + 5
                assert exponent == 1
                high_prime_product *= prime
            elif prime > 5:
                assert exponent <= floor_log(prime, 8 * depth + 5)
                exponent_checks += 1
            else:
                assert prime in (3, 5)
                assert exponent <= 4 * floor_log(prime, 8 * depth + 5)
                exponent_checks += 1

        cofactor = odd_denominator // high_prime_product
        assert odd_denominator == high_prime_product * cofactor
        assert gcd(high_prime_product, cofactor) == 1
        assert all(prime <= depth for prime in factor(cofactor, primes))

        # Check the claimed prime-power envelope directly.  This is a finite
        # replay of the local estimate, not a proof of the PNT asymptotic.
        envelope = 1
        for prime in primes:
            if prime > depth:
                break
            multiplier = 4 if prime in (3, 5) else 1
            if prime == 2:
                continue
            envelope *= prime ** (multiplier * floor_log(prime, 8 * depth + 5))
        assert envelope % cofactor == 0

        base_shadow = normalize(
            odd_denominator * dyadic_coordinate
            + dyadic_denominator * odd_quotient_numerator,
            16 * dyadic_denominator * odd_denominator,
        )
        assert base_shadow == partial

        for lattice_index in (-3, -1, 1, 2):
            alternative_quotient = (
                odd_quotient_numerator + high_prime_product * lattice_index
            )
            alternative_numerator = (
                odd_denominator * dyadic_coordinate
                + dyadic_denominator * alternative_quotient
            )

            # No fixed 2-factor or retained high prime can cancel.  Factors in
            # the deliberately unpreserved small-prime cofactor may cancel.
            assert gcd(
                abs(alternative_numerator),
                16 * dyadic_denominator * high_prime_product,
            ) == 1
            if gcd(abs(alternative_numerator), cofactor) > 1:
                cancellation_examples += 1

            for prime, exponent in factors.items():
                if prime <= depth:
                    continue
                assert exponent == 1
                assert coordinate(
                    odd_quotient_numerator, odd_denominator, prime
                ) == coordinate(alternative_quotient, odd_denominator, prime)
                coordinate_checks += 1

            alternative_shadow = normalize(
                alternative_numerator,
                16 * dyadic_denominator * odd_denominator,
            )
            exact_difference = subtract(alternative_shadow, partial)
            expected_difference = normalize(lattice_index, 16 * cofactor)
            assert exact_difference == expected_difference
            spacing_checks += 1

        # The exact factor 16 produces 32 (not 2) in the comparison with two
        # BBP-tail radii.
        twice_tail_numerator = 2
        twice_tail_denominator = 15 * (depth + 1) ** 2 * 16**depth
        spacing_numerator = 1
        spacing_denominator = 16 * cofactor
        unique = (
            twice_tail_numerator * spacing_denominator
            < spacing_numerator * twice_tail_denominator
        )
        uniqueness_flags.append((depth, unique))
        log_ratio = (
            depth * log(16)
            + log(15)
            + 2 * log(depth + 1)
            - log(32 * cofactor)
        )
        minimum_log_ratio = min(minimum_log_ratio, log_ratio)
        final_log_cofactor_over_depth = log(cofactor) / depth
        rows += 1

    permanent_onset = None
    for index, (depth, _) in enumerate(uniqueness_flags):
        if all(flag for _, flag in uniqueness_flags[index:]):
            permanent_onset = depth
            break
    assert permanent_onset is not None
    assert uniqueness_flags[-1][1]
    assert cancellation_examples > 0

    print(json.dumps({
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
        "claim_label": "experiment",
        "cofactor_cancellation_examples": cancellation_examples,
        "coordinate_preservation_checks": coordinate_checks,
        "depths_checked": rows,
        "final_log_cofactor_over_depth": final_log_cofactor_over_depth,
        "lattice_spacing_checks": spacing_checks,
        "maximum_depth": args.max_depth,
        "minimum_log_spacing_over_two_tail": minimum_log_ratio,
        "observed_permanent_uniqueness_onset": permanent_onset,
        "prime_exponent_bound_checks": exponent_checks,
        "resultants": resultants,
        "status": "PASS",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
