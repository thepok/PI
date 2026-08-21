#!/usr/bin/env python3
"""Exact replay for ``hutton_primary_phase_attack.md``.

All assertions before the phase table use integers or ``Fraction``.  The
complex means in the final table are finite floating-point experiments; they
are neither asymptotic claims nor claims about uncomputed digits of pi.
"""

from __future__ import annotations

import cmath
import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    assert value > 0 and prime > 1
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def floor_log(value: int, base: int) -> int:
    assert value >= 1 and base >= 2
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def primes_through(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            count = (bound - prime * prime) // prime + 1
            sieve[prime * prime : bound + 1 : prime] = b"\x00" * count
    return [candidate for candidate in range(2, bound + 1) if sieve[candidate]]


def hutton_term(odd: int) -> Fraction:
    assert odd >= 1 and odd % 2 == 1
    sign = 1 if odd % 4 == 1 else -1
    return Fraction(
        4 * sign * (2 * 7**odd + 3**odd),
        odd * 3**odd * 7**odd,
    )


def hutton_lower_from_radius(radius: int) -> Fraction:
    assert radius >= 3 and radius % 4 == 3
    return sum(
        (hutton_term(odd) for odd in range(1, radius + 1, 2)),
        Fraction(),
    )


def hutton_width(radius: int) -> Fraction:
    assert radius >= 3 and radius % 4 == 3
    next_odd = radius + 2
    return Fraction(8, next_odd * 3**next_odd) + Fraction(
        4, next_odd * 7**next_odd
    )


def bracket_horizon(radius: int) -> int:
    width = hutton_width(radius)
    answer = -1
    scale = 1
    while scale * width < 1:
        answer += 1
        scale *= 10
    assert 10**answer * width < 1 <= 10 ** (answer + 1) * width
    return answer


def rational_mod(value: Fraction, modulus: int) -> int:
    assert modulus >= 2 and math.gcd(value.denominator, modulus) == 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def local_high_prime_residue(radius: int, prime: int) -> int:
    """Return chi_4(p) A_n modulo p for p > sqrt(radius)."""
    assert prime > 7 and prime * prime > radius and prime <= radius
    prefix = 0
    for odd_multiplier in range(1, radius // prime + 1, 2):
        sign = 1 if odd_multiplier % 4 == 1 else -1
        denominator_3 = odd_multiplier * pow(3, odd_multiplier, prime) % prime
        denominator_7 = odd_multiplier * pow(7, odd_multiplier, prime) % prime
        prefix += sign * (
            8 * pow(denominator_3, -1, prime)
            + 4 * pow(denominator_7, -1, prime)
        )
    prime_sign = 1 if prime % 4 == 1 else -1
    return prime_sign * prefix % prime


def additive_coordinate(state: int, modulus: int, component: int) -> int:
    assert modulus % component == 0
    complement = modulus // component
    assert math.gcd(component, complement) == 1
    return state * pow(complement, -1, component) % component


def crt_pair(first: int, modulus_first: int, second: int, modulus_second: int) -> int:
    assert math.gcd(modulus_first, modulus_second) == 1
    lift = (second - first) * pow(modulus_first, -1, modulus_second)
    return (first + modulus_first * (lift % modulus_second)) % (
        modulus_first * modulus_second
    )


def unit_phase(numerator: int, denominator: int) -> complex:
    return cmath.exp(2j * math.pi * (numerator / denominator))


def log10_fraction(value: Fraction) -> float:
    assert value > 0
    return math.log10(value.numerator) - math.log10(value.denominator)


def main() -> None:
    sys.set_int_max_str_digits(1_000_000)
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    # The infinite simultaneous-primary family R_a = 3^a 7^(a+1).
    family_bound_checks = 0
    for exponent_3 in range(2, 21):
        exponent_7 = exponent_3 + 1
        radius = 3**exponent_3 * 7**exponent_7
        assert radius % 4 == 3
        assert floor_log(radius, 3) <= 3**exponent_3 - 2
        assert floor_log(radius, 7) <= 7**exponent_7 - 2
        assert floor_log(radius, 3) <= 3 * exponent_3 + 1
        assert floor_log(radius, 7) <= 2 * exponent_3
        family_bound_checks += 5

    # Enumerate the dominant-score assertion in the first three members.
    dominant_score_checks = 0
    dominant_bound_assertions = 0
    for exponent_3 in range(2, 5):
        exponent_7 = exponent_3 + 1
        radius = 3**exponent_3 * 7**exponent_7
        for prime, exponent in ((3, exponent_3), (7, exponent_7)):
            final_score = radius + exponent
            earlier_scores = [
                odd + valuation(odd, prime)
                for odd in range(1, radius, 2)
            ]
            assert max(earlier_scores) <= radius - 2
            assert max(earlier_scores) < final_score
            dominant_score_checks += len(earlier_scores)
            dominant_bound_assertions += 2

    # The first tractable member is already large enough to expose the scale.
    exponent_3 = 2
    exponent_7 = 3
    radius = 3**exponent_3 * 7**exponent_7
    index = (radius - 3) // 4
    value = hutton_lower_from_radius(radius)
    numerator = value.numerator
    denominator = value.denominator
    expected_3 = radius + exponent_3
    expected_7 = radius + exponent_7
    assert valuation(denominator, 3) == expected_3
    assert valuation(denominator, 7) == expected_7
    transient = valuation(denominator, 5)
    assert transient == floor_log(radius, 5) == 4

    # Leading primary units, before and after the exact decimal transient.
    modulus_3_low = 3 ** (exponent_3 + 2)
    modulus_7_low = 7 ** (exponent_7 + 2)
    scaled_3 = value * 3**expected_3
    scaled_7 = value * 7**expected_7
    expected_scaled_3 = -8 * pow(7**exponent_7, -1, modulus_3_low)
    expected_scaled_7 = -4 * pow(3**exponent_3, -1, modulus_7_low)
    assert rational_mod(scaled_3, modulus_3_low) == expected_scaled_3 % modulus_3_low
    assert rational_mod(scaled_7, modulus_7_low) == expected_scaled_7 % modulus_7_low

    post_modulus = denominator // 5**transient
    post_state = pow(2, transient, post_modulus) * numerator % post_modulus
    primary_3 = 3**expected_3
    primary_7 = 7**expected_7
    primary_product = primary_3 * primary_7
    primary_complement = post_modulus // primary_product
    assert math.gcd(primary_product, primary_complement) == 1
    primary_coordinate = additive_coordinate(
        post_state, post_modulus, primary_product
    )
    expected_coordinate_3 = (
        -8 * pow(10, transient, modulus_3_low) * pow(7, radius, modulus_3_low)
    ) % modulus_3_low
    expected_coordinate_7 = (
        -4 * pow(10, transient, modulus_7_low) * pow(3, radius, modulus_7_low)
    ) % modulus_7_low
    assert primary_coordinate % modulus_3_low == expected_coordinate_3
    assert primary_coordinate % modulus_7_low == expected_coordinate_7

    # Every surviving prime above sqrt(R) occurs once, and its coordinate is
    # the exact shorter-Hutton-prefix residue.
    primes = primes_through(radius)
    high_prime_primes = 0
    high_prime_classification_assertions = 0
    high_prime_coordinate_checks = 0
    surviving_high_primes: list[int] = []
    for prime in primes:
        if prime <= math.isqrt(radius) or prime <= 7:
            continue
        high_prime_primes += 1
        expected = local_high_prime_residue(radius, prime)
        denominator_exponent = valuation(denominator, prime)
        assert denominator_exponent in (0, 1)
        assert (denominator_exponent == 1) == (expected != 0)
        if denominator_exponent == 1:
            surviving_high_primes.append(prime)
            local_coordinate = additive_coordinate(
                post_state, post_modulus, prime
            )
            assert local_coordinate == (
                pow(10, transient, prime) * expected
            ) % prime
            high_prime_coordinate_checks += 1
        assert rational_mod(prime * value, prime) == expected
        high_prime_classification_assertions += 3

    selected_modulus = primary_product * math.prod(surviving_high_primes)
    unresolved_modulus = post_modulus // selected_modulus
    assert math.gcd(selected_modulus, unresolved_modulus) == 1
    assert unresolved_modulus <= radius ** math.isqrt(radius)
    assert unresolved_modulus == 3443846140271004739007417826008487767

    # Re-factor the unresolved part and verify that it uses only primes below
    # sqrt(R), as the general compression proof asserts.
    unresolved_factor_checks = 0
    remaining = unresolved_modulus
    unresolved_factors: list[tuple[int, int]] = []
    for prime in primes:
        if prime > math.isqrt(radius):
            break
        if prime in (2, 3, 5, 7):
            continue
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            unresolved_factors.append((prime, exponent))
            assert exponent <= floor_log(radius, prime)
            unresolved_factor_checks += 1
    assert remaining == 1

    # The exact low-primary information admits a least CRT lift which has the
    # same full denominator and period, yet is essentially stationary for the
    # entire Hutton transfer horizon.  This is an exact separator, not a claim
    # about the actual coordinate.
    low_primary_modulus = modulus_3_low * modulus_7_low
    stationary_lift = crt_pair(
        expected_coordinate_3,
        modulus_3_low,
        expected_coordinate_7,
        modulus_7_low,
    )
    assert 0 < stationary_lift < low_primary_modulus
    assert math.gcd(stationary_lift, primary_product) == 1
    assert math.gcd(primary_coordinate, primary_product) == 1
    assert stationary_lift % modulus_3_low == expected_coordinate_3
    assert stationary_lift % modulus_7_low == expected_coordinate_7

    horizon = bracket_horizon(radius)
    offsets = horizon - transient + 1
    assert stationary_lift * 10 ** (offsets - 1) < primary_product
    geometric_sum = (10**offsets - 1) // 9
    # Mean chord error is at most the following value (apart from the factor
    # 2*pi).  The strict integer comparison gives a huge certified margin.
    chord_ratio = Fraction(stationary_lift * geometric_sum, offsets * primary_product)
    assert chord_ratio < Fraction(1, 10**2500)

    # Exact additive-CRT reconstruction for the actual state.
    enriched_coordinate = additive_coordinate(
        post_state, post_modulus, selected_modulus
    )
    unresolved_coordinate = additive_coordinate(
        post_state, post_modulus, unresolved_modulus
    )
    assert fractional_part(
        Fraction(enriched_coordinate, selected_modulus)
        + Fraction(unresolved_coordinate, unresolved_modulus)
    ) == Fraction(post_state, post_modulus)

    # Finite floating-point experiment: actual short sums.  These values are
    # intentionally not used in any assertion above.
    components = [
        primary_3,
        primary_7,
        primary_product,
        selected_modulus,
        unresolved_modulus,
        post_modulus,
    ]
    labels = [
        "3-primary",
        "7-primary",
        "3x7-primary",
        "primary+high-prime",
        "complement",
        "full",
    ]
    coordinates = [
        additive_coordinate(post_state, post_modulus, component)
        for component in components
    ]
    running = [0j for _ in components]
    checkpoints = {radius // 10, radius // 4, offsets}
    phase_rows: list[tuple[int, list[float]]] = []
    for offset in range(1, offsets + 1):
        for position, (coordinate, component) in enumerate(
            zip(coordinates, components)
        ):
            running[position] += unit_phase(coordinate, component)
            coordinates[position] = coordinate * 10 % component
        if offset in checkpoints:
            phase_rows.append(
                (offset, [abs(total / offset) for total in running])
            )

    print(f"claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"family_bound_checks={family_bound_checks}")
    print(f"dominant_score_checks={dominant_score_checks}")
    print(f"dominant_bound_assertions={dominant_bound_assertions}")
    print(f"high_prime_primes={high_prime_primes}")
    print(
        "high_prime_classification_assertions="
        f"{high_prime_classification_assertions}"
    )
    print(
        f"high_prime_coordinate_checks={high_prime_coordinate_checks}"
    )
    print(f"unresolved_factor_checks={unresolved_factor_checks}")
    print(
        "exact_sample="
        f"a:{exponent_3},c:{exponent_7},R:{radius},K:{index},"
        f"v3:{expected_3},v7:{expected_7},b:{transient},"
        f"q_digits:{len(str(denominator))},"
        f"primary_digits:{len(str(primary_product))},"
        f"selected_digits:{len(str(selected_modulus))},"
        f"complement_digits:{len(str(unresolved_modulus))},"
        f"surviving_high_primes:{len(surviving_high_primes)},"
        f"horizon:{horizon},offsets:{offsets}"
    )
    print(
        "stationary_separator="
        f"least_lift:{stationary_lift},low_modulus:{low_primary_modulus},"
        f"log10_mean_chord_bound:"
        f"{math.log10(2 * math.pi) + log10_fraction(chord_ratio):.6f}"
    )
    print("finite actual-phase means: N " + " ".join(labels))
    for count, means in phase_rows:
        print(
            f"  {count:4d} "
            + " ".join(f"{mean:.12f}" for mean in means)
        )
    print(f"unresolved_factors={unresolved_factors}")
    print("all exact checks passed; complex means are experiments only")


if __name__ == "__main__":
    main()
