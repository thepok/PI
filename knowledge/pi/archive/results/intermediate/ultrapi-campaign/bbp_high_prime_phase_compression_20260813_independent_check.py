#!/usr/bin/env python3
"""Independent exact checks for the high-prime phase-compression audit.

All finite output is an ``experiment``.  This file does not import the
primary checker and does not prove PNT/AP, a fixed return, or V1.
"""

from __future__ import annotations

import argparse
import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
PRIMARY_REPORT_SHA256 = (
    "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564"
)
PRIMARY_CHECKER_SHA256 = (
    "7df64d082de31da1d902fa0e6418b97a5101cd14f93e495d141631535f3925ed"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def digest(relative: str) -> str:
    return hashlib.sha256((root() / relative).read_bytes()).hexdigest()


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def valuation(integer: int, prime: int) -> int:
    assert integer
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def power_of_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def localization(depth: int, prime: int) -> Fraction:
    """Rebuild G_(M,p) directly from the four pole families."""
    assert prime > 5
    chi_two = 1 if prime % 8 in (1, 7) else -1
    answer = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            answer -= power_of_two(6 - multiplier) / multiplier
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            answer += Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            answer -= Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return answer


def table_value(depth: int, prime: int) -> Fraction:
    positive = prime % 4 == 1
    assert positive or prime % 4 == 3
    if 3 * prime > 8 * depth + 5:
        return Fraction(64 if positive else -32)
    if prime > 2 * depth + 1:
        return Fraction(64) if positive else Fraction(-128, 3)
    if 5 * prime > 8 * depth + 5:
        return Fraction(56) if positive else Fraction(-152, 3)
    if 3 * prime > 4 * depth + 3:
        return Fraction(264, 5) if positive else Fraction(-152, 3)
    if 7 * prime > 8 * depth + 5:
        return Fraction(752, 15) if positive else Fraction(-152, 3)
    return Fraction(752, 15) if positive else Fraction(-1040, 21)


def exact_band(depth: int, prime: int) -> int:
    if 3 * prime > 8 * depth + 5:
        return 1
    if prime > 2 * depth + 1:
        return 2
    if 5 * prime > 8 * depth + 5:
        return 3
    if 3 * prime > 4 * depth + 3:
        return 4
    if 7 * prime > 8 * depth + 5:
        return 5
    return 6


def ideal_band(depth: int, prime: int) -> int:
    if 3 * prime > 8 * depth:
        return 1
    if prime > 2 * depth:
        return 2
    if 5 * prime > 8 * depth:
        return 3
    if 3 * prime > 4 * depth:
        return 4
    if 7 * prime > 8 * depth:
        return 5
    return 6


def possible_support(depth: int, prime: int) -> bool:
    if prime <= 4 * depth + 3:
        return True
    return (
        prime % 8 == 1 and prime <= 8 * depth + 1
    ) or (
        prime % 8 == 5 and prime <= 8 * depth + 5
    )


def ideal_support(depth: int, prime: int) -> bool:
    return prime <= 4 * depth or (
        prime <= 8 * depth and prime % 4 == 1
    )


def lift(value: Fraction, prime: int) -> tuple[int, int]:
    numerator = value.numerator
    denominator = value.denominator
    assert math.gcd(prime, denominator) == 1
    residue = numerator * pow(denominator, -1, prime) % prime
    kappa = -numerator * pow(prime, -1, denominator) % denominator
    discrepancy = (
        Fraction(residue, prime)
        - Fraction(kappa, denominator)
        - Fraction(numerator, denominator * prime)
    )
    assert discrepancy.denominator == 1
    return residue, kappa


def a_multiplier(exponent: int) -> int:
    assert exponent >= 4
    return (10**exponent - 16) // 16


def a_multiplier_mod(exponent: int, modulus: int) -> int:
    assert exponent >= 4 and modulus > 0
    return (
        pow(2, exponent - 4, modulus)
        * pow(5, exponent, modulus)
        - 1
    ) % modulus


def lcm_upto(limit: int) -> int:
    answer = 1
    for value in range(1, limit + 1):
        answer = math.lcm(answer, value)
    return answer


def common_denominator(limit: int) -> int:
    return 2 ** (2 * limit) * lcm_upto(limit)


def factor_small(integer: int, primes: list[int]) -> dict[int, int]:
    answer: dict[int, int] = {}
    remaining = integer
    for prime in primes:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            answer[prime] = exponent
        if remaining == 1:
            break
    assert remaining == 1
    return answer


def euler_phi(integer: int, factors: dict[int, int]) -> int:
    answer = integer
    for prime in factors:
        answer = answer // prime * (prime - 1)
    return answer


def multiplicative_order(base: int, modulus: int, primes: list[int]) -> int:
    if modulus == 1:
        return 1
    assert math.gcd(base, modulus) == 1
    modulus_factors = factor_small(modulus, primes)
    order = euler_phi(modulus, modulus_factors)
    order_factors = factor_small(order, primes)
    for prime, exponent in order_factors.items():
        for _ in range(exponent):
            if order % prime or pow(base, order // prime, modulus) != 1:
                break
            order //= prime
    assert pow(base, order, modulus) == 1
    return order


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=400)
    args = parser.parse_args()
    if args.max_depth < 400:
        raise SystemExit("--max-depth must be at least 400")

    assert digest("problems/local/pi-digits.txt") == SOURCE_SHA256
    assert digest(
        "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md"
    ) == PRIMARY_REPORT_SHA256
    assert digest(
        "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_check.py"
    ) == PRIMARY_CHECKER_SHA256

    primes = primes_through(8 * args.max_depth + 5)
    coordinates = (
        Fraction(64),
        Fraction(-32),
        Fraction(-128, 3),
        Fraction(56),
        Fraction(-152, 3),
        Fraction(264, 5),
        Fraction(752, 15),
        Fraction(-1040, 21),
    )

    elementary_lift_checks = 0
    for coordinate in coordinates:
        assert 105 % coordinate.denominator == 0
        for prime in primes_through(2000):
            if prime <= 47 or 105 % prime == 0:
                continue
            lift(coordinate, prime)
            elementary_lift_checks += 1

    expected_kappas = {
        Fraction(-128, 3): lambda p: 2 * pow(p, -1, 3) % 3,
        Fraction(-152, 3): lambda p: 2 * pow(p, -1, 3) % 3,
        Fraction(264, 5): lambda p: pow(p, -1, 5) % 5,
        Fraction(752, 15): lambda p: -2 * pow(p, -1, 15) % 15,
        Fraction(-1040, 21): lambda p: 11 * pow(p, -1, 21) % 21,
    }
    kappa_table_checks = 0
    dependence_mod_840_checks = 0
    for coordinate, expected in expected_kappas.items():
        for residue_class in range(1, 840):
            if math.gcd(residue_class, 840) != 1:
                continue
            _, kappa = lift(coordinate, residue_class)
            assert kappa == expected(residue_class)
            _, shifted = lift(coordinate, residue_class + 840)
            assert shifted == kappa
            kappa_table_checks += 1
            dependence_mod_840_checks += 1

    period = (99, 54, 24, 39, 84, 9)
    period_checks = 0
    for exponent in range(4, 1200):
        residue = a_multiplier(exponent) % 105
        assert residue == period[(exponent - 4) % 6]
        assert residue % 3 == 0
        if exponent % 6 == 2:
            assert math.gcd(residue, 105) == 21
        period_checks += 1

    # Derive the seven effective density weights from the two mod-4 rows.
    band_weights = (
        Fraction(32, 105),
        Fraction(-4, 15),
        Fraction(16, 15),
        Fraction(8, 3),
        Fraction(32, 3),
        Fraction(16),
        Fraction(32),
    )
    assert band_weights[0] == (Fraction(752, 15) + Fraction(-1040, 21)) / 2
    assert band_weights[1] == (Fraction(752, 15) + Fraction(-152, 3)) / 2
    assert band_weights[2] == (Fraction(264, 5) + Fraction(-152, 3)) / 2
    assert band_weights[3] == (Fraction(56) + Fraction(-152, 3)) / 2
    assert band_weights[4] == (Fraction(64) + Fraction(-128, 3)) / 2
    assert band_weights[5] == (Fraction(64) + Fraction(-32)) / 2
    # Above 4M, the two supported mod-8 classes have combined density 1/2.
    assert band_weights[6] == Fraction(64, 2)
    boundaries = (
        Fraction(1),
        Fraction(8, 7),
        Fraction(4, 3),
        Fraction(8, 5),
        Fraction(2),
        Fraction(8, 3),
        Fraction(4),
        Fraction(8),
    )
    band_constant = sum(
        float(weight) * math.log(float(upper / lower))
        for weight, lower, upper in zip(
            band_weights, boundaries, boundaries[1:]
        )
    )
    stated_constant = (
        32 * math.log(3)
        - 16 * math.log(3 / 2)
        + 32 / 3 * math.log(4 / 3)
        + 8 / 3 * math.log(5 / 4)
        + 16 / 15 * math.log(6 / 5)
        - 4 / 15 * math.log(7 / 6)
        + 32 / 105 * math.log(8 / 7)
    )
    assert abs(band_constant - stated_constant) < 1e-13
    assert 16 * math.log(6) > 4 / 15 * math.log(7 / 6)
    assert stated_constant > 0

    grid_checks = 0
    table_checks = 0
    endpoint_band_discrepancies = 0
    endpoint_support_discrepancies = 0
    maximum_band_discrepancies = 0
    maximum_support_discrepancies = 0
    signatures: dict[tuple[int, int], tuple[int, int, int]] = {}
    samples: dict[int, tuple[int, Fraction, int]] = {}
    for depth in range(48, args.max_depth + 1):
        xi = Fraction()
        harmonic = Fraction()
        numerator_105 = 0
        count = 0
        row_band_discrepancies = 0
        row_support_discrepancies = 0
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            exact_support = possible_support(depth, prime)
            asymptotic_support = ideal_support(depth, prime)
            if exact_support != asymptotic_support:
                row_support_discrepancies += 1
            coordinate = localization(depth, prime)
            assert bool(coordinate) == exact_support
            if not coordinate:
                continue
            assert coordinate == table_value(depth, prime)
            if exact_band(depth, prime) != ideal_band(depth, prime):
                row_band_discrepancies += 1
            residue, kappa = lift(coordinate, prime)
            xi += Fraction(residue, prime)
            harmonic += coordinate / prime
            numerator_105 += 105 // coordinate.denominator * kappa
            signature = (
                coordinate.numerator,
                coordinate.denominator,
                105 // coordinate.denominator * kappa % 105,
            )
            key = (exact_band(depth, prime), prime % 840)
            if key in signatures:
                assert signatures[key] == signature
            else:
                signatures[key] = signature
            count += 1
            table_checks += 1
        assert (
            xi
            - harmonic
            - Fraction(numerator_105 % 105, 105)
        ).denominator == 1
        # Each of the five bounded endpoint shifts can move at most one
        # prime between adjacent bands.
        assert row_band_discrepancies <= 5
        assert row_support_discrepancies <= 3
        endpoint_band_discrepancies += row_band_discrepancies
        endpoint_support_discrepancies += row_support_discrepancies
        maximum_band_discrepancies = max(
            maximum_band_discrepancies, row_band_discrepancies
        )
        maximum_support_discrepancies = max(
            maximum_support_discrepancies, row_support_discrepancies
        )
        grid_checks += 1
        if depth in (48, 100, 200, 400, args.max_depth):
            samples[depth] = (numerator_105 % 105, harmonic, count)

    # Independently connect the localization residue to the reduced BBP
    # rational at four depths.
    actual_depths = (48, 73, 109, 151)
    partial_sum = Fraction()
    actual_crt_checks = 0
    for depth in range(max(actual_depths) + 1):
        partial_sum += coefficient(depth) / 16**depth
        if depth not in actual_depths:
            continue
        two_exponent = valuation(partial_sum.denominator, 2)
        odd_denominator = partial_sum.denominator >> two_exponent
        dyadic_modulus = 1 << (two_exponent - 4)
        dyadic_coordinate = (
            partial_sum.numerator
            * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            partial_sum.numerator
            - odd_denominator * dyadic_coordinate
        ) // dyadic_modulus
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = localization(depth, prime)
            assert (odd_denominator % prime == 0) == bool(coordinate)
            if not coordinate:
                continue
            actual = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            predicted, _ = lift(coordinate, prime)
            assert actual == predicted
            actual_crt_checks += 1

    # The distance claim is a purely geometric consequence once 0<H<1/210.
    geometric_grid_checks = 0
    for numerator in range(105):
        for denominator in (211, 997, 10007):
            small = Fraction(1, denominator)
            assert small < Fraction(1, 210)
            phase = Fraction(numerator, 105) + small
            distance = min(
                circle_distance(phase - Fraction(point, 105))
                for point in range(105)
            )
            assert distance == small
            geometric_grid_checks += 1

    moving_grid_checks = 0
    moving_denominator_checks = 0
    moving_period_checks = 0
    moving_product_checks = 0
    small_primes = primes_through(500)
    for depth, level in ((120, 3), (240, 5), (400, 7)):
        cutoff = Fraction(depth, level)
        multiplier_limit = (8 * depth + 5) * level // depth
        denominator_grid = common_denominator(multiplier_limit)
        xi = Fraction()
        harmonic = Fraction()
        numerator_grid = 0
        selected: list[int] = []
        for prime in primes:
            if prime * level <= depth or prime <= multiplier_limit:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = localization(depth, prime)
            if not coordinate:
                continue
            assert denominator_grid % coordinate.denominator == 0
            residue, kappa = lift(coordinate, prime)
            xi += Fraction(residue, prime)
            harmonic += coordinate / prime
            numerator_grid += (
                denominator_grid // coordinate.denominator * kappa
            )
            # At these deliberately small finite cutoffs, modular numerator
            # cancellation can still occur.  The asymptotic height argument
            # removes it eventually; only nonzero residues are actual
            # surviving denominator primes in this replay.
            if residue:
                selected.append(prime)
            moving_denominator_checks += 1
        grid = Fraction(
            numerator_grid % denominator_grid, denominator_grid
        )
        assert (xi - harmonic - grid).denominator == 1
        selected_product = math.prod(selected)
        assert harmonic.denominator % selected_product == 0
        moving_product_checks += len(selected)

        exponent_two = valuation(denominator_grid, 2)
        exponent_five = valuation(denominator_grid, 5)
        unit_modulus = denominator_grid
        unit_modulus //= 2**exponent_two
        unit_modulus //= 5**exponent_five
        order = multiplicative_order(10, unit_modulus, small_primes)
        transient = max(4 + exponent_two, exponent_five, 4)
        for exponent in range(transient, transient + 12):
            first = a_multiplier_mod(exponent, denominator_grid)
            second = a_multiplier_mod(
                exponent + order, denominator_grid
            )
            assert first == second
            assert first % (2**exponent_two) == (-1) % (2**exponent_two)
            assert first % (5**exponent_five) == (-1) % (5**exponent_five)
            moving_period_checks += 1
        moving_grid_checks += 1

    annihilation_checks = 0
    maximum_killed_fraction = 0.0
    for depth in (80, 160, 320, 400):
        high_primes = [
            prime
            for prime in primes
            if depth < prime <= 8 * depth + 5
            and localization(depth, prime)
        ]
        total_mass = sum(math.log(prime) for prime in high_primes)
        upper = len(str(16**depth)) - 1
        for exponent in range(depth, upper + 1):
            multiplier = a_multiplier(exponent)
            killed = [
                prime for prime in high_primes if multiplier % prime == 0
            ]
            killed_product = math.prod(killed)
            killed_mass = sum(math.log(prime) for prime in killed)
            assert multiplier % killed_product == 0
            assert killed_mass <= math.log(abs(multiplier)) + 1e-12
            assert math.log(abs(multiplier)) < exponent * math.log(10)
            assert total_mass - killed_mass >= 0
            maximum_killed_fraction = max(
                maximum_killed_fraction,
                killed_mass / depth,
            )
            annihilation_checks += 1

    print("status: PASS")
    print("audit_label: experiment")
    print(f"primary_report_sha256: {PRIMARY_REPORT_SHA256}")
    print(f"primary_checker_sha256: {PRIMARY_CHECKER_SHA256}")
    print(f"elementary_lift_checks: {elementary_lift_checks}")
    print(f"kappa_table_checks: {kappa_table_checks}")
    print(f"dependence_mod_840_checks: {dependence_mod_840_checks}")
    print(f"period_mod_105_checks: {period_checks}")
    print(f"high_prime_table_checks: {table_checks}")
    print(f"aggregate_grid_checks: {grid_checks}")
    print(f"actual_reduced_crt_checks: {actual_crt_checks}")
    print(f"endpoint_band_discrepancies: {endpoint_band_discrepancies}")
    print(f"maximum_band_discrepancies_per_depth: {maximum_band_discrepancies}")
    print(f"endpoint_support_discrepancies: {endpoint_support_discrepancies}")
    print(
        "maximum_support_discrepancies_per_depth: "
        f"{maximum_support_discrepancies}"
    )
    print(f"geometric_grid_checks: {geometric_grid_checks}")
    print(f"moving_denominator_checks: {moving_denominator_checks}")
    print(f"moving_grid_checks: {moving_grid_checks}")
    print(f"moving_period_checks: {moving_period_checks}")
    print(f"moving_reduced_denominator_checks: {moving_product_checks}")
    print(f"annihilation_budget_checks: {annihilation_checks}")
    print(f"derived_asymptotic_constant: {stated_constant:.15f}")
    print(
        "maximum_observed_killed_log_mass_over_depth: "
        f"{maximum_killed_fraction:.15f}"
    )
    last_grid, last_harmonic, last_count = samples[args.max_depth]
    print(f"last_high_prime_count: {last_count}")
    print(f"last_grid_numerator_mod_105: {last_grid}")
    print(f"last_harmonic_lift: {float(last_harmonic):.15f}")
    print("asserts_fixed_sixteen_return: false")
    print("asserts_v1: false")


if __name__ == "__main__":
    main()
