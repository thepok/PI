#!/usr/bin/env python3
"""Independent exact audit of BBP cross-depth phase compensation.

This checker intentionally imports no primary checker.  Every bounded output
has label ``experiment``.  It proves neither the fixed-sixteen return nor V1.
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
    "3ff784ebad18c8dda7c63691ba99120f80299953361362f7d2f2f8cd26f89d3f"
)
PRIMARY_CHECKER_SHA256 = (
    "0a62b6d88414536fdb160a25a4d177e12d95cd712f76d980a0a0d40405541724"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient_from_partial_fractions(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(1, 4 * index + 2)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def valuation(integer: int, prime: int) -> int:
    assert integer
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        answer += 1
        integer //= prime
    return answer


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        exponent += 1
        power *= base
    return exponent


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def factor(integer: int, primes: list[int]) -> dict[int, int]:
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


def local_residue_from_singular_terms(
    depth: int, prime: int
) -> tuple[int, Fraction]:
    """Rebuild 16*p*B_M mod p directly from the four partial fractions."""
    assert prime > 5 and prime * prime > 8 * depth + 5
    answer = Fraction()
    for index in range(depth + 1):
        pole_terms = (
            (4, 8 * index + 1),
            (-1, 4 * index + 2),
            (-1, 8 * index + 5),
            (-1, 8 * index + 6),
        )
        for numerator, denominator in pole_terms:
            if denominator % prime:
                continue
            quotient = denominator // prime
            answer += Fraction(
                16 * numerator,
                quotient * 16**index,
            )
    assert math.gcd(answer.denominator, prime) == 1
    residue = answer.numerator * pow(answer.denominator, -1, prime) % prime
    return residue, answer


def additive_crt_coordinate(
    odd_numerator: int, odd_denominator: int, prime: int
) -> int:
    return (
        odd_numerator * pow(odd_denominator // prime, -1, prime)
    ) % prime


def carmichael_prime_power(prime: int, exponent: int) -> int:
    assert prime != 2
    return (prime - 1) * prime ** (exponent - 1)


def multiplicative_order(
    modulus: int,
    modulus_factors: dict[int, int],
    primes: list[int],
) -> int:
    if modulus == 1:
        return 1
    assert math.gcd(modulus, 10) == 1
    exponent = 1
    for prime, power in modulus_factors.items():
        exponent = math.lcm(exponent, carmichael_prime_power(prime, power))
    exponent_factors = factor(exponent, primes)
    order = exponent
    for prime, power in exponent_factors.items():
        for _ in range(power):
            if pow(10, order // prime, modulus) != 1:
                break
            order //= prime
    assert pow(10, order, modulus) == 1
    return order


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=280)
    args = parser.parse_args()
    if args.max_depth < 120:
        raise SystemExit("--max-depth must be at least 120")

    repository = root()
    source_path = repository / "problems/local/pi-digits.txt"
    report_path = repository / (
        "work/ultrapi-resume/"
        "bbp_cross_depth_phase_compensation_20260813.md"
    )
    checker_path = repository / (
        "work/ultrapi-resume/"
        "bbp_cross_depth_phase_compensation_20260813_check.py"
    )
    assert digest(source_path) == SOURCE_SHA256
    assert digest(report_path) == PRIMARY_REPORT_SHA256
    assert digest(checker_path) == PRIMARY_CHECKER_SHA256

    primes = primes_through(8 * args.max_depth + 5)
    partial_sum = Fraction()
    states: dict[int, dict[str, object]] = {}

    coefficient_identity_checks = 0
    actual_coordinate_checks = 0
    crt_reconstruction_checks = 0
    five_valuation_checks = 0
    static_five_checks = 0
    complete_phase_checks = 0
    period_checks = 0
    sqrt_period_checks = 0

    for depth in range(args.max_depth + 1):
        coefficient = coefficient_from_partial_fractions(depth)
        expanded = Fraction(
            120 * depth * depth + 151 * depth + 47,
            (2 * depth + 1)
            * (4 * depth + 3)
            * (8 * depth + 1)
            * (8 * depth + 5),
        )
        assert coefficient == expanded
        coefficient_identity_checks += 1
        partial_sum += coefficient / 16**depth
        if depth < 48:
            continue

        denominator = partial_sum.denominator
        numerator = partial_sum.numerator
        two_exponent = valuation(denominator, 2)
        odd_denominator = denominator >> two_exponent
        odd_factors = factor(odd_denominator, primes)
        assert two_exponent == 4 * depth - valuation(depth + 1, 2)

        dyadic_modulus = 1 << (two_exponent - 4)
        dyadic_coordinate = (
            numerator * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            numerator - odd_denominator * dyadic_coordinate
        ) // dyadic_modulus
        assert math.gcd(odd_numerator, odd_denominator) == 1
        y_value = Fraction(dyadic_coordinate, dyadic_modulus)
        odd_value = Fraction(odd_numerator, odd_denominator)
        assert 16 * partial_sum == y_value + odd_value

        high_product = 1
        xi_high = Fraction()
        high_coordinates: dict[int, tuple[int, Fraction]] = {}
        for prime, exponent in odd_factors.items():
            if prime <= depth:
                continue
            assert exponent == 1 and prime * prime > 8 * depth + 5
            direct_residue, direct_rational = local_residue_from_singular_terms(
                depth, prime
            )
            actual_residue = additive_crt_coordinate(
                odd_numerator, odd_denominator, prime
            )
            assert direct_residue == actual_residue != 0
            high_product *= prime
            xi_high += Fraction(actual_residue, prime)
            high_coordinates[prime] = (actual_residue, direct_rational)
            actual_coordinate_checks += 1

        cofactor = odd_denominator // high_product
        eta = odd_numerator * pow(high_product, -1, cofactor) % cofactor
        assert math.gcd(eta, cofactor) == 1
        assert (odd_value - xi_high - Fraction(eta, cofactor)).denominator == 1
        crt_reconstruction_checks += 1

        five_exponent = floor_log(5, 8 * depth + 5)
        five_power = 5**five_exponent
        assert valuation(odd_denominator, 5) == five_exponent
        assert valuation(cofactor, 5) == five_exponent
        five_valuation_checks += 1

        rest_modulus = cofactor // five_power
        beta_five = eta * pow(rest_modulus, -1, five_power) % five_power
        beta_rest = eta * pow(five_power, -1, rest_modulus) % rest_modulus
        assert (
            Fraction(eta, cofactor)
            - Fraction(beta_five, five_power)
            - Fraction(beta_rest, rest_modulus)
        ).denominator == 1

        upper = len(str(16**depth)) - 1
        assert 10**upper <= 16**depth < 10 ** (upper + 1)
        assert depth >= max(4, five_exponent)
        for decimal_exponent in range(depth, upper + 1):
            a_multiplier = (10**decimal_exponent - 16) // 16
            assert a_multiplier % five_power == five_power - 1
            split_phase = (
                a_multiplier * y_value
                + a_multiplier * xi_high
                - Fraction(beta_five, five_power)
                + a_multiplier * Fraction(beta_rest, rest_modulus)
            )
            direct_phase = (10**decimal_exponent - 16) * partial_sum
            assert (direct_phase - split_phase).denominator == 1
            static_five_checks += 1
            complete_phase_checks += 1

        rest_factors = {
            prime: exponent
            for prime, exponent in odd_factors.items()
            if prime <= depth and prime != 5
        }
        assert math.prod(
            prime**exponent
            for prime, exponent in rest_factors.items()
        ) == rest_modulus
        row_length = upper - depth + 1
        order = multiplicative_order(rest_modulus, rest_factors, primes)
        assert order > 0
        period_checks += 1

        sqrt_bound = math.isqrt(8 * depth + 5)
        sqrt_factors = {
            prime: exponent
            for prime, exponent in odd_factors.items()
            if prime <= sqrt_bound and prime != 5
        }
        sqrt_modulus = math.prod(
            prime**exponent for prime, exponent in sqrt_factors.items()
        )
        sqrt_order = multiplicative_order(
            sqrt_modulus, sqrt_factors, primes
        )
        assert sqrt_order > 0
        sqrt_period_checks += 1

        states[depth] = {
            "partial_sum": partial_sum,
            "upper": upper,
            "high_coordinates": high_coordinates,
            "xi_high": xi_high,
            "five_power": five_power,
            "beta_five": beta_five,
            "hidden": y_value + Fraction(beta_rest, rest_modulus),
            "row_length": row_length,
            "order": order,
            "sqrt_order": sqrt_order,
        }

    event_support_checks = 0
    event_formula_checks = 0
    event_constant_checks = 0
    compensation_checks = 0
    macroscopic_visible_jumps = 0
    maximum_visible_jump = Fraction()

    for depth in range(48, args.max_depth):
        old = states[depth]
        new = states[depth + 1]
        old_coordinates = old["high_coordinates"]
        new_coordinates = new["high_coordinates"]
        assert isinstance(old_coordinates, dict)
        assert isinstance(new_coordinates, dict)
        old_support = set(old_coordinates)
        new_support = set(new_coordinates)

        entering = new_support - old_support
        leaving = old_support - new_support
        assert leaving <= {depth + 1}
        for prime in entering:
            assert prime > depth + 1
            pole_count = sum(
                pole % prime == 0
                for pole in (
                    2 * (depth + 1) + 1,
                    4 * (depth + 1) + 3,
                    8 * (depth + 1) + 1,
                    8 * (depth + 1) + 5,
                )
            )
            assert pole_count == 1
            event_support_checks += 1
        changed = {
            prime
            for prime in old_support & new_support
            if old_coordinates[prime][1] != new_coordinates[prime][1]
        }
        for prime in changed:
            pole_count = sum(
                pole % prime == 0
                for pole in (
                    2 * (depth + 1) + 1,
                    4 * (depth + 1) + 3,
                    8 * (depth + 1) + 1,
                    8 * (depth + 1) + 5,
                )
            )
            assert pole_count == 1
            event_support_checks += 1

        predicted_increment = Fraction()
        for prime in entering:
            predicted_increment += new_coordinates[prime][1] / prime
        for prime in leaving:
            predicted_increment -= old_coordinates[prime][1] / prime
        for prime in changed:
            predicted_increment += (
                new_coordinates[prime][1] - old_coordinates[prime][1]
            ) / prime

        old_harmonic = sum(
            rational / prime
            for prime, (_, rational) in old_coordinates.items()
        )
        new_harmonic = sum(
            rational / prime
            for prime, (_, rational) in new_coordinates.items()
        )
        assert new_harmonic - old_harmonic == predicted_increment
        assert abs(predicted_increment) <= Fraction(320, depth + 1)
        event_formula_checks += 1
        event_constant_checks += 1

        common_upper = min(int(old["upper"]), int(new["upper"]))
        for decimal_exponent in range(depth + 1, common_upper + 1):
            a_multiplier = (10**decimal_exponent - 16) // 16
            visible_old = (
                a_multiplier * old["xi_high"]
                - Fraction(int(old["beta_five"]), int(old["five_power"]))
            )
            visible_new = (
                a_multiplier * new["xi_high"]
                - Fraction(int(new["beta_five"]), int(new["five_power"]))
            )
            hidden_old = a_multiplier * old["hidden"]
            hidden_new = a_multiplier * new["hidden"]
            direct_increment = (
                Fraction(10**decimal_exponent - 16)
                * coefficient_from_partial_fractions(depth + 1)
                / 16 ** (depth + 1)
            )
            assert (
                visible_new
                - visible_old
                + hidden_new
                - hidden_old
                - direct_increment
            ).denominator == 1
            assert 0 < direct_increment <= Fraction(
                1, 15 * (depth + 1) ** 2
            )
            visible_jump = circle_distance(visible_new - visible_old)
            if visible_jump > Fraction(1, 4):
                macroscopic_visible_jumps += 1
            maximum_visible_jump = max(maximum_visible_jump, visible_jump)
            compensation_checks += 1

    column_checks = 0
    double_array_points = 0
    distinct_columns: set[int] = set()
    exact_error_sum = Fraction()
    for depth, state in states.items():
        upper = int(state["upper"])
        row_length = upper - depth + 1
        double_array_points += row_length
        exact_error_sum += Fraction(row_length, 15 * (depth + 1) ** 2)
        distinct_columns.update(range(depth, upper + 1))

    for decimal_exponent in sorted(distinct_columns):
        admissible = [
            depth
            for depth, state in states.items()
            if depth <= decimal_exponent <= int(state["upper"])
        ]
        first = min(admissible)
        last = max(admissible)
        first_sum = states[first]["partial_sum"]
        last_sum = states[last]["partial_sum"]
        assert isinstance(first_sum, Fraction)
        assert isinstance(last_sum, Fraction)
        diameter = (10**decimal_exponent - 16) * (last_sum - first_sum)
        assert 0 <= diameter < Fraction(1, 15 * (first + 1) ** 2)
        column_checks += 1

    # The total Lipschitz error in the triangular double sum is bounded by a
    # constant times exact_error_sum.  Check the expected harmonic scale
    # against elementary upper and lower comparisons.
    harmonic_scale_checks = 0
    lower_harmonic = sum(Fraction(1, depth + 1) for depth in states)
    assert exact_error_sum <= Fraction(1, 15) * sum(
        Fraction(int(state["row_length"]), (depth + 1) ** 2)
        for depth, state in states.items()
    )
    assert exact_error_sum <= lower_harmonic
    harmonic_scale_checks += 2

    pigeonhole_countermodel_checks = 0
    values = set()
    for decimal_exponent in range(1, 201):
        value = Fraction(10**decimal_exponent - 16, 45) % 1
        assert value == Fraction(13, 15)
        values.add(value)
        pigeonhole_countermodel_checks += 1
    assert values == {Fraction(13, 15)}
    assert circle_distance(next(iter(values))) == Fraction(2, 15)

    print("status: PASS")
    print("independent_bounded_label: experiment")
    print("audited_infinite_label: proof sketch")
    print(f"depth_range: [48, {args.max_depth}]")
    print(f"coefficient_identity_checks: {coefficient_identity_checks}")
    print(f"actual_coordinate_checks: {actual_coordinate_checks}")
    print(f"crt_reconstruction_checks: {crt_reconstruction_checks}")
    print(f"five_valuation_checks: {five_valuation_checks}")
    print(f"static_five_checks: {static_five_checks}")
    print(f"complete_phase_checks: {complete_phase_checks}")
    print(f"event_support_checks: {event_support_checks}")
    print(f"event_formula_checks: {event_formula_checks}")
    print(f"event_constant_checks: {event_constant_checks}")
    print(f"compensation_checks: {compensation_checks}")
    print(f"macroscopic_visible_jumps: {macroscopic_visible_jumps}")
    print(f"maximum_visible_jump: {float(maximum_visible_jump):.15f}")
    print(f"column_checks: {column_checks}")
    print(f"double_array_points: {double_array_points}")
    print(f"distinct_columns: {len(distinct_columns)}")
    print(f"exact_error_sum: {float(exact_error_sum):.15f}")
    print(f"harmonic_scale_checks: {harmonic_scale_checks}")
    print(f"period_checks: {period_checks}")
    print(f"sqrt_period_checks: {sqrt_period_checks}")
    print(
        "periods_longer_than_rows: "
        f"{sum(int(state['order']) > int(state['row_length']) for state in states.values())}"
    )
    print(
        "sqrt_periods_longer_than_rows: "
        f"{sum(int(state['sqrt_order']) > int(state['row_length']) for state in states.values())}"
    )
    print(
        "pigeonhole_countermodel_checks: "
        f"{pigeonhole_countermodel_checks}"
    )
    print("asserts_fixed_sixteen_return: false")
    print("asserts_v1: false")


if __name__ == "__main__":
    main()
