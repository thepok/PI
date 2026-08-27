#!/usr/bin/env python3
"""Exact replay for BBP cross-depth phase compensation.

All finite output has claim label ``experiment``.  The script checks exact
rational, modular, event-boundary, and period identities.  It proves neither
the fixed-sixteen return nor V1.
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
ACTUAL_QUOTIENT_SHA256 = (
    "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc"
)
ODD_COFACTOR_SHA256 = (
    "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3"
)
HIGH_PHASE_SHA256 = (
    "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        answer += 1
        integer //= prime
    return answer


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
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


def power_of_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def localization(depth: int, prime: int) -> Fraction:
    """The simple-pole rational G_(M,p), for p^2 > 8M+5."""
    assert prime > 5 and prime * prime > 8 * depth + 5
    answer = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            answer -= power_of_two(6 - multiplier) / multiplier
    character_two = 1 if prime % 8 in (1, 7) else -1
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            answer += Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            answer -= Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return answer


def residue_lift(value: Fraction, prime: int) -> tuple[int, int]:
    numerator = value.numerator
    denominator = value.denominator
    assert math.gcd(denominator, prime) == 1
    residue = numerator * pow(denominator, -1, prime) % prime
    kappa = (-numerator * pow(prime, -1, denominator)) % denominator
    assert (
        Fraction(residue, prime)
        - Fraction(kappa, denominator)
        - value / prime
    ).denominator == 1
    return residue, kappa


def new_pole_event(index: int, prime: int) -> Fraction:
    """The unique contribution activated at k=index for a large prime."""
    assert prime > 5
    events: list[Fraction] = []

    first = 2 * index + 1
    if first % prime == 0:
        multiplier = first // prime
        assert multiplier % 2 == 1
        events.append(Fraction(-8, multiplier * 4 ** (multiplier - 1)))

    second = 4 * index + 3
    if second % prime == 0:
        multiplier = second // prime
        assert multiplier % 2 == 1
        events.append(-power_of_two(6 - multiplier) / multiplier)

    third = 8 * index + 1
    character_two = 1 if prime % 8 in (1, 7) else -1
    if third % prime == 0:
        multiplier = third // prime
        assert multiplier % 2 == 1
        events.append(
            Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
        )

    fourth = 8 * index + 5
    if fourth % prime == 0:
        multiplier = fourth // prime
        assert multiplier % 2 == 1
        events.append(
            Fraction(
                -64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
        )

    # Pairwise resultants exclude two singular pole families for p>5.
    assert len(events) == 1
    return events[0]


def circle_distance_numerator(residue: int, modulus: int) -> int:
    residue %= modulus
    return min(residue, modulus - residue)


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def merge_factor_max(
    target: dict[int, int], source: dict[int, int]
) -> None:
    for prime, exponent in source.items():
        target[prime] = max(target.get(prime, 0), exponent)


def multiplicative_order_from_factorization(
    modulus: int,
    modulus_factors: dict[int, int],
    primes: list[int],
) -> int:
    assert math.gcd(modulus, 10) == 1
    if modulus == 1:
        return 1
    carmichael_factors: dict[int, int] = {}
    for prime, exponent in modulus_factors.items():
        assert prime % 2 == 1 and prime != 5
        local_factors = factor(prime - 1, primes)
        if exponent > 1:
            local_factors[prime] = local_factors.get(prime, 0) + exponent - 1
        merge_factor_max(carmichael_factors, local_factors)
    order = math.prod(
        prime**exponent for prime, exponent in carmichael_factors.items()
    )
    for prime in sorted(carmichael_factors):
        for _ in range(carmichael_factors[prime]):
            if order % prime or pow(10, order // prime, modulus) != 1:
                break
            order //= prime
    assert pow(10, order, modulus) == 1
    return order


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=360)
    args = parser.parse_args()
    if args.max_depth < 120:
        raise SystemExit("--max-depth must be at least 120")

    repository = root()
    pinned = {
        repository / "problems/local/pi-digits.txt": SOURCE_SHA256,
        repository
        / "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md": (
            ACTUAL_QUOTIENT_SHA256
        ),
        repository
        / "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md": (
            ODD_COFACTOR_SHA256
        ),
        repository
        / "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md": (
            HIGH_PHASE_SHA256
        ),
    }
    for path, expected in pinned.items():
        assert sha256(path) == expected, path

    primes = primes_through(8 * args.max_depth + 5)
    prime_set = set(primes)
    partial_sum = Fraction()
    states: dict[int, dict[str, object]] = {}

    actual_coordinate_checks = 0
    high_lift_checks = 0
    five_static_checks = 0
    full_phase_decomposition_checks = 0
    period_checks = 0
    periods_longer_than_row = 0
    minimum_log_order_over_log_modulus = 1.0
    maximum_log_order_over_log_modulus = 0.0
    sqrt_period_checks = 0
    sqrt_periods_longer_than_row = 0
    sqrt_minimum_log_order_over_log_modulus = 1.0
    sqrt_maximum_log_order_over_log_modulus = 0.0

    for depth in range(args.max_depth + 1):
        partial_sum += coefficient(depth) / 16**depth
        if depth < 48:
            continue

        numerator = partial_sum.numerator
        denominator = partial_sum.denominator
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
        harmonic_lift = Fraction()
        grid_modulus = 105
        grid_terms: list[tuple[int, int]] = []
        for prime, exponent in odd_factors.items():
            if prime <= depth:
                continue
            assert exponent == 1
            local = localization(depth, prime)
            residue, kappa = residue_lift(local, prime)
            assert residue
            actual = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            assert actual == residue
            actual_coordinate_checks += 1
            high_product *= prime
            xi_high += Fraction(residue, prime)
            harmonic_lift += local / prime
            assert grid_modulus % local.denominator == 0
            grid_terms.append((kappa, local.denominator))

        grid_numerator = sum(
            kappa * (grid_modulus // local_denominator)
            for kappa, local_denominator in grid_terms
        ) % grid_modulus
        assert (
            xi_high
            - harmonic_lift
            - Fraction(grid_numerator, grid_modulus)
        ).denominator == 1
        high_lift_checks += 1

        cofactor = odd_denominator // high_product
        assert math.gcd(high_product, cofactor) == 1
        eta = odd_numerator * pow(high_product, -1, cofactor) % cofactor
        assert math.gcd(eta, cofactor) == 1
        assert (odd_value - xi_high - Fraction(eta, cofactor)).denominator == 1

        five_exponent = floor_log(5, 8 * depth + 5)
        five_power = 5**five_exponent
        assert odd_factors[5] == five_exponent
        assert cofactor % five_power == 0
        rest_modulus = cofactor // five_power
        assert math.gcd(five_power, rest_modulus) == 1
        beta_five = eta * pow(rest_modulus, -1, five_power) % five_power
        beta_rest = eta * pow(five_power, -1, rest_modulus) % rest_modulus
        assert (
            Fraction(eta, cofactor)
            - Fraction(beta_five, five_power)
            - Fraction(beta_rest, rest_modulus)
        ).denominator == 1

        upper = len(str(16**depth)) - 1
        assert 10**upper <= 16**depth < 10 ** (upper + 1)
        for exponent in range(depth, upper + 1):
            a_multiplier = (10**exponent - 16) // 16
            assert a_multiplier % five_power == five_power - 1
            lhs = a_multiplier * odd_value
            rhs = (
                a_multiplier * xi_high
                - Fraction(beta_five, five_power)
                + a_multiplier * Fraction(beta_rest, rest_modulus)
            )
            assert (lhs - rhs).denominator == 1
            full = Fraction((10**exponent - 16)) * partial_sum
            decomposed = a_multiplier * y_value + rhs
            assert (full - decomposed).denominator == 1
            five_static_checks += 1
            full_phase_decomposition_checks += 1

        rest_factors = dict(odd_factors)
        rest_factors[5] -= five_exponent
        if rest_factors[5] == 0:
            del rest_factors[5]
        for prime in list(rest_factors):
            if prime > depth:
                del rest_factors[prime]
        assert math.prod(
            prime**exponent for prime, exponent in rest_factors.items()
        ) == rest_modulus
        order = multiplicative_order_from_factorization(
            rest_modulus, rest_factors, primes
        )
        period_checks += 1
        row_length = upper - depth + 1
        if order > row_length:
            periods_longer_than_row += 1
        if rest_modulus > 1:
            ratio = math.log(order) / math.log(rest_modulus)
            minimum_log_order_over_log_modulus = min(
                minimum_log_order_over_log_modulus, ratio
            )
            maximum_log_order_over_log_modulus = max(
                maximum_log_order_over_log_modulus, ratio
            )

        sqrt_bound = math.isqrt(8 * depth + 5)
        sqrt_rest_factors = {
            prime: exponent
            for prime, exponent in odd_factors.items()
            if prime <= sqrt_bound and prime != 5
        }
        sqrt_rest_modulus = math.prod(
            prime**exponent
            for prime, exponent in sqrt_rest_factors.items()
        )
        sqrt_order = multiplicative_order_from_factorization(
            sqrt_rest_modulus, sqrt_rest_factors, primes
        )
        sqrt_period_checks += 1
        if sqrt_order > row_length:
            sqrt_periods_longer_than_row += 1
        if sqrt_rest_modulus > 1:
            sqrt_ratio = math.log(sqrt_order) / math.log(sqrt_rest_modulus)
            sqrt_minimum_log_order_over_log_modulus = min(
                sqrt_minimum_log_order_over_log_modulus, sqrt_ratio
            )
            sqrt_maximum_log_order_over_log_modulus = max(
                sqrt_maximum_log_order_over_log_modulus, sqrt_ratio
            )

        states[depth] = {
            "partial_sum": partial_sum,
            "odd_value": odd_value,
            "y_value": y_value,
            "xi_high": xi_high,
            "harmonic_lift": harmonic_lift,
            "grid_numerator": grid_numerator,
            "grid_modulus": grid_modulus,
            "beta_five": beta_five,
            "five_power": five_power,
            "beta_rest": beta_rest,
            "rest_modulus": rest_modulus,
            "upper": upper,
            "order": order,
        }

    boundary_event_checks = 0
    boundary_prime_removal_checks = 0
    positive_harmonic_increments = 0
    negative_harmonic_increments = 0
    zero_harmonic_increments = 0
    nonzero_grid_jumps = 0
    maximum_scaled_harmonic_increment = Fraction()
    adjacent_phase_telescope_checks = 0
    maximum_scaled_adjacent_phase_increment = Fraction()
    high_five_compensation_checks = 0
    macroscopic_high_five_jumps = 0
    maximum_high_five_jump = Fraction()

    for depth in range(48, args.max_depth):
        old = states[depth]
        new = states[depth + 1]
        old_harmonic = old["harmonic_lift"]
        new_harmonic = new["harmonic_lift"]
        assert isinstance(old_harmonic, Fraction)
        assert isinstance(new_harmonic, Fraction)

        new_index = depth + 1
        entering_primes: set[int] = set()
        for pole in (
            2 * new_index + 1,
            4 * new_index + 3,
            8 * new_index + 1,
            8 * new_index + 5,
        ):
            for prime in primes:
                if prime * prime > pole:
                    break
                if pole % prime == 0:
                    if prime > new_index:
                        entering_primes.add(prime)
                    quotient = pole // prime
                    if quotient > new_index and quotient in prime_set:
                        entering_primes.add(quotient)
            if pole in prime_set and pole > new_index:
                entering_primes.add(pole)

        event_difference = Fraction()
        for prime in entering_primes:
            assert prime > new_index
            event = new_pole_event(new_index, prime)
            assert (
                localization(new_index, prime)
                - localization(depth, prime)
                == event
            )
            event_difference += event / prime
            boundary_event_checks += 1

        boundary_prime = depth + 1
        if boundary_prime in prime_set:
            old_local = localization(depth, boundary_prime)
            old_residue, _ = residue_lift(old_local, boundary_prime)
            if old_residue:
                event_difference -= old_local / boundary_prime
                boundary_prime_removal_checks += 1

        harmonic_increment = new_harmonic - old_harmonic
        assert harmonic_increment == event_difference
        if harmonic_increment > 0:
            positive_harmonic_increments += 1
        elif harmonic_increment < 0:
            negative_harmonic_increments += 1
        else:
            zero_harmonic_increments += 1
        maximum_scaled_harmonic_increment = max(
            maximum_scaled_harmonic_increment,
            abs(harmonic_increment) * (depth + 1),
        )
        assert abs(harmonic_increment) <= Fraction(320, depth + 1)

        old_grid = Fraction(
            int(old["grid_numerator"]), int(old["grid_modulus"])
        )
        new_grid = Fraction(
            int(new["grid_numerator"]), int(new["grid_modulus"])
        )
        if (new_grid - old_grid).denominator != 1:
            nonzero_grid_jumps += 1

        common_upper = min(int(old["upper"]), int(new["upper"]))
        for exponent in range(depth + 1, common_upper + 1):
            old_sum = old["partial_sum"]
            new_sum = new["partial_sum"]
            assert isinstance(old_sum, Fraction)
            assert isinstance(new_sum, Fraction)
            phase_increment = (10**exponent - 16) * (new_sum - old_sum)
            exact_increment = (
                Fraction(10**exponent - 16)
                * coefficient(depth + 1)
                / 16 ** (depth + 1)
            )
            assert phase_increment == exact_increment
            assert 0 < phase_increment <= Fraction(1, 15 * (depth + 1) ** 2)
            maximum_scaled_adjacent_phase_increment = max(
                maximum_scaled_adjacent_phase_increment,
                phase_increment * 15 * (depth + 1) ** 2,
            )
            a_multiplier = (10**exponent - 16) // 16
            old_visible = (
                a_multiplier * old["xi_high"]
                - Fraction(int(old["beta_five"]), int(old["five_power"]))
            )
            new_visible = (
                a_multiplier * new["xi_high"]
                - Fraction(int(new["beta_five"]), int(new["five_power"]))
            )
            old_hidden = a_multiplier * (
                old["y_value"]
                + Fraction(int(old["beta_rest"]), int(old["rest_modulus"]))
            )
            new_hidden = a_multiplier * (
                new["y_value"]
                + Fraction(int(new["beta_rest"]), int(new["rest_modulus"]))
            )
            visible_jump = circle_distance(new_visible - old_visible)
            assert (
                (new_visible - old_visible)
                + (new_hidden - old_hidden)
                - phase_increment
            ).denominator == 1
            maximum_high_five_jump = max(
                maximum_high_five_jump, visible_jump
            )
            if visible_jump > Fraction(1, 4):
                macroscopic_high_five_jumps += 1
            high_five_compensation_checks += 1
            adjacent_phase_telescope_checks += 1

    column_telescope_checks = 0
    maximum_scaled_column_diameter = Fraction()
    weight_counts: dict[int, int] = {}
    total_row_points = 0
    transfer_error_ledger = Fraction()
    for depth, state in states.items():
        upper = int(state["upper"])
        row_length = upper - depth + 1
        total_row_points += row_length
        transfer_error_ledger += Fraction(
            row_length, 15 * (depth + 1) ** 2
        )
        for exponent in range(depth, upper + 1):
            weight_counts[exponent] = weight_counts.get(exponent, 0) + 1

    assert sum(weight_counts.values()) == total_row_points
    for exponent, weight in weight_counts.items():
        admissible_depths = [
            depth
            for depth, state in states.items()
            if depth <= exponent <= int(state["upper"])
        ]
        assert len(admissible_depths) == weight
        first_depth = min(admissible_depths)
        last_depth = max(admissible_depths)
        first_sum = states[first_depth]["partial_sum"]
        last_sum = states[last_depth]["partial_sum"]
        assert isinstance(first_sum, Fraction)
        assert isinstance(last_sum, Fraction)
        diameter = (10**exponent - 16) * (last_sum - first_sum)
        assert 0 <= diameter <= Fraction(1, 15 * (first_depth + 1) ** 2)
        maximum_scaled_column_diameter = max(
            maximum_scaled_column_diameter,
            diameter * 15 * (first_depth + 1) ** 2,
        )
        column_telescope_checks += 1

    pair_gap_checks = 0
    rows_pair_gap_strictly_smaller_than_zero_gap = 0
    largest_zero_to_pair_gap_ratio = 0.0
    strongest_pair_gap_example: tuple[int, int, int, int] | None = None
    pair_gap_hasher = hashlib.sha256()
    for depth, state in states.items():
        partial = state["partial_sum"]
        assert isinstance(partial, Fraction)
        modulus = partial.denominator
        upper = int(state["upper"])
        residues = sorted(
            ((pow(10, exponent, modulus) - 16) * partial.numerator) % modulus
            for exponent in range(depth, upper + 1)
        )
        zero_gap = min(
            circle_distance_numerator(residue, modulus) for residue in residues
        )
        cyclic_gaps = [
            residues[index + 1] - residues[index]
            for index in range(len(residues) - 1)
        ]
        cyclic_gaps.append(modulus + residues[0] - residues[-1])
        pair_gap = min(cyclic_gaps)
        assert zero_gap > 0 and pair_gap > 0
        if pair_gap < zero_gap:
            rows_pair_gap_strictly_smaller_than_zero_gap += 1
        ratio = zero_gap / pair_gap
        pair_gap_hasher.update(
            f"{depth}|{zero_gap}|{pair_gap}|{modulus}\n".encode()
        )
        if ratio > largest_zero_to_pair_gap_ratio:
            largest_zero_to_pair_gap_ratio = ratio
            strongest_pair_gap_example = (
                depth,
                zero_gap.bit_length(),
                pair_gap.bit_length(),
                modulus.bit_length(),
            )
        pair_gap_checks += 1

    assert transfer_error_ledger < 1
    assert strongest_pair_gap_example is not None

    # Exact countermodel to the inference "a close pair forces the target
    # zero": for x=1/45, every fixed-return phase with n>=1 is 13/15 mod 1.
    # Thus all pair gaps vanish while the zero gap stays 2/15.  The modulus
    # includes a 5-primary part and the base-ten orbit is already periodic.
    pigeonhole_countermodel_checks = 0
    countermodel_phases = []
    for exponent in range(1, 101):
        phase = Fraction(10**exponent - 16, 45) % 1
        assert phase == Fraction(13, 15)
        countermodel_phases.append(phase)
        pigeonhole_countermodel_checks += 1
    assert len(set(countermodel_phases)) == 1
    assert circle_distance(countermodel_phases[0]) == Fraction(2, 15)

    print("status: PASS")
    print("bounded_claim_label: experiment")
    print("cross_depth_identities_label: proof sketch")
    print(f"depth_range: [48, {args.max_depth}]")
    print(f"actual_high_coordinate_checks: {actual_coordinate_checks}")
    print(f"high_grid_lift_checks: {high_lift_checks}")
    print(f"five_static_phase_checks: {five_static_checks}")
    print(
        "full_phase_decomposition_checks: "
        f"{full_phase_decomposition_checks}"
    )
    print(f"boundary_event_checks: {boundary_event_checks}")
    print(
        "boundary_prime_removal_checks: "
        f"{boundary_prime_removal_checks}"
    )
    print(
        "harmonic_increment_sign_counts: "
        f"positive={positive_harmonic_increments},"
        f"negative={negative_harmonic_increments},"
        f"zero={zero_harmonic_increments}"
    )
    print(f"nonzero_grid_jumps: {nonzero_grid_jumps}")
    print(
        "maximum_depth_scaled_harmonic_increment: "
        f"{float(maximum_scaled_harmonic_increment):.15f}"
    )
    print(
        "adjacent_phase_telescope_checks: "
        f"{adjacent_phase_telescope_checks}"
    )
    print(
        "high_five_compensation_checks: "
        f"{high_five_compensation_checks}"
    )
    print(f"macroscopic_high_five_jumps: {macroscopic_high_five_jumps}")
    print(
        "maximum_high_five_jump: "
        f"{float(maximum_high_five_jump):.15f}"
    )
    print(f"column_telescope_checks: {column_telescope_checks}")
    print(
        "maximum_normalized_adjacent_phase_increment: "
        f"{float(maximum_scaled_adjacent_phase_increment):.15f}"
    )
    print(
        "maximum_normalized_column_diameter: "
        f"{float(maximum_scaled_column_diameter):.15f}"
    )
    print(f"period_checks: {period_checks}")
    print(f"periods_longer_than_row: {periods_longer_than_row}")
    print(
        "log_order_over_log_modulus_range: "
        f"[{minimum_log_order_over_log_modulus:.15f},"
        f" {maximum_log_order_over_log_modulus:.15f}]"
    )
    print(f"sqrt_period_checks: {sqrt_period_checks}")
    print(
        "sqrt_periods_longer_than_row: "
        f"{sqrt_periods_longer_than_row}"
    )
    print(
        "sqrt_log_order_over_log_modulus_range: "
        f"[{sqrt_minimum_log_order_over_log_modulus:.15f},"
        f" {sqrt_maximum_log_order_over_log_modulus:.15f}]"
    )
    print(f"total_double_array_points: {total_row_points}")
    print(f"distinct_exponent_columns: {len(weight_counts)}")
    print(
        "transfer_error_ledger_upper_bound: "
        f"{float(transfer_error_ledger):.15f}"
    )
    print(f"pair_gap_checks: {pair_gap_checks}")
    print(
        "rows_pair_gap_strictly_smaller_than_zero_gap: "
        f"{rows_pair_gap_strictly_smaller_than_zero_gap}"
    )
    print(
        "largest_zero_to_pair_gap_ratio: "
        f"{largest_zero_to_pair_gap_ratio:.15f}"
    )
    print(f"strongest_pair_gap_example: {strongest_pair_gap_example}")
    print(f"pair_gap_record_sha256: {pair_gap_hasher.hexdigest()}")
    print(
        "pigeonhole_countermodel_checks: "
        f"{pigeonhole_countermodel_checks}"
    )
    print("asserts_fixed_sixteen_return: false")
    print("asserts_v1: false")


if __name__ == "__main__":
    main()
