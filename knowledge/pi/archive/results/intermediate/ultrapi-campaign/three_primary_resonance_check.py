#!/usr/bin/env python3
"""Exact finite checks for the nested three-primary resonance analysis.

All finite output has claim status ``experiment``.  The script uses exact
``Fraction`` and integer arithmetic.  It neither evaluates pi nor reads a
table of pi digits.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd
from pathlib import Path

from actual_numerator_phase_experiment import machin_seed, valuation


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
RHO = Fraction(10, 625**3)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def fract(value: Fraction) -> Fraction:
    return value - (value.numerator // value.denominator)


def three_exponent(index: int) -> int:
    """The a with 3^a <= 12*index+3 < 3^(a+1)."""
    d = 12 * index + 3
    a = 0
    power = 1
    while 3 * power <= d:
        power *= 3
        a += 1
    assert power <= d < 3 * power
    return a


def expected_three_primary(index: int) -> int:
    return 3 ** (three_exponent(index) - 1)


def threshold_start(a: int) -> int:
    """First positive index with 3^a <= 12*j+3, for a >= 2."""
    assert a >= 2
    if a % 2:
        return (3**a - 3) // 12
    return (3**a + 3) // 12


def decimal_word(point: Fraction, length: int) -> str:
    value = (10**length * point.numerator) // point.denominator
    if not 0 <= value < 10**length:
        raise AssertionError(("decimal prefix range", point, length, value))
    return f"{value:0{length}d}"


def centered_grid(point: Fraction, modulus: int) -> set[Fraction]:
    return {fract(point + Fraction(t, modulus)) for t in range(modulus)}


def one_digit_counts(point: Fraction, modulus: int, length: int) -> dict[str, int]:
    words = [
        decimal_word(fract(point + Fraction(t, modulus)), length)
        for t in range(modulus)
    ]
    return {
        digit: sum(digit not in word for word in words)
        for digit in "0123456789"
    }


def multiplicative_order_ten(modulus: int) -> int:
    assert gcd(10, modulus) == 1
    value = 10 % modulus
    order = 1
    while value != 1:
        value = value * 10 % modulus
        order += 1
        if order > modulus:
            raise AssertionError(("order search", modulus))
    return order


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=80)
    args = parser.parse_args()
    if args.max_j < 3:
        raise SystemExit("--max-j must be at least three")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    seeds: list[Fraction | None] = [None]
    denominators: list[int] = [0]
    phases: list[Fraction] = [Fraction()]
    points: list[Fraction] = [Fraction()]
    exact_valuation_checks = 0
    exact_phase_checks = 0

    for j in range(1, args.max_j + 1):
        seed = machin_seed(j)
        seeds.append(seed)
        point = fract(seed)
        points.append(point)
        a = three_exponent(j)
        d_primary = expected_three_primary(j)
        if valuation(seed.denominator, 3) != a - 1:
            raise AssertionError(("three-primary denominator", j))
        if valuation(abs(seed.numerator), 3) != 0:
            raise AssertionError(("three-primary numerator", j))
        if d_primary != 3 ** valuation(seed.denominator, 3):
            raise AssertionError(("three-primary power", j))
        denominators.append(d_primary)
        exact_valuation_checks += 1

        factor = seed.denominator // d_primary
        if gcd(factor, d_primary) != 1:
            raise AssertionError(("coprime split", j))
        residue = seed.numerator % seed.denominator
        remainder = residue % factor
        phase = fract(d_primary * point)
        if phase != Fraction(remainder, factor):
            raise AssertionError(("phase reciprocity", j))
        phases.append(phase)
        exact_phase_checks += 1

    threshold_checks = 0
    order_checks = 0
    max_a = three_exponent(args.max_j)
    for a in range(2, max_a + 1):
        start = threshold_start(a)
        if start <= args.max_j:
            if three_exponent(start) != a:
                raise AssertionError(("threshold start", a, start))
            if start > 1 and three_exponent(start - 1) != a - 1:
                raise AssertionError(("threshold predecessor", a, start))
            threshold_checks += 1
        next_start = threshold_start(a + 1)
        expected_length = (
            (3 ** (a - 1) + 1) // 2
            if a % 2
            else (3 ** (a - 1) - 1) // 2
        )
        if next_start - start != expected_length:
            raise AssertionError(("plateau length", a))
        if a >= 3:
            modulus = 3 ** (a - 1)
            expected_order = modulus // 9
            if multiplicative_order_ten(modulus) != expected_order:
                raise AssertionError(("order of ten", a, modulus))
            order_checks += 1

    # A pulse of at most 2*J steps sees at most one tripling of D.
    pulse_threshold_checks = 0
    for start in range(1, args.max_j + 1):
        ratio = expected_three_primary(3 * start) // expected_three_primary(start)
        if ratio not in (1, 3):
            raise AssertionError(("two-J pulse threshold count", start, ratio))
        pulse_threshold_checks += 1

    transition_checks = 0
    frequency_checks = 0
    grid_map_checks = 0
    alias_partition_checks = 0
    threshold_alias_rows: list[tuple[int, int, int]] = []
    for j in range(1, args.max_j):
        seed = seeds[j]
        next_seed = seeds[j + 1]
        assert seed is not None and next_seed is not None
        d_primary = denominators[j]
        next_primary = denominators[j + 1]
        tau = next_primary // d_primary
        if tau not in (1, 3) or next_primary != tau * d_primary:
            raise AssertionError(("nested ratio", j, tau))
        forcing = next_seed - 10 * seed
        if forcing <= 0:
            raise AssertionError(("positive forcing", j))
        if points[j + 1] != fract(10 * points[j] + forcing):
            raise AssertionError(("circle recurrence", j))
        if phases[j + 1] != fract(
            10 * tau * phases[j] + next_primary * forcing
        ):
            raise AssertionError(("phase recurrence", j))
        transition_checks += 1
        for ell in range(-8, 9):
            left = fract(ell * phases[j + 1])
            right = fract(
                10 * tau * ell * phases[j]
                + ell * next_primary * forcing
            )
            if left != right:
                raise AssertionError(("frequency recurrence", j, ell))
            frequency_checks += 1

        image = {
            fract(10 * fract(points[j] + Fraction(t, d_primary)) + forcing)
            for t in range(d_primary)
        }
        next_grid = centered_grid(points[j + 1], next_primary)
        if tau == 1:
            if image != next_grid:
                raise AssertionError(("ordinary grid map", j))
        else:
            aliases = [
                {
                    fract(
                        points[j + 1]
                        + Fraction(u, d_primary)
                        + Fraction(alias, 3 * d_primary)
                    )
                    for u in range(d_primary)
                }
                for alias in range(3)
            ]
            if image != aliases[0]:
                raise AssertionError(("inherited threshold alias", j))
            if any(aliases[a] & aliases[b] for a in range(3) for b in range(a)):
                raise AssertionError(("alias disjointness", j))
            if set().union(*aliases) != next_grid:
                raise AssertionError(("alias partition", j))
            alias_partition_checks += 1
            threshold_alias_rows.append((j, d_primary, next_primary))
        grid_map_checks += len(image)

    # Exact T46-style telescopes and inherited alternative trajectories.
    telescope_checks = 0
    alternative_iterate_checks = 0
    for start in range(1, args.max_j + 1):
        max_steps = min(2 * start, args.max_j - start)
        seed = seeds[start]
        assert seed is not None
        for steps in range(max_steps + 1):
            later = seeds[start + steps]
            assert later is not None
            accumulation = later - 10**steps * seed
            if accumulation < 0:
                raise AssertionError(("nonnegative telescope", start, steps))
            if not accumulation < 10**steps * RHO**start:
                raise AssertionError(("geometric telescope", start, steps))
            telescope_checks += 1
            for t in {0, 1, denominators[start] - 1}:
                left = fract(
                    10**steps
                    * fract(points[start] + Fraction(t, denominators[start]))
                    + accumulation
                )
                right = fract(
                    points[start + steps]
                    + Fraction(10**steps * t, denominators[start])
                )
                if left != right:
                    raise AssertionError(("alternative iterate", start, steps, t))
                alternative_iterate_checks += 1

    # Falsify tempting pointwise occupancy recurrences on the actual seeds.
    occupancy: dict[tuple[int, str], int] = {}
    occupancy_membership_checks = 0
    for j in range(1, args.max_j + 1):
        counts = one_digit_counts(points[j], denominators[j], 2 * j)
        for digit, count in counts.items():
            occupancy[j, digit] = count
            occupancy_membership_checks += denominators[j]

    iid_contraction_violations = 0
    ordinary_positive_increases: list[tuple[int, str, int, int]] = []
    zero_resurrections: list[tuple[int, str, int, int]] = []
    for j in range(1, args.max_j):
        tau = denominators[j + 1] // denominators[j]
        for digit in "0123456789":
            before = occupancy[j, digit]
            after = occupancy[j + 1, digit]
            # Naive independent-digit heuristic for two additional digits:
            # N_{j+1} <= tau*(9/10)^2*N_j.  This is not assumed as a theorem.
            if 100 * after > 81 * tau * before:
                iid_contraction_violations += 1
            if tau == 1 and before > 0 and after > before:
                ordinary_positive_increases.append((j, digit, before, after))
            if before == 0 and after > 0:
                zero_resurrections.append((j, digit, before, after))

    # Structural separator: the same D schedule, a positive geometric
    # coboundary, and exact nested frequency closure can coexist with an
    # all-1 prefix of natural length at every scale.
    artificial_points: list[Fraction | None] = [None] * (args.max_j + 1)
    artificial_errors: list[Fraction | None] = [None] * (args.max_j + 1)
    artificial_denominator_checks = 0
    artificial_prefix_checks = 0
    artificial_subunit_survivals = 0
    for j in range(2, args.max_j + 1):
        d_primary = expected_three_primary(j)
        # The leading factor 2 prevents the D=9 numerator from acquiring an
        # extra factor 3 (10^k is 1 modulo 3).
        factor = 2 * 10 ** (9 * j)
        error = Fraction(1, d_primary * factor)
        point = Fraction(1, 9) - error
        artificial_errors[j] = error
        artificial_points[j] = point
        if point.denominator != d_primary * factor:
            raise AssertionError(("artificial reduced denominator", j))
        if 3 ** valuation(point.denominator, 3) != d_primary:
            raise AssertionError(("artificial three-primary part", j))
        if fract(d_primary * point) != Fraction(factor - 1, factor):
            raise AssertionError(("artificial resonant phase", j))
        if not error < RHO**j:
            raise AssertionError(("artificial geometric error", j))
        word = decimal_word(point, 2 * j)
        if word != "1" * (2 * j):
            raise AssertionError(("artificial all-one prefix", j, word))
        counts = one_digit_counts(point, d_primary, 2 * j)
        if counts["0"] < 1:
            raise AssertionError(("artificial zero avoidance", j))
        zero_mode = Fraction(d_primary * 9 ** (2 * j), 10 ** (2 * j))
        if zero_mode < 1:
            artificial_subunit_survivals += 1
        artificial_denominator_checks += 1
        artificial_prefix_checks += 1

    artificial_recurrence_checks = 0
    artificial_telescope_checks = 0
    for j in range(2, args.max_j):
        error = artificial_errors[j]
        next_error = artificial_errors[j + 1]
        point = artificial_points[j]
        next_point = artificial_points[j + 1]
        assert error is not None and next_error is not None
        assert point is not None and next_point is not None
        forcing = 10 * error - next_error
        if forcing <= 0:
            raise AssertionError(("artificial positive forcing", j))
        if next_point != fract(10 * point + forcing):
            raise AssertionError(("artificial circle recurrence", j))
        artificial_recurrence_checks += 1

        max_steps = min(2 * j, args.max_j - j)
        direct = Fraction()
        for steps in range(1, max_steps + 1):
            u = j + steps - 1
            error_u = artificial_errors[u]
            error_next = artificial_errors[u + 1]
            assert error_u is not None and error_next is not None
            forcing_u = 10 * error_u - error_next
            direct = 10 * direct + forcing_u
            terminal_error = artificial_errors[j + steps]
            assert terminal_error is not None
            closed = 10**steps * error - terminal_error
            if direct != closed:
                raise AssertionError(("artificial telescope identity", j, steps))
            if not 0 < direct < 10**steps * RHO**j:
                raise AssertionError(("artificial telescope bound", j, steps))
            artificial_telescope_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"j_range=1..{args.max_j}")
    print(f"exact_three_primary_valuation_checks={exact_valuation_checks}")
    print(f"exact_phase_reciprocity_checks={exact_phase_checks}")
    print(f"threshold_formula_checks={threshold_checks}")
    print(f"order_of_ten_checks={order_checks}")
    print(f"two_j_pulse_threshold_checks={pulse_threshold_checks}")
    print(f"cross_index_transition_checks={transition_checks}")
    print(f"cross_index_frequency_checks={frequency_checks}")
    print(f"grid_image_point_checks={grid_map_checks}")
    print(f"threshold_alias_partition_checks={alias_partition_checks}")
    print(f"threshold_alias_rows={threshold_alias_rows}")
    print(f"t46_style_telescope_checks={telescope_checks}")
    print(f"inherited_alternative_iterate_checks={alternative_iterate_checks}")
    print(
        "actual_seed_one_digit_avoidance_membership_checks="
        f"{occupancy_membership_checks}"
    )
    print(f"naive_iid_contraction_violations={iid_contraction_violations}")
    print(f"first_ordinary_positive_increases={ordinary_positive_increases[:5]}")
    print(f"first_zero_resurrections={zero_resurrections[:5]}")
    print(f"artificial_denominator_checks={artificial_denominator_checks}")
    print(f"artificial_all_one_prefix_checks={artificial_prefix_checks}")
    print(f"artificial_subunit_zero_mode_survivals={artificial_subunit_survivals}")
    print(f"artificial_recurrence_checks={artificial_recurrence_checks}")
    print(f"artificial_telescope_checks={artificial_telescope_checks}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
