#!/usr/bin/env python3
"""Exact replay for the BBP three-primary epoch calculation.

All bounded output has claim status ``experiment``.  The proof formulas that
the experiment replays are recorded in the companion report.  Arithmetic is
exact: ``Fraction`` is used for BBP partial sums, and modular calculations use
integers only.  This script neither evaluates pi nor proves V1.
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
PARENT_REPORT_SHA256 = (
    "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3"
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


def partial_fraction_coefficient(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(1, 2 * (2 * index + 1))
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 2 * (4 * index + 3))
    )


def valuation(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("valuation at zero is not used")
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def rational_valuation(value: Fraction, prime: int) -> int:
    return valuation(value.numerator, prime) - valuation(value.denominator, prime)


def rat_mod(value: Fraction, modulus: int) -> int:
    if modulus == 1:
        return 0
    if math.gcd(value.denominator, modulus) != 1:
        raise AssertionError(("nonunit rational denominator", value, modulus))
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def predicted_epoch(depth: int) -> tuple[int, int, int, str]:
    """Return (denominator exponent, leading unit, ambient e, stage)."""
    exponent = 1
    while True:
        power = 3**exponent
        if exponent & 1:
            start = (power - 3) // 4
            stop = (3 ** (exponent + 1) - 1) // 8
            if start <= depth < stop:
                return exponent, 1, exponent, "odd"
        else:
            start = (power - 1) // 8
            second = (power - 1) // 2
            cancellation = 5 * (power - 1) // 8
            stop = 3 * (power - 1) // 4
            if start <= depth < stop:
                if depth < second:
                    return exponent, 1, exponent, "even-first"
                if depth < cancellation:
                    return exponent, 2, exponent, "even-second"
                return exponent - 1, 2, exponent, "even-drop"
        exponent += 1


def pole_quotients(depth: int, exponent: int) -> tuple[tuple[int, ...], ...]:
    """List q with a pole linear form equal to q*3^exponent."""
    power = 3**exponent
    forms = (
        lambda index: 8 * index + 1,
        lambda index: 2 * index + 1,
        lambda index: 8 * index + 5,
        lambda index: 4 * index + 3,
    )
    answer: list[tuple[int, ...]] = []
    for form in forms:
        quotients = []
        for index in range(depth + 1):
            denominator = form(index)
            if valuation(denominator, 3) == exponent:
                quotients.append(denominator // power)
        answer.append(tuple(quotients))
    return tuple(answer)


def quotient_mod(exponent: int, modulus: int) -> int:
    """Return (10^exponent-16)/3 modulo ``modulus`` without huge powers."""
    if modulus == 1:
        return 0
    lifted_modulus = 3 * modulus
    numerator = (pow(10, exponent, lifted_modulus) - 16) % lifted_modulus
    if numerator % 3:
        raise AssertionError(("division by three", exponent, modulus, numerator))
    return numerator // 3


def exact_upper_from_power(power_of_sixteen: int) -> int:
    """Return floor(log_10(power_of_sixteen)) using only exact integers."""
    # Kept as a standalone cross-check; the main loop uses an incremental
    # decimal threshold to avoid repeated string conversions.
    return len(str(power_of_sixteen)) - 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=5000)
    args = parser.parse_args()
    if args.max_depth < 1000:
        raise SystemExit("--max-depth must be at least 1000")

    # Python 3.11 protects decimal conversions of large integers by default.
    # The largest default conversion here has only about 6021 digits.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    source_path = root() / "problems/local/pi-digits.txt"
    parent_path = (
        root()
        / "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md"
    )
    source_digest = sha256(source_path)
    parent_digest = sha256(parent_path)
    assert source_digest == SOURCE_SHA256
    assert parent_digest == PARENT_REPORT_SHA256

    partial_sum = Fraction()
    power_of_sixteen = 1
    decimal_threshold = 1
    upper = 0

    epoch_checks = 0
    partial_fraction_checks = 0
    row_window_checks = 0
    direct_phase_checks = 0
    boundary_checks = 0
    full_grid_rows = 0
    nontrivial_odd_rows = 0
    nontrivial_odd_full_grid_rows = 0
    sufficient_even_rows = 0
    max_primary_exponent = 0
    symbolic_epoch_structure_checks = 0
    transitions: list[tuple[int, int, int, str]] = []
    previous_state: tuple[int, int] | None = None
    phase_samples: dict[int, tuple[Fraction, int, int]] = {}

    for depth in range(args.max_depth + 1):
        if depth:
            power_of_sixteen *= 16
            while power_of_sixteen >= 10 * decimal_threshold:
                decimal_threshold *= 10
                upper += 1
        if depth in (0, 1, 10, 100, 1000, args.max_depth):
            assert upper == exact_upper_from_power(power_of_sixteen)

        coefficient_value = coefficient(depth)
        if coefficient_value != partial_fraction_coefficient(depth):
            raise AssertionError(("partial-fraction identity", depth))
        partial_fraction_checks += 1
        partial_sum += coefficient_value / power_of_sixteen
        expected_exponent, expected_unit, ambient, stage = predicted_epoch(depth)
        actual_exponent = -rational_valuation(partial_sum, 3)
        if actual_exponent != expected_exponent:
            raise AssertionError(
                ("three-primary exponent", depth, actual_exponent, expected_exponent)
            )
        scaled_unit = (3**actual_exponent) * partial_sum
        actual_unit = rat_mod(scaled_unit, 3)
        if actual_unit != expected_unit:
            raise AssertionError(
                ("leading unit", depth, actual_unit, expected_unit)
            )
        epoch_checks += 1
        max_primary_exponent = max(max_primary_exponent, actual_exponent)

        state = (actual_exponent, actual_unit)
        if state != previous_state:
            transitions.append((depth, actual_exponent, actual_unit, stage))
            previous_state = state
            phase_samples[depth] = (partial_sum, actual_exponent, upper)

        period = 1 if actual_exponent <= 2 else 3 ** (actual_exponent - 2)
        row_length = upper - depth + 1
        if row_length < 1:
            raise AssertionError(("empty proportional row", depth, upper))
        is_full = row_length >= period
        full_grid_rows += int(is_full)
        row_window_checks += 1

        if stage == "odd" and actual_exponent >= 3:
            nontrivial_odd_rows += 1
            nontrivial_odd_full_grid_rows += int(is_full)
            if is_full:
                raise AssertionError(("odd epoch unexpectedly covers period", depth))

        if stage == "even-drop":
            # The e=2 drop has the trivial denominator 3^(E-1)=1.  For e>=4,
            # M >= 5(T-1) is the elementary sufficient full-cycle condition.
            if ambient >= 4:
                if depth < 5 * (period - 1) or not is_full:
                    raise AssertionError(("even drop window", depth, period))
                sufficient_even_rows += 1

        # Save all structural endpoints for a direct rational phase replay.
        power = 3**ambient
        endpoints = (
            (power - 3) // 4 if ambient & 1 else (power - 1) // 8,
        )
        if not ambient & 1:
            endpoints += (
                (power - 1) // 2,
                5 * (power - 1) // 8,
                3 * (power - 1) // 4 - 1,
            )
        if depth in endpoints:
            phase_samples[depth] = (partial_sum, actual_exponent, upper)

    # Symbolically replay the all-depth endpoint structure well beyond the
    # Fraction cutoff.  This is still a bounded experiment, not a proof.
    previous_stop = 0
    for exponent in range(1, 41):
        power = 3**exponent
        if exponent & 1:
            start = (power - 3) // 4
            stop = (3 * power - 1) // 8
            first_exact = (
                (11 * power - 1) // 8,
                (power - 1) // 2,
                (7 * power - 5) // 8,
                start,
            )
            forms = (
                8 * first_exact[0] + 1,
                2 * first_exact[1] + 1,
                8 * first_exact[2] + 5,
                4 * first_exact[3] + 3,
            )
            if forms != (11 * power, power, 7 * power, power):
                raise AssertionError(("odd first exact poles", exponent, forms))
            if start != previous_stop or not start < stop:
                raise AssertionError(("odd interval partition", exponent))
            if 8 * stop + 1 != 3 ** (exponent + 1):
                raise AssertionError(("odd next record", exponent))
            if any(index < stop for index in first_exact[:3]):
                raise AssertionError(("odd competing pole", exponent, first_exact))
            previous_stop = stop
        else:
            start = (power - 1) // 8
            second = (power - 1) // 2
            cancellation = 5 * (power - 1) // 8
            stop = 3 * (power - 1) // 4
            fourth_exact = (7 * power - 3) // 4
            if start != previous_stop:
                raise AssertionError(("even interval partition", exponent))
            if (second, cancellation, stop) != (4 * start, 5 * start, 6 * start):
                raise AssertionError(("even A/4A/5A/6A", exponent))
            if (
                8 * start + 1 != power
                or 2 * second + 1 != power
                or 8 * cancellation + 5 != 5 * power
                or 4 * stop + 3 != 3 * power
                or 4 * fourth_exact + 3 != 7 * power
            ):
                raise AssertionError(("even pole identities", exponent))
            if not start < second < cancellation < stop < fourth_exact:
                raise AssertionError(("even pole ordering", exponent))

            # This is the rational 1/2, 1/5 computation in Z_(3)/9Z_(3).
            alpha_mod_three = start % 3
            beta_mod_three = second % 3
            gamma_mod_three = cancellation % 3
            if (alpha_mod_three, beta_mod_three, gamma_mod_three) != (1, 1, 2):
                raise AssertionError(("even exponent classes", exponent))
            top_cluster_mod_nine = (
                4 * pow(16, -start, 9)
                - pow(2, -1, 9) * pow(16, -second, 9)
                - pow(5, -1, 9) * pow(16, -cancellation, 9)
            ) % 9
            if top_cluster_mod_nine != 0:
                raise AssertionError(("symbolic top cluster", exponent))
            previous_stop = stop
        symbolic_epoch_structure_checks += 1

    # Verify every complete even epoch whose cancellation boundary is visible.
    exponent = 2
    while True:
        power = 3**exponent
        first = (power - 1) // 8
        second = (power - 1) // 2
        cancellation = 5 * (power - 1) // 8
        next_odd = 3 * (power - 1) // 4
        if next_odd > args.max_depth:
            break
        assert first < second < cancellation < next_odd

        # At the three top-pole arrivals the modulo-three contributions are
        # 1, 1, 1.  At the third arrival their sum vanishes.
        top_contributions = (
            4 % 3,
            (-pow(2, -1, 3)) % 3,
            (-pow(5, -1, 3)) % 3,
        )
        assert top_contributions == (1, 1, 1)

        # The cancellation is two powers deep.  Since e is even, the three
        # exponents are 1,1,2 modulo 3 and 16 has order 3 modulo 9.
        top_cluster_mod_nine = (
            4 * pow(16, -first, 9)
            - pow(2, -1, 9) * pow(16, -second, 9)
            - pow(5, -1, 9) * pow(16, -cancellation, 9)
        ) % 9
        if top_cluster_mod_nine != 0:
            raise AssertionError(("top cluster modulo nine", exponent))

        expected_lower = ((11,), (1,), (7,), (1, 5))
        at_cancellation = pole_quotients(cancellation, exponent - 1)
        before_next = pole_quotients(next_odd - 1, exponent - 1)
        if at_cancellation != expected_lower or before_next != expected_lower:
            raise AssertionError(
                ("lower pole list", exponent, at_cancellation, before_next)
            )
        lower_residue = (
            pow(11, -1, 3)
            - pow(2 * 1, -1, 3)
            - pow(7, -1, 3)
            - pow(2 * 1, -1, 3)
            - pow(2 * 5, -1, 3)
        ) % 3
        if lower_residue != 2:
            raise AssertionError(("lower pole residue", exponent, lower_residue))

        # The final pre-drop row already traverses a full primary cycle.
        pre_drop_depth = cancellation - 1
        expected_e, _, _, _ = predicted_epoch(pre_drop_depth)
        pre_drop_period = 1 if expected_e <= 2 else 3 ** (expected_e - 2)
        if pre_drop_depth < 5 * (pre_drop_period - 1):
            raise AssertionError(("pre-drop sufficient condition", exponent))
        boundary_checks += 1
        exponent += 2

    # The exact g_n orbit.  LTE gives ord_(3^E)(10)=3^(E-2), and the
    # enumerated orbit must be precisely the coset 1 modulo 3.
    orbit_checks = 0
    for exponent in range(2, max_primary_exponent + 1):
        modulus = 3 ** (exponent - 1)
        period = 3 ** (exponent - 2)
        if pow(10, period, 3**exponent) != 1:
            raise AssertionError(("period upper bound", exponent))
        if period > 1 and pow(10, period // 3, 3**exponent) == 1:
            raise AssertionError(("period minimality", exponent))
        orbit = {quotient_mod(index, modulus) for index in range(1, period + 1)}
        expected_orbit = {residue for residue in range(modulus) if residue % 3 == 1}
        if orbit != expected_orbit:
            raise AssertionError(("quotient orbit", exponent))
        for index in range(1, min(period, 50) + 1):
            if quotient_mod(index + period, modulus) != quotient_mod(index, modulus):
                raise AssertionError(("quotient period", exponent, index))
        orbit_checks += 1

    # Replay the localized residual identity directly with Fraction arithmetic
    # at every structural transition/end point and at three exponents per row.
    for depth, (value, exponent, sample_upper) in sorted(phase_samples.items()):
        if exponent <= 1:
            continue
        modulus = 3 ** (exponent - 1)
        beta = rat_mod((3**exponent) * value, modulus)
        expected_coset = rat_mod((3**exponent) * value, 3)
        exponents = {max(1, depth), max(1, sample_upper), max(1, (depth + sample_upper) // 2)}
        for row_exponent in exponents:
            quotient = (10**row_exponent - 16) // 3
            expected = beta * (quotient % modulus) % modulus
            localized = Fraction(3 ** (exponent - 1)) * (
                10**row_exponent - 16
            ) * value
            actual = rat_mod(localized, modulus)
            if actual != expected or actual % 3 != expected_coset:
                raise AssertionError(
                    ("localized residual phase", depth, row_exponent, actual, expected)
                )
            direct_phase_checks += 1

    transition_text = ",".join(
        f"{depth}:E{exponent}/u{unit}/{stage}"
        for depth, exponent, unit, stage in transitions
    )
    print("claim_status=experiment")
    print(f"source_sha256={source_digest}")
    print(f"parent_report_sha256={parent_digest}")
    print(f"max_depth={args.max_depth}")
    print(f"partial_fraction_identity_checks={partial_fraction_checks}")
    print(f"exact_fraction_epoch_checks={epoch_checks}")
    print(f"symbolic_epoch_structure_checks={symbolic_epoch_structure_checks}")
    print(f"even_boundary_cluster_checks={boundary_checks}")
    print(f"primary_orbit_checks={orbit_checks}")
    print(f"direct_residual_phase_checks={direct_phase_checks}")
    print(f"exact_row_window_checks={row_window_checks}")
    print(f"full_grid_rows={full_grid_rows}")
    print(f"nontrivial_odd_epoch_rows={nontrivial_odd_rows}")
    print(f"nontrivial_odd_full_grid_rows={nontrivial_odd_full_grid_rows}")
    print(f"certified_even_drop_rows={sufficient_even_rows}")
    print(f"max_three_primary_exponent={max_primary_exponent}")
    print(f"observed_state_transitions={transition_text}")
    print("v1_status=not_proved")
    print("status=PASS")


if __name__ == "__main__":
    main()
