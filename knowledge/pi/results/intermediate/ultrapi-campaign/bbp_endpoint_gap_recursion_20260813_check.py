#!/usr/bin/env python3
"""Exact finite audit of the proposed BBP endpoint-gap recursion.

Every bounded conclusion printed by this file has claim label ``experiment``.
The general algebraic implications recorded in the companion note have label
``proof sketch``.  This checker imports no other branch checker.

The purpose is falsification, not a numerical proof of distribution.  It
reconstructs the relevant BBP partial sums as exact ``Fraction`` objects,
checks the cross-epoch three-localized defect, and exhausts every pair of
consecutive complete-primary-period subwindows at the e=6 and e=8
transitions.  A separate elementary rational countermodel verifies that the
known primary nesting and adjacent-row closeness alone cannot force a small
full-phase gap.  The countermodel is explicitly not a BBP or pi model.
"""

from __future__ import annotations

import hashlib
import sys
from fractions import Fraction
from pathlib import Path
from typing import TypeAlias


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
DECIMATION_REPORT_SHA256 = (
    "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0"
)
DECIMATION_AUDIT_SHA256 = (
    "5dc190f913c1eb727e4a1cbc9bef2d8f3373af00b17e1aa50244ae8efceb3371"
)
FULL_PHASE_REPORT_SHA256 = (
    "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80"
)
FULL_PHASE_CHECKER_SHA256 = (
    "502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458"
)
TWISTED_REPORT_SHA256 = (
    "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12"
)
TWISTED_AUDIT_SHA256 = (
    "44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81"
)

Phase: TypeAlias = tuple[int, int]


def repository_root() -> Path:
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
    value = abs(integer)
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def exact_upper(depth: int) -> int:
    """Return floor(log_10(16**depth)) by exact integer conversion."""
    return len(str(1 << (4 * depth))) - 1


def endpoint_rows(ambient: int) -> tuple[tuple[int, str, int], ...]:
    a_value = (3**ambient - 1) // 8
    return (
        (5 * a_value - 1, "pre-drop", ambient),
        (5 * a_value, "first-drop", ambient - 1),
    )


def exact_partial_sums() -> tuple[dict[tuple[int, str], Fraction], int]:
    targets = {
        depth: (ambient, stage)
        for ambient in (4, 6, 8)
        for depth, stage, _ in endpoint_rows(ambient)
    }
    partial = Fraction()
    power_of_sixteen = 1
    answer: dict[tuple[int, str], Fraction] = {}
    partial_fraction_checks = 0
    for depth in range(max(targets) + 1):
        if depth:
            power_of_sixteen *= 16
        value = coefficient(depth)
        if value != partial_fraction_coefficient(depth):
            raise AssertionError(("partial fraction", depth))
        partial_fraction_checks += 1
        partial += value / power_of_sixteen
        if depth in targets:
            answer[targets[depth]] = partial
    return answer, partial_fraction_checks


def phase_residues(
    partial: Fraction, start: int, stop: int
) -> list[Phase]:
    """Exact phases {(10^n-16) partial}, inclusive in n."""
    modulus = partial.denominator
    numerator = partial.numerator
    residue = ((pow(10, start, modulus) - 16) * numerator) % modulus
    answer: list[Phase] = []
    for _ in range(start, stop + 1):
        # Keep the common unreduced denominator.  Cross-row Fraction
        # subtraction spends almost all of its time computing irrelevant
        # huge gcds; the raw pair supports faster exact integer comparison.
        answer.append((residue, modulus))
        residue = (10 * residue + 144 * numerator) % modulus
    direct = ((pow(10, stop, modulus) - 16) * numerator) % modulus
    if answer[-1] != (direct, modulus):
        raise AssertionError(("phase recurrence", start, stop))
    return answer


def circle_distance_parts(left: Phase, right: Phase) -> tuple[int, int]:
    left_numerator, left_denominator = left
    right_numerator, right_denominator = right
    denominator = left_denominator * right_denominator
    difference = abs(
        left_numerator * right_denominator
        - right_numerator * left_denominator
    )
    return min(difference, denominator - difference), denominator


def circle_distance_gt(
    left: Phase, right: Phase, threshold: Fraction
) -> bool:
    numerator, denominator = circle_distance_parts(left, right)
    return (
        numerator * threshold.denominator
        > threshold.numerator * denominator
    )


def largest_circular_gap(points: list[Phase]) -> Fraction:
    denominators = {denominator for _, denominator in points}
    if len(denominators) != 1:
        raise AssertionError("largest-gap row lacks a common denominator")
    denominator = next(iter(denominators))
    ordered = sorted(numerator for numerator, _ in points)
    gaps = [
        ordered[index + 1] - ordered[index]
        for index in range(len(ordered) - 1)
    ]
    gaps.append(denominator + ordered[0] - ordered[-1])
    return Fraction(max(gaps), denominator)


def endpoint_beta(partial: Fraction, exponent: int) -> int:
    actual = valuation(partial.denominator, 3)
    if actual != exponent:
        raise AssertionError(("endpoint exponent", actual, exponent))
    modulus = 3**exponent
    cofactor = partial.denominator // modulus
    return partial.numerator * pow(cofactor, -1, modulus) % modulus


def primary_phase_numerator(beta: int, exponent: int, n: int) -> int:
    modulus = 3 ** (exponent - 1)
    lifted_modulus = 3 * modulus
    lifted = (pow(10, n, lifted_modulus) - 16) % lifted_modulus
    if lifted % 3:
        raise AssertionError(("nonintegral primary quotient", n))
    return beta * (lifted // 3) % modulus


def exact_window_geometry() -> tuple[int, list[str]]:
    rows: dict[tuple[int, str], tuple[int, int, int]] = {}
    records: list[str] = []
    checks = 0
    for ambient in range(2, 16, 2):
        for depth, stage, _ in endpoint_rows(ambient):
            upper = exact_upper(depth)
            rows[ambient, stage] = (depth, upper, upper - depth + 1)
    for ambient in range(4, 16, 2):
        for stage, shift, low_c, high_c in (
            ("pre-drop", 13, 15, 24),
            ("first-drop", 5, 6, 15),
        ):
            depth, upper, length = rows[ambient, stage]
            old_depth, old_upper, old_length = rows[ambient - 2, stage]
            if depth != 9 * old_depth + shift:
                raise AssertionError(("lower endpoint fold", ambient, stage))
            c_value = upper - 9 * old_upper
            if not low_c <= c_value <= high_c:
                raise AssertionError(("upper endpoint fold", ambient, stage))
            delta = length - 9 * old_length
            if delta != c_value - shift - 8:
                raise AssertionError(("row length fold", ambient, stage))
            checks += 3
            records.append(
                f"e{ambient}/{stage}:shift={shift}:c={c_value}:delta={delta}"
            )
    return checks, records


def verify_transition(
    partials: dict[tuple[int, str], Fraction], ambient: int, stage: str
) -> dict[str, object]:
    old_ambient = ambient - 2
    old_depth, _, old_exponent = next(
        row for row in endpoint_rows(old_ambient) if row[1] == stage
    )
    new_depth, _, new_exponent = next(
        row for row in endpoint_rows(ambient) if row[1] == stage
    )
    old_upper = exact_upper(old_depth)
    new_upper = exact_upper(new_depth)
    old_partial = partials[old_ambient, stage]
    new_partial = partials[ambient, stage]

    localized = 9 * new_partial - old_partial
    if localized.denominator % 3 == 0:
        raise AssertionError(("cross-epoch defect is not 3-local", ambient, stage))

    old_beta = endpoint_beta(old_partial, old_exponent)
    new_beta = endpoint_beta(new_partial, new_exponent)
    if (new_beta - old_beta) % (3**old_exponent):
        raise AssertionError(("endpoint beta nesting", ambient, stage))

    old_period = 3 ** max(old_exponent - 2, 0)
    if new_exponent - old_exponent != 2:
        raise AssertionError(("non-ninefold transition", ambient, stage))

    old_points = phase_residues(old_partial, old_depth, old_upper)
    new_points = phase_residues(new_partial, new_depth, new_upper)
    old_same_exponent = phase_residues(old_partial, new_depth, new_upper)

    # The tempting exact-refinement recursion G_new <= G_old/9 already
    # fails at both signs and both transitions.  The weaker factor-three
    # inequality is merely recorded as finite evidence.
    old_gap = largest_circular_gap(old_points)
    new_gap = largest_circular_gap(new_points)
    if not new_gap > old_gap / 9:
        raise AssertionError(("unexpected ninefold gap inequality", ambient, stage))
    if not new_gap < old_gap / 3:
        raise AssertionError(("finite factor-three diagnostic", ambient, stage))

    maximum_fixed_parts = (0, 1)
    for new_point, old_point in zip(
        new_points, old_same_exponent, strict=True
    ):
        new_numerator, new_denominator = new_point
        parts = circle_distance_parts(
            ((9 * new_numerator) % new_denominator, new_denominator),
            old_point,
        )
        if parts[0] * maximum_fixed_parts[1] > (
            maximum_fixed_parts[0] * parts[1]
        ):
            maximum_fixed_parts = parts
    maximum_fixed_defect = Fraction(*maximum_fixed_parts)
    if maximum_fixed_defect <= Fraction(49, 100):
        raise AssertionError(("fixed-exponent complement unexpectedly small", ambient, stage))

    primary_inverse_checks = 0
    old_primary_modulus = 3 ** (old_exponent - 1)
    for offset, n in enumerate(range(new_depth, new_upper + 1)):
        rho = old_depth + ((n - old_depth) % old_period)
        if (
            pow(10, n, 3**old_exponent)
            - pow(10, rho, 3**old_exponent)
        ) % (3**old_exponent):
            raise AssertionError(("old primary period", ambient, stage, n, rho))
        new_numerator = primary_phase_numerator(new_beta, new_exponent, n)
        old_numerator = primary_phase_numerator(old_beta, old_exponent, rho)
        if new_numerator % old_primary_modulus != old_numerator:
            raise AssertionError(("primary inverse", ambient, stage, n, rho))
        # The exact full-phase defect is a sum of N_n times the 3-localized
        # endpoint defect and (N_n-N_rho) times the old endpoint.  The first
        # denominator is prime to three; the divisibility check above cancels
        # the entire old 3-primary denominator in the second summand.
        primary_inverse_checks += 1

    return {
        "ambient": ambient,
        "stage": stage,
        "old_depth": old_depth,
        "new_depth": new_depth,
        "old_upper": old_upper,
        "new_upper": new_upper,
        "old_period": old_period,
        "old_points": old_points,
        "new_points": new_points,
        "old_gap": old_gap,
        "new_gap": new_gap,
        "maximum_fixed_defect": maximum_fixed_defect,
        "primary_inverse_checks": primary_inverse_checks,
    }


def verify_all_complete_subwindows(
    transition: dict[str, object], threshold: Fraction
) -> tuple[int, int, int]:
    """Falsify primary-compatible ideal refinement for every subwindow.

    An old complete-primary-period subwindow contains one exponent in every
    residue class modulo T.  A new ninefold-period subwindow contains nine in
    every class.  For every pair of such consecutive subwindows we certify
    one old point and one of its nine ideal real-circle preimages that lies
    farther than ``threshold`` from all nine corresponding new exponents.
    """

    old_depth = int(transition["old_depth"])
    new_depth = int(transition["new_depth"])
    old_period = int(transition["old_period"])
    old_points = transition["old_points"]
    new_points = transition["new_points"]
    assert isinstance(old_points, list)
    assert isinstance(new_points, list)

    old_extra = len(old_points) - old_period
    new_extra = len(new_points) - 9 * old_period
    if old_extra < 0 or new_extra < 0:
        raise AssertionError(("missing complete subwindow", old_extra, new_extra))

    # Precompute all exact threshold comparisons that can occur.  Only new
    # exponents in the same old primary residue class are relevant, keeping
    # the expensive big-rational work small.
    far: list[list[dict[int, bool]]] = []
    exact_distance_checks = 0
    for old_index, old_point in enumerate(old_points):
        old_n = old_depth + old_index
        target_rows: list[dict[int, bool]] = []
        for branch in range(9):
            old_numerator, old_denominator = old_point
            target = (
                old_numerator + branch * old_denominator,
                9 * old_denominator,
            )
            row: dict[int, bool] = {}
            for new_index, new_point in enumerate(new_points):
                new_n = new_depth + new_index
                if (new_n - old_n) % old_period == 0:
                    row[new_index] = circle_distance_gt(
                        target, new_point, threshold
                    )
                    exact_distance_checks += 1
            target_rows.append(row)
        far.append(target_rows)

    window_pairs = 0
    for new_offset in range(new_extra + 1):
        # For every possible old point, retain a branch which is absent from
        # its nine corresponding new children, if one exists.
        absent_branch: list[int | None] = [None] * len(old_points)
        new_start_n = new_depth + new_offset
        for old_index in range(len(old_points)):
            old_n = old_depth + old_index
            first_n = new_start_n + ((old_n - new_start_n) % old_period)
            child_indices = [
                first_n - new_depth + multiple * old_period
                for multiple in range(9)
            ]
            if child_indices[-1] >= new_offset + 9 * old_period:
                raise AssertionError(("child window overflow", new_offset, old_index))
            for branch in range(9):
                if all(far[old_index][branch][index] for index in child_indices):
                    absent_branch[old_index] = branch
                    break

        for old_offset in range(old_extra + 1):
            witnesses = [
                old_index
                for old_index in range(old_offset, old_offset + old_period)
                if absent_branch[old_index] is not None
            ]
            if not witnesses:
                raise AssertionError(
                    (
                        "unfalsified primary-compatible subwindows",
                        transition["ambient"],
                        transition["stage"],
                        old_offset,
                        new_offset,
                        threshold,
                    )
                )
            window_pairs += 1

    return window_pairs, exact_distance_checks, old_extra + new_extra


def countermodel_checks() -> tuple[int, int]:
    """Exact rational no-go for using only the listed structural inputs.

    This deliberately is not a BBP/pi model.  It has the same endpoint
    3-valuations, ninefold localized decimation, nested units, complete
    primary grids, and arbitrarily close adjacent signs.  Nevertheless all
    full phases in each selected row lie in an arc shorter than 1/100.
    """

    epsilon = Fraction(1, 100)
    previous_c = 1
    previous_minus = Fraction(1, 3**2 * previous_c)
    previous_plus = Fraction(1, 3 * previous_c)
    checks = 0
    primary_points = 0

    for ambient in (4, 6, 8):
        pre_depth, _, pre_exponent = endpoint_rows(ambient)[0]
        plus_depth, _, plus_exponent = endpoint_rows(ambient)[1]
        maximum_upper = max(exact_upper(pre_depth), exact_upper(plus_depth))
        maximum_numerator = 10**maximum_upper - 16

        modulus = 3 ** (ambient - 2)
        lower_bound = 100 * maximum_numerator // (3 ** (ambient - 1)) + 2
        multiplier = max(1, (lower_bound - previous_c + modulus - 1) // modulus)
        current_c = previous_c + multiplier * modulus
        if current_c % 3 == 0 or current_c <= lower_bound:
            raise AssertionError(("countermodel cofactor", ambient))

        current_minus = Fraction(1, 3**ambient * current_c)
        current_plus = Fraction(1, 3 ** (ambient - 1) * current_c)
        if valuation(current_minus.denominator, 3) != pre_exponent:
            raise AssertionError(("countermodel pre valuation", ambient))
        if valuation(current_plus.denominator, 3) != plus_exponent:
            raise AssertionError(("countermodel plus valuation", ambient))
        if (9 * current_minus - previous_minus).denominator % 3 == 0:
            raise AssertionError(("countermodel pre decimation", ambient))
        if (9 * current_plus - previous_plus).denominator % 3 == 0:
            raise AssertionError(("countermodel plus decimation", ambient))
        if current_plus - current_minus != Fraction(2, 3**ambient * current_c):
            raise AssertionError(("countermodel adjacent identity", ambient))
        checks += 5

        for depth, stage, exponent in endpoint_rows(ambient):
            partial = current_minus if stage == "pre-drop" else current_plus
            upper = exact_upper(depth)
            maximum_phase = (10**upper - 16) * partial
            minimum_phase = (10**depth - 16) * partial
            if not 0 < minimum_phase <= maximum_phase < epsilon:
                raise AssertionError(("countermodel phase arc", ambient, stage))
            if not 1 - maximum_phase + minimum_phase > 1 - epsilon:
                raise AssertionError(("countermodel gap", ambient, stage))

            beta = pow(current_c, -1, 3**exponent)
            period = 3 ** (exponent - 2)
            residues = {
                primary_phase_numerator(beta, exponent, n)
                for n in range(depth, depth + period)
            }
            if len(residues) != period:
                raise AssertionError(("countermodel primary grid", ambient, stage))
            primary_points += period
            checks += 3

        previous_c = current_c
        previous_minus = current_minus
        previous_plus = current_plus

    return checks, primary_points


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    root = repository_root()
    pins = {
        root / "problems/local/pi-digits.txt": SOURCE_SHA256,
        root / "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md": (
            DECIMATION_REPORT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_three_primary_decimation_20260813_independent_audit.md": (
            DECIMATION_AUDIT_SHA256
        ),
        root / "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md": (
            FULL_PHASE_REPORT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py": (
            FULL_PHASE_CHECKER_SHA256
        ),
        root / "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md": (
            TWISTED_REPORT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_audit.md": (
            TWISTED_AUDIT_SHA256
        ),
    }
    for path, expected in pins.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(("frozen input", path, actual, expected))

    geometry_checks, geometry_records = exact_window_geometry()
    partials, partial_fraction_checks = exact_partial_sums()
    transitions = [
        verify_transition(partials, ambient, stage)
        for ambient in (6, 8)
        for stage in ("pre-drop", "first-drop")
    ]

    thresholds = {
        (6, "pre-drop"): Fraction(3, 20),
        (6, "first-drop"): Fraction(1, 10),
        (8, "pre-drop"): Fraction(1, 4),
        (8, "first-drop"): Fraction(1, 6),
    }
    subwindow_rows: list[str] = []
    total_window_pairs = 0
    total_distance_checks = 0
    for transition in transitions:
        key = int(transition["ambient"]), str(transition["stage"])
        window_pairs, distance_checks, extras = verify_all_complete_subwindows(
            transition, thresholds[key]
        )
        total_window_pairs += window_pairs
        total_distance_checks += distance_checks
        subwindow_rows.append(
            f"e{key[0]}/{key[1]}:threshold={thresholds[key]}:"
            f"window_pairs={window_pairs}:extra_offsets={extras}"
        )

    counter_checks, counter_primary_points = countermodel_checks()

    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print(f"frozen_input_checks={len(pins)}")
    print(f"partial_fraction_checks={partial_fraction_checks}")
    print(f"window_geometry_checks={geometry_checks}")
    print("window_geometry=" + ";".join(geometry_records))
    for transition in transitions:
        print(
            "transition="
            f"e{transition['ambient']}/{transition['stage']};"
            f"old_period={transition['old_period']};"
            f"old_gap={float(transition['old_gap']):.15g};"
            f"new_gap={float(transition['new_gap']):.15g};"
            f"new_gt_old_over_9=true;new_lt_old_over_3=true;"
            f"max_fixed_defect={float(transition['maximum_fixed_defect']):.15g};"
            f"primary_inverse_checks={transition['primary_inverse_checks']}"
        )
    print("subwindow_no_go=" + ";".join(subwindow_rows))
    print(f"complete_subwindow_pairs={total_window_pairs}")
    print(f"exact_subwindow_distance_checks={total_distance_checks}")
    print(f"countermodel_checks={counter_checks}")
    print(f"countermodel_primary_points={counter_primary_points}")
    print("countermodel_gap_lower_bound=99/100")
    print("countermodel_is_bbp_or_pi=false")
    print("asserts_endpoint_gap_law=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
