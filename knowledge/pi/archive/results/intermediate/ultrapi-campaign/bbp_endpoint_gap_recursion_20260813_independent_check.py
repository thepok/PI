#!/usr/bin/env python3
"""Independent adversarial replay of the endpoint-gap recursion report.

This checker imports no code from the primary checker.  It rebuilds the BBP
fractions from the four pole sums, generates phases by direct modular
exponentiation, and evaluates the complete-subwindow quantifiers over one
common integer denominator.  All bounded conclusions are ``experiment``;
the elementary general arguments in the audit remain ``proof sketch``.
"""

from __future__ import annotations

import hashlib
import re
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PRIMARY_REPORT = ROOT / "work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813.md"
PRIMARY_CHECKER = ROOT / "work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py"

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813_independent_audit.md":
        "5dc190f913c1eb727e4a1cbc9bef2d8f3373af00b17e1aa50244ae8efceb3371",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py":
        "502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md":
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_audit.md":
        "44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81",
    "work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813.md":
        "6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d",
    "work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py":
        "0c8967858d1023e001cbc3fb011ae525cdd1800d3622e92d7d1fc0dd712cc780",
}

EXPECTED_GEOMETRY = (
    (4, "pre-drop", 13, 23, 2),
    (4, "first-drop", 5, 6, -7),
    (6, "pre-drop", 13, 15, -6),
    (6, "first-drop", 5, 7, -6),
    (8, "pre-drop", 13, 21, 0),
    (8, "first-drop", 5, 13, 0),
    (10, "pre-drop", 13, 21, 0),
    (10, "first-drop", 5, 14, 1),
    (12, "pre-drop", 13, 23, 2),
    (12, "first-drop", 5, 6, -7),
    (14, "pre-drop", 13, 17, -4),
    (14, "first-drop", 5, 10, -3),
)

THRESHOLDS = {
    (6, "pre-drop"): Fraction(3, 20),
    (6, "first-drop"): Fraction(1, 10),
    (8, "pre-drop"): Fraction(1, 4),
    (8, "first-drop"): Fraction(1, 6),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_digest(value: Fraction) -> str:
    payload = f"{value.numerator}/{value.denominator}".encode()
    return hashlib.sha256(payload).hexdigest()


def valuation(number: int, prime: int) -> int:
    if number == 0:
        raise ValueError("valuation at zero")
    number = abs(number)
    answer = 0
    while number % prime == 0:
        number //= prime
        answer += 1
    return answer


def endpoints(e: int) -> tuple[tuple[str, int, int], ...]:
    a = (3**e - 1) // 8
    return (("pre-drop", 5 * a - 1, e), ("first-drop", 5 * a, e - 1))


def decimal_upper(m: int) -> int:
    """Find floor(log_10(16**m)) from exact inequalities."""
    value = 1 << (4 * m)
    guess = (120_411_998 * m) // 100_000_000
    while 10 ** (guess + 1) <= value:
        guess += 1
    while 10**guess > value:
        guess -= 1
    assert 10**guess <= value < 10 ** (guess + 1)
    return guess


def pole_term(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(1, 4 * k + 2)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def combined_term(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def small_bbp_sums() -> tuple[dict[tuple[int, str], Fraction], int]:
    targets = {
        m: (e, stage)
        for e in (4, 6, 8)
        for stage, m, _ in endpoints(e)
    }
    total = Fraction(0)
    denominator_power = 1
    answer: dict[tuple[int, str], Fraction] = {}
    term_checks = 0
    for k in range(max(targets) + 1):
        if k:
            denominator_power <<= 4
        pole = pole_term(k)
        assert pole == combined_term(k) and pole > 0
        total += pole / denominator_power
        term_checks += 1
        if k in targets:
            answer[targets[k]] = total
    assert len(answer) == len(targets)
    return answer, term_checks


def phase_row(value: Fraction, first: int, last: int) -> list[int]:
    """Generate exact phase numerators directly, not by recurrence."""
    p, q = value.numerator, value.denominator
    row = [((pow(10, n, q) - 16) * p) % q for n in range(first, last + 1)]
    assert len(set(row)) == len(row)
    return row


def largest_gap(numerators: list[int], denominator: int) -> Fraction:
    ordered = sorted(numerators)
    differences = [b - a for a, b in zip(ordered, ordered[1:])]
    differences.append(denominator + ordered[0] - ordered[-1])
    return Fraction(max(differences), denominator)


def circle_numerator(left: int, left_q: int, right: int, right_q: int) -> tuple[int, int]:
    common = left_q * right_q
    difference = abs(left * right_q - right * left_q)
    return min(difference, common - difference), common


def beta(value: Fraction, exponent: int) -> int:
    assert valuation(value.denominator, 3) == exponent
    cofactor = value.denominator // 3**exponent
    return value.numerator * pow(cofactor, -1, 3**exponent) % 3**exponent


def primary_numerator(unit: int, exponent: int, n: int) -> int:
    lifted_modulus = 3**exponent
    lifted = (pow(10, n, lifted_modulus) - 16) % lifted_modulus
    assert lifted % 3 == 0
    return unit * (lifted // 3) % (3 ** (exponent - 1))


def geometry_replay() -> list[tuple[int, str, int, int, int]]:
    # These exact integer inequalities certify the two bounds used in R9.
    assert 10**15 < 16**13 < 10**16
    assert 10**6 < 16**5 < 10**7
    output: list[tuple[int, str, int, int, int]] = []
    data: dict[tuple[int, str], tuple[int, int, int]] = {}
    for e in range(2, 16, 2):
        for stage, m, _ in endpoints(e):
            u = decimal_upper(m)
            data[e, stage] = (m, u, u - m + 1)
    for e in range(4, 16, 2):
        for stage, shift, lower_c, upper_c in (
            ("pre-drop", 13, 15, 24),
            ("first-drop", 5, 6, 15),
        ):
            m, u, length = data[e, stage]
            old_m, old_u, old_length = data[e - 2, stage]
            assert m == 9 * old_m + shift
            c = u - 9 * old_u
            assert lower_c <= c <= upper_c
            delta = length - 9 * old_length
            assert delta == c - shift - 8
            output.append((e, stage, shift, c, delta))
    assert tuple(output) == EXPECTED_GEOMETRY
    return output


def transition_replay(
    sums: dict[tuple[int, str], Fraction], e: int, stage: str
) -> dict[str, object]:
    old_stage, old_m, old_e3 = next(x for x in endpoints(e - 2) if x[0] == stage)
    new_stage, new_m, new_e3 = next(x for x in endpoints(e) if x[0] == stage)
    assert old_stage == new_stage == stage and new_e3 == old_e3 + 2
    old_u, new_u = decimal_upper(old_m), decimal_upper(new_m)
    old_b, new_b = sums[e - 2, stage], sums[e, stage]

    localized = 9 * new_b - old_b
    assert localized.denominator % 3 != 0
    old_beta, new_beta = beta(old_b, old_e3), beta(new_b, new_e3)
    assert (new_beta - old_beta) % 3**old_e3 == 0

    old_row = phase_row(old_b, old_m, old_u)
    new_row = phase_row(new_b, new_m, new_u)
    period = 3 ** (old_e3 - 2)
    old_primary_q = 3 ** (old_e3 - 1)
    new_primary_q = 9 * old_primary_q
    primary_checks = 0
    maximum_fixed = Fraction(0)

    for n, new_residue in zip(range(new_m, new_u + 1), new_row, strict=True):
        rho = old_m + ((n - old_m) % period)
        assert (pow(10, n, 3**old_e3) - pow(10, rho, 3**old_e3)) % 3**old_e3 == 0
        new_x = primary_numerator(new_beta, new_e3, n)
        old_x = primary_numerator(old_beta, old_e3, rho)
        assert new_primary_q == 9 * old_primary_q
        assert new_x % old_primary_q == old_x
        primary_checks += 1

        old_residue = ((pow(10, n, old_b.denominator) - 16) * old_b.numerator) % old_b.denominator
        distance_n, distance_q = circle_numerator(
            (9 * new_residue) % new_b.denominator,
            new_b.denominator,
            old_residue,
            old_b.denominator,
        )
        distance = Fraction(distance_n, distance_q)
        if distance > maximum_fixed:
            maximum_fixed = distance

    assert maximum_fixed > Fraction(49, 100)
    old_gap = largest_gap(old_row, old_b.denominator)
    new_gap = largest_gap(new_row, new_b.denominator)
    assert new_gap > old_gap / 9
    assert new_gap < old_gap / 3

    return {
        "e": e,
        "stage": stage,
        "old_m": old_m,
        "new_m": new_m,
        "old_u": old_u,
        "new_u": new_u,
        "period": period,
        "old_b": old_b,
        "new_b": new_b,
        "old_row": old_row,
        "new_row": new_row,
        "old_gap": old_gap,
        "new_gap": new_gap,
        "maximum_fixed": maximum_fixed,
        "primary_checks": primary_checks,
    }


def exhaustive_windows(data: dict[str, object], threshold: Fraction) -> tuple[int, int, Fraction]:
    """Compute min_windows max_old,branch min_n distance exactly.

    All distances use Q=9*D_old*D_new, so the nested extrema compare integers
    and do not share the primary checker's precomputed Boolean organization.
    """
    old_m, new_m = int(data["old_m"]), int(data["new_m"])
    period = int(data["period"])
    old_b, new_b = data["old_b"], data["new_b"]
    old_row, new_row = data["old_row"], data["new_row"]
    assert isinstance(old_b, Fraction) and isinstance(new_b, Fraction)
    assert isinstance(old_row, list) and isinstance(new_row, list)

    old_extra = len(old_row) - period
    new_extra = len(new_row) - 9 * period
    assert old_extra >= 0 and new_extra >= 0
    common_q = 9 * old_b.denominator * new_b.denominator

    distances: list[list[dict[int, int]]] = []
    exact_checks = 0
    for old_index, old_residue in enumerate(old_row):
        old_n = old_m + old_index
        branches: list[dict[int, int]] = []
        for branch in range(9):
            target_numerator = old_residue + branch * old_b.denominator
            by_new_index: dict[int, int] = {}
            for new_index, new_residue in enumerate(new_row):
                new_n = new_m + new_index
                if (new_n - old_n) % period:
                    continue
                raw = abs(
                    target_numerator * new_b.denominator
                    - 9 * old_b.denominator * new_residue
                )
                by_new_index[new_index] = min(raw, common_q - raw)
                exact_checks += 1
            branches.append(by_new_index)
        distances.append(branches)

    pairs = 0
    weakest_pair_witness = common_q
    for new_offset in range(new_extra + 1):
        point_scores: list[int] = []
        new_start = new_m + new_offset
        for old_index in range(len(old_row)):
            old_n = old_m + old_index
            first_n = new_start + ((old_n - new_start) % period)
            children = [first_n - new_m + j * period for j in range(9)]
            assert new_offset <= children[0] and children[-1] < new_offset + 9 * period
            score = max(
                min(distances[old_index][branch][child] for child in children)
                for branch in range(9)
            )
            point_scores.append(score)
        for old_offset in range(old_extra + 1):
            witness = max(point_scores[old_offset:old_offset + period])
            assert witness * threshold.denominator > threshold.numerator * common_q
            weakest_pair_witness = min(weakest_pair_witness, witness)
            pairs += 1

    return pairs, exact_checks, Fraction(weakest_pair_witness, common_q)


def adjacent_replay(
    sums: dict[tuple[int, str], Fraction], transitions: list[dict[str, object]]
) -> int:
    checks = 0
    for e in (4, 6, 8):
        _, m_minus, _ = endpoints(e)[0]
        _, m_plus, _ = endpoints(e)[1]
        assert m_plus == m_minus + 1
        tail = sums[e, "first-drop"] - sums[e, "pre-drop"]
        assert tail == pole_term(m_plus) / 16**m_plus and tail > 0
        u_minus, u_plus = decimal_upper(m_minus), decimal_upper(m_plus)
        assert u_plus - u_minus in (1, 2)
        delta = Fraction(1, 15 * (m_minus + 1) ** 2)
        assert (10**u_minus - 16) * tail < delta
        checks += 4

    for data in transitions:
        e = int(data["e"])
        _, new_m_minus, _ = endpoints(e)[0]
        _, old_m_minus, _ = endpoints(e - 2)[0]
        new_tail = sums[e, "first-drop"] - sums[e, "pre-drop"]
        old_tail = sums[e - 2, "first-drop"] - sums[e - 2, "pre-drop"]
        new_bound = Fraction(1, 15 * (new_m_minus + 1) ** 2)
        old_bound = Fraction(1, 15 * (old_m_minus + 1) ** 2)
        # This is the termwise triangle estimate in R26 on both common ranges.
        assert (10 ** decimal_upper(new_m_minus) - 16) * new_tail < new_bound
        assert (10 ** decimal_upper(old_m_minus) - 16) * old_tail < old_bound
        old_gap, new_gap = data["old_gap"], data["new_gap"]
        assert isinstance(old_gap, Fraction) and isinstance(new_gap, Fraction)
        # R28 itself is same-epoch; these exact rows also satisfy both directions.
        current_minus_gap = largest_gap(
            phase_row(sums[e, "pre-drop"], new_m_minus, decimal_upper(new_m_minus)),
            sums[e, "pre-drop"].denominator,
        )
        _, new_m_plus, _ = endpoints(e)[1]
        current_plus_gap = largest_gap(
            phase_row(sums[e, "first-drop"], new_m_plus, decimal_upper(new_m_plus)),
            sums[e, "first-drop"].denominator,
        )
        assert current_plus_gap <= 2 * current_minus_gap + 2 * new_bound
        assert current_minus_gap <= 3 * current_plus_gap + 2 * new_bound
        checks += 4
    return checks


def countermodel_replay() -> tuple[int, int, Fraction]:
    epsilon = Fraction(1, 100)
    previous_c = 1
    previous_minus = Fraction(1, 3**2)
    previous_plus = Fraction(1, 3)
    checks = 0
    primary_points = 0
    minimum_gap = Fraction(1)

    for e in (4, 6, 8):
        _, m_minus, minus_e3 = endpoints(e)[0]
        _, m_plus, plus_e3 = endpoints(e)[1]
        u_minus, u_plus = decimal_upper(m_minus), decimal_upper(m_plus)
        largest_n = 10**max(u_minus, u_plus) - 16
        adjacent_delta = Fraction(1, 15 * (m_minus + 1) ** 2)

        # Enforce both the 1/100 arc and the concrete R27 adjacent displacement.
        arc_lower = (100 * largest_n) // 3 ** (e - 1) + 1
        adjacent_lower = (
            2 * largest_n * adjacent_delta.denominator
        ) // (3**e * adjacent_delta.numerator) + 1
        lower = max(arc_lower, adjacent_lower)
        modulus = 3 ** (e - 2)
        k = max(1, (lower - previous_c) // modulus + 1)
        current_c = previous_c + k * modulus
        assert current_c > lower and current_c % 3 != 0

        current_minus = Fraction(1, 3**e * current_c)
        current_plus = Fraction(1, 3 ** (e - 1) * current_c)
        assert valuation(current_minus.denominator, 3) == minus_e3
        assert valuation(current_plus.denominator, 3) == plus_e3
        assert 9 * current_minus - previous_minus == Fraction(-k, current_c * previous_c)
        assert 9 * current_plus - previous_plus == Fraction(-3 * k, current_c * previous_c)
        assert current_plus - current_minus == Fraction(2, 3**e * current_c)
        assert largest_n * (current_plus - current_minus) < adjacent_delta
        checks += 6

        for stage, m, exponent in endpoints(e):
            value = current_minus if stage == "pre-drop" else current_plus
            u = decimal_upper(m)
            low_phase = (10**m - 16) * value
            high_phase = (10**u - 16) * value
            assert 0 < low_phase <= high_phase < epsilon
            gap = 1 - high_phase + low_phase
            assert gap > 1 - epsilon
            minimum_gap = min(minimum_gap, gap)

            unit = pow(current_c, -1, 3**exponent)
            old_exponent = exponent - 2
            if old_exponent >= 1:
                assert (unit - pow(previous_c, -1, 3**old_exponent)) % 3**old_exponent == 0
            period = 3 ** (exponent - 2)
            residues = [primary_numerator(unit, exponent, n) for n in range(m, m + period)]
            assert len(set(residues)) == period
            primary_points += period
            checks += 4

        previous_c = current_c
        previous_minus = current_minus
        previous_plus = current_plus

    assert primary_points == 1092
    return checks, primary_points, minimum_gap


def report_integrity() -> tuple[int, int]:
    raw = PRIMARY_REPORT.read_bytes()
    bad_controls = [byte for byte in raw if byte < 32 and byte not in (9, 10, 13)]
    assert not bad_controls
    text = raw.decode("utf-8")
    links = re.findall(r"\[[^\]]+\]\(([^)]+)\)", text)
    checked = 0
    for link in links:
        target = link.strip("<>").split("#", 1)[0]
        if not target or "://" in target:
            continue
        assert (PRIMARY_REPORT.parent / target).resolve().is_file(), target
        checked += 1
    assert checked >= 8
    return len(bad_controls), checked


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    for relative, expected in PINS.items():
        assert digest(ROOT / relative) == expected, relative
    control_count, link_checks = report_integrity()
    geometry = geometry_replay()
    sums, term_checks = small_bbp_sums()
    transitions = [
        transition_replay(sums, e, stage)
        for e in (6, 8)
        for stage in ("pre-drop", "first-drop")
    ]

    total_pairs = 0
    total_distances = 0
    window_records: list[str] = []
    for data in transitions:
        key = int(data["e"]), str(data["stage"])
        pairs, distances, weakest = exhaustive_windows(data, THRESHOLDS[key])
        total_pairs += pairs
        total_distances += distances
        window_records.append(
            f"e{key[0]}/{key[1]}:pairs={pairs}:threshold={THRESHOLDS[key]}:"
            f"weakest={float(weakest):.15g}:digest={fraction_digest(weakest)}"
        )
    assert total_pairs == 41_924
    assert total_distances == 38_772

    adjacent_checks = adjacent_replay(sums, transitions)
    counter_checks, counter_points, minimum_counter_gap = countermodel_replay()

    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print(f"frozen_hash_checks={len(PINS)}")
    print(f"c0_control_bytes={control_count}")
    print(f"markdown_link_checks={link_checks}")
    print(f"pole_term_checks={term_checks}")
    print(f"geometry_rows={len(geometry)}")
    for data in transitions:
        print(
            f"transition=e{data['e']}/{data['stage']};"
            f"old_gap={float(data['old_gap']):.15g};"
            f"new_gap={float(data['new_gap']):.15g};"
            f"fixed_defect={float(data['maximum_fixed']):.15g};"
            f"primary_checks={data['primary_checks']}"
        )
    print("subwindow_replay=" + ";".join(window_records))
    print(f"complete_subwindow_pairs={total_pairs}")
    print(f"exact_distance_entries={total_distances}")
    print(f"adjacent_checks={adjacent_checks}")
    print(f"countermodel_checks={counter_checks}")
    print(f"countermodel_primary_points={counter_points}")
    print(f"countermodel_minimum_gap={float(minimum_counter_gap):.15g}")
    print("countermodel_is_bbp_or_pi=false")
    print("asserts_endpoint_gap_law=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
