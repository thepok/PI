#!/usr/bin/env python3
"""Independent exact checks for the BBP three-primary epoch audit.

This checker imports no code from the primary checker.  It reconstructs the
BBP partial sums from the four original poles, enumerates admissible pole
quotients from their congruences, and separately checks the residual 3-adic
orbit and proportional-row inequalities.  Every bounded computation printed
by this program has claim status ``experiment``; it is not a proof of V1.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md":
        "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3",
    "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md":
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    "work/ultrapi-resume/bbp_three_primary_epoch_20260813_check.py":
        "4cb663d1d484c750ad99d2120d13143c24297ab4f81860a9f1584d5018ea2fa1",
    "work/theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf":
        "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7",
}

MAX_EXACT_DEPTH = 6200
MAX_SYMBOLIC_EXPONENT = 160
MAX_ORBIT_EXPONENT = 12

# (linear coefficient, constant term, partial-fraction coefficient)
POLES = (
    (8, 1, Fraction(4)),
    (2, 1, Fraction(-1, 2)),
    (8, 5, Fraction(-1)),
    (4, 3, Fraction(-1, 2)),
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(integer: int, prime: int) -> int:
    require(integer != 0, "valuation at zero is not used")
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        answer += 1
        integer //= prime
    return answer


def rational_valuation(value: Fraction, prime: int) -> int:
    return valuation(value.numerator, prime) - valuation(value.denominator, prime)


def rational_mod(value: Fraction, modulus: int) -> int:
    if modulus == 1:
        return 0
    require(math.gcd(value.denominator, modulus) == 1,
            f"nonunit denominator modulo {modulus}: {value.denominator}")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def four_pole_coefficient(index: int) -> Fraction:
    return sum(
        (coefficient / (slope * index + constant) for slope, constant, coefficient in POLES),
        Fraction(),
    )


def collapsed_coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def predicted_state(depth: int) -> tuple[int, int, int, str]:
    """Return (reduced 3-exponent, leading unit, ambient exponent, stage)."""
    ambient = 1
    while True:
        power = 3**ambient
        if ambient % 2:
            start = (power - 3) // 4
            stop = (3 * power - 1) // 8
            if start <= depth < stop:
                return ambient, 1, ambient, "odd"
        else:
            first = (power - 1) // 8
            second = (power - 1) // 2
            third = 5 * (power - 1) // 8
            stop = 3 * (power - 1) // 4
            if first <= depth < stop:
                if depth < second:
                    return ambient, 1, ambient, "even-first"
                if depth < third:
                    return ambient, 2, ambient, "even-second"
                return ambient - 1, 2, ambient, "even-drop"
        ambient += 1


def exact_height_quotients(depth: int, exponent: int) -> tuple[tuple[int, ...], ...]:
    """Enumerate q for L(k)=q*3^exponent without iterating over k."""
    power = 3**exponent
    rows: list[tuple[int, ...]] = []
    for slope, constant, _ in POLES:
        maximum_q = (slope * depth + constant) // power
        found: list[int] = []
        for quotient in range(1, maximum_q + 1):
            numerator = quotient * power - constant
            if (
                quotient % 3
                and numerator >= 0
                and numerator % slope == 0
                and numerator // slope <= depth
            ):
                found.append(quotient)
        rows.append(tuple(found))
    return tuple(rows)


def leading_sum(depth: int, exponent: int, modulus: int) -> int:
    """Localized sum of all exact-height terms, modulo a power of three."""
    power = 3**exponent
    total = Fraction()
    rows = exact_height_quotients(depth, exponent)
    for pole_index, (slope, constant, coefficient) in enumerate(POLES):
        for quotient in rows[pole_index]:
            index = (quotient * power - constant) // slope
            total += coefficient * Fraction(pow(16, -index, modulus), quotient)
    return rational_mod(total, modulus)


def divided_power_difference(exponent: int, modulus: int) -> int:
    """Compute (10^exponent-16)/3 modulo ``modulus`` exactly."""
    if modulus == 1:
        return 0
    residue = pow(10, exponent, 3 * modulus) - 16
    require(residue % 3 == 0, "division by three failed")
    return (residue // 3) % modulus


def run() -> dict[str, object]:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned artifact: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    # Independent common-denominator reconstruction of the BBP coefficient.
    coefficient_checks = 0
    for index in range(0, 2049):
        require(four_pole_coefficient(index) == collapsed_coefficient(index),
                f"four-pole identity at k={index}")
        coefficient_checks += 1

    # Re-derive the interval adjacency, all admissible top poles, the mod-9
    # cancellation, and the complete next-level pole list far beyond the
    # range where exact Fraction partial sums are practical.
    partition_checks = 0
    pole_list_checks = 0
    cluster_checks = 0
    inequality_checks = 0
    previous_stop = 0
    for ambient in range(1, MAX_SYMBOLIC_EXPONENT + 1):
        power = 3**ambient
        if ambient % 2:
            start = (power - 3) // 4
            stop = (3 * power - 1) // 8
            require(start == previous_stop and start < stop,
                    f"odd partition at e={ambient}")
            require(exact_height_quotients(start, ambient) == ((), (), (), (1,)),
                    f"odd first pole at e={ambient}")
            require(exact_height_quotients(stop - 1, ambient) == ((), (), (), (1,)),
                    f"odd complete top list at e={ambient}")
            require(exact_height_quotients(stop - 1, ambient + 1) == ((), (), (), ()),
                    f"odd no higher pole at e={ambient}")
            require(leading_sum(stop - 1, ambient, 3) == 1,
                    f"odd leading unit at e={ambient}")
            if ambient >= 5:
                period = 3 ** (ambient - 2)
                last = stop - 1
                require(8 * last == 27 * period - 9,
                        f"odd last-depth identity at e={ambient}")
                require(last <= 4 * (period - 1),
                        f"odd noncoverage inequality at e={ambient}")
                inequality_checks += 1
            previous_stop = stop
            pole_list_checks += 4
        else:
            first = (power - 1) // 8
            second = (power - 1) // 2
            third = 5 * (power - 1) // 8
            stop = 3 * (power - 1) // 4
            require(first == previous_stop,
                    f"even partition at e={ambient}")
            require((second, third, stop) == (4 * first, 5 * first, 6 * first),
                    f"even threshold multiples at e={ambient}")
            expected_stages = (
                (first, ((1,), (), (), ())),
                (second - 1, ((1,), (), (), ())),
                (second, ((1,), (1,), (), ())),
                (third - 1, ((1,), (1,), (), ())),
                (third, ((1,), (1,), (5,), ())),
                (stop - 1, ((1,), (1,), (5,), ())),
            )
            for depth, expected in expected_stages:
                require(exact_height_quotients(depth, ambient) == expected,
                        f"even top list at e={ambient}, M={depth}")
            require(exact_height_quotients(stop - 1, ambient + 1) == ((), (), (), ()),
                    f"even no higher pole at e={ambient}")
            require(leading_sum(first, ambient, 3) == 1,
                    f"first even unit at e={ambient}")
            require(leading_sum(second, ambient, 3) == 2,
                    f"second even unit at e={ambient}")
            require(leading_sum(third, ambient, 3) == 0,
                    f"third even cancellation at e={ambient}")

            # The top cluster is checked in Z_(3)/9Z_(3), including the
            # rational coefficients 1/2 and 1/5 rather than integer stand-ins.
            top_cluster = (
                Fraction(4) * Fraction(pow(16, -first, 9))
                - Fraction(1, 2) * Fraction(pow(16, -second, 9))
                - Fraction(1, 5) * Fraction(pow(16, -third, 9))
            )
            require(rational_mod(top_cluster, 9) == 0,
                    f"top cluster modulo nine at e={ambient}")

            lower_expected = ((11,), (1,), (7,), (1, 5))
            require(exact_height_quotients(third, ambient - 1) == lower_expected,
                    f"lower list at cancellation at e={ambient}")
            require(exact_height_quotients(stop - 1, ambient - 1) == lower_expected,
                    f"lower list before next epoch at e={ambient}")
            require(leading_sum(third, ambient - 1, 3) == 2,
                    f"lower leading sum at e={ambient}")
            require(leading_sum(stop - 1, ambient - 1, 3) == 2,
                    f"persistent lower leading sum at e={ambient}")

            top_after_division = rational_mod(top_cluster / 3, 3)
            require(top_after_division == 0,
                    f"top cluster vanishes one level down at e={ambient}")
            require((top_after_division + leading_sum(third, ambient - 1, 3)) % 3 == 2,
                    f"exact one-level drop unit at e={ambient}")

            top_period = 3 ** (ambient - 2)
            pre_drop = third - 1
            require(8 * pre_drop == 45 * top_period - 13,
                    f"pre-drop depth identity at e={ambient}")
            require(pre_drop >= 5 * (top_period - 1),
                    f"pre-drop coverage inequality at e={ambient}")
            if ambient >= 4:
                drop_period = 3 ** (ambient - 3)
                require(8 * third == 135 * drop_period - 5,
                        f"drop depth identity at e={ambient}")
                require(third > 5 * (drop_period - 1),
                        f"drop coverage inequality at e={ambient}")
            previous_stop = stop
            pole_list_checks += len(expected_stages) + 4
            cluster_checks += 1
            inequality_checks += 2 if ambient >= 4 else 1
        partition_checks += 1

    require(8**5 > 10 * 5**5, "(8/5)^5 > 10")
    require(8**4 < 10 * 5**4, "(8/5)^4 < 10")

    # Exact rational replay from the four poles, independently of the
    # collapsed coefficient and independently of the primary checker.
    partial_sum = Fraction()
    power_of_sixteen = 1
    upper = 0
    decimal_threshold = 1
    exact_state_checks = 0
    exact_row_checks = 0
    direct_phase_checks = 0
    transitions: list[tuple[int, int, int, str]] = []
    previous_state: tuple[int, int] | None = None
    samples: dict[int, tuple[Fraction, int, int]] = {}
    full_rows = 0
    odd_full_rows = 0
    for depth in range(MAX_EXACT_DEPTH + 1):
        if depth:
            power_of_sixteen *= 16
            while power_of_sixteen >= 10 * decimal_threshold:
                decimal_threshold *= 10
                upper += 1
        partial_sum += four_pole_coefficient(depth) / power_of_sixteen
        expected_exponent, expected_unit, ambient, stage = predicted_state(depth)
        actual_exponent = -rational_valuation(partial_sum, 3)
        actual_unit = rational_mod((3**actual_exponent) * partial_sum, 3)
        require((actual_exponent, actual_unit) == (expected_exponent, expected_unit),
                f"exact state at M={depth}")
        exact_state_checks += 1

        state = (actual_exponent, actual_unit)
        if state != previous_state:
            transitions.append((depth, actual_exponent, actual_unit, stage))
            previous_state = state
            samples[depth] = (partial_sum, actual_exponent, upper)

        period = 1 if actual_exponent <= 2 else 3 ** (actual_exponent - 2)
        row_length = upper - depth + 1
        require(row_length == len(str(power_of_sixteen)) - 1 - depth + 1,
                f"exact logarithm at M={depth}")
        is_full = row_length >= period
        full_rows += int(is_full)
        if stage == "odd" and actual_exponent >= 3:
            odd_full_rows += int(is_full)
            require(not is_full, f"unexpected complete odd row at M={depth}")
        if stage == "even-drop" and ambient >= 4:
            require(is_full, f"incomplete certified drop row at M={depth}")
        exact_row_checks += 1

        ambient_power = 3**ambient
        endpoints = {(ambient_power - 3) // 4} if ambient % 2 else {
            (ambient_power - 1) // 8,
            (ambient_power - 1) // 2,
            5 * (ambient_power - 1) // 8,
            3 * (ambient_power - 1) // 4 - 1,
        }
        if depth in endpoints:
            samples[depth] = (partial_sum, actual_exponent, upper)

    # Exact quotient orbit: injectivity comes from the order, and cardinality
    # then identifies the entire congruence-one coset.
    orbit_checks = 0
    orbit_points = 0
    for exponent in range(2, MAX_ORBIT_EXPONENT + 1):
        modulus = 3 ** (exponent - 1)
        period = 3 ** (exponent - 2)
        require(pow(10, period, 3**exponent) == 1,
                f"order upper bound at E={exponent}")
        if period > 1:
            require(pow(10, period // 3, 3**exponent) != 1,
                    f"order minimality at E={exponent}")
        orbit = [divided_power_difference(n, modulus) for n in range(1, period + 1)]
        require(len(set(orbit)) == period, f"quotient injectivity at E={exponent}")
        require(set(orbit) == set(range(1, modulus, 3)),
                f"complete congruence-one coset at E={exponent}")
        require(all(
            divided_power_difference(n + period, modulus) == orbit[n - 1]
            for n in range(1, min(period, 200) + 1)
        ), f"quotient periodicity at E={exponent}")
        orbit_checks += 1
        orbit_points += period

    # Directly compare the localized row phase with beta*g_n at independent
    # transition samples.  The extraction uses 3^(E-1)(10^n-16)B_M.
    for depth, (value, exponent, sample_upper) in sorted(samples.items()):
        if exponent <= 1:
            continue
        modulus = 3 ** (exponent - 1)
        beta = rational_mod((3**exponent) * value, modulus)
        for n in sorted({max(1, depth), max(1, sample_upper), max(1, depth + 1)}):
            expected = beta * divided_power_difference(n, modulus) % modulus
            actual = rational_mod(
                Fraction(3 ** (exponent - 1)) * (10**n - 16) * value,
                modulus,
            )
            require(actual == expected, f"localized phase at M={depth}, n={n}")
            require(actual % 3 == rational_mod((3**exponent) * value, 3),
                    f"localized coset at M={depth}, n={n}")
            direct_phase_checks += 1

    # Finite falsification of the elementary primitive-numerator lemma used
    # for the Bourgain--Chang applicability discussion.  Its general proof is
    # the two one-line reductions modulo 3 and modulo every p|Q in the report.
    primitive_checks = 0
    for exponent in range(1, 12):
        for q in (5, 7, 11, 35, 55, 77, 385):
            for beta in range(1, min(3**exponent, 30)):
                if beta % 3 == 0:
                    continue
                for xi in range(1, min(q, 30)):
                    if math.gcd(xi, q) != 1:
                        continue
                    numerator = beta * q + xi * 3**exponent
                    require(math.gcd(numerator, 3**exponent * q) == 1,
                            "combined numerator is not primitive")
                    primitive_checks += 1

    transition_text = ",".join(
        f"{depth}:E{exponent}/u{unit}/{stage}"
        for depth, exponent, unit, stage in transitions
    )
    return {
        "claim_status": "experiment",
        "coefficient_identity_checks": coefficient_checks,
        "symbolic_partition_checks": partition_checks,
        "symbolic_pole_list_checks": pole_list_checks,
        "symbolic_cluster_checks": cluster_checks,
        "symbolic_row_inequality_checks": inequality_checks,
        "exact_fraction_state_checks": exact_state_checks,
        "exact_row_window_checks": exact_row_checks,
        "full_grid_rows": full_rows,
        "nontrivial_odd_full_grid_rows": odd_full_rows,
        "quotient_orbit_checks": orbit_checks,
        "quotient_orbit_points": orbit_points,
        "direct_localized_phase_checks": direct_phase_checks,
        "primitive_numerator_checks": primitive_checks,
        "observed_state_transitions": transition_text,
        "v1_status": "not_proved",
        "status": "PASS",
    }


if __name__ == "__main__":
    for key, value in run().items():
        print(f"{key}={value}")
