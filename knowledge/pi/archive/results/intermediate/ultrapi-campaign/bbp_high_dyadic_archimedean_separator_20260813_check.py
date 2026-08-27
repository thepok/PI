#!/usr/bin/env python3
"""Exact replay for the sevenfold BBP high-dyadic audit.

This script verifies finite instances of the diagonal two-adic formula, its
seven-step carry recurrence, fixed-level permutation behavior, and a dual
separator which preserves the complete dyadic selected-numerator coordinate
but deliberately changes odd coordinates.  The finite output is experiment
evidence only; it does not prove any decimal-distribution statement for pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_short_orbit_return_attack.md":
        "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d",
}

DIAGONAL_MAX_N = 110
SEPARATOR_START_N = 50
SEPARATOR_MAX_N = 100
DEEP_N = 130
PERIODS = (1, 2, 3, 4)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(coefficient_numerator(k), coefficient_denominator(k))


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def rational_mod(value: Fraction, exponent: int) -> int:
    """Canonical residue of a rational with odd denominator modulo 2^exponent."""
    require(exponent >= 1, "positive two-adic precision required")
    modulus = 1 << exponent
    require(value.denominator & 1 == 1, "denominator must be odd")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def nearest_fraction(value: Fraction) -> int:
    """Return floor(value + 1/2), also for negative values."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def nearest_ratio(numerator: int, denominator: int) -> int:
    require(denominator > 0, "positive denominator required")
    return (2 * numerator + denominator) // (2 * denominator)


def nearest_shift_changing_odd_class(
    target_shift: Fraction,
    residue: int,
    numerator: int,
    modulus: int,
    odd: int,
) -> int:
    """Choose a near shift but avoid S = V modulo the odd denominator."""
    require(odd > 1 and odd & 1 == 1, "nontrivial odd modulus required")
    require(gcd(modulus, odd) == 1, "dyadic modulus must be an odd-unit")
    shift = nearest_fraction(target_shift)
    forbidden_shift = (
        (numerator - residue) * pow(modulus, -1, odd) % odd
    )
    if (shift - forbidden_shift) % odd == 0:
        left = shift - 1
        right = shift + 1
        shift = left if abs(Fraction(left) - target_shift) <= abs(
            Fraction(right) - target_shift
        ) else right
    require((shift - forbidden_shift) % odd != 0,
            "selected shift must change the odd class")
    require(abs(Fraction(shift) - target_shift) <= Fraction(3, 2),
            "admissible shift lies within three half-meshes")
    return shift


def log10_abs_fraction(value: Fraction) -> float:
    require(value != 0, "logarithm requires nonzero value")
    return (log(abs(value.numerator)) - log(value.denominator)) / log(10)


def build_endpoints() -> list[dict[str, int]]:
    """Build exact L_(7n), A_(7n), and seven-term increments."""
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    endpoints = [{"n": 0, "L": common, "A": scaled, "R": 1, "H": 0}]

    for depth in range(1, 7 * DEEP_N + 1):
        denominator = coefficient_denominator(depth)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(depth) * (next_common // denominator)
        )
        common = next_common
        if depth % 7 == 0:
            previous = endpoints[-1]
            ratio = common // previous["L"]
            forcing = sum(
                coefficient_numerator(k)
                * 16 ** (depth - k)
                * (common // coefficient_denominator(k))
                for k in range(depth - 6, depth + 1)
            )
            require(
                scaled == 16**7 * ratio * previous["A"] + forcing,
                f"sevenfold endpoint recurrence at depth={depth}",
            )
            endpoints.append(
                {"n": depth // 7, "L": common, "A": scaled,
                 "R": ratio, "H": forcing}
            )

    require(len(endpoints) == DEEP_N + 1, "endpoint count")
    return endpoints


def rational_bbp(endpoint: dict[str, int]) -> Fraction:
    n = endpoint["n"]
    return Fraction(endpoint["A"], 16 ** (7 * n) * endpoint["L"])


def f_mod(x: int, exponent: int) -> int:
    """Evaluate F(x)=sum 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    total = 0
    for j in range((exponent - 1) // 4 + 1):
        term = coefficient(x - 1 - j)
        total += pow(16, j, modulus) * rational_mod(term, exponent)
    return total % modulus


def diagonal_state(endpoint: dict[str, int]) -> dict[str, int | Fraction]:
    n = endpoint["n"]
    require(n >= 1, "positive sevenfold depth required")
    order = valuation_two(7 * n + 1)
    precision = 27 * n - order
    f_value = Fraction(endpoint["A"], endpoint["L"])
    unit = Fraction(5**n) * f_value / (1 << order)
    coordinate = rational_mod(unit, precision)

    selected = Fraction(
        5**n * endpoint["A"],
        2 ** (27 * n) * endpoint["L"],
    )
    reduced_odd = selected.denominator >> precision
    require(selected.denominator == (1 << precision) * reduced_odd,
            f"reduced dyadic exponent at n={n}")
    require(reduced_odd & 1 == 1, f"reduced odd denominator at n={n}")
    direct_coordinate = (
        selected.numerator
        * pow(reduced_odd, -1, 1 << precision)
        % (1 << precision)
    )
    require(coordinate == direct_coordinate,
            f"complete diagonal coordinate at n={n}")

    return {
        "n": n,
        "order": order,
        "precision": precision,
        "F": f_value,
        "unit": unit,
        "w": coordinate,
    }


def separator_state(
    endpoint: dict[str, int], deep_bbp: Fraction
) -> dict[str, int | Fraction]:
    """Nearest state in the dyadic class whose odd class differs from BBP."""
    n = endpoint["n"]
    odd = endpoint["L"]
    denominator = 2 ** (27 * n) * odd
    numerator = 5**n * endpoint["A"]
    modulus = 2 ** (27 * n)
    target = -10**n * (deep_bbp - rational_bbp(endpoint))

    residue = numerator % modulus
    target_shift = (denominator * target - residue) / modulus
    shift = nearest_shift_changing_odd_class(
        target_shift, residue, numerator, modulus, odd
    )
    centered = residue + modulus * shift
    error = Fraction(centered, denominator) - target
    phase_numerator = denominator + centered

    return {
        "n": n,
        "L": odd,
        "D": denominator,
        "V": numerator,
        "M": modulus,
        "target": target,
        "S_alt": centered,
        "eta": error,
        "r_alt": phase_numerator,
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    endpoints = build_endpoints()

    null_identity_checks = 0
    fixed_level_permutation_checks = 0
    for exponent in range(1, 11):
        require(f_mod(0, exponent) == 0,
                f"finite residue of F(0) at precision={exponent}")
        values = {
            f_mod(7 * n + 1, exponent)
            for n in range(1 << exponent)
        }
        require(len(values) == 1 << exponent,
                f"fixed-level permutation at precision={exponent}")
        null_identity_checks += 1
        fixed_level_permutation_checks += 1 << exponent

    diagonal_checks = 0
    recurrence_checks = 0
    adversarial_selector_checks = 0
    states = {
        n: diagonal_state(endpoints[n])
        for n in range(1, DIAGONAL_MAX_N + 1)
    }

    for n, state in states.items():
        endpoint = endpoints[n]
        modulus = 2 ** (27 * n)
        numerator = 5**n * endpoint["A"]
        residue = numerator % modulus
        forbidden = (
            (numerator - residue) * pow(modulus, -1, endpoint["L"])
            % endpoint["L"]
        )
        for offset in (Fraction(0), Fraction(1, 3), Fraction(-1, 3)):
            chosen = nearest_shift_changing_odd_class(
                Fraction(forbidden) + offset,
                residue,
                numerator,
                modulus,
                endpoint["L"],
            )
            require((chosen - forbidden) % endpoint["L"] != 0,
                    f"adversarial odd-class avoidance at n={n}")
            adversarial_selector_checks += 1
        for extra in (0, 5):
            exponent = 27 * n + extra
            require(
                f_mod(7 * n + 1, exponent)
                == rational_mod(Fraction(endpoint["A"], endpoint["L"]), exponent),
                f"exact reflected-tail identity modulo 2^{exponent} at n={n}",
            )
            null_identity_checks += 1
        require(
            valuation_two(endpoint["A"]) == valuation_two(7 * n + 1),
            f"selected numerator valuation at n={n}",
        )
        diagonal_checks += 4

        if n == DIAGONAL_MAX_N:
            continue
        following = states[n + 1]
        order = int(state["order"])
        next_order = int(following["order"])
        coordinate = int(state["w"])
        next_coordinate = int(following["w"])
        f_value = Fraction(state["F"])
        next_f_value = Fraction(following["F"])

        increment = sum(
            16 ** (7 - j) * coefficient(7 * n + j)
            for j in range(1, 8)
        )
        require(next_f_value == 16**7 * f_value + increment,
                f"seven-step functional equation at n={n}")

        bracket_exponent = 27 * (n + 1)
        alpha = rational_mod(Fraction(5 ** (n + 1)) * increment,
                             bracket_exponent)
        bracket = (
            alpha + 5 * (1 << (28 + order)) * coordinate
        ) % (1 << bracket_exponent)
        require(bracket % (1 << next_order) == 0,
                f"normalized carry divisibility at n={n}")
        require(bracket >> next_order == next_coordinate,
                f"complete high-dyadic recurrence at n={n}")
        recurrence_checks += 3

    deep_bbp = rational_bbp(endpoints[DEEP_N])
    separator = {
        n: separator_state(endpoints[n], deep_bbp)
        for n in range(SEPARATOR_START_N, SEPARATOR_MAX_N + 1)
    }
    separator_state_checks = 0
    separator_transition_checks = 0
    color_checks = 0
    largest_log10_relative_tail_error = float("-inf")
    largest_log10_relative_forcing_error = float("-inf")

    for n, state in separator.items():
        denominator = int(state["D"])
        numerator = int(state["V"])
        modulus = int(state["M"])
        centered = int(state["S_alt"])
        phase_numerator = int(state["r_alt"])
        target = Fraction(state["target"])
        error = Fraction(state["eta"])

        require(-denominator < 2 * centered < 0,
                f"negative centered representative at n={n}")
        require(0 < phase_numerator < denominator,
                f"phase numerator range at n={n}")
        require((centered - numerator) % modulus == 0,
                f"complete dyadic state class at n={n}")
        require((phase_numerator - numerator) % modulus == 0,
                f"complete dyadic phase class at n={n}")
        require(abs(error) <= Fraction(3, 2 * int(state["L"])),
                f"nearest admissible full-dyadic grid error at n={n}")
        require((centered - numerator) % int(state["L"]) != 0,
                f"odd selected residue deliberately differs at n={n}")
        require(valuation_two(centered) == valuation_two(numerator),
                f"exact centered two-adic order at n={n}")
        require(valuation_two(phase_numerator) == valuation_two(numerator),
                f"exact phase two-adic order at n={n}")
        separator_state_checks += 8

        if error:
            largest_log10_relative_tail_error = max(
                largest_log10_relative_tail_error,
                log10_abs_fraction(error / target),
            )

        for period in PERIODS:
            q = 10**period - 1
            q_centered = Fraction(q * centered, denominator)
            require(Fraction(-1, 2) < q_centered < 0,
                    f"fixed-period centered cell P={period}, n={n}")
            color = nearest_ratio(q * phase_numerator, denominator)
            require(color == q,
                    f"all-nine boundary color P={period}, n={n}")
            color_checks += 2

    for n in range(SEPARATOR_START_N, SEPARATOR_MAX_N):
        current = separator[n]
        following = separator[n + 1]
        endpoint = endpoints[n + 1]
        denominator = int(current["D"])
        next_denominator = int(following["D"])
        dilation = next_denominator // denominator
        require(dilation == 2**27 * endpoint["R"],
                f"sevenfold denominator dilation at n={n}")

        actual_forcing = (
            int(following["V"]) - 10 * dilation * int(current["V"])
        )
        require(actual_forcing == 5 ** (n + 1) * endpoint["H"],
                f"actual forcing at n={n}")
        alternative_forcing = (
            int(following["S_alt"])
            - 10 * dilation * int(current["S_alt"])
        )
        require(alternative_forcing > 0,
                f"positive alternative forcing at n={n}")

        next_modulus = int(following["M"])
        require((alternative_forcing - actual_forcing) % next_modulus == 0,
                f"complete next-depth dyadic forcing class at n={n}")

        delta = Fraction(actual_forcing, next_denominator)
        delta_alt = Fraction(alternative_forcing, next_denominator)
        current_error = Fraction(current["eta"])
        next_error = Fraction(following["eta"])
        require(delta_alt - delta == next_error - 10 * current_error,
                f"forcing coboundary at n={n}")
        forcing_error = abs((delta_alt - delta) / delta)
        if forcing_error:
            largest_log10_relative_forcing_error = max(
                largest_log10_relative_forcing_error,
                log10_abs_fraction(forcing_error),
            )

        phase_step = (
            10 * dilation * int(current["r_alt"]) + alternative_forcing
            - int(following["r_alt"])
        )
        require(phase_step == 9 * next_denominator,
                f"phase quotient nine at n={n}")
        for period in PERIODS:
            q = 10**period - 1
            current_color = nearest_ratio(
                q * int(current["r_alt"]), denominator
            )
            next_color = nearest_ratio(
                q * int(following["r_alt"]), next_denominator
            )
            carry = q * 9 + next_color - 10 * current_color
            require(carry == 0,
                    f"zero colored carry P={period}, n={n}")
            color_checks += 1
        separator_transition_checks += 6

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "report_claim_label": "proof sketch",
        "diagonal_depth_range": [1, DIAGONAL_MAX_N],
        "separator_depth_range": [SEPARATOR_START_N, SEPARATOR_MAX_N],
        "rational_tail_cutoff": DEEP_N,
        "null_identity_checks": null_identity_checks,
        "fixed_level_permutation_checks": fixed_level_permutation_checks,
        "complete_diagonal_coordinate_checks": diagonal_checks,
        "seven_step_recurrence_checks": recurrence_checks,
        "adversarial_selector_checks": adversarial_selector_checks,
        "separator_state_checks": separator_state_checks,
        "separator_transition_checks": separator_transition_checks,
        "color_and_zero_carry_checks": color_checks,
        "largest_log10_relative_tail_error": largest_log10_relative_tail_error,
        "largest_log10_relative_forcing_error": largest_log10_relative_forcing_error,
        "preserves_complete_dyadic_selected_coordinate": True,
        "preserves_complete_next_dyadic_forcing_class": True,
        "preserves_odd_selected_coordinate": False,
        "asserts_actual_bbp_carries_are_zero": False,
        "asserts_all_color_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
