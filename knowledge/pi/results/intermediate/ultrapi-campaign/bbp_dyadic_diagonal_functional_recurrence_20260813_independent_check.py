#!/usr/bin/env python3
"""Independent exact replay of the BBP moving-dyadic recurrence audit.

This file deliberately does not import the primary checker.  It reconstructs
the BBP coefficient from the four original poles, evaluates the restricted
two-adic series directly modulo powers of two, and checks the recurrence and
the seven phase lifts with independent code.  All bounded checks are labelled
``experiment``; they do not prove a return of the decimal orbit of pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813.md":
        "5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md":
        "8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba",
    "work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py":
        "c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651",
}

MAX_FIXED_PRECISION = 11
MAX_DIRECT_RECURRENCE_DEPTH = 128
MAX_PHASE_DEPTH = 3072
PHASE_IDENTITY_DEPTHS = set(range(1, 97)) | {
    127, 255, 511, 1023, 1535, 2047, 2559, 3071
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def original_four_pole_coefficient(k: int) -> Fraction:
    """The coefficient as printed in BBP Theorem 1."""
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def collapsed_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def collapsed_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def collapsed_coefficient(k: int) -> Fraction:
    return Fraction(collapsed_numerator(k), collapsed_denominator(k))


def rational_mod(value: Fraction, exponent: int) -> int:
    require(exponent >= 1, "positive precision required")
    require(value.denominator % 2 == 1, "two-integral rational required")
    modulus = 1 << exponent
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def f_mod(x: int, exponent: int) -> int:
    """Directly truncate sum_j 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    term_count = (exponent + 3) // 4
    total = 0
    for j in range(term_count):
        total += pow(16, j, modulus) * rational_mod(
            original_four_pole_coefficient(x - 1 - j), exponent
        )
    return total % modulus


def finite_f_at_positive_integer(x: int) -> Fraction:
    """F(x), using F(0)=0 and the exact functional recurrence."""
    require(x >= 0, "nonnegative integer input required")
    return sum(
        (
            Fraction(16 ** (x - 1 - k), 1)
            * original_four_pole_coefficient(k)
        )
        for k in range(x)
    )


def z_exact(n: int) -> Fraction:
    return 5**n * finite_f_at_positive_integer(7 * n + 1)


def z_mod(n: int, exponent: int) -> int:
    modulus = 1 << exponent
    return pow(5, n, modulus) * f_mod(7 * n + 1, exponent) % modulus


def block(n: int) -> Fraction:
    return sum(
        Fraction(16 ** (7 - j), 1)
        * original_four_pole_coefficient(7 * n + j)
        for j in range(1, 8)
    )


def forcing_rows(n: int) -> list[tuple[int, int]]:
    return [
        (
            5 ** (n + 1)
            * 16 ** (7 - j)
            * collapsed_numerator(7 * n + j),
            collapsed_denominator(7 * n + j),
        )
        for j in range(1, 8)
    ]


def forcing_residue_and_lifts(
    n: int,
) -> tuple[int, list[tuple[int, int, int, int]]]:
    exponent = 27 * (n + 1)
    modulus = 1 << exponent
    lifted: list[tuple[int, int, int, int]] = []
    residue_sum = 0
    for numerator, denominator in forcing_rows(n):
        residue = numerator * pow(denominator, -1, modulus) % modulus
        difference = denominator * residue - numerator
        require(difference % modulus == 0, f"integral lift at n={n}")
        height = difference // modulus
        lifted.append((numerator, denominator, residue, height))
        residue_sum += residue
    return residue_sum % modulus, lifted


def valuation_two(value: int) -> int:
    require(value != 0, "valuation of zero is not requested")
    value = abs(value)
    return (value & -value).bit_length() - 1


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned file: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    # Reconstruct the collapsed coefficient independently from BBP's four
    # poles, including negative arguments used by the two-adic series.
    coefficient_checks = 0
    for k in range(-256, 257):
        require(
            original_four_pole_coefficient(k) == collapsed_coefficient(k),
            f"four-pole collapse at k={k}",
        )
        require(
            collapsed_coefficient(k).denominator % 2 == 1,
            f"odd reduced denominator at k={k}",
        )
        coefficient_checks += 1

    # Check the defining functional equation, including negative inputs, and
    # the frozen null value F(0)=0 to substantially higher precision than is
    # needed for the mod-four obstruction.
    functional_checks = 0
    for exponent in range(1, 65):
        modulus = 1 << exponent
        require(f_mod(0, exponent) == 0, f"frozen F(0)=0 mod 2^{exponent}")
        for x in (-129, -65, -17, -1, 0, 1, 2, 7, 31, 127):
            expected = (
                16 * f_mod(x, exponent)
                + rational_mod(original_four_pole_coefficient(x), exponent)
            ) % modulus
            require(
                f_mod(x + 1, exponent) == expected,
                f"functional equation at x={x}, exponent={exponent}",
            )
            functional_checks += 1

    # Fixed-level isometry/permutation and the exact mod-four obstruction.
    permutation_checks = 0
    mod_four: list[int] = []
    for exponent in range(1, MAX_FIXED_PRECISION + 1):
        modulus = 1 << exponent
        values = [z_mod(n, exponent) for n in range(modulus)]
        require(sorted(values) == list(range(modulus)),
                f"selected map permutation mod 2^{exponent}")
        permutation_checks += modulus
        if exponent == 2:
            mod_four = values
    require(mod_four == [1, 0, 3, 2], "exact mod-four map")
    invariant = {0, 1}
    require({mod_four[x] for x in invariant} == invariant,
            "nontrivial invariant mod-four subset")
    require({x for x in range(4) if mod_four[x] in invariant} == invariant,
            "invariant subset has equal full preimage")

    isometry_checks = 0
    offsets = [1, 2, 3, 4, 7, 8, 16, 31, 32, 63, 64, 127, 256, 1024]
    for n in [0, 1, 2, 3, 17, 255, 1024, 4097]:
        for offset in offsets:
            m = n + offset
            expected_valuation = valuation_two(offset)
            exponent = expected_valuation + 8
            difference = (z_mod(m, exponent) - z_mod(n, exponent)) % (1 << exponent)
            require(difference != 0, f"nonzero selected difference n={n}, m={m}")
            require(
                valuation_two(difference) == expected_valuation,
                f"selected isometry n={n}, m={m}",
            )
            isometry_checks += 1

    # Re-derive the rational seven-step recurrence without modular arithmetic.
    rational_recurrence_checks = 0
    for n in range(0, 33):
        require(
            z_exact(n + 1) == 5 * (1 << 28) * z_exact(n) + 5 ** (n + 1) * block(n),
            f"exact rational seven-step recurrence n={n}",
        )
        rational_recurrence_checks += 1

    # Check raw and normalized recurrences directly at independent depths.
    direct_recurrence_checks = 0
    normalized_recurrence_checks = 0
    for n in range(0, MAX_DIRECT_RECURRENCE_DEPTH + 1):
        old_exponent = 27 * n
        next_exponent = old_exponent + 27
        next_modulus = 1 << next_exponent
        old_state = 0 if n == 0 else z_mod(n, old_exponent)
        next_state = z_mod(n + 1, next_exponent)
        forcing_residue, _ = forcing_residue_and_lifts(n)
        require(
            next_state
            == (5 * (1 << 28) * old_state + forcing_residue) % next_modulus,
            f"raw diagonal recurrence n={n}",
        )
        old_modulus = 1 << old_exponent
        normalized_rhs = (
            Fraction(10 * old_state, old_modulus)
            + Fraction(forcing_residue, next_modulus)
        )
        require(
            Fraction(next_state, next_modulus) == fractional_part(normalized_rhs),
            f"normalized multiplier-ten recurrence n={n}",
        )
        direct_recurrence_checks += 1
        normalized_recurrence_checks += 1

    # The report's simple sufficient proof of canonical heights starts at
    # n=1: its p<M estimate is false at n=0.  Direct calculation shows that
    # the exact lift identity and canonical heights nevertheless also happen
    # to hold at n=0.  We record this edge case rather than extrapolating the
    # stated p<M proof outside its domain.
    modulus_zero = 1 << 27
    _, zero_rows = forcing_residue_and_lifts(0)
    zero_numerator_bound_failures = sum(
        numerator >= modulus_zero for numerator, _, _, _ in zero_rows
    )
    zero_noncanonical_heights = sum(
        not (0 <= height < denominator)
        for _, denominator, _, height in zero_rows
    )
    require(zero_numerator_bound_failures > 0, "n=0 lies outside p<M range")
    require(zero_noncanonical_heights == 0, "direct n=0 heights are canonical")

    phase_lift_checks = 0
    phase_power_checks = 0
    numerator_bound_checks = 0
    denominator_bound_checks = 0
    circle_decomposition_checks = 0
    error_bound_checks = 0
    valuation_checks = 0

    state = z_mod(1, 27)
    first_two_states: list[tuple[int, int]] = []
    for n in range(1, MAX_PHASE_DEPTH + 1):
        exponent = 27 * n
        modulus = 1 << exponent
        require(0 < state < modulus, f"canonical nonzero state n={n}")
        require(
            valuation_two(state) == valuation_two(7 * n + 1),
            f"complete-coordinate valuation n={n}",
        )
        valuation_checks += 1
        if n <= 2:
            first_two_states.append((state, exponent))
        if n == MAX_PHASE_DEPTH:
            break

        next_exponent = exponent + 27
        next_modulus = 1 << next_exponent
        forcing_residue, rows = forcing_residue_and_lifts(n)
        residue_sum = 0
        for j, (numerator, denominator, residue, height) in enumerate(rows, start=1):
            k = 7 * n + j
            require(
                denominator * residue - numerator == height * next_modulus,
                f"exact phase lift n={n}, j={j}",
            )
            require(0 <= height < denominator,
                    f"canonical phase height n={n}, j={j}")
            require(numerator < next_modulus,
                    f"phase numerator below modulus n={n}, j={j}")
            crude_bound = (1 << (3 * (n + 1) + 38)) * (n + 1) ** 2
            require(numerator < crude_bound,
                    f"stated crude numerator bound n={n}, j={j}")
            require(
                denominator <= 15 * 31 * 57 * 61 * (n + 1) ** 4,
                f"quartic denominator bound n={n}, j={j}",
            )
            phase_base = (5 * pow(1 << 27, -1, denominator)) % denominator
            expected_height = (
                -collapsed_numerator(k)
                * pow(2, 4 * (7 - j), denominator)
                * pow(phase_base, n + 1, denominator)
            ) % denominator
            require(
                height % denominator == expected_height,
                f"varying-modulus power phase n={n}, j={j}",
            )
            residue_sum += residue
            phase_lift_checks += 1
            phase_power_checks += 1
            numerator_bound_checks += 1
            denominator_bound_checks += 1
        require(residue_sum % next_modulus == forcing_residue,
                f"sum of seven forcing residues n={n}")

        if n in PHASE_IDENTITY_DEPTHS:
            theta = sum(
                Fraction(height, denominator)
                for _, denominator, _, height in rows
            )
            forcing = 5 ** (n + 1) * block(n)
            epsilon = forcing / next_modulus
            gamma = Fraction(forcing_residue, next_modulus)
            require(
                fractional_part(theta + epsilon) == gamma,
                f"exact circle decomposition n={n}",
            )
            bound = Fraction(
                (16**7 - 1) * 5 ** (n + 1),
                15 * (7 * n + 1) ** 2 * next_modulus,
            )
            require(0 < epsilon <= bound, f"phase error bound n={n}")
            circle_decomposition_checks += 1
            error_bound_checks += 1

        state = (
            5 * (1 << 28) * state + forcing_residue
        ) % next_modulus

    first_two_quarters = [
        value >> (exponent - 2) for value, exponent in first_two_states
    ]
    require(first_two_quarters == [1, 1], "first moving states share one quarter")

    forcing_12, rows_12 = forcing_residue_and_lifts(12)
    gamma_12 = Fraction(forcing_12, 1 << (27 * 13))
    epsilon_12 = 5**13 * block(12) / (1 << (27 * 13))
    require(gamma_12 > Fraction(98, 100), "macroscopic n=12 forcing phase")
    require(epsilon_12 < Fraction(1, 10**90), "tiny n=12 real correction")
    require(len(rows_12) == 7, "seven n=12 phase rows")

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "audited_theorem_claim_label": "proof sketch",
        "coefficient_reconstruction_checks": coefficient_checks,
        "functional_equation_checks": functional_checks,
        "maximum_fixed_precision": MAX_FIXED_PRECISION,
        "fixed_level_permutation_checks": permutation_checks,
        "isometry_spot_checks": isometry_checks,
        "selected_map_mod_four": mod_four,
        "mod_four_invariant_subset": [0, 1],
        "rational_seven_step_recurrence_checks": rational_recurrence_checks,
        "direct_diagonal_recurrence_checks": direct_recurrence_checks,
        "normalized_multiplier_ten_checks": normalized_recurrence_checks,
        "maximum_phase_depth": MAX_PHASE_DEPTH,
        "seven_phase_lift_checks": phase_lift_checks,
        "varying_modulus_power_checks": phase_power_checks,
        "numerator_bound_checks": numerator_bound_checks,
        "quartic_denominator_bound_checks": denominator_bound_checks,
        "circle_decomposition_checks": circle_decomposition_checks,
        "phase_error_bound_checks": error_bound_checks,
        "complete_coordinate_valuation_checks": valuation_checks,
        "n_zero_numerator_bound_failures": zero_numerator_bound_failures,
        "n_zero_noncanonical_heights": zero_noncanonical_heights,
        "first_two_two_bit_cells": first_two_quarters,
        "twelfth_forcing_phase_above_0_98": True,
        "twelfth_real_correction_below_1e_minus_90": True,
        "asserts_diagonal_equidistribution": False,
        "asserts_target_hitting": False,
        "asserts_decimal_word_occurrence": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
