#!/usr/bin/env python3
"""Exact replay for the coefficient-specific dyadic diagonal recurrence.

The all-index claims in the companion note are elementary rational and
two-adic identities.  Every bounded statistic printed here has claim label
``experiment``; in particular, finite discrepancy and cell coverage do not
prove a return or any assertion about decimal digits of pi.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
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
}

MAX_FIXED_PRECISION = 10
MAX_DIRECT_DEPTH = 80
MAX_DIAGONAL_DEPTH = 2048
PHASE_SAMPLE_DEPTHS = set(range(1, 161)) | {255, 511, 1023, 2047}


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


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def rational_mod(value: Fraction, exponent: int) -> int:
    require(exponent >= 1, "positive two-adic precision required")
    require(value.denominator & 1 == 1, "denominator must be odd")
    modulus = 1 << exponent
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def f_mod(x: int, exponent: int) -> int:
    """Evaluate F(x)=sum_j 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    return sum(
        pow(16, j, modulus)
        * rational_mod(coefficient(x - 1 - j), exponent)
        for j in range((exponent - 1) // 4 + 1)
    ) % modulus


def z_mod_direct(n: int, exponent: int) -> int:
    modulus = 1 << exponent
    return pow(5, n, modulus) * f_mod(7 * n + 1, exponent) % modulus


def block_fraction(n: int) -> Fraction:
    """G_n from the sevenfold functional equation."""
    return sum(
        Fraction(
            16 ** (7 - j) * coefficient_numerator(7 * n + j),
            coefficient_denominator(7 * n + j),
        )
        for j in range(1, 8)
    )


def forcing_terms(n: int) -> list[tuple[int, int]]:
    """Return numerator/odd-denominator pairs for b_n=5^(n+1) G_n."""
    return [
        (
            5 ** (n + 1)
            * 16 ** (7 - j)
            * coefficient_numerator(7 * n + j),
            coefficient_denominator(7 * n + j),
        )
        for j in range(1, 8)
    ]


def forcing_mod_and_phases(
    n: int, exponent: int
) -> tuple[int, list[tuple[int, int, int, int]]]:
    """Return [b_n] and rows (p,d,residue,h) with d*residue-p=h*2^K."""
    modulus = 1 << exponent
    rows: list[tuple[int, int, int, int]] = []
    residue_sum = 0
    for numerator, denominator in forcing_terms(n):
        require(denominator & 1 == 1, f"odd forcing denominator at n={n}")
        require(numerator < modulus, f"term numerator below diagonal modulus at n={n}")
        residue = numerator * pow(denominator, -1, modulus) % modulus
        difference = denominator * residue - numerator
        require(difference % modulus == 0, f"integral phase lift at n={n}")
        height = difference // modulus
        require(0 <= height < denominator, f"canonical phase height at n={n}")
        rows.append((numerator, denominator, residue, height))
        residue_sum += residue
    return residue_sum % modulus, rows


def exact_star_discrepancy(
    values: list[int], exponents: list[int]
) -> tuple[int, int]:
    """Return numerator/denominator of star discrepancy for dyadic points."""
    require(values and len(values) == len(exponents), "aligned nonempty points")
    common_exponent = max(exponents)
    common_modulus = 1 << common_exponent
    scaled = sorted(
        value << (common_exponent - exponent)
        for value, exponent in zip(values, exponents, strict=True)
    )
    count = len(scaled)
    discrepancy_numerator = 0
    for index, value in enumerate(scaled):
        discrepancy_numerator = max(
            discrepancy_numerator,
            (index + 1) * common_modulus - count * value,
            count * value - index * common_modulus,
        )
    return discrepancy_numerator, count * common_modulus


def decimal_ratio(numerator: int, denominator: int) -> str:
    getcontext().prec = 30
    return str(Decimal(numerator) / Decimal(denominator))


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    fixed_level_checks = 0
    mod_four_values: list[int] = []
    for exponent in range(1, MAX_FIXED_PRECISION + 1):
        modulus = 1 << exponent
        ordered_values = [z_mod_direct(n, exponent) for n in range(modulus)]
        require(set(ordered_values) == set(range(modulus)),
                f"fixed-level selected-coordinate permutation at s={exponent}")
        if exponent == 2:
            mod_four_values = ordered_values
        fixed_level_checks += modulus
    require(mod_four_values == [1, 0, 3, 2],
            "the p-adic selected map has two cycles modulo four")

    first_modulus = 1 << 27
    state = z_mod_direct(1, 27)
    diagonal_values: list[int] = []
    diagonal_exponents: list[int] = []
    forcing_values: list[int] = []
    forcing_exponents: list[int] = []

    direct_checks = 0
    recurrence_checks = 0
    phase_lift_checks = 0
    phase_decomposition_checks = 0
    phase_error_bound_checks = 0
    exact_valuation_checks = 0
    denominator_height_checks = 0

    for n in range(1, MAX_DIAGONAL_DEPTH + 1):
        exponent = 27 * n
        modulus = 1 << exponent
        require(0 < state < modulus, f"canonical nonzero diagonal state n={n}")
        require(
            valuation_two(state) == valuation_two(7 * n + 1),
            f"exact diagonal valuation n={n}",
        )
        exact_valuation_checks += 1
        if n <= MAX_DIRECT_DEPTH:
            require(state == z_mod_direct(n, exponent),
                    f"direct F evaluation agrees at n={n}")
            direct_checks += 1

        diagonal_values.append(state)
        diagonal_exponents.append(exponent)
        if n == MAX_DIAGONAL_DEPTH:
            break

        next_exponent = exponent + 27
        next_modulus = 1 << next_exponent
        forcing_residue, phase_rows = forcing_mod_and_phases(n, next_exponent)
        forcing_values.append(forcing_residue)
        forcing_exponents.append(next_exponent)

        residue_sum = 0
        for numerator, denominator, residue, height in phase_rows:
            require(
                denominator * residue - numerator == height * next_modulus,
                f"exact seven-phase identity n={n}",
            )
            require(
                denominator
                <= 15 * 31 * 57 * 61 * (n + 1) ** 4,
                f"quartic phase-denominator bound n={n}",
            )
            residue_sum += residue
            phase_lift_checks += 1
            denominator_height_checks += 1
        require(residue_sum % next_modulus == forcing_residue,
                f"phase residues sum to forcing n={n}")

        if n in PHASE_SAMPLE_DEPTHS:
            forcing = 5 ** (n + 1) * block_fraction(n)
            theta = sum(
                Fraction(height, denominator)
                for _, denominator, _, height in phase_rows
            )
            gamma = Fraction(forcing_residue, next_modulus)
            require((theta + forcing / next_modulus - gamma).denominator == 1,
                    f"exact circle phase decomposition n={n}")
            bound = Fraction(
                (16 ** 7 - 1) * 5 ** (n + 1),
                15 * (7 * n + 1) ** 2 * next_modulus,
            )
            require(0 < forcing / next_modulus <= bound,
                    f"exponential phase-error bound n={n}")
            phase_decomposition_checks += 1
            phase_error_bound_checks += 1

        next_state = (
            5 * (1 << 28) * state + forcing_residue
        ) % next_modulus
        require(
            next_state
            == (10 * (1 << 27) * state + forcing_residue) % next_modulus,
            f"normalized decimal multiplier n={n}",
        )
        state = next_state
        recurrence_checks += 1

    require(len(diagonal_values) == MAX_DIAGONAL_DEPTH,
            "complete diagonal sample")
    require(len(forcing_values) == MAX_DIAGONAL_DEPTH - 1,
            "complete forcing sample")

    # The first two moving-diagonal points lie in the same quarter.  This is
    # an exact counterexample to importing fixed-level permutation counts to
    # the leading moving-diagonal bits.
    first_cells = [
        value >> (exponent - 2)
        for value, exponent in zip(
            diagonal_values[:2], diagonal_exponents[:2], strict=True
        )
    ]
    require(first_cells == [1, 1], "exact first-quarter collision")

    twelfth_forcing = Fraction(forcing_values[11], 1 << forcing_exponents[11])
    require(twelfth_forcing > Fraction(98, 100),
            "the n=12 two-adic forcing phase is macroscopic")
    twelfth_real_error = (
        5 ** 13 * block_fraction(12) / (1 << (27 * 13))
    )
    require(twelfth_real_error < Fraction(1, 10**90),
            "the n=12 real forcing correction is tiny")

    prefix_coverage: dict[str, int] = {}
    prefix_missing_first: dict[str, list[int]] = {}
    for precision in (1, 2, 8, 9, 10, 11):
        cells = {
            value >> (exponent - precision)
            for value, exponent in zip(
                diagonal_values, diagonal_exponents, strict=True
            )
        }
        missing = sorted(set(range(1 << precision)) - cells)
        prefix_coverage[str(precision)] = len(cells)
        prefix_missing_first[str(precision)] = missing[:5]

    leading_bits = [
        value >> (exponent - 1)
        for value, exponent in zip(
            diagonal_values, diagonal_exponents, strict=True
        )
    ]
    longest_run = 1
    longest_run_start = 1
    longest_run_bit = leading_bits[0]
    run_start = 0
    for index in range(1, len(leading_bits) + 1):
        if index == len(leading_bits) or leading_bits[index] != leading_bits[run_start]:
            if index - run_start > longest_run:
                longest_run = index - run_start
                longest_run_start = run_start + 1
                longest_run_bit = leading_bits[run_start]
            run_start = index

    diagonal_discrepancy = exact_star_discrepancy(
        diagonal_values, diagonal_exponents
    )
    forcing_discrepancy = exact_star_discrepancy(
        forcing_values, forcing_exponents
    )

    common_exponent = diagonal_exponents[-1]
    common_modulus = 1 << common_exponent
    minimum_boundary_numerator = min(
        min(
            value << (common_exponent - exponent),
            common_modulus - (value << (common_exponent - exponent)),
        )
        for value, exponent in zip(
            diagonal_values, diagonal_exponents, strict=True
        )
    )

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "theorem_claim_label": "proof sketch",
        "maximum_fixed_precision": MAX_FIXED_PRECISION,
        "maximum_direct_depth": MAX_DIRECT_DEPTH,
        "maximum_diagonal_depth": MAX_DIAGONAL_DEPTH,
        "fixed_level_permutation_checks": fixed_level_checks,
        "selected_map_mod_four": mod_four_values,
        "selected_map_not_ergodic_mod_four": True,
        "direct_functional_identity_checks": direct_checks,
        "diagonal_recurrence_checks": recurrence_checks,
        "seven_phase_lift_checks": phase_lift_checks,
        "phase_decomposition_checks": phase_decomposition_checks,
        "phase_error_bound_checks": phase_error_bound_checks,
        "exact_valuation_checks": exact_valuation_checks,
        "quartic_denominator_bound_checks": denominator_height_checks,
        "first_two_two_bit_cells": first_cells,
        "prefix_coverage": prefix_coverage,
        "prefix_missing_first": prefix_missing_first,
        "longest_leading_bit_run": {
            "length": longest_run,
            "start_n": longest_run_start,
            "bit": longest_run_bit,
        },
        "diagonal_star_discrepancy": decimal_ratio(*diagonal_discrepancy),
        "forcing_star_discrepancy": decimal_ratio(*forcing_discrepancy),
        "minimum_distance_to_boundary": decimal_ratio(
            minimum_boundary_numerator, common_modulus
        ),
        "twelfth_forcing_phase_above_0_98": True,
        "twelfth_real_correction_below_1e_minus_90": True,
        "asserts_diagonal_equidistribution": False,
        "asserts_target_hitting": False,
        "asserts_decimal_word_occurrence": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
