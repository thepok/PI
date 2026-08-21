#!/usr/bin/env python3
"""Exact bounded checks for the Peres--Yang/BBP endpoint comparison.

All mathematical conclusions extracted from the finite endpoint row have
label ``experiment``.  The script does not assert an asymptotic gap bound,
Fourier decay, a fixed return, or V1.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/fresh_special_value_fractal_literature_20260813.md":
        "0852d12d67609fffae963f49369643b2378e319852f0e13eabf716581725abfe",
    "work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813.md":
        "6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md":
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    "work/theory/pi-lacunary-near-return-sparsity/library/t181/peres-yang-2606.28860v1.pdf":
        "bbfbd8b3cbcb0e4523873142eea72326f8d729c4cb2eeb58104741828688ac24",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def v_p(n: int, p: int) -> int:
    out = 0
    while n % p == 0:
        out += 1
        n //= p
    return out


def floor_log10_int(n: int) -> int:
    # Exact for positive integers, with no floating logarithm.
    return len(str(n)) - 1


def bbp_partial_sum(depth: int) -> Fraction:
    total = Fraction(0)
    pow16 = 1
    for k in range(depth + 1):
        numerator = 120 * k * k + 151 * k + 47
        denominator = (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)
        total += Fraction(numerator, denominator * pow16)
        pow16 *= 16
    return total


def circle_gap_numerators(residues: list[int], denominator: int) -> Fraction:
    ordered = sorted(set(residues))
    assert ordered
    gaps = [ordered[i + 1] - ordered[i] for i in range(len(ordered) - 1)]
    gaps.append(denominator - ordered[-1] + ordered[0])
    return Fraction(max(gaps), denominator)


def primary_grid_size(numerator: int, denominator: int, start: int, period: int,
                      three_exponent: int) -> int:
    modulus = 3 ** three_exponent
    assert denominator % modulus == 0
    coefficient = numerator * pow(denominator // modulus, -1, modulus) % modulus
    reduced_modulus = modulus // 3
    values = {
        (((10 ** n - 16) // 3) * coefficient) % reduced_modulus
        for n in range(start, start + period)
    }
    return len(values)


def main() -> None:
    for rel, expected in PINS.items():
        actual = sha256(ROOT / rel)
        assert actual == expected, (rel, expected, actual)

    # Last pre-drop row at the even three-adic epoch e=6.
    e = 6
    endpoint_a = (3 ** e - 1) // 8
    depth = 5 * endpoint_a - 1
    assert depth == 454
    bbp = bbp_partial_sum(depth)
    numerator, denominator = bbp.numerator, bbp.denominator
    assert math.gcd(numerator, denominator) == 1

    k_two = 4 * depth - v_p(depth + 1, 2)
    assert k_two == 1816
    assert denominator % (1 << k_two) == 0
    odd_denominator = denominator >> k_two
    assert odd_denominator % 2 == 1
    assert v_p(odd_denominator, 3) == e

    upper = floor_log10_int(16 ** depth)
    length = upper - depth + 1
    period = 3 ** (e - 2)
    assert (upper, length, period) == (546, 93, 81)

    actual_residues = [
        ((10 ** n - 16) * numerator) % denominator
        for n in range(depth, upper + 1)
    ]
    assert len(set(actual_residues)) == length
    actual_gap = circle_gap_numerators(actual_residues, denominator)
    assert Fraction(43, 1000) < actual_gap < Fraction(44, 1000)

    # Exact equal-cell DFT criterion at K=floor(L/log L)=20.
    cell_count = int(length / math.log(length))
    assert cell_count == 20
    labels = [(cell_count * r) // denominator for r in actual_residues]
    histogram = [labels.count(a) for a in range(cell_count)]
    assert sum(histogram) == length
    assert min(histogram) == 2
    assert max(histogram) == 7
    assert histogram == [6, 4, 7, 3, 5, 3, 4, 7, 3, 7,
                         2, 5, 5, 7, 3, 2, 3, 4, 6, 7]

    transforms = [
        sum(cmath.exp(2j * math.pi * h * q / cell_count) for q in labels)
        for h in range(cell_count)
    ]
    inverse_error = 0.0
    for a in range(cell_count):
        recovered = sum(
            transforms[h] * cmath.exp(-2j * math.pi * h * a / cell_count)
            for h in range(cell_count)
        ) / cell_count
        inverse_error = max(inverse_error, abs(recovered - histogram[a]))
    assert inverse_error < 1e-10

    # Parseval in exact integer form.  If one cell were empty, Cauchy gives
    # nonzero Fourier energy at least L^2/(K-1).  The actual energy is above
    # that threshold, hence energy alone cannot certify its observed cover.
    actual_energy = cell_count * sum(c * c for c in histogram) - length * length
    empty_threshold = Fraction(length * length, cell_count - 1)
    assert actual_energy == 1211
    assert actual_energy > empty_threshold

    quotient, remainder = divmod(length, cell_count - 1)
    balanced_empty = [0] + [quotient + 1] * remainder + [quotient] * (
        cell_count - 1 - remainder
    )
    assert len(balanced_empty) == cell_count
    assert sum(balanced_empty) == length
    assert min(balanced_empty) == 0
    empty_energy = cell_count * sum(c * c for c in balanced_empty) - length * length
    assert empty_energy == 491
    assert empty_energy > empty_threshold

    # Same exact denominator and unit numerator, but a nearly collapsed row.
    one_upper = Fraction(10 ** upper - 16, denominator)
    assert one_upper < Fraction(1, 10 ** 1186)
    assert primary_grid_size(1, denominator, depth, period, e) == period

    # Preserve every actual odd CRT numerator residue, including all actual
    # high-prime and three-primary coordinates; change only the dyadic one.
    odd_preserving_numerator = numerator % odd_denominator
    if odd_preserving_numerator % 2 == 0:
        odd_preserving_numerator += odd_denominator
    assert 0 < odd_preserving_numerator < 2 * odd_denominator
    assert odd_preserving_numerator % odd_denominator == numerator % odd_denominator
    assert math.gcd(odd_preserving_numerator, denominator) == 1
    odd_arc_upper = Fraction(
        (10 ** upper - 16) * odd_preserving_numerator, denominator
    )
    assert odd_arc_upper < Fraction(83, 1000)
    assert primary_grid_size(
        odd_preserving_numerator, denominator, depth, period, e
    ) == period

    # Preserve the complete actual dyadic numerator coordinate; change the
    # odd coordinates.  The first coprime lift occurs at t=3 and is still
    # so small that the whole row is contained in an arc shorter than 10^-639.
    dyadic_modulus = 1 << k_two
    dyadic_residue = numerator % dyadic_modulus
    lift = 0
    while math.gcd(dyadic_residue + lift * dyadic_modulus, odd_denominator) != 1:
        lift += 1
    assert lift == 3
    dyadic_preserving_numerator = dyadic_residue + lift * dyadic_modulus
    assert dyadic_preserving_numerator % dyadic_modulus == numerator % dyadic_modulus
    assert math.gcd(dyadic_preserving_numerator, denominator) == 1
    dyadic_arc_upper = Fraction(
        (10 ** upper - 16) * dyadic_preserving_numerator, denominator
    )
    assert dyadic_arc_upper < Fraction(1, 10 ** 639)

    # Quantitative size behind the discrete-selector obstruction.
    reduced_start_dyadic_exponent = k_two - depth
    finest_row_dyadic_exponent = k_two - depth - (length - 1)
    assert reduced_start_dyadic_exponent == 1362
    assert finest_row_dyadic_exponent == 1270
    assert (1 << finest_row_dyadic_exponent) > 10 ** 380

    record_lines = [
        "bounded_claim_label=experiment",
        "analytic_claim_label=proof sketch",
        "literature_claim_label=literature-checked",
        f"endpoint=e{e}-pre-drop-M{depth}",
        f"upper_exponent={upper}",
        f"row_length={length}",
        f"three_primary_period={period}",
        f"denominator_decimal_digits={len(str(denominator))}",
        f"odd_denominator_decimal_digits={len(str(odd_denominator))}",
        f"actual_gap_float={float(actual_gap):.15g}",
        f"cell_count={cell_count}",
        f"cell_histogram={','.join(map(str, histogram))}",
        f"cell_minimum={min(histogram)}",
        f"cell_dft_inverse_max_error={inverse_error:.3e}",
        f"actual_nonzero_dft_energy={actual_energy}",
        f"empty_energy_threshold={empty_threshold}",
        f"balanced_empty_nonzero_dft_energy={empty_energy}",
        "same_denominator_unit_row_arc_upper_lt=10^-1186",
        "same_denominator_unit_row_full_three_grid=true",
        "odd_crt_preserving_row_arc_upper_lt=83/1000",
        "odd_crt_preserving_row_gap_lower_gt=917/1000",
        "odd_crt_preserving_row_full_three_grid=true",
        f"dyadic_preserving_first_coprime_lift={lift}",
        "dyadic_preserving_row_arc_upper_lt=10^-639",
        f"finest_row_dyadic_exponent={finest_row_dyadic_exponent}",
        "asserts_endpoint_gap_law=false",
        "asserts_fixed_return=false",
        "asserts_v1=false",
    ]
    record = "\n".join(record_lines) + "\n"
    print(record, end="")
    print(f"exact_record_sha256={hashlib.sha256(record.encode()).hexdigest()}")
    print("status=PASS")


if __name__ == "__main__":
    main()
