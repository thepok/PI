#!/usr/bin/env python3
"""Disjoint bounded replay for the Peres--Yang/BBP endpoint audit.

This checker does not import the primary checker.  Its finite conclusions have
label ``experiment``.  It asserts no almost-everywhere theorem, fixed-pi
return, endpoint asymptotic, or V1 statement.
"""

from __future__ import annotations

import hashlib
import math
import re
from fractions import Fraction
from pathlib import Path

import mpmath as mp


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813.md":
        "3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_check.py":
        "121fad4ba825591d701b4156c6a570962e0609173b875d9b9fe5246afb0a8bcb",
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
    "work/theory/pi-lacunary-near-return-sparsity/library/t181/peres-yang-2606.28860v1.txt":
        "9591c2cc7b37e2c643301df0aad7e9f3a96218605ecd70cd0fa88483603c30d7",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(n: int, prime: int) -> int:
    exponent = 0
    while n % prime == 0:
        exponent += 1
        n //= prime
    return exponent


def bbp_four_pole_prefix(last_index: int) -> Fraction:
    """Use the classical four fractions, not the primary combined summand."""
    answer = Fraction(0)
    scale = 1
    for k in range(last_index + 1):
        bracket = (
            Fraction(4, 8 * k + 1)
            - Fraction(2, 8 * k + 4)
            - Fraction(1, 8 * k + 5)
            - Fraction(1, 8 * k + 6)
        )
        answer += bracket / scale
        scale *= 16
    return answer


def circular_gap(residues: list[int], modulus: int) -> Fraction:
    points = sorted(set(residues))
    forward = [b - a for a, b in zip(points, points[1:])]
    forward.append(modulus + points[0] - points[-1])
    return Fraction(max(forward), modulus)


def orbit(numerator: int, modulus: int, first: int, last: int) -> list[int]:
    return [((pow(10, n, modulus) - 16) * numerator) % modulus
            for n in range(first, last + 1)]


def three_primary_coordinates(
    numerator: int, modulus: int, first: int, count: int, exponent: int
) -> set[int]:
    primary_modulus = 3 ** exponent
    cofactor = modulus // primary_modulus
    cofactor_inverse = pow(cofactor, -1, primary_modulus)
    return {
        ((pow(10, n, primary_modulus) - 16)
         * numerator * cofactor_inverse) % primary_modulus
        for n in range(first, first + count)
    }


def verify_primary_hygiene() -> int:
    primary = ROOT / "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813.md"
    raw = primary.read_bytes()
    bad_controls = [byte for byte in raw if byte < 32 and byte not in (9, 10)]
    assert not bad_controls

    text = raw.decode("utf-8")
    local_links = []
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if "://" in target or target.startswith("#"):
            continue
        clean = target.split("#", 1)[0]
        if clean:
            resolved = (primary.parent / clean).resolve()
            assert resolved.exists(), (target, resolved)
            local_links.append(target)
    return len(local_links)


def verify_source_markers() -> None:
    source = (ROOT / "problems/local/pi-digits.txt").read_text()
    assert "every finite sequence of decimal digits" in source.lower()

    paper = (ROOT / "work/theory/pi-lacunary-near-return-sparsity/library/t181/"
             "peres-yang-2606.28860v1.txt").read_text()
    for marker in (
        "Theorem 1.2 (Divisibility chains)",
        "Proposition 5.2 (No-hit estimate for regular intervals)",
        "the digits (ξj )j≥1 are independent",
        "Proposition 5.7 (Uniform avoidance for separated targets)",
        "Borel–Cantelli, followed by the interpolation argument",
    ):
        assert marker in paper


def main() -> None:
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        assert actual == expected, (relative, expected, actual)

    local_link_count = verify_primary_hygiene()
    verify_source_markers()

    # The e=6 pre-drop endpoint is M=5(3^e-1)/8-1=454.
    e = 6
    depth = 5 * ((3 ** e - 1) // 8) - 1
    assert depth == 454
    prefix = bbp_four_pole_prefix(depth)
    numerator = prefix.numerator
    denominator = prefix.denominator
    assert math.gcd(numerator, denominator) == 1

    two_exponent = valuation(denominator, 2)
    odd_denominator = denominator >> two_exponent
    assert two_exponent == 4 * depth - valuation(depth + 1, 2) == 1816
    assert valuation(odd_denominator, 3) == e
    assert len(str(denominator)) == 1733
    assert len(str(odd_denominator)) == 1187

    upper = len(str(16 ** depth)) - 1
    row_length = upper - depth + 1
    three_period = 3 ** (e - 2)
    assert (upper, row_length, three_period) == (546, 93, 81)

    actual_row = orbit(numerator, denominator, depth, upper)
    assert len(set(actual_row)) == row_length
    actual_gap = circular_gap(actual_row, denominator)
    assert Fraction(43, 1000) < actual_gap < Fraction(44, 1000)

    # Exact equal-cell data; high-precision roots of unity merely replay the
    # integer histogram and are never used as a proof of an asymptotic claim.
    cells = math.floor(row_length / math.log(row_length))
    assert cells == 20
    labels = [(cells * residue) // denominator for residue in actual_row]
    histogram = [0] * cells
    for label in labels:
        histogram[label] += 1
    assert histogram == [6, 4, 7, 3, 5, 3, 4, 7, 3, 7,
                         2, 5, 5, 7, 3, 2, 3, 4, 6, 7]
    assert min(histogram) == 2

    mp.mp.dps = 100
    root = mp.e ** (2j * mp.pi / cells)
    coefficients = [
        sum(histogram[a] * root ** (h * a) for a in range(cells))
        for h in range(cells)
    ]
    reconstruction_error = max(
        abs(sum(coefficients[h] * root ** (-h * a)
                for h in range(cells)) / cells - histogram[a])
        for a in range(cells)
    )
    assert reconstruction_error < mp.mpf("1e-90")
    signed_troughs = [cells * count - row_length for count in histogram]
    assert min(signed_troughs) == -53 > -row_length

    energy = cells * sum(count * count for count in histogram) - row_length ** 2
    empty_threshold = Fraction(row_length ** 2, cells - 1)
    assert energy == 1211 > empty_threshold == Fraction(8649, 19)

    balanced_empty = [0] + [5] * 17 + [4] * 2
    balanced_energy = (
        cells * sum(count * count for count in balanced_empty) - row_length ** 2
    )
    assert sum(balanced_empty) == row_length
    assert balanced_energy == 491 > empty_threshold

    # Stronger disjoint falsifier: an empty histogram can have exactly the
    # same total and exactly the same nonzero DFT energy as the covered row.
    isospectral_empty = [6] * 6 + [5] * 11 + [1] * 2 + [0]
    assert len(isospectral_empty) == cells
    assert sum(isospectral_empty) == row_length
    assert min(isospectral_empty) == 0
    isospectral_energy = (
        cells * sum(count * count for count in isospectral_empty)
        - row_length ** 2
    )
    assert isospectral_energy == energy == 1211

    # Three same-denominator numerators.  Direct orbit gaps and direct CRT
    # projections are checked, not inferred from the primary checker.
    unit_row = orbit(1, denominator, depth, upper)
    unit_arc = Fraction(10 ** upper - 16, denominator)
    assert unit_arc < Fraction(1, 10 ** 1186)
    assert circular_gap(unit_row, denominator) > 1 - Fraction(1, 10 ** 1186)
    assert len(three_primary_coordinates(
        1, denominator, depth, three_period, e
    )) == three_period

    odd_candidate = numerator % odd_denominator
    if odd_candidate % 2 == 0:
        odd_candidate += odd_denominator
    assert 0 < odd_candidate < 2 * odd_denominator
    assert odd_candidate % odd_denominator == numerator % odd_denominator
    assert math.gcd(odd_candidate, denominator) == 1
    odd_row = orbit(odd_candidate, denominator, depth, upper)
    odd_arc = Fraction((10 ** upper - 16) * odd_candidate, denominator)
    odd_gap = circular_gap(odd_row, denominator)
    assert odd_arc < Fraction(83, 1000)
    assert odd_gap > Fraction(917, 1000)
    assert len(three_primary_coordinates(
        odd_candidate, denominator, depth, three_period, e
    )) == three_period

    dyadic_modulus = 1 << two_exponent
    dyadic_residue = numerator % dyadic_modulus
    lift_index = next(
        t for t in range(100)
        if math.gcd(dyadic_residue + t * dyadic_modulus, odd_denominator) == 1
    )
    assert lift_index == 3
    dyadic_candidate = dyadic_residue + lift_index * dyadic_modulus
    assert dyadic_candidate % dyadic_modulus == numerator % dyadic_modulus
    assert math.gcd(dyadic_candidate, denominator) == 1
    dyadic_row = orbit(dyadic_candidate, denominator, depth, upper)
    dyadic_arc = Fraction(
        (10 ** upper - 16) * dyadic_candidate, denominator
    )
    assert dyadic_arc < Fraction(1, 10 ** 639)
    assert circular_gap(dyadic_row, denominator) > 1 - Fraction(1, 10 ** 639)

    finest_dyadic_exponent = two_exponent - upper
    assert finest_dyadic_exponent == 1270

    gap_encoding = f"{actual_gap.numerator}/{actual_gap.denominator}".encode()
    record_lines = [
        "bounded_claim_label=experiment",
        "analytic_claim_label=proof sketch",
        "literature_claim_label=literature-checked",
        f"primary_local_links_verified={local_link_count}",
        "primary_control_bytes=0",
        f"endpoint=e{e}-pre-drop-M{depth}",
        f"row_length={row_length}",
        f"actual_gap_sha256={hashlib.sha256(gap_encoding).hexdigest()}",
        f"cell_count={cells}",
        f"cell_minimum={min(histogram)}",
        f"signed_nonzero_dft_trough={min(signed_troughs)}",
        f"dft_reconstruction_error_lt_1e-90={reconstruction_error < mp.mpf('1e-90')}",
        f"actual_nonzero_dft_energy={energy}",
        f"empty_energy_threshold={empty_threshold}",
        f"balanced_empty_nonzero_dft_energy={balanced_energy}",
        f"isospectral_empty_nonzero_dft_energy={isospectral_energy}",
        "isospectral_empty_cell_count=1",
        "unit_numerator_gap_gt=1-10^-1186",
        "odd_crt_preserving_gap_gt=917/1000",
        f"dyadic_preserving_first_coprime_lift={lift_index}",
        "dyadic_preserving_gap_gt=1-10^-639",
        f"finest_row_dyadic_exponent={finest_dyadic_exponent}",
        "asserts_ae_endpoint_law=false",
        "asserts_endpoint_gap_law=false",
        "asserts_fixed_pi_return=false",
        "asserts_v1=false",
    ]
    record = "\n".join(record_lines) + "\n"
    print(record, end="")
    print(f"independent_record_sha256={hashlib.sha256(record.encode()).hexdigest()}")
    print("status=PASS")


if __name__ == "__main__":
    main()
