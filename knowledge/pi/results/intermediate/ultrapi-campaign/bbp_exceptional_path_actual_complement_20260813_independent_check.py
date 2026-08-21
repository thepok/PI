#!/usr/bin/env python3
"""Disjoint replay for the exceptional-path actual-complement audit.

All bounded numerical output has claim label ``experiment``.  This checker
imports no primary checker.  It recomputes the endpoint residues separately
at their own 3-power moduli, constructs an independently certified decimal
shadow of pi, obtains the all-unit correlations from six cyclic convolutions,
and checks the two small cross-depth identities with exact ``Fraction``
arithmetic.  The all-depth deductions remain the companion audit's
``proof sketch`` and are not promoted by this finite replay.
"""

from __future__ import annotations

import cmath
import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2
import numpy as np


sys.set_int_max_str_digits(5_000_000)

SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
FROZEN = {
    "problems/local/pi-digits.txt": SOURCE_SHA256,
    "work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813.md":
        "95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc",
    "work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_check.py":
        "1c151a8cbe253fb6323006f156719a85f970c3eb4b5feed0961e218a59c67b3e",
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md":
        "3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean":
        "eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727",
}

EPOCHS = (4, 6, 8, 10, 12, 14)
EXACT_EPOCHS = (4, 6, 8)
COSET_REPRESENTATIVES = (1, 2, 4, 5, 7, 8)
DECIMAL_WIDTH = 60
ETAS = (0.25, 0.1, 0.05, 0.03, 0.02, 0.015, 0.01, 0.007,
        0.005, 0.003, 0.002, 0.001)
EXPECTED_BETA = {
    4: 38,
    6: 524,
    8: 4898,
    10: 57386,
    12: 175484,
    14: 3364130,
}
EXPECTED_SELECTED = {
    4: (29, 0.296266113865536, 4),
    6: (29, 0.0523286585438117, 46),
    8: (29, 0.0192384830114831, 359),
    10: (26273, 0.0110218123722289, 1998),
    12: (203420, 0.00401366588930711, 15255),
    14: (1797743, 0.00118472154506736, 168116),
}
EXPECTED_MAXIMUM = {
    4: 0.598344580040705,
    6: 0.249570456391329,
    8: 0.0886419782225740,
    10: 0.0358390133604160,
    12: 0.0150083638691772,
    14: 0.00529762500028326,
}
TRANSITION_WITNESS = {
    4: (0.100, 234, 26, 26),
    6: (0.030, 2286, 254, 244),
    8: (0.015, 8928, 992, 833),
    10: (0.007, 19458, 2162, 1586),
    12: (0.002, 381474, 42386, 33532),
}
EXPECTED_RECORD_SHA256 = (
    "8e71daa3d7881ebbf0b8ef5ac0f7ad57c67a8a40e98fb668b54b8271ec8198aa"
)


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation at zero is outside this replay")
    result = 0
    value = abs(value)
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def depth(epoch: int) -> int:
    return 5 * (3**epoch - 1) // 8 - 1


def row_length(epoch: int) -> int:
    return 3 ** (epoch - 2)


def four_pole_term(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def combined_numerator_denominator(index: int) -> tuple[int, int]:
    numerator = 120 * index * index + 151 * index + 47
    denominator = (
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5)
    )
    return numerator, denominator


def check_combination_identity() -> None:
    for index in range(257):
        numerator, denominator = combined_numerator_denominator(index)
        assert four_pole_term(index) == Fraction(numerator, denominator)


def exact_partial_sums() -> dict[int, Fraction]:
    targets = {depth(epoch): epoch for epoch in EXACT_EPOCHS}
    total = Fraction()
    power16 = 1
    result: dict[int, Fraction] = {}
    for index in range(max(targets) + 1):
        if index:
            power16 *= 16
        numerator, denominator = combined_numerator_denominator(index)
        total += Fraction(numerator, denominator * power16)
        if index in targets:
            result[targets[index]] = total
    return result


def endpoint_beta(epoch: int) -> int:
    """Compute 3^e B_M mod 3^e at its own modulus, independently per e."""
    modulus = 3**epoch
    inverse16 = pow(16, -1, modulus)
    inverse_power = 1
    total = 0
    for index in range(depth(epoch) + 1):
        numerator, denominator = combined_numerator_denominator(index)
        numerator_height = valuation(numerator, 3)
        denominator_height = valuation(denominator, 3)
        exponent = epoch + numerator_height - denominator_height
        assert exponent >= 0
        unit_numerator = numerator // (3**numerator_height)
        unit_denominator = denominator // (3**denominator_height)
        total += (
            unit_numerator
            * 3**exponent
            * pow(unit_denominator, -1, modulus)
            * inverse_power
        )
        total %= modulus
        inverse_power = inverse_power * inverse16 % modulus
    assert total == EXPECTED_BETA[epoch]
    assert total % 3 != 0
    return total


def certified_pi_fraction_digits(places: int) -> str:
    bits = math.ceil((places + 128) * math.log2(10))
    scale = gmpy2.mpz(10) ** places
    downward = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundDown
    )
    upward = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundUp
    )
    with downward:
        low = gmpy2.floor(gmpy2.const_pi() * scale)
    with upward:
        high = gmpy2.floor(gmpy2.const_pi() * scale)
    assert low == high
    text = str(low)
    assert text.startswith("3") and len(text) == places + 1
    return text[1:]


def certified_sixteen_pi_fraction(width: int) -> int:
    bits = math.ceil((width + 128) * math.log2(10))
    scale = gmpy2.mpz(10) ** width
    downward = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundDown
    )
    upward = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundUp
    )
    with downward:
        low = gmpy2.floor(16 * gmpy2.const_pi() * scale)
    with upward:
        high = gmpy2.floor(16 * gmpy2.const_pi() * scale)
    assert low == high
    return int(low % scale)


def exact_phase_row(epoch: int, partial: Fraction) -> np.ndarray:
    count = row_length(epoch)
    numerator = partial.numerator
    denominator = partial.denominator
    residue = numerator * (pow(10, depth(epoch), denominator) - 16) % denominator
    result = np.empty(count, dtype=np.complex128)
    for offset in range(count):
        result[offset] = cmath.exp(
            2j * math.pi * float(Fraction(residue, denominator))
        )
        residue = (10 * residue + 144 * numerator) % denominator
    return result


def shadow_phase_row(
    epoch: int, digits: str, sixteen_pi_fraction: int
) -> tuple[np.ndarray, float]:
    count = row_length(epoch)
    start = depth(epoch)
    scale = 10**DECIMAL_WIDTH
    result = np.empty(count, dtype=np.complex128)
    for offset in range(count):
        exponent = start + offset
        pi_fraction = int(digits[exponent : exponent + DECIMAL_WIDTH])
        residue = (pi_fraction - sixteen_pi_fraction) % scale
        result[offset] = cmath.exp(2j * math.pi * (residue / scale))
    tail_log10 = (
        start + count
        - start * math.log10(16)
        - math.log10(15 * (start + 1) ** 2)
    )
    assert tail_log10 < -900
    return result, tail_log10


def fibre_structure(epoch: int) -> dict[str, int]:
    q = 3**epoch
    count = row_length(epoch)
    assert q == 9 * count
    base_count = 0
    lift_count = 0
    for base in range(count):
        if base % 3 == 0:
            continue
        lifts = [base + multiple * count for multiple in range(9)]
        assert len(set(lifts)) == 9
        assert all(value % count == base for value in lifts)
        assert all(math.gcd(value, q) == 1 for value in lifts)
        base_count += 1
        lift_count += len(lifts)
    assert base_count == 2 * count // 3
    assert lift_count == 6 * count
    assert lift_count == 2 * 3 ** (epoch - 1)
    assert all(pow(10, exponent, 9) == 1 for exponent in range(count))
    return {"fibres": base_count, "unit_lifts": lift_count}


def all_unit_row(
    epoch: int, beta: int, phase: np.ndarray, tail_log10: float | None
) -> tuple[dict[str, object], np.ndarray]:
    count = row_length(epoch)
    q = 3**epoch
    powers = np.empty(count, dtype=np.int64)
    current = 1
    for index in range(count):
        powers[index] = current
        current = 10 * current % q
    assert current == 1
    assert len(np.unique(powers)) == count

    selected = beta * pow(10, depth(epoch), q) % q
    expected_coefficient, expected_value, expected_rank = EXPECTED_SELECTED[epoch]
    assert selected == expected_coefficient
    selected_primary = np.exp(
        2j * np.pi * ((selected * powers) % q).astype(np.float64) / q
    )
    weight = phase / selected_primary

    fibre_sum = np.zeros(count, dtype=np.float64)
    fibre_count = np.zeros(count, dtype=np.uint8)
    fibre_minimum = np.full(count, np.inf, dtype=np.float64)
    fibre_maximum = np.full(count, -np.inf, dtype=np.float64)
    reversed_weight = np.concatenate((weight[:1], weight[:0:-1]))
    reversed_transform = np.fft.fft(reversed_weight)
    selected_fft: float | None = None
    for representative in COSET_REPRESENTATIVES:
        primary = np.exp(
            2j
            * np.pi
            * ((representative * powers) % q).astype(np.float64)
            / q
        )
        raw = np.fft.ifft(np.fft.fft(primary) * reversed_transform)
        magnitudes = np.abs(raw) / count
        coefficients = (representative * powers) % q
        bases = coefficients % count
        np.add.at(fibre_sum, bases, magnitudes)
        np.add.at(fibre_count, bases, 1)
        np.minimum.at(fibre_minimum, bases, magnitudes)
        np.maximum.at(fibre_maximum, bases, magnitudes)
        hits = np.flatnonzero(coefficients == selected)
        if len(hits):
            assert len(hits) == 1 and selected_fft is None
            selected_fft = float(magnitudes[int(hits[0])])

    bases = np.flatnonzero(fibre_count)
    assert len(bases) == 2 * count // 3
    assert np.all(fibre_count[bases] == 9)
    assert np.all(fibre_count[np.arange(count) % 3 == 0] == 0)
    maximum_spread = float(np.max(fibre_maximum[bases] - fibre_minimum[bases]))
    assert maximum_spread < 3e-11
    values = fibre_sum[bases] / 9

    selected_base_index = int(np.flatnonzero(bases == selected % count)[0])
    selected_value = float(values[selected_base_index])
    direct_selected = float(abs(np.sum(phase)) / count)
    assert selected_fft is not None
    assert abs(selected_value - selected_fft) < 3e-11
    assert abs(selected_value - direct_selected) < 3e-11
    assert abs(selected_value - expected_value) < 6e-10

    tolerance = 2e-10
    rank_low = 1 + int(np.count_nonzero(values > selected_value + tolerance))
    rank_high = int(np.count_nonzero(values >= selected_value - tolerance))
    assert rank_low == rank_high == expected_rank
    maximum = float(np.max(values))
    assert abs(maximum - EXPECTED_MAXIMUM[epoch]) < 6e-10

    shift = count // 3
    shifted_product = np.sum(np.roll(weight, -shift) * np.conjugate(weight))
    second_moment_observed = float(np.mean(values * values))
    second_moment_formula = float(
        (count - shifted_product.real) / (count * count)
    )
    assert abs(second_moment_observed - second_moment_formula) < 3e-11
    assert second_moment_formula <= 2 / count + 3e-12

    exceptional: dict[str, dict[str, int]] = {}
    for eta in ETAS:
        bad_fibres = int(np.count_nonzero(values >= eta))
        bad_units = 9 * bad_fibres
        assert bad_units <= 12 / (eta * eta) + 1e-9
        assert bad_fibres <= 4 / (3 * eta * eta) + 1e-9
        exceptional[f"{eta:.3f}"] = {
            "fibres": bad_fibres,
            "unit_coefficients": bad_units,
        }

    row = {
        "epoch": epoch,
        "depth": depth(epoch),
        "row_length": count,
        "beta": beta,
        "selected_coefficient": selected,
        "selected_normalized_magnitude": f"{selected_value:.15f}",
        "fibre_rank": rank_low,
        "fibre_count": len(bases),
        "all_unit_rank_low": 9 * (rank_low - 1) + 1,
        "all_unit_rank_high": 9 * rank_high,
        "all_unit_count": 6 * count,
        "maximum_normalized_magnitude": f"{maximum:.15f}",
        "maximum_fibre_spread": f"{maximum_spread:.3e}",
        "normalized_second_moment": f"{second_moment_observed:.15f}",
        "phase_kind": "exact-rational" if tail_log10 is None else "pi-shadow-60-decimal",
        "tail_log10_upper": None if tail_log10 is None else f"{tail_log10:.6f}",
        "exceptional": exceptional,
    }
    full_values = np.full(count, np.nan, dtype=np.float64)
    full_values[bases] = values
    return row, full_values


def transition_replay(
    rows: dict[int, dict[str, object]],
    groups: dict[int, np.ndarray],
) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for epoch, expected in TRANSITION_WITNESS.items():
        higher = epoch + 2
        eta, expected_units, expected_parents, expected_overlap = expected
        lower_values = groups[epoch]
        upper_values = groups[higher]
        upper_bases = np.flatnonzero(~np.isnan(upper_values))
        bad_mask = upper_values[upper_bases] >= eta
        bad_parents = upper_bases[bad_mask]
        overlap = int(np.count_nonzero(
            lower_values[bad_parents % row_length(epoch)] >= eta
        ))
        bad_parent_count = len(bad_parents)
        bad_unit_count = 9 * bad_parent_count
        assert bad_unit_count == expected_units
        assert bad_parent_count == expected_parents
        assert overlap == expected_overlap

        selected_lower = int(rows[epoch]["selected_coefficient"])
        selected_upper = int(rows[higher]["selected_coefficient"])
        assert selected_upper % (3**epoch) == selected_lower
        lower_selected_value = float(
            lower_values[selected_lower % row_length(epoch)]
        )
        upper_selected_lifts_value = float(upper_values[selected_lower])
        assert lower_selected_value > eta > upper_selected_lifts_value
        result.append({
            "transition": f"{epoch}->{higher}",
            "eta": f"{eta:.3f}",
            "higher_exceptional_unit_coefficients": bad_unit_count,
            "higher_exceptional_parent_fibres": bad_parent_count,
            "parents_exceptional_below": overlap,
            "selected_exceptional_lifts": 0,
        })
    return result


def exact_cross_depth(
    partials: dict[int, Fraction], betas: dict[int, int]
) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for epoch in (4, 6):
        higher = epoch + 2
        lower_depth = depth(epoch)
        higher_depth = depth(higher)
        delta = higher_depth - lower_depth
        lower = partials[epoch]
        upper = partials[higher]
        assert higher_depth == 9 * lower_depth + 13
        assert delta == 5 * 3**epoch

        lower_q = 3**epoch
        lower_a = betas[epoch] * pow(10, lower_depth, lower_q) % lower_q
        upper_a = (
            betas[higher]
            * pow(10, higher_depth, 3**higher)
            % (3**higher)
        )
        assert upper_a % lower_q == lower_a
        # EP15 is an exact modular identity; no floating comparison is used.
        for exponent in range(row_length(epoch)):
            assert (
                upper_a * pow(10, exponent, 3**higher)
                - lower_a * pow(10, exponent, lower_q)
            ) % lower_q == 0

        defect = 9 * 10**delta * upper - lower
        constant = 16 * lower - 144 * upper
        assert valuation((9 * upper - lower).denominator, 3) == 0
        assert valuation(defect.denominator, 3) == 0
        for offset in range(row_length(epoch)):
            left = (
                9 * (10 ** (higher_depth + offset) - 16) * upper
                - (10 ** (lower_depth + offset) - 16) * lower
            )
            right = 10 ** (lower_depth + offset) * defect + constant
            assert left == right

        lower_k = 4 * lower_depth - valuation(lower_depth + 1, 2)
        upper_k = 4 * higher_depth - valuation(higher_depth + 1, 2)
        active_denominator = upper_k - delta
        assert active_denominator > lower_k
        assert valuation(defect.denominator, 2) == active_denominator
        minimum_depth = (
            active_denominator
            - lower_depth
            - (row_length(epoch) - 1)
        )
        assert minimum_depth > 0
        result.append({
            "transition": f"{epoch}->{higher}",
            "EP15_exact_modular_points": row_length(epoch),
            "EP16_exact_rational_points": row_length(epoch),
            "EP20_dyadic_denominator_exponent": active_denominator,
            "EP21_minimum_active_depth": minimum_depth,
        })
    return result


def haar_budget() -> dict[str, object]:
    thresholds: list[dict[str, str | int]] = []
    for reciprocal in range(1, 17):
        # e=4+2r gives T_e=3^(2+2r), so the infinite upper budget is
        # 2*m^2 * (1/9)/(1-1/9) = m^2/4.
        total = Fraction(2 * reciprocal * reciprocal, 9) / (
            1 - Fraction(1, 9)
        )
        assert total == Fraction(reciprocal * reciprocal, 4)
        thresholds.append({
            "eta_reciprocal": reciprocal,
            "measure_sum_upper": f"{total.numerator}/{total.denominator}",
        })
    return {
        "unit_cylinder_measure": "1/(6*T_e)",
        "bad_residue_count_upper": "12/eta^2",
        "bad_measure_upper": "2/(eta^2*T_e)",
        "even_epoch_sum_upper": "1/(4*eta^2)",
        "thresholds": thresholds,
        "uses_independence": False,
        "asserts_selected_path_generic": False,
    }


def main() -> None:
    observed_frozen = {
        relative: sha256(repository_root() / relative)
        for relative in FROZEN
    }
    assert observed_frozen == FROZEN
    check_combination_identity()
    partials = exact_partial_sums()
    betas = {epoch: endpoint_beta(epoch) for epoch in EPOCHS}

    required_places = (
        depth(max(EPOCHS))
        + row_length(max(EPOCHS))
        + DECIMAL_WIDTH
        + 4
    )
    digits = certified_pi_fraction_digits(required_places)
    sixteen_pi_fraction = certified_sixteen_pi_fraction(DECIMAL_WIDTH)

    structures: dict[int, dict[str, int]] = {}
    rows: dict[int, dict[str, object]] = {}
    groups: dict[int, np.ndarray] = {}
    for epoch in EPOCHS:
        structures[epoch] = fibre_structure(epoch)
        if epoch in EXACT_EPOCHS:
            phase = exact_phase_row(epoch, partials[epoch])
            tail_log10 = None
        else:
            phase, tail_log10 = shadow_phase_row(
                epoch, digits, sixteen_pi_fraction
            )
        row, group = all_unit_row(
            epoch, betas[epoch], phase, tail_log10
        )
        rows[epoch] = row
        groups[epoch] = group

    cross_depth = exact_cross_depth(partials, betas)
    transitions = transition_replay(rows, groups)
    budget = haar_budget()
    record = {
        "claim_label": "experiment",
        "rows": [rows[epoch] for epoch in EPOCHS],
        "fibre_structures": structures,
        "transitions": transitions,
        "cross_depth": cross_depth,
        "haar_budget": budget,
        "frozen": observed_frozen,
        "asserts_T74_proves_endpoint_nesting": False,
        "asserts_cross_level_exceptional_relation": False,
        "asserts_CF36": False,
        "asserts_path_decay": False,
        "asserts_V1": False,
    }
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    if EXPECTED_RECORD_SHA256:
        assert digest == EXPECTED_RECORD_SHA256

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    for epoch in EPOCHS:
        row = rows[epoch]
        print(
            f"epoch_{row['epoch']}=a{row['selected_coefficient']},"
            f"selected{row['selected_normalized_magnitude']},"
            f"fibre_rank{row['fibre_rank']}/{row['fibre_count']},"
            f"all_rank{row['all_unit_rank_low']}-{row['all_unit_rank_high']}/"
            f"{row['all_unit_count']},max{row['maximum_normalized_magnitude']}"
        )
    print("EP7_all_epoch_fibre_counts=true")
    print("EP8_bound_replayed=true")
    print("EP11_even_epoch_sum=1/(4*eta^2)")
    print("transition_witnesses=5")
    print("EP15_exact_transitions=2")
    print("EP16_exact_transitions=2")
    print("EP20_exact_transitions=2")
    print("asserts_T74_proves_endpoint_nesting=false")
    print("asserts_cross_level_exceptional_relation=false")
    print(f"exact_record_sha256={digest}")
    print("asserts_CF36=false")
    print("asserts_path_decay=false")
    print("asserts_V1=false")


if __name__ == "__main__":
    main()
