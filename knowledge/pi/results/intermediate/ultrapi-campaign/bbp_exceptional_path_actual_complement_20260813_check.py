#!/usr/bin/env python3
"""Finite diagnostic for exceptional primary coefficients in the BBP complement.

Every bounded numerical conclusion in this file has claim label ``experiment``.
The companion report separates the elementary all-depth identities, labelled
``proof sketch``, from these finite FFT data.  The script imports no other
branch checker.  Exact integers/Fractions are used for the four-pole endpoint
units and the small full phases.  The larger full phases use a directed MPFR
prefix of pi and the positive BBP-tail bound.  Binary complex FFTs are used
only for the explicitly labelled correlation diagnostic.
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
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md":
        "3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e",
    "work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_independent_audit.md":
        "46642011eb928e85ed7e707524ed79589c957cf5f1d742db5f0177c3e4887b51",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
    "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md":
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_audit.md":
        "6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9",
    "TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean":
        "eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727",
}

EPOCHS = (4, 6, 8, 10, 12, 14)
EXACT_EPOCHS = (4, 6, 8)
SHADOW_EPOCHS = (10, 12, 14)
WIDTH = 50
COSETS_MOD_NINE = (1, 2, 4, 5, 7, 8)
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
FRACTION_SHA256 = {
    4: "5d587fa24114f1bb0babc1652053b227043167e948b4a685281df899ce28772b",
    6: "b99709e38f3846bdc08de616cb2efc049f70fe4b9f9ab998ea4c82016ddf54fc",
    8: "b9673780cbf68442704c8e3038b1edf2d42fa2dbfc369ab1c0e6f76e7be036ca",
}

# Each threshold witnesses disappearance of the selected exceptional fibre
# on the indicated actual transition.  These are finite experiment assertions,
# not a uniform asymptotic statement.
TRANSITION_ETA = {4: 0.1, 6: 0.03, 8: 0.015, 10: 0.007, 12: 0.002}
DIAGNOSTIC_ETAS = (0.25, 0.1, 0.05, 0.03, 0.02, 0.015, 0.01, 0.007,
                   0.005, 0.003, 0.002, 0.001)

EXPECTED_RECORD_SHA256 = (
    "9bbdfe2218c537c54216648ca44eaf3d674fda5f51f98986e513cafaa969eae5"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation at zero is not used")
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def depth(epoch: int) -> int:
    return 5 * (3**epoch - 1) // 8 - 1


def period(epoch: int) -> int:
    return 3 ** (epoch - 2)


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def check_frozen_inputs() -> dict[str, str]:
    observed = {relative: sha256(root() / relative) for relative in FROZEN}
    if observed != FROZEN:
        raise AssertionError(("frozen input changed", observed, FROZEN))
    return observed


def exact_small_sums() -> dict[int, Fraction]:
    targets = {depth(epoch): epoch for epoch in EXACT_EPOCHS}
    maximum = max(targets)
    partial = Fraction()
    power16 = 1
    answer: dict[int, Fraction] = {}
    for index in range(maximum + 1):
        if index:
            power16 <<= 4
        partial += coefficient(index) / power16
        if index in targets:
            epoch = targets[index]
            digest = hashlib.sha256(
                f"{partial.numerator}/{partial.denominator}".encode()
            ).hexdigest()
            assert digest == FRACTION_SHA256[epoch]
            answer[epoch] = partial
    return answer


def endpoint_three_units() -> dict[int, int]:
    """Recompute 3^e B_M mod 3^e from the four-pole coefficient."""
    top = max(EPOCHS)
    modulus = 3**top
    targets = {depth(epoch): epoch for epoch in EPOCHS}
    inverse16 = pow(16, -1, modulus)
    inverse_power = 1
    scaled = 0
    answer: dict[int, int] = {}
    for index in range(max(targets) + 1):
        numerator = 120 * index * index + 151 * index + 47
        denominator = (
            (2 * index + 1)
            * (4 * index + 3)
            * (8 * index + 1)
            * (8 * index + 5)
        )
        numerator_height = valuation(numerator, 3)
        denominator_height = valuation(denominator, 3)
        shift = top + numerator_height - denominator_height
        assert shift >= 0
        unit_numerator = numerator // (3**numerator_height)
        unit_denominator = denominator // (3**denominator_height)
        term = (
            unit_numerator
            * 3**shift
            * pow(unit_denominator, -1, modulus)
            * inverse_power
        ) % modulus
        scaled = (scaled + term) % modulus
        if index in targets:
            epoch = targets[index]
            divisor = 3 ** (top - epoch)
            assert scaled % divisor == 0
            beta = scaled // divisor % (3**epoch)
            assert beta == EXPECTED_BETA[epoch] and beta % 3 == 2
            answer[epoch] = beta
        inverse_power = inverse_power * inverse16 % modulus
    return answer


def certified_pi_digits(decimal_places: int) -> str:
    bits = math.ceil((decimal_places + 96) * math.log2(10))
    scale = gmpy2.mpz(10) ** decimal_places
    down = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=bits, round=gmpy2.RoundUp
    )
    with down:
        lower = gmpy2.floor(gmpy2.const_pi() * scale)
    with up:
        upper = gmpy2.floor(gmpy2.const_pi() * scale)
    assert lower == upper
    text = str(lower)
    assert text[0] == "3" and len(text) == decimal_places + 1
    return text[1:]


def sixteen_pi_prefix(pi_digits: str) -> int:
    total = len(pi_digits)
    scaled_pi = int("3" + pi_digits)
    divisor = 10 ** (total - WIDTH)
    lower = 16 * scaled_pi // divisor
    upper = 16 * (scaled_pi + 1) // divisor
    assert lower == upper
    return lower % (10**WIDTH)


def exact_full_phase(epoch: int, value: Fraction) -> tuple[np.ndarray, str]:
    start = depth(epoch)
    count = period(epoch)
    numerator = value.numerator
    denominator = value.denominator
    residue = ((pow(10, start, denominator) - 16) * numerator) % denominator
    phases = np.empty(count, dtype=np.complex128)
    stream = hashlib.sha256()
    byte_width = (denominator.bit_length() + 7) // 8
    for offset in range(count):
        phases[offset] = cmath.exp(2j * math.pi * (residue / denominator))
        stream.update(residue.to_bytes(byte_width, "big"))
        residue = (10 * residue + 144 * numerator) % denominator
    return phases, stream.hexdigest()


def shadow_full_phase(
    epoch: int, pi_digits: str, sixteen_pi: int
) -> tuple[np.ndarray, str, float]:
    start = depth(epoch)
    count = period(epoch)
    modulus = 10**WIDTH
    phases = np.empty(count, dtype=np.complex128)
    stream = hashlib.sha256()
    byte_width = (modulus.bit_length() + 7) // 8
    for offset, exponent in enumerate(range(start, start + count)):
        residue = (int(pi_digits[exponent : exponent + WIDTH]) - sixteen_pi) % modulus
        phases[offset] = cmath.exp(2j * math.pi * (residue / modulus))
        stream.update(residue.to_bytes(byte_width, "big"))

    # The positive BBP tail gives
    # (10^(M+T)-16)(pi-B_M) < 10^(M+T)16^-M/[15(M+1)^2].
    tail_log10 = (
        start + count
        - start * math.log10(16)
        - math.log10(15 * (start + 1) ** 2)
    )
    assert tail_log10 < -900
    return phases, stream.hexdigest(), tail_log10


def circular_correlations(primary: np.ndarray, weight: np.ndarray) -> np.ndarray:
    """Return r[s] = sum_j primary[j+s] weight[j], divided by T."""
    reversed_weight = np.concatenate((weight[:1], weight[:0:-1]))
    return np.fft.ifft(np.fft.fft(primary) * np.fft.fft(reversed_weight)) / len(weight)


def analyze_epoch(
    epoch: int,
    beta: int,
    full_phase: np.ndarray,
    phase_stream_sha256: str,
    shadow_tail_log10: float | None,
) -> tuple[dict[str, object], np.ndarray, np.ndarray]:
    q = 3**epoch
    count = period(epoch)
    start = depth(epoch)
    powers = np.empty(count, dtype=np.int64)
    current = 1
    for index in range(count):
        powers[index] = current
        current = 10 * current % q
    assert current == 1 and len(set(map(int, powers))) == count

    selected = beta * pow(10, start, q) % q
    expected_selected, expected_magnitude, expected_rank = EXPECTED_SELECTED[epoch]
    assert selected == expected_selected
    selected_primary = np.exp(2j * np.pi * ((selected * powers) % q) / q)
    weight = full_phase / selected_primary

    # Coefficients a and a+kT have primary phases differing by the constant
    # e_9(k), so magnitudes occur in exact nine-element fibres.  The FFT
    # computes all six cosets c<10> and groups them by a mod T.
    group_sum = np.zeros(count, dtype=np.float64)
    group_count = np.zeros(count, dtype=np.uint8)
    group_first = np.full(count, np.nan, dtype=np.float64)
    maximum_fibre_spread = 0.0
    coefficient_count = 0
    selected_fft_value: float | None = None
    for representative in COSETS_MOD_NINE:
        primary = np.exp(2j * np.pi * ((representative * powers) % q) / q)
        correlations = circular_correlations(primary, weight)
        for shift, correlation in enumerate(correlations):
            coefficient = representative * int(powers[shift]) % q
            magnitude = float(abs(correlation))
            base = coefficient % count
            if group_count[base]:
                maximum_fibre_spread = max(
                    maximum_fibre_spread,
                    abs(magnitude - group_first[base]),
                )
            else:
                group_first[base] = magnitude
            group_sum[base] += magnitude
            group_count[base] += 1
            coefficient_count += 1
            if coefficient == selected:
                selected_fft_value = magnitude

    assert coefficient_count == 6 * count
    unit_bases = np.flatnonzero(group_count)
    assert len(unit_bases) == 2 * count // 3
    assert np.all(group_count[unit_bases] == 9)
    assert np.all(group_count[np.arange(count) % 3 == 0] == 0)
    assert maximum_fibre_spread < 2e-11
    group_value = np.full(count, np.nan, dtype=np.float64)
    group_value[unit_bases] = group_sum[unit_bases] / 9.0

    selected_base = selected % count
    selected_value = float(group_value[selected_base])
    assert selected_fft_value is not None
    assert abs(selected_fft_value - selected_value) < 2e-11
    direct_selected = float(abs(np.sum(full_phase)) / count)
    assert abs(direct_selected - selected_value) < 2e-11
    assert abs(selected_value - expected_magnitude) < 5e-10

    values = group_value[unit_bases]
    rank_tolerance = 2e-10
    quotient_rank_low = 1 + int(np.count_nonzero(values > selected_value + rank_tolerance))
    quotient_rank_high = int(np.count_nonzero(values >= selected_value - rank_tolerance))
    assert quotient_rank_low == expected_rank
    maximum = float(np.max(values))
    assert abs(maximum - EXPECTED_MAXIMUM[epoch]) < 5e-10
    maximum_bases = unit_bases[np.abs(values - maximum) < rank_tolerance]

    # Direct replay of GX16 on this actual complement row.
    shift = count // 3
    shifted_inner = np.sum(np.roll(weight, -shift) * np.conjugate(weight))
    ramanujan_rhs = float((count - shifted_inner.real) / (count * count))
    ramanujan_lhs = float(np.mean(values * values))
    assert abs(ramanujan_lhs - ramanujan_rhs) < 2e-11
    assert ramanujan_rhs <= 2 / count + 2e-12

    ratio = selected * pow(selected % 9, -1, q) % q
    selected_shift_hits = np.flatnonzero(powers == ratio)
    assert len(selected_shift_hits) == 1
    selected_shift = int(selected_shift_hits[0])

    exceptional_counts = {
        f"{eta:.3f}": {
            "projected_fibres": int(np.count_nonzero(values >= eta)),
            "all_unit_coefficients": 9 * int(np.count_nonzero(values >= eta)),
            "selected_is_exceptional": bool(selected_value >= eta),
        }
        for eta in DIAGNOSTIC_ETAS
    }

    row = {
        "epoch": epoch,
        "depth": start,
        "q": q,
        "period": count,
        "beta": beta,
        "selected_coefficient": selected,
        "selected_coefficient_mod9": selected % 9,
        "selected_shift": selected_shift,
        "selected_normalized_magnitude": f"{selected_value:.15f}",
        "selected_quotient_rank_low": quotient_rank_low,
        "selected_quotient_rank_high": quotient_rank_high,
        "quotient_class_count": len(unit_bases),
        "selected_all_unit_rank_low": 9 * (quotient_rank_low - 1) + 1,
        "selected_all_unit_rank_high": 9 * quotient_rank_high,
        "all_unit_coefficient_count": 6 * count,
        "maximum_normalized_magnitude": f"{maximum:.15f}",
        "maximum_projected_bases": [int(value) for value in maximum_bases],
        "maximum_fibre_spread": f"{maximum_fibre_spread:.3e}",
        "ramanujan_normalized_second_moment": f"{ramanujan_lhs:.15f}",
        "phase_stream_sha256": phase_stream_sha256,
        "phase_kind": "exact-rational" if shadow_tail_log10 is None else "directed-pi-shadow",
        "shadow_tail_log10_upper": (
            None if shadow_tail_log10 is None else f"{shadow_tail_log10:.6f}"
        ),
        "exceptional_counts": exceptional_counts,
    }
    return row, group_value, weight


def cross_depth_exact_checks(
    small: dict[int, Fraction],
    units: dict[int, int],
    weights: dict[int, np.ndarray],
) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    for epoch in (4, 6):
        higher = epoch + 2
        m = depth(epoch)
        n = depth(higher)
        delta = n - m
        assert n == 9 * m + 13 and delta == 5 * 3**epoch
        lower_sum = small[epoch]
        higher_sum = small[higher]

        decimation_defect = 9 * higher_sum - lower_sum
        assert valuation(decimation_defect.denominator, 3) == 0
        geometric_defect = 9 * 10**delta * higher_sum - lower_sum
        constant_defect = 16 * lower_sum - 144 * higher_sum
        assert valuation(geometric_defect.denominator, 3) == 0

        lower_k = 4 * m - valuation(m + 1, 2)
        higher_k = 4 * n - valuation(n + 1, 2)
        dyadic_depth = higher_k - delta
        assert dyadic_depth > lower_k
        assert valuation(geometric_defect.denominator, 2) == dyadic_depth
        minimum_active_depth = dyadic_depth - (m + period(epoch) - 1)
        assert minimum_active_depth > 0

        lower_q = 3**epoch
        lower_a = units[epoch] * pow(10, m, lower_q) % lower_q
        higher_a = units[higher] * pow(10, n, 3**higher) % (3**higher)
        assert higher_a % lower_q == lower_a

        maximum_complex_error = 0.0
        for offset in range(period(epoch)):
            left = 9 * (10 ** (n + offset) - 16) * higher_sum
            left -= (10 ** (m + offset) - 16) * lower_sum
            right = 10 ** (m + offset) * geometric_defect + constant_defect
            assert left == right

            phase = right - math.floor(right)
            predicted = cmath.exp(2j * math.pi * float(phase))
            observed = weights[higher][offset] ** 9 / weights[epoch][offset]
            maximum_complex_error = max(
                maximum_complex_error, abs(predicted - observed)
            )
        assert maximum_complex_error < 2e-9

        records.append({
            "transition": f"{epoch}->{higher}",
            "lower_depth": m,
            "higher_depth": n,
            "depth_shift": delta,
            "geometric_defect_three_integral": True,
            "geometric_defect_dyadic_denominator_exponent": dyadic_depth,
            "minimum_active_dyadic_depth": minimum_active_depth,
            "exact_pointwise_checks": period(epoch),
            "maximum_complex_replay_error": f"{maximum_complex_error:.3e}",
        })
    return records


def projection_records(
    rows: dict[int, dict[str, object]],
    groups: dict[int, np.ndarray],
) -> list[dict[str, object]]:
    answer: list[dict[str, object]] = []
    for epoch in EPOCHS[:-1]:
        higher = epoch + 2
        lower_values = groups[epoch]
        higher_values = groups[higher]
        higher_bases = np.flatnonzero(~np.isnan(higher_values))
        assert len(higher_bases) == 6 * period(epoch)
        selected_lower = int(rows[epoch]["selected_coefficient"])
        selected_higher = int(rows[higher]["selected_coefficient"])
        assert selected_higher % (3**epoch) == selected_lower
        assert higher_bases[selected_lower == higher_bases].size == 1

        for eta in DIAGNOSTIC_ETAS:
            upper_exception = higher_values[higher_bases] >= eta
            projected = higher_bases[upper_exception]
            lower_exception = (
                lower_values[projected % period(epoch)] >= eta
            )
            selected_upper_value = float(higher_values[selected_lower])
            selected_lifts = 9 if selected_upper_value >= eta else 0
            answer.append({
                "transition": f"{epoch}->{higher}",
                "eta": f"{eta:.3f}",
                "higher_exceptional_coefficients": 9 * int(np.count_nonzero(upper_exception)),
                "projected_exceptional_parents": int(np.count_nonzero(upper_exception)),
                "parents_also_exceptional_below": int(np.count_nonzero(lower_exception)),
                "selected_parent_exceptional_lifts": selected_lifts,
            })

        witness_eta = TRANSITION_ETA[epoch]
        lower_selected_value = float(
            lower_values[selected_lower % period(epoch)]
        )
        upper_selected_value = float(higher_values[selected_lower])
        assert lower_selected_value > witness_eta > upper_selected_value
    return answer


def borel_cantelli_budget() -> dict[str, object]:
    """Exact Haar-measure ledger for the first Borel--Cantelli corollary.

    At even epoch e, GX17 gives at most 12/eta^2 bad unit residues among
    phi(3^e)=6*3^(e-2).  For eta=1/m the lifted-cylinder measure is therefore
    at most 2*m^2/3^(e-2).  Its sum over e=4,6,... is exactly m^2/4.
    This finite checker verifies the geometric-series arithmetic; the
    measure-theoretic deduction itself is the companion report's proof sketch.
    """
    rational_thresholds: list[dict[str, str | int]] = []
    for denominator in range(1, 13):
        partial = sum(
            (Fraction(2 * denominator * denominator, 3 ** (epoch - 2))
             for epoch in range(4, 26, 2)),
            Fraction(),
        )
        # The omitted epochs are 26,28,..., with first denominator 3^24 and
        # ratio 1/9.
        tail = Fraction(
            2 * denominator * denominator,
            3**24,
        ) / (1 - Fraction(1, 9))
        total = Fraction(denominator * denominator, 4)
        assert partial + tail == total
        rational_thresholds.append({
            "eta_reciprocal": denominator,
            "summed_measure_upper_bound": f"{total.numerator}/{total.denominator}",
        })
    return {
        "epoch_parity": "even",
        "first_epoch": 4,
        "unit_cylinder_measure": "1/phi(3^e)",
        "bad_cylinder_measure_upper": "2/(eta^2*3^(e-2))",
        "rational_thresholds": rational_thresholds,
        "asserts_selected_bbp_path_is_haar_generic": False,
    }


def main() -> None:
    frozen = check_frozen_inputs()
    small = exact_small_sums()
    units = endpoint_three_units()

    maximum_places = depth(max(EPOCHS)) + period(max(EPOCHS)) + WIDTH + 10
    pi_digits = certified_pi_digits(maximum_places)
    sixteen_pi = sixteen_pi_prefix(pi_digits)

    rows: dict[int, dict[str, object]] = {}
    groups: dict[int, np.ndarray] = {}
    weights: dict[int, np.ndarray] = {}
    for epoch in EPOCHS:
        if epoch in EXACT_EPOCHS:
            full_phase, stream_digest = exact_full_phase(epoch, small[epoch])
            tail_log10 = None
        else:
            full_phase, stream_digest, tail_log10 = shadow_full_phase(
                epoch, pi_digits, sixteen_pi
            )
        row, group_values, weight = analyze_epoch(
            epoch,
            units[epoch],
            full_phase,
            stream_digest,
            tail_log10,
        )
        rows[epoch] = row
        groups[epoch] = group_values
        weights[epoch] = weight

    cross_depth = cross_depth_exact_checks(small, units, weights)
    projections = projection_records(rows, groups)
    borel_cantelli = borel_cantelli_budget()
    record = {
        "rows": [rows[epoch] for epoch in EPOCHS],
        "cross_depth": cross_depth,
        "projections": projections,
        "borel_cantelli": borel_cantelli,
        "frozen_inputs": frozen,
        "claim_label": "experiment",
        "asserts_cf36_bound": False,
        "asserts_path_decay": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    assert digest == EXPECTED_RECORD_SHA256, (digest, EXPECTED_RECORD_SHA256)

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print("literature_claim_label=literature-checked")
    for epoch in EPOCHS:
        row = rows[epoch]
        print(
            f"epoch_{epoch}=a{row['selected_coefficient']},"
            f"selected{row['selected_normalized_magnitude']},"
            f"quotient_rank{row['selected_quotient_rank_low']}-"
            f"{row['selected_quotient_rank_high']}/"
            f"{row['quotient_class_count']},"
            f"all_rank{row['selected_all_unit_rank_low']}-"
            f"{row['selected_all_unit_rank_high']}/"
            f"{row['all_unit_coefficient_count']},"
            f"maximum{row['maximum_normalized_magnitude']}"
        )
    for epoch, eta in TRANSITION_ETA.items():
        higher = epoch + 2
        witness_projection = next(
            item
            for item in projections
            if item["transition"] == f"{epoch}->{higher}"
            and item["eta"] == f"{eta:.3f}"
        )
        print(
            f"transition_{epoch}_{higher}_disappearance_eta={eta:.3f},"
            f"lower{rows[epoch]['selected_normalized_magnitude']},"
            f"upper{rows[higher]['selected_normalized_magnitude']},"
            f"higher_exceptional{witness_projection['higher_exceptional_coefficients']},"
            f"projected_parents{witness_projection['projected_exceptional_parents']},"
            f"overlap{witness_projection['parents_also_exceptional_below']},"
            f"selected_lifts{witness_projection['selected_parent_exceptional_lifts']}"
        )
    print(f"projection_records={len(projections)}")
    print(f"cross_depth_exact_transitions={len(cross_depth)}")
    print("borel_cantelli_even_epoch_sum_eta_inverse_m=m^2/4")
    print("asserts_selected_bbp_path_is_haar_generic=false")
    print(f"exact_record_sha256={digest}")
    print("asserts_cf36_bound=false")
    print("asserts_path_decay=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
