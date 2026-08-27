#!/usr/bin/env python3
"""Bounded checks for the BBP growing-band joint-harmonic attack.

Every row computation in this file has claim label ``experiment``.  Exact
Fractions are used at e=4,6,8.  At e=10,12, a directed MPFR prefix of pi and
the positive BBP-tail bound certify the equal-cell labels of the rational
BBP endpoint row.  Floating DFT inversion is only a diagnostic; all retained
occupancy, centered-trough, peak, and energy statements are integer-exact
after the cell labels have been certified.

The checker asserts no asymptotic gap estimate, Fourier decay, fixed return,
or occurrence theorem for pi.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2
import numpy as np


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813.md":
        "3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md":
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    "work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md":
        "eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_audit.md":
        "8c138103b4b2afb3e2b6e559c147c9b1ed69495e3689c1d00fa9fe50cee062ff",
}

AMBIENT_EXPONENTS = (4, 6, 8, 10, 12)
EXACT_EXPONENTS = (4, 6, 8)
SHADOW_EXPONENTS = (10, 12)
GUARD_DIGITS = 50
EXPECTED_RECORD_SHA256 = (
    "cc2cdf5824f772cc8062205f661ea605e244f369100132f1820f70fd481648c6"
)


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


def exact_upper(depth: int) -> int:
    return len(str(1 << (4 * depth))) - 1


def endpoint_rows(ambient: int) -> tuple[tuple[int, str, int], ...]:
    endpoint = (3**ambient - 1) // 8
    return (
        (5 * endpoint - 1, "pre-drop", ambient),
        (5 * endpoint, "first-drop", ambient - 1),
    )


def exact_partial_sums() -> dict[tuple[int, str], Fraction]:
    targets = {
        depth: (ambient, stage)
        for ambient in EXACT_EXPONENTS
        for depth, stage, _ in endpoint_rows(ambient)
    }
    maximum = max(targets)
    partial = Fraction()
    power = 1
    answer: dict[tuple[int, str], Fraction] = {}
    for index in range(maximum + 1):
        if index:
            power *= 16
        partial += coefficient(index) / power
        if index in targets:
            ambient, stage = targets[index]
            answer[ambient, stage] = partial
    return answer


def exact_phase_residues(depth: int, partial: Fraction) -> list[int]:
    modulus = partial.denominator
    numerator = partial.numerator
    upper = exact_upper(depth)
    residue = ((pow(10, depth, modulus) - 16) * numerator) % modulus
    answer = []
    for _ in range(depth, upper + 1):
        answer.append(residue)
        residue = (10 * residue + 144 * numerator) % modulus
    assert answer[-1] == ((pow(10, upper, modulus) - 16) * numerator) % modulus
    return answer


def directed_pi_digits(decimal_places: int) -> str:
    precision = math.ceil((decimal_places + 30) * math.log2(10))
    scale = gmpy2.mpz(10) ** decimal_places
    down = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    with down:
        lower = gmpy2.floor(gmpy2.const_pi() * scale)
    with up:
        upper = gmpy2.floor(gmpy2.const_pi() * scale)
    assert lower == upper
    text = str(lower)
    assert text[0] == "3" and len(text) == decimal_places + 1
    return text[1:]


def sixteen_pi_prefix(pi_digits: str, width: int) -> int:
    places = len(pi_digits)
    scaled_pi_floor = int("3" + pi_digits)
    divisor = 10 ** (places - width)
    lower = (16 * scaled_pi_floor) // divisor
    upper = (16 * (scaled_pi_floor + 1)) // divisor
    assert lower == upper
    return lower % (10**width)


def shadow_phase_residues(
    depth: int, pi_digits: str, sixteen_pi: int, width: int
) -> list[int]:
    modulus = 10**width
    return [
        (int(pi_digits[n : n + width]) - sixteen_pi) % modulus
        for n in range(depth, exact_upper(depth) + 1)
    ]


def certified_bandwidth(length: int) -> int:
    """Certify floor(length / log(length)) with directed MPFR arithmetic."""
    precision = 256
    down = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    with down:
        log_lower = gmpy2.log(gmpy2.mpfr(length))
    with up:
        log_upper = gmpy2.log(gmpy2.mpfr(length))
    with down:
        quotient_lower = gmpy2.mpfr(length) / log_upper
    with up:
        quotient_upper = gmpy2.mpfr(length) / log_lower
    lower_floor = int(gmpy2.floor(quotient_lower))
    upper_floor = int(gmpy2.floor(quotient_upper))
    assert lower_floor == upper_floor
    return lower_floor


def certify_labels(
    residues: list[int], modulus: int, bandwidth: int, phase_error: Fraction
) -> list[int]:
    if phase_error:
        minimum = modulus
        for residue in residues:
            boundary_residue = (bandwidth * residue) % modulus
            minimum = min(minimum, boundary_residue, modulus - boundary_residue)
        assert Fraction(minimum, modulus) > bandwidth * phase_error
    labels = [(bandwidth * residue) // modulus for residue in residues]
    assert all(0 <= label < bandwidth for label in labels)
    return labels


def dft_inverse_error(histogram: np.ndarray) -> float:
    transform = np.fft.fft(histogram)
    recovered = np.fft.ifft(transform)
    return float(np.max(np.abs(recovered.real - histogram)))


def largest_decimal_power_below(numerator: int, denominator: int) -> int:
    """Largest d >= 0 certified by numerator/denominator < 10^-d."""
    assert 0 < numerator < denominator
    exponent = max(0, len(str(denominator)) - len(str(numerator)) - 1)
    while numerator * 10 ** (exponent + 1) < denominator:
        exponent += 1
    while numerator * 10**exponent >= denominator:
        exponent -= 1
    return exponent


def primary_preserving_collapsed_countermodel(
    ambient: int,
    stage: str,
    reduced_exponent: int,
    depth: int,
    partial: Fraction,
    bandwidth: int,
) -> dict[str, int]:
    """Small coprime numerator with the actual complete primary coordinate."""
    modulus = partial.denominator
    numerator = partial.numerator
    primary_modulus = 3**reduced_exponent
    assert modulus % primary_modulus == 0
    cofactor = modulus // primary_modulus
    actual_primary = numerator * pow(cofactor, -1, primary_modulus)
    actual_primary %= primary_modulus

    residue = numerator % primary_modulus
    lift = 0
    while math.gcd(residue + lift * primary_modulus, modulus) != 1:
        lift += 1
    alternative = residue + lift * primary_modulus
    assert alternative % primary_modulus == numerator % primary_modulus
    alternative_primary = alternative * pow(cofactor, -1, primary_modulus)
    assert alternative_primary % primary_modulus == actual_primary

    upper = exact_upper(depth)
    arc_numerator = (10**upper - 16) * alternative
    assert arc_numerator * bandwidth < modulus
    arc_power = largest_decimal_power_below(arc_numerator, modulus)

    period = 3 ** (reduced_exponent - 2)
    primary_values = {
        ((10**n - 16) * alternative * pow(cofactor, -1, primary_modulus))
        % primary_modulus
        for n in range(depth, depth + period)
    }
    assert len(primary_values) == period
    assert bandwidth < depth
    return {
        "ambient": ambient,
        "stage": 0 if stage == "pre-drop" else 1,
        "lift": lift,
        "numerator": alternative,
        "arc_power": arc_power,
        "period": period,
    }


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    for relative, expected in PINS.items():
        actual = sha256(ROOT / relative)
        assert actual == expected, (relative, expected, actual)

    exact_sums = exact_partial_sums()
    shadow_targets = [
        depth
        for ambient in SHADOW_EXPONENTS
        for depth, _, _ in endpoint_rows(ambient)
    ]
    decimal_places = max(exact_upper(depth) for depth in shadow_targets)
    decimal_places += GUARD_DIGITS + 5
    pi_digits = directed_pi_digits(decimal_places)
    sixteen_pi = sixteen_pi_prefix(pi_digits, GUARD_DIGITS)

    record_lines = []
    countermodel_lines = []
    absolute_moment_failures = 0
    energy_failures = 0
    for ambient in AMBIENT_EXPONENTS:
        for depth, stage, reduced_exponent in endpoint_rows(ambient):
            upper = exact_upper(depth)
            length = upper - depth + 1
            bandwidth = certified_bandwidth(length)
            if ambient in EXACT_EXPONENTS:
                partial = exact_sums[ambient, stage]
                residues = exact_phase_residues(depth, partial)
                modulus = partial.denominator
                phase_error = Fraction()
            else:
                modulus = 10**GUARD_DIGITS
                residues = shadow_phase_residues(
                    depth, pi_digits, sixteen_pi, GUARD_DIGITS
                )
                phase_error = Fraction(1, modulus) + Fraction(
                    1, 15 * (depth + 1) ** 2
                )
            assert len(residues) == length
            labels = certify_labels(residues, modulus, bandwidth, phase_error)
            histogram = np.bincount(labels, minlength=bandwidth)
            assert len(histogram) == bandwidth
            assert int(histogram.sum()) == length
            assert dft_inverse_error(histogram) < 1e-8

            minimum = int(histogram.min())
            maximum = int(histogram.max())
            assert minimum > 0
            centered_minimum = bandwidth * minimum - length
            centered_maximum = bandwidth * maximum - length
            energy = bandwidth * int(np.dot(histogram, histogram)) - length**2
            threshold_numerator = length**2
            threshold_denominator = bandwidth - 1
            energy_fails = energy * threshold_denominator >= threshold_numerator
            absolute_fails = centered_maximum >= length
            energy_failures += int(energy_fails)
            absolute_moment_failures += int(absolute_fails)

            record_lines.append(
                "|".join(
                    str(value)
                    for value in (
                        ambient,
                        stage,
                        depth,
                        upper,
                        length,
                        bandwidth,
                        minimum,
                        maximum,
                        centered_minimum,
                        centered_maximum,
                        energy,
                        threshold_numerator,
                        threshold_denominator,
                        int(energy_fails),
                        int(absolute_fails),
                    )
                )
            )

            if ambient in EXACT_EXPONENTS:
                countermodel = primary_preserving_collapsed_countermodel(
                    ambient,
                    stage,
                    reduced_exponent,
                    depth,
                    exact_sums[ambient, stage],
                    bandwidth,
                )
                countermodel_lines.append(
                    "|".join(
                        str(value)
                        for value in (
                            ambient,
                            stage,
                            depth,
                            reduced_exponent,
                            bandwidth,
                            countermodel["period"],
                            countermodel["lift"],
                            countermodel["numerator"],
                            countermodel["arc_power"],
                        )
                    )
                )

    assert energy_failures == 8
    assert absolute_moment_failures == 6

    # The independent Peres--Yang audit found an empty histogram with the
    # same scalar nonzero DFT energy as the covered e=6 pre-drop histogram.
    # This is stronger than merely crossing the Cauchy energy threshold.
    isospectral_empty = [6] * 6 + [5] * 11 + [1] * 2 + [0]
    assert len(isospectral_empty) == 20
    assert sum(isospectral_empty) == 93
    assert min(isospectral_empty) == 0
    isospectral_energy = 20 * sum(c * c for c in isospectral_empty) - 93**2
    assert isospectral_energy == 1211
    isospectral_line = (
        "isospectral-empty|L=93|K=20|hist=6^6,5^11,1^2,0|energy=1211"
    )

    record = "\n".join(
        record_lines + countermodel_lines + [isospectral_line]
    ) + "\n"
    digest = hashlib.sha256(record.encode()).hexdigest()
    if EXPECTED_RECORD_SHA256 != "TO_BE_FILLED":
        assert digest == EXPECTED_RECORD_SHA256, (digest, EXPECTED_RECORD_SHA256)

    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print(f"gmpy2_version={gmpy2.version()}")
    print(f"mpfr_version={gmpy2.mpfr_version()}")
    print(f"decimal_guard_digits={GUARD_DIGITS}")
    for line in record_lines:
        (
            ambient,
            stage,
            depth,
            upper,
            length,
            bandwidth,
            minimum,
            maximum,
            centered_minimum,
            centered_maximum,
            energy,
            threshold_numerator,
            threshold_denominator,
            energy_fails,
            absolute_fails,
        ) = line.split("|")
        print(
            f"actual_row=e{ambient}/{stage};M={depth};U={upper};L={length};"
            f"K={bandwidth};cell_min={minimum};cell_max={maximum};"
            f"negative_trough={centered_minimum};positive_peak={centered_maximum};"
            f"nonzero_dft_energy={energy};"
            f"empty_energy_threshold={threshold_numerator}/{threshold_denominator};"
            f"energy_certificate_fails={bool(int(energy_fails))};"
            f"absolute_supnorm_certificate_fails={bool(int(absolute_fails))}"
        )
    for line in countermodel_lines:
        (
            ambient,
            stage,
            depth,
            reduced_exponent,
            bandwidth,
            period,
            lift,
            numerator,
            arc_power,
        ) = line.split("|")
        print(
            f"countermodel=e{ambient}/{stage};M={depth};E={reduced_exponent};"
            f"K={bandwidth};primary_period={period};lift={lift};"
            f"alternative_numerator={numerator};"
            f"complete_row_arc_lt=10^-{arc_power};all_cell_labels_zero=true"
        )
    print(f"actual_row_count={len(record_lines)}")
    print(f"countermodel_count={len(countermodel_lines)}")
    print(f"energy_certificate_failure_count={energy_failures}")
    print(f"absolute_supnorm_failure_count={absolute_moment_failures}")
    print("isospectral_empty_histogram=6^6,5^11,1^2,0")
    print(f"isospectral_empty_nonzero_dft_energy={isospectral_energy}")
    print(f"exact_record_sha256={digest}")
    print("asserts_growing_band_bound=false")
    print("asserts_endpoint_gap_law=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
