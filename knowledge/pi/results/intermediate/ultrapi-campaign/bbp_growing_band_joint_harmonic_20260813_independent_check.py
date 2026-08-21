#!/usr/bin/env python3
"""Disjoint replay for the BBP growing-band joint-harmonic audit.

All bounded conclusions in this file have claim label ``experiment``.  The
script imports no primary checker.  Exact ``Fraction`` arithmetic is used for
the six rows through e=8 and for all same-denominator countermodels.  The four
larger rows use a fresh directed 70-decimal MPFR shadow and the positive BBP
tail bound.  Occupancies, troughs, peaks, and energies are integer-exact after
the labels are certified.
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

import gmpy2


sys.set_int_max_str_digits(5_000_000)

SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
FROZEN = {
    "problems/local/pi-digits.txt": SOURCE_SHA256,
    "work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813.md":
        "e44096cba88629cce55668332096c22f14950ff9e6c209cdd6b0a1cd36c776b6",
    "work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_check.py":
        "edd7cdb4971b3969aaa05f3764036f7ad78cfecfe1a5362c9d5e1a00b981b30b",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813.md":
        "3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60",
    "work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_audit.md":
        "8c138103b4b2afb3e2b6e559c147c9b1ed69495e3689c1d00fa9fe50cee062ff",
}

AMBIENT_EXPONENTS = (4, 6, 8, 10, 12)
EXACT_EXPONENTS = (4, 6, 8)
SHADOW_EXPONENTS = (10, 12)
DECIMAL_WIDTH = 70

EXPECTED_ROWS = {
    (4, "pre-drop"): (49, 59, 11, 4, 2, 3, -3, 1, 3, False, False),
    (4, "first-drop"): (50, 60, 11, 4, 2, 3, -3, 1, 3, False, False),
    (6, "pre-drop"): (454, 546, 93, 20, 2, 7, -53, 47, 1211, True, False),
    (6, "first-drop"): (455, 547, 93, 20, 2, 7, -53, 47, 1051, True, False),
    (8, "pre-drop"): (4099, 4935, 837, 124, 2, 14, -589, 899, 101339, True, True),
    (8, "first-drop"): (4100, 4936, 837, 124, 2, 14, -589, 899, 101835, True, True),
    (10, "pre-drop"): (36904, 44436, 7533, 843, 2, 21, -5847, 10170, 6683760, True, True),
    (10, "first-drop"): (36905, 44438, 7534, 843, 2, 21, -5848, 10169, 6686396, True, True),
    (12, "pre-drop"): (332149, 399947, 67799, 6094, 1, 28, -61705, 102833, 403489633, True, True),
    (12, "first-drop"): (332150, 399948, 67799, 6094, 1, 28, -61705, 102833, 403587137, True, True),
}

EXPECTED_COUNTERMODELS = {
    (4, "pre-drop"): (4, 9, 7, 617, 126),
    (4, "first-drop"): (3, 3, 9, 263, 129),
    (6, "pre-drop"): (6, 81, 4, 3307, 1183),
    (6, "first-drop"): (5, 27, 14, 3547, 1185),
    (8, "pre-drop"): (8, 729, 12, 79039, 10676),
    (8, "first-drop"): (7, 243, 11, 26171, 10682),
}

EXPECTED_RECORD_SHA256 = (
    "3212a0030910842034d223bf495077502306bd8e2e63d7b7539a2558857db3b3"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoint_rows(ambient: int) -> tuple[tuple[int, str, int], ...]:
    base = (3**ambient - 1) // 8
    return (
        (5 * base - 1, "pre-drop", ambient),
        (5 * base, "first-drop", ambient - 1),
    )


def four_pole(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def combined_term(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def exact_partial_sums() -> dict[tuple[int, str], Fraction]:
    targets = {
        depth: (ambient, stage)
        for ambient in EXACT_EXPONENTS
        for depth, stage, _ in endpoint_rows(ambient)
    }
    power16 = 1
    partial = Fraction()
    answer: dict[tuple[int, str], Fraction] = {}
    for index in range(max(targets) + 1):
        if index:
            power16 *= 16
        term = combined_term(index)
        assert term == four_pole(index)
        partial += term / power16
        if index in targets:
            answer[targets[index]] = partial
    return answer


def exact_upper(depth: int) -> int:
    power = gmpy2.mpz(16) ** depth
    digits = gmpy2.num_digits(power, 10)
    # GMP documents that num_digits may overestimate by one in non-power-of-2
    # bases.  Resolve that explicitly with exact integer comparisons.
    if power < 10 ** (digits - 1):
        digits -= 1
    elif power >= 10**digits:
        digits += 1
    upper = digits - 1
    assert 10**upper <= power < 10 ** (upper + 1)
    return upper


def certified_bandwidth(length: int) -> int:
    precision = 384
    downward = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    upward = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    with downward:
        log_lower = gmpy2.log(gmpy2.mpfr(length))
    with upward:
        log_upper = gmpy2.log(gmpy2.mpfr(length))
    with downward:
        lower = gmpy2.mpfr(length) / log_upper
    with upward:
        upper = gmpy2.mpfr(length) / log_lower
    lower_floor = int(gmpy2.floor(lower))
    upper_floor = int(gmpy2.floor(upper))
    assert lower_floor == upper_floor

    # A separate Decimal evaluation guards against a shared MPFR setup error.
    with localcontext() as context:
        context.prec = 80
        decimal_value = Decimal(length) / Decimal(length).ln()
        assert int(decimal_value) == lower_floor
    return lower_floor


def exact_residues(depth: int, partial: Fraction) -> list[int]:
    numerator = partial.numerator
    denominator = partial.denominator
    upper = exact_upper(depth)
    residue = numerator * (pow(10, depth, denominator) - 16) % denominator
    result: list[int] = []
    for _ in range(depth, upper + 1):
        result.append(residue)
        residue = (10 * residue + 144 * numerator) % denominator
    assert result[-1] == (
        numerator * (pow(10, upper, denominator) - 16) % denominator
    )
    return result


def certified_pi_digits(places: int) -> str:
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


def certified_sixteen_pi(width: int) -> int:
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


def shadow_residues(
    depth: int, digits: str, sixteen_pi: int
) -> list[int]:
    scale = 10**DECIMAL_WIDTH
    return [
        (int(digits[exponent : exponent + DECIMAL_WIDTH]) - sixteen_pi)
        % scale
        for exponent in range(depth, exact_upper(depth) + 1)
    ]


def labels_with_certificate(
    residues: list[int], modulus: int, bandwidth: int, error: Fraction
) -> tuple[list[int], Fraction]:
    minimum_distance = modulus
    for residue in residues:
        position = bandwidth * residue % modulus
        minimum_distance = min(
            minimum_distance, position, modulus - position
        )
    if error:
        assert Fraction(minimum_distance, modulus) > bandwidth * error
    labels = [bandwidth * residue // modulus for residue in residues]
    assert all(0 <= label < bandwidth for label in labels)
    return labels, Fraction(minimum_distance, modulus)


def quantization_identity_count(
    residues: list[int], modulus: int, bandwidth: int
) -> int:
    checked = 0
    for residue in residues:
        label = bandwidth * residue // modulus
        theta_numerator = bandwidth * residue - label * modulus
        assert 0 <= theta_numerator < modulus
        # Cross-multiply GB7 exactly, avoiding any rational normalization:
        # label/K = residue/D - theta_num/(K*D).
        assert label * modulus == bandwidth * residue - theta_numerator
        checked += 1
    return checked


def analyze_histogram(
    ambient: int,
    stage: str,
    depth: int,
    labels: list[int],
    bandwidth: int,
    boundary_distance: Fraction,
) -> dict[str, object]:
    length = len(labels)
    counts = Counter(labels)
    histogram = [counts.get(cell, 0) for cell in range(bandwidth)]
    assert sum(histogram) == length
    minimum = min(histogram)
    maximum = max(histogram)
    trough = bandwidth * minimum - length
    peak = bandwidth * maximum - length
    energy = bandwidth * sum(value * value for value in histogram) - length**2
    energy_fails = energy * (bandwidth - 1) >= length**2
    absolute_fails = peak >= length
    upper = exact_upper(depth)
    expected = EXPECTED_ROWS[ambient, stage]
    observed = (
        depth,
        upper,
        length,
        bandwidth,
        minimum,
        maximum,
        trough,
        peak,
        energy,
        energy_fails,
        absolute_fails,
    )
    assert observed == expected
    if ambient == 12:
        assert trough == -length + bandwidth
        assert minimum == 1
    return {
        "ambient": ambient,
        "stage": stage,
        "depth": depth,
        "upper": upper,
        "length": length,
        "bandwidth": bandwidth,
        "minimum_occupancy": minimum,
        "maximum_occupancy": maximum,
        "negative_trough": trough,
        "positive_peak": peak,
        "energy": energy,
        "empty_energy_threshold": f"{length**2}/{bandwidth - 1}",
        "energy_certificate_fails": energy_fails,
        "absolute_supnorm_certificate_fails": absolute_fails,
        "boundary_distance": (
            f"{boundary_distance.numerator}/{boundary_distance.denominator}"
        ),
    }


def diagonal_and_crt_checks(
    depth: int,
    reduced_exponent: int,
    partial: Fraction,
    bandwidth: int,
) -> dict[str, int]:
    denominator = partial.denominator
    numerator = partial.numerator
    primary_modulus = 3**reduced_exponent
    assert denominator % primary_modulus == 0
    complement_modulus = denominator // primary_modulus
    assert math.gcd(primary_modulus, complement_modulus) == 1
    primary_numerator = (
        numerator * pow(complement_modulus, -1, primary_modulus)
        % primary_modulus
    )
    complement_numerator = (
        numerator * pow(primary_modulus, -1, complement_modulus)
        % complement_modulus
    )
    reconstructed = (
        primary_numerator * complement_modulus
        + complement_numerator * primary_modulus
    )
    assert (reconstructed - numerator) % denominator == 0

    point_checks = 0
    diagonal_checks = 0
    harmonics = sorted({1, 2, 3, max(1, bandwidth - 1)})
    residual = pow(10, depth, denominator) - 16
    for exponent in range(depth, exact_upper(depth) + 1):
        assert (
            residual * reconstructed - residual * numerator
        ) % denominator == 0
        point_checks += 1
        for harmonic in harmonics:
            # GB16: b=h*a and the complement is raised to h.
            primary_part = (
                harmonic * primary_numerator * residual
            ) % primary_modulus
            complement_part = (
                harmonic * complement_numerator * residual
            ) % complement_modulus
            recombined = (
                primary_part * complement_modulus
                + complement_part * primary_modulus
            ) % denominator
            assert recombined == harmonic * numerator * residual % denominator

            # The artificial W=conj(e_q(aR)) is exactly resonant at b=h*a.
            artificial_complement = -harmonic * primary_numerator * residual
            assert (primary_part + artificial_complement) % primary_modulus == 0
            diagonal_checks += 1
        residual = (10 * residual + 144) % denominator

    period = 3 ** (reduced_exponent - 2)
    multiplicities = Counter(
        exponent % period
        for exponent in range(depth, exact_upper(depth) + 1)
    )
    collision_pairs = sum(value * value for value in multiplicities.values())
    length = exact_upper(depth) - depth + 1
    assert collision_pairs <= math.ceil(length / period) * length
    nonunit_harmonics = (bandwidth - 1) // 3
    return {
        "crt_point_checks": point_checks,
        "diagonal_harmonic_checks": diagonal_checks,
        "primary_period": period,
        "horizontal_collision_pairs": collision_pairs,
        "nonunit_diagonal_harmonics": nonunit_harmonics,
    }


def decimal_arc_power(numerator: int, denominator: int) -> int:
    assert 0 < numerator < denominator
    power = max(0, len(str(denominator)) - len(str(numerator)) - 1)
    while numerator * 10 ** (power + 1) < denominator:
        power += 1
    while numerator * 10**power >= denominator:
        power -= 1
    assert numerator * 10**power < denominator
    assert numerator * 10 ** (power + 1) >= denominator
    return power


def countermodel(
    ambient: int,
    stage: str,
    depth: int,
    reduced_exponent: int,
    partial: Fraction,
    bandwidth: int,
) -> dict[str, object]:
    denominator = partial.denominator
    numerator = partial.numerator
    primary_modulus = 3**reduced_exponent
    assert denominator % primary_modulus == 0
    complement = denominator // primary_modulus

    residue = numerator % primary_modulus
    lift = 0
    while math.gcd(residue + lift * primary_modulus, denominator) != 1:
        lift += 1
    alternative = residue + lift * primary_modulus
    assert math.gcd(alternative, denominator) == 1
    assert alternative % primary_modulus == numerator % primary_modulus

    actual_coordinate = numerator * pow(complement, -1, primary_modulus)
    alternative_coordinate = alternative * pow(
        complement, -1, primary_modulus
    )
    assert (actual_coordinate - alternative_coordinate) % primary_modulus == 0

    upper = exact_upper(depth)
    largest_phase_numerator = (10**upper - 16) * alternative
    assert largest_phase_numerator * bandwidth < denominator
    arc_power = decimal_arc_power(largest_phase_numerator, denominator)

    phase_numerator = (10**depth - 16) * alternative
    labels_checked = 0
    for _ in range(depth, upper + 1):
        assert 0 < phase_numerator < denominator
        assert bandwidth * phase_numerator // denominator == 0
        phase_numerator = 10 * phase_numerator + 144 * alternative
        labels_checked += 1

    period = 3 ** (reduced_exponent - 2)
    primary_values: set[int] = set()
    residual = pow(10, depth, primary_modulus) - 16
    coordinate = alternative_coordinate % primary_modulus
    for _ in range(period):
        primary_values.add(residual * coordinate % primary_modulus)
        residual = (10 * residual + 144) % primary_modulus
    assert len(primary_values) == period
    assert bandwidth < depth

    expected = EXPECTED_COUNTERMODELS[ambient, stage]
    assert (
        reduced_exponent,
        period,
        lift,
        alternative,
        arc_power,
    ) == expected
    return {
        "ambient": ambient,
        "stage": stage,
        "depth": depth,
        "reduced_exponent": reduced_exponent,
        "bandwidth": bandwidth,
        "primary_period": period,
        "lift": lift,
        "alternative_numerator": alternative,
        "arc_power": arc_power,
        "all_labels_zero": True,
        "labels_checked": labels_checked,
        "same_reduced_denominator": True,
        "same_primary_coordinate": True,
        "high_prime_primitivity_scope": "h<K<M<p and gcd(Pprime,D)=1",
    }


def isospectral_energy_check() -> dict[str, object]:
    histogram = [6] * 6 + [5] * 11 + [1] * 2 + [0]
    assert len(histogram) == 20
    assert sum(histogram) == 93
    assert min(histogram) == 0
    energy = 20 * sum(value * value for value in histogram) - 93**2
    assert energy == 1211
    return {
        "histogram": "6^6,5^11,1^2,0",
        "length": 93,
        "bandwidth": 20,
        "empty": True,
        "energy": energy,
    }


def main() -> None:
    observed_frozen = {
        relative: sha256(root() / relative)
        for relative in FROZEN
    }
    assert observed_frozen == FROZEN
    exact_sums = exact_partial_sums()

    maximum_places = max(
        exact_upper(depth)
        for ambient in SHADOW_EXPONENTS
        for depth, _, _ in endpoint_rows(ambient)
    ) + DECIMAL_WIDTH + 5
    digits = certified_pi_digits(maximum_places)
    sixteen_pi = certified_sixteen_pi(DECIMAL_WIDTH)

    rows: list[dict[str, object]] = []
    countermodels: list[dict[str, object]] = []
    diagonal_records: list[dict[str, object]] = []
    quantization_checks = 0
    for ambient in AMBIENT_EXPONENTS:
        for depth, stage, reduced_exponent in endpoint_rows(ambient):
            upper = exact_upper(depth)
            length = upper - depth + 1
            bandwidth = certified_bandwidth(length)
            if ambient in EXACT_EXPONENTS:
                partial = exact_sums[ambient, stage]
                residues = exact_residues(depth, partial)
                modulus = partial.denominator
                error = Fraction()
                quantization_checks += quantization_identity_count(
                    residues, modulus, bandwidth
                )
            else:
                modulus = 10**DECIMAL_WIDTH
                residues = shadow_residues(depth, digits, sixteen_pi)
                # The two decimal truncation errors differ by less than one
                # unit at this scale.  The BBP tail contributes the second
                # term uniformly because 10^n <= 16^M throughout the row.
                error = Fraction(1, modulus) + Fraction(
                    1, 15 * (depth + 1) ** 2
                )
            labels, boundary_distance = labels_with_certificate(
                residues, modulus, bandwidth, error
            )
            rows.append(analyze_histogram(
                ambient,
                stage,
                depth,
                labels,
                bandwidth,
                boundary_distance,
            ))

            if ambient in EXACT_EXPONENTS:
                partial = exact_sums[ambient, stage]
                diagonal_records.append(diagonal_and_crt_checks(
                    depth, reduced_exponent, partial, bandwidth
                ))
                countermodels.append(countermodel(
                    ambient,
                    stage,
                    depth,
                    reduced_exponent,
                    partial,
                    bandwidth,
                ))

    energy_failures = sum(
        int(row["energy_certificate_fails"]) for row in rows
    )
    absolute_failures = sum(
        int(row["absolute_supnorm_certificate_fails"]) for row in rows
    )
    assert len(rows) == 10
    assert len(countermodels) == 6
    assert energy_failures == 8
    assert absolute_failures == 6
    assert quantization_checks == 1882

    record = {
        "claim_label": "experiment",
        "rows": rows,
        "countermodels": countermodels,
        "diagonal_records": diagonal_records,
        "quantization_exact_points": quantization_checks,
        "isospectral": isospectral_energy_check(),
        "energy_certificate_failure_count": energy_failures,
        "absolute_supnorm_failure_count": absolute_failures,
        "frozen": observed_frozen,
        "unit_slice_covers_all_growing_h": False,
        "full_additive_slice_available": True,
        "asserts_growing_band_bound": False,
        "asserts_endpoint_gap_law": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    if EXPECTED_RECORD_SHA256:
        assert digest == EXPECTED_RECORD_SHA256

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print(f"decimal_guard_digits={DECIMAL_WIDTH}")
    for row in rows:
        print(
            f"actual_row=e{row['ambient']}/{row['stage']};"
            f"M={row['depth']};U={row['upper']};L={row['length']};"
            f"K={row['bandwidth']};cell_min={row['minimum_occupancy']};"
            f"cell_max={row['maximum_occupancy']};"
            f"negative_trough={row['negative_trough']};"
            f"positive_peak={row['positive_peak']};energy={row['energy']}"
        )
    for model in countermodels:
        print(
            f"countermodel=e{model['ambient']}/{model['stage']};"
            f"M={model['depth']};E={model['reduced_exponent']};"
            f"K={model['bandwidth']};period={model['primary_period']};"
            f"lift={model['lift']};Pprime={model['alternative_numerator']};"
            f"arc_lt=10^-{model['arc_power']};all_labels_zero=true"
        )
    print(f"quantization_exact_points={quantization_checks}")
    print("diagonal_exact_rows=6")
    print("unit_slice_covers_all_growing_h=false")
    print("full_additive_slice_available=true")
    print(f"energy_certificate_failure_count={energy_failures}")
    print(f"absolute_supnorm_failure_count={absolute_failures}")
    print("isospectral_empty_energy=1211")
    print(f"exact_record_sha256={digest}")
    print("asserts_growing_band_bound=false")
    print("asserts_endpoint_gap_law=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
