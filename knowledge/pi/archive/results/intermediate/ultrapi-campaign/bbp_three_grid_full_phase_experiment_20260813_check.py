#!/usr/bin/env python3
"""Certified finite experiment for the full BBP phase on 3-primary epochs.

Every numerical conclusion produced here has claim label ``experiment``.
For e = 4, 6, 8 the BBP partial sum is constructed as an exact Fraction.
For e = 10, 12, 14 a directed-rounding MPFR enclosure of pi is combined
with the proved positive BBP-tail bound.  Thus every reported full-phase
target distance, circular gap, Fourier magnitude, and ternary correlation is
either exact or enclosed by an explicit error interval.

The script imports no branch checker and proves neither a fixed return nor V1.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
THREE_PRIMARY_REPORT_SHA256 = (
    "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7"
)
ODD_COFACTOR_REPORT_SHA256 = (
    "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3"
)
EXPECTED_RECORD_SHA256 = (
    "2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d"
)

EXACT_AMBIENT_EXPONENTS = (4, 6, 8)
SHADOW_AMBIENT_EXPONENTS = (10, 12, 14)
ALL_AMBIENT_EXPONENTS = EXACT_AMBIENT_EXPONENTS + SHADOW_AMBIENT_EXPONENTS
DECIMAL_GUARD_DIGITS = 50
FOURIER_PRECISION_BITS = 256
FOURIER_FREQUENCIES = (1, 2)


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


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


def partial_fraction_coefficient(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(1, 2 * (2 * index + 1))
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 2 * (4 * index + 3))
    )


def valuation(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("valuation at zero is not used")
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        answer += 1
        integer //= prime
    return answer


def exact_upper(depth: int) -> int:
    """Return floor(log_10(16**depth)) by an exact integer conversion."""
    return len(str(1 << (4 * depth))) - 1


def endpoint_rows(ambient: int) -> tuple[tuple[int, str, int], ...]:
    a_value = (3**ambient - 1) // 8
    return (
        (5 * a_value - 1, "pre-drop", ambient),
        (5 * a_value, "first-drop", ambient - 1),
    )


def exact_partial_sums() -> dict[tuple[int, str], Fraction]:
    targets = {
        depth: (ambient, stage)
        for ambient in EXACT_AMBIENT_EXPONENTS
        for depth, stage, _ in endpoint_rows(ambient)
    }
    maximum = max(targets)
    answer: dict[tuple[int, str], Fraction] = {}
    partial = Fraction()
    power_of_sixteen = 1
    for depth in range(maximum + 1):
        if depth:
            power_of_sixteen *= 16
        value = coefficient(depth)
        if value != partial_fraction_coefficient(depth):
            raise AssertionError(("partial-fraction identity", depth))
        partial += value / power_of_sixteen
        if depth in targets:
            ambient, stage = targets[depth]
            answer[ambient, stage] = partial
    return answer


def endpoint_three_units() -> dict[tuple[int, str], int]:
    """Compute endpoint beta values in one exact Z/3^14 Z prefix pass.

    Every individual pole through the e=14 first-drop endpoint has 3-height
    at most 14.  We therefore sum 3^14 B_M modulo 3^14 term by term.  At an
    endpoint of reduced denominator exponent E, division by 3^(14-E) recovers
    beta = 3^E B_M modulo 3^E.
    """
    top = max(ALL_AMBIENT_EXPONENTS)
    modulus = 3**top
    targets: dict[int, tuple[int, str, int]] = {}
    for ambient in ALL_AMBIENT_EXPONENTS:
        for depth, stage, reduced_exponent in endpoint_rows(ambient):
            targets[depth] = (ambient, stage, reduced_exponent)

    maximum = max(targets)
    inverse_sixteen = pow(16, -1, modulus)
    inverse_power = 1
    scaled_sum = 0
    answer: dict[tuple[int, str], int] = {}
    for index in range(maximum + 1):
        value = coefficient(index)
        height = valuation(value.denominator, 3)
        if height > top:
            raise AssertionError(("unexpected pole height", index, height))
        unit_denominator = value.denominator // (3**height)
        term = (
            value.numerator
            * 3 ** (top - height)
            * pow(unit_denominator, -1, modulus)
            * inverse_power
        ) % modulus
        scaled_sum = (scaled_sum + term) % modulus
        if index in targets:
            ambient, stage, reduced_exponent = targets[index]
            divisor = 3 ** (top - reduced_exponent)
            if scaled_sum % divisor:
                raise AssertionError(
                    ("endpoint unit not divisible", ambient, stage, scaled_sum)
                )
            beta = (scaled_sum // divisor) % (3**reduced_exponent)
            if beta % 3 != 2:
                raise AssertionError(("wrong leading endpoint unit", ambient, stage))
            answer[ambient, stage] = beta
        inverse_power = inverse_power * inverse_sixteen % modulus
    return answer


def directed_pi_digits(decimal_places: int) -> str:
    """Certify floor(pi*10^decimal_places), then return fractional digits."""
    binary_precision = math.ceil((decimal_places + 30) * math.log2(10))
    scale = gmpy2.mpz(10) ** decimal_places
    down = gmpy2.context(
        gmpy2.get_context(),
        precision=binary_precision,
        round=gmpy2.RoundDown,
    )
    up = gmpy2.context(
        gmpy2.get_context(),
        precision=binary_precision,
        round=gmpy2.RoundUp,
    )
    with down:
        lower_floor = gmpy2.floor(gmpy2.const_pi() * scale)
    with up:
        upper_floor = gmpy2.floor(gmpy2.const_pi() * scale)
    if lower_floor != upper_floor:
        raise AssertionError("directed MPFR endpoints do not certify pi prefix")
    text = str(lower_floor)
    if len(text) != decimal_places + 1 or text[0] != "3":
        raise AssertionError("unexpected certified pi prefix")
    return text[1:]


def sixteen_pi_prefix(pi_digits: str, width: int) -> int:
    """Certify floor(fract(16*pi)*10^width) from the pi prefix."""
    places = len(pi_digits)
    scaled_pi_floor = int("3" + pi_digits)
    divisor = 10 ** (places - width)
    lower = (16 * scaled_pi_floor) // divisor
    upper = (16 * (scaled_pi_floor + 1)) // divisor
    if lower != upper:
        raise AssertionError("16*pi prefix is not certified")
    return lower % (10**width)


def exact_phase_residues(depth: int, partial: Fraction) -> list[int]:
    modulus = partial.denominator
    numerator = partial.numerator
    upper = exact_upper(depth)
    residue = ((pow(10, depth, modulus) - 16) * numerator) % modulus
    answer = []
    for _ in range(depth, upper + 1):
        answer.append(residue)
        residue = (10 * residue + 144 * numerator) % modulus
    direct_last = (
        (pow(10, upper, modulus) - 16) * numerator
    ) % modulus
    if answer[-1] != direct_last:
        raise AssertionError(("phase recurrence", depth))
    return answer


def shadow_phase_residues(
    depth: int,
    pi_digits: str,
    sixteen_pi: int,
    width: int,
) -> list[int]:
    upper = exact_upper(depth)
    modulus = 10**width
    return [
        (int(pi_digits[exponent : exponent + width]) - sixteen_pi) % modulus
        for exponent in range(depth, upper + 1)
    ]


def directed_decimal_text(
    value: gmpy2.mpfr,
    rounding: int,
    significant_digits: int = 19,
) -> str:
    """Render an MPFR endpoint outwards in scientific notation."""
    context = gmpy2.context(
        gmpy2.get_context(),
        precision=max(value.precision, 128),
        round=rounding,
    )
    with context:
        mantissa, exponent, _ = gmpy2.digits(
            value, 10, significant_digits
        )
    if mantissa == "0":
        return "0.000000000000000000e+0"
    sign = ""
    if mantissa.startswith("-"):
        sign = "-"
        mantissa = mantissa[1:]
    return (
        f"{sign}{mantissa[0]}.{mantissa[1:]}"
        f"e{exponent - 1:+d}"
    )


def interval_text(lower: gmpy2.mpfr, upper: gmpy2.mpfr) -> str:
    return (
        "["
        + directed_decimal_text(lower, gmpy2.RoundDown)
        + ","
        + directed_decimal_text(upper, gmpy2.RoundUp)
        + "]"
    )


def rational_interval_text(lower: Fraction, upper: Fraction) -> str:
    precision = 128
    down = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    with down:
        low_value = gmpy2.mpfr(gmpy2.mpq(lower.numerator, lower.denominator))
    with up:
        high_value = gmpy2.mpfr(gmpy2.mpq(upper.numerator, upper.denominator))
    return interval_text(low_value, high_value)


def sqrt_fraction_interval(value: Fraction) -> tuple[gmpy2.mpfr, gmpy2.mpfr]:
    precision = 128
    down = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    rational = gmpy2.mpq(value.numerator, value.denominator)
    with down:
        lower = gmpy2.sqrt(gmpy2.mpfr(rational))
    with up:
        upper = gmpy2.sqrt(gmpy2.mpfr(rational))
    return lower, upper


def gap_log_interval(
    gap_center: Fraction,
    phase_error: Fraction,
    count: int,
) -> tuple[gmpy2.mpfr, gmpy2.mpfr]:
    gap_lower = max(Fraction(), gap_center - 2 * phase_error)
    gap_upper = min(Fraction(1), gap_center + 2 * phase_error)
    precision = 160
    down = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=precision, round=gmpy2.RoundUp
    )
    with down:
        low_gap = gmpy2.mpfr(gmpy2.mpq(gap_lower.numerator, gap_lower.denominator))
        low_log = gmpy2.log(gmpy2.mpfr(count))
    with up:
        high_gap = gmpy2.mpfr(gmpy2.mpq(gap_upper.numerator, gap_upper.denominator))
        high_log = gmpy2.log(gmpy2.mpfr(count))
    with down:
        lower = low_gap * count / high_log
    with up:
        upper = high_gap * count / low_log
    return lower, upper


def fourier_magnitude_interval(
    residues: list[int],
    modulus: int,
    phase_error: Fraction,
    frequency: int,
) -> tuple[gmpy2.mpfr, gmpy2.mpfr]:
    """Enclose a Fourier magnitude with a loose audited MPFR error ledger."""
    count = len(residues)
    nearest = gmpy2.context(
        gmpy2.get_context(),
        precision=FOURIER_PRECISION_BITS,
        round=gmpy2.RoundToNearest,
    )
    with nearest:
        two_pi_h = 2 * frequency * gmpy2.const_pi()
        real_sum = gmpy2.mpfr(0)
        imag_sum = gmpy2.mpfr(0)
        for residue in residues:
            point = gmpy2.mpfr(gmpy2.mpq(residue, modulus))
            sine, cosine = gmpy2.sin_cos(two_pi_h * point)
            real_sum += cosine
            imag_sum += sine
        real_mean = real_sum / count
        imag_mean = imag_sum / count
        approximate = gmpy2.sqrt(real_mean * real_mean + imag_mean * imag_mean)

    # Each input reduction, angle operation, correctly-rounded sin/cos call,
    # sequential sum, division, and final norm is covered by this deliberately
    # loose envelope.  Since count < 2^20 and p=256 in the retained run, it is
    # below 2^-220.  The second term is the exact Lipschitz transfer from the
    # decimal pi shadow to the rational B_M phase.
    internal_exponent = (
        math.ceil(math.log2(count)) + 16 - FOURIER_PRECISION_BITS
    )
    internal_error = Fraction(2**max(internal_exponent, 0), 1)
    if internal_exponent < 0:
        internal_error = Fraction(1, 2 ** (-internal_exponent))

    down = gmpy2.context(
        gmpy2.get_context(),
        precision=FOURIER_PRECISION_BITS,
        round=gmpy2.RoundDown,
    )
    up = gmpy2.context(
        gmpy2.get_context(),
        precision=FOURIER_PRECISION_BITS,
        round=gmpy2.RoundUp,
    )
    error_rat = gmpy2.mpq(internal_error.numerator, internal_error.denominator)
    phase_rat = gmpy2.mpq(phase_error.numerator, phase_error.denominator)
    with up:
        error = gmpy2.mpfr(error_rat)
        error += 2 * gmpy2.const_pi() * frequency * gmpy2.mpfr(phase_rat)
        upper = min(gmpy2.mpfr(1), approximate + error)
    with down:
        lower = max(gmpy2.mpfr(0), approximate - error)
    # At e=10 the proved BBP-tail transfer itself has width about 10^-10;
    # the retained threshold is deliberately much larger than that transfer
    # while still detecting a lost-precision enclosure.
    if upper - lower > gmpy2.mpfr("1e-8"):
        raise AssertionError(("wide Fourier enclosure", count, frequency))
    return lower, upper


def analyze_row(
    ambient: int,
    stage: str,
    reduced_exponent: int,
    beta: int,
    residues: list[int],
    modulus: int,
    phase_error: Fraction,
    record_hasher: "hashlib._Hash",
) -> dict[str, object]:
    depth = dict(
        (row_stage, row_depth)
        for row_depth, row_stage, _ in endpoint_rows(ambient)
    )[stage]
    upper = exact_upper(depth)
    count = upper - depth + 1
    if len(residues) != count:
        raise AssertionError(("row length", ambient, stage))
    if len(set(residues)) != count:
        raise AssertionError(("phase-center collision", ambient, stage))
    dyadic_exponent = 4 * depth - valuation(depth + 1, 2)
    if upper >= dyadic_exponent:
        raise AssertionError(("dyadic distinctness bound", ambient, stage))

    residue_hasher = hashlib.sha256()
    residue_width = (modulus.bit_length() + 7) // 8
    for residue in residues:
        residue_hasher.update(residue.to_bytes(residue_width, "big"))
    residue_digest = residue_hasher.hexdigest()

    ordered = sorted(residues)
    gaps = [
        ordered[index + 1] - ordered[index]
        for index in range(count - 1)
    ]
    gaps.append(modulus + ordered[0] - ordered[-1])
    largest_gap_numerator = max(gaps)
    target_numerator, target_exponent = min(
        (min(residue, modulus - residue), depth + offset)
        for offset, residue in enumerate(residues)
    )
    gap_center = Fraction(largest_gap_numerator, modulus)
    target_center = Fraction(target_numerator, modulus)
    gap_lower = max(Fraction(), gap_center - 2 * phase_error)
    gap_upper = min(Fraction(1), gap_center + 2 * phase_error)
    target_lower = max(Fraction(), target_center - phase_error)
    target_upper = min(Fraction(1, 2), target_center + phase_error)

    period = 3 ** (reduced_exponent - 2)
    primary_modulus = 3 * period
    leading_unit = beta % 3
    lifted = (pow(10, depth, 3 * primary_modulus) - 16) % (
        3 * primary_modulus
    )
    if lifted % 3:
        raise AssertionError(("residual quotient", ambient, stage))
    quotient = lifted // 3
    grid_counts = [0] * period
    ternary_counts = [0, 0, 0]
    minimum_boundary_numerator = 3 * modulus
    for residue in residues:
        delta = beta * quotient % primary_modulus
        grid_index = ((delta - leading_unit) % primary_modulus) // 3
        grid_counts[grid_index] += 1
        phase_bin = 3 * residue // modulus
        grid_bin = 3 * grid_index // period
        ternary_counts[(phase_bin - grid_bin) % 3] += 1
        boundary_coordinate = 3 * residue
        boundary_distance = min(
            abs(boundary_coordinate - boundary * modulus)
            for boundary in range(4)
        )
        minimum_boundary_numerator = min(
            minimum_boundary_numerator, boundary_distance
        )
        quotient = (10 * quotient + 48) % primary_modulus

    if min(grid_counts) == 0 or max(grid_counts) - min(grid_counts) > 1:
        raise AssertionError(("incomplete residual grid", ambient, stage))
    if phase_error:
        if (
            minimum_boundary_numerator * phase_error.denominator
            <= 3 * modulus * phase_error.numerator
        ):
            raise AssertionError(("uncertified ternary bin", ambient, stage))

    c0, c1, c2 = ternary_counts
    correlation_squared = Fraction(
        c0 * c0 + c1 * c1 + c2 * c2 - c0 * c1 - c1 * c2 - c2 * c0,
        count * count,
    )
    correlation_interval = sqrt_fraction_interval(correlation_squared)
    scaled_correlation_interval = sqrt_fraction_interval(
        correlation_squared * count
    )
    gap_log = gap_log_interval(gap_center, phase_error, count)
    fourier = {
        frequency: fourier_magnitude_interval(
            residues, modulus, phase_error, frequency
        )
        for frequency in FOURIER_FREQUENCIES
    }

    record = "|".join(
        str(value)
        for value in (
            ambient,
            stage,
            depth,
            upper,
            count,
            reduced_exponent,
            period,
            beta,
            modulus,
            phase_error.numerator,
            phase_error.denominator,
            target_numerator,
            target_exponent,
            largest_gap_numerator,
            minimum_boundary_numerator,
            *ternary_counts,
            correlation_squared.numerator,
            correlation_squared.denominator,
            residue_digest,
        )
    )
    record_hasher.update((record + "\n").encode())
    return {
        "ambient": ambient,
        "stage": stage,
        "depth": depth,
        "upper": upper,
        "count": count,
        "reduced_exponent": reduced_exponent,
        "period": period,
        "beta": beta,
        "target_interval": rational_interval_text(target_lower, target_upper),
        "target_exponent": target_exponent,
        "gap_interval": rational_interval_text(gap_lower, gap_upper),
        "mesh_interval": rational_interval_text(gap_lower / 2, gap_upper / 2),
        "gap_log_interval": interval_text(*gap_log),
        "fourier": {
            frequency: interval_text(*bounds)
            for frequency, bounds in fourier.items()
        },
        "ternary_counts": ternary_counts,
        "ternary_correlation": interval_text(*correlation_interval),
        "scaled_ternary_correlation": interval_text(
            *scaled_correlation_interval
        ),
        "residue_sha256": residue_digest,
    }


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)

    root = repository_root()
    pins = {
        root / "problems/local/pi-digits.txt": SOURCE_SHA256,
        root
        / "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md": (
            THREE_PRIMARY_REPORT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md": (
            ODD_COFACTOR_REPORT_SHA256
        ),
    }
    for path, expected in pins.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(("source pin", path, actual, expected))

    exact_sums = exact_partial_sums()
    units = endpoint_three_units()
    for ambient in EXACT_AMBIENT_EXPONENTS:
        for _, stage, reduced_exponent in endpoint_rows(ambient):
            value = exact_sums[ambient, stage]
            actual_exponent = valuation(value.denominator, 3)
            if actual_exponent != reduced_exponent:
                raise AssertionError(("exact denominator exponent", ambient, stage))
            cofactor = value.denominator // (3**reduced_exponent)
            beta = (
                value.numerator
                * pow(cofactor, -1, 3**reduced_exponent)
            ) % (3**reduced_exponent)
            if beta != units[ambient, stage]:
                raise AssertionError(("independent beta mismatch", ambient, stage))

    shadow_rows = [
        (depth, ambient, stage)
        for ambient in SHADOW_AMBIENT_EXPONENTS
        for depth, stage, _ in endpoint_rows(ambient)
    ]
    maximum_upper = max(exact_upper(depth) for depth, _, _ in shadow_rows)
    decimal_places = maximum_upper + DECIMAL_GUARD_DIGITS + 5
    pi_digits = directed_pi_digits(decimal_places)
    sixteen_pi = sixteen_pi_prefix(pi_digits, DECIMAL_GUARD_DIGITS)

    rows = []
    record_hasher = hashlib.sha256()
    for ambient in ALL_AMBIENT_EXPONENTS:
        for depth, stage, reduced_exponent in endpoint_rows(ambient):
            beta = units[ambient, stage]
            if ambient in EXACT_AMBIENT_EXPONENTS:
                partial = exact_sums[ambient, stage]
                residues = exact_phase_residues(depth, partial)
                modulus = partial.denominator
                phase_error = Fraction()
            else:
                residues = shadow_phase_residues(
                    depth,
                    pi_digits,
                    sixteen_pi,
                    DECIMAL_GUARD_DIGITS,
                )
                modulus = 10**DECIMAL_GUARD_DIGITS
                phase_error = Fraction(1, modulus) + Fraction(
                    1, 15 * (depth + 1) ** 2
                )
            rows.append(
                analyze_row(
                    ambient,
                    stage,
                    reduced_exponent,
                    beta,
                    residues,
                    modulus,
                    phase_error,
                    record_hasher,
                )
            )

    record_digest = record_hasher.hexdigest()
    if EXPECTED_RECORD_SHA256 != "TO_BE_FILLED":
        if record_digest != EXPECTED_RECORD_SHA256:
            raise AssertionError(
                ("exact record hash", record_digest, EXPECTED_RECORD_SHA256)
            )

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"three_primary_report_sha256={THREE_PRIMARY_REPORT_SHA256}")
    print(f"odd_cofactor_report_sha256={ODD_COFACTOR_REPORT_SHA256}")
    print(f"gmpy2_version={gmpy2.version()}")
    print(f"mpfr_version={gmpy2.mpfr_version()}")
    print(f"decimal_guard_digits={DECIMAL_GUARD_DIGITS}")
    print(f"fourier_precision_bits={FOURIER_PRECISION_BITS}")
    for row in rows:
        fourier_text = ",".join(
            f"h{frequency}:{row['fourier'][frequency]}"
            for frequency in FOURIER_FREQUENCIES
        )
        print(
            "row="
            f"e{row['ambient']}/{row['stage']};"
            f"M={row['depth']};U={row['upper']};L={row['count']};"
            f"E={row['reduced_exponent']};T={row['period']};"
            f"beta={row['beta']};"
            f"target={row['target_interval']}@n{row['target_exponent']};"
            f"largest_gap={row['gap_interval']};"
            f"target_mesh={row['mesh_interval']};"
            f"Lgap_over_logL={row['gap_log_interval']};"
            f"fourier={fourier_text};"
            f"ternary_counts={row['ternary_counts']};"
            f"ternary_corr={row['ternary_correlation']};"
            f"sqrtL_ternary_corr={row['scaled_ternary_correlation']}"
            f";residue_sha256={row['residue_sha256']}"
        )
    print(f"row_count={len(rows)}")
    print(f"exact_fraction_rows={2 * len(EXACT_AMBIENT_EXPONENTS)}")
    print(f"directed_shadow_rows={2 * len(SHADOW_AMBIENT_EXPONENTS)}")
    print(f"exact_record_sha256={record_digest}")
    print("asserts_asymptotic_gap_bound=false")
    print("asserts_fourier_decay=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
