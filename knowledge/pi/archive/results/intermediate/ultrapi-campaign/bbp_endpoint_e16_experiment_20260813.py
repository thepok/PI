#!/usr/bin/env python3
"""Directed finite full-phase gap experiment at the BBP endpoint epoch e=16.

Every conclusion emitted by this script has claim label ``experiment``.
It certifies a sufficiently long decimal prefix of pi by directed MPFR
rounding, forms the complete pi-centered shadows of the pre-drop and first-
drop endpoint rows, and transfers their target distances and largest gaps to
the corresponding rational BBP rows with the positive tail bound.  It proves
no asymptotic gap law, fixed return, or V1.
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2
import numpy as np


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
FULL_PHASE_REPORT_SHA256 = (
    "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80"
)
FULL_PHASE_AUDIT_SHA256 = (
    "6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9"
)

AMBIENT_EXPONENT = 16
DECIMAL_WIDTH = 18
FOURIER_CHUNK = 1_000_000


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoint_depths() -> tuple[tuple[str, int], ...]:
    a_value = (3**AMBIENT_EXPONENT - 1) // 8
    return (("pre-drop", 5 * a_value - 1), ("first-drop", 5 * a_value))


def exact_upper(depth: int) -> int:
    """Certify floor(log_10(16**depth)) by directed MPFR rounding."""
    down = gmpy2.context(
        gmpy2.get_context(), precision=256, round=gmpy2.RoundDown
    )
    up = gmpy2.context(
        gmpy2.get_context(), precision=256, round=gmpy2.RoundUp
    )
    with down:
        lower = gmpy2.floor(4 * depth * gmpy2.log10(gmpy2.mpfr(2)))
    with up:
        upper = gmpy2.floor(4 * depth * gmpy2.log10(gmpy2.mpfr(2)))
    if lower != upper:
        raise AssertionError(("uncertified decimal upper", depth, lower, upper))
    result = int(lower)
    # Exact integer inequalities make the MPFR certification independently
    # checkable at the boundary.
    power16 = gmpy2.mpz(1) << (4 * depth)
    if not gmpy2.mpz(10) ** result <= power16 < gmpy2.mpz(10) ** (result + 1):
        raise AssertionError(("decimal upper boundary", depth, result))
    return result


def directed_pi_prefix(decimal_places: int) -> tuple[bytes, gmpy2.mpz]:
    """Return certified fractional digits and floor(pi*10**decimal_places)."""
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
    if lower != upper:
        raise AssertionError("directed MPFR endpoints do not certify pi prefix")
    text = str(lower).encode("ascii")
    if len(text) != decimal_places + 1 or text[:1] != b"3":
        raise AssertionError("unexpected certified pi prefix")
    return text[1:], gmpy2.mpz(lower)


def sixteen_pi_prefix(scaled_pi: gmpy2.mpz, places: int) -> int:
    divisor = gmpy2.mpz(10) ** (places - DECIMAL_WIDTH)
    lower = (16 * scaled_pi) // divisor
    upper = (16 * (scaled_pi + 1)) // divisor
    if lower != upper:
        raise AssertionError("16*pi prefix is not certified")
    return int(lower % (10**DECIMAL_WIDTH))


def decimal_windows(digits: np.ndarray, start: int, stop: int) -> np.ndarray:
    """Return exact DECIMAL_WIDTH-digit windows for exponents start..stop."""
    count = stop - start + 1
    modulus = 10**DECIMAL_WIDTH
    drop_scale = 10 ** (DECIMAL_WIDTH - 1)
    value = 0
    for digit in digits[start : start + DECIMAL_WIDTH]:
        value = 10 * value + int(digit)
    result = np.empty(count, dtype=np.uint64)
    result[0] = value
    for offset in range(1, count):
        value = (
            (value % drop_scale) * 10
            + int(digits[start + DECIMAL_WIDTH + offset - 1])
        )
        result[offset] = value
    if int(result[-1]) >= modulus:
        raise AssertionError("window outside decimal modulus")
    return result


def fourier_float_diagnostics(
    residues: np.ndarray, modulus: int
) -> dict[str, str]:
    """Return explicitly non-rigorous float diagnostics, not enclosures."""
    answer: dict[str, str] = {}
    for frequency in (1, 2):
        real_total = 0.0
        imag_total = 0.0
        for start in range(0, len(residues), FOURIER_CHUNK):
            chunk = residues[start : start + FOURIER_CHUNK].astype(np.float64)
            angles = (2.0 * math.pi * frequency / modulus) * chunk
            real_total += float(np.cos(angles).sum(dtype=np.float64))
            imag_total += float(np.sin(angles).sum(dtype=np.float64))
        magnitude = math.hypot(real_total, imag_total) / len(residues)
        answer[str(frequency)] = f"{magnitude:.15g}"
    return answer


def analyze_row(
    stage: str,
    depth: int,
    upper: int,
    digits: np.ndarray,
    sixteen_prefix: int,
) -> dict[str, object]:
    modulus = 10**DECIMAL_WIDTH
    orbit_windows = decimal_windows(digits, depth, upper)
    residues = np.where(
        orbit_windows >= sixteen_prefix,
        orbit_windows - sixteen_prefix,
        orbit_windows + np.uint64(modulus - sixteen_prefix),
    ).astype(np.uint64, copy=False)
    if len(np.unique(residues)) != len(residues):
        raise AssertionError(("truncated phase collision", stage))
    fourier = fourier_float_diagnostics(residues, modulus)
    residues.sort()
    differences = np.diff(residues)
    internal_gap = int(differences.max(initial=np.uint64(0)))
    wrap_gap = modulus + int(residues[0]) - int(residues[-1])
    largest_gap = max(internal_gap, wrap_gap)
    target_distance = min(int(residues[0]), modulus - int(residues[-1]))
    count = len(residues)
    eta = Fraction(1, modulus) + Fraction(1, 15 * (depth + 1) ** 2)
    gap_center = Fraction(largest_gap, modulus)
    target_center = Fraction(target_distance, modulus)
    gap_lower = max(Fraction(), gap_center - 2 * eta)
    gap_upper = min(Fraction(1), gap_center + 2 * eta)
    target_lower = max(Fraction(), target_center - eta)
    target_upper = min(Fraction(1, 2), target_center + eta)
    # Each truncated pi-centered phase is within 1/modulus of the true phase:
    # both floor(10^n*pi) and floor(16*pi) contribute one-sided truncations,
    # whose difference has absolute error strictly below 1/modulus.  Hence the
    # true pi-orbit largest gap is strictly below this exact bound.  Translation
    # by 16*pi preserves gaps, so a bound below 10^(-p) certifies every p-digit
    # decimal cylinder in this finite exponent window.
    pi_orbit_gap_upper = gap_center + Fraction(2, modulus)
    certified_word_length = 0
    while pi_orbit_gap_upper < Fraction(
        1, 10 ** (certified_word_length + 1)
    ):
        certified_word_length += 1
    record = {
        "ambient": AMBIENT_EXPONENT,
        "stage": stage,
        "depth": depth,
        "upper": upper,
        "count": count,
        "decimal_width": DECIMAL_WIDTH,
        "phase_error_upper_exact": f"{eta.numerator}/{eta.denominator}",
        "target_center_exact": (
            f"{target_center.numerator}/{target_center.denominator}"
        ),
        "target_interval_exact": (
            f"[{target_lower.numerator}/{target_lower.denominator},"
            f"{target_upper.numerator}/{target_upper.denominator}]"
        ),
        "gap_center_exact": f"{gap_center.numerator}/{gap_center.denominator}",
        "gap_interval_exact": (
            f"[{gap_lower.numerator}/{gap_lower.denominator},"
            f"{gap_upper.numerator}/{gap_upper.denominator}]"
        ),
        "pi_orbit_gap_upper_exact": (
            f"{pi_orbit_gap_upper.numerator}/{pi_orbit_gap_upper.denominator}"
        ),
        "certifies_all_decimal_words_through_length": certified_word_length,
        "gap_center_decimal": f"{float(gap_center):.18e}",
        "scaled_gap_float_diagnostic": (
            f"{count * float(gap_center) / math.log(count):.15g}"
        ),
        "fourier_float_diagnostic": fourier,
    }
    return record


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    root = Path(__file__).resolve().parents[2]
    pins = {
        root / "problems/local/pi-digits.txt": SOURCE_SHA256,
        root
        / "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md": (
            FULL_PHASE_REPORT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_audit.md": (
            FULL_PHASE_AUDIT_SHA256
        ),
    }
    for path, expected in pins.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(("frozen input", path, expected, actual))

    rows = [(stage, depth, exact_upper(depth)) for stage, depth in endpoint_depths()]
    maximum_upper = max(upper for _, _, upper in rows)
    places = maximum_upper + DECIMAL_WIDTH + 5
    pi_digits, scaled_pi = directed_pi_prefix(places)
    digits = np.frombuffer(pi_digits, dtype=np.uint8) - ord("0")
    if int(digits.max()) > 9:
        raise AssertionError("nondecimal pi prefix")
    sixteen_prefix = sixteen_pi_prefix(scaled_pi, places)
    records = [
        analyze_row(stage, depth, upper, digits, sixteen_prefix)
        for stage, depth, upper in rows
    ]
    record_bytes = json.dumps(
        records, sort_keys=True, separators=(",", ":")
    ).encode("ascii")
    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"gmpy2_version={gmpy2.version()}")
    print(f"mpfr_version={gmpy2.mpfr_version()}")
    print(f"numpy_version={np.__version__}")
    print(f"certified_pi_decimal_places={places}")
    for record in records:
        print("row=" + json.dumps(record, sort_keys=True, separators=(",", ":")))
    print(f"exact_record_sha256={hashlib.sha256(record_bytes).hexdigest()}")
    print("asserts_asymptotic_gap_bound=false")
    print("asserts_fourier_decay=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
