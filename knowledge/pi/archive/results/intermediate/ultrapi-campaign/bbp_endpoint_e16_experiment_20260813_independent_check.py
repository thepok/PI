#!/usr/bin/env python3
"""Independent audit replay of the finite BBP endpoint e=16 experiment.

This file imports no definition from the primary experiment.  It uses a
higher MPFR precision, constructs all overlapping decimal windows by a
column-wise digit polynomial rather than a rolling recurrence, checks all
100,000 five-digit words directly in the certified pi prefix, and separately
reconstructs the translated gaps and exact BBP-tail transfer intervals.

Every computed conclusion has label ``experiment``.  No asymptotic statement,
fixed return, or V1 is asserted.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

import gmpy2
import numpy as np


ROOT = Path(__file__).resolve().parents[2]
WIDTH = 18
MODULUS = 10**WIDTH
EPOCH = 16
FOURIER_BLOCK = 777_777

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md":
        "f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80",
    "work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_audit.md":
        "6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9",
    "work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.py":
        "d9fc5d4f8bff417bb50812788c0f893a03d9c02c343b1a031f69b390a2320e13",
    "work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_record.txt":
        "2a9b25378bdf0a0a7a8d796c76c5e7058932876bb0a8004f21322d792edf982d",
    "work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.md":
        "b9dfc7682b525afae6d70379982f6503962dfce55389c4b0d2a8efb87505c9aa",
}

EXPECTED_JSON_SHA256 = (
    "421dae474d0735647e5a6d7b4358cc40416142c50d1763d385e9a56c593ceadf"
)
EXPECTED_GAP = 2_736_782_005_017
EXPECTED_TARGET = 62_123_460_130
EXPECTED_COUNT = 5_491_685
EXPECTED_FOURIER = {
    "pre-drop": (0.0001591580933441, 0.000165938039838824),
    "first-drop": (0.00015935600452984, 0.000165767821489929),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoints() -> tuple[tuple[str, int], ...]:
    a = (3**EPOCH - 1) // 8
    return (("pre-drop", 5 * a - 1), ("first-drop", 5 * a))


def exact_decimal_upper(depth: int) -> int:
    """Correct an mpz digit-count estimate by exact boundary inequalities."""
    power = gmpy2.mpz(1) << (4 * depth)
    result = int(gmpy2.num_digits(power, 10)) - 1
    boundary = gmpy2.mpz(10) ** result
    while boundary > power:
        boundary //= 10
        result -= 1
    while boundary * 10 <= power:
        boundary *= 10
        result += 1
    assert boundary <= power < 10 * boundary
    return result


def independent_directed_prefix(places: int) -> tuple[bytes, int, int]:
    """Certify floor(pi*10^places) at a precision distinct from the primary."""
    # 332193/100000 is a strict rational upper bound for log_2(10).
    precision = (places * 332_193 + 99_999) // 100_000 + 512
    scale = gmpy2.mpz(10) ** places
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
    text = str(lower).encode("ascii")
    assert len(text) == places + 1 and text[0] == ord("3")
    return text[1:], int(lower), precision


def certify_sixteen_prefix(pi_floor: int, places: int) -> int:
    divisor = 10 ** (places - WIDTH)
    low = (16 * pi_floor) // divisor
    high = (16 * (pi_floor + 1)) // divisor
    assert low == high
    return low % MODULUS


def direct_digit_polynomial(
    digits: np.ndarray, first: int, count: int
) -> np.ndarray:
    """Build each WIDTH-digit word from its digit columns, without rolling."""
    assert first >= 0 and first + count + WIDTH - 1 <= len(digits)
    values = np.zeros(count, dtype=np.uint64)
    for column in range(WIDTH):
        values *= np.uint64(10)
        values += digits[first + column:first + column + count]
    assert bool(np.all(values < np.uint64(MODULUS)))
    return values


def fixed_u64_digest(values: np.ndarray) -> str:
    little = values.astype("<u8", copy=False)
    return hashlib.sha256(little.tobytes()).hexdigest()


def direct_word_coverage(windows: np.ndarray) -> tuple[list[int], list[int]]:
    """Check all decimal cylinders of each length 1 through 5 directly."""
    distinct: list[int] = []
    minimum_multiplicity: list[int] = []
    for length in range(1, 6):
        words = windows // np.uint64(10 ** (WIDTH - length))
        counts = np.bincount(words.astype(np.int64), minlength=10**length)
        assert len(counts) == 10**length
        assert bool(np.all(counts > 0))
        distinct.append(int(np.count_nonzero(counts)))
        minimum_multiplicity.append(int(counts.min()))
    return distinct, minimum_multiplicity


def translated_residues(windows: np.ndarray, shift: int) -> np.ndarray:
    residues = windows.copy()
    upper = residues >= np.uint64(shift)
    residues[upper] -= np.uint64(shift)
    residues[~upper] += np.uint64(MODULUS - shift)
    return residues


def float_fourier_from_unshifted(windows: np.ndarray) -> tuple[float, float]:
    """Translation-invariant magnitude, evaluated on unshifted phases."""
    output: list[float] = []
    for frequency in (1, 2):
        real = 0.0
        imaginary = 0.0
        coefficient = 2.0 * math.pi * frequency / MODULUS
        for start in range(0, len(windows), FOURIER_BLOCK):
            chunk = windows[start:start + FOURIER_BLOCK].astype(np.float64)
            angles = coefficient * chunk
            real += float(np.cos(angles).sum(dtype=np.float64))
            imaginary += float(np.sin(angles).sum(dtype=np.float64))
        output.append(math.hypot(real, imaginary) / len(windows))
    return output[0], output[1]


def exact_gap_data(residues: np.ndarray) -> tuple[int, int, int, str]:
    residues.sort(kind="quicksort")
    differences = np.diff(residues)
    assert int(differences.min()) > 0
    internal_index = int(np.argmax(differences))
    internal_gap = int(differences[internal_index])
    wrap_gap = MODULUS + int(residues[0]) - int(residues[-1])
    if internal_gap >= wrap_gap:
        gap = internal_gap
        endpoints_text = f"{int(residues[internal_index])}:{int(residues[internal_index + 1])}"
    else:
        gap = wrap_gap
        endpoints_text = f"{int(residues[-1])}:{int(residues[0])}"
    target = min(int(residues[0]), MODULUS - int(residues[-1]))
    return gap, target, wrap_gap, endpoints_text


def parse_primary_record() -> list[dict[str, object]]:
    lines = (
        ROOT / "work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_record.txt"
    ).read_text().splitlines()
    rows = [json.loads(line.removeprefix("row=")) for line in lines if line.startswith("row=")]
    assert len(rows) == 2
    encoded = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("ascii")
    assert hashlib.sha256(encoded).hexdigest() == EXPECTED_JSON_SHA256
    assert f"exact_record_sha256={EXPECTED_JSON_SHA256}" in lines
    assert "claim_status=experiment" in lines
    assert "asserts_asymptotic_gap_bound=false" in lines
    assert "asserts_fourier_decay=false" in lines
    assert "asserts_fixed_return=false" in lines
    assert "asserts_v1=false" in lines
    assert lines[-1] == "status=PASS"
    return rows


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def interval_text(lower: Fraction, upper: Fraction) -> str:
    return f"[{fraction_text(lower)},{fraction_text(upper)}]"


def exact_transfer_replay(
    stage: str,
    depth: int,
    gap: int,
    target: int,
    primary: dict[str, object],
) -> dict[str, str]:
    gap_center = Fraction(gap, MODULUS)
    target_center = Fraction(target, MODULUS)
    eta = Fraction(1, MODULUS) + Fraction(1, 15 * (depth + 1) ** 2)
    gap_lower = max(Fraction(0), gap_center - 2 * eta)
    gap_upper = min(Fraction(1), gap_center + 2 * eta)
    target_lower = max(Fraction(0), target_center - eta)
    target_upper = min(Fraction(1, 2), target_center + eta)
    pi_gap_upper = gap_center + Fraction(2, MODULUS)

    assert primary["stage"] == stage
    assert primary["depth"] == depth
    assert primary["count"] == EXPECTED_COUNT
    assert primary["gap_center_exact"] == fraction_text(gap_center)
    assert primary["target_center_exact"] == fraction_text(target_center)
    assert primary["phase_error_upper_exact"] == fraction_text(eta)
    assert primary["gap_interval_exact"] == interval_text(gap_lower, gap_upper)
    assert primary["target_interval_exact"] == interval_text(target_lower, target_upper)
    assert primary["pi_orbit_gap_upper_exact"] == fraction_text(pi_gap_upper)
    assert pi_gap_upper < Fraction(1, 100_000)
    assert pi_gap_upper > Fraction(1, 1_000_000)
    assert primary["certifies_all_decimal_words_through_length"] == 5

    # Directed logarithms independently verify the wide normalized-gap range,
    # using the BBP transfer interval rather than the displayed float center.
    down = gmpy2.context(gmpy2.get_context(), precision=256, round=gmpy2.RoundDown)
    up = gmpy2.context(gmpy2.get_context(), precision=256, round=gmpy2.RoundUp)
    with down:
        log_lower = gmpy2.log(gmpy2.mpfr(EXPECTED_COUNT))
    with up:
        log_upper = gmpy2.log(gmpy2.mpfr(EXPECTED_COUNT))
    with down:
        normalized_lower = (
            gmpy2.mpfr(EXPECTED_COUNT)
            * gmpy2.mpfr(gap_lower.numerator)
            / gmpy2.mpfr(gap_lower.denominator)
            / log_upper
        )
    with up:
        normalized_upper = (
            gmpy2.mpfr(EXPECTED_COUNT)
            * gmpy2.mpfr(gap_upper.numerator)
            / gmpy2.mpfr(gap_upper.denominator)
            / log_lower
        )
    assert normalized_lower > gmpy2.mpq(899, 1000)
    assert normalized_upper < gmpy2.mpq(1084, 1000)

    return {
        "eta": fraction_text(eta),
        "gap_interval": interval_text(gap_lower, gap_upper),
        "pi_gap_upper": fraction_text(pi_gap_upper),
    }


def report_integrity() -> tuple[int, int]:
    report = ROOT / "work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.md"
    raw = report.read_bytes()
    controls = [byte for byte in raw if byte < 32 and byte not in (9, 10, 13)]
    assert not controls
    links = re.findall(r"\[[^\]]+\]\(([^)]+)\)", raw.decode("utf-8"))
    local_count = 0
    for link in links:
        target = link.strip("<>").split("#", 1)[0]
        if not target or "://" in target:
            continue
        assert (report.parent / target).resolve().is_file(), target
        local_count += 1
    assert local_count == 5
    return len(controls), local_count


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    for relative, expected in PINS.items():
        assert sha256(ROOT / relative) == expected, relative
    controls, link_checks = report_integrity()
    primary_rows = parse_primary_record()

    rows = [(stage, depth, exact_decimal_upper(depth)) for stage, depth in endpoints()]
    assert rows == [
        ("pre-drop", 26_904_199, 32_395_883),
        ("first-drop", 26_904_200, 32_395_884),
    ]
    assert all(upper - depth + 1 == EXPECTED_COUNT for _, depth, upper in rows)
    first = rows[0][1]
    last = rows[1][2]
    places = last + WIDTH + 5

    prefix, pi_floor, precision = independent_directed_prefix(places)
    assert len(prefix) == places
    prefix_sha = hashlib.sha256(prefix).hexdigest()
    digits = np.frombuffer(prefix, dtype=np.uint8) - np.uint8(ord("0"))
    assert int(digits.max()) <= 9
    sixteen = certify_sixteen_prefix(pi_floor, places)

    all_windows = direct_digit_polynomial(digits, first, last - first + 1)
    assert len(all_windows) == EXPECTED_COUNT + 1
    stream_sha = fixed_u64_digest(all_windows)

    output_rows: list[dict[str, object]] = []
    for index, (stage, depth, upper) in enumerate(rows):
        windows = all_windows[index:index + EXPECTED_COUNT]
        distinct, minimum_multiplicity = direct_word_coverage(windows)
        assert distinct == [10, 100, 1_000, 10_000, 100_000]
        residues = translated_residues(windows, sixteen)
        fourier = float_fourier_from_unshifted(windows)
        for actual, expected in zip(fourier, EXPECTED_FOURIER[stage], strict=True):
            assert abs(actual - expected) < 5e-15
        gap, target, wrap_gap, gap_endpoints = exact_gap_data(residues)
        assert gap == EXPECTED_GAP
        assert target == EXPECTED_TARGET
        transfer = exact_transfer_replay(
            stage, depth, gap, target, primary_rows[index]
        )
        output_rows.append(
            {
                "stage": stage,
                "depth": depth,
                "upper": upper,
                "count": len(windows),
                "window_sha256": fixed_u64_digest(windows),
                "sorted_residue_sha256": fixed_u64_digest(residues),
                "gap_numerator_over_1e18": gap,
                "gap_endpoints": gap_endpoints,
                "wrap_gap": wrap_gap,
                "target_numerator_over_1e18": target,
                "direct_word_distinct": distinct,
                "direct_word_minimum_multiplicity": minimum_multiplicity,
                "fourier_unshifted_float": [f"{value:.17g}" for value in fourier],
                **transfer,
            }
        )

    print("claim_status=experiment")
    print(f"frozen_hash_checks={len(PINS)}")
    print(f"c0_control_bytes={controls}")
    print(f"markdown_link_checks={link_checks}")
    print(f"gmpy2_version={gmpy2.version()}")
    print(f"mpfr_version={gmpy2.mpfr_version()}")
    print(f"numpy_version={np.__version__}")
    print(f"independent_mpfr_precision_bits={precision}")
    print(f"certified_pi_decimal_places={places}")
    print(f"certified_pi_fractional_prefix_sha256={prefix_sha}")
    print(f"sixteen_pi_18_digit_prefix={sixteen:018d}")
    print(f"combined_window_stream_sha256={stream_sha}")
    for row in output_rows:
        print("row=" + json.dumps(row, sort_keys=True, separators=(",", ":")))
    print("directly_checks_all_words_length_1_through_5=true")
    print("asserts_words_length_6=false")
    print("asserts_asymptotic_gap_bound=false")
    print("asserts_fourier_decay=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
