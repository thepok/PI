#!/usr/bin/env python3
"""Boundary-safe finite census of T56's raw short-lag pi near returns.

All mathematical classifications use integers. Floating point is used only
for elapsed-time reporting. The Chudnovsky identity is evaluated with two
consecutive exact partial sums; the alternating-series bracket and directed
integer square-root bounds produce a rational interval containing pi.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import resource
import sys
import time
from pathlib import Path
from typing import Any


sys.set_int_max_str_digits(0)

ITEM = "T62"
LABEL = "experiment"
CANONICAL_FILE = "pi-positive-decimal-factor-entropy.txt"
CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
MANDATORY_MIN_N = 2
MANDATORY_MAX_N = 12
DEFAULT_GUARD_DIGITS = 16

A = 13_591_409
B = 545_140_134
C = 640_320
C3_OVER_24 = C**3 // 24
SQRT_RADICAND = 10_005
PI_FACTOR = 426_880


class TimeCapExceeded(RuntimeError):
    pass


def check_deadline(deadline: float | None, stage: str) -> None:
    if deadline is not None and time.perf_counter() >= deadline:
        raise TimeCapExceeded(stage)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def integer_sha256(value: int) -> str:
    """Hash an integer without the prohibitively slow million-digit base-10 conversion."""
    sign = b"\x01" if value < 0 else b"\x00"
    magnitude = abs(value)
    payload = magnitude.to_bytes(max(1, (magnitude.bit_length() + 7) // 8), "big")
    return sha256_bytes(sign + payload)


def rational_text(numerator: int, denominator: int) -> str:
    divisor = math.gcd(numerator, denominator)
    return f"{numerator // divisor}/{denominator // divisor}"


def verify_canonical_statement(directory: Path) -> str:
    digest = sha256_bytes((directory / CANONICAL_FILE).read_bytes())
    if digest != CANONICAL_SHA256:
        raise RuntimeError(
            f"canonical statement hash mismatch: expected {CANONICAL_SHA256}, got {digest}"
        )
    return digest


def chudnovsky_leaf(k: int) -> tuple[int, int, int]:
    if k == 0:
        return 1, 1, A
    p = (6 * k - 5) * (2 * k - 1) * (6 * k - 1)
    q = k**3 * C3_OVER_24
    t = p * (A + B * k)
    if k % 2:
        t = -t
    return p, q, t


def chudnovsky_split(
    start: int, stop: int, deadline: float | None = None
) -> tuple[int, int, int]:
    """Return binary-splitting P,Q,T for the half-open term range."""
    if stop - start >= 256:
        check_deadline(deadline, "pi_binary_split")
    if stop - start == 1:
        return chudnovsky_leaf(start)
    middle = (start + stop) // 2
    p_left, q_left, t_left = chudnovsky_split(start, middle, deadline)
    check_deadline(deadline, "pi_binary_split")
    p_right, q_right, t_right = chudnovsky_split(middle, stop, deadline)
    check_deadline(deadline, "pi_binary_split_merge")
    return (
        p_left * p_right,
        q_left * q_right,
        t_left * q_right + p_left * t_right,
    )


def merge_split(
    left: tuple[int, int, int], right: tuple[int, int, int]
) -> tuple[int, int, int]:
    p_left, q_left, t_left = left
    p_right, q_right, t_right = right
    return (
        p_left * p_right,
        q_left * q_right,
        t_left * q_right + p_left * t_right,
    )


def certify_pi(
    decimal_places: int, deadline: float | None = None
) -> tuple[str, dict[str, Any]]:
    """Certify floor(pi*10^decimal_places) and return its decimal expansion."""
    if decimal_places < 1:
        raise ValueError("decimal_places must be positive")

    # Chudnovsky contributes about 14.18 decimal digits per term. Correctness
    # does not rely on that estimate: equal directed endpoint floors below are
    # the acceptance test, and failure causes a larger exact recomputation.
    terms = decimal_places // 14 + 12
    attempts = 0
    while True:
        attempts += 1
        check_deadline(deadline, "pi_certificate_start")
        partial_n = chudnovsky_split(0, terms, deadline)
        partial_n1 = merge_split(partial_n, chudnovsky_leaf(terms))
        _p_n, q_n, t_n = partial_n
        _p_n1, q_n1, t_n1 = partial_n1
        if t_n <= 0 or t_n1 <= 0:
            raise RuntimeError("unexpected nonpositive Chudnovsky partial sum")

        # Consecutive alternating partial sums bracket the positive full sum.
        if t_n * q_n1 < t_n1 * q_n:
            sum_low_num, sum_low_den = t_n, q_n
            sum_high_num, sum_high_den = t_n1, q_n1
        else:
            sum_low_num, sum_low_den = t_n1, q_n1
            sum_high_num, sum_high_den = t_n, q_n

        sqrt_extra = 32
        check_deadline(deadline, "pi_square_root")
        sqrt_scale = 10 ** (decimal_places + sqrt_extra)
        sqrt_floor = math.isqrt(SQRT_RADICAND * sqrt_scale * sqrt_scale)
        if not (
            sqrt_floor * sqrt_floor
            < SQRT_RADICAND * sqrt_scale * sqrt_scale
            < (sqrt_floor + 1) * (sqrt_floor + 1)
        ):
            raise RuntimeError("directed square-root bounds failed")

        # sum_low < S < sum_high and sqrt_low < sqrt(10005) < sqrt_high.
        # Division reverses the choice of sum endpoint.
        lower_num = PI_FACTOR * sqrt_floor * sum_high_den
        lower_den = sqrt_scale * sum_high_num
        upper_num = PI_FACTOR * (sqrt_floor + 1) * sum_low_den
        upper_den = sqrt_scale * sum_low_num
        if lower_num * upper_den >= upper_num * lower_den:
            raise RuntimeError("pi interval endpoints are not ordered")

        decimal_scale = 10**decimal_places
        check_deadline(deadline, "pi_endpoint_floor")
        floor_from_lower = lower_num * decimal_scale // lower_den
        # The upper endpoint is strict, so ceil(U)-1 is the largest floor.
        floor_from_upper = (upper_num * decimal_scale - 1) // upper_den
        if floor_from_lower == floor_from_upper:
            scaled_floor = floor_from_lower
            break
        terms += 1024
        if attempts >= 4:
            raise RuntimeError("failed to isolate the requested decimal prefix")

    scaled_text = str(scaled_floor)
    check_deadline(deadline, "pi_decimal_conversion")
    if len(scaled_text) != decimal_places + 1 or not scaled_text.startswith("3"):
        raise RuntimeError("certified scaled pi has an unexpected decimal shape")
    decimal_digits = scaled_text[1:]
    certificate = {
        "method": "Chudnovsky consecutive-partial-sum bracket with directed integer sqrt",
        "analytic_identity": "pi = 426880*sqrt(10005)/sum_k((-1)^k*c_k*(13591409+545140134*k))",
        "alternating_bound": {
            "term_ratio_upper": f"72576/{C**3}",
            "term_ratio_strictly_below_one": 72_576 < C**3,
            "partial_sum_indices": [terms, terms + 1],
        },
        "decimal_places": decimal_places,
        "series_terms": terms,
        "attempts": attempts,
        "sqrt_scale_decimal_places": decimal_places + sqrt_extra,
        "scaled_floor": scaled_text,
        "scaled_floor_sha256": sha256_bytes(scaled_text.encode("ascii")),
        "decimal_digits_sha256": sha256_bytes(decimal_digits.encode("ascii")),
        "decimal_prefix_64": decimal_digits[:64],
        "decimal_suffix_64": decimal_digits[-64:],
        "certified_interval": {
            "form": "scaled_floor/10^decimal_places <= pi < (scaled_floor+1)/10^decimal_places",
            "lower_scaled_integer": scaled_text,
            "upper_scaled_integer_offset": 1,
            "scale": f"10^{decimal_places}",
        },
        "exact_endpoint_hashes": {
            "encoding": "SHA-256 of one sign byte (00 nonnegative, 01 negative) followed by minimal big-endian magnitude",
            "chudnovsky_sum_lower_numerator": integer_sha256(sum_low_num),
            "chudnovsky_sum_lower_denominator": integer_sha256(sum_low_den),
            "chudnovsky_sum_upper_numerator": integer_sha256(sum_high_num),
            "chudnovsky_sum_upper_denominator": integer_sha256(sum_high_den),
            "pi_lower_numerator": integer_sha256(lower_num),
            "pi_lower_denominator": integer_sha256(lower_den),
            "pi_upper_numerator": integer_sha256(upper_num),
            "pi_upper_denominator": integer_sha256(upper_den),
        },
    }
    return decimal_digits, certificate


def decimal_windows(
    digits: str, width: int, count: int, deadline: float | None = None
) -> list[int]:
    """Return exact width-digit prefixes of frac(10^j*pi), 0 <= j < count."""
    if width < 1 or count < 1 or len(digits) < count + width - 1:
        raise ValueError("insufficient certified digits for requested windows")
    power = 10 ** (width - 1)
    current = int(digits[:width])
    windows = [current]
    for j in range(1, count):
        if j % 65_536 == 0:
            check_deadline(deadline, "decimal_windows")
        current = (current % power) * 10 + (ord(digits[j + width - 1]) - 48)
        windows.append(current)
    return windows


def classify_prefix_difference(
    left: int, right: int, width: int, n: int
) -> dict[str, Any]:
    """Classify circle distance using conservative closed prefix intervals."""
    base = 10**width
    cutoff = 10 ** (width - n)
    delta = right - left
    candidates = ((abs(delta + base), -1), (abs(delta), 0), (abs(delta - base), 1))
    center_distance, nearest_integer = min(candidates)
    distance_lower = max(0, center_distance - 1)
    distance_upper = center_distance + 1
    if distance_upper < cutoff:
        classification = "hit"
        boundary_margin = cutoff - distance_upper
    elif distance_lower >= cutoff:
        classification = "miss"
        boundary_margin = distance_lower - cutoff
    else:
        classification = "unresolved"
        boundary_margin = 0
    return {
        "classification": classification,
        "nearest_integer": nearest_integer,
        "prefix_delta": delta,
        "distance_lower_numerator": distance_lower,
        "distance_upper_numerator": distance_upper,
        "common_denominator": base,
        "strict_cutoff_numerator": cutoff,
        "boundary_margin_numerator": boundary_margin,
    }


def audit_scale(
    n: int, digits: str, guard_digits: int, deadline: float | None = None
) -> dict[str, Any]:
    length = 10 ** (n // 2)
    lags = list(range(1, min(n, length)))
    width = n + guard_digits
    windows = decimal_windows(digits, width, length, deadline)
    lag_rows: list[dict[str, Any]] = []
    all_hits: list[dict[str, Any]] = []
    total_unoriented = 0
    unresolved = 0

    for lag in lags:
        hit_count = 0
        nearest: tuple[int, int, dict[str, Any]] | None = None
        for j in range(length - lag):
            if j % 65_536 == 0:
                check_deadline(deadline, f"census_n_{n}_lag_{lag}")
            result = classify_prefix_difference(windows[j], windows[j + lag], width, n)
            if result["classification"] == "hit":
                hit_count += 1
                all_hits.append({"n": n, "lag": lag, "j": j, **result})
            elif result["classification"] == "unresolved":
                unresolved += 1
            margin = int(result["boundary_margin_numerator"])
            candidate = (margin, j, result)
            if nearest is None or candidate[:2] < nearest[:2]:
                nearest = candidate

        if nearest is None:
            raise RuntimeError("empty lag range")
        total_unoriented += hit_count
        _margin, nearest_j, nearest_result = nearest
        capacity = length - lag
        lag_rows.append(
            {
                "lag": lag,
                "start_range": f"0 <= j < {capacity}",
                "capacity": capacity,
                "unoriented_hits": hit_count,
                "ordered_hits": 2 * hit_count,
                "hit_fraction": rational_text(hit_count, capacity),
                "closest_boundary_witness": {
                    "j": nearest_j,
                    **nearest_result,
                },
            }
        )

    ordered_short_count = 2 * total_unoriented
    diagonal_plus_short = length + ordered_short_count
    return {
        "n": n,
        "L_n": length,
        "sample_length_definition": "10^(n//2)",
        "lag_range": f"1 <= r < {min(n, length)}",
        "strict_cutoff": f"circleDistance(10^j*(10^r-1)*pi) < 10^-{n}",
        "prefix_width": width,
        "per_lag": lag_rows,
        "totals": {
            "unoriented_short_hits": total_unoriented,
            "ordered_short_count": ordered_short_count,
            "ordered_short_over_L_n": rational_text(ordered_short_count, length),
            "diagonal_plus_short": diagonal_plus_short,
            "diagonal_plus_short_over_L_n": rational_text(diagonal_plus_short, length),
            "note": "diagonal_plus_short excludes every lag r>=n and is not the full Q_pi",
        },
        "hit_witnesses": all_hits,
        "unresolved_boundary_cases": unresolved,
    }


def deterministic_projection(result: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in result.items()
        if key not in {"performance_observed", "replay_verification"}
    }


def candidate_count(n: int) -> int:
    length = 10 ** (n // 2)
    return sum(length - lag for lag in range(1, min(n, length)))


def build_result(args: argparse.Namespace, directory: Path) -> dict[str, Any]:
    started = time.perf_counter()
    statement_digest = verify_canonical_statement(directory)

    optional_plan: list[dict[str, Any]] = []
    if args.optional_max_n is not None:
        if args.optional_max_n <= MANDATORY_MAX_N:
            raise ValueError("--optional-max-n must exceed 12")
        if args.max_length is None or args.max_candidates is None or args.max_seconds is None:
            raise ValueError(
                "optional scales require --max-length, --max-candidates, and --max-seconds"
            )
        if args.max_length <= 0 or args.max_candidates <= 0:
            raise ValueError("optional length and candidate caps must be positive")
        if not math.isfinite(args.max_seconds) or args.max_seconds <= 0:
            raise ValueError("optional time cap must be finite and positive")
    max_length = 10 ** (MANDATORY_MAX_N // 2)
    max_width = MANDATORY_MAX_N + args.guard_digits
    decimal_places = max_length + max_width - 1
    digits, pi_certificate = certify_pi(decimal_places)

    mandatory_tables = [
        audit_scale(n, digits, args.guard_digits)
        for n in range(MANDATORY_MIN_N, MANDATORY_MAX_N + 1)
    ]
    optional_tables: list[dict[str, Any]] = []
    if args.optional_max_n is not None:
        optional_started = time.perf_counter()
        optional_deadline = optional_started + args.max_seconds
        for n in range(MANDATORY_MAX_N + 1, args.optional_max_n + 1):
            length = 10 ** (n // 2)
            candidates = candidate_count(n)
            if length > args.max_length:
                optional_plan.append(
                    {"n": n, "status": "capped", "reason": "max_length", "L_n": length}
                )
                break
            if candidates > args.max_candidates:
                optional_plan.append(
                    {
                        "n": n,
                        "status": "capped",
                        "reason": "max_candidates",
                        "candidate_count": candidates,
                    }
                )
                break
            try:
                check_deadline(optional_deadline, "before_optional_scale")
                optional_places = length + n + args.guard_digits - 1
                optional_digits, optional_certificate = certify_pi(
                    optional_places, optional_deadline
                )
                table = audit_scale(
                    n, optional_digits, args.guard_digits, optional_deadline
                )
            except TimeCapExceeded as error:
                optional_plan.append(
                    {
                        "n": n,
                        "status": "capped",
                        "reason": "max_seconds",
                        "stage": str(error),
                        "optional_elapsed_seconds": round(
                            time.perf_counter() - optional_started, 6
                        ),
                    }
                )
                break
            if table["unresolved_boundary_cases"]:
                optional_plan.append(
                    {
                        "n": n,
                        "status": "capped",
                        "reason": "unresolved_boundary_cases",
                        "count": table["unresolved_boundary_cases"],
                    }
                )
                break
            table["pi_certificate"] = optional_certificate
            optional_tables.append(table)
            optional_plan.append(
                {
                    "n": n,
                    "status": "completed",
                    "L_n": length,
                    "candidate_count": candidates,
                    "optional_elapsed_seconds": round(
                        time.perf_counter() - optional_started, 6
                    ),
                }
            )

    unresolved = sum(row["unresolved_boundary_cases"] for row in mandatory_tables)
    if len(mandatory_tables) != MANDATORY_MAX_N - MANDATORY_MIN_N + 1:
        raise RuntimeError("mandatory baseline is incomplete")
    if unresolved:
        raise RuntimeError(f"mandatory baseline has {unresolved} unresolved boundary cases")

    elapsed = time.perf_counter() - started
    max_rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return {
        "item": ITEM,
        "label": LABEL,
        "canonical_statement": {
            "file": CANONICAL_FILE,
            "sha256": statement_digest,
            "source_url": None,
            "provenance": "local canonical statement formulated by this system on 2026-07-22",
        },
        "definitions": {
            "L_n": "10^(n//2), with natural-number division",
            "raw_short_lags": "1 <= r < n and r < L_n",
            "starts": "0 <= j < L_n-r",
            "near_return": "circleDistance(10^j*(10^r-1)*pi) < 10^-n",
            "orientation": "per-lag hits use the smaller index j; ordered count is twice their sum",
            "scope_distinction": "raw short-lag count, not T56 shortResidualPairCount(mu,c,Q0,...) because no arithmetic parameters were specified",
        },
        "pi_certificate": pi_certificate,
        "mandatory_baseline": {
            "n_range": [MANDATORY_MIN_N, MANDATORY_MAX_N],
            "guard_digits": args.guard_digits,
            "tables": mandatory_tables,
            "unresolved_boundary_cases": unresolved,
            "complete": True,
        },
        "optional_larger_scales": {
            "enabled": args.optional_max_n is not None,
            "declared_caps": {
                "optional_max_n": args.optional_max_n,
                "max_length": args.max_length,
                "max_candidates": args.max_candidates,
                "max_seconds": args.max_seconds,
            },
            "plan_and_frontier": optional_plan,
            "tables": optional_tables,
        },
        "scope": {
            "finite_heuristic_evidence_only": True,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
            "proves_positive_decimal_factor_entropy": False,
        },
        "performance_observed": {
            "elapsed_seconds": round(elapsed, 6),
            "peak_rss_kib": max_rss_kib,
            "python": platform.python_version(),
            "platform": platform.platform(),
        },
    }


def verify_expected(result: dict[str, Any], expected_path: Path) -> None:
    expected = json.loads(expected_path.read_text(encoding="ascii"))
    if deterministic_projection(result) != deterministic_projection(expected):
        raise RuntimeError("deterministic replay differs from expected census")

    witnesses_checked = 0
    certified_digits = result["pi_certificate"]["scaled_floor"][1:]
    for table in result["mandatory_baseline"]["tables"]:
        n = table["n"]
        width = table["prefix_width"]
        for lag_row in table["per_lag"]:
            witness = lag_row["closest_boundary_witness"]
            j = witness["j"]
            lag = lag_row["lag"]
            left = int(certified_digits[j : j + width])
            right = int(certified_digits[j + lag : j + lag + width])
            check = classify_prefix_difference(
                left,
                right,
                width,
                n,
            )
            for key in (
                "classification",
                "nearest_integer",
                "prefix_delta",
                "distance_lower_numerator",
                "distance_upper_numerator",
                "common_denominator",
                "strict_cutoff_numerator",
                "boundary_margin_numerator",
            ):
                if check[key] != witness[key]:
                    raise RuntimeError(f"closest witness check failed at n={n}, r={lag_row['lag']}")
            witnesses_checked += 1
        for witness in table["hit_witnesses"]:
            j = witness["j"]
            lag = witness["lag"]
            left = int(certified_digits[j : j + width])
            right = int(certified_digits[j + lag : j + lag + width])
            check = classify_prefix_difference(left, right, width, n)
            if check["classification"] != "hit":
                raise RuntimeError(f"hit witness check failed at n={n}")
            witnesses_checked += 1
    result["replay_verification"] = {
        "expected_deterministic_projection_matches": True,
        "witnesses_checked": witnesses_checked,
        "unresolved_boundary_cases": result["mandatory_baseline"][
            "unresolved_boundary_cases"
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--guard-digits", type=int, default=DEFAULT_GUARD_DIGITS)
    parser.add_argument("--optional-max-n", type=int)
    parser.add_argument("--max-length", type=int)
    parser.add_argument("--max-candidates", type=int)
    parser.add_argument("--max-seconds", type=float)
    args = parser.parse_args()
    if args.guard_digits < 4:
        parser.error("--guard-digits must be at least 4")
    return args


def main() -> None:
    args = parse_args()
    directory = Path(__file__).resolve().parent
    result = build_result(args, directory)
    if args.verify:
        verify_expected(result, args.verify)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="ascii")
    if args.quiet:
        verification = result.get("replay_verification", {})
        print(
            "T62 census: PASS; "
            f"n=2..12; unresolved={result['mandatory_baseline']['unresolved_boundary_cases']}; "
            f"witnesses_checked={verification.get('witnesses_checked', 'not-requested')}; "
            f"elapsed_seconds={result['performance_observed']['elapsed_seconds']}; "
            f"peak_rss_kib={result['performance_observed']['peak_rss_kib']}"
        )
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
