#!/usr/bin/env python3
"""Reproducible bounded fixed-pi near-return experiment."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

import mpmath


STATEMENT_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
MPMATH_VERSION = "1.3.0"
N_VALUES = tuple(range(3, 9))
CAPITAL_N_VALUES = (1000, 2000, 4000, 8000, 16000, 32000)
DIRECT_N_VALUES = tuple(range(1, 7))
DIRECT_CAPITAL_N_VALUES = (8, 16, 32, 64, 128)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_hash(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def ratio_record(numerator: int, denominator: int) -> dict[str, Any]:
    value = Fraction(numerator, denominator)
    with localcontext() as context:
        context.prec = 16
        rendered = Decimal(value.numerator) / Decimal(value.denominator)
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal_16_sig": format(rendered, ".15g"),
    }


def pi_digits(count: int, guard_digits: int) -> tuple[str, int]:
    dps = count + guard_digits
    with mpmath.workdps(dps):
        scaled = mpmath.floor((mpmath.pi - 3) * mpmath.mpf(10) ** count)
        digits = str(int(scaled)).zfill(count)
    if len(digits) != count or not digits.isdigit():
        raise RuntimeError("failed to generate the requested pi prefix")
    return digits, dps


def orbit_values(digits: str, count: int, tail_digits: int) -> list[int]:
    required = count - 1 + tail_digits
    if len(digits) < required:
        raise ValueError("pi prefix is too short")
    return [int(digits[index : index + tail_digits]) for index in range(count)]


def fast_pairs(
    values: list[int], n: int, tail_digits: int
) -> tuple[int, Counter[int], int]:
    """Sort and circularly scan in O(N log N + K) time."""
    capital_n = len(values)
    scale = 10**tail_digits
    radius = 10 ** (tail_digits - n)
    ordered = sorted((value, index) for index, value in enumerate(values))
    extended = ordered + [(value + scale, index) for value, index in ordered]
    lag_counts: Counter[int] = Counter()
    minimum_margin = scale
    for left in range(capital_n):
        right = left + 1
        while right < left + capital_n:
            delta = extended[right][0] - extended[left][0]
            minimum_margin = min(minimum_margin, abs(delta - radius))
            if delta >= radius:
                break
            lag_counts[abs(extended[right][1] - extended[left][1])] += 1
            right += 1
    return capital_n + 2 * sum(lag_counts.values()), lag_counts, minimum_margin


def cylinder_energy(
    values: list[int], n: int, tail_digits: int
) -> tuple[int, int]:
    width = 10 ** (tail_digits - n)
    fibers: Counter[int] = Counter()
    minimum_margin = width
    for value in values:
        code, remainder = divmod(value, width)
        fibers[code] += 1
        minimum_margin = min(minimum_margin, remainder, width - remainder)
    return sum(size * size for size in fibers.values()), minimum_margin


def direct_statistics(
    values: list[int], n: int, tail_digits: int
) -> tuple[int, Counter[int], int, int, int]:
    """Independent O(N^2) reference implementation."""
    capital_n = len(values)
    scale = 10**tail_digits
    radius = 10 ** (tail_digits - n)
    codes: list[int] = []
    lag_counts: Counter[int] = Counter()
    energy = capital_n
    pair_margin = scale
    boundary_margin = radius
    for value in values:
        code, remainder = divmod(value, radius)
        codes.append(code)
        boundary_margin = min(boundary_margin, remainder, radius - remainder)
    for left in range(capital_n):
        for right in range(left + 1, capital_n):
            difference = abs(values[left] - values[right])
            distance = min(difference, scale - difference)
            pair_margin = min(pair_margin, abs(distance - radius))
            if distance < radius:
                lag_counts[right - left] += 1
            if codes[left] == codes[right]:
                energy += 2
    return capital_n + 2 * sum(lag_counts.values()), lag_counts, energy, pair_margin, boundary_margin


def minimum(records: list[dict[str, Any]], key: str) -> dict[str, Any]:
    eligible = [record for record in records if record[key] is not None]
    if not eligible:
        return {"available": False}
    record = min(
        eligible,
        key=lambda row: (Fraction(*row[key]), row["N"]),
    )
    result = {"available": True, "N": record["N"], **ratio_record(*record[key])}
    if key == "q_ratio":
        result["Q_pi"] = record["Q_pi"]
    elif key == "energy_ratio":
        result["cylinder_energy"] = record["cylinder_energy"]
    elif key == "top1_ratio":
        result.update(
            unordered_non_diagonal_pairs=record["unordered_pairs"],
            maximizing_lags=record["maximizing_lags"],
            max_lag_count=record[key][0],
        )
    else:
        result.update(
            unordered_non_diagonal_pairs=record["unordered_pairs"],
            top_lags=record["top_lags"],
            top10_lag_count=record[key][0],
        )
    return result


def evaluate(tail_digits: int, guard_digits: int) -> dict[str, Any]:
    digit_count = max(CAPITAL_N_VALUES) - 1 + tail_digits
    digits, dps = pi_digits(digit_count, guard_digits)
    all_values = orbit_values(digits, max(CAPITAL_N_VALUES), tail_digits)
    scale = 10**tail_digits
    ordered_values = sorted(all_values)
    sort_margin = min(
        [right - left for left, right in zip(ordered_values, ordered_values[1:])]
        + [scale + ordered_values[0] - ordered_values[-1]]
    )
    pair_margin = scale
    boundary_margin = scale
    complete_signature: list[Any] = []
    minima: list[dict[str, Any]] = []

    for n in N_VALUES:
        records: list[dict[str, Any]] = []
        for capital_n in CAPITAL_N_VALUES:
            values = all_values[:capital_n]
            q_value, lags, local_pair_margin = fast_pairs(values, n, tail_digits)
            energy, local_boundary_margin = cylinder_energy(values, n, tail_digits)
            pair_margin = min(pair_margin, local_pair_margin)
            boundary_margin = min(boundary_margin, local_boundary_margin)
            unordered_pairs = sum(lags.values())
            ranked = sorted(lags.items(), key=lambda item: (-item[1], item[0]))
            maximum = ranked[0][1] if ranked else None
            record = {
                "N": capital_n,
                "Q_pi": q_value,
                "cylinder_energy": energy,
                "unordered_pairs": unordered_pairs,
                "q_ratio": (n * q_value, capital_n * capital_n),
                "energy_ratio": (n * energy, capital_n * capital_n),
                "top1_ratio": (maximum, unordered_pairs) if maximum else None,
                "top10_ratio": (sum(count for _, count in ranked[:10]), unordered_pairs) if ranked else None,
                "maximizing_lags": [lag for lag, count in ranked if count == maximum],
                "top_lags": ranked[:10],
            }
            records.append(record)
            complete_signature.append([n, capital_n, q_value, energy, sorted(lags.items())])
        minima.append(
            {
                "n": n,
                "min_n_Q_over_N_squared": minimum(records, "q_ratio"),
                "min_n_energy_over_N_squared": minimum(records, "energy_ratio"),
                "min_top1_lag_share": minimum(records, "top1_ratio"),
                "min_top10_lag_share": minimum(records, "top10_ratio"),
            }
        )

    direct_signature: list[Any] = []
    for n in DIRECT_N_VALUES:
        for capital_n in DIRECT_CAPITAL_N_VALUES:
            values = all_values[:capital_n]
            fast_q, fast_lags, fast_margin = fast_pairs(values, n, tail_digits)
            fast_energy, fast_boundary = cylinder_energy(values, n, tail_digits)
            direct_q, direct_lags, direct_energy, direct_margin, direct_boundary = direct_statistics(
                values, n, tail_digits
            )
            if (fast_q, fast_lags, fast_energy) != (direct_q, direct_lags, direct_energy):
                raise RuntimeError(f"quadratic validation failed at n={n}, N={capital_n}")
            pair_margin = min(pair_margin, fast_margin, direct_margin)
            boundary_margin = min(boundary_margin, fast_boundary, direct_boundary)
            direct_signature.append([n, capital_n, direct_q, direct_energy, sorted(direct_lags.items())])

    return {
        "digits": digits,
        "digit_count": digit_count,
        "dps": dps,
        "semantic_sha256": canonical_hash([complete_signature, direct_signature]),
        "minima": minima,
        "sort_margin": sort_margin,
        "pair_margin": pair_margin,
        "boundary_margin": boundary_margin,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--statement", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--initial-tail-digits", type=int, default=24)
    parser.add_argument("--precision-step", type=int, default=12)
    parser.add_argument("--max-tail-digits", type=int, default=60)
    parser.add_argument("--guard-digits", type=int, default=25)
    args = parser.parse_args()

    if mpmath.__version__ != MPMATH_VERSION:
        raise SystemExit(f"mpmath version must be {MPMATH_VERSION}, found {mpmath.__version__}")
    if file_hash(args.statement) != STATEMENT_SHA256:
        raise SystemExit("canonical statement SHA-256 mismatch")
    if args.initial_tail_digits <= max(N_VALUES) or args.precision_step < 1:
        raise SystemExit("invalid precision parameters")

    checks: list[dict[str, Any]] = []
    previous: dict[str, Any] | None = None
    final: dict[str, Any] | None = None
    for tail_digits in range(args.initial_tail_digits, args.max_tail_digits + 1, args.precision_step):
        current = evaluate(tail_digits, args.guard_digits)
        prefix_equal = previous is not None and current["digits"].startswith(previous["digits"])
        semantic_equal = previous is not None and current["semantic_sha256"] == previous["semantic_sha256"]
        margins_clear = min(current["sort_margin"], current["pair_margin"], current["boundary_margin"]) > 2
        checks.append(
            {
                "tail_digits": tail_digits,
                "pi_fraction_digits_generated": current["digit_count"],
                "mpmath_decimal_precision": current["dps"],
                "semantic_sha256": current["semantic_sha256"],
                "previous_digit_prefix_equal": prefix_equal,
                "previous_semantic_counts_equal": semantic_equal,
                "all_reported_integer_margins_exceed_two_units": margins_clear,
                "minimum_sort_gap": f"{current['sort_margin']}e-{tail_digits}",
                "minimum_pair_threshold_margin": f"{current['pair_margin']}e-{tail_digits}",
                "minimum_cylinder_boundary_margin": f"{current['boundary_margin']}e-{tail_digits}",
            }
        )
        if prefix_equal and semantic_equal and margins_clear:
            final = current
            break
        previous = current
    if final is None:
        raise SystemExit("adaptive precision did not stabilize within the declared bound")

    output = {
        "artifact_kind": "experiment",
        "item_id": "T8",
        "algorithm": {
            "id": "sorted-circular-prefix-v1",
            "pair_counting": "sort plus circular forward scan",
            "pair_counting_complexity": "O(N log N + K) time and O(N + K_lag) memory",
            "K_definition": "number of unordered non-diagonal near-return pairs",
            "strict_threshold": True,
            "ordered_pairs": True,
            "diagonal_included": True,
        },
        "inputs": {
            "constant": "pi",
            "base": 10,
            "statement_file": "canonical_statement.txt",
            "statement_sha256": STATEMENT_SHA256,
            "code_sha256": file_hash(Path(__file__).resolve()),
            "mpmath_version": mpmath.__version__,
        },
        "search_bounds": {
            "n_values": list(N_VALUES),
            "N_values": list(CAPITAL_N_VALUES),
            "N_selection": "each listed N independently; no intermediate N",
            "precision_tail_digits": {
                "initial": args.initial_tail_digits,
                "step": args.precision_step,
                "maximum": args.max_tail_digits,
                "extra_mpmath_digits": args.guard_digits,
            },
        },
        "quadratic_validation": {
            "n_values": list(DIRECT_N_VALUES),
            "N_values": list(DIRECT_CAPITAL_N_VALUES),
            "cases_checked": len(DIRECT_N_VALUES) * len(DIRECT_CAPITAL_N_VALUES),
            "compared_quantities": ["Q_pi", "complete unordered lag histogram", "finite cylinder collision energy"],
            "all_equal": True,
        },
        "precision_checks": checks,
        "reported_values": {
            "policy": "only minima over the explicitly listed N search set",
            "lag_share_denominator": "all unordered non-diagonal near-return pairs",
            "minima_by_n": final["minima"],
        },
        "interpretation": {
            "label": "experiment",
            "scope": "bounded fixed-pi heuristic evidence only",
            "claim": "These finite computations neither prove nor refute C1 or C2 and make no universal or fixed-pi proof claim.",
        },
    }
    args.output.write_bytes(json.dumps(output, indent=2, sort_keys=True).encode() + b"\n")


if __name__ == "__main__":
    main()
