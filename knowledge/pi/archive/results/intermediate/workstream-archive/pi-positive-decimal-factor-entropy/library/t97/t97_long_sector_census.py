#!/usr/bin/env python3
"""T97 boundary-safe circular-sort census of T56's complete long-lag sector."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import platform
import resource
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any, Iterator

import t62_census


sys.set_int_max_str_digits(0)

ITEM = "T97"
LABEL = "experiment"
MIN_N = 2
MAX_N = 12
GUARD_STEPS = (4, 8, 16, 32)
CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE_PINS = {
    "pi-positive-decimal-factor-entropy.txt": CANONICAL_SHA256,
    "t62_census.py": "8bfe1929658644d7cb986d592d1b5afbe0b95567001c79b85d22fa3d1c5178c7",
    "T56LagSectorAudit.lean": "41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc",
    "T69FiveCaseCharging.lean": "43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9",
    "T71ConventionAudit.lean": "228ff683b81368049f703fd1016e92131c77ce43b19406335f8a865e9e356d66",
    "T71_short_baseline.csv": "5349f89c3755b67d2babb83210546acfba1b7077f66c2772f95fee0d4388dd4e",
    "milla-chudnovsky-1809.00533v6.pdf": "69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20",
    "milla-chudnovsky-1809.00533v6.txt": "f1bc6daff21f730bf3e3856938f04bcf53056ee896f30f98bb7f2ebb3e7ec564",
}


class CandidateCapExceeded(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_source_pins(directory: Path) -> dict[str, str]:
    observed = {name: sha256_file(directory / name) for name in SOURCE_PINS}
    for name, expected in SOURCE_PINS.items():
        if observed[name] != expected:
            raise RuntimeError(
                f"source hash mismatch for {name}: expected {expected}, got {observed[name]}"
            )
    return observed


def rational_text(numerator: int, denominator: int) -> str:
    divisor = math.gcd(numerator, denominator)
    return f"{numerator // divisor}/{denominator // divisor}"


def check_deadline(deadline: float | None, stage: str) -> None:
    if deadline is not None and time.perf_counter() >= deadline:
        raise t62_census.TimeCapExceeded(stage)


def classify_five(q: int, a: int, b: int) -> str | None:
    """T69's accepted five-case priority for two decimal-cell labels."""
    if b == a:
        return "equal"
    if b + 1 == a:
        return "predecessor"
    if a + 1 == b:
        return "successor"
    if a == 0 and b + 1 == q:
        return "wrapPredecessor"
    if b == 0 and a + 1 == q:
        return "wrapSuccessor"
    return None


def read_short_baseline(path: Path) -> dict[int, dict[str, str]]:
    with path.open(newline="", encoding="ascii") as source:
        rows = list(csv.DictReader(source))
    baseline = {int(row["n"]): row for row in rows}
    if sorted(baseline) != list(range(MIN_N, MAX_N + 1)):
        raise RuntimeError("T71 short baseline does not contain exactly n=2..12")
    return baseline


def circular_prefix_candidates(
    windows: list[int],
    cutoff: int,
    base: int,
    deadline: float | None,
    candidate_cap: int | None,
) -> Iterator[tuple[int, int]]:
    """Yield every unordered pair whose prefix-circle distance is <= cutoff.

    Since each true orbit point lies in its prefix cell of width 1/base, any
    pair not yielded has lower distance bound at least cutoff/base and is a
    certified miss. The doubled-circle indexing is virtual, avoiding a second
    O(L) tuple array.
    """
    length = len(windows)
    order = list(range(length))
    order.sort(key=windows.__getitem__)
    yielded = 0
    for position in range(length):
        if position % 65_536 == 0:
            check_deadline(deadline, "circular_candidate_scan")
        left_index = order[position]
        left_value = windows[left_index]
        right_position = position + 1
        while right_position < position + length:
            wrapped = right_position >= length
            right_index = order[right_position - length if wrapped else right_position]
            right_value = windows[right_index] + (base if wrapped else 0)
            if right_value - left_value > cutoff:
                break
            yielded += 1
            if candidate_cap is not None and yielded > candidate_cap:
                raise CandidateCapExceeded(str(yielded))
            if left_index < right_index:
                yield left_index, right_index
            else:
                yield right_index, left_index
            right_position += 1


def w5_short_census(labels: list[int], n: int, deadline: float | None) -> dict[str, Any]:
    q = 10**n
    cases: Counter[str] = Counter()
    per_lag = []
    for lag in range(1, min(n, len(labels))):
        lag_cases: Counter[str] = Counter()
        for j in range(len(labels) - lag):
            if j % 65_536 == 0:
                check_deadline(deadline, f"W5_n_{n}_lag_{lag}")
            case = classify_five(q, labels[j], labels[j + lag])
            if case is not None:
                lag_cases[case] += 1
                cases[case] += 1
        per_lag.append(
            {
                "lag": lag,
                "unoriented_count": sum(lag_cases.values()),
                "ordered_count": 2 * sum(lag_cases.values()),
                "five_case_counts": {
                    name: lag_cases[name]
                    for name in (
                        "equal",
                        "predecessor",
                        "successor",
                        "wrapPredecessor",
                        "wrapSuccessor",
                    )
                },
            }
        )
    return {
        "W5_ordered": 2 * sum(cases.values()),
        "per_lag": per_lag,
    }


def scan_scale_at_guard(
    n: int,
    digits: str,
    guard: int,
    deadline: float | None,
    candidate_cap: int | None,
) -> dict[str, Any]:
    length = 10 ** (n // 2)
    width = n + guard
    base = 10**width
    cutoff = 10**guard
    windows = t62_census.decimal_windows(digits, width, length, deadline)
    long_counts = [0] * (length - n)
    short_counts = [0] * (min(n, length) - 1)
    long_witnesses: list[dict[str, Any]] = []
    short_witnesses: list[dict[str, Any]] = []
    unresolved: list[dict[str, Any]] = []
    candidate_count = 0

    for j, k in circular_prefix_candidates(
        windows, cutoff, base, deadline, candidate_cap
    ):
        candidate_count += 1
        lag = k - j
        result = t62_census.classify_prefix_difference(
            windows[j], windows[k], width, n
        )
        sector = "short" if lag < n else "long"
        if result["classification"] == "unresolved":
            unresolved.append({"j": j, "j_plus_r": k, "lag": lag, "sector": sector})
            continue
        if result["classification"] != "hit":
            continue

        label_divisor = 10**guard
        left_label = windows[j] // label_divisor
        right_label = windows[k] // label_divisor
        cell_case = classify_five(10**n, left_label, right_label)
        if cell_case is None:
            raise RuntimeError(
                f"strict hit lacks a T69 cell classification at n={n}, j={j}, r={lag}"
            )
        witness = {
            "j": j,
            "j_plus_r": k,
            "lag": lag,
            "ordered_multiplicity": 2,
            "left_decimal_block": str(left_label).zfill(n),
            "right_decimal_block": str(right_label).zfill(n),
            "adjacent_cell_classification": cell_case,
            "left_prefix": windows[j],
            "right_prefix": windows[k],
            **result,
        }
        if sector == "long":
            long_counts[lag - n] += 1
            long_witnesses.append(witness)
        else:
            short_counts[lag - 1] += 1
            short_witnesses.append(witness)

    labels = [window // (10**guard) for window in windows]
    w5 = w5_short_census(labels, n, deadline)
    return {
        "guard_digits": guard,
        "prefix_width": width,
        "prefix_candidate_pairs": candidate_count,
        "unresolved": unresolved,
        "long_counts": long_counts,
        "short_counts": short_counts,
        "long_witnesses": long_witnesses,
        "short_witnesses": short_witnesses,
        "w5": w5,
    }


def audit_scale(
    n: int,
    digits: str,
    short_baseline: dict[int, dict[str, str]],
    deadline: float | None = None,
    candidate_cap: int | None = None,
) -> dict[str, Any]:
    length = 10 ** (n // 2)
    precision_attempts = []
    scan: dict[str, Any] | None = None
    for guard in GUARD_STEPS:
        check_deadline(deadline, f"before_n_{n}_guard_{guard}")
        scan = scan_scale_at_guard(n, digits, guard, deadline, candidate_cap)
        precision_attempts.append(
            {
                "guard_digits": guard,
                "prefix_candidate_pairs": scan["prefix_candidate_pairs"],
                "unresolved_boundary_cases": len(scan["unresolved"]),
            }
        )
        if not scan["unresolved"]:
            break
    if scan is None or scan["unresolved"]:
        count = 0 if scan is None else len(scan["unresolved"])
        raise RuntimeError(f"n={n} retains {count} unresolved boundary cases")

    long_counts: list[int] = scan["long_counts"]
    long_witnesses: list[dict[str, Any]] = scan["long_witnesses"]
    direct_unoriented_total = len(long_witnesses)
    summed_unoriented_total = sum(long_counts)
    recomputed_counts = [0] * len(long_counts)
    for witness in long_witnesses:
        recomputed_counts[witness["lag"] - n] += 1
    if recomputed_counts != long_counts or summed_unoriented_total != direct_unoriented_total:
        raise RuntimeError(f"independent per-lag aggregation failed at n={n}")

    short_unoriented = sum(scan["short_counts"])
    accepted = short_baseline.get(n)
    accepted_w5 = None if accepted is None else int(accepted["W5"])
    accepted_residual = (
        None if accepted is None else int(accepted["T56_short_residual"])
    )
    if accepted is not None:
        if 2 * short_unoriented != 0 or accepted_residual != 0:
            raise RuntimeError(f"raw-short emptiness comparison failed at n={n}")
        if scan["w5"]["W5_ordered"] != accepted_w5:
            raise RuntimeError(f"T71 W5 comparison failed at n={n}")

    positive = [(n + offset, count) for offset, count in enumerate(long_counts) if count]
    maximum_count = max((count for _lag, count in positive), default=0)
    maximum_lags = [lag for lag, count in positive if count == maximum_count]
    ordered_counts = [2 * count for count in long_counts]
    return {
        "n": n,
        "L_n": length,
        "sample_length_definition": "10^(n//2), natural-number division",
        "long_lag_range": {"first": n, "last": length - 1, "count": length - n},
        "start_range": "for lag r: 0 <= j < L_n-r",
        "strict_cutoff": f"circleDistance(10^j*(10^r-1)*pi) < 10^-{n}",
        "normalization": "each j<j+r hit has ordered multiplicity 2",
        "algorithm": {
            "name": "integer circular prefix sort and forward window",
            "complexity": "O(L_n log L_n + K_n), where K_n is the enumerated prefix-candidate count",
            "noncandidate_certificate": "prefix circle distance > 10^guard implies conservative lower distance >= strict cutoff",
        },
        "adaptive_precision": {
            "guard_schedule": list(GUARD_STEPS),
            "attempts": precision_attempts,
            "selected_guard_digits": scan["guard_digits"],
            "selected_prefix_width": scan["prefix_width"],
        },
        "per_lag_ordered_counts": {
            "lag_offset": n,
            "counts": ordered_counts,
            "interpretation": "counts[i] is the ordered count at lag r=lag_offset+i",
        },
        "totals": {
            "unoriented_long_hits_direct": direct_unoriented_total,
            "unoriented_long_hits_from_per_lag_sum": summed_unoriented_total,
            "ordered_long_count": 2 * direct_unoriented_total,
            "ordered_long_count_over_L_n": rational_text(
                2 * direct_unoriented_total, length
            ),
            "unordered_long_pair_capacity": (length - n) * (length - n + 1) // 2,
            "prefix_candidate_pairs_all_positive_lags": scan["prefix_candidate_pairs"],
        },
        "contributing_lags": {
            "positive_unoriented_counts": [
                {"lag": lag, "unoriented_count": count, "ordered_count": 2 * count}
                for lag, count in positive
            ],
            "maximum_unoriented_per_lag_count": maximum_count,
            "lags_attaining_positive_maximum": maximum_lags,
            "largest_contributing_lag": max((lag for lag, _count in positive), default=None),
        },
        "hit_witnesses": long_witnesses,
        "short_sector_comparison": {
            "raw_strict_short_ordered_count_recomputed": 2 * short_unoriented,
            "raw_strict_short_witnesses": scan["short_witnesses"],
            "accepted_T56_short_residual_ordered": accepted_residual,
            "T71_W5_ordered_recomputed": scan["w5"]["W5_ordered"],
            "T71_W5_ordered_accepted": accepted_w5,
            "T71_W5_per_lag_recomputed": scan["w5"]["per_lag"],
            "convention_warning": "W5 is the cyclic-adjacent cell superset, not the strict raw near-return count",
        },
        "independent_checks": {
            "dense_per_lag_vector_equals_witness_reaggregation": True,
            "direct_total_equals_per_lag_sum": True,
            "T71_W5_matches_pinned_baseline": accepted is not None,
        },
        "unresolved_boundary_cases": 0,
    }


def certificate_projection(certificate: dict[str, Any]) -> dict[str, Any]:
    return {
        "method": certificate["method"],
        "analytic_identity": certificate["analytic_identity"],
        "decimal_places": certificate["decimal_places"],
        "series_terms": certificate["series_terms"],
        "attempts": certificate["attempts"],
        "decimal_prefix_64": certificate["decimal_prefix_64"],
        "decimal_suffix_64": certificate["decimal_suffix_64"],
        "scaled_floor_sha256": certificate["scaled_floor_sha256"],
        "decimal_digits_sha256": certificate["decimal_digits_sha256"],
        "exact_endpoint_hashes": certificate["exact_endpoint_hashes"],
        "certified_interval_form": certificate["certified_interval"]["form"],
        "scale": certificate["certified_interval"]["scale"],
    }


def deterministic_projection(result: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in result.items()
        if key not in {"performance_observed", "replay_verification"}
    }


def build_result(args: argparse.Namespace, directory: Path) -> tuple[dict[str, Any], str]:
    started = time.perf_counter()
    source_pins = check_source_pins(directory)
    short_baseline = read_short_baseline(directory / "T71_short_baseline.csv")
    optional_enabled = args.optional_max_n is not None
    if optional_enabled:
        if args.optional_max_n <= MAX_N:
            raise ValueError("--optional-max-n must exceed 12")
        if args.max_length is None or args.max_candidates is None or args.max_seconds is None:
            raise ValueError(
                "optional scales require --max-length, --max-candidates, and --max-seconds"
            )
        if args.max_length <= 0 or args.max_candidates <= 0:
            raise ValueError("optional caps must be positive")
        if not math.isfinite(args.max_seconds) or args.max_seconds <= 0:
            raise ValueError("--max-seconds must be finite and positive")

    baseline_length = 10 ** (MAX_N // 2)
    decimal_places = baseline_length + MAX_N + max(GUARD_STEPS) - 1
    digits, certificate = t62_census.certify_pi(decimal_places)
    tables = [
        audit_scale(n, digits, short_baseline) for n in range(MIN_N, MAX_N + 1)
    ]
    unresolved = sum(table["unresolved_boundary_cases"] for table in tables)
    if len(tables) != MAX_N - MIN_N + 1 or unresolved:
        raise RuntimeError("mandatory census is incomplete or unresolved")

    optional_plan = []
    optional_tables = []
    if optional_enabled:
        optional_started = time.perf_counter()
        deadline = optional_started + args.max_seconds
        for n in range(MAX_N + 1, args.optional_max_n + 1):
            length = 10 ** (n // 2)
            if length > args.max_length:
                optional_plan.append(
                    {"n": n, "status": "capped", "reason": "max_length", "L_n": length}
                )
                break
            try:
                places = length + n + max(GUARD_STEPS) - 1
                optional_digits, _certificate = t62_census.certify_pi(places, deadline)
                table = audit_scale(
                    n,
                    optional_digits,
                    short_baseline,
                    deadline=deadline,
                    candidate_cap=args.max_candidates,
                )
            except CandidateCapExceeded as error:
                optional_plan.append(
                    {
                        "n": n,
                        "status": "capped",
                        "reason": "max_candidates",
                        "observed_first_excess": int(str(error)),
                    }
                )
                break
            except t62_census.TimeCapExceeded as error:
                optional_plan.append(
                    {"n": n, "status": "capped", "reason": "max_seconds", "stage": str(error)}
                )
                break
            optional_tables.append(table)
            optional_plan.append({"n": n, "status": "completed", "L_n": length})

    elapsed = time.perf_counter() - started
    result = {
        "item": ITEM,
        "label": LABEL,
        "canonical_statement": {
            "file": "pi-positive-decimal-factor-entropy.txt",
            "sha256": source_pins["pi-positive-decimal-factor-entropy.txt"],
            "source_url": None,
            "bounded_sibling": "A14 finite-prefix experiment",
        },
        "source_pins": source_pins,
        "imported_conventions": {
            "T56": "L_n=10^(n//2); long lags n<=r<L_n; starts 0<=j<L_n-r; strict cutoff; factor-two ordered normalization",
            "T62": "directed Chudnovsky interval and conservative decimal-prefix classification",
            "T71": "T69 five-case cyclic adjacency and pinned short-sector baseline",
        },
        "pi_certificate": certificate_projection(certificate),
        "mandatory_baseline": {
            "n_range": [MIN_N, MAX_N],
            "complete": True,
            "unresolved_boundary_cases": unresolved,
            "tables": tables,
        },
        "optional_larger_scales": {
            "enabled": optional_enabled,
            "declared_caps": {
                "optional_max_n": args.optional_max_n,
                "max_length": args.max_length,
                "max_candidates": args.max_candidates,
                "max_seconds": args.max_seconds,
            },
            "plan_and_frontier": optional_plan,
            "tables": optional_tables,
            "separate_from_mandatory_verdict": True,
        },
        "scope": {
            "finite_heuristic_evidence_only": True,
            "proves_eventual_long_sector_bound": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
            "proves_positive_decimal_factor_entropy": False,
        },
        "performance_observed": {
            "elapsed_seconds": round(elapsed, 6),
            "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "python": platform.python_version(),
            "platform": platform.platform(),
        },
    }
    return result, digits


SUMMARY_FIELDS = [
    "n",
    "L_n",
    "long_lag_first",
    "long_lag_last",
    "ordered_long_count",
    "ordered_long_count_over_L_n",
    "positive_lag_count",
    "largest_contributing_lag",
    "selected_guard_digits",
    "prefix_candidate_pairs",
    "raw_short_ordered_count",
    "T71_W5_ordered",
    "unresolved_boundary_cases",
]


def summary_text(result: dict[str, Any]) -> str:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=SUMMARY_FIELDS, lineterminator="\n")
    writer.writeheader()
    for table in result["mandatory_baseline"]["tables"]:
        writer.writerow(
            {
                "n": table["n"],
                "L_n": table["L_n"],
                "long_lag_first": table["long_lag_range"]["first"],
                "long_lag_last": table["long_lag_range"]["last"],
                "ordered_long_count": table["totals"]["ordered_long_count"],
                "ordered_long_count_over_L_n": table["totals"][
                    "ordered_long_count_over_L_n"
                ],
                "positive_lag_count": len(
                    table["contributing_lags"]["positive_unoriented_counts"]
                ),
                "largest_contributing_lag": table["contributing_lags"][
                    "largest_contributing_lag"
                ],
                "selected_guard_digits": table["adaptive_precision"][
                    "selected_guard_digits"
                ],
                "prefix_candidate_pairs": table["totals"][
                    "prefix_candidate_pairs_all_positive_lags"
                ],
                "raw_short_ordered_count": table["short_sector_comparison"][
                    "raw_strict_short_ordered_count_recomputed"
                ],
                "T71_W5_ordered": table["short_sector_comparison"][
                    "T71_W5_ordered_recomputed"
                ],
                "unresolved_boundary_cases": table["unresolved_boundary_cases"],
            }
        )
    return stream.getvalue()


def verify_witnesses(result: dict[str, Any], digits: str) -> dict[str, Any]:
    checked = 0
    lag_rows_checked = 0
    for table in result["mandatory_baseline"]["tables"]:
        n = table["n"]
        guard = table["adaptive_precision"]["selected_guard_digits"]
        width = n + guard
        reconstructed = [0] * (table["L_n"] - n)
        for witness in table["hit_witnesses"]:
            j = witness["j"]
            lag = witness["lag"]
            left = int(digits[j : j + width])
            right = int(digits[j + lag : j + lag + width])
            classification = t62_census.classify_prefix_difference(left, right, width, n)
            if classification["classification"] != "hit":
                raise RuntimeError(f"hit witness failed at n={n}, j={j}, r={lag}")
            left_label = left // (10**guard)
            right_label = right // (10**guard)
            if classify_five(10**n, left_label, right_label) != witness[
                "adjacent_cell_classification"
            ]:
                raise RuntimeError(f"cell witness failed at n={n}, j={j}, r={lag}")
            reconstructed[lag - n] += 2
            checked += 1
        expected_counts = table["per_lag_ordered_counts"]["counts"]
        if reconstructed != expected_counts:
            raise RuntimeError(f"witness-to-per-lag reconstruction failed at n={n}")
        if sum(expected_counts) != table["totals"]["ordered_long_count"]:
            raise RuntimeError(f"per-lag-to-total reconstruction failed at n={n}")
        lag_rows_checked += len(expected_counts)
    return {
        "expected_deterministic_projection_matches": True,
        "hit_witnesses_checked": checked,
        "per_lag_rows_checked": lag_rows_checked,
        "unresolved_boundary_cases": result["mandatory_baseline"][
            "unresolved_boundary_cases"
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--summary-output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--optional-max-n", type=int)
    parser.add_argument("--max-length", type=int)
    parser.add_argument("--max-candidates", type=int)
    parser.add_argument("--max-seconds", type=float)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    directory = Path(__file__).resolve().parent
    result, digits = build_result(args, directory)
    if args.verify:
        expected = json.loads(args.verify.read_text(encoding="ascii"))
        if deterministic_projection(result) != deterministic_projection(expected):
            raise RuntimeError("deterministic replay differs from expected T97 census")
        expected_summary = (directory / "T97_mandatory_table.csv").read_text(encoding="ascii")
        if summary_text(result) != expected_summary:
            raise RuntimeError("mandatory summary table differs from fresh census")
        result["replay_verification"] = verify_witnesses(result, digits)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="ascii")
    if args.summary_output:
        args.summary_output.write_text(summary_text(result), encoding="ascii")
    if args.quiet:
        checks = result.get("replay_verification", {})
        print(
            "T97 census: PASS; n=2..12; "
            f"unresolved={result['mandatory_baseline']['unresolved_boundary_cases']}; "
            f"witnesses={checks.get('hit_witnesses_checked', 'not-requested')}; "
            f"lag_rows={checks.get('per_lag_rows_checked', 'not-requested')}; "
            f"elapsed_seconds={result['performance_observed']['elapsed_seconds']}; "
            f"peak_rss_kib={result['performance_observed']['peak_rss_kib']}"
        )
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
