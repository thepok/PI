#!/usr/bin/env python3
"""Certified finite T56/T69 census for the first sparse pi labels.

All mathematical classifications and counts use integers. The imported T62
module reconstructs a directed rational interval for pi. Floating point is
used only for elapsed-time and memory reporting.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
import math
import platform
import resource
import sys
import time
from pathlib import Path
from typing import Any

import t62_census


sys.set_int_max_str_digits(0)

ITEM = "T71"
LABEL = "experiment"
MIN_N = 2
MAX_N = 12
CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
T56_SHA256 = "41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc"
T69_SHA256 = "43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9"
MAX_REPORTED_WITNESSES_PER_LAG = 32
MAX_COMPONENT_WITNESS_POSITIONS = 8
MAX_TOP_COMPONENTS = 12


class TimeCapExceeded(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_source_pins(directory: Path) -> dict[str, str]:
    pins = {
        "pi-positive-decimal-factor-entropy.txt": CANONICAL_SHA256,
        "T56LagSectorAudit.lean": T56_SHA256,
        "T69FiveCaseCharging.lean": T69_SHA256,
    }
    observed = {name: sha256_file(directory / name) for name in pins}
    for name, expected in pins.items():
        if observed[name] != expected:
            raise RuntimeError(
                f"source hash mismatch for {name}: expected {expected}, got {observed[name]}"
            )
    return observed


def rational_text(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "undefined"
    divisor = math.gcd(numerator, denominator)
    return f"{numerator // divisor}/{denominator // divisor}"


def check_deadline(deadline: float | None, stage: str) -> None:
    if deadline is not None and time.perf_counter() >= deadline:
        raise TimeCapExceeded(stage)


def classify_five(q: int, a: int, b: int) -> str | None:
    """T69 classifyFive priority, restricted to actual adjacent pairs."""
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


def pi_labels(digits: str, n: int, length: int) -> list[int]:
    """T69 piLabelSequence: first L length-n fractional decimal blocks."""
    return t62_census.decimal_windows(digits, n, length)


def component_census(
    labels: list[int], n: int, deadline: float | None = None
) -> tuple[int, dict[str, Any]]:
    counts = Counter(labels)
    check_deadline(deadline, f"T71_components_n_{n}")
    histogram = Counter(counts.values())
    base_load = sum(size * size for size in counts.values())
    e3 = 3 * base_load

    top_pairs = sorted(counts.items(), key=lambda item: (-item[1], item[0]))[
        :MAX_TOP_COMPONENTS
    ]
    wanted = {label for label, _size in top_pairs}
    positions: dict[int, list[int]] = {label: [] for label in wanted}
    for index, label in enumerate(labels):
        if index % 65_536 == 0:
            check_deadline(deadline, f"T71_component_witnesses_n_{n}")
        if label in wanted and len(positions[label]) < MAX_COMPONENT_WITNESS_POSITIONS:
            positions[label].append(index)

    top_components = [
        {
            "label": label,
            "decimal_label": str(label).zfill(n),
            "size": size,
            "witness_positions": positions[label],
        }
        for label, size in top_pairs
    ]
    histogram_rows = []
    for size, number in sorted(histogram.items()):
        contribution = 3 * number * size * size
        histogram_rows.append(
            {
                "component_size": size,
                "number_of_nonempty_components": number,
                "E3_contribution": contribution,
                "E3_contribution_fraction": rational_text(contribution, e3),
            }
        )

    return e3, {
        "nonempty_component_count": len(counts),
        "base_equality_component_load": base_load,
        "E3_equals_three_times_base_load": e3,
        "maximum_component_size": max(counts.values(), default=0),
        "size_histogram": histogram_rows,
        "top_component_witnesses": top_components,
    }


def audit_labels(
    n: int,
    digits: str,
    short_table: dict[str, Any],
    deadline: float | None = None,
) -> dict[str, Any]:
    length = 10 ** (n // 2)
    q = 10**n
    labels = pi_labels(digits, n, length)
    e3, components = component_census(labels, n, deadline)
    short_rows = {row["lag"]: row for row in short_table["per_lag"]}

    per_lag = []
    total_unoriented = 0
    all_witnesses = 0
    for lag in range(1, min(n, length)):
        cases = Counter()
        witnesses = []
        for j in range(length - lag):
            if j % 65_536 == 0:
                check_deadline(deadline, f"T71_W5_n_{n}_lag_{lag}")
            a = labels[j]
            b = labels[j + lag]
            case = classify_five(q, a, b)
            if case is not None:
                cases[case] += 1
                all_witnesses += 1
                if len(witnesses) < MAX_REPORTED_WITNESSES_PER_LAG:
                    witnesses.append(
                        {
                            "j": j,
                            "j_plus_r": j + lag,
                            "left_label": a,
                            "right_label": b,
                            "case": case,
                        }
                    )
        unoriented = sum(cases.values())
        total_unoriented += unoriented
        raw_row = short_rows[lag]
        if raw_row["unoriented_hits"] != 0:
            raise RuntimeError(
                "baseline raw near-return set was unexpectedly nonempty; "
                "parameter-independent residual conclusion is unavailable"
            )
        per_lag.append(
            {
                "lag": lag,
                "start_capacity": length - lag,
                "W5_unoriented_contribution": unoriented,
                "W5_ordered_contribution": 2 * unoriented,
                "five_case_counts": {
                    name: cases[name]
                    for name in (
                        "equal",
                        "predecessor",
                        "successor",
                        "wrapPredecessor",
                        "wrapSuccessor",
                    )
                },
                "reported_witnesses": witnesses,
                "reported_witnesses_complete": len(witnesses) == unoriented,
                "raw_short_near_return_unoriented": raw_row["unoriented_hits"],
                "T56_short_residual_ordered_for_all_mu_c_Q0": 0,
                "closest_strict_boundary_witness": raw_row[
                    "closest_boundary_witness"
                ],
            }
        )

    w5 = 2 * total_unoriented
    for row in per_lag:
        row["W5_concentration_fraction"] = rational_text(
            row["W5_ordered_contribution"], w5
        )
    charging_rhs = length + e3
    if w5 > charging_rhs:
        raise RuntimeError("computed data violates imported T69 charging theorem")

    return {
        "n": n,
        "L_n": length,
        "label_modulus": q,
        "label_definition": "piCylinderCode n i = length-n decimal block starting at fractional digit i+1",
        "short_lag_domain": f"1 <= r < {min(n, length)}; 0 <= j < L_n-r",
        "W5": w5,
        "W5_over_L_n": rational_text(w5, length),
        "E3": e3,
        "E3_over_L_n": rational_text(e3, length),
        "T56_short_residual_ordered_for_all_mu_c_Q0": 0,
        "short_residual_over_L_n": "0/1",
        "T69_charging_rhs_L_n_plus_E3": charging_rhs,
        "T69_charging_slack": charging_rhs - w5,
        "T69_charging_utilization": rational_text(w5, charging_rhs),
        "components": components,
        "per_lag": per_lag,
        "W5_witness_count": all_witnesses,
        "unresolved_boundary_cases": short_table["unresolved_boundary_cases"],
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


def audit_range(
    min_n: int,
    max_n: int,
    digits: str,
    guard_digits: int,
    deadline: float | None = None,
) -> list[dict[str, Any]]:
    tables = []
    for n in range(min_n, max_n + 1):
        check_deadline(deadline, f"T71_before_n_{n}")
        short_table = t62_census.audit_scale(n, digits, guard_digits, deadline)
        if short_table["unresolved_boundary_cases"]:
            raise RuntimeError(f"n={n} has unresolved strict-boundary cases")
        tables.append(audit_labels(n, digits, short_table, deadline))
    return tables


def deterministic_projection(result: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in result.items()
        if key not in {"performance_observed", "replay_verification"}
    }


def build_result(args: argparse.Namespace, directory: Path) -> tuple[dict[str, Any], str]:
    started = time.perf_counter()
    source_pins = check_source_pins(directory)
    optional_enabled = args.optional_max_n is not None
    if optional_enabled:
        if args.optional_max_n <= MAX_N:
            raise ValueError("--optional-max-n must exceed 12")
        if args.max_length is None or args.max_candidates is None or args.max_seconds is None:
            raise ValueError(
                "optional scales require --max-length, --max-candidates, and --max-seconds"
            )
        if args.max_length <= 0 or args.max_candidates <= 0:
            raise ValueError("optional length and candidate caps must be positive")
        if not math.isfinite(args.max_seconds) or args.max_seconds <= 0:
            raise ValueError("optional time cap must be finite and positive")

    baseline_length = 10 ** (MAX_N // 2)
    decimal_places = baseline_length + MAX_N + args.guard_digits - 1
    digits, certificate = t62_census.certify_pi(decimal_places)
    baseline_tables = audit_range(MIN_N, MAX_N, digits, args.guard_digits)
    unresolved = sum(row["unresolved_boundary_cases"] for row in baseline_tables)
    if len(baseline_tables) != MAX_N - MIN_N + 1 or unresolved:
        raise RuntimeError("mandatory baseline is incomplete or unresolved")

    optional_plan = []
    optional_tables = []
    if optional_enabled:
        optional_started = time.perf_counter()
        deadline = optional_started + args.max_seconds
        for n in range(MAX_N + 1, args.optional_max_n + 1):
            length = 10 ** (n // 2)
            candidates = sum(length - lag for lag in range(1, min(n, length)))
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
                optional_places = length + n + args.guard_digits - 1
                optional_digits, _optional_certificate = t62_census.certify_pi(
                    optional_places, deadline
                )
                table = audit_range(n, n, optional_digits, args.guard_digits, deadline)[0]
            except (TimeCapExceeded, t62_census.TimeCapExceeded) as error:
                optional_plan.append(
                    {
                        "n": n,
                        "status": "capped",
                        "reason": "max_seconds",
                        "stage": str(error),
                    }
                )
                break
            optional_tables.append(table)
            optional_plan.append(
                {
                    "n": n,
                    "status": "completed",
                    "L_n": length,
                    "candidate_count": candidates,
                }
            )

    elapsed = time.perf_counter() - started
    result = {
        "item": ITEM,
        "label": LABEL,
        "source_pins": source_pins,
        "kernel_checked_imports": {
            "T56": "TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit",
            "T69": "TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging",
            "audit_file": "T71ConventionAudit.lean",
        },
        "definitions": {
            "L_n": "10^(n//2), natural-number division",
            "short_lags": "0 < r < n and r < L_n",
            "starts": "0 <= j < L_n-r",
            "W5": "twice the sum of T69 CyclicAdjacent starts over exact short lags",
            "E3": "three times the sum of squared pi-label component sizes",
            "short_residual": "T56 shortResidualPairCount(mu,c,Q0,n,L_n); zero for every parameter choice because each containing raw near-return set is certified empty",
            "charging_slack": "(L_n + E3) - W5",
        },
        "pi_certificate": certificate_projection(certificate),
        "mandatory_baseline": {
            "n_range": [MIN_N, MAX_N],
            "guard_digits": args.guard_digits,
            "complete": True,
            "unresolved_boundary_cases": unresolved,
            "tables": baseline_tables,
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
        },
        "scope": {
            "bounded_sibling_A14": True,
            "finite_heuristic_evidence_only": True,
            "proves_eventual_bound": False,
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


def verify_witnesses(result: dict[str, Any], digits: str) -> dict[str, int | bool]:
    adjacency_checked = 0
    component_positions_checked = 0
    boundary_checked = 0
    for table in result["mandatory_baseline"]["tables"]:
        n = table["n"]
        length = table["L_n"]
        q = table["label_modulus"]
        labels = pi_labels(digits, n, length)
        counts = Counter(labels)
        for component in table["components"]["top_component_witnesses"]:
            label = component["label"]
            if counts[label] != component["size"]:
                raise RuntimeError(f"component size witness failed at n={n}, label={label}")
            for position in component["witness_positions"]:
                if labels[position] != label:
                    raise RuntimeError(f"component position witness failed at n={n}")
                component_positions_checked += 1
        width = n + result["mandatory_baseline"]["guard_digits"]
        boundary_windows = t62_census.decimal_windows(digits, width, length)
        for lag_row in table["per_lag"]:
            lag = lag_row["lag"]
            for witness in lag_row["reported_witnesses"]:
                j = witness["j"]
                if labels[j] != witness["left_label"] or labels[j + lag] != witness["right_label"]:
                    raise RuntimeError(f"adjacency label witness failed at n={n}, r={lag}")
                if classify_five(q, labels[j], labels[j + lag]) != witness["case"]:
                    raise RuntimeError(f"adjacency case witness failed at n={n}, r={lag}")
                adjacency_checked += 1
            boundary = lag_row["closest_strict_boundary_witness"]
            j = boundary["j"]
            checked = t62_census.classify_prefix_difference(
                boundary_windows[j], boundary_windows[j + lag], width, n
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
                if checked[key] != boundary[key]:
                    raise RuntimeError(f"strict-boundary witness failed at n={n}, r={lag}")
            boundary_checked += 1
    return {
        "expected_deterministic_projection_matches": True,
        "adjacency_witnesses_checked": adjacency_checked,
        "component_positions_checked": component_positions_checked,
        "strict_boundary_witnesses_checked": boundary_checked,
        "unresolved_boundary_cases": result["mandatory_baseline"][
            "unresolved_boundary_cases"
        ],
    }


def verify_baseline_table(result: dict[str, Any], path: Path) -> int:
    fieldnames = [
        "n",
        "L_n",
        "W5",
        "W5_over_L_n",
        "E3",
        "E3_over_L_n",
        "T56_short_residual",
        "T69_charging_slack",
        "maximum_component_size",
        "unresolved_boundary_cases",
    ]
    expected = []
    for table in result["mandatory_baseline"]["tables"]:
        expected.append(
            {
                "n": str(table["n"]),
                "L_n": str(table["L_n"]),
                "W5": str(table["W5"]),
                "W5_over_L_n": table["W5_over_L_n"],
                "E3": str(table["E3"]),
                "E3_over_L_n": table["E3_over_L_n"],
                "T56_short_residual": str(
                    table["T56_short_residual_ordered_for_all_mu_c_Q0"]
                ),
                "T69_charging_slack": str(table["T69_charging_slack"]),
                "maximum_component_size": str(
                    table["components"]["maximum_component_size"]
                ),
                "unresolved_boundary_cases": str(
                    table["unresolved_boundary_cases"]
                ),
            }
        )
    with path.open(newline="", encoding="ascii") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames != fieldnames or list(reader) != expected:
            raise RuntimeError("baseline_table.csv differs from the fresh T71 census")
    return len(expected)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--guard-digits", type=int, default=16)
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
    result, digits = build_result(args, directory)
    if args.verify:
        expected = json.loads(args.verify.read_text(encoding="ascii"))
        if deterministic_projection(result) != deterministic_projection(expected):
            raise RuntimeError("deterministic replay differs from expected T71 census")
        result["replay_verification"] = verify_witnesses(result, digits)
        result["replay_verification"]["baseline_table_rows_checked"] = (
            verify_baseline_table(result, directory / "baseline_table.csv")
        )
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="ascii")
    if args.quiet:
        checks = result.get("replay_verification", {})
        print(
            "T71 census: PASS; n=2..12; "
            f"unresolved={result['mandatory_baseline']['unresolved_boundary_cases']}; "
            f"boundary_witnesses={checks.get('strict_boundary_witnesses_checked', 'not-requested')}; "
            f"elapsed_seconds={result['performance_observed']['elapsed_seconds']}; "
            f"peak_rss_kib={result['performance_observed']['peak_rss_kib']}"
        )
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
