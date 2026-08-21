#!/usr/bin/env python3
"""Replay the finite abstract short-lag obstruction used in the T56 note."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"


def instance(n: int, length: int) -> dict[str, object]:
    if n < 2 or length < 2 * n:
        raise ValueError("the abstract construction requires n >= 2 and L >= 2n")

    # At each short lag 1 <= r < n retain starts 0 <= j < L-n.
    # Since r < n, every retained j also satisfies the required j < L-r.
    fiber_count = length - n
    lags = list(range(1, n))
    endpoint_checks = [fiber_count == 0 or fiber_count - 1 < length - r for r in lags]
    short_ordered = 2 * len(lags) * fiber_count
    diagonal = length
    excluded = 0
    long_residual = 0
    total = diagonal + excluded + short_ordered + long_residual
    retained_short_budget = 2 * length * n

    assert all(endpoint_checks)
    assert short_ordered == 2 * (n - 1) * (length - n)
    assert short_ordered <= retained_short_budget
    assert total >= n * length

    return {
        "n": n,
        "L": length,
        "short_lag_range": [1, n - 1],
        "starts_at_each_short_lag": [0, fiber_count - 1],
        "short_lag_count": len(lags),
        "starts_per_short_lag": fiber_count,
        "ordered_short_incidence_count": short_ordered,
        "excluded_incidence_count": excluded,
        "long_residual_incidence_count": long_residual,
        "diagonal_count": diagonal,
        "total_incidence_count": total,
        "retained_short_budget_2Ln": retained_short_budget,
        "total_at_least_nL": total >= n * length,
        "all_triangular_endpoints_valid": all(endpoint_checks),
    }


def build_report(statement_path: Path) -> dict[str, object]:
    digest = hashlib.sha256(statement_path.read_bytes()).hexdigest()
    if digest != CANONICAL_SHA256:
        raise RuntimeError(f"canonical statement hash mismatch: {digest}")

    target_scale_instances = []
    for n in range(2, 13):
        length = 10 ** (n // 2)
        target_scale_instances.append(instance(n, length))

    constant_witnesses = []
    for constant in range(1, 11):
        n = constant + 1
        length = 10 ** (n // 2)
        row = instance(n, length)
        assert row["total_incidence_count"] > constant * length
        constant_witnesses.append(
            {
                "proposed_constant": constant,
                "witness_n": n,
                "witness_L": length,
                "total_incidence_count": row["total_incidence_count"],
                "constant_times_L": constant * length,
                "strict_failure": True,
            }
        )

    lean_scale_instances = []
    for n in range(2, 13):
        length = 2 * n
        row = instance(n, length)
        assert row["total_incidence_count"] == n * length
        lean_scale_instances.append(row)

    return {
        "label": "experiment",
        "claim_scope": (
            "Abstract finite incidence families only; no member is asserted to arise "
            "from pi. They show that the retained sector budgets do not logically "
            "imply a uniform linear total bound."
        ),
        "canonical_statement_sha256": digest,
        "construction": {
            "short_lags": "1 <= r < n",
            "starts": "0 <= j < L-n at every short lag",
            "orientations": 2,
            "diagonal": "L",
            "excluded_sector": 0,
            "long_residual_sector": 0,
            "ordered_short_count": "2*(n-1)*(L-n)",
            "total_count": "L+2*(n-1)*(L-n)",
        },
        "target_scale_instances": target_scale_instances,
        "constant_witnesses": constant_witnesses,
        "lean_exact_ratio_instances_L_eq_2n": lean_scale_instances,
        "all_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    report = build_report(here / "pi-positive-decimal-factor-entropy.txt")
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.write is not None:
        args.write.write_text(text, encoding="ascii")
    print(text, end="")


if __name__ == "__main__":
    main()
