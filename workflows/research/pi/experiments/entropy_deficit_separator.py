#!/usr/bin/env python3
"""Finite verifier for the de Bruijn entropy/collision separators.

This is an experiment only. It checks the exact finite word counts used in
20260824-entropy-deficit-haar-hierarchy.md and reports floating-point entropy
and collision diagnostics for manageable word lengths.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from collections import Counter
from dataclasses import asdict, dataclass, fields
from typing import Literal, TextIO


Mode = Literal["sqrt", "k"]


def de_bruijn(alphabet_size: int, order: int) -> list[int]:
    """Return a cyclic de Bruijn sequence B(alphabet_size, order)."""
    if alphabet_size < 2:
        raise ValueError("alphabet_size must be at least 2")
    if order < 1:
        raise ValueError("order must be positive")

    workspace = [0] * (alphabet_size * order + 1)
    output: list[int] = []

    def visit(t: int, period: int) -> None:
        if t > order:
            if order % period == 0:
                output.extend(workspace[1 : period + 1])
            return

        workspace[t] = workspace[t - period]
        visit(t + 1, period)
        for digit in range(workspace[t - period] + 1, alphabet_size):
            workspace[t] = digit
            visit(t + 1, t)

    visit(1, 1)
    expected = alphabet_size**order
    if len(output) != expected:
        raise AssertionError(f"de Bruijn length {len(output)} != {expected}")
    return output


@dataclass(frozen=True)
class StageResult:
    order: int
    mode: Mode
    cells: int
    zero_prefix_starts: int
    samples: int
    support: int
    exceptional_mass: float
    entropy_deficit: float
    deficit_per_digit: float
    convexity_upper_bound: float
    normalized_l2_energy: float
    old_collision_ratio: float
    zero_word_mass: float


def verify_stage(order: int, mode: Mode) -> StageResult:
    """Construct one finite stage and check its combinatorial contract."""
    q = 10**order
    scale = math.sqrt(order) if mode == "sqrt" else float(order)
    z = math.floor(q / scale)

    cycle = de_bruijn(10, order)
    linearized = cycle + cycle[: order - 1]
    digits = [0] * (z + order - 1) + linearized
    samples = q + z + order - 1
    if len(digits) != samples + order - 1:
        raise AssertionError("stage does not contain enough guard digits")

    counts = Counter(tuple(digits[i : i + order]) for i in range(samples))
    if sum(counts.values()) != samples:
        raise AssertionError("sample count mismatch")

    debruijn_start = z + order - 1
    debruijn_counts = Counter(
        tuple(digits[i : i + order])
        for i in range(debruijn_start, debruijn_start + q)
    )
    if len(debruijn_counts) != q or set(debruijn_counts.values()) != {1}:
        raise AssertionError("de Bruijn section is not exactly uniform")

    probabilities = [count / samples for count in counts.values()]
    entropy = -sum(p * math.log(p) for p in probabilities)
    deficit = math.log(q) - entropy
    normalized_l2 = q * sum(p * p for p in probabilities)
    collision_ratio = normalized_l2 / (1.0 + q / samples)
    exceptional_mass = (z + order - 1) / samples
    convexity_bound = exceptional_mass * math.log(q)
    zero_mass = counts[(0,) * order] / samples

    # Numerical checks only; the memo contains the asymptotic proof.
    tolerance = 1e-10 * max(1.0, convexity_bound)
    if deficit > convexity_bound + tolerance:
        raise AssertionError("KL convexity upper bound failed numerically")
    if zero_mass + 1e-15 < z / samples:
        raise AssertionError("zero-run lower bound failed")

    return StageResult(
        order=order,
        mode=mode,
        cells=q,
        zero_prefix_starts=z,
        samples=samples,
        support=len(counts),
        exceptional_mass=exceptional_mass,
        entropy_deficit=deficit,
        deficit_per_digit=deficit / order,
        convexity_upper_bound=convexity_bound,
        normalized_l2_energy=normalized_l2,
        old_collision_ratio=collision_ratio,
        zero_word_mass=zero_mass,
    )


def write_csv(results: list[StageResult], output: TextIO) -> None:
    names = [field.name for field in fields(StageResult)]
    writer = csv.DictWriter(output, fieldnames=names, lineterminator="\n")
    writer.writeheader()
    writer.writerows(asdict(result) for result in results)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-order", type=int, default=5)
    parser.add_argument("--format", choices=("csv", "json"), default="csv")
    args = parser.parse_args()
    if not 2 <= args.max_order <= 6:
        raise SystemExit("use 2 <= --max-order <= 6; the stage has 10^k cells")

    results = [
        verify_stage(order, mode)
        for order in range(2, args.max_order + 1)
        for mode in ("sqrt", "k")
    ]
    if args.format == "json":
        json.dump([asdict(result) for result in results], sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        write_csv(results, sys.stdout)


if __name__ == "__main__":
    main()
