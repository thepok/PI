#!/usr/bin/env python3
"""Replay finite T58 arithmetic checks and the abstract fixed-phase obstruction."""

from __future__ import annotations

import argparse
import cmath
import json
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path


CANONICAL_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"


def ten_reduction(h: int) -> tuple[int, int]:
    assert h > 0
    a = 0
    while h % 10 == 0:
        h //= 10
        a += 1
    return a, h


def repunit_factor(r: int) -> int:
    return 10**r - 1


def phi(h: int, j: int, r: int) -> int:
    return h * 10**j * repunit_factor(r)


def audit_scale(n: int) -> dict[str, object]:
    length = 10 ** (n // 2)
    bandwidth = 10**n // 2
    rectangle = [
        (r, j)
        for r in range(1, n)
        for j in range(length - r)
    ]

    fixed_h_injective = True
    for h in range(1, bandwidth):
        seen: dict[int, tuple[int, int]] = {}
        for r, j in rectangle:
            value = phi(h, j, r)
            if value in seen and seen[value] != (r, j):
                fixed_h_injective = False
            seen[value] = (r, j)

    fibers: dict[int, list[tuple[int, int, int, int, int]]] = defaultdict(list)
    reduced_keys: dict[tuple[int, int], int] = {}
    diagonal_weight = Fraction(0)
    for h in range(1, bandwidth):
        a, u = ten_reduction(h)
        weight = Fraction(bandwidth - h, bandwidth)
        for r, j in rectangle:
            value = phi(h, j, r)
            key = (a + j, u * repunit_factor(r))
            old_value = reduced_keys.setdefault(key, value)
            assert old_value == value
            fibers[value].append((h, j, r, a, u))
            diagonal_weight += weight * weight

    collision_criterion = True
    gcd_parametrization = True
    off_diagonal_weight = Fraction(0)
    grouped_second_moment = Fraction(0)
    for records in fibers.values():
        fiber_weight = Fraction(0)
        for h, _j, _r, _a, _u in records:
            fiber_weight += Fraction(bandwidth - h, bandwidth)
        grouped_second_moment += fiber_weight * fiber_weight
        for index, left in enumerate(records):
            h1, j1, r1, a1, u1 = left
            w1 = Fraction(bandwidth - h1, bandwidth)
            for right in records[index + 1 :]:
                h2, j2, r2, a2, u2 = right
                w2 = Fraction(bandwidth - h2, bandwidth)
                off_diagonal_weight += 2 * w1 * w2
                if not (a1 + j1 == a2 + j2 and u1 * repunit_factor(r1) == u2 * repunit_factor(r2)):
                    collision_criterion = False
                g = math.gcd(repunit_factor(r1), repunit_factor(r2))
                left_step = repunit_factor(r2) // g
                right_step = repunit_factor(r1) // g
                if u1 % left_step or u2 % right_step:
                    gcd_parametrization = False
                else:
                    if u1 // left_step != u2 // right_step:
                        gcd_parametrization = False

    max_multiplicity = max((len(records) for records in fibers.values()), default=0)
    multiplicity_bound = n * (n - 1)
    assert grouped_second_moment == diagonal_weight + off_diagonal_weight
    assert max_multiplicity <= multiplicity_bound

    return {
        "n": n,
        "L_n": length,
        "H_n": bandwidth,
        "frequency_range": [1, bandwidth - 1],
        "rectangle_size": len(rectangle),
        "rectangle_first_last": [list(rectangle[0]), list(rectangle[-1])],
        "triple_count": (bandwidth - 1) * len(rectangle),
        "fixed_h_injective": fixed_h_injective,
        "collision_criterion": collision_criterion,
        "gcd_parametrization": gcd_parametrization,
        "max_multiplicity": max_multiplicity,
        "proved_bound_checked": multiplicity_bound,
        "second_moment_identity": grouped_second_moment == diagonal_weight + off_diagonal_weight,
        "diagonal_weight": str(diagonal_weight),
        "off_diagonal_weight": str(off_diagonal_weight),
        "total_collision_weight": str(grouped_second_moment),
    }


def obstruction(m: int) -> dict[str, object]:
    # Distinct frequencies k with triangular weights.  The coefficients are
    # phase-adapted so all terms equal their positive weights at alpha = pi.
    weights = [Fraction(m + 1 - k, m + 1) for k in range(1, m + 1)]
    average_l2 = sum((weight * weight for weight in weights), Fraction(0))
    fixed_value_sq = sum(weights, Fraction(0)) ** 2
    numerical = sum(
        float(weight)
        * cmath.exp(-2j * math.pi * k * math.pi)
        * cmath.exp(2j * math.pi * k * math.pi)
        for k, weight in enumerate(weights, 1)
    )
    return {
        "m": m,
        "distinct_frequencies": list(range(1, m + 1)),
        "triangular_weight_sum": str(sum(weights, Fraction(0))),
        "phase_average_L2": str(average_l2),
        "fixed_pi_value_squared": str(fixed_value_sq),
        "fixed_to_average_ratio": str(fixed_value_sq / average_l2),
        "numerical_alignment_error": abs(numerical - float(sum(weights, Fraction(0)))),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    result = {
        "label": "experiment",
        "canonical_statement_sha256": CANONICAL_SHA256,
        "finite_arithmetic_checks": [audit_scale(n) for n in (2, 3)],
        "abstract_fixed_phase_obstruction": [obstruction(m) for m in (4, 8, 16, 32)],
        "scope": {
            "proves_fixed_pi_estimate": False,
            "proves_T56_predicate": False,
            "proves_C7": False,
            "proves_C2": False,
            "proves_C1": False,
        },
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(text, encoding="ascii")
    print(text, end="")


if __name__ == "__main__":
    main()
