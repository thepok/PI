#!/usr/bin/env python3
"""Exact finite replay for T75 synthetic label systems; never reads pi digits."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def sample_length(n: int) -> int:
    return 10 ** (n // 2)


def max_short_lag(n: int) -> int:
    length = sample_length(n)
    return min(max(n - 1, 0), max(length - 1, 0))


def windows(length: int, h: int) -> list[list[int]]:
    if h == 0:
        return [[] for _ in range(length)]
    return [
        list(range(k * h, min(length, (k + 2) * h)))
        for k in range(length)
    ]


def a_loc(labels: list[int], h: int) -> int:
    total = 0
    for window in windows(len(labels), h):
        for multiplicity in Counter(labels[i] for i in window).values():
            total += multiplicity * (multiplicity - 1)
    return total


def cyclic_adjacent(q: int, a: int, b: int) -> bool:
    return (
        b == a
        or b + 1 == a
        or a + 1 == b
        or (a == 0 and b + 1 == q)
        or (b == 0 and a + 1 == q)
    )


def w5(n: int, labels: list[int]) -> int:
    length = sample_length(n)
    assert len(labels) == length
    q = 10**n
    return 2 * sum(
        1
        for r in range(1, length)
        if r < n
        for j in range(length - r)
        if cyclic_adjacent(q, labels[j], labels[j + r])
    )


def equality_load(labels: list[int]) -> int:
    return sum(m * m for m in Counter(labels).values())


def verify_window_combinatorics() -> dict[str, int]:
    cases = 0
    pairs = 0
    for length in range(1, 31):
        for h in range(length + 1):
            ws = windows(length, h)
            assert sum(map(len, ws)) <= 2 * length
            for i in range(length):
                assert sum(i in window for window in ws) <= 2
            if h > 0:
                for i in range(length):
                    for j in range(i + 1, min(length, i + h + 1)):
                        k = i // h
                        assert i in ws[k] and j in ws[k]
                        pairs += 1
            cases += 1
    return {"window_parameter_cases": cases, "covered_pairs": pairs}


def verify_charging_and_inverse() -> dict[str, int]:
    patterns = 0
    thresholds = 0
    for n in range(1, 6):
        length = sample_length(n)
        q = 10**n
        candidates = [
            [0] * length,
            list(range(length)),
            [i % min(q, 7) for i in range(length)],
            [(i * i + 3 * i + 7) % q for i in range(length)],
            [((i // max(1, n)) * 3) % q for i in range(length)],
        ]
        for labels in candidates:
            h = max_short_lag(n)
            local = a_loc(labels, h)
            weight = w5(n, labels)
            assert weight <= 6 * length + 3 * local
            maximum = max(
                (max(Counter(labels[i] for i in window).values(), default=0)
                 for window in windows(length, h)),
                default=0,
            )
            assert local <= 2 * maximum * length
            for k in range(maximum + 2):
                if 2 * k * length < local:
                    assert maximum > k
                thresholds += 1
            patterns += 1
    return {"label_patterns": patterns, "inverse_thresholds": thresholds}


def verify_separating_families() -> dict[str, object]:
    constant_rows = []
    injective_rows = []
    for n in range(2, 9):
        length = sample_length(n)
        h = max_short_lag(n)
        ws = windows(length, h)

        constant = [0] * length
        local_constant = a_loc(constant, h)
        exact_formula = sum(len(window) * (len(window) - 1) for window in ws)
        e3_constant = 3 * equality_load(constant)
        assert local_constant == exact_formula
        assert local_constant <= 4 * h * length
        assert e3_constant == 3 * length * length
        constant_rows.append(
            {
                "n": n,
                "L": length,
                "h": h,
                "A_loc": local_constant,
                "E3": e3_constant,
            }
        )

        injective = list(range(length))
        local_injective = a_loc(injective, h)
        w5_injective = w5(n, injective)
        assert local_injective == 0
        assert w5_injective == 2 * (length - 1)
        injective_rows.append(
            {
                "n": n,
                "L": length,
                "A_loc": local_injective,
                "W5": w5_injective,
            }
        )
    return {
        "constant_family": constant_rows,
        "injective_family": injective_rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", type=Path, required=True)
    args = parser.parse_args()
    result = {
        "classification": "experiment on synthetic finite label systems only",
        "pi_digits_read": 0,
        "window_checks": verify_window_combinatorics(),
        "charging_checks": verify_charging_and_inverse(),
        "separating_families": verify_separating_families(),
        "nonclaims": ["PiALocLinearBound", "C7", "C2", "C1"],
    }
    args.write.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
