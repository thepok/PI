#!/usr/bin/env python3
"""Exact finite replay for T96's displayed arithmetic and factor count."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


PINNED_SHA256 = "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
SOURCE = "pi-positive-decimal-factor-entropy.txt"


def least_split(width: int, m: int) -> tuple[int, int]:
    q = 1
    while width + m > 3 * (4**q):
        q += 1
    return q, 4**q


def prefix_digits(n: int, q: int, e: int) -> str:
    numerator = sum(n * (10 ** (e - 4**r)) for r in range(1, q + 1))
    residue = numerator % (10**e)
    return f"{residue:0{e}d}"


def padded_block_factors(block: str, m: int) -> set[str]:
    padded = "0" * (m - 1) + block + "0" * (m - 1)
    factors = {
        padded[start : start + m]
        for start in range(len(block) + m - 1)
    }
    factors.add("0" * m)
    return factors


def structural_factors(j: int, m: int) -> tuple[set[str], dict[str, int]]:
    n = 16**j
    block = str(n)
    width = len(block)
    q, e = least_split(width, m)

    assert 1 <= width <= 2 * j + 1
    assert width + m <= 3 * e
    if q > 1:
        assert width + m > 3 * (4 ** (q - 1))
    assert e <= 2 * (width + m)
    assert 3 * e - width >= m
    # Exact integer form of 2*10^(width-4E) < 10^(-E).
    assert 2 * (10**width) < 10 ** (3 * e)

    prefix = prefix_digits(n, q, e)
    prefix_factors = {
        (prefix + "0" * (m - 1))[start : start + m]
        for start in range(e)
    }
    tail_factors = padded_block_factors(block, m)
    factors = prefix_factors | tail_factors
    assert len(prefix_factors) <= e
    assert len(tail_factors) <= width + m
    assert len(factors) <= e + width + m
    assert len(factors) <= 3 * (width + m)
    return factors, {"width": width, "q": q, "e": e}


def materialized_factors(j: int, m: int) -> set[str]:
    """Build the prefix and first two tail blocks at their exact positions."""
    n = 16**j
    block = str(n)
    width = len(block)
    q, e = least_split(width, m)
    last_q = q + 2
    end = 4**last_q
    digits = ["0"] * end
    prefix = prefix_digits(n, q, e)
    digits[:e] = prefix

    previous_end = e
    for tail_q in range(q + 1, last_q + 1):
        block_end = 4**tail_q
        start = block_end - width
        assert start - previous_end >= m
        assert all(digit == "0" for digit in digits[start:block_end])
        digits[start:block_end] = block
        previous_end = block_end

    # Check the finite rational identity after clearing the denominator.
    partial_numerator = sum(
        n * (10 ** (end - 4**term_q)) for term_q in range(1, last_q + 1)
    )
    displayed_numerator = int(prefix) * (10 ** (end - e)) + sum(
        n * (10 ** (end - 4**term_q))
        for term_q in range(q + 1, last_q + 1)
    )
    assert partial_numerator % (10**end) == displayed_numerator

    text = "".join(digits) + "0" * (m - 1)
    return {text[start : start + m] for start in range(end)}


def first_omitted(factors: set[str], m: int) -> str:
    for digits in itertools.product("0123456789", repeat=m):
        word = "".join(digits)
        if word not in factors:
            return word
    raise AssertionError("factor set unexpectedly contains every word")


def replay() -> dict[str, object]:
    source_hash = hashlib.sha256(Path(SOURCE).read_bytes()).hexdigest()
    assert source_hash == PINNED_SHA256

    base_left = 40 * (4**5)
    base_right = 10**5
    assert base_left == 40960
    assert base_right == 100000
    assert base_left < base_right
    assert 4 < 10

    rows = []
    first_word = None
    false_shortcut = {"m": 5, "j": 32, "width": len(str(16**32)), "R_plus_1": 33}
    assert false_shortcut["width"] == 39
    assert false_shortcut["width"] > false_shortcut["R_plus_1"]

    for m in range(5, 9):
        r = 2**m
        assert m + 1 <= r
        assert r + 1 <= 2 * r
        factors: set[str] = set()
        width_sum = 0
        max_e = 0
        min_zero_gap = None
        for j in range(r + 1):
            level_factors, data = structural_factors(j, m)
            assert materialized_factors(j, m) == level_factors
            factors.update(level_factors)
            width_sum += data["width"]
            max_e = max(max_e, data["e"])
            zero_gap = 3 * data["e"] - data["width"]
            min_zero_gap = zero_gap if min_zero_gap is None else min(min_zero_gap, zero_gap)

        analytical = 3 * (r + 1) * (r + m + 1)
        requested = 40 * (4**m)
        all_words = 10**m
        assert width_sum <= (r + 1) ** 2
        assert len(factors) <= analytical
        assert analytical <= 12 * r * r
        assert 12 * r * r <= requested
        assert requested < all_words
        if m == 5:
            first_word = first_omitted(factors, m)
            assert first_word not in factors
        rows.append(
            {
                "m": m,
                "R": r,
                "actual_structural_union": len(factors),
                "analytical_bound": analytical,
                "requested_bound": requested,
                "all_words": all_words,
                "max_prefix_length": max_e,
                "materialized_levels": r + 1,
                "minimum_zero_gap": min_zero_gap,
            }
        )

    return {
        "canonical_sha256": source_hash,
        "finite_base": {"m": 5, "left": base_left, "right": base_right},
        "induction_multipliers": {"left": 4, "right": 10},
        "false_shortcut_witness": false_shortcut,
        "checked_range": {"m_min": 5, "m_max": 8},
        "rows": rows,
        "first_omitted_word_m5": first_word,
        "status": "all exact checks passed",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    result = replay()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.verify is not None:
        expected = args.verify.read_text(encoding="ascii")
        if rendered != expected:
            raise SystemExit("replay output differs from expected output")
    print(rendered, end="")


if __name__ == "__main__":
    main()
