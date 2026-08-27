#!/usr/bin/env python3
"""Exact replay for the T50 Fibonacci two-block semicircle classification."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable


EXPECTED_STATEMENT_SHA256 = (
    "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
)
SYMBOLS = ("A", "B", "C")
FACTORS = {"A": "00", "B": "01", "C": "10"}


@dataclass(frozen=True)
class Affine:
    """The exact real expression q + r*zeta."""

    q: Fraction
    r: Fraction

    def __add__(self, other: "Affine") -> "Affine":
        return Affine(self.q + other.q, self.r + other.r)

    def __sub__(self, other: "Affine") -> "Affine":
        return Affine(self.q - other.q, self.r - other.r)


def rat(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def affine_json(value: Affine) -> dict[str, dict[str, int]]:
    return {"q": rat(value.q), "r": rat(value.r)}


def affine_bounds(value: Affine, lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    if value.r >= 0:
        return value.q + value.r * lo, value.q + value.r * hi
    return value.q + value.r * hi, value.q + value.r * lo


def fibonacci_prefix(length: int) -> str:
    word = "0"
    while len(word) < length:
        word = "".join("01" if bit == "0" else "0" for bit in word)
    return word[:length]


def block_word(binary: str) -> str:
    inverse = {factor: symbol for symbol, factor in FACTORS.items()}
    return "".join(inverse[binary[i : i + 2]] for i in range(len(binary) - 1))


def prefix_affine(symbol_word: str, digits: dict[str, int]) -> Affine:
    """Decimal value of symbol_word followed by Z, where zeta=0.Z."""
    integer = 0
    for symbol in symbol_word:
        integer = 10 * integer + digits[symbol]
    scale = 10 ** len(symbol_word)
    return Affine(Fraction(integer, scale), Fraction(1, scale))


def endpoint_expressions(digits: dict[str, int]) -> dict[str, Affine]:
    return {
        "AZ": prefix_affine("A", digits),
        "ABCZ": prefix_affine("ABC", digits),
        "BCAZ": prefix_affine("BCA", digits),
        "BCZ": prefix_affine("BC", digits),
        "CAZ": prefix_affine("CA", digits),
        "CZ": prefix_affine("C", digits),
    }


def cylinder_extrema(digits: dict[str, int]) -> dict[str, dict[str, str]]:
    if digits["A"] < digits["B"]:
        return {
            "A": {"min": "AZ", "max": "ABCZ"},
            "B": {"min": "BCAZ", "max": "BCZ"},
            "C": {"min": "CAZ", "max": "CZ"},
        }
    return {
        "A": {"min": "ABCZ", "max": "AZ"},
        "B": {"min": "BCZ", "max": "BCAZ"},
        "C": {"min": "CZ", "max": "CAZ"},
    }


def order_name(digits: dict[str, int]) -> str:
    return "<".join(sorted(SYMBOLS, key=digits.__getitem__))


def certify_case(values: tuple[int, int, int]) -> dict[str, object]:
    digits = dict(zip(SYMBOLS, values))
    endpoints = endpoint_expressions(digits)
    extrema = cylinder_extrema(digits)
    ordered = sorted(SYMBOLS, key=digits.__getitem__)

    gaps: list[tuple[str, Affine]] = []
    for left, right in zip(ordered, ordered[1:]):
        gap = endpoints[extrema[right]["min"]] - endpoints[extrema[left]["max"]]
        gaps.append((left + "->" + right, gap))
    exterior = (
        Affine(Fraction(1), Fraction(0))
        - endpoints[extrema[ordered[-1]]["max"]]
        + endpoints[extrema[ordered[0]]["min"]]
    )
    gaps.append((ordered[-1] + "->" + ordered[0] + " (exterior)", exterior))

    minimum = min(values)
    maximum = max(values)
    # Z=P(f) begins in B. Bound every later coded digit between minimum and maximum.
    zeta_lo = Fraction(digits["B"], 10) + Fraction(minimum, 90)
    zeta_hi = Fraction(digits["B"], 10) + Fraction(maximum, 90)
    internal_bound = Fraction(maximum - minimum, 90)

    gap_records = []
    bounds = []
    for name, expression in gaps:
        lo, hi = affine_bounds(expression, zeta_lo, zeta_hi)
        assert 0 <= lo <= hi
        bounds.append((lo, hi))
        gap_records.append(
            {
                "name": name,
                "expression": affine_json(expression),
                "lower": rat(lo),
                "upper": rat(hi),
            }
        )

    best_lower_index = max(range(3), key=lambda i: bounds[i][0])
    best_upper = max(hi for _, hi in bounds)
    if bounds[best_lower_index][0] >= Fraction(1, 2):
        verdict = "contained"
        decisive = {
            "kind": "certified_gap_at_least_half",
            "gap_index": best_lower_index,
            "lower": rat(bounds[best_lower_index][0]),
            "margin_over_half": rat(bounds[best_lower_index][0] - Fraction(1, 2)),
        }
    elif best_upper < Fraction(1, 2) and internal_bound < Fraction(1, 2):
        verdict = "not_contained"
        decisive = {
            "kind": "all_gaps_strictly_below_half",
            "top_level_upper": rat(best_upper),
            "internal_upper": rat(internal_bound),
            "margin_below_half": rat(
                Fraction(1, 2) - max(best_upper, internal_bound)
            ),
        }
    else:
        raise AssertionError(f"unresolved coding {values}: {bounds}")

    return {
        "coding": {symbol: digits[symbol] for symbol in SYMBOLS},
        "relative_order": order_name(digits),
        "zeta_bounds": {"lower": rat(zeta_lo), "upper": rat(zeta_hi)},
        "cylinder_extrema": extrema,
        "top_level_gaps": gap_records,
        "internal_gap_upper_bound": rat(internal_bound),
        "verdict": verdict,
        "decisive_inequality": decisive,
    }


def finite_convention_checks() -> dict[str, object]:
    f = fibonacci_prefix(80)
    assert f.startswith("010010100100101")
    assert {f[i : i + 2] for i in range(len(f) - 1)} == set(FACTORS.values())
    z = block_word(f)
    assert z.startswith("BCABCBCA")

    # These checks validate finite prefixes of all six endpoint identities used
    # by the proof; the note proves the corresponding infinite identities.
    endpoint_binary = {
        "0f": "0" + f,
        "001f": "001" + f,
        "010f": "010" + f,
        "01f": "01" + f,
        "10f": "10" + f,
        "1f": "1" + f,
    }
    expected = {
        "0f": "A" + z,
        "001f": "ABC" + z,
        "010f": "BCA" + z,
        "01f": "BC" + z,
        "10f": "CA" + z,
        "1f": "C" + z,
    }
    for name in endpoint_binary:
        actual = block_word(endpoint_binary[name])
        assert actual[:60] == expected[name][:60]

    return {
        "fibonacci_prefix": f[:32],
        "two_block_prefix": z[:31],
        "factor_language_length_2": sorted(FACTORS.values()),
        "endpoint_prefix_check_length": 60,
    }


def build_certificate() -> dict[str, object]:
    cases = [certify_case(values) for values in itertools.permutations(range(10), 3)]
    assert len(cases) == 720
    assert len({tuple(case["coding"].values()) for case in cases}) == 720

    by_order = {}
    equality_cases = 0
    for order in itertools.permutations(SYMBOLS):
        name = "<".join(order)
        group = [case for case in cases if case["relative_order"] == name]
        contained = sum(case["verdict"] == "contained" for case in group)
        not_contained = len(group) - contained
        boundary = sum(
            case["verdict"] == "contained"
            and case["decisive_inequality"]["margin_over_half"] == rat(Fraction(0))
            for case in group
        )
        equality_cases += boundary
        by_order[name] = {
            "total": len(group),
            "contained": contained,
            "not_contained": not_contained,
            "boundary_equal_half": boundary,
        }

    contained_total = sum(case["verdict"] == "contained" for case in cases)
    summary = {
        "total": len(cases),
        "contained": contained_total,
        "not_contained": len(cases) - contained_total,
        "boundary_equal_half": equality_cases,
        "by_relative_order": by_order,
    }
    assert summary == {
        "total": 720,
        "contained": 520,
        "not_contained": 200,
        "boundary_equal_half": 60,
        "by_relative_order": {
            "A<B<C": {"total": 120, "contained": 90, "not_contained": 30, "boundary_equal_half": 20},
            "A<C<B": {"total": 120, "contained": 80, "not_contained": 40, "boundary_equal_half": 0},
            "B<A<C": {"total": 120, "contained": 90, "not_contained": 30, "boundary_equal_half": 10},
            "B<C<A": {"total": 120, "contained": 80, "not_contained": 40, "boundary_equal_half": 0},
            "C<A<B": {"total": 120, "contained": 90, "not_contained": 30, "boundary_equal_half": 10},
            "C<B<A": {"total": 120, "contained": 90, "not_contained": 30, "boundary_equal_half": 20},
        },
    }

    return {
        "schema_version": 1,
        "item": "T50",
        "scope": "non-pi Fibonacci two-block sibling classification",
        "canonical_statement_sha256": EXPECTED_STATEMENT_SHA256,
        "coding_convention": {
            "A": "00",
            "B": "01",
            "C": "10",
            "digit_tuple_order": ["A", "B", "C"],
            "leading_zeroes_retained": True,
            "overlapping_blocks": True,
            "closed_semicircle_length": rat(Fraction(1, 2)),
        },
        "finite_convention_checks": finite_convention_checks(),
        "endpoint_words": {
            "A": {"left_intercept": "AZ", "right_intercept": "ABCZ"},
            "B": {"left_intercept": "BCAZ", "right_intercept": "BCZ"},
            "C": {"left_intercept": "CAZ", "right_intercept": "CZ"},
            "Z": "overlapping two-block coding of f, beginning BCABCBCA...",
        },
        "summary": summary,
        "cases": cases,
    }


def verify_statement(path: Path) -> None:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != EXPECTED_STATEMENT_SHA256:
        raise SystemExit(f"canonical statement hash mismatch: {digest}")


def compact_summary(certificate: dict[str, object]) -> str:
    summary = certificate["summary"]
    return json.dumps(summary, sort_keys=True, separators=(",", ":"))


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", type=Path, help="write the generated certificate JSON")
    action.add_argument("--verify", type=Path, help="compare a certificate with exact recomputation")
    parser.add_argument(
        "--statement",
        type=Path,
        default=Path(__file__).with_name("pi-positive-decimal-factor-entropy.txt"),
    )
    args = parser.parse_args(argv)

    verify_statement(args.statement)
    generated = build_certificate()
    if args.write:
        args.write.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.write}")
    elif args.verify:
        supplied = json.loads(args.verify.read_text())
        if supplied != generated:
            raise SystemExit("certificate mismatch")
        print("certificate replay: PASS")
    print(compact_summary(generated))


if __name__ == "__main__":
    main()
