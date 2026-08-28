#!/usr/bin/env python3
"""Exact diagnostics for the uniform-integrability frontier.

For the decimal orbit x_n = {10^n pi}, the q = 10^k partition cell
containing x_n is exactly the k-digit word beginning at fractional digit n.
This program counts those words on a finite consecutive block and reports:

* exact cell occupancies;
* the exact collision sum sum_a n(a)^2;
* the normalized second moment q * sum_a n(a)^2 / L^2;
* for each requested M, the exact tail mass

      (1/L) * sum_{a : n(a) > M L / q} n(a).

The tail mass is the finite observable occurring in
knowledge/pi/archive/results/intermediate/20260824-uniform-integrability-haar-frontier.md.
All threshold comparisons use
integer arithmetic.  The output is a reproducible finite certificate, not a
proof of decimal richness or of the asymptotic uniform-integrability premise.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


SCHEMA = "pi-ui-tail-diagnostic/v1"


class DiagnosticError(ValueError):
    """Raised for invalid input or inconsistent parameters."""


@dataclass(frozen=True)
class ParsedDigits:
    fractional: str
    raw_sha256: str
    fractional_sha256: str


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_fractional_digits(raw: bytes) -> ParsedDigits:
    """Parse a text digit source.

    Whitespace, underscores, and commas are ignored.  If a decimal point is
    present, only the digits after the point are used.  Otherwise every digit
    is treated as a fractional digit.  No sign, exponent, or other character
    is accepted.
    """

    raw_hash = _sha256(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise DiagnosticError("digit source must be ASCII text") from exc

    compact = "".join(ch for ch in text if not ch.isspace() and ch not in "_,")
    if compact.count(".") > 1:
        raise DiagnosticError("digit source contains more than one decimal point")

    if "." in compact:
        integer, fractional = compact.split(".", 1)
        if not integer or not integer.isdigit():
            raise DiagnosticError("invalid integer part before decimal point")
    else:
        fractional = compact

    if not fractional:
        raise DiagnosticError("no fractional digits found")
    if not fractional.isdigit():
        bad = sorted(set(ch for ch in fractional if not ch.isdigit()))
        raise DiagnosticError(f"invalid non-digit characters: {bad!r}")

    fractional_bytes = fractional.encode("ascii")
    return ParsedDigits(
        fractional=fractional,
        raw_sha256=raw_hash,
        fractional_sha256=_sha256(fractional_bytes),
    )


def parse_positive_fraction(text: str) -> Fraction:
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(f"invalid rational threshold {text!r}") from exc
    if value <= 0:
        raise argparse.ArgumentTypeError("thresholds must be positive")
    return value


def count_cells(digits: str, start: int, length: int, word_length: int) -> Counter[str]:
    if start < 0:
        raise DiagnosticError("start must be nonnegative")
    if length <= 0:
        raise DiagnosticError("length must be positive")
    if word_length <= 0:
        raise DiagnosticError("word length must be positive")

    required = start + length + word_length - 1
    if required > len(digits):
        raise DiagnosticError(
            "not enough fractional digits: "
            f"need {required}, have {len(digits)}"
        )

    return Counter(
        digits[n : n + word_length]
        for n in range(start, start + length)
    )


def fraction_record(value: Fraction) -> dict[str, object]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": format(float(value), ".17g"),
    }


def threshold_record(
    counts: Iterable[int], *, threshold: Fraction, length: int, q: int
) -> dict[str, object]:
    """Return an exact UI-tail record.

    A count n is in the tail precisely when

        n > M * L / q.

    For M = p/r, this is tested as n*q*r > p*L.
    """

    p = threshold.numerator
    r = threshold.denominator
    tail_counts = [n for n in counts if n * q * r > p * length]
    visits = sum(tail_counts)
    cells = len(tail_counts)
    mass = Fraction(visits, length)

    return {
        "M": str(threshold),
        "strict_tail_test": "n*q*M.denominator > M.numerator*L",
        "tail_cells": cells,
        "tail_visits": visits,
        "tail_mass": fraction_record(mass),
    }


def build_report(
    parsed: ParsedDigits,
    *,
    source: str,
    start: int,
    length: int,
    word_length: int,
    thresholds: Sequence[Fraction],
    include_counts: bool,
) -> dict[str, object]:
    counts = count_cells(parsed.fractional, start, length, word_length)
    q = 10**word_length
    values = list(counts.values())
    collision_sum = sum(n * n for n in values)
    normalized_l2 = Fraction(q * collision_sum, length * length)
    coverage = Fraction(len(counts), q)

    report: dict[str, object] = {
        "schema": SCHEMA,
        "source": source,
        "source_raw_sha256": parsed.raw_sha256,
        "parsed_fractional_digits_sha256": parsed.fractional_sha256,
        "parameters": {
            "start_zero_based": start,
            "block_length": length,
            "word_length": word_length,
            "q": q,
            "required_fractional_digits": start + length + word_length - 1,
        },
        "occupancy": {
            "distinct_cells": len(counts),
            "empty_cells": q - len(counts),
            "coverage_fraction": fraction_record(coverage),
            "maximum_count": max(values),
            "minimum_positive_count": min(values),
        },
        "collision": {
            "sum_count_squared": collision_sum,
            "normalized_second_moment_q_sum_n2_over_L2": fraction_record(normalized_l2),
        },
        "uniform_integrability_tails": [
            threshold_record(values, threshold=M, length=length, q=q)
            for M in thresholds
        ],
        "claim_boundary": (
            "This is an exact finite diagnostic. It does not prove V1, "
            "equidistribution, or the asymptotic UI condition."
        ),
    }

    if include_counts:
        report["counts"] = dict(sorted(counts.items()))

    return report


def self_test() -> None:
    """Exercise parser, exact thresholds, and the integer separator family."""

    parsed = parse_fractional_digits(b"3.0123456789012345\n")
    assert parsed.fractional == "0123456789012345"

    counts = count_cells(parsed.fractional, start=0, length=10, word_length=1)
    assert len(counts) == 10
    assert all(counts[str(d)] == 1 for d in range(10))

    # Exact strict comparison: mean occupancy is one.
    record = threshold_record(counts.values(), threshold=Fraction(1), length=10, q=10)
    assert record["tail_visits"] == 0

    # Integer separator from uniform_integrability_frontier.md.
    for j in range(2, 50):
        q = j**3
        length = j * (q - 1)
        values = [q - 1] + [j - 1] * (q - 1)
        assert sum(values) == length

        spike_density = Fraction(q * values[0], length)
        base_density = Fraction(q * values[1], length)
        assert spike_density == j**2
        assert base_density < 1

        normalized_l2 = Fraction(q * sum(n * n for n in values), length * length)
        assert normalized_l2 >= j

        M = Fraction(j * j - 1)
        tail = threshold_record(values, threshold=M, length=length, q=q)
        assert Fraction(
            int(tail["tail_mass"]["numerator"]),
            int(tail["tail_mass"]["denominator"]),
        ) == Fraction(1, j)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Compute exact occupancy tails for decimal-orbit blocks."
    )
    parser.add_argument(
        "digit_file",
        type=Path,
        nargs="?",
        help=(
            "ASCII digit source. With a decimal point, only its fractional "
            "part is used; otherwise all digits are treated as fractional."
        ),
    )
    parser.add_argument("--start", type=int, default=0, help="zero-based orbit/block start")
    parser.add_argument("--length", type=int, help="number of consecutive orbit points")
    parser.add_argument(
        "--word-length",
        type=int,
        help="decimal cell depth k, so q=10^k",
    )
    parser.add_argument(
        "--threshold",
        dest="thresholds",
        action="append",
        type=parse_positive_fraction,
        help="positive M; repeat for several exact rational thresholds",
    )
    parser.add_argument(
        "--include-counts",
        action="store_true",
        help="include the complete nonzero cell-count dictionary",
    )
    parser.add_argument("--output", type=Path, help="write JSON here instead of stdout")
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run internal exact-arithmetic tests and exit",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = make_parser()
    args = parser.parse_args(argv)

    if args.self_test:
        self_test()
        print("self-test: ok")
        return 0

    if args.digit_file is None:
        parser.error("digit_file is required unless --self-test is used")
    if args.length is None:
        parser.error("--length is required")
    if args.word_length is None:
        parser.error("--word-length is required")

    thresholds = args.thresholds or [
        Fraction(2),
        Fraction(4),
        Fraction(8),
        Fraction(16),
    ]

    try:
        raw = args.digit_file.read_bytes()
        parsed = parse_fractional_digits(raw)
        report = build_report(
            parsed,
            source=str(args.digit_file),
            start=args.start,
            length=args.length,
            word_length=args.word_length,
            thresholds=thresholds,
            include_counts=args.include_counts,
        )
    except (OSError, DiagnosticError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(encoded)
    else:
        try:
            args.output.write_text(encoded, encoding="utf-8")
        except OSError as exc:
            print(f"error: cannot write {args.output}: {exc}", file=sys.stderr)
            return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
