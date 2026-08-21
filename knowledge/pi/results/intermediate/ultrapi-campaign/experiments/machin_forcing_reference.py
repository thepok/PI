#!/usr/bin/env python3
"""Small independent exact-rational reference for ultrapi equation (11w).

This intentionally uses only Fraction and direct powers.  It is slower than
the GMP production run, but its different implementation is useful for
checking the retained N=0,...,20 exact integers.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from fractions import Fraction
from pathlib import Path


def forcing_row(n: int) -> dict[str, int]:
    terms: list[Fraction] = []
    scale = 10 ** (n + 1)
    for j in range(6):
        a = 12 * n + 5 + 2 * j
        sign = -1 if j % 2 else 1
        terms.append(Fraction(sign * 16 * scale, a * 5**a))
        b = a + 2
        terms.append(Fraction(sign * 4 * scale, b * 239**b))

    lcd = 1
    for term in terms:
        lcd = math.lcm(lcd, term.denominator)
    integer_sum = sum(
        term.numerator * (lcd // term.denominator) for term in terms
    )
    delta = Fraction(integer_sum, lcd)
    cancellation = math.gcd(abs(integer_sum), lcd)
    assert delta.numerator == integer_sum // cancellation
    assert delta.denominator == lcd // cancellation
    return {
        "N": n,
        "T": integer_sum,
        "Lambda": lcd,
        "g": cancellation,
        "delta_num": delta.numerator,
        "delta_den": delta.denominator,
    }


def read_gmp_small_exact(path: Path) -> list[dict[str, int]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return [
            {key: int(value) for key, value in row.items()}
            for row in csv.DictReader(handle, delimiter="\t")
        ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=20)
    parser.add_argument("--gmp-small-exact", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    rows = [forcing_row(n) for n in range(args.max_n + 1)]
    comparison = None
    if args.gmp_small_exact:
        retained = read_gmp_small_exact(args.gmp_small_exact)
        comparison = {
            "retained_rows": len(retained),
            "reference_rows": len(rows),
            "exact_match": retained == rows[: len(retained)],
        }
        if not comparison["exact_match"]:
            raise SystemExit("GMP/reference mismatch")

    result = {
        "claim_status": "experiment",
        "implementation": "Python Fraction direct twelve-term sum",
        "max_n": args.max_n,
        "comparison": comparison,
        "rows": rows,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
