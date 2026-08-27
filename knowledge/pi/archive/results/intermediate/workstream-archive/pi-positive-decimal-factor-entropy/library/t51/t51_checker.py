#!/usr/bin/env python3
"""Exact replay for the T51 Fibonacci two-block sibling."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


EXPECTED_STATEMENT_SHA256 = (
    "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
)
SYMBOLS = ("A", "B", "C")
FACTORS = {"A": "00", "B": "01", "C": "10"}


@dataclass(frozen=True)
class Affine:
    """An exact expression q + r*zeta."""

    q: Fraction
    r: Fraction

    def __add__(self, other: "Affine") -> "Affine":
        return Affine(self.q + other.q, self.r + other.r)

    def __sub__(self, other: "Affine") -> "Affine":
        return Affine(self.q - other.q, self.r - other.r)


def rational(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def affine_record(value: Affine) -> dict[str, dict[str, int]]:
    return {"q": rational(value.q), "r": rational(value.r)}


def affine_bounds(value: Affine, lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    if value.r >= 0:
        return value.q + value.r * lo, value.q + value.r * hi
    return value.q + value.r * hi, value.q + value.r * lo


def prefix_affine(symbols: str, digits: dict[str, int]) -> Affine:
    integer = 0
    for symbol in symbols:
        integer = 10 * integer + digits[symbol]
    scale = 10 ** len(symbols)
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


def certify_case(values: tuple[int, int, int]) -> dict[str, object]:
    digits = dict(zip(SYMBOLS, values))
    endpoints = endpoint_expressions(digits)
    extrema = cylinder_extrema(digits)
    ordered = sorted(SYMBOLS, key=digits.__getitem__)

    gaps: list[tuple[str, Affine]] = []
    for left, right in zip(ordered, ordered[1:]):
        gaps.append(
            (
                f"{left}->{right}",
                endpoints[extrema[right]["min"]] - endpoints[extrema[left]["max"]],
            )
        )
    exterior = (
        Affine(Fraction(1), Fraction(0))
        - endpoints[extrema[ordered[-1]]["max"]]
        + endpoints[extrema[ordered[0]]["min"]]
    )
    gaps.append((f"{ordered[-1]}->{ordered[0]} (exterior)", exterior))

    minimum = min(values)
    maximum = max(values)
    zeta_lo = Fraction(digits["B"], 10) + Fraction(minimum, 90)
    zeta_hi = Fraction(digits["B"], 10) + Fraction(maximum, 90)
    internal_bound = Fraction(maximum - minimum, 90)

    records = []
    bounds = []
    for name, expression in gaps:
        lo, hi = affine_bounds(expression, zeta_lo, zeta_hi)
        assert 0 <= lo <= hi
        bounds.append((lo, hi))
        records.append(
            {
                "name": name,
                "expression": affine_record(expression),
                "lower": rational(lo),
                "upper": rational(hi),
            }
        )

    best_lower = max(lo for lo, _ in bounds)
    best_upper = max(hi for _, hi in bounds)
    if best_lower >= Fraction(1, 2):
        verdict = "contained"
        margin = best_lower - Fraction(1, 2)
    elif best_upper < Fraction(1, 2) and internal_bound < Fraction(1, 2):
        verdict = "strictly_not_contained"
        margin = Fraction(1, 2) - max(best_upper, internal_bound)
    else:
        raise AssertionError(f"unresolved coding {values}")

    return {
        "coding": {symbol: digits[symbol] for symbol in SYMBOLS},
        "relative_order": "<".join(ordered),
        "zeta_bounds": {"lower": rational(zeta_lo), "upper": rational(zeta_hi)},
        "cylinder_extrema": extrema,
        "top_level_gaps": records,
        "internal_gap_upper_bound": rational(internal_bound),
        "verdict": verdict,
        "strict_margin": rational(margin),
    }


def fibonacci_prefix(length: int) -> str:
    word = "0"
    while len(word) < length:
        word = "".join("01" if bit == "0" else "0" for bit in word)
    return word[:length]


def block_word(binary: str) -> str:
    inverse = {factor: symbol for symbol, factor in FACTORS.items()}
    return "".join(inverse[binary[i : i + 2]] for i in range(len(binary) - 1))


def finite_convention_checks() -> dict[str, object]:
    f = fibonacci_prefix(100)
    z = block_word(f)
    assert f.startswith("010010100100101")
    assert z.startswith("BCABCBCA")
    assert {f[i : i + 2] for i in range(len(f) - 1)} == set(FACTORS.values())
    return {
        "fibonacci_prefix": f[:32],
        "overlapping_pair_prefix": z[:31],
        "factor_language": sorted(FACTORS.values()),
    }


def average_certificate() -> dict[str, object]:
    # Arithmetic in Q[sqrt(5)], represented as constant + radical*sqrt(5).
    def qadd(x: tuple[Fraction, Fraction], y: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        return x[0] + y[0], x[1] + y[1]

    def qmul(x: tuple[Fraction, Fraction], y: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        return x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]

    def qscale(c: Fraction, x: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
        return c * x[0], c * x[1]

    one = (Fraction(1), Fraction(0))
    sqrt5 = (Fraction(0), Fraction(1))
    alpha = (Fraction(3, 2), Fraction(-1, 2))
    delta = (Fraction(-2), Fraction(1))

    # The four cell estimates in the note are 9/10, 1/2,
    # -(1+sqrt(5))/4, and -1 respectively.
    first_two_symbolic = qadd(
        qadd(qscale(Fraction(9, 10), delta), qscale(Fraction(1, 2), alpha)),
        qadd(
            qscale(Fraction(-1, 4), qmul(qadd(one, sqrt5), delta)),
            qscale(Fraction(-1), qadd(qscale(3, alpha), qscale(-1, one))),
        ),
    )
    assert first_two_symbolic == (Fraction(-53, 10), Fraction(12, 5))

    # sqrt(5) > 223/100, checked without floating point.
    sqrt5_lo = Fraction(223, 100)
    assert sqrt5_lo * sqrt5_lo < 5

    # Substitute the strict radical lower bound into the positive coefficient.
    first_two_real_lo = first_two_symbolic[0] + first_two_symbolic[1] * sqrt5_lo
    assert first_two_real_lo == Fraction(13, 250)

    # Machin plus 0 < atan(x) < x gives pi < 16/5.
    pi_upper = Fraction(16, 5)
    # This also certifies cos(pi/50)>9/10 via cos(x)>=1-x^2/2.
    x_upper = pi_upper / 50
    assert 1 - x_upper * x_upper / 2 > Fraction(9, 10)
    # And 8*pi/25 < pi/3, so cos(8*pi/25)>cos(pi/3)=1/2.
    assert Fraction(8, 25) < Fraction(1, 3)
    decimal_tail_error_upper = pi_upper / 75
    limiting_real_lower = first_two_real_lo - decimal_tail_error_upper
    assert limiting_real_lower == Fraction(7, 750)
    assert limiting_real_lower > 0

    return {
        "frequency": 1,
        "rotation_cell_prefixes": ["01", "16", "60", "61"],
        "rotation_cell_lengths": ["delta", "alpha", "delta", "3*alpha-1"],
        "first_two_symbolic_Qsqrt5": {
            "constant": rational(first_two_symbolic[0]),
            "sqrt5_coefficient": rational(first_two_symbolic[1]),
        },
        "sqrt5_strict_lower": rational(sqrt5_lo),
        "first_two_phasor_real_strict_lower": rational(first_two_real_lo),
        "pi_strict_upper": rational(pi_upper),
        "tail_error_strict_upper": rational(decimal_tail_error_upper),
        "limiting_average_real_strict_lower": rational(limiting_real_lower),
    }


def finite_range_checks() -> dict[str, object]:
    # These are convention guards only. The universal range is proved in Lean.
    for n in range(1, 31):
        m = 10**n
        h = m // 2
        admissible = [r for r in range(n + 3) if 10**r < h]
        assert admissible == list(range(n))
        d = (n + 1) // 3 + 1
        multiplicity = (m + d - 1) // d
        assert Fraction(multiplicity, m) <= Fraction(1, d) + Fraction(1, m)
    # Equal-prefix normalized coefficient is 1. With sum 1/s^2 <= 2,
    # the unequal-shell coefficient is 9/(H/M)^2 = 36 at H/M=1/2.
    half = Fraction(1, 2)
    shell_sum_upper = Fraction(2)
    unequal_coefficient = Fraction(9, 2) * shell_sum_upper / (half * half)
    energy_upper_constant = 1 + unequal_coefficient
    assert unequal_coefficient == 36
    assert energy_upper_constant == 37
    return {
        "checked_n": [1, 30],
        "universal_range_proof": "T51DecimalChainRange.lean",
        "shell_reciprocal_square_sum_upper": rational(shell_sum_upper),
        "equal_prefix_normalized_coefficient": 1,
        "unequal_prefix_normalized_coefficient": int(unequal_coefficient),
        "energy_upper_constant": int(energy_upper_constant),
    }


def build_certificate() -> dict[str, object]:
    cases = [certify_case(values) for values in itertools.permutations(range(10), 3)]
    assert len(cases) == 720
    negative = [case for case in cases if case["verdict"] == "strictly_not_contained"]
    first_index = next(i for i, case in enumerate(cases) if case["verdict"] == "strictly_not_contained")
    selected = cases[first_index]
    selected_tuple = tuple(selected["coding"][symbol] for symbol in SYMBOLS)
    assert first_index == 4
    assert selected_tuple == (0, 1, 6)
    assert len(negative) == 200
    assert len(cases) - len(negative) == 520

    selection_prefix = [
        {
            "coding": [case["coding"][symbol] for symbol in SYMBOLS],
            "verdict": case["verdict"],
            "strict_margin": case["strict_margin"],
        }
        for case in cases[: first_index + 1]
    ]

    return {
        "schema_version": 1,
        "item": "T51",
        "scope": "non-pi Fibonacci overlapping-two-block sibling",
        "canonical_statement_sha256": EXPECTED_STATEMENT_SHA256,
        "case_order": "itertools.permutations(range(10), 3) in (A,B,C) order",
        "coding_convention": {
            "A": "00",
            "B": "01",
            "C": "10",
            "overlapping": True,
            "leading_zeroes_retained": True,
        },
        "finite_convention_checks": finite_convention_checks(),
        "classification_summary": {
            "total": len(cases),
            "contained": len(cases) - len(negative),
            "strictly_not_contained": len(negative),
        },
        "selection_index_zero_based": first_index,
        "selection_prefix": selection_prefix,
        "selected_case": selected,
        "limiting_average_certificate": average_certificate(),
        "range_and_energy_checks": finite_range_checks(),
    }


def verify_statement(path: Path) -> None:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != EXPECTED_STATEMENT_SHA256:
        raise SystemExit(f"canonical statement hash mismatch: {digest}")


def main() -> None:
    parser = argparse.ArgumentParser()
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--write", type=Path)
    actions.add_argument("--verify", type=Path)
    parser.add_argument(
        "--statement",
        type=Path,
        default=Path(__file__).with_name("pi-positive-decimal-factor-entropy.txt"),
    )
    args = parser.parse_args()
    verify_statement(args.statement)
    generated = build_certificate()
    if args.write:
        args.write.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.write}")
    else:
        supplied = json.loads(args.verify.read_text())
        if supplied != generated:
            raise SystemExit("certificate mismatch")
        print("certificate replay: PASS")
    print(json.dumps(generated["classification_summary"], sort_keys=True))
    print(json.dumps(generated["selected_case"]["coding"], sort_keys=True))
    print(json.dumps(generated["limiting_average_certificate"]["limiting_average_real_strict_lower"], sort_keys=True))


if __name__ == "__main__":
    main()
