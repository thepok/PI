#!/usr/bin/env python3
"""Exact finite replay for bbp_empirical_rigidity_attack.md.

All output has claim status ``experiment``.  The script verifies source pins,
extracts theorem markers, checks the BBP diagonal/hexadecimal recurrences and
summable coupling bounds with exact rational arithmetic, and prints finite
decimal entropy and pushforward-affinity diagnostics.  It does not prove an
empirical limit theorem, entropy, affinity, a return for pi, or V1.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import log10, sqrt
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
    "lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf":
        "cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358",
    "work/theory/pi-digits/library/t44/hochman-2022-host-equidistribution-v2.pdf":
        "2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b",
    "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf":
        "9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85",
    "work/theory/pi-digits/library/t12/schmidt-1960-on-normal-numbers.pdf":
        "28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient(index: int) -> Fraction:
    split = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    combined = Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )
    assert split == combined > 0
    return combined


def fractional(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def pdf_text(relative: str) -> str:
    with tempfile.TemporaryDirectory(prefix="bbp-empirical-") as tmp:
        target = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / relative), str(target)],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return " ".join(target.read_text(errors="replace").split())


def source_markers() -> dict[str, bool]:
    texts = {
        "bbp": pdf_text("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf"),
        "lagarias": pdf_text(
            "work/theory/pi-lacunary-near-return-sparsity/library/t63/"
            "lagarias-math0101055v2.pdf"
        ),
        "furstenberg": pdf_text(
            "work/theory/pi-digits/library/t44/furstenberg-1967-disjointness.pdf"
        ),
        "hochman": pdf_text(
            "work/theory/pi-digits/library/t44/"
            "hochman-2022-host-equidistribution-v2.pdf"
        ),
        "rudolph": pdf_text(
            "work/theory/pi-digits/library/t44/rudolph-1990-times2-times3.pdf"
        ),
        "schmidt": pdf_text(
            "work/theory/pi-digits/library/t12/schmidt-1960-on-normal-numbers.pdf"
        ),
    }
    checks = {
        "bbp_formula": "Theorem 1." in texts["bbp"]
            and "The following identity holds" in texts["bbp"],
        "lagarias_perturbed_orbit": "perturbed remainder sequence" in texts["lagarias"]
            and "Theorem 3.1" in texts["lagarias"],
        "furstenberg_iv1": "T H E O R E M IV. 1" in texts["furstenberg"],
        "hochman_1_1": "Theorem 1.1" in texts["hochman"]
            and "multiplicatively independent" in texts["hochman"],
        "rudolph_4_11": "COROLLARY 4.11" in texts["rudolph"]
            and "cofinite subgroup" in texts["rudolph"],
        "schmidt_2": "THEOREM 2" in texts["schmidt"]
            and "normal in the scale of r" in texts["schmidt"],
    }
    assert all(checks.values()), checks
    return checks


def block_cell(value: Fraction, depth: int) -> int:
    return (value.numerator * 10**depth) // value.denominator


def entropy(distribution: Counter[int], total: int) -> float:
    answer = 0.0
    for count in distribution.values():
        probability = count / total
        answer -= probability * log10(probability)
    return answer


def affinity(left: Counter[int], right: Counter[int], total: int) -> float:
    return sum(
        sqrt(left.get(cell, 0) * right.get(cell, 0)) / total
        for cell in left.keys() | right.keys()
    )


def replay(max_depth: int = 120) -> dict[str, object]:
    partial = Fraction()
    diagonal_states: list[Fraction] = []
    hex_states: list[Fraction] = []
    diagonal_recurrence_checks = 0
    coboundary_checks = 0
    hex_recurrence_checks = 0

    prior_diagonal: Fraction | None = None
    prior_hex: Fraction | None = None
    prior_partial = Fraction()

    finite_decimal_error_sum = Fraction()
    finite_hex_error_sum = Fraction()

    for index in range(max_depth + 1):
        term = coefficient(index) / 16**index
        partial += term
        diagonal = fractional(10**index * partial)
        hexadecimal = fractional(16**index * partial)
        diagonal_states.append(diagonal)
        hex_states.append(hexadecimal)

        decimal_tail_bound = Fraction(5, 8) ** index / (15 * (index + 1) ** 2)
        hex_tail_bound = Fraction(1, 15 * (index + 1) ** 2)
        finite_decimal_error_sum += decimal_tail_bound
        finite_hex_error_sum += hex_tail_bound

        if index > 0:
            epsilon = coefficient(index) * Fraction(5, 8) ** index
            assert diagonal == fractional(10 * prior_diagonal + epsilon)
            diagonal_recurrence_checks += 1

            # This is 10*t_(n-1)-t_n after cancellation of the pi terms.
            canceled_coboundary = 10**index * (partial - prior_partial)
            assert canceled_coboundary == epsilon
            coboundary_checks += 1

            assert hexadecimal == fractional(16 * prior_hex + coefficient(index))
            hex_recurrence_checks += 1

        prior_diagonal = diagonal
        prior_hex = hexadecimal
        prior_partial = partial

    assert finite_decimal_error_sum < Fraction(8, 45)
    assert finite_hex_error_sum < Fraction(2, 15)

    sample_count = len(diagonal_states)
    diagnostics = {}
    for depth in range(1, 6):
        left = Counter(block_cell(state, depth) for state in diagonal_states)
        pushed = Counter(
            block_cell(fractional(16 * state), depth)
            for state in diagonal_states
        )
        diagnostics[str(depth)] = {
            "decimal_entropy_base10": entropy(left, sample_count),
            "entropy_per_digit": entropy(left, sample_count) / depth,
            "pushforward_affinity": affinity(left, pushed, sample_count),
            "occupied_cells": len(left),
            "pushed_occupied_cells": len(pushed),
        }

    return {
        "claim_label": "experiment",
        "max_depth": max_depth,
        "sample_count": sample_count,
        "diagonal_recurrence_checks": diagonal_recurrence_checks,
        "coboundary_checks": coboundary_checks,
        "hex_recurrence_checks": hex_recurrence_checks,
        "finite_decimal_error_sum": str(finite_decimal_error_sum),
        "universal_decimal_error_sum_bound": "8/45",
        "finite_hex_error_sum": str(finite_hex_error_sum),
        "universal_hex_error_sum_bound": "2/15",
        "finite_cylinder_diagnostics": diagnostics,
        "warning": "finite entropy and affinity are not asymptotic hypotheses",
    }


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        actual = digest(ROOT / relative)
        assert actual == expected, (relative, expected, actual)
        pins[relative] = actual

    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "source_markers": source_markers(),
        "replay": replay(),
        "asserts_v1": False,
        "asserts_fixed_return": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
