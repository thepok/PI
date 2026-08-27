#!/usr/bin/env python3
"""Independent exact replay for the BBP fibre-matching separator.

This implementation does not import the companion checker. It reconstructs
the actual rows from direct BBP partial sums, audits the binary coding by a
first-difference bound, and exhausts finite discrete shadows of the two
matching equivalences. Finite diagnostics have experiment status only.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_audit.md":
        "32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93",
    "work/theory/multiplicative-avoidance-gap/library/t1/"
    "S04_Blanchard_Host_Maass_1996.pdf":
        "c69b437a2c963d856f4f0026c1716434329b916f961a07da07d2421118d984fa",
    "work/theory/multiplicative-avoidance-gap/library/t1/"
    "S09_Badea_Grivaux_2303.01089v3.pdf":
        "6275f964abab16b16394523367709fa5b7c9ddec5b72ee29dbcc6292284430b1",
}
DIRECT_DEPTH = 128


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def clean(path: Path) -> bool:
    return all(byte in (9, 10, 13) or byte >= 32 for byte in path.read_bytes())


def a(index: int) -> Fraction:
    four_pole = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    polynomial = Fraction(
        120 * index**2 + 151 * index + 47,
        (2 * index + 1) * (4 * index + 3)
        * (8 * index + 1) * (8 * index + 5),
    )
    require(four_pole == polynomial > 0, f"coefficient k={index}")
    return four_pole


def frac(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def norm(value: Fraction) -> Fraction:
    value = frac(value)
    return min(value, 1 - value)


def direct_rows() -> tuple[list[Fraction], list[Fraction], int]:
    original_sum = Fraction()
    shifted_sum = Fraction(1, 30)
    u: list[Fraction] = []
    v: list[Fraction] = []
    checks = 0
    for n in range(DIRECT_DEPTH + 2):
        original_sum += a(n) / 16**n
        if n <= DIRECT_DEPTH:
            shifted_sum += a(n + 1) / 16**n
            u.append(frac(10**n * original_sum))
            v.append(frac(10**n * shifted_sum))
            if n >= 1:
                d_n = a(n + 1) * Fraction(5, 8) ** n
                require(v[n] == frac(16 * u[n] + d_n), f"direct adjacent n={n}")
                checks += 1
        else:
            u.append(frac(10**n * original_sum))

    for n in range(1, DIRECT_DEPTH + 1):
        require(frac(5 * v[n]) == frac(8 * u[n + 1]), f"direct fibre n={n}")
        decimal_carry = (
            10 * u[n]
            + a(n + 1) * Fraction(5, 8) ** (n + 1)
            - u[n + 1]
        )
        sixteen_carry = (
            16 * u[n]
            + a(n + 1) * Fraction(5, 8) ** n
            - v[n]
        )
        require(decimal_carry.denominator == 1, f"decimal carry n={n}")
        require(sixteen_carry.denominator == 1, f"sixteen carry n={n}")
        require(
            5 * v[n] - 8 * u[n + 1]
            == 8 * decimal_carry - 5 * sixteen_carry,
            f"carry label n={n}",
        )
        checks += 4
    return u, v, checks


def binary_integer(word: tuple[int, ...]) -> int:
    value = 0
    for digit in word:
        require(digit in (0, 1), "binary-decimal digit")
        value = 10 * value + digit
    return value


def binary_coding_audit() -> dict[str, object]:
    first_difference_checks = 0
    for position in range(1, 65):
        leading_gap = Fraction(1, 10**position)
        maximum_tail = Fraction(1, 9 * 10**position)
        require(
            leading_gap - maximum_tail
            == Fraction(8, 9 * 10**position) > 0,
            f"first-difference separation r={position}",
        )
        first_difference_checks += 1

    periodic_results = {}
    for depth in (3, 6, 9):
        words = list(product((0, 1), repeat=depth))
        denominator = 10**depth - 1
        points = [Fraction(binary_integer(word), denominator) for word in words]
        require(len(set(points)) == len(points), f"periodic injectivity L={depth}")
        rotated = {frac(10 * point) for point in points}
        require(rotated == set(points), f"T10 periodic invariance L={depth}")

        interval = lambda x: Fraction(3, 5) <= x <= Fraction(7, 9)
        require(sum(map(interval, points)) == 0, f"input interval L={depth}")
        image_count = sum(interval(frac(16 * point)) for point in points)
        require(image_count * 2 == len(points), f"image half mass L={depth}")
        periodic_results[str(depth)] = {
            "points": len(points),
            "input_interval_count": 0,
            "pushforward_interval_count": image_count,
        }

    return {
        "first_difference_checks": first_difference_checks,
        "exact_lower_bound": "8/(9*10^r)",
        "alternative_terminating_expansion_uses_digit_9": True,
        "periodic_checks": periodic_results,
    }


def cancellation_counterexample() -> dict[str, str]:
    x = Fraction(1, 9)
    y = frac(16 * x)
    require(y == Fraction(7, 9), "sixteen image of 1/9")
    require(frac(10 * x) == x and frac(10 * y) == y, "T10 fixed points")
    require(frac(8 * x) == frac(5 * y) == Fraction(8, 9), "common fibre image")
    require(x != y and norm(x - y) == Fraction(1, 3), "disjoint atoms")
    return {
        "mu": "delta_(1/9)",
        "nu": "delta_(7/9)",
        "common_fibre_image": "delta_(8/9)",
        "circle_separation": "1/3",
    }


def finite_matching_shadow() -> dict[str, int]:
    """Exhaust finite count-vector versions of Propositions 2.1 and 2.2."""

    alphabet = 3
    total = 6
    positive_overlap_checks = 0
    domination_checks = 0
    vectors = [
        counts
        for counts in product(range(total + 1), repeat=alphabet)
        if sum(counts) == total
    ]
    for left in vectors:
        for right in vectors:
            maximum_injective_overlap = sum(
                min(left[index], right[index]) for index in range(alphabet)
            )
            common_support = any(
                left[index] > 0 and right[index] > 0
                for index in range(alphabet)
            )
            require(
                (maximum_injective_overlap > 0) == common_support,
                f"finite positive overlap {left},{right}",
            )
            positive_overlap_checks += 1

            for congestion in (1, 2, 3):
                maximum_capacity_match = sum(
                    min(left[index], congestion * right[index])
                    for index in range(alphabet)
                )
                domination = all(
                    left[index] <= congestion * right[index]
                    for index in range(alphabet)
                )
                require(
                    (maximum_capacity_match == total) == domination,
                    f"finite domination C={congestion},{left},{right}",
                )
                domination_checks += 1
    return {
        "positive_overlap_equivalence_checks": positive_overlap_checks,
        "bounded_domination_equivalence_checks": domination_checks,
    }


def fixed_period_noncollapse_shadow() -> dict[str, float]:
    depth = 10
    points = [
        Fraction(binary_integer(word), 10**depth - 1)
        for word in product((0, 1), repeat=depth)
    ]
    output = {}
    for period in range(1, 7):
        average = sum(
            norm((10**period - 1) * point) ** 2 for point in points
        ) / len(points)
        require(average > 0, f"finite fixed-period shadow P={period}")
        output[str(period)] = float(average)
    return output


def main() -> None:
    pins = {}
    for relative, expected in PINS.items():
        path = ROOT / relative
        actual = digest(path)
        require(actual == expected, f"pin mismatch {relative}: {actual}")
        if path.suffix in {".md", ".txt", ".py"}:
            require(clean(path), f"C0 byte in {relative}")
        pins[relative] = actual

    report = ROOT / "work/ultrapi-resume/bbp_fiber_matching_no_go_20260813.md"
    companion = ROOT / "work/ultrapi-resume/bbp_fiber_matching_no_go_check.py"
    require(clean(report) and clean(companion) and clean(Path(__file__)), "C0 hygiene")
    text = report.read_text()
    require("V1 remains a" in text and "No bounded-congestion matching" in text,
            "claim boundary markers")
    require("statements are equivalent" in text and "mutually singular" in text,
            "equivalence markers")
    require("double-expansion ambiguity" in text, "decimal ambiguity marker")

    _, _, direct_checks = direct_rows()
    result = {
        "status": "PASS",
        "claim_label": "experiment",
        "source_pins": pins,
        "c0_hygiene": "PASS",
        "direct_partial_sum_identity_checks": direct_checks,
        "binary_coding_audit": binary_coding_audit(),
        "atomic_noncancellation": cancellation_counterexample(),
        "finite_matching_equivalence_shadow": finite_matching_shadow(),
        "fixed_period_noncollapse_experiment": fixed_period_noncollapse_shadow(),
        "imports_companion_checker": False,
        "asserts_actual_matching": False,
        "asserts_v1": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
