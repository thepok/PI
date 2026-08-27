#!/usr/bin/env python3
"""Independent exact replay for the all-depth BBP two-adic audit.

This program deliberately does not import the primary checker.  It verifies
finite rational and symbolic identities only, so its output has status
`experiment`; it is not a proof of an infinite p-adic assertion or V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
EXPECTED_HASHES = {
    "problems/local/pi-digits.txt": (
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
    ),
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf": (
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4"
    ),
    "work/theory/pi-digits/library/t6/barsky-munoz-perez-marco-2021.pdf": (
        "64629d2323ad8e1a11b457b3572c1568993c29b37e3959e8e9d31fa03d06fa2f"
    ),
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/lagarias-math0101055v2.pdf": (
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9"
    ),
}


def v2_integer(value: int) -> int:
    assert value
    value = abs(value)
    exponent = 0
    while value % 2 == 0:
        exponent += 1
        value //= 2
    return exponent


def v2_fraction(value: Fraction) -> int:
    assert value
    return v2_integer(value.numerator) - v2_integer(value.denominator)


def a_split(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def a_compact(index: int) -> Fraction:
    return Fraction(
        120 * index**2 + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def reflected(index: int) -> Fraction:
    return (
        Fraction(1, 8 * index + 2)
        + Fraction(1, 8 * index + 3)
        + Fraction(2, 8 * index + 4)
        - Fraction(4, 8 * index + 7)
    )


def check_symbolic_identities() -> None:
    x = sp.symbols("x")
    imaginary_unit = sp.I
    polynomial = x + x**2 + 2 * x**3 - 4 * x**6
    denominator = 1 - 16 * x**8
    first_quadratic = 2 * x**2 - 1
    second_quadratic = 2 * x**2 - 2 * x + 1

    assert sp.expand(
        polynomial
        + x * (x - 1) * (2 * x**2 + 1) * (2 * x**2 + 2 * x + 1)
    ) == 0
    assert sp.expand(
        denominator
        + (2 * x**2 - 1)
        * (2 * x**2 + 1)
        * (2 * x**2 - 2 * x + 1)
        * (2 * x**2 + 2 * x + 1)
    ) == 0

    reduced = x * (x - 1) / (first_quadratic * second_quadratic)
    assert sp.cancel(polynomial / denominator - reduced) == 0

    a_prime = (
        (imaginary_unit - 1) / (1 + (imaginary_unit - 1) * x)
        + (1 + imaginary_unit) / (1 - (1 + imaginary_unit) * x)
    ) / (2 * imaginary_unit)
    assert sp.cancel(a_prime - 1 / second_quadratic) == 0

    g_prime = (
        -sp.diff(sp.log(1 - 2 * x**2), x) / 8
        + sp.diff(sp.log(1 + 2 * x**2 - 2 * x), x) / 8
        + a_prime / 4
    )
    assert sp.cancel(g_prime - reduced) == 0


def main() -> None:
    for relative_path, expected_hash in EXPECTED_HASHES.items():
        actual_hash = sha256((ROOT / relative_path).read_bytes()).hexdigest()
        assert actual_hash == expected_hash, (relative_path, actual_hash)

    check_symbolic_identities()

    reflection_checks = 0
    for index in range(601):
        assert a_split(index) == a_compact(index)
        assert reflected(index) == a_compact(-1 - index)
        assert reflected(index).denominator % 2 == 1
        reflection_checks += 1

    # An independent finite shadow of the null series.  The stronger displayed
    # equality is observed only over this finite range and is not claimed in
    # the accompanying mathematical audit.
    reverse_partial = Fraction()
    reverse_checks = 0
    for block_count in range(1, 321):
        index = block_count - 1
        reverse_partial += 16**index * reflected(index)
        assert v2_fraction(reverse_partial) == (
            4 * block_count + v2_integer(block_count)
        )
        reverse_checks += 1

    bbp_partial = Fraction()
    scaled_partial = Fraction()
    denominator_checks = 0
    tail_separation_checks = 0
    for depth in range(321):
        coefficient = a_compact(depth)
        bbp_partial += coefficient / 16**depth
        scaled_partial = 16 * scaled_partial + coefficient
        assert scaled_partial == 16**depth * bbp_partial
        assert v2_fraction(scaled_partial) == v2_integer(depth + 1)

        if depth >= 1:
            assert v2_integer(bbp_partial.denominator) == (
                4 * depth - v2_integer(depth + 1)
            )
            denominator_checks += 1

        # Replace the infinite F(m) by a much deeper exact truncation.  Its
        # observed valuation is separated from both the finite BBP sum and
        # the first omitted possible valuation, replaying the ultrametric step.
        m = depth + 1
        cutoff = m + 12
        f_truncated = sum(
            (16**j * a_compact(m - 1 - j) for j in range(cutoff)),
            Fraction(),
        )
        assert v2_fraction(f_truncated) == v2_integer(m)
        assert 4 * cutoff > v2_fraction(f_truncated)
        if depth:
            assert 4 * m > v2_fraction(scaled_partial)
        tail_separation_checks += 1

    print("claim_status=experiment")
    print("independence=does_not_import_primary_checker")
    print(f"source_hash_checks={len(EXPECTED_HASHES)}")
    print("symbolic_factor_and_derivative_checks=5")
    print(f"reflection_checks={reflection_checks}")
    print(f"finite_null_series_valuation_checks={reverse_checks}")
    print(f"denominator_formula_checks={denominator_checks}")
    print(f"finite_tail_separation_checks={tail_separation_checks}")
    print("all independent exact assertions passed")


if __name__ == "__main__":
    main()
