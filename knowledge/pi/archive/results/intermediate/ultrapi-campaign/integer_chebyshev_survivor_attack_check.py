#!/usr/bin/env python3
"""Exact finite checks for integer_chebyshev_survivor_attack.md.

The symbolic identities and finite boxed optimizations checked here do not
prove V1.  The optimization output is an ``experiment`` over a finite node
set and a finite coefficient box.
"""

from __future__ import annotations

import hashlib
import itertools
import math
from fractions import Fraction
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "problems/local/pi-digits.txt"
REPORT = Path(__file__).with_name("integer_chebyshev_survivor_attack.md")
TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def l1(poly: sp.Poly) -> int:
    return sum(abs(int(coefficient)) for coefficient in poly.all_coeffs())


def dickson_trace(n: int, variable: sp.Symbol) -> sp.Poly:
    """C_n with C_n(z+z^-1)=z^n+z^-n."""
    if n == 0:
        return sp.Poly(2, variable, domain=sp.ZZ)
    if n == 1:
        return sp.Poly(variable, variable, domain=sp.ZZ)
    previous = sp.Poly(2, variable, domain=sp.ZZ)
    current = sp.Poly(variable, variable, domain=sp.ZZ)
    for _ in range(1, n):
        previous, current = current, sp.Poly(
            variable * current.as_expr() - previous.as_expr(),
            variable,
            domain=sp.ZZ,
        )
    return current


def avoids(digits: tuple[int, ...], forbidden: tuple[int, ...]) -> bool:
    width = len(forbidden)
    return all(
        digits[start : start + width] != forbidden
        for start in range(len(digits) - width + 1)
    )


def finite_admissible_prefix_nodes(
    forbidden: tuple[int, ...], length: int
) -> list[int]:
    """Numerators of admissible prefixes, not necessarily points of K_w."""
    return [
        sum(digit * 10 ** (length - 1 - index) for index, digit in enumerate(digits))
        for digits in itertools.product(range(10), repeat=length)
        if avoids(digits, forbidden)
    ]


def boxed_integer_chebyshev(
    forbidden: tuple[int, ...],
    level: int,
    degree: int,
    coefficient_bound: int,
) -> tuple[Fraction, tuple[int, ...]]:
    """Exact minimax search on rational truncation nodes in a finite box."""
    numerators = finite_admissible_prefix_nodes(forbidden, level)
    denominator = 10**level
    # Evaluate after multiplication by denominator**degree, so all comparisons
    # remain integer comparisons.
    rows = [
        [a**power * denominator ** (degree - power) for power in range(degree + 1)]
        for a in numerators
    ]
    best: tuple[int, int, int, tuple[int, ...]] | None = None
    for coefficients in itertools.product(
        range(-coefficient_bound, coefficient_bound + 1),
        repeat=degree + 1,
    ):
        if not any(coefficients):
            continue
        maximum = max(
            abs(sum(coefficients[k] * row[k] for k in range(degree + 1)))
            for row in rows
        )
        actual_degree = max(k for k, value in enumerate(coefficients) if value)
        key = (maximum, actual_degree, max(map(abs, coefficients)), coefficients)
        if best is None or key < best:
            best = key
    assert best is not None
    return Fraction(best[0], denominator**degree), best[3]


def check_trace_and_minimal_laurent_clearing() -> None:
    x, z = sp.symbols("x z")
    for n in range(1, 15):
        trace = dickson_trace(n, x)
        assert trace.degree() == n
        # Clear z^-n before asking SymPy for a polynomial identity.
        identity = sp.expand(
            z**n * trace.as_expr().subs(x, z + z**-1) - (z ** (2 * n) + 1)
        )
        assert identity == 0

    assert dickson_trace(3, x).as_expr() == x**3 - 3 * x

    # The Laurent detector has exponents -p, 0, p.  Its exponent span is 2p,
    # so no monomial shift can produce a polynomial of degree below 2p.
    for p in range(1, 40):
        cleared = sp.Poly(
            sp.expand(z**p * (z**p + z**-p - 2)), z, domain=sp.ZZ
        )
        assert sp.expand(cleared.as_expr() - (z**p - 1) ** 2) == 0
        assert cleared.degree() == 2 * p
        assert l1(cleared) == 4


def check_exact_auxiliary_ledgers() -> None:
    x, z = sp.symbols("x z")
    c3 = dickson_trace(3, x).as_expr()
    for copies in range(1, 25):
        real_auxiliary = sp.Poly(
            ((x - 3) * (4 - x)) ** copies,
            x,
            domain=sp.ZZ,
        )
        assert real_auxiliary.degree() == 2 * copies
        # All contributions to a fixed coefficient have the same sign.
        assert l1(real_auxiliary) == 20**copies

        exponential_auxiliary = sp.Poly(
            (z**3 + 1) ** (2 * copies),
            z,
            domain=sp.ZZ,
        )
        assert exponential_auxiliary.degree() == 6 * copies
        assert l1(exponential_auxiliary) == 4**copies
        assert max(abs(int(c)) for c in exponential_auxiliary.all_coeffs()) == math.comb(
            2 * copies, copies
        )

        # z^(3D) (C_3(z+z^-1)+2)^D = (z^3+1)^(2D).
        lifted = sp.expand(
            z ** (3 * copies)
            * (c3.subs(x, z + z**-1) + 2) ** copies
        )
        assert sp.expand(lifted - exponential_auxiliary.as_expr()) == 0


def check_general_trace_lift() -> None:
    """Check degree and length bounds for deterministic integer R."""
    y, z = sp.symbols("y z")
    for degree in range(1, 7):
        coefficients = [((5 * k + 2 * degree) % 9) - 4 for k in range(degree + 1)]
        if coefficients[-1] == 0:
            coefficients[-1] = 1
        r = sp.Poly(sum(coefficients[k] * y**k for k in range(degree + 1)), y)
        length = sum(abs(c) for c in coefficients)
        for p in (1, 2, 5, 13):
            lifted = sp.Poly(
                sp.expand(
                    z ** (degree * p)
                    * r.as_expr().subs(y, z**p + z**-p)
                ),
                z,
                domain=sp.ZZ,
            )
            assert lifted.degree() <= 2 * degree * p
            assert l1(lifted) <= 2**degree * length


def check_orbit_product_height_ledger() -> None:
    """Check the exact leading term and l1 bound with arbitrary prefixes."""
    x = sp.symbols("x")
    r = sp.Poly(2 - 3 * x + x**2, x, domain=sp.ZZ)
    degree = r.degree()
    length = l1(r)
    product_poly = sp.Poly(1, x, domain=sp.ZZ)
    for j, tail_prefix in enumerate((0, 1, 14, 141, 1415, 14159)):
        p_j = 3 * 10**j + tail_prefix
        factor = sp.Poly(r.as_expr().subs(x, 10**j * x - p_j), x, domain=sp.ZZ)
        product_poly *= factor
        count = j + 1
        expected_leading = int(r.LC()) ** count * 10 ** (
            degree * count * (count - 1) // 2
        )
        assert int(product_poly.LC()) == expected_leading
        upper = length**count * 5 ** (degree * count) * 10 ** (
            degree * count * (count - 1) // 2
        )
        assert l1(product_poly) <= upper


def check_finite_boxed_optimizations() -> None:
    # These are finite ``experiment`` results.  In this small search box, the
    # minimizer is the universal square [x(1-x)]^2; most forbidden words are
    # invisible at this scale.
    expected = {
        (0,): Fraction(6245001, 100000000),
        (3, 1): Fraction(1, 16),
        (9,): Fraction(1, 16),
    }
    universal = (0, 0, -1, 2, -1)
    for forbidden, optimum in expected.items():
        value, coefficients = boxed_integer_chebyshev(forbidden, 2, 4, 2)
        assert value == optimum
        assert coefficients == universal


def main() -> None:
    assert hashlib.sha256(TARGET.read_bytes()).hexdigest() == TARGET_SHA
    report_text = REPORT.read_text(encoding="utf-8")
    for source_pin in (
        "8685ecf5001fe76271c5fd2a9b50783967d2c1a708e6ace52d215b2231cbc8c2",
        "d703e1d94a115b86ba510549c599dbf01845dc153cc83fd77a40594a43761d27",
        "fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a",
    ):
        assert source_pin in report_text
    check_trace_and_minimal_laurent_clearing()
    check_exact_auxiliary_ledgers()
    check_general_trace_lift()
    check_orbit_product_height_ledger()
    check_finite_boxed_optimizations()
    print(
        "PASS: exact trace lifts, minimal Laurent clearing, auxiliary ledgers, "
        "orbit heights, and finite boxed optimizations"
    )
    print(
        "EXPERIMENT: degree<=4, |coefficient|<=2 finite-node minimizers are "
        "the universal [x(1-x)]^2 for w=0, w=31, and w=9"
    )


if __name__ == "__main__":
    main()
