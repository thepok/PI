#!/usr/bin/env python3
"""Independent exact checks for the integer--Chebyshev survivor audit.

This program deliberately does not import the primary checker.  It verifies
finite algebraic identities and parameter ledgers only.  The potential-theory
and transcendence-measure inputs are checked against their primary sources in
the accompanying independent audit; no finite computation proves V1.
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
PRIMARY = Path(__file__).with_name("integer_chebyshev_survivor_attack.md")
PRIMARY_CHECKER = Path(__file__).with_name(
    "integer_chebyshev_survivor_attack_check.py"
)

TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
PRIMARY_SHA = "27252531f03e8a8826fdb6cd471bd447990c89ff881bcd5e24f357f307eb5192"
PRIMARY_CHECKER_SHA = (
    "89f4114b0faedc312b08e9338d94f944ac91de4f3febdb4b3804664e27ad766a"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def length(poly: sp.Poly) -> int:
    return sum(abs(int(c)) for c in poly.all_coeffs())


def trace_poly(n: int, x: sp.Symbol) -> sp.Poly:
    previous = sp.Poly(2, x, domain=sp.ZZ)
    if n == 0:
        return previous
    current = sp.Poly(x, x, domain=sp.ZZ)
    for _ in range(1, n):
        previous, current = current, sp.Poly(
            x * current.as_expr() - previous.as_expr(), x, domain=sp.ZZ
        )
    return current


def check_capacity_skeleton() -> None:
    """Check the exact digit choices and separated-similarity geometry."""
    palette = (2, 3, 6, 7)
    for forbidden_digit in range(10):
        choices = [digit for digit in palette if digit != forbidden_digit]
        assert len(choices) >= 3
        a, b = choices[:2]
        assert 2 <= a < b <= 7
        # Images of [2/9,7/9] under x |-> (a+x)/10 and (b+x)/10
        # are strictly separated.
        assert b + 2 / 9 > a + 7 / 9
    assert math.log(2) / math.log(10) > 0
    # On [2/9,7/9], |(2 cos x)'| is bounded above and away from zero.
    assert 0 < 2 * math.sin(2 / 9) <= 2 * math.sin(7 / 9) < 2
    assert 0 < (1 - math.cos(1)) / 2 < 1 / 4


def check_trace_lifts_and_minimal_clearing() -> None:
    x, y, z = sp.symbols("x y z")
    for n in range(1, 18):
        c_n = trace_poly(n, x)
        cleared_identity = sp.expand(
            z**n * c_n.as_expr().subs(x, z + z**-1) - (z ** (2 * n) + 1)
        )
        assert cleared_identity == 0

    r = sp.Poly(y**3 - 2 * y + 1, y, domain=sp.ZZ)
    d = r.degree()
    exponents = (2, 5, 13)
    exponent_sum = sum(exponents)
    laurent_product = sp.prod(
        r.as_expr().subs(y, z**p + z**-p) for p in exponents
    )
    lifted = sp.Poly(
        sp.expand(z ** (d * exponent_sum) * laurent_product),
        z,
        domain=sp.ZZ,
    )
    assert lifted.degree() == 2 * d * exponent_sum
    assert length(lifted) <= (2**d * length(r)) ** len(exponents)

    simplest = sp.Poly(
        sp.expand(
            z ** exponent_sum
            * sp.prod(z**p + z**-p - 2 for p in exponents)
        ),
        z,
        domain=sp.ZZ,
    )
    expected = sp.Poly(
        sp.expand(sp.prod((z**p - 1) ** 2 for p in exponents)),
        z,
        domain=sp.ZZ,
    )
    assert simplest == expected
    assert simplest.degree() == 2 * exponent_sum
    assert int(simplest.LC()) == 1 and int(simplest.TC()) == 1
    assert length(simplest) <= 4 ** len(exponents)


def check_real_orbit_height() -> None:
    x = sp.symbols("x")
    prefixes = (3, 31, 314, 3141)
    test_polynomials = (
        sp.Poly(x**2 - 3 * x + 2, x, domain=sp.ZZ),
        sp.Poly(2 * x**3 - x + 3, x, domain=sp.ZZ),
    )
    for r in test_polynomials:
        product = sp.Poly(1, x, domain=sp.ZZ)
        for j, prefix in enumerate(prefixes):
            assert 3 * 10**j <= prefix < 4 * 10**j
            product *= sp.Poly(
                sp.expand(r.as_expr().subs(x, 10**j * x - prefix)),
                x,
                domain=sp.ZZ,
            )
            count = j + 1
            d = r.degree()
            expected_lc = int(r.LC()) ** count * 10 ** (
                d * count * (count - 1) // 2
            )
            assert int(product.LC()) == expected_lc
            upper = length(r) ** count * 5 ** (d * count) * 10 ** (
                d * count * (count - 1) // 2
            )
            assert length(product) <= upper


def check_pi_to_logarithm_transfer() -> None:
    """Reconstruct the omitted Gaussian-to-integer Cijsouw transfer."""
    x, t = sp.symbols("x t")
    families = (
        (1, -2),
        (3, 0, -4, 2),
        (-1, 5, 2, 0, -3),
    )
    for coefficients in families:
        p = sp.Poly(
            sum(coefficient * x**k for k, coefficient in enumerate(coefficients)),
            x,
            domain=sp.ZZ,
        )
        d = p.degree()
        h = max(abs(int(c)) for c in p.all_coeffs())
        q_expr = sp.expand(
            p.as_expr().subs(x, -sp.I * x)
            * p.as_expr().subs(x, sp.I * x)
        )
        q = sp.Poly(q_expr, x, domain=sp.ZZ)
        assert q.degree() == 2 * d
        assert length(q) <= length(p) ** 2 <= ((d + 1) * h) ** 2
        assert sp.expand(q.as_expr().subs(x, sp.I * t) - p.as_expr().subs(x, t) * p.as_expr().subs(x, -t)) == 0


def check_euler_power_ledger() -> None:
    z = sp.symbols("z")
    for copies in range(1, 31):
        auxiliary = sp.Poly((z**3 + 1) ** (2 * copies), z, domain=sp.ZZ)
        assert auxiliary.degree() == 6 * copies
        assert length(auxiliary) == 4**copies
        assert max(abs(int(c)) for c in auxiliary.all_coeffs()) == math.comb(
            2 * copies, copies
        )
    # The rational part of 3 < pi < 22/7 used in the value estimate.
    assert 3 < Fraction(333, 106) < Fraction(22, 7)
    assert Fraction(22, 7) - 3 == Fraction(1, 7)


def check_cijsouw_parameter_substitution() -> None:
    """Check the degree/height scales used in the two applications."""
    # If D <= C N and log H <= C N, then D^2(D+log H) <= 2 C^3 N^3.
    for c, n in itertools.product((1, 2, 5, 11), (1, 3, 10, 50)):
        d_bound = c * n
        log_h_bound = c * n
        assert d_bound**2 * (d_bound + log_h_bound) <= 2 * c**3 * n**3

    # For the real orbit product with fixed detector degree, D=Theta(N)
    # and log H=Theta(N^2), so the logarithm measure has N^4 log^2 N
    # scale.  For the trace lift D=Theta(10^N), its exponential measure
    # has 10^(3N) scale.  Exact integer comparisons avoid asymptotic CAS.
    for n in range(2, 20):
        real_d = 3 * n
        real_log_h_majorant = 7 * n**2
        real_penalty = real_d**2 * (real_d + real_log_h_majorant)
        assert real_penalty <= 630 * n**4

        trace_d_lower = 10**n
        trace_penalty_lower = trace_d_lower**3
        assert trace_penalty_lower == 10 ** (3 * n)

    # A power N^(3+epsilon) eventually beats every fixed multiple of N^3;
    # this is the exact logical content of the sufficient compression lemma.
    for fixed_multiplier in (1, 7, 10_000):
        epsilon = 0.5
        threshold = math.ceil(fixed_multiplier ** (1 / epsilon)) + 1
        assert threshold ** (3 + epsilon) > fixed_multiplier * threshold**3


def check_prefix_experiment_scope() -> None:
    """Exhibit why admissible truncations are not survivor points."""
    forbidden = (0,)
    prefix = (1, 1)
    assert all(digit not in forbidden for digit in prefix)
    # The terminating value 0.11 has tails 0,0,... in its terminating
    # expansion; its alternative 0.10999... also contains 0.  Thus this
    # primary-checker node is not a point of K_(0).
    terminating_start = prefix + (0,)
    alternative_start = (1, 0, 9)
    assert 0 in terminating_start and 0 in alternative_start


def main() -> None:
    assert sha256(TARGET) == TARGET_SHA
    assert sha256(PRIMARY) == PRIMARY_SHA
    assert sha256(PRIMARY_CHECKER) == PRIMARY_CHECKER_SHA
    check_capacity_skeleton()
    check_trace_lifts_and_minimal_clearing()
    check_real_orbit_height()
    check_pi_to_logarithm_transfer()
    check_euler_power_ledger()
    check_cijsouw_parameter_substitution()
    check_prefix_experiment_scope()
    print(
        "PASS: independent capacity skeleton, orbit/trace algebra, height ledgers, "
        "Cijsouw transfer/scales, Euler powers, and compression threshold"
    )
    print(
        "SCOPE: admissible-prefix truncations are not generally points of K_w; "
        "their boxed minimax output remains experiment only"
    )
    print("VERDICT: no contradiction and no proof of V1")


if __name__ == "__main__":
    main()
