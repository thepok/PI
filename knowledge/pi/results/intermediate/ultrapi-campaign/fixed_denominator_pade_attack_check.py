#!/usr/bin/env python3
"""Exact finite replay for fixed_denominator_pade_attack.md.

All mathematical identities below use integers/Fraction.  The optional
high-precision pi return is deliberately omitted: it is only an experiment
recorded in the report, not an input to any proof-sketch deduction.
"""

from fractions import Fraction
from math import gcd


def check(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def gauss_arctan_convergent(p: int, q: int, depth: int) -> Fraction:
    """Depth-n convergent of p/(q + p^2/(3q + (2p)^2/(5q+...)))."""
    pm2, pm1 = 1, 0
    qm2, qm1 = 0, 1
    for n in range(1, depth + 1):
        a = p if n == 1 else (n - 1) ** 2 * p * p
        b = q * (2 * n - 1)
        pn = b * pm1 + a * pm2
        qn = b * qm1 + a * qm2
        pm2, pm1 = pm1, pn
        qm2, qm1 = qm1, qn
    return Fraction(pm1, qm1)


def arctan_partial(p: int, q: int, terms: int) -> Fraction:
    x = Fraction(p, q)
    return sum(
        ((-1) ** k * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms)),
        Fraction(),
    )


def v_p(n: int, p: int) -> int:
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


# Wang's coefficient recurrence and the classical first convergents.
expected = [Fraction(4), Fraction(3), Fraction(19, 6), Fraction(160, 51),
            Fraction(1744, 555), Fraction(644, 205)]
actual = [4 * gauss_arctan_convergent(1, 1, n) for n in range(1, 7)]
check(actual == expected, "Gauss--Lambert pi convergents")

# OEIS A012244 / continuant recurrence before reduction by the numerator.
q_expected = [1, 1, 4, 24, 204, 2220, 29520, 463680]
q = [1, 1]
for n in range(2, len(q_expected)):
    q.append((2 * n - 1) * q[-1] + (n - 1) ** 2 * q[-2])
check(q == q_expected, "continuant denominator recurrence")

# Exact first reduced-denominator 5-adic windows; this is an experiment only.
zero_windows = []
current = []
for n in range(1, 201):
    d = (4 * gauss_arctan_convergent(1, 1, n)).denominator
    if v_p(d, 5) == 0:
        current.append(n)
    elif current:
        zero_windows.append((current[0], current[-1]))
        current = []
if current:
    zero_windows.append((current[0], current[-1]))
check(zero_windows == [(1, 4), (20, 24), (110, 114)],
      "finite 5-adic eligibility windows through depth 200")

# Euler split pi/4 = atan(1/2)+atan(1/3), equal depth six.
a6 = 4 * (gauss_arctan_convergent(1, 2, 6)
          + gauss_arctan_convergent(1, 3, 6))
check(a6 == Fraction(774756220, 246612571), "Euler split depth-six shadow")
d6 = a6.denominator
check(d6 == 19 * 641 * 20249, "depth-six factorization")

# A fully transparent order/discrete-log replay (no black-box CAS call).
def first_hit_and_order(modulus: int) -> tuple[int, int]:
    residue = 1 % modulus
    first_hit = -1
    for n in range(1, modulus + 1):
        residue = residue * 10 % modulus
        if residue == 16 % modulus and first_hit < 0:
            first_hit = n
        if residue == 1:
            return first_hit, n
    raise AssertionError("multiplicative order not found")


prime_data = {19: (14, 18), 641: (10, 32), 20249: (1472, 2531)}
for p, wanted in prime_data.items():
    check(first_hit_and_order(p) == wanted, f"discrete log/order modulo {p}")

# Verify the CRT solution directly and its minimality by stepping through the
# lcm-sized period, still tiny enough for an exact finite checker.
N = 684_842
period = 728_928
check(pow(10, N, d6) == 16 % d6, "exact fixed-sixteen anchor")
check(pow(10, period, d6) == 1, "combined order")
residue = 1
for n in range(1, N):
    residue = residue * 10 % d6
    if residue == 16 % d6:
        raise AssertionError("claimed first fixed-sixteen anchor is not first")

# Certified rational lower bound on |pi-A6|.  The 20-term alternating
# Gregory sums for atan(1/2) and atan(1/3) are strict lower bounds, because
# the last retained term has negative sign.  Hence A6 < L < pi.
lower_pi = 4 * (arctan_partial(1, 2, 20) + arctan_partial(1, 3, 20))
check(a6 < lower_pi, "orientation of the exact lower bound")
check(lower_pi - a6 > Fraction(1, 11_560_000),
      "certified |pi-A6| lower bound")

# Consequently the Archimedean transfer-error term in the triangle-
# inequality is larger than this enormous integer at the exact anchor.
# This is a lower bound on that term, not on the true circle return.  The
# integer comparison contains no floating point.
check((10**N - 16) * (lower_pi - a6) > 10 ** (N - 8),
      "anchored Archimedean mismatch")

print(
    "PASS: Gauss recurrence, finite 5-adic windows, Euler depth-six "
    "fixed-sixteen anchor, and exact rational error mismatch"
)
