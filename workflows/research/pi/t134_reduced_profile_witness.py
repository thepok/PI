#!/usr/bin/env python3
"""Reproduce the exact finite T134 reduced-profile counterstate witness."""

from fractions import Fraction as F
from math import gcd, lcm


def floor(x: F) -> int:
    return x.numerator // x.denominator


def frac(x: F) -> F:
    return x - floor(x)


def center(x: F) -> F:
    return x - floor(x + F(1, 2))


def nu(n: int) -> int:
    return 120 * n * n + 151 * n + 47


def den(n: int) -> int:
    return (2 * n + 1) * (4 * n + 3) * (8 * n + 1) * (8 * n + 5)


def q(j: int) -> int:
    return 10**j - 16


def eps(j: int) -> F:
    return F(5**j, 8**j * 15 * (j + 1) ** 2)


MAX_N = 14
lam = 1
scale = 1
total = F(0)
Lambda: list[int] = []
M: list[int] = []
S: list[int] = []
A: list[F] = []
for n in range(MAX_N + 1):
    lam = lcm(lam, den(n))
    total += F(nu(n), scale * den(n))
    Lambda.append(lam)
    M.append(scale * lam)
    S.append(sum(nu(k) * 16 ** (n - k) * (lam // den(k)) for k in range(n + 1)))
    A.append(total)
    assert F(S[n], M[n]) == A[n]
    scale *= 16


def delta(n: int, i: int) -> F:
    return q(n + i) * (A[n + i] - A[n])


def ell(n: int) -> int:
    i = 1
    while delta(n, i) < F(1, 4):
        i += 1
    return i


def phase(n: int, s: int, x: F) -> tuple[int, str, bool, F, F]:
    e = ell(n)
    j = n + e + s
    raw = F(1, 4) + delta(n, e + s) + F(q(j), 48) * x
    z = floor(raw + F(1, 2))
    y = raw - z
    margin = abs(y) - (F(1, 4) - eps(j))
    return z, "-" if y < 0 else "+", margin >= 0, y, margin


base = 6
offset = -570
counter = S[base] + offset
counter_S = {base: counter}
for n in range(base, base + 3):
    rho = Lambda[n + 1] // Lambda[n]
    counter = 16 * rho * counter + nu(n + 1) * (Lambda[n + 1] // den(n + 1))
    counter_S[n + 1] = counter

# (8/5)^5 > 10 and (8/5)^100 < 10^21 imply 1/5 < alpha < 21/100,
# hence ceil(6(alpha+1/100)) = 2 without floating-point arithmetic.
assert 8**5 > 10 * 5**5
assert 8**100 < 10**21 * 5**100
L = 2
assert (S[base] - counter_S[base]) % M[base] == 570

expected_gcds = (5, 40, 5, 190)
gcd_pairs = tuple(
    (gcd(S[n], M[n]), gcd(counter_S[n], M[n]))
    for n in range(base, base + 4)
)
assert gcd_pairs == tuple((g, g) for g in expected_gcds)

rows = []
for n in range(base, base + L + 1):
    canonical_x = frac(48 * F(S[n], M[n]) - F(573, 4))
    counter_x = frac(48 * F(counter_S[n], M[n]) - F(573, 4))
    for s in (-1, 0):
        canonical = phase(n, s, canonical_x)
        alternate = phase(n, s, counter_x)
        assert canonical[:3] == alternate[:3]
        assert canonical[2]
        assert canonical[3] == center(q(n + ell(n) + s) * A[n + ell(n) + s])
        assert canonical[4] > F(1, 100) and alternate[4] > F(1, 100)
        assert canonical[3] != alternate[3]
        rows.append((n, s, canonical[:3], canonical[3] - alternate[3]))

print("L", L)
print("M_6", M[6])
print("S_6", S[6])
print("S'_6", counter_S[6])
print("gcd pairs", gcd_pairs)
print("address rows", rows)

