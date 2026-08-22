#!/usr/bin/env python3
"""Exact T140 n=10 private-prime CRT full-BAD survivor certificate.

This is a finite experiment.  The CRT residue is reconstructed from the
unique surviving BBP summand prime-power by prime-power; canonical e_10 is
used only in a final consistency assertion.
"""

from fractions import Fraction as F
from math import lcm


def floor(x: F) -> int:
    return x.numerator // x.denominator


def center(x: F) -> F:
    return x - floor(x + F(1, 2))


def nu(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def den(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def q(j: int) -> int:
    return 10**j - 16


def eps(j: int) -> F:
    return F(5**j, 8**j * 15 * (j + 1) ** 2)


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def horizon(n: int) -> int:
    """Exact ceil(n*(log10(8/5)+1/100)), without floating point."""
    value = (n + 99) // 100
    while 10 ** (100 * value - n) * 5 ** (100 * n) < 8 ** (100 * n):
        value += 1
    assert 8 ** (100 * n) <= 10 ** (100 * value - n) * 5 ** (100 * n)
    assert 8 ** (100 * n) > 10 ** (100 * (value - 1) - n) * 5 ** (100 * n)
    return value


MAX_N = 30
Lambda: list[int] = []
M: list[int] = []
S: list[int] = []
A: list[F] = []
lam = 1
scale = 1
total = F(0)
for n in range(MAX_N + 1):
    lam = lcm(lam, den(n))
    total += F(nu(n), scale * den(n))
    Lambda.append(lam)
    M.append(scale * lam)
    S.append(sum(nu(k) * 16 ** (n - k) * (lam // den(k))
                 for k in range(n + 1)))
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


BASE = 10
L = horizon(BASE)
assert L == 3
T = M[BASE] // 48

# Select private primes from D_0,...,D_10 and derive residues without e_10.
factorizations = [factor(den(k)) for k in range(BASE + 1)]
private: list[tuple[int, int, int, int, int]] = []
for p in sorted(set().union(*(set(row) for row in factorizations))):
    if p <= 3:
        continue
    occurrences = [k for k, row in enumerate(factorizations) if p in row]
    a = max(row.get(p, 0) for row in factorizations)
    if len(occurrences) == 1 and factorizations[occurrences[0]][p] == a:
        k = occurrences[0]
        modulus = p**a
        residue = (nu(k) * 16 ** (BASE - k) *
                   (Lambda[BASE] // den(k))) % modulus
        private.append((p, k, a, modulus, residue))

P = 1
for _, _, _, modulus, _ in private:
    P *= modulus
assert T % P == 0

r = 0
for _, _, _, modulus, residue in private:
    cofactor = P // modulus
    r = (r + residue * cofactor * pow(cofactor, -1, modulus)) % P

assert private == [
    (29, 3, 1, 29, 6), (31, 7, 1, 31, 2),
    (37, 4, 1, 37, 31), (41, 5, 1, 41, 12),
    (43, 10, 1, 43, 8), (53, 6, 1, 53, 28),
    (61, 7, 1, 61, 57), (73, 9, 1, 73, 27),
]
assert P == 13_840_197_668_021
assert T == 501_279_153_857_749_830_020_441_598_590_976_000
assert r == 13_814_527_577_135

# This consistency check occurs only after the independent CRT construction.
canonical_e = (S[BASE] - 191 * M[BASE] // 64) % T
assert canonical_e % P == r

t0 = 12_294_962_618_106_739_655_891
x0 = r + P * t0
assert x0 == 170_164_712_955_526_266_975_539_796_722_538_846
assert 0 <= x0 < T


def fresh_increment(m: int) -> int:
    return sum(nu(k) * 16 ** (m - k) * (Lambda[m] // den(k))
               for k in range(BASE + 1, m + 1))


def phase_margin(x: int, m: int, s: int) -> tuple[int, F, F]:
    multiplier = M[m] // M[BASE]
    v = fresh_increment(m)
    assert S[m] == multiplier * S[BASE] + v
    tm = M[m] // 48
    em = (multiplier * x + v) % tm
    j = m + ell(m) + s
    raw = (F(1, 4) + delta(m, ell(m) + s)
           + F(q(j), 48) * F(em, tm))
    y = center(raw)
    margin = abs(y) - (F(1, 4) - eps(j))
    return j, y, margin


rows: list[tuple[int, int, int, str, F]] = []
rho_bounds: list[F] = []
for m in range(BASE, BASE + L + 1):
    for s in (-1, 0):
        j, y, margin = phase_margin(x0, m, s)
        assert margin >= 0
        rows.append((m, s, j, "-" if y < 0 else "+", margin))
        # A lift shift h changes this circle phase by q_j*h/(48*(T/P)).
        rho_bounds.append(F(48 * margin, q(j)))

H = T // P
rho = min(rho_bounds)
radius = floor(rho * H)
assert radius == 2_893

# Circular distance to the good arc is the margin above.  Therefore every
# |h|<=floor(rho H) stays BAD.  Replay every certified integer lift too.
for h in range(-radius, radius + 1):
    x = r + P * (t0 + h)
    assert 0 <= x < T
    for m in range(BASE, BASE + L + 1):
        for s in (-1, 0):
            assert phase_margin(x, m, s)[2] >= 0

# The next lower lift crosses the tight (m,s)=(13,0) boundary.
assert phase_margin(r + P * (t0 - radius - 1), 13, 0)[2] < 0

print("base/horizon", BASE, L)
print("private (p,k,a,p^a,residue)", private)
print("P,T,r", P, T, r)
print("t0,x0", t0, x0)
print("phase rows (m,s,j,sign,margin)", rows)
print("floor(rho*T/P)", radius)
print("certified consecutive CRT lifts", 2 * radius + 1)
