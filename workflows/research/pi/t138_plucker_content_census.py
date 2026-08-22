#!/usr/bin/env python3
"""Exact finite P13 Plucker-content census; experiment only."""

from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations
from math import ceil, gcd


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


def horizon(n: int) -> int:
    with localcontext() as ctx:
        ctx.prec = 80
        alpha = (Decimal(8) / Decimal(5)).log10() + Decimal(1) / Decimal(100)
        candidate = ceil(alpha * n)
    lhs = 8 ** (100 * n)
    assert lhs > 5 ** (100 * n) * 10 ** (100 * (candidate - 1) - n)
    assert lhs < 5 ** (100 * n) * 10 ** (100 * candidate - n)
    return candidate


MAX_A = 500
A = []
total = F(0)
scale = 1
for m in range(MAX_A + 1):
    total += F(nu(m), scale * den(m))
    A.append(total)
    scale *= 16


def delta(m: int, i: int) -> F:
    return q(m + i) * (A[m + i] - A[m])


ELL = {}
for m in range(6, 350):
    i = 1
    while delta(m, i) < F(1, 4):
        i += 1
    ELL[m] = i


def phase(m: int, s: int, x: F) -> tuple[int, int, F, bool]:
    j = m + ELL[m] + s
    assert j >= 4 and q(j) % 48 == 0
    Q = q(j) // 48
    raw = F(1, 4) + delta(m, ELL[m] + s) + Q * x
    z = floor(raw + F(1, 2))
    y = raw - z
    return Q, z, y, abs(y) >= F(1, 4) - eps(j)


def canonical_x(m: int) -> F:
    return frac(48 * A[m] - F(573, 4))


def comparator_x(base: int, m: int) -> F:
    return frac(F(63, 64) + 48 * (A[m] - A[base]))


def rows(checkpoints: tuple[int, ...]) -> list[tuple[int, int]]:
    out = []
    for m in checkpoints:
        x = canonical_x(m)
        for s in (-1, 0):
            Q, z, y, bad = phase(m, s, x)
            j = m + ELL[m] + s
            assert y == center(q(j) * A[j])
            assert bad
            out.append((Q, z))
    return out


def minor_gcd(row_data: list[tuple[int, int]]) -> int:
    value = 0
    for (Qa, za), (Qb, zb) in combinations(row_data, 2):
        value = gcd(value, abs(Qa * zb - Qb * za))
    return value


print("known all-BAD runs")
for run in (tuple(range(168, 173)), tuple(range(335, 340))):
    full_g = minor_gcd(rows(run))
    print("run", run[0], run[-1], "full_gcd", full_g)
    assert full_g == 1
    for omitted in run:
        subset = tuple(m for m in run if m != omitted)
        g = minor_gcd(rows(subset))
        print("omit", omitted, "subset_gcd", g)
        assert g == 1


eligible = []
n = 6
while len(eligible) < 32:
    L = horizon(n)
    rs = (0, L // 3, (2 * L) // 3, L)
    if len(set(rs)) == 4:
        eligible.append((n, L, rs))
    n += 1

assert [row[0] for row in eligible] == list(range(10, 42))
canonical_all_bad = comparator_all_bad = joint_all_bad = 0
same_z = 0
for n, L, rs in eligible:
    checkpoints = tuple(n + r for r in rs)
    canonical_bits = []
    comparator_bits = []
    canonical_z = []
    comparator_z = []
    for m in checkpoints:
        for s in (-1, 0):
            j = m + ELL[m] + s
            Qc, zc, yc, bc = phase(m, s, canonical_x(m))
            Qp, zp, yp, bp = phase(m, s, comparator_x(n, m))
            assert Qc == Qp
            assert yc == center(q(j) * A[j])
            assert yp == center(
                F(1, 4) + q(j) * (A[j] - A[n]) + F(63 * q(j), 3072)
            )
            canonical_bits.append(bc)
            comparator_bits.append(bp)
            canonical_z.append(zc)
            comparator_z.append(zp)
    c_bad = all(canonical_bits)
    p_bad = all(comparator_bits)
    canonical_all_bad += c_bad
    comparator_all_bad += p_bad
    joint_all_bad += c_bad and p_bad
    same_z += canonical_z == comparator_z

print("quarter bases", eligible)
print("canonical all-eight-BAD", canonical_all_bad)
print("comparator all-eight-BAD", comparator_all_bad)
print("joint all-eight-BAD", joint_all_bad)
print("identical eight-z vectors", same_z)
assert (canonical_all_bad, comparator_all_bad, joint_all_bad, same_z) == (0, 0, 0, 0)
