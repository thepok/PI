#!/usr/bin/env python3
"""Exact finite census for T136 three-growth BAD cylinders.

This is an experiment, not a proof.  It compares the canonical BBP entry with
the entry 63/64 propagated through the same exact prefix increments.
"""

from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import ceil, gcd, lcm

N_MIN, N_MAX = 65, 128


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
    # Certify the Decimal-produced candidate using exact integer inequalities:
    # candidate-1 < n(log10(8/5)+1/100) < candidate.
    lhs = 8 ** (100 * n)
    assert lhs > 5 ** (100 * n) * 10 ** (100 * (candidate - 1) - n)
    assert lhs < 5 ** (100 * n) * 10 ** (100 * candidate - n)
    return candidate


max_m = max(n + horizon(n) for n in range(N_MIN, N_MAX + 1))

lam = []
current_lcm = 1
A = []
total = F(0)
scale = 1
for m in range(max_m + 40):
    current_lcm = lcm(current_lcm, den(m))
    lam.append(current_lcm)
    total += F(nu(m), scale * den(m))
    A.append(total)
    scale *= 16


def delta(m: int, i: int) -> F:
    return q(m + i) * (A[m + i] - A[m])


ell = {}
for m in range(N_MIN, max_m + 1):
    i = 1
    while delta(m, i) < F(1, 4):
        i += 1
    ell[m] = i


def phase(m: int, s: int, x: F) -> tuple[F, bool]:
    j = m + ell[m] + s
    raw = F(1, 4) + delta(m, ell[m] + s) + F(q(j), 48) * x
    y = center(raw)
    return y, abs(y) >= F(1, 4) - eps(j)


def bad_pair(m: int, x: F) -> tuple[bool, bool]:
    out = []
    for s in (-1, 0):
        out.append(phase(m, s, x)[1])
    return tuple(out)


def canonical_x(m: int) -> F:
    return frac(48 * A[m] - F(573, 4))


def comparator_x(n: int, m: int) -> F:
    return frac(F(63, 64) + 48 * (A[m] - A[n]))


eligible = []
membership_counts = {(False, False): 0, (False, True): 0,
                     (True, False): 0, (True, True): 0}
distinguishing = []
for n in range(N_MIN, N_MAX + 1):
    L = horizon(n)
    growth = [r for r in range(L) if lam[n + r + 1] > lam[n + r]]
    if len(growth) < 3:
        continue
    rs = tuple(growth[-3:])
    checkpoints = tuple(n + r + 1 for r in rs)
    canonical_bits = tuple(bad_pair(m, canonical_x(m)) for m in checkpoints)
    comparator_bits = tuple(bad_pair(m, comparator_x(n, m)) for m in checkpoints)
    for m in checkpoints:
        for s in (-1, 0):
            j = m + ell[m] + s
            canonical_y = phase(m, s, canonical_x(m))[0]
            comparator_y = phase(m, s, comparator_x(n, m))[0]
            assert canonical_y == center(q(j) * A[j])
            assert comparator_y == center(
                F(1, 4) + q(j) * (A[j] - A[n]) + F(63 * q(j), 3072)
            )
    canonical_in = all(all(pair) for pair in canonical_bits)
    comparator_in = all(all(pair) for pair in comparator_bits)
    membership_counts[(canonical_in, comparator_in)] += 1
    row = (n, L, rs, checkpoints, canonical_bits, comparator_bits)
    eligible.append(row)
    if comparator_in and not canonical_in:
        distinguishing.append(row)

assert len(eligible) == N_MAX - N_MIN + 1
assert eligible[0][0:4] == (65, 14, (10, 11, 12), (76, 77, 78))
assert eligible[0][4] == ((False, True), (True, True), (True, True))
assert eligible[0][5] == ((False, False), (False, True), (True, False))

print("range", N_MIN, N_MAX)
print("eligible", len(eligible))
print("membership (canonical, comparator)", membership_counts)
print("comparator-in/canonical-out", len(distinguishing))
for row in distinguishing[:20]:
    print("distinguishing", row)
