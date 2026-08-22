#!/usr/bin/env python3
"""Exact T132 three-checkpoint carry census; finite evidence only."""

from collections import Counter
from fractions import Fraction as F

N_MIN, N_MAX = 6, 512


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
    lhs = 6 * (n + 1) ** 2 * 8**n
    h = 0
    while lhs >= 10**h * 5**n:
        h += 1
    return h


max_checkpoint = max(n + horizon(n) + 3 for n in range(N_MIN, N_MAX + 1))
A: list[F] = []
total = F(0)
scale = 1
for n in range(2 * max_checkpoint + 33):
    total += F(nu(n), scale * den(n))
    A.append(total)
    scale *= 16


def delta(n: int, i: int) -> F:
    return q(n + i) * (A[n + i] - A[n])


ELL: dict[int, int] = {}
for n in range(N_MIN, max_checkpoint + 3):
    i = 1
    while delta(n, i) < F(1, 4):
        i += 1
    ELL[n] = i


def phase(n: int, s: int, x: F) -> tuple[int, F, bool]:
    j = n + ELL[n] + s
    raw = F(1, 4) + delta(n, ELL[n] + s) + F(q(j), 48) * x
    z = floor(raw + F(1, 2))
    y = raw - z
    return z, y, abs(y) >= F(1, 4) - eps(j)


def checkpoint(n: int, x: F):
    minus = phase(n, -1, x)
    plus = phase(n, 0, x)
    return minus[2] and plus[2], plus[0] - 10 * minus[0], minus, plus


def canonical_x(n: int) -> F:
    return frac(48 * A[n] - F(573, 4))


def comparator_x(base: int, n: int) -> F:
    return frac(F(63, 64) + 48 * (A[n] - A[base]))


canonical_rows, comparator_rows = [], []
direct_checks = comparator_checks = 0
for N in range(N_MIN, N_MAX + 1):
    H = horizon(N)
    for c in range(4):
        start = N + H + c - 2
        ns = (start, start + 1, start + 2)
        cps = [checkpoint(n, canonical_x(n)) for n in ns]
        for n, cp in zip(ns, cps):
            for s, data in ((-1, cp[2]), (0, cp[3])):
                assert data[1] == center(q(n + ELL[n] + s) * A[n + ELL[n] + s])
                direct_checks += 1
        if all(cp[0] for cp in cps):
            canonical_rows.append((N, c, start, tuple(cp[1] for cp in cps)))

        cps = [checkpoint(n, comparator_x(N, n)) for n in ns]
        for n, cp in zip(ns, cps):
            for s, data in ((-1, cp[2]), (0, cp[3])):
                j = n + ELL[n] + s
                expected = center(F(1, 4) + q(j) * (A[j] - A[N]) + F(63 * q(j), 3072))
                assert data[1] == expected
                comparator_checks += 1
        if all(cp[0] for cp in cps):
            comparator_rows.append((N, c, start, tuple(cp[1] for cp in cps)))


starts = sorted({row[2] for row in canonical_rows})
raw_words = {row[3] for row in canonical_rows}
defect_words, sign_words, combined_words = [], [], []
for start in starts:
    defects, signs, combined = [], [], []
    for n in (start, start + 1, start + 2):
        x = canonical_x(n)
        cp = checkpoint(n, x)
        D = F(1, 4) + delta(n, ELL[n]) - 10 * (F(1, 4) + delta(n, ELL[n] - 1)) + 3 * x
        defect = cp[1] - floor(D + F(1, 2))
        sign = ("-" if cp[2][1] < 0 else "+", "-" if cp[3][1] < 0 else "+")
        defects.append(defect)
        signs.append(sign)
        combined.append((defect, sign))
    defect_words.append(tuple(defects))
    sign_words.append(tuple(signs))
    combined_words.append(tuple(combined))

print("direct checks", direct_checks, comparator_checks)
print("canonical rows/starts/raw words", len(canonical_rows), len(starts), len(raw_words))
print("canonical starts", starts)
print("comparator rows/index starts/words", len(comparator_rows), len({r[2] for r in comparator_rows}), len({r[3] for r in comparator_rows}))
print("defect/sign/combined words", len(set(defect_words)), len(set(sign_words)), len(set(combined_words)))
print("repeated defects", sorted((k, v) for k, v in Counter(defect_words).items() if v > 1))

