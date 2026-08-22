#!/usr/bin/env python3
"""Exact T141 conductor identity and finite n=10..64 census.

The proof-level identity is h_pair=H.  The finite scan checks that neither
single phase closes the conductor on the predeclared P16 range.  No canonical
numerator, residue, carry, or phase cell is computed.
"""

from fractions import Fraction as F
from math import gcd, lcm, prod


def nu(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def den(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


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
    value = (n + 99) // 100
    while 10 ** (100 * value - n) * 5 ** (100 * n) < 8 ** (100 * n):
        value += 1
    assert 8 ** (100 * n) <= 10 ** (100 * value - n) * 5 ** (100 * n)
    assert 8 ** (100 * n) > 10 ** (100 * (value - 1) - n) * 5 ** (100 * n)
    return value


MAX_N = 120
Lambda: list[int] = []
A: list[F] = []
lam = 1
scale = 1
total = F(0)
for k in range(MAX_N + 1):
    lam = lcm(lam, den(k))
    Lambda.append(lam)
    total += F(nu(k), scale * den(k))
    A.append(total)
    scale *= 16


def delta(m: int, i: int) -> F:
    return (10 ** (m + i) - 16) * (A[m + i] - A[m])


def ell(m: int) -> int:
    i = 1
    while delta(m, i) < F(1, 4):
        i += 1
    return i


def q_over_48(j: int) -> int:
    assert j >= 4
    assert (10**j - 16) % 48 == 0
    return (10**j - 16) // 48


factorizations = [factor(den(k)) for k in range(65)]


def data(n: int) -> tuple[int, dict[int, int]]:
    primes = set().union(*(set(factorizations[k]) for k in range(n + 1)))
    lam_exp = {
        p: max(factorizations[k].get(p, 0) for k in range(n + 1))
        for p in primes
    }
    private: dict[int, int] = {}
    for p, a in lam_exp.items():
        occurrences = [k for k in range(n + 1) if p in factorizations[k]]
        if (p > 3 and len(occurrences) == 1
                and factorizations[occurrences[0]][p] == a):
            private[p] = a

    # T_n=16^n Lambda_n/48.  R_n removes its full 2-part and every
    # strongly-private p^a.  The remaining exponents factor H_n exactly.
    h_factor = {
        p: a for p, a in lam_exp.items() if p != 2 and p not in private
    }
    h_factor[3] -= 1
    h_factor = {p: a for p, a in h_factor.items() if a}
    h = prod(p**a for p, a in h_factor.items())

    t = 16**n * Lambda[n] // 48
    p_product = prod(p**a for p, a in private.items())
    b = (t & -t).bit_length() - 1
    r_modulus = 2**b * p_product
    assert t % r_modulus == 0 and t // r_modulus == h
    # D_1 contains 3^3, while division by 48 removes only one 3; hence
    # H_n is divisible by 9 for every screened n.
    assert h % 9 == 0
    return h, dict(sorted(h_factor.items()))


rows = []
for n in range(10, 65):
    h, h_factor = data(n)
    single = []
    for m in range(n, n + horizon(n) + 1):
        j0 = m + ell(m)
        q_minus = q_over_48(j0 - 1)
        q_zero = q_over_48(j0)
        assert q_zero == 10 * q_minus + 3
        assert q_minus % 3 == 1
        assert gcd(q_minus, q_zero) == 1

        h_minus = h // gcd(h, q_minus)
        h_zero = h // gcd(h, q_zero)
        assert lcm(h_minus, h_zero) == h
        single.extend(((h_minus, m, -1), (h_zero, m, 0)))

    assert all(period > 1 for period, _, _ in single)
    rows.append((n, horizon(n), h, h_factor, min(single), max(single)))

assert len(rows) == 55
assert rows[0][2] == 527_056_905_375
assert rows[0][3] == {3: 4, 5: 3, 7: 2, 11: 1, 13: 1,
                      17: 1, 19: 1, 23: 1}
assert rows[0][4] == (40_542_838_875, 10, 0)
assert rows[-1][2] == 32_787_361_060_559_456_552_179_544_854_263_702_748_353_948_016_667_601_508_675_938_310_875
assert rows[-1][4][0].bit_length() == 205

print("range/bases", (10, 64), len(rows))
print("all adjacent h_pair=H; all single h_s>1")
print("H bit range", min(r[2].bit_length() for r in rows),
      max(r[2].bit_length() for r in rows))
print("n=10 H/factor/min-single", rows[0][2], rows[0][3], rows[0][4])
print("n=64 H/factor/min-single", rows[-1][2], rows[-1][3], rows[-1][4])
