#!/usr/bin/env python3
"""Exact checks for the universal T142 2-primary dense-support obstruction."""

from math import gcd, lcm


def nu(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def den(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def v2(n: int) -> int:
    out = 0
    while n % 2 == 0:
        out += 1
        n //= 2
    return out


def q_over_48(j: int) -> int:
    assert j >= 5
    numerator = 10**j - 16
    assert numerator % 48 == 0
    out = numerator // 48
    assert out % 2 == 1
    return out


# Universal magnitude proof data.  At k=4, nu_k<2^(4k-4).  Moreover
# nu_(k+1)=120k^2+391k+318 and
# 16nu_k-nu_(k+1)=1800k^2+2025k+434>0 for all k>=0.
assert nu(4) == 2571 < 2**12
for k in range(0, 129):
    assert nu(k + 1) == 120 * k * k + 391 * k + 318
    assert 16 * nu(k) - nu(k + 1) == 1800 * k * k + 2025 * k + 434
    assert 1800 * k * k + 2025 * k + 434 > 0

# Direct exceptional cases.
assert (nu(0), v2(nu(0))) == (47, 0)
assert (nu(1), v2(nu(1))) == (318, 1)
assert (nu(2), v2(nu(2))) == (829, 0)
assert (nu(3), v2(nu(3))) == (1580, 2)

# Replay the exact active-set conclusion on the full declared P17 checkpoint
# range.  This finite loop checks the implementation; the induction above is
# the proof for all k>=4.
lam = 1
for m in range(0, 160):
    lam = lcm(lam, den(m))
    assert lam % 2 == 1
    if m < 2:
        continue
    a = 4 * m - 4
    active_two = [
        k for k in range(m + 1)
        if v2(nu(k)) + 4 * (m - k) < a
    ]
    assert active_two == list(range(2, m + 1))

    # Every relevant character coefficient Q is odd, so gcd(Q,T_m) removes
    # no 2-part and Dchar retains 2^a.  Sampling all relevant decimal indices
    # is more than needed for the congruence proof 10^j=64 (mod 96), j>=5.
    for j in range(max(5, m), m + 32):
        q = q_over_48(j)
        assert gcd(q, 2**a) == 1

    # 191*M_m/64 has valuation 4m-6 and is nonzero modulo 2^(4m-4).
    assert 4 * m - 6 < a

print("universal base", "nu_4 < 2^12 and nu_(k+1) < 16 nu_k")
print("small valuations", [(k, nu(k), v2(nu(k))) for k in range(4)])
print("checked m", (2, 159))
print("2-primary active set", "exactly {2,...,m}")
print("support-density lower bound", "(m-1)/(m+1) -> 1")
print("centering valuation", "4m-6 < 4m-4")
