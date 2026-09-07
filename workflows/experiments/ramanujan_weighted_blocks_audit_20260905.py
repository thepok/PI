"""Finite exact-integer experiment; not a proof of the infinite statements.

Reproduces the weighted-block checks in the 2026-09-05 Ramanujan note.
Standard library only; no files written and no Lean verification performed.
"""
from math import comb, inf

def v2(x: int):
    """2-adic valuation; v2(0) = infinity."""
    if x == 0:
        return inf
    x = abs(x)
    return (x & -x).bit_length() - 1

def s2(n: int) -> int:
    if n < 0:
        raise ValueError("s2 requires a nonnegative integer")
    return n.bit_count()

N = 300
c = [(6*n + 1) * comb(2*n, n)**3 for n in range(N + 1)]

rho = [1]
for n in range(1, N + 1):
    rho.append(-sum(c[j] * rho[n-j] for j in range(1, n + 1)))

# Q(z) = G(z)/(1 - 256z).
q = [1]
for n in range(1, N + 1):
    q.append(rho[n] + 256*q[n-1])

def linear_multiplier(a, coefficient):
    """Coefficients of (1 + coefficient*z) times the series a."""
    return [a[0]] + [
        a[n] + coefficient*a[n-1] for n in range(1, len(a))
    ]

R = linear_multiplier(rho, 56)
sigma128 = linear_multiplier(rho, -128)
sigma200 = linear_multiplier(rho, -200)
h200 = linear_multiplier(q, -200)
sigma8 = linear_multiplier(rho, -8)
h8 = linear_multiplier(q, -8)

for m in range(N + 1):
    assert v2(rho[m]) == 3*s2(m)
    assert v2(q[m]) == 3*s2(m)
    assert v2(sigma128[m]) == 3*s2(m)

assert R[1] == 0
assert h200[1] == 0
assert sigma200[1] == -256

for m in range(2, N + 1):
    expected = 3*s2(m) + (v2(m-1) if m % 2 else 0)
    assert v2(R[m]) == expected
    assert v2(h200[m]) == expected

    if m % 2:
        modulus = 1 << (expected + 1)
        assert (h200[m] - (56*c[m-1] - c[m])) % modulus == 0

checked = 0
for M in range(1, N + 1):
    W = 0
    weight = 1
    for L in range(1, M + 1):
        W += sigma200[M-L+1] * weight
        weight *= 256
        n = M - L

        assert W == h200[M] - (h200[n] << (8*L))

        if L >= 2:
            expected = 3*s2(M) + (v2(M-1) if M % 2 else 0)
            assert v2(W) == expected
            checked += 1

print("Verified P=1-200z blocks with L>=2:", checked)
print("M, v2(sigma_M for 1-8z), v2(h_M for 1-8z)")
for M in (9, 41, 105, 233):
    print(M, v2(sigma8[M]), v2(h8[M]))
