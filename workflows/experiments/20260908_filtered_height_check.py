"""Exact finite checks for the filtered-generator/decimal-height ledger note.

Status: experiment, not an all-index proof, analytic verification, or pi-digit
test. Uses only tracked formulas and Python's standard library; no pi data.
"""

from fractions import Fraction as F
from math import comb, gcd, isqrt, lcm


def product(a, b, order):
    return [sum((a[j] * b[k - j] for j in range(k + 1)), F())
            for k in range(order + 1)]


def valuation(a, p):
    assert a > 0
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def check_series():
    order = 37
    caps = [1]
    for k in range(1, order + 1):
        caps.append(lcm(caps[-1], k))
    a, t = [F()] * (order + 1), [F()] * (order + 1)
    for n in range(order // 2 + 1):
        a[2 * n] = F(comb(2 * n, n))
        t[2 * n + 1] = F(-4 * comb(2 * n, n), 2 * n + 1)
    b_series = product(a, t, order)
    t_squared = product(t, t, order)
    for beta in (F(0), F(7, 11), F(37, 10)):
        h = [b_series[k] - beta * a[k] for k in range(order + 1)]
        h_squared = product(h, h, order)
        g = [t_squared[k] - 2 * beta * t[k] for k in range(order + 1)]
        # Independent ODE recurrence: Q G''-4z G'=32, G(0)=0, G'(0)=8 beta.
        g_ode = [F(), 8 * beta]
        for k in range(order - 1):
            g_ode.append((4 * k * k * g_ode[k] + (32 if k == 0 else 0))
                         / ((k + 2) * (k + 1)))
        assert g == g_ode
        for k in range(order + 1):
            qh_squared = h_squared[k] - (4 * h_squared[k - 2] if k >= 2 else 0)
            assert g[k] == qh_squared - (beta * beta if k == 0 else 0)
            assert (beta.denominator * caps[k] * h[k]).denominator == 1
            assert (beta.denominator * caps[k] * caps[k // 2] * g[k]).denominator == 1
            if k < order:
                assert (k + 1) * g[k + 1] == -8 * h[k]
        for n in range((order - 1) // 2 + 1):
            assert g[2 * n + 1] == 8 * beta * F(comb(2 * n, n), 2 * n + 1)
        for n in range(1, order // 2 + 1):
            assert g[2 * n] == F(2 * 16**n, n * n * comb(2 * n, n))

        # K'=H/(1-z), calculated both from component sums and this recurrence.
        k_series = [F()]
        for k in range(1, order + 1):
            ka = sum(a[:k], F()) / k
            kb = sum(b_series[:k], F()) / k
            k_series.append(kb - beta * ka)
            assert (k * ka).denominator == 1
            assert (k * caps[k - 1] * kb).denominator == 1
            assert (beta.denominator * caps[k]**2 * k_series[k]).denominator == 1
            assert k * k_series[k] - (k - 1) * k_series[k - 1] == h[k - 1]

        # Test actual coefficient offsets of each row of the finite lattice.
        rows = [[F(1)] + [F()] * order, h, g]
        for depth in range(1, 9):
            scales = (F(1, caps[depth]**2),
                      F(beta.denominator, caps[depth]), F(beta.denominator))
            for k in range(3 * depth + 4):
                clearing = caps[max(k, depth)] * caps[max(k // 2, depth)]
                for row, scale in zip(rows, scales):
                    for j in range(depth + 1):
                        index = k - depth + j
                        coefficient = row[index] if index >= 0 else F()
                        assert (clearing * scale * coefficient).denominator == 1

    integral = F(2) + F(5, 2) + F(15, 4)
    assert integral == F(33, 4)
    assert integral - 3 == F(9, 2) * F(7, 6)
    assert (3 * F(3, 2) + 5 * F(3, 2)) / 9 == F(4, 3)
    assert 1 - (1 - F(2, 3))**2 == F(8, 9)


def check_decimal_residues():
    for s in range(1, 6):
        for digit in (2, 4, 6, 8):
            assert valuation(5 * 10**s + digit, 2) <= 4
            assert valuation(digit * 10**s + 5, 5) <= 2
            if s >= 4:
                assert valuation(5 * 10**s + digit, 2) == valuation(digit, 2)
                assert valuation(digit * 10**s + 5, 5) == 1
    for a in range(1, 10000):
        if a % 10 and gcd(a, 10**4) > 25:
            assert ((a % 10 in (2, 4, 6, 8) and valuation(a, 2) >= 5)
                    or (a % 10 == 5 and valuation(a, 5) >= 3))

    # Prefix check of the explicit irrational control; irrationality itself
    # follows from the nonperiodic square positions, not this finite loop.
    a, power, good = 3, 1, []
    for n in range(1, 401):
        digit = 2 if isqrt(n)**2 == n else 1
        a, power = 10 * a + digit, 10 * power
        reduction = gcd(a, power)
        good.append(reduction <= 25)
        assert F(1, 9) * (1 - F(1, power)) <= F(a, power) - 3
        assert F(a, power) - 3 <= F(2, 9) * (1 - F(1, power))
        assert F(a, power).denominator == power // reduction
        if n >= 3:
            assert any(good[-3:])


if __name__ == "__main__":
    check_series()
    check_decimal_residues()
    print("PASS: exact G identities/ODE, H/G/K denominator caps, lattice offsets,")
    print("      leading arithmetic costs, alternating valuations, avoiding control.")
    print("EXPERIMENT ONLY: no all-index, analytic, or pi-digit assertion proved.")
