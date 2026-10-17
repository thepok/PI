"""Exact finite checks for the source017 decimal-prefix interpolation audit.

These are falsification checks, not a proof of the general lemma.
Only Python's standard library is used.
"""

from fractions import Fraction as Q
from math import comb, gcd


def mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i + j] += ai * bj
    return c


def power(a, n):
    c = [Q(1)]
    for _ in range(n):
        c = mul(c, a)
    return c


def shift(a, x):
    return [sum(a[k] * comb(k, j) * x ** (k - j)
                for k in range(j, len(a))) for j in range(len(a))]


def value(a, x):
    y = Q(0)
    for c in reversed(a):
        y = y * x + c
    return y


def inverse(a, n):
    assert a[0] == 1
    b = [Q(1)]
    for k in range(1, n + 1):
        b.append(-sum(a[j] * b[k - j]
                      for j in range(1, min(k, len(a) - 1) + 1)))
    return b


def basis(centers, i, j, t):
    ai = centers[i]
    lagrange = [Q(1)]
    for ell, al in enumerate(centers):
        if ell != i:
            lagrange = mul(lagrange, [Q(-al, ai - al), Q(1, ai - al)])
    lagrange_power = power(lagrange, t + 1)
    local_inverse = inverse(shift(lagrange_power, ai), t - j)
    global_inverse = shift(local_inverse, -ai)
    return mul(mul(power([Q(-ai), Q(1)], j), lagrange_power), global_inverse)


def main():
    # The constructive direction of the source parameter regime.
    for nu in [Q(201, 100), Q(5, 2), Q(3), Q(7)]:
        b = (Q(1, 2) + 1 - 1 / nu) / 2
        delta = min(Q(1), (2 * b - 1) / b ** 2) / 2
        theta, a = 1 - delta, 1 - b * delta
        c = (a / theta + 1 / a) / 2
        bb = (a + min(1 / c, c * theta)) / 2
        eta = (nu * (a - theta) - (1 - theta)) / (2 * nu * a)
        assert 0 < theta < a < bb < 1
        assert c > 1 and bb < 1 / c and bb < c * theta < 1
        assert nu * (a * (1 - eta) - theta) > 1 - theta

    for deleted in range(10):
        digits = [d for d in range(10) if d != deleted]
        prefixes = [0]
        for n in range(1, 4):
            prefixes = [10 * a + d for a in prefixes for d in digits]
            for p in (2, 5):
                assert {a % (p ** n) for a in prefixes} == set(range(p ** n))

    def joint_polynomial(x):
        return 5 * x + 6 * x * (x - 1) * (x - 2) * (x - 3)

    assert all(gcd(joint_polynomial(x), 10) > 1 for x in range(9))
    assert gcd(joint_polynomial(9), 10) == 1
    print("PASS: 4 rational parameter witnesses, 60 residue-cover checks, "
          "and the joint-prime example.")

    cases = [
        (2, 1, [0, 3], 4),
        (2, 2, [0, 5, 2, 7], 2),
        (2, 3, [16, 1, 26, 3, 12, 5, 22, 7], 1),
        (3, 2, [18, 1, 11, 3, 22, 5, 15, 7, 35], 1),
        (5, 1, [10, 1, 7, 3, 24], 2),
    ]
    basis_count = 0
    value_count = 0
    packet_count = 0
    for p, n, centers, t in cases:
        m = p ** n
        assert len(centers) == m
        assert set(a % m for a in centers) == set(range(m))
        for i in range(m):
            for j in range(t + 1):
                h = basis(centers, i, j, t)
                assert len(h) <= m * (t + 1)
                for k, a in enumerate(centers):
                    packet = shift(h, a)[:t + 1]
                    assert packet == [Q(int(k == i and ell == j))
                                      for ell in range(t + 1)]
                    packet_count += t + 1
                for x in range(-25, 51):
                    assert value(h, x).denominator % p != 0
                    value_count += 1
                basis_count += 1
    print(f"PASS: {basis_count} exact Hermite basis polynomials; "
          f"{packet_count} cardinal Taylor coefficients; "
          f"{value_count} p-integral integer evaluations.")


if __name__ == "__main__":
    main()
