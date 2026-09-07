"""Exact finite falsification checks; not a proof of normality or novelty.

Run: python3 workflows/experiments/polynomial_feedback_20260907/check.py
Only the Python standard library is required.
"""

from fractions import Fraction
from math import factorial


def check_feedback():
    # b=10, p=3, F(X)=X^2, a=1, K=1.
    x, numerator, s = Fraction(1), 1, 0
    for n in range(7):
        assert x == Fraction(numerator, 3**n * 10**s)
        assert numerator % 3 != 0
        m = factorial(n + 1)
        coefficient = Fraction(3**n, 3 * 10**m)
        following = x + coefficient * x**2
        new_numerator = 3 * 10**(s + m) * numerator + numerator**2
        new_s = 2 * s + m
        assert following == Fraction(new_numerator, 3**(n + 1) * 10**new_s)
        assert new_numerator % 3 == numerator**2 % 3
        assert 1 <= following < Fraction(3, 2)
        numerator, s, x = new_numerator, new_s, following


def check_orbits():
    for b, p in [(10, 3), (2, 7), (10, 7)]:
        tau, residue = 1, b % p
        while residue != 1:
            residue = residue * b % p
            tau += 1
        kappa, z = 0, b**tau - 1
        while z % p == 0:
            kappa, z = kappa + 1, z // p
        for n in range(kappa, kappa + 4):
            q = p**n
            period = tau * p**(n - kappa)
            for a in [1, p + 1, q - 1]:
                orbit, r = [], a % q
                for _ in range(period):
                    orbit.append(r)
                    r = b * r % q
                assert r == a % q and len(set(orbit)) == period
                classes = {a * pow(b, j, p**kappa) % p**kappa for j in range(tau)}
                expected = {v for v in range(q) if v % p**kappa in classes}
                assert set(orbit) == expected
                for width in [b, b**2]:
                    counts = [0] * width
                    for v in orbit:
                        counts[width * v // q] += 1
                    assert all(abs(width * c - period) <= 2 * tau * width for c in counts)


def check_control():
    subset_sums, product, total = {0}, Fraction(1), 0
    for n in range(7):
        r = factorial(n + 1) + 1
        assert r > total
        shifted = {s + r for s in subset_sums}
        assert subset_sums.isdisjoint(shifted)
        subset_sums |= shifted
        total += r
        product *= 1 + Fraction(1, 10**r)
        assert product == sum((Fraction(1, 10**s) for s in subset_sums), Fraction())
    # All exponents occur at most once: finite products have coefficients 0/1.
    # The infinite no-carry/irrationality arguments require a separate proof.


if __name__ == "__main__":
    check_feedback()
    check_orbits()
    check_control()
    print("PASS: exact finite feedback, prime-power orbit, and avoiding-product checks")
    print("experiment only; no infinite digit-occurrence or novelty conclusion")
