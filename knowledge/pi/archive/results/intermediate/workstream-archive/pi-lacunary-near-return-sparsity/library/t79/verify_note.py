#!/usr/bin/env python3
"""Self-contained exact-arithmetic replay for T79; Python standard library only."""

from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path


EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "abrarov-quine-1706.08835v3.pdf": "7500ccc8cb55f651b81dd6310f02e428d2455ca6739dfb0c382435bfac8b6c3c",
    "abrarov-quine-1706.08835v3.txt": "b5e8eff87327d624abffd4d1e45258e2ba8b5487f8b555c21b1b5fccd7e91d94",
    "bailey-crandall-2002.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "bailey-crandall-2002.txt": "bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47",
}
P = 147153121
B = 1758719


def file_hash(name):
    return sha256(Path(name).read_bytes()).hexdigest()


def valuation(value, prime):
    assert value > 0
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def is_prime_trial(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def factor(value):
    """Factor the supplied moduli; P is the fixed prime certified below."""
    assert value > 0
    result = {}
    while value % P == 0:
        result[P] = result.get(P, 0) + 1
        value //= P
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result[value] = result.get(value, 0) + 1
    return result


def euler_phi(factors):
    value = 1
    for prime, exponent in factors.items():
        value *= (prime - 1) * prime ** (exponent - 1)
    return value


def multiplicative_order_10(modulus):
    assert modulus > 0 and gcd(10, modulus) == 1
    phi = euler_phi(factor(modulus))
    order = phi
    for prime in factor(phi):
        while order % prime == 0 and pow(10, order // prime, modulus) == 1:
            order //= prime
    assert pow(10, order, modulus) == 1
    for prime in factor(order):
        assert pow(10, order // prime, modulus) != 1
    return order


def cmul(left, right):
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def cpow(base, exponent):
    result = (Fraction(1), Fraction(0))
    while exponent:
        if exponent & 1:
            result = cmul(result, base)
        base = cmul(base, base)
        exponent //= 2
    return result


def partial_sum(terms):
    total = Fraction(0)
    for r in range(terms):
        total += Fraction(32 * (-1) ** r, (2 * r + 1) * 10 ** (2 * r + 1))
        total -= Fraction(4 * (-1) ** r * B ** (2 * r + 1),
                          (2 * r + 1) * P ** (2 * r + 1))
    return total


def tail_collision_count(length, order):
    return sum(((length - 1 - residue) // order + 1) ** 2
               for residue in range(min(length, order)))


def check_machin_specialization():
    ratio = (Fraction(99, 101), Fraction(20, 101))
    eighth = cpow(ratio, 8)
    assert eighth == (Fraction(-258800989811999, 10828567056280801),
                      Fraction(10825473963759840, 10828567056280801))
    real, imag_minus_one = eighth[0], eighth[1] - 1
    norm = real * real + imag_minus_one * imag_minus_one
    u2 = (2 * real / norm, -2 * imag_minus_one / norm - 1)
    assert u2 == (Fraction(-P, B), Fraction(0))
    assert P > 80 * B
    print("Machin specialization: k=4, u1=10, u2=-147153121/1758719")


def main():
    for name, expected in EXPECTED_HASHES.items():
        actual = file_hash(name)
        assert actual == expected, (name, actual, expected)
    print("source hashes: verified (5 files)")

    assert is_prime_trial(P)
    assert factor(P) == {P: 1}
    check_machin_specialization()

    expected = {
        1: (0, 1, {P: 1}),
        2: (0, 3, {P: 3}),
        3: (0, 6, {P: 5}),
        4: (2, 7, {7: 1, P: 7}),
        5: (4, 9, {7: 1, P: 9}),
        6: (6, 11, {7: 1, 11: 1, P: 11}),
        7: (8, 13, {7: 1, 11: 1, P: 13}),
        8: (10, 16, {7: 1, 11: 1, P: 15}),
    }
    rows = []
    for terms, (want_a, want_b, want_factors) in expected.items():
        value = partial_sum(terms)
        numerator, denominator = value.numerator, value.denominator
        assert gcd(numerator, denominator) == 1 and denominator > 0
        a, b = valuation(denominator, 2), valuation(denominator, 5)
        modulus = denominator // (2 ** a * 5 ** b)
        factors = factor(modulus)
        order = multiplicative_order_10(modulus)
        assert (a, b, factors) == (want_a, want_b, want_factors)
        assert factors[P] == 2 * terms - 1
        assert modulus >= P ** (2 * terms - 1)
        rows.append((terms, a, b, max(a, b), modulus, order))
        print(f"K={terms}: v2={a}, v5={b}, t={max(a,b)}, "
              f"m_factors={factors}, ord10={order}")

    k, n, prefix = 8, 1, 11
    assert prefix + n + 4 <= 2 * k
    assert rows[-1][3] >= prefix
    print("uniform schedule: K=8, n=1, N=11; N+n+4<=2K and N<=t")

    k, _a, _b, transient, _m, order = rows[3]
    length = 10
    assert order > length
    assert tail_collision_count(length, order) == length
    print("tail collisions: K=4, tail length=10, exact ordered count=10")

    k = 8
    assert 2 * k - 1 < P
    assert P ** 7 > 11
    print("prime-power scale: K=8 gives sqrt(m) >= P^(15/2) > 11")
    print("all exact-arithmetic checks passed")


if __name__ == "__main__":
    main()
