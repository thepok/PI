#!/usr/bin/env python3
"""Exact finite checks accompanying the T34 prose counterexamples."""

from fractions import Fraction
from itertools import product
from math import comb


def dirac_affinity(depth: int, cutoff: int) -> int:
    x = (0,) * (cutoff + 1)
    y = (0,) * cutoff + (1,)
    return int(x[:depth] == y[:depth])


def bernoulli_collision(one_probability: Fraction, depth: int) -> Fraction:
    zero_probability = 1 - one_probability
    total = Fraction(0)
    for word in product((0, 1), repeat=depth):
        probability = Fraction(1)
        for digit in word:
            probability *= one_probability if digit else zero_probability
        total += probability * probability
    return total


def quad3_mul(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]):
    """Multiply a+b*sqrt(3), represented exactly by the pair (a,b)."""
    a, b = left
    c, d = right
    return a * c + 3 * b * d, a * d + b * c


def quad3_pow(value: tuple[Fraction, Fraction], exponent: int):
    result = (Fraction(1), Fraction(0))
    for _ in range(exponent):
        result = quad3_mul(result, value)
    return result


cutoff = 6
dirac_values = [dirac_affinity(m, cutoff) for m in range(cutoff + 2)]
assert dirac_values == [1] * (cutoff + 1) + [0]

for m in range(8):
    assert bernoulli_collision(Fraction(1, 2), m) == Fraction(1, 2) ** m
    assert bernoulli_collision(Fraction(3, 4), m) == Fraction(5, 8) ** m

    # By the binomial theorem, A_m^2=(1/2+sqrt(3)/4)^m.  Check its
    # exact expansion in Q(sqrt(3)), independently of repeated multiplication.
    expanded = (Fraction(0), Fraction(0))
    for k in range(m + 1):
        coefficient = Fraction(comb(m, k), 2 ** (m - k) * 4**k)
        if k % 2 == 0:
            term = (coefficient * 3 ** (k // 2), Fraction(0))
        else:
            term = (Fraction(0), coefficient * 3 ** ((k - 1) // 2))
        expanded = (expanded[0] + term[0], expanded[1] + term[1])
    assert expanded == quad3_pow((Fraction(1, 2), Fraction(1, 4)), m)

# ((1+sqrt(3))/(2*sqrt(2)))^2 < 1 is equivalent to 2*sqrt(3) < 4,
# and squaring positive sides reduces this to the exact integer check 12 < 16.
assert 12 < 16

print("Dirac affinities through cutoff 6:", dirac_values)
print("Bernoulli(1/2) collision base:", Fraction(1, 2))
print("Bernoulli(3/4) collision base:", Fraction(5, 8))
print("Cross-affinity base squared is < 1: exact check 12 < 16")
print("T34 counterexample checks: PASS")
