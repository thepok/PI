#!/usr/bin/env python3
"""Exact finite checks of the full word/power-lattice equality.

The all-N proof is in ATTEMPT_LEDGER.md, under the logarithmic holonomy
entry. These Fraction calculations are experiments, not that proof or a
pi-digit result. No external packages or decimal pi data are used.
"""

from fractions import Fraction
from itertools import combinations
from math import comb, factorial


def vp(value, prime):
    assert value != 0
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def valuation(value, prime):
    return vp(value.numerator, prime) - vp(value.denominator, prime)


def witness(depth, degree, word, prime):
    assert depth >= 1 and 1 <= degree < prime**depth
    assert word and all(char in "0123456789" for char in word)
    starts = (1, 3) if prime == 2 else (0, 5)
    start = next(u for u in starts if int(word[0]) not in range(u, u + prime))
    offset = start * (10**depth - 1) // 9
    nodes = [
        offset + sum((i // prime**r % prime) * 10**r for r in range(depth))
        for i in range(degree + 1)
    ]
    assert len(set(nodes)) == degree + 1
    assert all(0 <= a < 10**depth for a in nodes)
    assert all(word not in str(a).zfill(depth) for a in nodes)
    for i, j in combinations(range(degree + 1), 2):
        assert vp(nodes[j] - nodes[i], prime) == vp(j - i, prime)
    return nodes


def matrix(nodes, depth, degree):
    return [
        [comb(degree, j) * (-Fraction(a, 10**depth)) ** (degree - j)
         for a in nodes]
        for j in range(degree + 1)
    ]


def solve(left, right):
    """Return det(left) and the exact change-of-basis matrix left^-1 right."""
    size = len(left)
    rows = [list(a) + list(b) for a, b in zip(left, right)]
    determinant = Fraction(1)
    for col in range(size):
        pivot = next(row for row in range(col, size) if rows[row][col])
        if pivot != col:
            rows[pivot], rows[col] = rows[col], rows[pivot]
            determinant = -determinant
        scale = rows[col][col]
        determinant *= scale
        rows[col] = [value / scale for value in rows[col]]
        for row in range(size):
            if row != col:
                scale = rows[row][col]
                rows[row] = [a - scale * b for a, b in zip(rows[row], rows[col])]
    change = [row[size:] for row in rows]
    assert all(
        sum(left[i][k] * change[k][j] for k in range(size)) == right[i][j]
        for i in range(size) for j in range(size)
    )
    return determinant, change


def expected(depth, degree, prime):
    return (
        -depth * comb(degree + 1, 2)
        + sum(vp(comb(degree, j), prime) for j in range(degree + 1))
        + sum(vp(factorial(j), prime) for j in range(1, degree + 1))
    )


def main():
    for prime, depth, degree in ((2, 3, 7), (5, 2, 7)):
        for word in ("0", "99", "12"):
            nodes = witness(depth, degree, word, prime)
            restricted = matrix(nodes, depth, degree)
            consecutive = matrix(range(degree + 1), depth, degree)
            for left, right in ((restricted, consecutive), (consecutive, restricted)):
                determinant, change = solve(left, right)
                assert valuation(determinant, prime) == expected(depth, degree, prime)
                assert all(value.denominator % prime for row in change for value in row)
            print(f"p={prime}, N={depth}, m={degree}, w={word}: equal lattice bases")

    # Independently enumerate all maximal minors only in tiny one-digit sets.
    for prime, degree in ((2, 1), (5, 3)):
        for word in (None, "0", "99", "12"):
            nodes = [a for a in range(10) if word is None or word not in str(a)]
            minimum = min(
                sum(vp(b - a, prime) for a, b in combinations(subset, 2))
                for subset in combinations(nodes, degree + 1)
            )
            assert minimum == sum(vp(factorial(j), prime) for j in range(1, degree + 1))
    print("PASS: exact witnesses, determinant valuations, both basis changes, tiny minima")


if __name__ == "__main__":
    main()
