#!/usr/bin/env python3
"""Finite audit for sparse_20261016_arbitrary_corridors.md.

Exact integer counts and rational probability normalizations check the
uniform bridge law. Complex Fourier comparisons are floating-point
experiments, not certificates of an infinite assertion.
Only the Python standard library is required. No files are written.
"""

from cmath import exp
from fractions import Fraction
from itertools import product
from math import pi


def transition(word, state, digit):
    suffix = word[:state] + (digit,)
    if len(suffix) >= len(word) and suffix[-len(word):] == word:
        return None
    for end in range(len(word) - 1, -1, -1):
        if end == 0 or suffix[-end:] == word[:end]:
            return end
    raise AssertionError("zero state always exists")


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def matrix_power(a, n):
    result = [[int(i == j) for j in range(len(a))] for i in range(len(a))]
    while n:
        if n & 1:
            result = matmul(result, a)
        a = matmul(a, a)
        n //= 2
    return result


def counting_matrix(base, word):
    result = [[0] * len(word) for _ in word]
    for u in range(len(word)):
        for digit in range(base):
            v = transition(word, u, digit)
            if v is not None:
                result[u][v] += 1
    return result


def bridges(base, word, length, initial):
    states = [(0, initial)]
    for _ in range(length):
        following = []
        for value, u in states:
            for digit in range(base):
                v = transition(word, u, digit)
                if v is not None:
                    following.append((value * base + digit, v))
        states = following
    result = [[] for _ in word]
    for value, v in states:
        result[v].append(value)
    return result


def fourier_matrix(base, word, t):
    result = [[0j] * len(word) for _ in word]
    for u in range(len(word)):
        for digit in range(base):
            v = transition(word, u, digit)
            if v is not None:
                result[u][v] += exp(-2j * pi * digit * t)
    return result


def mask(values, t):
    return sum(exp(-2j * pi * value * t) for value in values) / len(values)


def audit_bridges():
    cases = [
        (10, (0, 0), 4),
        (10, (0, 1), 4),
        (10, (4, 9), 4),
        (10, (5, 0), 4),
        (10, (9, 9), 4),
        (3, (0, 0, 0), 6),
        (3, (0, 1, 0), 6),
        (3, (0, 1, 2), 6),
        (3, (2, 0, 2), 6),
    ]
    max_error = 0.0
    exact_pairs = 0
    fourier_pairs = 0
    for base, word, length in cases:
        counts = matrix_power(counting_matrix(base, word), length)
        values_by_start = [bridges(base, word, length, u) for u in range(len(word))]
        for u in range(len(word)):
            for v in range(len(word)):
                values = values_by_start[u][v]
                assert len(values) == counts[u][v] > 0
                assert len(values) * Fraction(1, counts[u][v]) == 1
                exact_pairs += 1
        for t in (0.0, 0.137 / base**length, 1.75 / base**length, 0.137):
            q = [[complex(i == j) for j in range(len(word))] for i in range(len(word))]
            for exponent in range(length - 1, -1, -1):
                q = matmul(q, fourier_matrix(base, word, base**exponent * t))
            for u in range(len(word)):
                for v in range(len(word)):
                    direct = mask(values_by_start[u][v], t)
                    matrix = q[u][v] / counts[u][v]
                    error = abs(direct - matrix)
                    assert error < 1e-10
                    max_error = max(max_error, error)
                    fourier_pairs += 1
    return len(cases), exact_pairs, fourier_pairs, max_error


def audit_dirty_block():
    base, word, length = 3, (0, 1), 4
    radix = base**length
    reference = (2, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0)
    states = [0]
    current = 0
    for index, digit in enumerate(reference, 1):
        current = transition(word, current, digit)
        assert current is not None
        if index % length == 0:
            states.append(current)
    # Both clean blocks end in nonzero state; no reset-state assumption.
    assert states[1] == states[2] == states[3] == 1
    first = bridges(base, word, length, states[0])[states[1]]
    last = bridges(base, word, length, states[2])[states[3]]
    forced = 0
    for digit in reference[length : 2 * length]:
        forced = forced * base + digit
    concatenated = [(a * radix + forced) * radix + c for a, c in product(first, last)]
    assert len(concatenated) * Fraction(1, len(first) * len(last)) == 1

    for value in concatenated:
        digits = []
        remainder = value
        for _ in range(3 * length):
            digits.append(remainder % base)
            remainder //= base
        digits.reverse()
        assert tuple(digits[length : 2 * length]) == reference[length : 2 * length]
        state = 0
        for digit in digits:
            state = transition(word, state, digit)
            assert state is not None

    max_error = 0.0
    for k in (0, 1, 2, 7, 19, 80, 81, 700):
        t = k / radix**3
        direct = mask(concatenated, t)
        factored = (
            mask(first, radix**2 * t)
            * exp(-2j * pi * forced * radix * t)
            * mask(last, t)
        )
        error = abs(direct - factored)
        assert error < 1e-10
        max_error = max(max_error, error)
    return len(concatenated), max_error


def main():
    cases, exact_pairs, fourier_pairs, bridge_error = audit_bridges()
    concatenations, dirty_error = audit_dirty_block()
    # Exact integer witness for the limiting short end of the stated range.
    m, r = 49, 500
    length = m * r
    d_m = 20 * m**4
    a_length = 4 * 10**(m - 1) * d_m**r
    assert a_length**6 < 10**length
    # log(10)<3 makes this dominate the post-horizon uniform mask bound.
    assert a_length > 2 + 3 * length
    assert 8 * 10**(m - 1) < 10**m
    print(f"PASS: {cases} models; {exact_pairs} exact bridge-count/normalization checks.")
    print(f"PASS: {fourier_pairs} finite Fourier comparisons; max error {bridge_error:.3g}.")
    print(f"PASS: {concatenations} legal concatenations with a frozen dirty block and nonzero boundary states.")
    print(f"PASS: independent block Fourier factorization; max error {dirty_error:.3g}.")
    print("PASS: exact m=49, r=500, L=24500 witness: A_L^6<10^L; entropy loss<1/500.")
    print("Status: experiment. No infinite dimension or Fourier-decay claim is certified.")


if __name__ == "__main__":
    main()

