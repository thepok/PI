"""Experiment: exact finite calibration of the scalar Cantor norm bound.

Checks balanced nodes and interpolation coefficients, not a transcendence
theorem, an infinite supremum, or any decimal assertion about pi.
"""

from fractions import Fraction as F
from itertools import product


def times_linear(poly, root):
    out = [F(0)] * (len(poly) + 1)
    for j, coefficient in enumerate(poly):
        out[j] -= root * coefficient
        out[j + 1] += coefficient
    return out


def evaluate(poly, x):
    out = F(0)
    for coefficient in reversed(poly):
        out = out * x + coefficient
    return out


def check(d, forbidden_word):
    # Omitting one letter omits the entire word. The infinite tail is a,
    # not zero: zero padding could create a forbidden word.
    omitted = int(forbidden_word[0])
    a, b = [digit for digit in range(10) if digit != omitted][:2]
    delta = b - a
    n = 1
    k = 0
    while n < d + 1:
        n *= 2
        k += 1
    assert d + 1 <= n <= 2 * d
    bits = list(product((0, 1), repeat=k))
    nodes = [F(3) + F(a, 9) + delta * sum(
        (F(bit, 10 ** j) for j, bit in enumerate(word, 1)), F(0))
        for word in bits]
    assert len(set(nodes)) == n and all(3 <= x <= 4 for x in nodes)
    for word in bits:
        shown = ''.join(str(a + delta * bit) for bit in word)
        shown += str(a) * len(forbidden_word)
        assert forbidden_word not in shown
    total_depth = sum(j * 2 ** (k - j) for j in range(1, k + 1))
    assert total_depth == 2 * n - k - 2
    denominator_floor = F(8 * delta, 9) ** (n - 1) / 10 ** total_depth
    lagrange = []
    for i, x in enumerate(nodes):
        den, numerator = F(1), [F(1)]
        for j, y in enumerate(nodes):
            if i == j:
                continue
            depth = next(r for r in range(k) if bits[i][r] != bits[j][r]) + 1
            assert abs(x - y) >= F(8 * delta, 9 * 10 ** depth)
            den *= x - y
            numerator = times_linear(numerator, y)
        assert abs(den) >= denominator_floor
        assert sum(map(abs, numerator)) <= 5 ** (n - 1)
        lagrange.append([coefficient / den for coefficient in numerator])
    operator_bound = max(sum(abs(row[j]) for row in lagrange) for j in range(n))
    exact_bound = F(n * 5 ** (n - 1), 1) / denominator_floor
    assert exact_bound == F(1, 5 ** k) * F(1125, 2 * delta) ** (n - 1)
    assert operator_bound <= exact_bound <= 600 ** (2 * d)
    polynomial = [F((-1) ** j * (j + 1)) for j in range(d + 1)]
    values = [evaluate(polynomial, x) for x in nodes]
    reconstructed = [sum(values[i] * lagrange[i][j] for i in range(n))
                     for j in range(n)]
    assert reconstructed == polynomial + [F(0)] * (n - d - 1)
    assert max(map(abs, polynomial)) <= exact_bound * max(map(abs, values))


if __name__ == "__main__":
    for word in ("0", "12", "987"):
        for degree in (1, 2, 3, 4, 7, 8):
            check(degree, word)
    assert 3 ** 12 > 600 ** 2
    print("PASS: exact Cantor nodes, Lagrange bounds, reconstruction, scalar constants")
