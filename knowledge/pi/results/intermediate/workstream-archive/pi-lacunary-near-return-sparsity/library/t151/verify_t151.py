#!/usr/bin/env python3
"""Exact finite experiments for T151; not a proof of its universal theorem."""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import factorial
from pathlib import Path


EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-T141-REPORT.md": "e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356",
    "prior-T143-REPORT.md": "b446b83025fd408fdbc8580e0e6871ab514ad169b0fe1d33407f6ad9061ca0d9",
    "prior-T145-REPORT.md": "17774f8020ddba63203d2a956e1edbd3e2d432a32cafde11386d35a3514d229c",
    "prior-T148-REPORT.md": "7a360dfc73ae9aa7c4582bc18f93cc06b7317f8fc1226b54fa0c11ca5fc223d7",
}


def digit_sum(n, p):
    total = 0
    while n:
        total += n % p
        n //= p
    return total


def valuation(n, p):
    total = 0
    while n and n % p == 0:
        total += 1
        n //= p
    return total


def factorial_ratio(n, a, b):
    numerator = 1
    denominator = 1
    for c in a:
        numerator *= factorial(c * n)
    for c in b:
        denominator *= factorial(c * n)
    assert numerator % denominator == 0
    return numerator // denominator


def factorial_valuation(n, p):
    total = 0
    power = p
    while power <= n:
        total += n // power
        power *= p
    return total


def ratio_valuation(n, p, a, b):
    return sum(factorial_valuation(c * n, p) for c in a) - sum(
        factorial_valuation(c * n, p) for c in b
    )


def landau(x, a, b):
    return sum((c * x.numerator) // x.denominator for c in a) - sum(
        (c * x.numerator) // x.denominator for c in b
    )


def atoms(a, b):
    points = {Fraction(0), Fraction(1)}
    for c in a + b:
        points.update(Fraction(m, c) for m in range(1, c))
    points = sorted(points)
    result = []
    for left, right in zip(points, points[1:]):
        middle = (left + right) / 2
        result.append((left, right, landau(middle, a, b)))
    return result


def ceil_log(p, m):
    h = 0
    power = 1
    while power < m:
        power *= p
        h += 1
    return h


def D_bound(p, m):
    d = 1
    while p**d - 1 <= m * m:
        d += 1
    return d


def atom_depth(p, left, right):
    for d in range(1, 64):
        q = p**d - 1
        for k in range(1, q):
            if left < Fraction(k, q) < right:
                return d, k
    raise AssertionError("depth search cap exhausted")


def state_for(x, a, b):
    return tuple((c * x.numerator) // x.denominator for c in a + b)


def potential(state, a):
    r = len(a)
    return sum(state[:r]) - sum(state[r:])


def step(state, digit, p, a, b):
    coeffs = a + b
    nxt = tuple((c * digit + carry) // p for c, carry in zip(coeffs, state))
    emitted = tuple(
        c * digit + carry - p * new
        for c, carry, new in zip(coeffs, state, nxt)
    )
    r = len(a)
    weight = sum(emitted[r:]) - sum(emitted[:r])
    assert weight == p * potential(nxt, a) - potential(state, a)
    return nxt, weight


def terminal(state, p, a):
    r = len(a)
    return sum(digit_sum(x, p) for x in state[r:]) - sum(
        digit_sum(x, p) for x in state[:r]
    )


def digits_lsdf(n, p, length):
    result = []
    for _ in range(length):
        result.append(n % p)
        n //= p
    assert n == 0
    return result


def run_word(digits, p, a, b, start=None):
    state = (0,) * (len(a) + len(b)) if start is None else start
    total = 0
    potentials = [potential(state, a)]
    for digit in digits:
        state, weight = step(state, digit, p, a, b)
        total += weight
        potentials.append(potential(state, a))
    return state, total, terminal(state, p, a), potentials


def verify_model(p, a, b, n_cap):
    assert a and b and sum(a) == sum(b) and sorted(a) != sorted(b)
    m = max(a + b)
    table = atoms(a, b)
    assert all(height >= 0 for _, _, height in table)
    positives = [row for row in table if row[2] > 0]
    assert positives
    for left, right, height in positives:
        d, k = atom_depth(p, left, right)
        assert d <= D_bound(p, m)
        q = p**d - 1
        x = Fraction(k, q)
        qx = state_for(x, a, b)
        period = digits_lsdf(k, p, d)
        end, weight, _, potentials = run_word(period, p, a, b, qx)
        assert end == qx
        assert potentials[0] == height
        assert all(phi >= 0 for phi in potentials)
        assert weight == (p - 1) * sum(potentials[:-1])
        assert Fraction(weight, d) >= Fraction((p - 1) * height, d)

        h = ceil_log(p, m)
        t = d + h
        scaled = p**t * x
        access_value = (scaled.numerator + scaled.denominator - 1) // scaled.denominator
        assert 0 <= access_value < p**t
        access = digits_lsdf(access_value, p, t)
        reached, _, _, access_potentials = run_word(access, p, a, b)
        assert reached == qx
        flushed, _, _, flush_potentials = run_word([0] * h, p, a, b, qx)
        assert flushed == (0,) * len(qx)
        assert all(phi >= 0 for phi in access_potentials + flush_potentials)

        closed = access + period + [0] * h
        end, closed_weight, _, closed_potentials = run_word(closed, p, a, b)
        assert end == (0,) * len(qx)
        assert len(closed) == 2 * d + 2 * h
        assert closed_weight == (p - 1) * sum(closed_potentials[:-1])
        assert closed_weight >= (p - 1) * height

        for repetitions in range(8):
            repeated = access + period * repetitions
            n_value = sum(digit * p**i for i, digit in enumerate(repeated))
            end, edge_total, tau, _ = run_word(repeated, p, a, b)
            assert end == qx
            value = ratio_valuation(n_value, p, a, b)
            assert edge_total + tau == (p - 1) * value
            if repetitions:
                previous = access + period * (repetitions - 1)
                prev_n = sum(digit * p**i for i, digit in enumerate(previous))
                prev_value = ratio_valuation(prev_n, p, a, b)
                assert (p - 1) * (value - prev_value) == weight

    for n in range(21):
        factorial_ratio(n, a, b)

    for length in range(0, 7):
        for ds in product(range(p), repeat=length):
            n = sum(digit * p**i for i, digit in enumerate(ds))
            if n >= n_cap:
                continue
            end, edge_total, tau, _ = run_word(ds, p, a, b)
            value = ratio_valuation(n, p, a, b)
            assert edge_total + tau == (p - 1) * value
            assert potential(end, a) == landau(Fraction(n, p**length), a, b)
    return len(table), len(positives)


def main():
    root = Path(__file__).resolve().parent
    for name, digest in EXPECTED.items():
        actual = sha256((root / name).read_bytes()).hexdigest()
        assert actual == digest, (name, actual)
    print("EXPERIMENT: pinned input hashes OK")

    displayed = verify_model(2, (3,), (1, 1, 1), 4096)
    assert displayed == (3, 2)
    left, right, height = Fraction(1, 3), Fraction(2, 3), 1
    d, k = atom_depth(2, left, right)
    assert (d, k) == (3, 3)
    assert ceil_log(2, 3) == 2 and D_bound(2, 3) == 4
    print("EXPERIMENT: displayed model atoms=3 positive=2 d=3 H=2 D=4")

    count = 0
    for parts in ((1, 1), (1, 2), (1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 3)):
        a = (sum(parts),)
        b = tuple(parts)
        if sorted(a) == sorted(b):
            continue
        for p in (2, 3, 5):
            atom_count, positive_count = verify_model(p, a, b, 2000)
            print(
                "EXPERIMENT:",
                f"p={p} a={a} b={b} atoms={atom_count} positive={positive_count}",
            )
            count += 1
    assert count == 18
    print("EXPERIMENT: bounded multinomial census models=18 OK")
    print("EXPERIMENT: finite computations do not prove the universal theorem")


if __name__ == "__main__":
    main()
