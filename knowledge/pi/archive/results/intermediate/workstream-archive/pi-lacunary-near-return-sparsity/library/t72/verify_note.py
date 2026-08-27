#!/usr/bin/env python3
"""Self-contained finite replay for the T72 metric-calibration note."""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path


EXPECTED_CANONICAL_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def nu10(n: int) -> int:
    assert n >= 1
    value = 0
    while n % 10 == 0:
        value += 1
        n //= 10
    return value


def weight(r: int, u: int) -> Fraction:
    return Fraction(r - u, r)


def terminal_shell(h: int) -> range:
    return range(h // 10 + 1, h + 1)


def collision_pair(ell: int, j: int, jp: int) -> tuple[int, int]:
    assert 0 <= j < jp < ell
    s = ell - j
    t = ell - jp
    g = gcd(s, t)
    repunit_gcd = 10**g - 1
    a = (10**s - 1) // repunit_gcd
    b = 10 ** (jp - j) * (10**t - 1) // repunit_gcd
    assert gcd(a, b) == 1
    return a, b


def sum_squares(n: int) -> int:
    return n * (n + 1) * (2 * n + 1) // 6


def fejer_frequency_dictionary(ell: int, h: int) -> dict[int, Fraction]:
    r = h + 1
    frequencies: dict[int, Fraction] = defaultdict(Fraction)
    for j in range(ell):
        d = 10**ell - 10**j
        for u in range(1, h + 1):
            w = weight(r, u)
            frequencies[u * d] += w
            frequencies[-u * d] += w
    return frequencies


def fejer_variance_dictionary(ell: int, h: int) -> Fraction:
    frequencies = fejer_frequency_dictionary(ell, h)
    return sum(value * value for value in frequencies.values())


def weighted_linear_sum(p: int, q: int, a: int, b: int, r: int) -> Fraction:
    if p > q:
        return Fraction(0)
    count = q - p + 1
    sum_q = (q * (q + 1) - (p - 1) * p) // 2
    sum_q2 = (
        q * (q + 1) * (2 * q + 1) - (p - 1) * p * (2 * p - 1)
    ) // 6
    return Fraction(count) - Fraction((a + b) * sum_q, r) + Fraction(
        a * b * sum_q2, r * r
    )


def fejer_variance_formula(ell: int, h: int) -> Fraction:
    r = h + 1
    diagonal = Fraction(ell * h * (2 * h + 1), 3 * r)
    collisions = Fraction(0)
    for j in range(ell):
        for jp in range(j + 1, ell):
            a, b = collision_pair(ell, j, jp)
            collisions += 4 * weighted_linear_sum(1, h // a, a, b, r)
    return diagonal + collisions


def direct_variance_dictionary(ell: int, h: int) -> tuple[Fraction, Fraction]:
    r = h + 1
    positive: dict[int, Fraction] = defaultdict(Fraction)
    total_weight = Fraction(0)
    for u in terminal_shell(h):
        w = weight(r, u)
        for j in range(ell):
            frequency = u * (10**ell - 10**j)
            positive[frequency] += w
            total_weight += w
    expectation = 2 * total_weight
    variance = 2 * sum(value * value for value in positive.values())
    return expectation, variance


def direct_variance_formula(ell: int, h: int) -> tuple[Fraction, Fraction]:
    r = h + 1
    h0 = h // 10
    low = h0 + 1
    n = h - h0
    expectation = Fraction(ell * n * (n + 1), r)
    variance = Fraction(ell * n * (n + 1) * (2 * n + 1), 3 * r * r)
    for j in range(ell):
        for jp in range(j + 1, ell):
            a, b = collision_pair(ell, j, jp)
            p = (low + b - 1) // b
            q = h // a
            variance += 4 * weighted_linear_sum(p, q, a, b, r)
    return expectation, variance


def terminal_frequency_dictionary(ell: int, h: int) -> dict[int, Fraction]:
    r = h + 1
    frequencies: dict[int, Fraction] = defaultdict(Fraction)
    for u in terminal_shell(h):
        for a in range(nu10(u) + 1):
            w = weight(r, u // 10**a)
            for j in range(ell):
                n = 10**ell * (u // 10**a) - 10**j * u
                frequencies[n] += w
    return frequencies


def terminal_zero_formula(ell: int, h: int) -> Fraction:
    r = h + 1
    total = Fraction(0)
    for u in terminal_shell(h):
        for a in range(1, min(ell, nu10(u)) + 1):
            total += weight(r, u // 10**a)
    return total


def verify_canonical_hash() -> None:
    path = Path(__file__).with_name("canonical_statement.txt")
    actual = sha256(path.read_bytes()).hexdigest()
    assert actual == EXPECTED_CANONICAL_SHA256, (actual, EXPECTED_CANONICAL_SHA256)


def verify_primitive_rays() -> None:
    for h in range(1, 250):
        seen: dict[int, int] = {}
        for u in terminal_shell(h):
            v = u
            while v % 10 == 0:
                v //= 10
            assert v not in seen
            seen[v] = u
        primitive = [v for v in range(1, h + 1) if v % 10 != 0]
        assert set(seen) == set(primitive)


def verify_collision_classes() -> None:
    for ell in range(2, 7):
        for j in range(ell):
            for jp in range(j + 1, ell):
                a, b = collision_pair(ell, j, jp)
                d = 10**ell - 10**j
                dp = 10**ell - 10**jp
                assert b * d == a * dp
                for u in range(1, 80):
                    for up in range(1, 80):
                        equal = u * d == up * dp
                        parametrized = u % b == 0 and up == (u // b) * a
                        assert equal == parametrized
    assert 10 * (10**2 - 1) == 11 * (10**2 - 10) == 990


def verify_moments() -> None:
    for ell in range(1, 6):
        for h in range(0, 45):
            assert fejer_variance_dictionary(ell, h) == fejer_variance_formula(ell, h)
            direct_dictionary = direct_variance_dictionary(ell, h)
            direct_formula = direct_variance_formula(ell, h)
            assert direct_dictionary == direct_formula
            terminal = terminal_frequency_dictionary(ell, h)
            assert terminal.get(0, Fraction(0)) == terminal_zero_formula(ell, h)


def verify_decimal_valuations() -> None:
    for ell in range(1, 7):
        for u in range(1, 150):
            b = nu10(u)
            v = u // 10**b
            for a in range(b + 1):
                for j in range(ell):
                    n = 10**ell * (u // 10**a) - 10**j * u
                    if a + j == ell:
                        assert n == 0
                    else:
                        predicted = (
                            v
                            * 10 ** (b + min(j, ell - a))
                            * (10 ** abs(ell - a - j) - 1)
                        )
                        assert abs(n) == predicted


def verify_explicit_schedule() -> None:
    h = r = d_parameter = k_request = 1
    depth = 2
    shifts = [2, 3]
    assert len(shifts) == depth
    assert len(set(shifts)) == depth
    assert all(shift >= 1 and shift != r for shift in shifts)
    incoming_s = shifts[0]
    outgoing_u = 10 ** shifts[1] - 1
    adjacent_coefficient = h * (10**r - 1) * (10**incoming_s - 1)
    assert (d_parameter, k_request) == (1, 1)
    assert incoming_s == 2
    assert outgoing_u == 999
    assert adjacent_coefficient == 891
    for t in range(1, 20):
        m = t + 6
        assert k_request <= m - sum(shifts)
        residual_q = m - shifts[0]
        residual_q1 = m - sum(shifts)
        assert min(residual_q, residual_q1) == t + 1
        assert t < min(residual_q, residual_q1)


def verify_exceptional_tail() -> None:
    u = 999
    for start in range(1, 20):
        finite = sum(
            (Fraction(2, u * 10**t) + Fraction(1, u * u * 10 ** (2 * t)))
            for t in range(start, start + 100)
        )
        closed = Fraction(2, 9 * u * 10 ** (start - 1)) + Fraction(
            100, 99 * u * u * 10 ** (2 * start)
        )
        assert finite < closed
        remainder_bound = Fraction(2, u * 10 ** (start + 100)) + Fraction(
            1, u * u * 10 ** (2 * (start + 100))
        )
        assert closed - finite < 2 * remainder_bound
    # The exact denominators displayed in (7.9).
    assert 9 * u == 8991
    assert 99 * u * u == 98_802_099


def main() -> None:
    verify_canonical_hash()
    verify_primitive_rays()
    verify_collision_classes()
    verify_moments()
    verify_decimal_valuations()
    verify_explicit_schedule()
    verify_exceptional_tail()
    print("T72 replay: PASS")
    print("canonical SHA-256: PASS")
    print("coupled covariance and schedule identities: PASS")
    print("terminal label: ALMOST-EVERYWHERE SCHEDULE REFUTATION; NO PI CLAIM")


if __name__ == "__main__":
    main()
