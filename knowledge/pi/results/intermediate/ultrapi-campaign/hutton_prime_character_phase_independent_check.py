#!/usr/bin/env python3
"""Independent checks for the Hutton prime-character phase audit.

Fraction/integer assertions are exact.  Transcendental identities and quoted
endpoint constants are replayed at 80-decimal precision with mpmath; these are
numerical checks, not proofs and not evidence for V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from pathlib import Path

import mpmath as mp
from sympy.ntheory import n_order


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sieve(limit: int) -> list[bool]:
    result = [True] * (limit + 1)
    result[:2] = [False, False]
    for p in range(2, int(limit**0.5) + 1):
        if result[p]:
            for n in range(p * p, limit + 1, p):
                result[n] = False
    return result


def chi4(n: int) -> int:
    assert n % 2
    return 1 if n % 4 == 1 else -1


def eligible(n: int, primes: list[bool]) -> bool:
    return n < len(primes) and primes[n] and n > 7 and n != 17


def phase(k: int, primes: list[bool]) -> tuple[list[int], int, int, Fraction]:
    r = 4 * k + 3
    selected = [p for p in range(r // 2 + 1, r + 1) if eligible(p, primes)]
    g = 1
    for p in selected:
        g *= p
    s = sum(chi4(p) * (g // p) for p in selected)
    return selected, g, s, Fraction(s, g)


def increment(k: int, primes: list[bool]) -> Fraction:
    terms = Fraction(0)
    if eligible(4 * k + 5, primes):
        terms += Fraction(1, 4 * k + 5)
    if eligible(4 * k + 7, primes):
        terms -= Fraction(1, 4 * k + 7)
    if eligible(2 * k + 3, primes):
        terms += Fraction((-1) ** k, 2 * k + 3)
    return terms


def valuation_two(n: int) -> int:
    assert n > 0
    answer = 0
    while n % 2 == 0:
        answer += 1
        n //= 2
    return answer


def exact_arithmetic_checks(primes: list[bool]) -> None:
    old = phase(2, primes)[3]
    for k in range(2, 1001):
        selected, g, s, delta = phase(k, primes)
        assert delta == sum((Fraction(chi4(p), p) for p in selected), Fraction(0))
        assert Fraction(s, g) == delta
        assert __import__("math").gcd(s, g) == 1

        u = 1
        v = 1
        for p in selected:
            u *= p + chi4(p)
            v *= p - chi4(p)
        assert valuation_two(u) == len(selected)
        assert valuation_two(v) >= 2 * len(selected)
        assert (s - len(selected) * g) % 4 == 0

        if k < 1001:
            new = phase(k + 1, primes)[3]
            assert new - delta == increment(k, primes)
            old = new
    assert old == phase(1001, primes)[3]


def abel_rhs(k: int, primes: list[bool]) -> mp.mpf:
    """Right side of (11), integrating the Chebyshev step function exactly."""
    r = mp.mpf(4 * k + 3)
    a = r / 2
    full_primes = [p for p in range(3, int(r) + 1) if primes[p] and p % 2]

    def theta(x: mp.mpf) -> mp.mpf:
        return mp.fsum(chi4(p) * mp.log(p) for p in full_primes if p <= x)

    def f(x: mp.mpf) -> mp.mpf:
        return 1 / (x * mp.log(x))

    jumps = [mp.mpf(p) for p in full_primes if a < p <= r]
    left = a
    integral = mp.mpf("0")
    current = theta(a)
    for point in jumps:
        integral += current * (f(left) - f(point))
        current += chi4(int(point)) * mp.log(point)
        left = point
    integral += current * (f(left) - f(r))
    return theta(r) * f(r) - theta(a) * f(a) + integral


def high_precision_checks(primes: list[bool]) -> None:
    mp.mp.dps = 80
    for k in (8, 9, 17, 40, 127, 500):
        delta = mp.mpf(phase(k, primes)[3].numerator) / phase(k, primes)[3].denominator
        assert abs(delta - abel_rhs(k, primes)) < mp.mpf("1e-70")

    # At K=7 the unrestricted Chebyshev window contains excluded p=17.
    delta7 = mp.mpf(phase(7, primes)[3].numerator) / phase(7, primes)[3].denominator
    assert abs(abel_rhs(7, primes) - delta7 - mp.mpf(1) / 17) < mp.mpf("1e-70")

    for k in (8, 20, 100, 300):
        selected, _, _, delta_q = phase(k, primes)
        delta = mp.mpf(delta_q.numerator) / delta_q.denominator
        log_ratio = mp.fsum(
            mp.log(mp.mpf(p + chi4(p)) / (p - chi4(p))) for p in selected
        ) / 2
        tail = mp.fsum(mp.mpf(1) / (3 * p * (p * p - 1)) for p in selected)
        assert abs(delta - log_ratio) <= tail

    alpha = mp.log(10) / mp.log(5)
    assert abs(alpha - mp.mpf("1.4306765580733930506701065687639656321")) < mp.mpf("1e-37")
    assert abs((2 - alpha) - mp.mpf("0.5693234419266069493298934312360343679")) < mp.mpf("1e-37")

    # Recompute the two displayed endpoint evaluations independently.
    r = mp.mpf(2 * 4_800_162_889)
    ell, ell0 = mp.log(r), mp.log(r / 2)
    du = mp.mpf("0.0009644") * (
        1 / ell0 - 1 / ell + 1 / (2 * ell**2) + 3 / (2 * ell0**2)
    )
    assert abs(du - mp.mpf("5.12842986012554e-6")) < mp.mpf("1e-19")
    assert int(mp.floor(mp.log(r) / mp.log(5))) == 14

    r = 2 * mp.e**10
    ell, ell0 = mp.log(r), mp.log(r / 2)
    m = ell**2 / (8 * mp.pi) + (mp.log(4) / (2 * mp.pi) + mp.mpf("9.17523")) * ell + mp.mpf("0.78834")
    dg = m / mp.sqrt(r) * (
        (3 * mp.sqrt(2) - 1) / ell0 + 2 * (mp.sqrt(2) - 1) / ell0**2
    )
    assert abs(dg - mp.mpf("0.167645225442396")) < mp.mpf("1e-15")
    assert int(mp.floor(mp.log(r) / mp.log(5))) == 6

    # Independently verify the zero-frequency multiplier in (32).
    for gamma in (mp.mpf("0"), mp.mpf("1.25"), mp.mpf("14.134725")):
        base = 1 - mp.sqrt(2) * mp.e ** (-1j * gamma * mp.log(2))
        integral = (1 - mp.sqrt(2) * mp.e ** (-1j * gamma * mp.log(2))) / (-mp.mpf("0.5") + 1j * gamma)
        multiplier = base + integral
        closed = base * (mp.mpf("0.5") + 1j * gamma) / (-mp.mpf("0.5") + 1j * gamma)
        assert abs(multiplier - closed) < mp.mpf("1e-70")
        assert abs(closed) + mp.mpf("1e-70") >= mp.sqrt(2) - 1


def order_checks(primes: list[bool]) -> None:
    for k in (3, 5, 10, 20, 30):
        selected, g, s, _ = phase(k, primes)
        assert selected and __import__("math").gcd(10, g) == 1
        order = int(n_order(10, g))
        assert pow(10, order, g) == 1
        decimal_threshold = 0
        power = 1
        while power < g + 1:
            decimal_threshold += 1
            power *= 10
        assert order >= decimal_threshold
        assert __import__("math").gcd(s, g) == 1


def lift_branch_counterexample() -> None:
    """Show why equidistribution of 21*y mod 1 does not control y."""
    n = 101
    xs = [Fraction(j, n) for j in range(n)]
    ys = [(68 * x - (68 * x).__floor__()) / 21 for x in xs]
    assert sorted((68 * x) % 1 for x in xs) == xs
    assert all((21 * y - 68 * x).denominator == 1 for x, y in zip(xs, ys))
    assert all(Fraction(0) <= y < Fraction(1, 21) for y in ys)


def main() -> None:
    assert sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256
    primes = sieve(5000)
    exact_arithmetic_checks(primes)
    high_precision_checks(primes)
    order_checks(primes)
    lift_branch_counterexample()
    print("PASS: independent exact recurrence, gcd, 2-adic, mod-4, order, and lift checks")
    print("EXPERIMENT PASS: 80-digit Abel, log-tail, endpoint, and multiplier replays")


if __name__ == "__main__":
    main()
