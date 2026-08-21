#!/usr/bin/env python3
"""Deterministic sanity checks for T65's displayed arithmetic.

These finite checks detect transcription errors; they are not evidence for the
universal algebraic claims or for cancellation.  Those claims are justified in
REPORT.md.
"""

from fractions import Fraction
from math import gcd
from pathlib import Path


HERE = Path(__file__).resolve().parent


def v_p(n: int, p: int) -> int:
    n = abs(n)
    value = 0
    while n and n % p == 0:
        n //= p
        value += 1
    return value


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def check_orbit_decomposition() -> None:
    # Exact rational arguments are enough: e(x) depends only on x modulo Z.
    for e in range(6):
        for J in range(8):
            for m in (1, 3, 7, 9, 21):
                for a in range(1, 12):
                    if gcd(a, 5 * m) != 1:
                        continue
                    for h in (-15, -6, -1, 1, 5, 14):
                        lhs = [Fraction(h * a * 10**j, 5**e * m) for j in range(J)]
                        split = [
                            Fraction(h * a * 10**j, 5**e * m)
                            for j in range(min(e, J))
                        ]
                        if J > e:
                            split += [
                                Fraction(h * a * 2**e * 10**t, m)
                                for t in range(J - e)
                            ]
                        assert lhs == split

                        s = v_p(h, 5)
                        g = gcd(abs(h), m)
                        reduced_m = m // g
                        u = h // (5**s * g)
                        transient = max(e - s, 0)
                        reduced = [
                            Fraction(a * u * 2**j, 5 ** (e - s - j) * reduced_m)
                            for j in range(min(J, transient))
                        ]
                        if J > transient:
                            h_tail = a * u * 2**transient * 5 ** (s + transient - e)
                            reduced += [
                                Fraction(h_tail * 10**t, reduced_m)
                                for t in range(J - transient)
                            ]
                        assert lhs == reduced


def zudilin_coefficients(count: int) -> list[int]:
    values = [1, -1]
    while len(values) < count:
        values.append(-6 * values[-1] - 25 * values[-2])
    return values[:count]


def check_common_denominators() -> None:
    expected = {
        1: (1, 1),
        2: (3, 3),
        3: (6, 3),
        4: (8, 21),
        5: (10, 63),
        6: (12, 693),
    }
    coefficients = zudilin_coefficients(12)
    for K in range(1, 13):
        x = 2 * K - 1
        odd_lcm = 1
        for odd in range(1, x + 1, 2):
            odd_lcm = lcm(odd_lcm, odd)
        Q = 5**x * odd_lcm
        exponent = v_p(Q, 5)
        cofactor = Q // 5**exponent
        if K in expected:
            assert (exponent, cofactor) == expected[K]

        value = sum(
            (Fraction(16 * coefficients[n], (2 * n + 1) * 5 ** (2 * n + 1))
             for n in range(K)),
            Fraction(0),
        )
        A = value * Q
        assert A.denominator == 1
        A_int = A.numerator
        e_reduced = exponent - min(exponent, v_p(A_int, 5))
        m_reduced = cofactor // gcd(cofactor, A_int)
        assert value.denominator == 5**e_reduced * m_reduced

        for h in (-30, -7, 1, 5, 18):
            for j in range(5):
                reduced = Fraction(h * 10**j) * value
                formula = (
                    5 ** max(exponent - v_p(A_int * h, 5) - j, 0)
                    * cofactor // gcd(cofactor, A_int * h)
                )
                assert reduced.denominator == formula


def check_individual_summands_and_ranges() -> None:
    coefficients = zudilin_coefficients(20)
    for n, b_n in enumerate(coefficients):
        t = 2 * n + 1
        k = v_p(t, 5)
        m = t // 5**k
        assert b_n % 5 == (1 if n % 2 == 0 else -1) % 5
        for d in range(8):
            scalar = Fraction(10**d * 16 * b_n, t * 5**t)
            e = max(t + k - d, 0)
            expected = 5**e * (m // gcd(m, b_n))
            assert scalar.denominator == expected
            for h in (-25, -6, -1, 1, 5, 14):
                phase = scalar * h
                transient = max(e - v_p(h, 5), 0)
                post = m // gcd(m, h * b_n)
                assert phase.denominator == 5**transient * post

    for ell in range(1, 7):
        for R in range(2, 15):
            H = R - 1
            shell = range(H // 10 + 1, H + 1)
            for u in shell:
                for j in range(ell):
                    frequency = u * (10**ell - 10**j)
                    assert 9 * u * 10 ** (ell - 1) <= frequency
                    assert frequency < u * 10**ell
                    assert frequency < R * 10**ell


def check_elementary_inequalities() -> None:
    for K in range(1, 200):
        assert 2 * K + 1 <= 5**K
    for J in range(1, 100):
        # Rational lower bound pi > 3 is enough for (7.7).
        assert 16 * 3 * 10 ** (J - 1) > 5 ** (J + 1)


def check_report_contract() -> None:
    report = (HERE / "REPORT.md").read_text(encoding="ascii")
    verdict = "NO RESCUE FOR T63 DENOMINATORS"
    assert report.rstrip().endswith(verdict)
    assert report.count(verdict) == 1
    assert "CONDITIONAL RESCUE WITH NAMED HYPOTHESES" not in report
    assert "USABLE RESCUE" not in report
    forbidden = ("normality claim", "equidistribution claim")
    for phrase in forbidden:
        assert phrase not in report


def main() -> None:
    check_orbit_decomposition()
    check_common_denominators()
    check_individual_summands_and_ranges()
    check_elementary_inequalities()
    check_report_contract()
    print("T65 deterministic arithmetic sanity checks passed.")
    print("Finite replay is not evidence of cancellation or a universal proof.")


if __name__ == "__main__":
    main()
