"""Exact finite falsification checks; not a proof of infinite statements.

See ATTEMPT_LEDGER.md, decimal C-finite logarithm admission check.
No external data, floating-point pi, or third-party dependencies.
"""

from fractions import Fraction as F
from math import gcd


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def valuation(n, p):
    assert n > 0
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def atan_bracket(q, terms=100):
    """Alternating-series enclosure for atan(1/q), q>1."""
    assert q > 1 and terms > 0
    head = sum((F((-1) ** j, (2 * j + 1) * q ** (2 * j + 1))
                for j in range(terms)), F(0))
    other = head + F((-1) ** terms, (2 * terms + 1) * q ** (2 * terms + 1))
    return min(head, other), max(head, other)


def main():
    lo5, hi5 = atan_bracket(5)
    lo239, hi239 = atan_bracket(239)
    pi_lo, pi_hi = 16 * lo5 - 4 * hi239, 16 * hi5 - 4 * lo239
    ratio = F(90, 11) * F(27, 26) * F(9, 10) ** 25
    assert ratio < 1
    p, q, coefficients, head = (1, 0), (1, 0), [0], F(0)
    for n in range(1, 126):
        p, q = mul(p, (0, -5)), mul(q, (4, -2))
        a = -4 * (p[1] + q[1])
        coefficients.append(a)
        assert a % 5 == pow(3, n, 5)
        if n >= 4:
            assert a == (8 * coefficients[n - 1] - 45 * coefficients[n - 2]
                         + 200 * coefficients[n - 3] - 500 * coefficients[n - 4])
        head += F(a, n * 10 ** n)
        if n not in (5, 25, 125):
            continue
        d = head.denominator
        assert valuation(d, 5) == n + valuation(n, 5)
        if n >= 25:
            error_lower = head - pi_hi
            assert error_lower > 0
            assert d * error_lower >= F(1, 3) * F(5, 2) ** n
            for t in (0, 1, n):
                reduced_shift_denominator = d // gcd(d, 10 ** t)
                assert reduced_shift_denominator * 10 ** t >= d
        print(f"N={n}: v5(reduced denominator)={valuation(d, 5)}; exact checks pass")
    assert pi_lo < pi_hi
    print("Finite checks only; the infinite proof is the ledger's proof sketch.")


if __name__ == "__main__":
    main()
