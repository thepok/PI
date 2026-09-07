"""Exact finite checks for the bounded mixed-period ledger entry.

Label: experiment. This checks identities and finite calibrations, not the
all-index arguments, novelty, or any assertion about pi's decimal orbit.
Standard library only; no stored digits or floating-point comparisons.
"""

from fractions import Fraction as F
from functools import cache
from math import comb, factorial, gcd


def valuation(z, p):
    z = abs(z)
    assert z, "valuation of zero is not a finite integer"
    count = 0
    while z % p == 0:
        count += 1
        z //= p
    return count


def rational_valuation(x, p):
    return valuation(x.numerator, p) - valuation(x.denominator, p)


@cache
def arctan_head(b, n):
    return sum((F((-1) ** k, (2 * k + 1) * b ** (2 * k + 1))
                for k in range(n)), F(0))


@cache
def machin(n):
    return 16 * arctan_head(5, n) - 4 * arctan_head(239, n)


def pi_bracket(n=100):
    assert n > 0 and n % 2 == 0
    return (16 * arctan_head(5, n) - 4 * arctan_head(239, n + 1),
            16 * arctan_head(5, n + 1) - 4 * arctan_head(239, n))


def ramanujan_term(j):
    return F((6 * j + 1) * comb(2 * j, j) ** 3, 256 ** j)


def ramanujan_head(m):
    return sum((ramanujan_term(j) for j in range(m)), F(0))


def wallis(n):
    result = F(2)
    for j in range(1, n + 1):
        result *= F(4 * j * j, 4 * j * j - 1)
    return result


def apery_heads(n):
    a, b = [F(1), F(3)], [F(0), F(5)]
    for k in range(1, n):
        for seq in (a, b):
            seq.append(((11 * k * k + 11 * k + 3) * seq[k]
                        + k * k * seq[k - 1]) / (k + 1) ** 2)
    return a, b


def check_secant(lo, hi):
    for n in (2, 6, 10):
        lower, upper = machin(n), machin(n + 1)
        assert 3 < lower < lo < hi < upper < 4
        assert rational_valuation(lower, 2) == 3
        assert rational_valuation(upper, 2) == 2
        u, den_l = lower.numerator // 8, lower.denominator
        v, den_u = upper.numerator // 4, upper.denominator
        for m in (2, 3, 4, 8):
            rec = ramanujan_head(m)
            d = 8 * (m - 1) - 3 * (m - 1).bit_count()
            assert rec.denominator == 2 ** d
            term = ramanujan_term(m)
            assert term < 4 / hi - rec < 4 / lo - rec < F(4, 3) * term
            h = lower + upper - lower * upper * rec / 4
            j = 2 ** (d - 1) * (2 * u * den_u + v * den_l) - u * v * rec.numerator
            g = gcd(j, den_l * den_u)
            assert h == F(j // g, 2 ** (d - 3) * den_l * den_u // g)
            assert h.numerator == j // g
            assert h.denominator == 2 ** (d - 3) * den_l * den_u // g
            assert valuation(h.denominator, 2) == d - 3
            assert h > hi
            for x in (lo, hi):
                eps, delta, tau = x - lower, upper - x, 4 / x - rec
                assert h - x == eps * delta / x + lower * upper * tau / 4
                assert lower * upper * tau / 4 == (
                    x * x * tau / 4 + x * (delta - eps) * tau / 4
                    - eps * delta * tau / 4)
    x = F(4, 3)
    for n, m in ((2, 2), (6, 3), (10, 4)):
        lower = x - F(4, (2 * n + 1) * 5 ** (2 * n + 1))
        upper = x + F(8, (2 * n + 3) * 5 ** (2 * n + 3))
        rec = 3 - ramanujan_term(m - 1)
        h = lower + upper - lower * upper * rec / 4
        assert rational_valuation(lower, 2) == 3
        assert rational_valuation(upper, 2) == 2
        assert valuation(h.denominator, 2) == 8 * (m - 1) - 3 * (m - 1).bit_count() - 3
        assert h - x == (x - lower) * (upper - x) / x + lower * upper * (3 - rec) / 4
        assert lower * upper / 4 > F(1, 3)


def check_wallis(lo, hi):
    for n in range(1, 17):
        m = machin(n)
        p, q = m.numerator, m.denominator
        sigma = 2 + valuation(n, 2)
        assert q % 2 == 1 and valuation(p, 2) == sigma
        for k in range(1, 11):
            w = wallis(k)
            a = 4 * k + 1 - 2 * k.bit_count()
            d = (2 * k + 1) * (comb(2 * k, k) // 2 ** k.bit_count()) ** 2
            assert w == F(2 * 16 ** k, (2 * k + 1) * comb(2 * k, k) ** 2)
            assert w == F(2 ** a, d) and d % 2 == 1
            assert F(1, 4 * k + 4) < lo / w - 1 < hi / w - 1 < F(1, 4 * k + 1)
            mixed = p * d - 2 ** a * q
            if a > sigma:
                assert valuation(mixed, 2) == sigma
                assert (m / w - 1).denominator == 2 ** (a - sigma) * q // gcd(q, d)
            # Arbitrary comparison prefixes, not programmed target digits.
            for endpoint, scale in ((0, 1), (7, 10), (-11, 1000)):
                assert (d * (scale * p - endpoint * q)
                        - q * (scale * 2 ** a - endpoint * d) == scale * mixed)


def check_square(lo, hi):
    aa, bb = apery_heads(322)
    assert aa[2] == 19 and bb[2] == F(125, 4)
    for r, n in ((2, 1), (4, 2), (4, 3), (239, 2), (239, 322)):
        m = machin(r)
        a, b = m.numerator, m.denominator
        square = 6 * bb[n] / aa[n]
        p, q = square.numerator, square.denominator
        g = gcd(2 * a * b * q, q * a * a + p * b * b)
        d, num = 2 * a * b * q // g, (q * a * a + p * b * b) // g
        c = F(b * b * q, g)
        assert gcd(d, num) == 1 and c == d / (2 * m)
        assert F(num, d) == (m * m + square) / (2 * m)
        for x in (lo, hi):
            assert d * x - num == c * (x * x - square - (x - m) ** 2)
        assert aa[n].denominator == 1 and 0 < aa[n] <= 12 ** n
        assert (factorial(n) ** 2 * bb[n]).denominator == 1
        if r == 239:
            assert valuation(b, 239) == valuation(d, 239) == 2 * r - 1
            assert c > F(239 ** (2 * r - 1), 8)
            assert valuation(d // gcd(d, 10 ** 1000), 239) == 2 * r - 1


if __name__ == "__main__":
    lo, hi = pi_bracket()
    assert 3 < lo < hi < 4
    check_secant(lo, hi)
    check_wallis(lo, hi)
    check_square(lo, hi)
    print("PASS: exact secant/control, Wallis normalization, primitive square identities")
