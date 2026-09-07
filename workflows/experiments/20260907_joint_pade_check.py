"""Exact finite diagnostics for the joint Machin--Hermite--Pade ledger entry.

Label: experiment, not an infinite proof, novelty or digit-occurrence claim.
Run with standard-library Python 3.10+. No pi digits or numerical pi input.
Independent reproduction of the reviewed research appendix; the integral
inequalities establishing the lower bound are proof sketches in the ledger.
"""
from fractions import Fraction as F
from math import comb, factorial, gcd, lcm

A, B, M, ROOT_M = 25, 57121, 1428025, 1195


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def evaluate(a, x):
    out = 0
    for c in reversed(a):
        out = out * x + c
    return out


def odd_lcm(mx):
    return lcm(*range(1, mx + 1, 2))


def integer(x):
    assert x.denominator == 1
    return x.numerator


def floor_log10(x):
    """Exact logarithmic order of a positive Fraction, not its numerator."""
    assert x > 0
    k = len(str(x.numerator)) - len(str(x.denominator))
    power = F(10**k) if k >= 0 else F(1, 10**(-k))
    if x < power:
        k -= 1
        power /= 10
    assert power <= x < 10 * power
    return k


def audit(n):
    assert n >= 2 and n % 2 == 0
    f = mul([comb(n, k) * (-A)**(n-k) for k in range(n+1)],
            [comb(n, k) * (-B)**(n-k) for k in range(n+1)])
    eta0 = sum((F(c*A**k, 2*(n+k)+1) for k, c in enumerate(f)), F(0))
    eta1 = A * sum((F(c*A**k, 2*(n+k)+3) for k, c in enumerate(f)), F(0))
    mean = eta1 / eta0
    u, v = mean.numerator, mean.denominator
    raw = mul(f, [-u, v])
    y = []
    for k, c in enumerate(raw):
        multiplier = F(4**n, factorial(n))
        for j in range(n):
            multiplier *= F(2*(k+j)+1, 2)
        y.append(integer(multiplier) * c)
    degree = 2*n + 1
    ell = odd_lcm(2*degree - 1)
    q = -ell * evaluate(y, -M)
    assert q > 0
    for endpoint, root, count in ((A, 5, n+1), (B, 239, n)):
        for k in range(count):
            assert sum((F(root*c*endpoint**(k+j), 2*(k+j)+1)
                        for j, c in enumerate(y)), F(0)) == 0
    quotient = [-sum(y[j]*(-M)**(j-1-k) for j in range(k+1, degree+1))
                for k in range(degree)]
    assert mul(quotient, [M, 1]) == [evaluate(y, -M)-y[0]] + [-c for c in y[1:]]
    b_b = integer(-ell * sum((F(239*c*B**k, 2*k+1)
                              for k, c in enumerate(quotient)), F(0)))
    b_a = integer(-ell * sum((F(5*c*A**k, 2*k+1)
                              for k, c in enumerate(quotient)), F(0)))
    p = ROOT_M * (16*b_b - 4*b_a)
    common = gcd(q, p)
    reduced_den = q // common
    lower = F(285605, 78) * ell * v * F(3262808641, 234)**n / common
    k_lcm = odd_lcm(6*n + 3)
    moments = [integer(k_lcm * sum((
        F((-1)**(r+t)*comb(n, r)*comb(n, t)*A**t*B**(n-t),
          2*n+2*r+2*t+2*j+1)
        for r in range(n+1) for t in range(n+1)), F(0))) for j in (0, 1)]
    assert moments[0] > 0
    assert mean == F(A*moments[1], moments[0])
    assert 1 <= v <= moments[0] <= k_lcm*F(B, 4)**n
    return len(str(q)), len(str(reduced_den)), common, floor_log10(lower)


if __name__ == '__main__':
    expected = {
        2: (47, 41, 1376640, 24),
        4: (88, 80, 44052480, 50),
        6: (129, 119, 7753236480, 77),
        8: (170, 156, 263891976192000, 100),
        10: (212, 200, 902194790400, 131),
        12: (256, 242, 225187819683840, 159),
    }
    for n, row in expected.items():
        result = audit(n)
        assert result == row, (n, result, row)
        print(n, *result)
    print('PASS: exact moments, integer lifts, mean, gcds and rational orders; experiment only.')
