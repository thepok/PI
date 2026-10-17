#!/usr/bin/env python3
"""Exact polynomial certificate for five-adic Salikhov companion survival.

Standard library only. The all-k argument uses rational identities and a
three-identity Cartier certificate; recurrence samples are separate checks.
No pi digits, numerical pi evaluation, network, or external CAS is used.
Source normalization: https://arxiv.org/html/1912.06345v2
"""
from __future__ import annotations

import argparse
import importlib.util
from fractions import Fraction as Q
from math import comb
from pathlib import Path


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [0]


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def scale(a, x):
    return trim([x * y for y in a])


def mul(a, b, limit=None):
    length = len(a) + len(b) - 1
    if limit is not None:
        length = min(length, limit + 1)
    c = [0] * length
    for i, x in enumerate(a):
        for j, y in enumerate(b[:max(0, length - i)]):
            c[i+j] += x * y
    return trim(c)


def power(a, n, limit=None):
    r = [1]
    while n:
        if n & 1:
            r = mul(r, a, limit)
        n //= 2
        if n:
            a = mul(a, a, limit)
    return r


def derivative(a):
    return trim([i*a[i] for i in range(1, len(a))])


def shift_minus_one(a):
    result = [0]
    for x in reversed(a):
        result = add(mul(result, [-1, 1]), [x])
    return result


def quotient(a, b):
    a = list(map(Q, a))
    result = [Q(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and a != [0]:
        offset = len(a) - len(b)
        c = a[-1] / b[-1]
        result[offset] += c
        for j, x in enumerate(b):
            a[offset+j] -= c*x
        a = trim(a)
    return trim(result)


def mod5(a):
    return trim([int(x) % 5 for x in a])


def section(a, b):
    return mod5(a[b::5])


H = [1, 0, 6, 0, 25]
E = [1, 0, 20, 0, 125, 0, -50]
W = [-211, 0, 318, 0, -75]
EX = [625, 0, 500, 0, 125, 0, -2]
WX = [-5275, 0, 318, 0, -3]
L = [25, 0, 6, 0, 1]


def polynomial_certificate():
    u, u2, one_minus_u2 = [0, 1], [0, 0, 1], [1, 0, -1]
    assert E == add(mul(add(H, mul(u, derivative(H))), one_minus_u2),
                    scale(mul(u2, H), 3))
    assert add(mul(one_minus_u2, derivative(W)), scale(mul(u, W), 3)) \
        == scale(mul(u, H), 3)
    assert [Q(625*x, 5**i) for i, x in enumerate(E)] == EX
    assert [Q(25*x, 5**i) for i, x in enumerate(W)] == WX
    assert [Q(25*x, 5**i) for i, x in enumerate(H)] == L

    # This checks full polynomials, including all zero coefficients.
    F = mod5(mul(power([-1, 1], 2), power([2, -2, 1], 2)))
    K = mod5(mul(power([2, -1], 10), power(F, 2)))
    initial = [1, 2, 4]
    odd = [4, 4, 4, 1, 4]
    even = [3, 2, 2]
    assert mod5(scale(mul(shift_minus_one(E), shift_minus_one(W)), -2)) \
        == initial  # -1/3 == -2 in F_5
    assert section(mul(initial, K), 4) == odd
    assert section(mul(odd, K), 2) == even
    assert section(mul(even, K), 2) == odd
    # Constant and first coefficient of (2-w)^(-4) modulo 5.
    assert pow(2, -4, 5) == 1
    assert 4 * pow(2, -5, 5) % 5 == 2
    assert (odd[1] + 2*odd[0]) % 5 == 2
    assert (even[1] + 2*even[0]) % 5 == 3
    assert (-3 * pow(2, -1, 5)) % 5 == 1  # E_1 = -3/2
    print('Exact certificate: two integer identities, coordinate scaling, '
          'and all three Cartier polynomial equalities passed.')


def load_source(path):
    spec = importlib.util.spec_from_file_location('salikhov_source', path)
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    return source


def transformed_companion(n, source):
    """Direct partial fractions for the NEW differential, using exact rationals."""
    num = scale(mul(mul(power([-1, 1], 2*n-2),
                        power(shift_minus_one(H), 2*n-2)),
                    mul(shift_minus_one(E), shift_minus_one(W))), Q(-1, 3))
    inv = [Q(comb(3*n+j, j), 2**(3*n+1+j)) for j in range(3*n+1)]
    coefficients = mul(num, inv, 3*n)
    coefficients += [Q(0)] * (3*n+1-len(coefficients))
    b = Q((-1)**n, 2) * coefficients[3*n]
    a = Q(0)
    for j in range(1, 3*n+1):
        ej = -2*(source.gp((Q(1), Q(1, 2)), j)[1]
                 + source.gp((Q(3, 4), Q(1, 4)), j)[1])
        a += (-1)**(n+1)*coefficients[3*n-j]*ej/j

    physical_num = scale(mul(mul([0]*(2*n-2)+[1], power(L, 2*n-2)),
                             mul(EX, WX)), Q(-5, 3))
    physical_den = power([25, 0, -1], 3*n+1)
    polynomial = quotient(physical_num, physical_den)
    for exponent, coefficient in enumerate(polynomial):
        assert coefficient.denominator % 5 != 0
        assert coefficient.numerator % 5 == 0
        assert exponent % 2 == 0 or coefficient == 0
        if coefficient:
            j = exponent+1
            endpoint = -2*source.gp((Q(-1), Q(2)), j)[1]
            a += (-1)**(n+1)*coefficient*endpoint/j
    return a, b


def valuation5(x):
    if x == 0:
        raise ValueError('valuation5 needs a nonzero value')
    numerator, denominator = x.numerator, x.denominator
    result = 0
    while numerator % 5 == 0:
        numerator //= 5
        result += 1
    while denominator % 5 == 0:
        denominator //= 5
        result -= 1
    return result


def residue5(x):
    assert x.denominator % 5 != 0
    return x.numerator * pow(x.denominator, -1, 5) % 5


def finite_checks(source, max_n, direct):
    aa, bb = source.recurrence_sequences(max_n)
    for n in range(1, min(direct, max_n)+1):
        transformed_a, transformed_b = transformed_companion(n, source)
        assert (2*n-1)*transformed_a == aa[n], n
        assert (2*n-1)*transformed_b == bb[n], n
    for n in range(1, max_n+1):
        power5, s = 1, 0
        while 5*power5 <= 4*n:
            power5 *= 5
            s += 1
        assert valuation5(aa[n]) >= valuation5(Q(2*n-1))-s, n
        assert valuation5(bb[n]) >= valuation5(Q(2*n-1)), n
    rows = []
    k, h = 1, 5
    while (h+1)//2 <= max_n:
        n = (h+1)//2
        expected_a = (1+2*(-1)**k) % 5
        assert valuation5(aa[n]) == 0
        assert residue5(aa[n]) == expected_a
        assert residue5(bb[n]/h) == (-1)**k % 5
        q = source.p2(2-(5*n)//2)*bb[n]
        assert q.denominator == 1
        assert residue5(q/h) == pow(2, k, 5)
        reduced = -aa[n]/bb[n]
        assert valuation5(Q(reduced.denominator)) == k
        rows.append((k, n, expected_a, residue5(bb[n]/h), k))
        k, h = k+1, 5*h
    print(f'Finite independent checks: transformed integral for n=1..{min(direct,max_n)}; '
          f'valuation bounds against the published recurrence through n={max_n}.')
    print('Finite special-index rows (k,n,a mod5,(b/5^k) mod5,v5(reduced Q)):')
    for row in rows:
        print(row)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-checker', type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        'salikhov_mod5_support_20260906' / 'full_pair.py')
    parser.add_argument('--max-n', type=int, default=400)
    parser.add_argument('--direct', type=int, default=8)
    args = parser.parse_args()
    if args.max_n < 1 or args.direct < 0:
        parser.error('--max-n must be positive and --direct nonnegative')
    polynomial_certificate()
    finite_checks(load_source(args.source_checker), args.max_n, args.direct)


if __name__ == '__main__':
    main()
