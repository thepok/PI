#!/usr/bin/env python3
"""Exact fixed-seed certificate for reduced Salikhov five-adic depth.

The proof is the companion integration identity, the Cartier identities,
and Lucas reduction of the polynomial part. Recurrence checks are finite
validation of the formulas and are reported separately.
"""
from __future__ import annotations

import argparse
import importlib.util
from math import comb
from pathlib import Path


def mul(a, b, limit=None):
    length = len(a)+len(b)-1
    if limit is not None:
        length = min(length, limit+1)
    c = [0]*length
    for i, x in enumerate(a):
        for j, y in enumerate(b[:max(0, length-i)]):
            c[i+j] = (c[i+j]+x*y) % 5
    while len(c)>1 and c[-1]==0:
        c.pop()
    return c


def power(a, n, limit=None):
    result = [1]
    while n:
        if n & 1:
            result = mul(result, a, limit)
        n //= 2
        if n:
            a = mul(a, a, limit)
    return result


F = mul([1, -2, 1], power([2, -2, 1], 2))
D = power([2, -1], 3)
STATES = {1: [4, 4, 4, 1, 4], 0: [3, 2, 2]}
KERNELS = [mul(power([2, -1], 16-3*a), power(F, a)) for a in range(5)]


def section(a, b):
    out = a[b::5] or [0]
    while len(out)>1 and out[-1]==0:
        out.pop()
    return out


def coefficient(state, m, r):
    """[z^m w^r] S(w)/((2-w)((2-w)^3-zF(w))), over F_5."""
    if r < 0:
        return 0
    while m or r:
        a, b = m % 5, r % 5
        state = section(mul(state, KERNELS[a]), b)
        assert len(state) <= 7
        m, r = m//5, r//5
    return state[0] % 5


def lucas(n, r):
    result = 1
    while n or r:
        if r % 5 > n % 5:
            return 0
        result = result*comb(n % 5, r % 5) % 5
        n, r = n//5, r//5
    return result


def seed_outputs(t, parity):
    """Return (c, 5^c*a_n mod5, b_n/5^k mod5) for n=(t5^k+1)/2."""
    if t < 1 or t % 2 == 0 or t % 5 == 0 or parity not in (0, 1):
        raise ValueError('t must be positive, odd and prime to 5; parity is 0 or 1')
    c, p = 0, 1
    while 10*p <= 3*t:
        c, p = c+1, 5*p
    m = (t-1)//2
    state = STATES[parity]
    sign = (-1)**((t+1)//2+1)
    principal = sum(weight*coefficient(state, m, (3*t-2*u*p-1)//2)
                    for u, weight in ((1, 1), (2, 3), (3, 1)))
    polynomial = 4*t*lucas(t-1, (5*p-1)//2)
    companion = (t*sign*principal+polynomial) % 5
    multiplier = (-t*sign*3*coefficient(state, m, (3*t-1)//2)) % 5
    return c, companion, multiplier


def polynomial_checks():
    for a in range(5):
        # z^a coefficient in Q^4, reduced modulo 5.
        direct = mul(power([2, -1], 4), mul(power(D, 4-a), power(F, a)))
        direct = [((-1)**a)*comb(4, a)*x % 5 for x in direct]
        assert direct == KERNELS[a]
    # The original two-state cycle, independently checked here.
    initial = [1, 2, 4]
    assert section(mul(initial, KERNELS[2]), 4) == STATES[1]
    assert section(mul(STATES[1], KERNELS[2]), 2) == STATES[0]
    assert section(mul(STATES[0], KERNELS[2]), 2) == STATES[1]
    comparisons = 0
    for m in range(21):
        top = 3*m+1
        exponent = 3*m+4
        inv = [comb(exponent+j-1, j)*pow(2, -exponent-j, 5) % 5
               for j in range(top+1)]
        for state in STATES.values():
            dense = mul(mul(state, power(F, m, top), top), inv, top)
            dense += [0]*(top+1-len(dense))
            for r in range(top+1):
                assert coefficient(state, m, r) == dense[r]
                comparisons += 1
    expected = {
        1: ((0, 4, 4), (0, 3, 1)),
        3: ((0, 4, 1), (0, 2, 3)),
        7: ((1, 1, 4), (1, 2, 3)),
        9: ((1, 4, 1), (1, 4, 1)),
        13: ((1, 1, 4), (1, 4, 2)),
        17: ((2, 3, 3), (2, 1, 1)),
        71: ((2, 2, 0), (2, 3, 0)),
        27: ((2, 0, 0), (2, 0, 0)),
    }
    for t, outputs in expected.items():
        assert (seed_outputs(t, 1), seed_outputs(t, 0)) == outputs
    print('Exact certificate: all five general Cartier kernels and the three '
          'identities for the two-state cycle passed.')
    print(f'Finite implementation checks: {comparisons} fast coefficient outputs '
          'agree with independent dense power-series extraction.')
    print('Fixed-seed polynomial certificates (t: odd-k output, even-k output):')
    for t, outputs in expected.items():
        print(f'{t}: {outputs}')


def recurrence_checks(path, max_n, max_seed):
    spec = importlib.util.spec_from_file_location('salikhov_source', path)
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    aa, bb = source.recurrence_sequences(max_n)

    def residue(x):
        assert x.denominator % 5 != 0
        return x.numerator*pow(x.denominator, -1, 5) % 5

    count = 0
    for t in range(1, max_seed+1, 2):
        if t % 5 == 0:
            continue
        k, h = 1, 5
        while (t*h+1)//2 <= max_n:
            n = (t*h+1)//2
            c, companion, multiplier = seed_outputs(t, k % 2)
            assert residue(aa[n]*5**c) == companion, (t, k, 'companion')
            assert residue(bb[n]/h) == multiplier, (t, k, 'multiplier')
            count += 1
            k, h = k+1, 5*h
    print(f'Finite independent recurrence validation: {count} seed/index pairs, '
          f't <= {max_seed}, n <= {max_n}.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-checker', type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        'salikhov_mod5_support_20260906' / 'full_pair.py')
    parser.add_argument('--max-n', type=int, default=1200)
    parser.add_argument('--max-seed', type=int, default=93)
    args = parser.parse_args()
    if args.max_n < 1 or args.max_seed < 1:
        parser.error('bounds must be positive')
    polynomial_checks()
    recurrence_checks(args.source_checker, args.max_n, args.max_seed)


if __name__ == '__main__':
    main()
