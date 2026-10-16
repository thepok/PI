#!/usr/bin/env python3
"""Exact Cartier evaluation of the Salikhov multiplier modulo powers of five.

For G=S0/(D-zF), m=5**(precision-1), work with S/Q**m and use
Q**(5*m) == Q(z**5,w**5)**m mod 5**precision.
The initial numerator is S0*Q**(m-1). All arithmetic is exact.
"""
from math import comb
from pathlib import Path


def baseline_directory():
    """Locate the tracked predecessor experiment from either repository layout."""
    relative = Path('workflows/experiments/salikhov_mod5_support_20260906')
    for parent in Path(__file__).resolve().parents:
        for candidate in (parent / relative, parent / 'PI' / relative):
            if (candidate / 'full_pair.py').is_file():
                return candidate
    raise FileNotFoundError('The tracked Salikhov mod-5 predecessor is required')


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def mul(a, b, modulus):
    if not any(a) or not any(b):
        return [0]
    width = (min(len(a), len(b)) * (modulus - 1)**2).bit_length() + 1
    aa = sum(x << (width * j) for j, x in enumerate(a))
    bb = sum(x << (width * j) for j, x in enumerate(b))
    product = aa * bb
    mask = (1 << width) - 1
    out = []
    for _ in range(len(a) + len(b) - 1):
        out.append((product & mask) % modulus)
        product >>= width
    return trim(out)


def powers(a, limit, modulus):
    out = [[1]]
    for _ in range(limit):
        out.append(mul(out[-1], a, modulus))
    return out


class Cartier:
    def __init__(self, precision=2):
        assert precision >= 1
        self.precision = precision
        self.modulus = p = 5**precision
        self.m = m = 5**(precision - 1)
        H = [x % p for x in [32, -112, 156, -100, 25]]
        F = mul([1, p-2, 1], mul(H, H, p), p)
        D = [x % p for x in [8, -12, 6, -1]]
        S0 = [4, p-4, 1]
        ff = powers(F, 4*m, p)
        dd = powers(D, 4*m, p)
        self.initial = []
        for u in range(m):
            factor = comb(m-1, u) * (-1)**u % p
            poly = mul(S0, mul(ff[u], dd[m-1-u], p), p)
            self.initial.append(trim([factor * x % p for x in poly]))
        # Every numerator row has degree <=10m-2, under every transition.
        self.width = width = ((10*m+1)*(p-1)**2).bit_length() + 1
        self.mask = (1 << width) - 1
        self.B = []
        for u in range(4*m+1):
            factor = comb(4*m, u) * (-1)**u % p
            if factor:
                poly = mul(ff[u], dd[4*m-u], p)
                poly = trim([factor*x % p for x in poly])
            else:
                poly = [0]
            packed = sum(x << (width*j) for j, x in enumerate(poly))
            self.B.append((packed, len(poly)))
        self.invconstant = pow(pow(8, m, p), -1, p)

    def step(self, numerator, a, b):
        p, m, width = self.modulus, self.m, self.width
        out = [[0]*(10*m+1) for _ in range(m)]
        for u, poly in enumerate(numerator):
            if not any(poly):
                continue
            aa = sum(x << (width*j) for j, x in enumerate(poly))
            for e in range((a-u) % 5, 4*m+1, 5):
                dest = (u+e-a)//5
                if not 0 <= dest < m:
                    continue
                bb, sizeb = self.B[e]
                if not bb:
                    continue
                prod = (aa * bb) >> (width*b)
                count = max(0, (len(poly)+sizeb-2-b)//5+1)
                row = out[dest]
                for j in range(count):
                    row[j] = (row[j] + (prod & self.mask)) % p
                    prod >>= 5*width
        return [trim(row) for row in out]

    def coefficient(self, n, w):
        if min(n,w) < 0:
            return 0
        state = self.initial
        while n or w:
            state = self.step(state, n % 5, w % 5)
            n //= 5
            w //= 5
        return state[0][0] * self.invconstant % self.modulus

    def q(self, n):
        phi = 4 * 5**(self.precision-1)
        factor = (-1)**n * pow(2, (1-5*n//2) % phi, self.modulus)
        return factor * self.coefficient(n, 3*n) % self.modulus


if __name__ == '__main__':
    import argparse
    import sys
    import time
    parser = argparse.ArgumentParser()
    parser.add_argument('--precision', type=int, default=2)
    parser.add_argument('--check', type=int, default=50)
    args = parser.parse_args()
    sys.path.insert(0,str(baseline_directory()))
    from full_pair import recurrence_sequences, p2
    start=time.monotonic()
    engine=Cartier(args.precision)
    aa,bb=recurrence_sequences(args.check)
    for n in range(args.check+1):
        q=p2(2-5*n//2)*bb[n]
        assert q.denominator==1
        assert engine.q(n)==q.numerator%engine.modulus,n
    print('Exact recurrence comparison passed:',args.check,'precision',args.precision,'seconds',time.monotonic()-start)
    for copies in range(1,7):
        digits='03'*copies
        n=sum(int(d)*5**i for i,d in enumerate(digits))
        print('digits LSF',digits,'n',n,'q mod',engine.modulus,engine.q(n))
