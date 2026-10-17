#!/usr/bin/env python3
"""Exact arbitrary-index Salikhov pair modulo a fixed power of five.

The multiplier uses the tracked bounded-denominator Cartier engine.  The
rational companion uses its exact endpoint formula: only denominators in
the highest precision many five-adic shells can survive normalization.
No floating-point arithmetic, pi digits, or fitted recurrence is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import sys
import time


def experiment_directory(name: str) -> Path:
    relative = Path('workflows/experiments') / name
    for parent in Path(__file__).resolve().parents:
        for candidate in (parent / relative, parent / 'PI' / relative):
            if candidate.is_dir():
                return candidate
    raise FileNotFoundError(relative)


sys.path.insert(0, str(experiment_directory('salikhov_prime_power_20261016')))
from bounded_cartier import BoundedCartier  # noqa: E402


def valuation(n: int, p: int = 5) -> int:
    if not n:
        raise ValueError('valuation of zero is not finite')
    n = abs(n)
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def rational_valuation(x: Fraction, p: int = 5) -> int:
    return valuation(x.numerator, p) - valuation(x.denominator, p)


def shell(n: int) -> int:
    assert n >= 1
    s, power = 0, 5
    while power <= 4*n:
        s += 1
        power *= 5
    return s


def gaussian_mul(a, b, modulus):
    return ((a[0]*b[0]-a[1]*b[1]) % modulus,
            (a[0]*b[1]+a[1]*b[0]) % modulus)


def gaussian_power(a, exponent, modulus):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = gaussian_mul(result, a, modulus)
        exponent //= 2
        if exponent:
            a = gaussian_mul(a, a, modulus)
    return result


class BinomialFive:
    """Factorial-unit evaluation valid for arbitrary nonnegative indices."""

    def __init__(self, precision):
        self.precision = precision
        self.modulus = 5**precision
        prefix = [1]
        for j in range(1, self.modulus+1):
            prefix.append(prefix[-1] * (j if j % 5 else 1) % self.modulus)
        self.prefix = prefix
        assert prefix[-1] == self.modulus-1

    def factorial_unit(self, n):
        result, exponent = 1, 0
        while n:
            result = result * self.prefix[n % self.modulus] % self.modulus
            if (n // self.modulus) % 2:
                result = -result % self.modulus
            n //= 5
            exponent += n
        return result, exponent

    def choose(self, n, k):
        if k < 0 or k > n:
            return 0
        a, va = self.factorial_unit(n)
        b, vb = self.factorial_unit(k)
        c, vc = self.factorial_unit(n-k)
        v = va-vb-vc
        assert v >= 0
        if v >= self.precision:
            return 0
        return (a * pow(b*c % self.modulus, -1, self.modulus)
                * 5**v) % self.modulus


class JointFive:
    def __init__(self, precision=3):
        assert precision >= 2
        self.precision = precision
        self.modulus = p = 5**precision
        self.cartier = BoundedCartier(precision)
        self.binomial = BinomialFive(precision)
        self.half = pow(2, -1, p)
        self.quarter = pow(4, -1, p)

    def endpoint_e(self, j):
        p = self.modulus
        z1 = gaussian_power((1, self.half), j, p)
        z2 = gaussian_power((3*self.quarter % p, self.quarter), j, p)
        return -2*(z1[1]+z2[1]) % p

    def endpoint_j(self, j):
        return -2*gaussian_power((-1, 2), j, self.modulus)[1] % self.modulus

    def polynomial_coefficient(self, n, k):
        """[y^k](1+6y+25y^2)^(2n)/(1-25y)^(3n+1)."""
        p, choose = self.modulus, self.binomial.choose
        if k < 0:
            return 0
        result = 0
        for total in range((self.precision-1)//2+1):
            for u in range(total+1):
                v = total-u
                linear = k-2*u-v
                if not (0 <= u <= 2*n and 0 <= linear <= 2*n-u):
                    continue
                result += (25**total * choose(2*n, u)
                           * choose(2*n-u, linear) * pow(6, linear, p)
                           * choose(3*n+v, v))
        return result % p

    def pair(self, n, components=False):
        assert n >= 1
        p, a, s = self.modulus, self.precision, shell(n)
        norm = pow(2, (2-5*n//2) % (4*5**(a-1)), p)
        partial, polynomial = 0, 0
        partial_step = 5**max(0, s-a+1)
        # All surviving partial-fraction indices share this whole prefix.
        # A zero scalar coefficient would not suffice for this optimization.
        state = self.cartier.initial
        low_n, low_w, remaining_step = n, 3*n, partial_step
        while remaining_step > 1:
            state = self.cartier.step(state, low_n % 5, low_w % 5)
            low_n //= 5
            low_w //= 5
            remaining_step //= 5

        def coefficient_after_prefix(shift):
            remainder_n, remainder_w, current = low_n, low_w-shift, state
            if remainder_w < 0:
                return 0
            while remainder_n or remainder_w:
                current = self.cartier.step(current, remainder_n % 5, remainder_w % 5)
                remainder_n //= 5
                remainder_w //= 5
            return current[0][0] * self.cartier.invconstant % p

        for j in range(partial_step, 3*n+1, partial_step):
            t = valuation(j)
            power = s-t
            assert power >= 0
            if power >= a:
                continue
            coefficient = coefficient_after_prefix(j//partial_step)
            partial += (coefficient * self.endpoint_e(j) * 5**power
                        * pow(j//5**t, -1, p))
        partial = norm * (-1)**(n+1) * partial % p
        polynomial_step = 5**max(0, s-a+2)
        for j in range(polynomial_step, 4*n, 2*polynomial_step):
            t = valuation(j)
            power = 1+s-t
            assert power >= 1
            if power >= a:
                continue
            k = (4*n-1-j)//2
            polynomial += (self.polynomial_coefficient(n, k) * self.endpoint_j(j)
                           * 5**power * pow(j//5**t, -1, p))
        polynomial = norm * polynomial % p
        q = (-1)**n * norm * self.half * coefficient_after_prefix(0) % p
        result = (q, (partial+polynomial) % p)
        if components:
            return result, {'partial': partial, 'polynomial': polynomial, 's': s}
        return result


def core_precision(length):
    best, a = 0, 2
    while True:
        h = 1
        while 4*5**(h-1) < a-1:
            h += 1
        if 4*a*(5*h+100) > length:
            return best
        best, a = a, a+1


def joint_precision(length):
    return core_precision(14*length//15)


def proof_constants():
    # delta_* = (1+14 log_5(91/20))/15 < 52/55.
    assert 91**154 < 20**154 * 5**145
    # log_5(3) < 7/10, so the Kummer exponent is below 18/25.
    assert 3**10 < 5**7
    # 52/55 < H_2(4/11) < H_2(phi^-2).
    assert 11**55 > 4**20 * 7**35 * 2**52
    return {'cartier_exponent_lt': '52/55', 'kummer_exponent_lt': '18/25',
            'joint_precision_first_nonzero_length': 900,
            'precision_samples': {str(L): joint_precision(L)
                                  for L in [899, 900, 1000, 10000, 100000, 1000000]}}


def verify(precision, recurrence_limit, sample_indices):
    sys.path.insert(0, str(experiment_directory('salikhov_mod5_support_20260906')))
    from full_pair import recurrence_sequences, p2, power, mul
    now = time.monotonic()
    E = JointFive(precision)
    p = E.modulus
    for n in range(100):
        for k in range(n+1):
            assert E.binomial.choose(n, k) == comb(n, k) % p, (n, k)
    for n in range(1, 16):
        numerator = power([1, 6, 25], 2*n, 2*n-1)
        denominator = [comb(3*n+k, k)*25**k for k in range(2*n)]
        direct = mul(numerator, denominator, 2*n-1)
        assert all(E.polynomial_coefficient(n, k) == x % p
                   for k, x in enumerate(direct)), n
    maximum = max([recurrence_limit, *sample_indices], default=recurrence_limit)
    aa, bb = recurrence_sequences(maximum)
    indices = sorted(set(range(1, recurrence_limit+1)) | set(sample_indices))
    samples = []
    for n in indices:
        q = p2(2-5*n//2) * bb[n]
        v = 5**shell(n) * p2(2-5*n//2) * aa[n]
        assert q.denominator == 1 and v.denominator % 5
        expected = (q.numerator % p,
                    v.numerator * pow(v.denominator, -1, p) % p)
        actual, components = E.pair(n, components=True)
        assert actual == expected, (n, actual, expected)
        if n in sample_indices:
            samples.append({'n': n, 'q_mod': actual[0], 'v_mod': actual[1],
                            **components, 'vq': rational_valuation(q),
                            'vv': rational_valuation(v),
                            'vQ': max(0, shell(n)+rational_valuation(q)-rational_valuation(v))})
    family = []
    for n in range(4, maximum+1, 4):
        k = valuation(n, 2)
        if (3*(n >> k)).bit_count() > k:
            continue
        q = p2(2-5*n//2) * bb[n]
        v = 5**shell(n) * p2(2-5*n//2) * aa[n]
        vq, vv = rational_valuation(q), rational_valuation(v)
        family.append((n, vq, vv, shell(n), max(0, shell(n)+vq-vv)))
    census = Counter('equal' if row[1] == row[2] else 'q_higher' if row[1] > row[2]
                     else 'v_higher' for row in family)
    return {'modulus': p, 'recurrence_checked_through': recurrence_limit,
            'sample_indices': samples, 'family_cutoff': maximum,
            'family_count': len(family), 'valuation_comparison': dict(census),
            'family_q_higher': [row for row in family if row[1] > row[2]],
            'proof_constants': proof_constants(), 'seconds': round(time.monotonic()-now, 3)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--precision', type=int, default=3)
    parser.add_argument('--check', type=int, default=45)
    parser.add_argument('--samples', type=int, nargs='*', default=[1072, 1536, 2000])
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    result = verify(args.precision, args.check, args.samples)
    payload = json.dumps(result, indent=2) + '\n'
    if args.json:
        args.json.write_text(payload)
    print(payload, end='')
