#!/usr/bin/env python3
"""Exact checks of prime-isolated corrections to PR15's pi carrier.

The infinite statements are in the accompanying proof sketch. The checker
uses rational arithmetic, modular powers, and exact tail inequalities; it
does not use decimal digits of pi or floating point. Standard library only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import comb, gcd, lcm
from pathlib import Path
import json


def vp_integer(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError('Zero has no finite prime valuation')
    value = abs(value)
    if prime == 2:
        return (value & -value).bit_length()-1
    answer, power, exponent, chunks = 0, prime, 1, []
    while value % power == 0:
        value //= power
        answer += exponent
        chunks.append((power, exponent))
        power *= power
        exponent *= 2
    for power, exponent in reversed(chunks):
        if value % power == 0:
            value //= power
            answer += exponent
    return answer


def vp(value: F | int, prime: int) -> int:
    value = F(value)
    return vp_integer(value.numerator, prime)-vp_integer(value.denominator, prime)


def rough_part(value: int) -> int:
    for prime in (2, 5):
        value //= prime**vp_integer(value, prime)
    return value


def prime_factors(value: int) -> list[tuple[int, int]]:
    output, p = [], 2
    while p*p <= value:
        if value % p == 0:
            e = vp_integer(value, p)
            output.append((p, e))
            value //= p**e
        p += 1 if p == 2 else 2
    if value > 1:
        output.append((value, 1))
    return output


def rational_mod(value: F, modulus: int) -> int:
    return value.numerator*pow(value.denominator, -1, modulus) % modulus


def strict_decimal_upper(value: F) -> int:
    """Return an integer e with the exact certified inequality value < 10^e."""
    if value < 1:
        depth = 0
        while value*10**(depth+1) < 1:
            depth += 1
        exponent = -depth
    else:
        exponent = 0
        while value >= 10**exponent:
            exponent += 1
    assert value < F(10)**exponent
    return exponent


def triangle(k: int) -> tuple[int, int, int]:
    a, b, c = 1, 0, 1
    for _ in range(k):
        a, b, c = 3*a-4*b, 4*a+3*b, 5*c
    a, b = sorted((abs(a), abs(b)))
    assert a*a+b*b == c*c and gcd(a, b) == 1
    return a, b, c


def cancellation_weights(triangles) -> list[F]:
    sums = [F(a+b, c) for a, b, c in triangles]
    nodes = [s*s for s in sums]
    raw = []
    for i, node in enumerate(nodes):
        denominator = sums[i]
        for j, other in enumerate(nodes):
            if i != j:
                denominator *= node-other
        raw.append(1/denominator)
    total = sum(raw)
    return [x/total for x in raw]


class Carrier:
    def __init__(self):
        self.exponents = [1, 6, 11, 16]
        self.triangles = [triangle(k) for k in self.exponents]
        self.weights = cancellation_weights(self.triangles)
        self.q = lcm(*(w.denominator for w in self.weights))
        self.scale = lcm(*range(1, 4*len(self.triangles), 2))
        self.integer_weights = [int(self.scale*self.q*w) for w in self.weights]
        self.legs = [(F(a, c), F(b, c)) for a, b, c in self.triangles]
        self.common_hypotenuse = 5**self.exponents[-1]
        self.integer_legs = [(a*(self.common_hypotenuse//c),
                              b*(self.common_hypotenuse//c))
                             for a, b, c in self.triangles]
        assert sum(self.weights) == 1 and self.scale == 45045
        assert self.q == 324662081660072025546270114178816356
        assert self.moment(1) == self.moment(3) == self.moment(5) == 0
        ordered = sorted(range(4), key=lambda i: self.legs[i][1], reverse=True)
        first = ordered[0]
        self.y0 = self.legs[first][1]
        self.leading_weight = self.integer_weights[first]
        assert self.y0 == F(4, 5) and self.leading_weight > 0
        self.rho = self.y0**2
        ratio = max(self.legs[i][1]/self.y0 for i in ordered[1:])
        rest = sum(abs(self.integer_weights[i]) for i in ordered[1:])
        self.n0 = 0
        while 4*rest*ratio**(2*self.n0+1) > self.leading_weight:
            self.n0 += 1
        assert self.n0 == 57
        self.upper_constant = 2*sum(abs(w) for w in self.integer_weights)*self.y0

    def moment(self, h: int) -> F:
        numerator = sum(w*(a**h+b**h)
                        for w, (a, b) in zip(self.integer_weights, self.integer_legs))
        return F(numerator, self.common_hypotenuse**h)

    def moment_mod(self, h: int, modulus: int) -> int:
        total = 0
        for w, (a, b, c) in zip(self.integer_weights, self.triangles):
            inverse = pow(c, -1, modulus)
            total += w*(pow(a*inverse % modulus, h, modulus)
                        + pow(b*inverse % modulus, h, modulus))
        return total % modulus

    def term(self, n: int) -> F:
        return F(comb(2*n, n), 4**n*(2*n+1))*self.moment(2*n+1)

    def prefix(self, n: int) -> F:
        return sum((self.term(j) for j in range(n+1)), F(0))

    def positive_term_lower(self, n: int) -> F:
        assert n >= self.n0
        return self.leading_weight*self.y0**(2*n+1)/(2*(2*n+1)**2)

    def tail_upper(self, n: int) -> F:
        return self.upper_constant*self.rho**(n+1)/((2*n+3)*(1-self.rho))


def isolated_index(carrier: Carrier, prime: int, depth: int, n: int, budget: F):
    # The proof gives termination; the selected examples need only e<=3.
    for e in range(1, 8):
        for h in range(1, 4*len(carrier.triangles), 2):
            if h % prime == 0:
                continue
            residue = carrier.moment_mod(h*prime**e, prime**(e+1))
            if not residue:
                continue
            c = vp_integer(residue, prime)
            b = vp_integer(comb(h-1, (h-1)//2), prime)
            pole = e-c-b
            j = (h*prime**e-1)//2
            if pole < depth or j <= max(n, carrier.n0-1):
                continue
            if carrier.upper_constant*carrier.rho**j >= budget:
                continue
            return h, e, c, b, pole, j
    raise ValueError('Increase the search limit for this selected finite case')


def case(carrier: Carrier, n: int) -> dict:
    initial = carrier.prefix(n)
    current = initial
    original_five_depth = max(0, -vp(initial, 5))
    rough = rough_part(initial.denominator)
    factors = prime_factors(rough)
    assert factors
    delta = F(1, 2**n)
    budget = delta/len(factors)
    correction_sum = F(0)
    rows = []
    for prime, original_depth in factors:
        depth = -vp(current, prime)
        assert depth == original_depth and depth > 0
        h, e, c, b, pole, j = isolated_index(carrier, prime, depth, n, budget)
        term = carrier.term(j)
        assert term > 0 and term >= carrier.positive_term_lower(j)
        assert vp(term, prime) == -pole
        assert rough_part(term.denominator) == prime**pole
        modulus = prime**pole
        unit = rational_mod(term*modulus, modulus)
        z = rational_mod(current*modulus, modulus)*pow(unit, -1, modulus) % modulus
        assert 1 <= z < modulus <= prime**e <= 2*j+1
        correction = z*term
        assert 0 < correction < carrier.upper_constant*carrier.rho**j < budget
        current -= correction
        correction_sum += correction
        assert vp(current, prime) >= 0
        rough //= prime**depth
        assert rough_part(current.denominator) == rough
        term_five_depth = -vp(term, 5)
        necessary_extra_fives = max(0, term_five_depth-original_five_depth)
        smallest_height_preserving = 5**necessary_extra_fives
        assert smallest_height_preserving*term > 1
        rows.append({'prime': prime, 'original_prime_depth': depth,
                     'h': h, 'e': e, 'Teichmuller_moment_depth': c,
                     'top_binomial_depth': b, 'isolated_pole_depth': pole,
                     'correction_index': j, 'integer_coefficient': z,
                     'coefficient_five_valuation': vp(z, 5),
                     'term_five_denominator_depth': term_five_depth,
                     'minimum_coefficient_five_depth_to_preserve_original_height': necessary_extra_fives,
                     'minimum_height_preserving_added_error_exceeds_one': True,
                     'positive_correction_below_budget': True})
    assert 0 < correction_sum < delta
    assert rough_part(current.denominator) == 1
    numerator_five = vp_integer(current.numerator, 5)
    numerator_two = vp_integer(current.numerator, 2)
    denominator_two = vp_integer(current.denominator, 2)
    denominator_five = vp_integer(current.denominator, 5)
    clearing_exponent = max(denominator_two, denominator_five)
    # The original positive tail is at least its first omitted term's
    # certified lower bound. Correction subtraction only increases it.
    lower_original_error = carrier.positive_term_lower(n+1)
    assert 5**denominator_five*lower_original_error > 1
    unscaled_upper = carrier.tail_upper(n)+delta
    return {'N': n, 'initial_rough_prime_factors': factors,
            'initial_five_denominator_depth': original_five_depth,
            'corrections': rows,
            'result_rough_denominator': 1,
            'result_numerator_two_valuation': numerator_two,
            'result_numerator_five_valuation': numerator_five,
            'result_denominator_two_valuation': denominator_two,
            'result_denominator_five_valuation': denominator_five,
            'minimum_decimal_clearing_exponent': clearing_exponent,
            'decimal_cleared_numerator_two_valuation': numerator_two+clearing_exponent-denominator_two,
            'decimal_cleared_numerator_five_valuation': numerator_five+clearing_exponent-denominator_five,
            'added_positive_error_less_than_two_power': -n,
            'unscaled_positive_error_upper_less_than_ten_power': strict_decimal_upper(unscaled_upper),
            'full_decimal_clearing_makes_positive_tail_exceed_one': True,
            'result_numerator_bits': abs(current.numerator).bit_length(),
            'result_denominator_bits': current.denominator.bit_length()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--indices', default='80,160,400')
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    carrier = Carrier()
    assert 2**404 > 5**170
    data = {'status': 'experiment',
            'source_commit': '5fd8197ce4a48304392e6c350cee68e29631aaee',
            'gaussian_exponents': carrier.exponents,
            'fixed_integer_scale_L': carrier.scale,
            'fixed_pi_multiplier': str(F(carrier.scale*carrier.q, 2)),
            'positive_coefficient_threshold': carrier.n0,
            'five_height_tradeoff_certificate': {'left': str(2**404),
                                                 'right': str(5**170),
                                                 'left_greater': True},
            'cases': [case(carrier, int(n)) for n in args.indices.split(',')],
            'limitations': ['All-index existence and the uniform tradeoff require the written proof.',
                            'No prescribed decimal residue or occurrence theorem is asserted.',
                            'The exact error bounds use the positive series, not pi digits.']}
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': 'experiment; checks passed',
                      'fixed_pi_multiplier_bits': (carrier.scale*carrier.q//2).bit_length(),
                      'cases': [{'N': row['N'],
                                 'correction_indices': [c['correction_index'] for c in row['corrections']],
                                 'rough_denominator': row['result_rough_denominator'],
                                 'result_five_denominator_depth': row['result_denominator_five_valuation'],
                                 'cleared_positive_tail_exceeds_one': True}
                                for row in data['cases']]}, indent=2))


if __name__ == '__main__':
    main()
