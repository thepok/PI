#!/usr/bin/env python3
"""Exact finite checks for odd-index modified Salikhov cancellation.

The all-index arguments are the ramified lifting and finite-precision
coefficient formulas in the accompanying note. No pi digits, floating point,
external packages, or network access are used. The output label is experiment.
"""

from __future__ import annotations

import argparse
from array import array
from fractions import Fraction
from functools import lru_cache
import json
from math import comb
from pathlib import Path


def valuation_two(value: int) -> int:
    if value == 0:
        raise ValueError("Zero has no finite two-adic valuation")
    value = abs(value)
    return (value & -value).bit_length()-1


def polynomial_product(a: list[int], b: list[int], limit: int) -> list[int]:
    out = [0]*min(len(a)+len(b)-1, limit+1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:max(0, limit+1-i)]):
            out[i+j] += x*y
    return out


def polynomial_power(a: list[int], exponent: int, limit: int) -> list[int]:
    out = [1]
    while exponent:
        if exponent % 2:
            out = polynomial_product(out, a, limit)
        exponent //= 2
        if exponent:
            a = polynomial_product(a, a, limit)
    return out


def direct_multiplier(n: int) -> int:
    """Full exact expansion of the root-substitution coefficient identity."""
    degree = 3*n
    kernel = polynomial_power([32, 56, 25], 2*n, degree)
    coefficient = Fraction(0)
    binomial = Fraction(1)
    for j in range(degree+1):
        coefficient += binomial*kernel[degree-j]
        binomial *= Fraction(2*n-1-2*j, 2*(j+1))
    result = coefficient/2**(5*n//2)
    assert result.denominator == 1, ("integer multiplier", n)
    return result.numerator


def direct_ramified_multiplier(n: int) -> int:
    """Independent integer expansion after the ramified coordinate change."""
    assert n % 2 == 1
    degree = 3*n
    j_polynomial = [2, -14, 39, -50, 25]
    numerator = polynomial_power(
        polynomial_product([1, -2], j_polynomial, degree), 2*n, degree)
    coefficient = sum(x*comb(3*n+degree-i, degree-i)
                      for i, x in enumerate(numerator))
    divisor = 2**((n-1)//2)
    assert coefficient % divisor == 0
    return -coefficient//divisor


def valuation_residue(n: int, precision: int) -> int:
    """Return q_n divided by a common odd unit, modulo 2^precision.

    The common unit is the odd part of binom(2n,ceil(n/2)), multiplied by
    25^(2n-ceil(n/2)). This residue has the same valuation as q_n whenever
    it is nonzero. A zero residue certifies only v2(q_n) >= precision.
    """
    assert n >= 1 and precision >= 1
    modulus = 1 << precision
    parity = n % 2
    s0 = (n+1)//2
    outer_exponent = s0.bit_count()+(2*n-s0).bit_count()-n.bit_count()
    outer_unit = 1
    inverse25 = pow(25, -1, modulus)
    binomial_units = [1]
    for j in range(1, 2*precision+2):
        unit = binomial_units[-1]*(2*n+1-2*j)
        unit *= pow(j >> valuation_two(j), -1, modulus)
        binomial_units.append(unit % modulus)
    total = 0
    # Every omitted s=s0+ell term has absolute order >= parity+ell.
    for ell in range(min(precision-parity, 2*n-s0+1)):
        s = s0+ell
        if ell:
            numerator, denominator = 2*n-s+1, s
            outer_exponent += valuation_two(numerator)-valuation_two(denominator)
            outer_unit *= numerator >> valuation_two(numerator)
            outer_unit *= pow(denominator >> valuation_two(denominator), -1, modulus)
            outer_unit = outer_unit*inverse25 % modulus
        if parity+ell+outer_exponent >= precision:
            continue
        inner_exponent, inner_unit, seven_power, subtotal = 0, 1, 1, 0
        for b in range(min(s, 2*ell+parity)+1):
            if b:
                numerator, denominator = s-b+1, b
                inner_exponent += valuation_two(numerator)-valuation_two(denominator)
                inner_unit *= numerator >> valuation_two(numerator)
                inner_unit *= pow(denominator >> valuation_two(denominator), -1, modulus)
                inner_unit %= modulus
                seven_power = seven_power*7 % modulus
            j = 2*s-b-n
            exponent = parity+ell+j.bit_count()+inner_exponent+outer_exponent
            if exponent < precision:
                subtotal += (binomial_units[j]*inner_unit*seven_power) << exponent
        total = (total+subtotal*outer_unit) % modulus
    return total


def multiplier_valuation(n: int) -> int:
    s0 = (n+1)//2
    precision = s0.bit_count()+(2*n-s0).bit_count()-n.bit_count()+16
    while True:
        residue = valuation_residue(n, precision)
        if residue:
            return valuation_two(residue)
        precision *= 2


class FactorialUnitEvaluator:
    """A separate modular implementation with actual binomial units.

    Its output is q_n itself modulo 2^M. It uses factorial units rather
    than the binomial-ratio updates of valuation_residue, at a memory cost
    proportional to 2^M. This is only used at small fixed precision.
    """

    def __init__(self, precision: int):
        assert 3 <= precision <= 21
        self.precision = precision
        self.modulus = 1 << precision
        self.prefix = array('I', [1])*self.modulus
        product = 1
        for j in range(1, self.modulus):
            if j % 2:
                product = product*j % self.modulus
            self.prefix[j] = product
        assert product == 1

    @lru_cache(maxsize=None)
    def factorial_unit(self, n: int) -> int:
        if n == 0:
            return 1
        return (self.prefix[n % self.modulus]
                * self.factorial_unit(n//2) % self.modulus)

    def binomial(self, n: int, k: int) -> int:
        exponent = k.bit_count()+(n-k).bit_count()-n.bit_count()
        if exponent >= self.precision:
            return 0
        unit = self.factorial_unit(n)
        unit *= pow(self.factorial_unit(k), -1, self.modulus)
        unit *= pow(self.factorial_unit(n-k), -1, self.modulus)
        return (unit << exponent) % self.modulus

    def multiplier(self, n: int) -> int:
        parity, s0 = n % 2, (n+1)//2
        total = 0
        binomial_units = [1]
        for j in range(1, 2*self.precision+2):
            unit = binomial_units[-1]*(2*n+1-2*j)
            unit *= pow(j >> valuation_two(j), -1, self.modulus)
            binomial_units.append(unit % self.modulus)
        for ell in range(min(self.precision-parity, 2*n-s0+1)):
            s = s0+ell
            outer = self.binomial(2*n, s)*pow(25, 2*n-s, self.modulus)
            subtotal = 0
            for b in range(min(s, 2*ell+parity)+1):
                j = 2*s-b-n
                exponent = parity+ell+j.bit_count()
                if exponent < self.precision:
                    subtotal += (binomial_units[j]*comb(s, b)
                                 * pow(7, b, self.modulus)) << exponent
            total = (total+outer*subtotal) % self.modulus
        return total


def fixed_polynomial_checks() -> dict:
    # H(w)=25(w-1)^4+6(w-1)^2+1.
    original_h = [32, -112, 156, -100, 25]
    assert [original_h[0], 2*original_h[1], 8*original_h[2],
            16*original_h[3], 64*original_h[4]] == [32, -224, 1248, -1600, 1600]
    # Entries at odd positions are the coefficients of tau*z^j.
    assert [32, -224, 1248, -1600, 1600] == [32*x for x in [1, -7, 39, -50, 50]]
    j_polynomial = [2, -14, 39, -50, 25]
    numerator = polynomial_product(
        polynomial_power([1, -2], 2, 10), polynomial_power(j_polynomial, 2, 10), 10)
    tail_constant = -sum(x*comb(6-i, 3) for i, x in enumerate(numerator[:4]))
    assert tail_constant == 1196 and valuation_two(tail_constant) == 2
    return {"H_coefficients": original_h, "J_coefficients": j_polynomial,
            "H_tail_zero": tail_constant}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct', type=int, default=50)
    parser.add_argument('--max-L', type=int, default=12)
    parser.add_argument('--max-m', type=int, default=79)
    parser.add_argument('--crt-depths', type=int, default=20)
    parser.add_argument('--special-depths', type=int, default=100)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.direct < 1 or not 3 <= args.max_L <= 20 or args.max_m < 1:
        parser.error('Require --direct >= 1, 3 <= --max-L <= 20, --max-m >= 1')
    if args.crt_depths < 1 or args.special_depths < 1:
        parser.error('Depth counts must be positive')

    fixed = fixed_polynomial_checks()
    modular = FactorialUnitEvaluator(max(8, args.max_L+1))
    ramified_count = 0
    for n in range(1, args.direct+1):
        exact = direct_multiplier(n)
        assert multiplier_valuation(n) == valuation_two(exact), ("valuation", n)
        assert modular.multiplier(n) == exact % modular.modulus, ("modular", n)
        if n % 2:
            assert direct_ramified_multiplier(n) == exact, ("ramified", n)
            ramified_count += 1
    assert direct_multiplier(1) == 1196
    assert direct_multiplier(2) == 18662336//8

    congruence_counts = {"odd_m": 0, "even_m": 0}
    for ell in range(3, args.max_L+1):
        for m in range(1, args.max_m+1):
            index = 1+(1 << ell)*m
            multiplier = modular.multiplier(index)
            expected = 1196*modular.binomial(index-1, (index-1)//4)
            assert (multiplier-expected) % (1 << (ell+1)) == 0, ("odd congruence", ell, m)
            congruence_counts['odd_m' if m % 2 else 'even_m'] += 1
            if (3*m).bit_count() <= ell-2:
                assert multiplier_valuation(index) == 2+(3*m).bit_count()

    crt = []
    for a in range(1, args.crt_depths+1):
        ell, modulus_five = 3*a+4, 5**a
        m = (-pow(pow(2, ell+1, modulus_five), -1, modulus_five)) % modulus_five
        index = 1+(1 << ell)*m
        predicted = 2+(3*m).bit_count()
        assert 1 <= m < modulus_five
        assert (2*index-1) % modulus_five == 0
        assert predicted <= ell and multiplier_valuation(index) == predicted
        crt.append({"a": a, "L": ell, "m": m, "n": index,
                    "q_two_valuation": predicted,
                    "index_forced_five_depth_at_least": a})

    special = [{"k": k, "q_two_valuation": multiplier_valuation((5**k+1)//2)}
               for k in range(1, args.special_depths+1)]
    report = {
        "status": "experiment; all-index claims require the accompanying proof sketch",
        "fixed_polynomial_checks": fixed,
        "exact_root_coefficient_indices": [1, args.direct],
        "exact_ramified_coefficient_count": ramified_count,
        "congruence_range": {"L": [3, args.max_L], "m": [1, args.max_m]},
        "congruence_counts": congruence_counts,
        "crt_family": crt,
        "special_branch_two_valuations": special,
        "scope": "No computed five-adic q values at CRT indices, no reduced-Q five-adic survival there, and no decimal-digit conclusion.",
    }
    output = json.dumps(report, indent=2)+'\n'
    if args.json:
        args.json.write_text(output, encoding='utf-8')
    print(output, end='')


if __name__ == '__main__':
    main()
