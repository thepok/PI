#!/usr/bin/env python3
"""Exact finite checks for a mixed modified-Salikhov approximation family.

This is an experiment. The all-k argument and the asymptotic approximation
rate require the accompanying proof sketch. The script uses no pi digits,
floating point, external packages, network access, or untracked local files.

The recurrence is the published oSALIKHOVpi3 recurrence, normalized from
E_n=-I_n/5 to I_n=a_n+b_n*pi. Its primary source is
https://arxiv.org/html/1912.06345v2, Part II.

The modular evaluator implements the finite-precision root-coefficient
formula proved in the odd-multiplier note. Its residues are q_n itself,
not q_n divided by a possibly different odd unit at each index.
"""

from __future__ import annotations

import argparse
from array import array
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial, lcm
from pathlib import Path


def valuation_two(value: int) -> int:
    if value == 0:
        raise ValueError("Zero has no finite two-adic valuation")
    value = abs(value)
    return (value & -value).bit_length()-1


def integer_valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("Zero has no finite prime valuation")
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def valuation(value: Fraction | int, prime: int) -> int:
    value = Fraction(value)
    return (integer_valuation(value.numerator, prime)
            - integer_valuation(value.denominator, prime))


def floor_log_five(value: int) -> int:
    assert value > 0
    exponent = 0
    while value >= 5:
        value //= 5
        exponent += 1
    return exponent


def companion_two_bound(index: int) -> int:
    return 2*index+1-((4*index+1).bit_length()-1)


def index_parameters(k: int) -> dict:
    """Return the literal index construction, using integer arithmetic."""
    assert k >= 1
    n = (5**k+1)//2
    if k <= 6:
        ell = (n-1).bit_length()
        m = 1
    else:
        ell = n.bit_length()-7
        m = n >> ell
        if m % 2 == 0:
            m -= 1
    r = m << ell
    e = (3*m).bit_count()
    assert ell >= 2 and m % 2 == 1 and e <= ell
    if k <= 6:
        assert r >= n and e == 2
    else:
        assert ell >= 8 and 63 <= m < 128 and e <= 8
        assert 31*n < 32*r <= 32*n
    s = floor_log_five(4*r)
    bound = min(companion_two_bound(n), companion_two_bound(r))-e-1
    assert bound > 0
    return {"k": k, "n": n, "r": r, "L": ell, "m": m, "e": e,
            "five_clearing_exponent": k+s+1, "P_two_bound": bound}


class ModularMultiplier:
    """Evaluate the actual normalized multiplier q_n modulo 2^11.

    Only terms with outer offset ell < 11-(n mod 2) can contribute.
    Odd factorial units are evaluated recursively. The factorial product
    over a complete block of odd residues modulo 2^11 is one.
    """

    precision = 11
    modulus = 1 << precision

    def __init__(self):
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
        for offset in range(min(self.precision-parity, 2*n-s0+1)):
            s = s0+offset
            outer = self.binomial(2*n, s)*pow(25, 2*n-s, self.modulus)
            subtotal = 0
            for b in range(min(s, 2*offset+parity)+1):
                j = 2*s-b-n
                exponent = parity+offset+j.bit_count()
                if exponent < self.precision:
                    subtotal += (binomial_units[j]*comb(s, b)
                                 * pow(7, b, self.modulus)) << exponent
            total = (total+outer*subtotal) % self.modulus
        return total


def modular_choice(parameters: dict, evaluator: ModularMultiplier) -> dict:
    k, n, r, e = (parameters[key] for key in ('k', 'n', 'r', 'e'))
    qn, qr = evaluator.multiplier(n), evaluator.multiplier(r)
    assert qr != 0 and valuation_two(qr) == e, ("even-family valuation", k)
    weight = pow(5, parameters['five_clearing_exponent'], evaluator.modulus)
    first = (qn+weight*qr) % evaluator.modulus
    choice = 1 if first % (1 << (e+2)) != 0 else 3
    mixed = (qn+choice*weight*qr) % evaluator.modulus
    assert mixed != 0 and valuation_two(mixed) <= e+1 <= 9
    return {**parameters, "coefficient_choice": choice,
            "q_n_mod2048": qn, "q_r_mod2048": qr,
            "mixed_q_mod2048": mixed,
            "mixed_q_two_valuation": valuation_two(mixed)}


def recurrence_coefficients(n: int) -> tuple[int, int, int, int]:
    return (
        -1024*(2*n+5)*(2*n+3)*(2*n+1)*(n+2)*(n+1)
        *(559455*n**4+5637736*n**3+21207869*n**2+35294652*n+21926016),
        64*(2*n+5)*(2*n+3)*(n+2)
        *(1208982255*n**6+14601112006*n**5+71554462078*n**4
          +181444545414*n**3+250049018747*n**2+176898555884*n+50159702880),
        -6*(2*n+5)
        *(440102548665*n**8+7075613606958*n**7+49182254436312*n**6
          +192978557313766*n**5+467319046780891*n**4+714892923466956*n**3
          +674376299494052*n**2+358497976451216*n+82191375084672),
        3*(4*n+11)*(3*n+8)*(3*n+7)*(4*n+9)*(n+3)
        *(559455*n**4+3399916*n**3+7651391*n**2+7554302*n+2760952),
    )


def recurrence_pairs(bound: int):
    """Yield actual rational pairs through bound, with constant pair memory."""
    a = [Fraction(0), -Fraction(11272, 3), -Fraction(6156093056, 105)]
    b = [Fraction(1, 4), Fraction(1196), Fraction(18662336)]
    for n in range(min(3, bound+1)):
        yield n, a[n], b[n]
    for n in range(max(0, bound-2)):
        coefficients = recurrence_coefficients(n)
        next_a = -sum(coefficients[j]*a[j] for j in range(3))/coefficients[3]
        next_b = -sum(coefficients[j]*b[j] for j in range(3))/coefficients[3]
        a = a[1:]+[next_a]
        b = b[1:]+[next_b]
        yield n+3, next_a, next_b


def exact_recurrence_checks(rows: list[dict], evaluator: ModularMultiplier) -> list[dict]:
    needed = {row[key] for row in rows for key in ('n', 'r')}
    pairs = {}
    for index, a, b in recurrence_pairs(max(needed)):
        if index not in needed:
            continue
        scale = Fraction(1, 2**(5*index//2-2))
        c, q = scale*a, scale*b
        assert q.denominator == 1 and q > 0
        assert q.numerator % evaluator.modulus == evaluator.multiplier(index)
        assert valuation(c, 2) >= companion_two_bound(index)
        assert valuation(c, 5) >= -floor_log_five(4*index)
        pairs[index] = (c, q.numerator)

    # Check the exact denominator clearing claimed in the proof at every
    # selected source index; odd lcm(1,...,4j) is lcm of the odd integers.
    odd_lcm, next_odd = 1, 1
    for index in sorted(needed):
        while next_odd <= 4*index:
            odd_lcm = lcm(odd_lcm, next_odd)
            next_odd += 2
        assert odd_lcm % pairs[index][0].denominator == 0, ("denominator", index)

    exact_rows = []
    for row in rows:
        k, n, r, e = (row[key] for key in ('k', 'n', 'r', 'e'))
        cn, qn = pairs[n]
        cr, qr = pairs[r]
        assert valuation(qn, 5) == k and valuation(cn, 5) == 0
        assert valuation(qr, 2) == e
        weight = row['coefficient_choice']*5**row['five_clearing_exponent']
        cstar, qstar = cn+weight*cr, qn+weight*qr
        assert qstar > 0 and valuation(qstar, 5) == k and valuation(cstar, 5) == 0
        assert qstar % evaluator.modulus == row['mixed_q_mod2048']
        assert valuation(qstar, 2) == row['mixed_q_two_valuation']
        approximation = -cstar/qstar
        p, q = approximation.numerator, approximation.denominator
        assert q % 2 == 1 and valuation(q, 5) == k
        assert valuation(p, 2) >= row['P_two_bound'] > 0
        exact_rows.append({"k": k, "n": n, "r": r,
                           "coefficient_choice": row['coefficient_choice'],
                           "Q_five_valuation": valuation(q, 5),
                           "P_two_valuation": valuation(p, 2),
                           "P_two_bound": row['P_two_bound'],
                           "mixed_q_two_valuation": valuation(qstar, 2),
                           "Q_bit_length": q.bit_length()})
    return exact_rows


def exact_rate_certificate() -> dict:
    def cubic(x: int) -> int:
        return 108*x**3-2359989*x**2+138304*x-2048

    assert cubic(21000) < 0 < cubic(22000)
    # The exponential-series tail from 1/5! onward is at most 1/100:
    # successive ratios are at most 1/6, and (1/120)/(1-1/6)=1/100.
    upper_e = sum(Fraction(1, factorial(j)) for j in range(5))+Fraction(1, 100)
    assert upper_e < Fraction(11, 4)
    lhs = 21000**129*3**465*4**1344
    rhs = 2**555*11**1344
    assert lhs > rhs
    assert 21000**93*3**93 > 2**599*5**320
    return {"cubic_at_21000": cubic(21000), "cubic_at_22000": cubic(22000),
            "exponential_upper_bound": str(upper_e),
            "integer_comparison": "21000^129*3^465*4^1344 > 2^555*11^1344",
            "integer_comparison_passed": True,
            "horizon_comparison_31_gamma_over_32_gt_5_log10": True,
            "lhs_bit_length": lhs.bit_length(), "rhs_bit_length": rhs.bit_length(),
            "approximation_exponent": "21/20",
            "scope": "Exact constant inequality; asymptotic input and all-k proof are in the note"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-depths', type=int, default=5,
                        help='Full rational recurrence depths; default requires indices through 2048')
    parser.add_argument('--modular-depths', type=int, default=100)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if not 1 <= args.exact_depths <= args.modular_depths:
        parser.error('Require 1 <= --exact-depths <= --modular-depths')

    evaluator = ModularMultiplier()
    rate = exact_rate_certificate()
    rows = [modular_choice(index_parameters(k), evaluator)
            for k in range(1, args.modular_depths+1)]
    exact = exact_recurrence_checks(rows[:args.exact_depths], evaluator)
    certificate = {
        "status": "experiment; all-index claims require 20261017-salikhov-mixed-precision.md",
        "exact_rate_constant_certificate": rate,
        "full_exact_recurrence_checks": exact,
        "modular_mixed_multiplier_checks": rows,
        "limitations": [
            "No finite sample proves the all-index claims.",
            "The asymptotic exponent is eventual; this script does not provide its threshold.",
            "No prescribed decimal target, error sign, or V1 conclusion is asserted.",
        ],
    }
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(certificate, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({"status": "experiment; checks passed",
                      "exact_recurrence_depths": len(exact),
                      "selected_source_denominators_checked": len({row[key] for row in rows[:args.exact_depths]
                                                                   for key in ('n', 'r')}),
                      "modular_mixture_depths": len(rows),
                      "rate_constant_certificate": "passed",
                      "max_mixed_q_two_valuation": max(row['mixed_q_two_valuation'] for row in rows),
                      "coefficient_three_depths": [row['k'] for row in rows if row['coefficient_choice'] == 3]},
                     indent=2))


if __name__ == '__main__':
    main()
