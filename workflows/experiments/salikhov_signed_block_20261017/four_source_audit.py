#!/usr/bin/env python3
"""Exact checks for positive four-source modified-Salikhov mixtures.

Label: experiment. Infinite validity requires the repository note
knowledge/pi/results/intermediate/20261017-salikhov-four-source-brackets.md
and its explicitly cited arithmetic and actual-integral asymptotic inputs. Standard
library only. No external pi digits, floating point, or asymptotic sign guesses.

Default exact examples use k=3,4,5 and individually verified four-source blocks.
The literal eventual grid has guaranteed binary orders from k=11. Its audit
checks arithmetic for all four potential sources, not actual pi signs there.

Primary recurrence:
https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt
It is normalized here from E_n=-I_n/5 to I_n=a_n+b_n*pi.
"""

from __future__ import annotations

import argparse
from array import array
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, factorial, lcm
from pathlib import Path


def v2(value: int) -> int:
    value = abs(value)
    if not value:
        raise ValueError("Zero has no finite valuation")
    return (value & -value).bit_length()-1


def valuation(value: F | int, prime: int) -> int:
    value = F(value)
    if not value:
        raise ValueError("Zero has no finite valuation")
    a, b, result = abs(value.numerator), value.denominator, 0
    while a % prime == 0:
        a //= prime
        result += 1
    while b % prime == 0:
        b //= prime
        result -= 1
    return result


def log5_floor(n: int) -> int:
    result = 0
    while n >= 5:
        n //= 5
        result += 1
    return result


def companion_bound(j: int) -> int:
    return 2*j+1-((4*j+1).bit_length()-1)


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


def recurrence_pairs(limit: int):
    a = [F(0), -F(11272, 3), -F(6156093056, 105)]
    b = [F(1, 4), F(1196), F(18662336)]
    for j in range(min(3, limit+1)):
        yield j, a[j], b[j]
    for n in range(max(0, limit-2)):
        p = recurrence_coefficients(n)
        a = a[1:]+[-sum(p[j]*a[j] for j in range(3))/p[3]]
        b = b[1:]+[-sum(p[j]*b[j] for j in range(3))/p[3]]
        yield n+3, a[-1], b[-1]


class MultiplierModPowerTwo:
    """Actual q_n modulo 2^14 using the proved finite root-coordinate sum.

    This returns q_n itself, not q_n divided by an index-dependent odd unit.
    Each omitted outer term is individually divisible by the modulus.
    """
    precision = 14
    modulus = 1 << precision

    def __init__(self):
        self.prefix = array('I', [1])*self.modulus
        product = 1
        for j in range(1, self.modulus):
            if j & 1:
                product = product*j % self.modulus
            self.prefix[j] = product
        assert product == 1

    @lru_cache(maxsize=None)
    def factorial_unit(self, n: int) -> int:
        if n == 0:
            return 1
        return self.prefix[n % self.modulus]*self.factorial_unit(n//2) % self.modulus

    def binomial(self, n: int, k: int) -> int:
        order = k.bit_count()+(n-k).bit_count()-n.bit_count()
        if order >= self.precision:
            return 0
        unit = self.factorial_unit(n)
        unit *= pow(self.factorial_unit(k), -1, self.modulus)
        unit *= pow(self.factorial_unit(n-k), -1, self.modulus)
        return (unit << order) % self.modulus

    def multiplier(self, n: int) -> int:
        parity, s0 = n & 1, (n+1)//2
        units, total = [1], 0
        for j in range(1, 2*self.precision+2):
            unit = units[-1]*(2*n+1-2*j)
            unit *= pow(j >> v2(j), -1, self.modulus)
            units.append(unit % self.modulus)
        for offset in range(min(self.precision-parity, 2*n-s0+1)):
            s = s0+offset
            outer = self.binomial(2*n, s)*pow(25, 2*n-s, self.modulus)
            subtotal = 0
            for b in range(min(s, 2*offset+parity)+1):
                j = 2*s-b-n
                order = parity+offset+j.bit_count()
                if order < self.precision:
                    subtotal += (units[j]*comb(s, b)*pow(7, b, self.modulus)) << order
            total = (total+outer*subtotal) % self.modulus
        return total


def fixed_certificates() -> dict:
    def chi(x):
        return 108*x**3-2359989*x*x+138304*x-2048

    assert chi(21000) < 0 < chi(22000)
    exp_upper = sum(F(1, factorial(j)) for j in range(5))+F(1, 100)
    assert exp_upper < F(11, 4)
    lhs, rhs = 21000**77*3**279*4**832, 2**332*11**832
    assert lhs > rhs
    scale = 1 << 96
    lo, hi = 21851*scale, 21852*scale
    assert chi(F(lo, scale)) < 0 < chi(F(hi, scale))
    assert 324*21851**2-4719978*21851+138304 > 0
    while hi-lo > 1:
        mid = (lo+hi)//2
        if chi(F(mid, scale)) < 0:
            lo = mid
        else:
            hi = mid
    lower, upper = F(lo, scale), F(hi, scale)
    root_sum, root_product = F(2359989, 108), F(2048, 108)
    assert 0 < root_sum-upper < root_sum-lower
    cos2_lower = lower*(root_sum-upper)**2/(4*root_product)
    cos2_upper = upper*(root_sum-lower)**2/(4*root_product)
    assert F(1, 100) < 1-cos2_upper < 1-cos2_lower < F(11, 1000)
    assert F(51, 500)**2 < 1-cos2_upper
    assert F(11, 989) < F(53, 500)**2
    return {"rate_integer_comparison_passed": True,
            "rate_integer_comparison": "21000^77*3^279*4^832 > 2^332*11^832",
            "approximation_exponent": "13/12", "e_upper_bound": str(exp_upper),
            "root_interval_scale": scale, "root_interval_lower": lo,
            "root_interval_upper": hi, "sin_theta_squared_in": ["1/100", "11/1000"],
            "sin_theta_squared_stronger_lower_bound": "2601/250000",
            "theta_interval": ["51/500", "53/500"],
            "adjacent_phase_gap_certified": True}


def grid(k: int) -> dict:
    assert k >= 11
    n = (5**k+1)//2
    ell = n.bit_length()-8
    m = (63*n)//(64 << ell)
    if not m & 1:
        m -= 1
    r, e = m << ell, (3*m).bit_count()
    assert n >= 1 << 18 and ell >= 17 and 125 <= m <= 251
    assert e <= 9 and e <= ell-2
    assert 31*n < 32*r and 64*r <= 63*n
    assert 128*(r+31) <= 127*n
    assert companion_bound(r)-12 > 0
    return {"k": k, "n": n, "L": ell, "m": m, "r": r, "e": e}


def positive_choice(qn: int, qj: int, weight: int, order: int) -> int:
    return 1 if (qn+weight*qj) % (1 << (order+2)) else 3


def grid_checks(max_k: int, evaluator: MultiplierModPowerTwo) -> list[dict]:
    rows = []
    for k in range(11, max_k+1):
        data = grid(k)
        n, r, e = data['n'], data['r'], data['e']
        qn = evaluator.multiplier(n)
        choices = []
        for offset in (0, 1, 30, 31):
            j = r+offset
            order = e+(0 if offset == 0 else 2)
            qj = evaluator.multiplier(j)
            assert qj and v2(qj) == order
            weight = pow(5, k+log5_floor(4*j)+1, evaluator.modulus)
            lam = positive_choice(qn, qj, weight, order)
            mixed = (qn+lam*weight*qj) % evaluator.modulus
            assert mixed and v2(mixed) <= order+1 <= 12
            choices.append({"source_offset": offset, "lambda": lam,
                            "source_q_v2": order, "mixed_q_mod16384": mixed,
                            "mixed_q_v2": v2(mixed)})
        rows.append({**data, "potential_source_choices": choices})
    return rows


def arctan_fixed(q: int, scale: int) -> tuple[int, int]:
    total, qpower, j = 0, q, 0
    while True:
        term = scale//((2*j+1)*qpower)
        if not term:
            return total, j+1
        total += term if j % 2 == 0 else -term
        qpower *= q*q
        j += 1


def pi_interval(bits: int) -> tuple[F, F, int]:
    scale = 1 << bits
    a, ea = arctan_fixed(5, scale)
    b, eb = arctan_fixed(239, scale)
    center, error = 16*a-4*b, 16*ea+4*eb
    lo, hi = F(center-error, scale), F(center+error, scale)
    assert 3 < lo < hi < 4
    return lo, hi, error


def absolute_interval(interval: tuple[F, F]) -> tuple[F, F]:
    lo, hi = interval
    return (F(0) if lo <= 0 <= hi else min(abs(lo), abs(hi)), max(abs(lo), abs(hi)))


def finite_pair(k: int) -> dict:
    """Largest old even-family source with all four offsets below63*n/64.

    These are finite sample choices. Every needed binary order is also
    checked directly; the eventual-grid congruence threshold is not assumed.
    """
    n = (5**k+1)//2
    possibilities = []
    for ell in range(3, n.bit_length()):
        for m in range(1, ((63*n//64-31) >> ell)+1, 2):
            e = (3*m).bit_count()
            if e <= ell-2:
                possibilities.append((m << ell, ell, m, e))
    r, ell, m, e = max(possibilities)
    return {"k": k, "n": n, "r": r, "L": ell, "m": m, "e": e}


def error_upper_power_two(error: F) -> int:
    """Return an integer b with 0<error<=2^b, using only integer comparisons."""
    assert error > 0
    b = error.numerator.bit_length()-error.denominator.bit_length()
    power = F(1 << b) if b >= 0 else F(1, 1 << (-b))
    return b if error <= power else b+1


def polynomial_product(a, b, limit):
    result = [0]*min(limit+1, len(a)+len(b)-1)
    for j, x in enumerate(a):
        for k, y in enumerate(b[:max(0, len(result)-j)]):
            result[j+k] += x*y
    return result


def polynomial_power(a, exponent, limit):
    result = [1]
    while exponent:
        if exponent & 1:
            result = polynomial_product(result, a, limit)
        exponent //= 2
        if exponent:
            a = polynomial_product(a, a, limit)
    return result


def fixed_coefficient(s):
    # This is (1-2y)J(y), expanded directly in integers.
    coefficients = polynomial_power([2, -18, 67, -128, 125, -50], 2*s, 3*s)
    integer = sum(c*comb(6*s-j, 3*s-j) for j, c in enumerate(coefficients))
    value = F((-1)**s*integer, 1 << (s//2))
    assert value.denominator == 1
    return int(value)


def fixed_shift_checks(evaluator):
    small = []
    for s, _, b in recurrence_pairs(63):
        exponent = 2-5*s//2
        factor = F(1 << exponent) if exponent >= 0 else F(1, 1 << (-exponent))
        q = factor*b
        assert q.denominator == 1 and q > 0
        assert int(q) == fixed_coefficient(s)
        assert int(q) % evaluator.modulus == evaluator.multiplier(s)
        small.append(int(q))
    orders = [v2(q) for q in small]
    assert [orders[s] for s in (0, 1, 30, 31)] == [0, 2, 2, 2]
    cases, valuation_cases = [], 0
    for ell in (12, 16, 19):
        for m in (1, 2, 3, 5, 6, 7):
            n, exponent = m << ell, (3*m).bit_count()
            modulus = 1 << (ell-5)
            central = evaluator.binomial(n, n//4)
            assert central % modulus and v2(central) == exponent
            for shift in range(64):
                q = evaluator.multiplier(n+shift)
                assert (q-small[shift]*central) % modulus == 0
                if exponent+orders[shift] < ell-5:
                    assert q and v2(q) == exponent+orders[shift]
                    valuation_cases += 1
            cases.append({"L": ell, "m": m, "N": n, "shifts_checked": 64,
                          "modulus_exponent": ell-5})
    pi_lo, pi_hi, _ = pi_interval(128)
    assert F(31, 10) < pi_lo < pi_hi < F(22, 7)
    lower_theta, upper_theta = F(51, 500), F(53, 500)
    assert 31*upper_theta < 2*F(31, 10)
    assert F(31, 10)-upper_theta > F(1, 100)
    assert F(31, 10)-29*upper_theta > F(1, 100)
    assert 31*lower_theta-F(22, 7) > F(1, 100)
    return {"recurrence_vs_direct_fixed_coefficient_checks": 64,
            "modular_shift_cases": len(cases)*64,
            "exact_valuation_cases": valuation_cases, "instances": cases,
            "four_source_offsets": [0, 1, 30, 31],
            "four_source_q_valuations": [0, 2, 2, 2],
            "four_point_circular_gap_bound": "pi-1/100",
            "four_point_both_cosine_margin": "1/400",
            "four_gap_integer_comparisons_passed": True}


def exact_examples(max_k: int, evaluator: MultiplierModPowerTwo) -> dict:
    data = [finite_pair(k) for k in range(3, max_k+1)]
    offsets = (0, 1, 30, 31)
    needed = {j for d in data for j in (d['n'], *(d['r']+s for s in offsets))}
    limit, pairs, recurrence_modular_comparisons = max(needed), {}, 0
    for j, a, b in recurrence_pairs(limit):
        if 1 <= j <= 80 or j in needed:
            scale = F(1, 1 << (5*j//2-2))
            c, q = scale*a, scale*b
            assert q.denominator == 1 and q > 0
            assert int(q) % evaluator.modulus == evaluator.multiplier(j)
            recurrence_modular_comparisons += 1
            if j in needed:
                assert valuation(c, 2) >= companion_bound(j)
                pairs[j] = c, int(q)
    bits = 24*limit+256
    lo, hi, error_scaled = pi_interval(bits)
    odd_lcm, next_odd = 1, 1
    for j in sorted(needed):
        while next_odd <= 4*j:
            odd_lcm = lcm(odd_lcm, next_odd)
            next_odd += 2
        assert odd_lcm % pairs[j][0].denominator == 0
    rows = []
    for d in data:
        k, n, r, e = (d[key] for key in ('k', 'n', 'r', 'e'))
        sources = tuple(r+s for s in offsets)
        cn, qn = pairs[n]
        assert valuation(qn, 5) == k and valuation(cn, 5) == 0
        intervals = {j: (pairs[j][0]+pairs[j][1]*lo, pairs[j][0]+pairs[j][1]*hi)
                     for j in (n, *sources)}
        absolute = {j: absolute_interval(intervals[j]) for j in intervals}
        jplus = max(sources, key=lambda j: intervals[j][0])
        jminus = min(sources, key=lambda j: intervals[j][1])
        assert all(intervals[jplus][0] > intervals[j][1] for j in sources if j != jplus)
        assert all(intervals[jminus][1] < intervals[j][0] for j in sources if j != jminus)
        assert intervals[jplus][0] > 0 and intervals[jminus][1] < 0
        source_orders = [v2(pairs[j][1]) for j in sources]
        assert source_orders[0] == e and source_orders[1] == e+2
        assert max(source_orders) <= e+2 <= 11
        sign_rows = []
        for source_sign, j in ((1, jplus), (-1, jminus)):
            cj, qj = pairs[j]
            order, weight = v2(qj), 5**(k+log5_floor(4*j)+1)
            assert 6*weight*qj < qn
            assert 2*absolute[n][1] < weight*absolute[j][0]
            assert weight*abs(cj+qj*F(4, 9))*2 < abs(cn+qn*F(4, 9))
            lam = positive_choice(qn, qj, weight, order)
            cs, qs = cn+lam*weight*cj, qn+lam*weight*qj
            assert qs > 0 and valuation(qs, 2) <= order+1 <= 12
            assert valuation(qs, 5) == k and valuation(cs, 5) == 0
            approximation = -cs/qs
            p, q = approximation.numerator, approximation.denominator
            assert q % 2 == 1 and valuation(q, 5) == k
            assert valuation(p, 2) >= companion_bound(r)-12 > 0
            error_interval = lo-approximation, hi-approximation
            actual_sign = 1 if error_interval[0] > 0 else -1
            assert actual_sign == 1 or error_interval[1] < 0
            assert actual_sign == source_sign
            delta = max(abs(error_interval[0]), abs(error_interval[1]))
            rate_passed = delta.numerator**12*q**13 < delta.denominator**12
            assert p > 3*q
            sign_rows.append({"source": j, "source_error_sign": source_sign,
                              "lambda": lam, "mixing_coefficient_positive": True,
                              "pi_minus_approximant_sign": actual_sign,
                              "Q_five_valuation": valuation(q, 5),
                              "P_two_valuation": valuation(p, 2),
                              "proved_P_two_bound": companion_bound(r)-12,
                              "q_two_valuation": valuation(qs, 2),
                              "Q_bit_length": q.bit_length(),
                              "error_upper_power_of_two": error_upper_power_two(delta),
                              "rate_13_over_12_certified_in_this_instance": rate_passed,
                              "four_ninths_minus_approximant_sign": -1})
        assert {row['pi_minus_approximant_sign'] for row in sign_rows} == {-1, 1}
        rows.append({**d, "four_source_q_two_orders": source_orders,
                     "denominator_and_error_domination_certified": True,
                     "four_ninths_error_domination_fails": True,
                     "literal_eventual_grid_used": False, "positive_mixtures": sign_rows})
    return {"max_exact_k": max_k, "max_exact_n": limit, "pi_interval_bits": bits,
            "pi_interval_halfwidth_scaled": error_scaled,
            "recurrence_vs_modular_comparisons": recurrence_modular_comparisons,
            "each_selected_companion_denominator_divides_its_own_odd_lcm": True,
            "instances": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid-max-k', type=int, default=100)
    parser.add_argument('--exact-max-k', type=int, choices=(3, 4, 5), default=5)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.grid_max_k < 11:
        parser.error('--grid-max-k must be at least 11')
    evaluator = MultiplierModPowerTwo()
    result = {"label": "experiment", "fixed_certificates": fixed_certificates(),
              "fixed_shift_certificate": fixed_shift_checks(evaluator),
              "large_grid_scope": "Modular checks for four potential sources; actual source selection and signs are not evaluated at these large indices",
              "large_grid": grid_checks(args.grid_max_k, evaluator),
              "exact_actual_pi_examples": exact_examples(args.exact_max_k, evaluator)}
    if args.json:
        args.json.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({"saved": str(args.json), "grid_cases": len(result['large_grid']),
                          "exact_cases": len(result['exact_actual_pi_examples']['instances']),
                          "label": "experiment"}))
    else:
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
