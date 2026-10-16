#!/usr/bin/env python3
"""Exact finite audit of the Salikhov binary-weight family.

Label: experiment. The infinite assertions and inherited prerequisites are
in 20261016-salikhov-entropy-family.md. No floating-point phase prediction
or external pi digits are used. All dependencies are tracked stdlib scripts.

Example, from the repository root:
  python3 workflows/experiments/salikhov_entropy_family_20261016/audit.py \
      --census-limit 10000000 --sign-max-n 2000
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from math import comb, isqrt
from pathlib import Path
import sys

EXPERIMENTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EXPERIMENTS / "salikhov_mod5_support_20260906"))
sys.path.insert(0, str(EXPERIMENTS / "salikhov_dyadic_intersection_20261016"))
from full_pair import evaluate, recurrence_coefficients
from sign_check import mod5_rational, pi_interval, power2, v2_integer


def family_data(n):
    if n < 4:
        return None
    k = v2_integer(n)
    m = n >> k
    w = (3*m).bit_count()
    return (k, m, w) if k >= 2 and w <= k else None


def family_below(limit):
    for k in range(2, limit.bit_length()):
        for m in range(1, (limit >> k)+1, 2):
            if (3*m).bit_count() <= k:
                yield (1 << k)*m


def bounded_weight_count(limit, weight):
    """Count positive odd r<=limit with 3|r and popcount(r)<=weight."""
    if limit < 1 or weight < 0:
        return 0
    digits = [int(c) for c in bin(limit)[2:]]
    states = {(0, 0, True): 1}
    for pos, cap in enumerate(digits):
        next_states = Counter()
        for (ones, residue, tight), count in states.items():
            for bit in range((cap if tight else 1)+1):
                if pos == len(digits)-1 and bit != 1:
                    continue
                if ones+bit > weight:
                    continue
                key = (ones+bit, (2*residue+bit) % 3,
                       tight and bit == cap)
                next_states[key] += count
        states = next_states
    return sum(count for (_, residue, _), count in states.items()
               if residue == 0)


def family_count(limit):
    return sum(bounded_weight_count(3*(limit >> k), k)
               for k in range(2, limit.bit_length()))


def rotation_certificate():
    """All order-change breakpoints; affine interpolation is in the proof."""
    lo, hi = Q(1, 8), Q(3, 8)
    knots = {lo, hi}
    for denominator in range(1, 7):
        for numerator in range(denominator+1):
            t = Q(numerator, denominator)
            if lo <= t <= hi:
                knots.add(t)
    rows = []
    for t in sorted(knots):
        values = sorted({(j*t) % 1 for j in range(7)})
        largest = max(b-a for a, b in
                      zip(values, values[1:]+[values[0]+1]))
        assert largest <= Q(1, 3)
        rows.append({"t": str(t), "largest_circular_gap": str(largest)})
    assert len(rows) == 6
    return rows


def combinatorial_certificates():
    fibonacci = [0, 1]
    for _ in range(80):
        fibonacci.append(sum(fibonacci[-2:]))
    for cost in range(2, 81):
        count = 0
        for length in range(1, cost):
            ones = cost-length
            if 1 <= ones <= length:
                count += comb(length-1, ones-1)
        assert count == fibonacci[cost-1]
    images = set()
    for u in range(1, 10001):
        v = next(v for v in (1, 3, 5) if (8*u+v) % 3 == 0)
        r = 8*u+v
        k = r.bit_count()
        n = (1 << k)*(r//3)
        assert family_data(n) == (k, r//3, k)
        assert r.bit_length()+k <= u.bit_length()+u.bit_count()+5
        assert ((3*(n >> v2_integer(n))) >> 3) == u
        assert n not in images
        images.add(n)
    low_blocks = []
    for residue in range(3):
        v0 = next(v for v in (1, 3, 5) if (64*residue+v) % 3 == 0)
        values = [v0+6*j for j in range(7)]
        assert all(v % 2 == 1 and v < 64 and v.bit_count() <= 5
                   and (64*residue+v) % 3 == 0 for v in values)
        low_blocks.append({"core_mod3": residue, "low_parts": values})
    tilt_checks = 0
    for length in range(1, 81):
        for weight in range((3*length)//10+1):
            count = sum(comb(length, j) for j in range(weight+1))
            assert count*3**weight*7**(length-weight) <= 10**length
            tilt_checks += 1
    # Exact certificates for delta < 881/1000 < H_2(3/10).
    lam_upper = Q(33, 8)
    assert lam_upper**3-4*lam_upper**2-lam_upper+2 > 0
    assert 33**1000 < 5**881*8**1000
    assert 10**1000 > 2**881*3**300*7**700
    # p is in this rational interval; the explicit sign fraction exceeds .001.
    pl, pu = Q(3819, 10000), Q(382, 1000)
    assert pl*pl-3*pl+1 > 0 and pu*pu-3*pu+1 < 0
    assert pl**5*(1-2*pu) > Q(1, 1000)
    return {"fibonacci_costs_checked_through": 80,
            "injective_examples": len(images), "low_bit_choices": low_blocks,
            "tilted_binomial_inequalities": tilt_checks,
            "exponent_and_sign_fraction_integer_inequalities": True}


def algebraic_good_indices(max_k):
    """Outward fixed-point intervals for zeta^(2^k)+zeta^(-2^k).

    If L is the large root, A is the sum and C the product of the cubic
    roots, then zeta+zeta^-1 = L*(A-L)^2/C-2. Afterwards use T -> T^2-2.
    Extra precision is doubled if an interval cannot decide a strict test.
    """
    bits = 4*max_k+160
    while True:
        scale = 1 << bits

        def chi_scaled(z):
            return (108*z**3-2359989*z*z*scale
                    +138304*z*scale**2-2048*scale**3)

        left, right = 21851*scale, 21852*scale
        assert chi_scaled(left) < 0 < chi_scaled(right)
        # chi'>0 throughout this root-isolating interval.
        assert 324*21851**2-4719978*21851+138304 > 0
        while right-left > 1:
            mid = (left+right)//2
            if chi_scaled(mid) < 0:
                left = mid
            else:
                right = mid
        A, C = Q(2359989, 108), Q(2048, 108)
        lroot, uroot = Q(left, scale), Q(right, scale)
        assert 0 < A-uroot < A-lroot
        lvalue = lroot*(A-uroot)**2/C-2
        uvalue = uroot*(A-lroot)**2/C-2
        lo = (lvalue*scale).numerator//(lvalue*scale).denominator
        hs = uvalue*scale
        hi = -((-hs.numerator)//hs.denominator)
        good, bad, unresolved = [], [], []
        for k in range(max_k+1):
            sqlo = 0 if lo <= 0 <= hi else min(lo*lo, hi*hi)
            sqhi = max(lo*lo, hi*hi)
            if sqhi < 2*scale*scale:
                good.append(k)
            elif sqlo > 2*scale*scale:
                bad.append(k)
            else:
                unresolved.append(k)
            lo = sqlo//scale-2*scale
            hi = (sqhi+scale-1)//scale-2*scale
        if not unresolved:
            return {"max_k": max_k, "fixed_point_bits": bits,
                    "large_root_lower_scaled": left,
                    "large_root_upper_scaled": right,
                    "good_k": good, "bad_k": bad,
                    "unresolved": [], "all_comparisons_rigorous": True}
        bits *= 2


def family_census(limit):
    limits = []
    power = 1000
    while power <= limit:
        limits.append(power)
        power *= 10
    if not limits or limits[-1] != limit:
        limits.append(limit)
    values = sorted(family_below(limit))
    assert len(values) == len(set(values)) == family_count(limit)
    rows, index, zero = [], 0, 0
    for bound in limits:
        while index < len(values) and values[index] <= bound:
            zero += evaluate(values[index]) == (0, 0)
            index += 1
        assert index == family_count(bound)
        original = sum(min(2**(k-2), ((bound >> k)+1)//2)
                       for k in range(2, bound.bit_length()))
        rows.append({"N": bound, "weight_family": index,
                     "old_interval_family": original,
                     "zero_local_class": zero,
                     "nonzero_local_class": index-zero})
    huge_counts = [{"N": 1 << b, "binary_exponent": b,
                    "weight_family": family_count(1 << b)}
                   for b in (40, 60, 80)]
    return {"census": rows, "large_exact_digit_dp_counts": huge_counts}


def valuation5(q):
    if not q:
        raise ValueError("v5(0) is infinite")
    num, den = abs(q.numerator), q.denominator
    v = 0
    while num % 5 == 0:
        num //= 5
        v += 1
    while den % 5 == 0:
        den //= 5
        v -= 1
    return v


def exact_sign_census(max_n):
    if not max_n:
        return None
    bits = 24*max_n+128
    lo, hi, scale, error = pi_interval(bits)
    a = [Q(0), -Q(11272, 3), -Q(6156093056, 105)]
    b = [Q(1, 4), Q(1196), Q(18662336)]
    rows = []
    for n in range(3, max_n+1):
        coeff = recurrence_coefficients(n-3)
        aa = -sum(coeff[j]*a[j] for j in range(3))/coeff[3]
        bb = -sum(coeff[j]*b[j] for j in range(3))/coeff[3]
        a, b = a[1:]+[aa], b[1:]+[bb]
        data = family_data(n)
        if data is None:
            continue
        k, m, weight = data
        normalizer = power2(2-(5*n)//2)
        qn, cn = normalizer*bb, normalizer*aa
        assert qn.denominator == 1
        assert v2_integer(qn.numerator) == weight <= k
        approximant = -aa/bb
        P, D = approximant.numerator, approximant.denominator
        depth = v2_integer(P)
        lower_depth = 2*n-1-(n.bit_length()-1)-weight
        assert D % 2 == 1 and depth >= lower_depth > 0
        power5 = 1
        while power5*5 <= 4*n:
            power5 *= 5
        direct = (int(qn) % 5, mod5_rational(power5*cn))
        assert direct == evaluate(n)
        if lo*D-P*scale > 0:
            sign = 1
        elif hi*D-P*scale < 0:
            sign = -1
        else:
            raise AssertionError(f"Increase pi interval precision at n={n}")
        rows.append({"n": n, "k": k, "m": m, "binary_weight_3m": weight,
                     "local_pair": list(direct), "v2_reduced_numerator": depth,
                     "proved_lower_bound": lower_depth,
                     "pi_minus_approximant_sign": sign,
                     "v5_q": valuation5(qn), "v5_scaled_c": valuation5(power5*cn)})
    assert len(rows) == family_count(max_n)
    zero = [r for r in rows if r["local_pair"] == [0, 0]]
    signs = Counter(r["pi_minus_approximant_sign"] for r in zero)
    return {"max_n": max_n, "pi_interval_bits": bits,
            "pi_interval_halfwidth_scaled": error, "family_members": len(rows),
            "zero_local_class": len(zero), "zero_class_positive": signs[1],
            "zero_class_negative": signs[-1],
            "all_signs_certified_by_integer_intervals": True,
            "all_local_pairs_and_reduced_numerator_bounds_pass": True,
            "instances": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census-limit", type=int, default=10000000)
    parser.add_argument("--sign-max-n", type=int, default=0,
                        help="0 skips the slower exact rational sign census")
    parser.add_argument("--phase-max-k", type=int, default=80)
    args = parser.parse_args()
    if args.census_limit < 4 or args.phase_max_k < 2:
        parser.error("census limit must be >=4 and phase max k >=2")
    if args.sign_max_n != 0 and args.sign_max_n < 4:
        parser.error("sign max n must be 0 or >=4")
    # Independently compare digit DP with direct membership at modest cutoffs.
    for limit in (4, 7, 31, 100, 999, 4096, 10000):
        assert family_count(limit) == sum(family_data(n) is not None
                                         for n in range(1, limit+1))
    result = {"label": "experiment", "rotation_certificate": rotation_certificate(),
              "combinatorial_certificates": combinatorial_certificates(),
              "algebraic_good_index_certificate": algebraic_good_indices(args.phase_max_k),
              **family_census(args.census_limit),
              "actual_pi_sign_certificate": exact_sign_census(args.sign_max_n)}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
