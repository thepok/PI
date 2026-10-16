#!/usr/bin/env python3
"""Exact finite checks of the Salikhov dyadic intersection.

The all-index result is in the accompanying proof sketch. This program only
verifies finite instances, with rigorous actual-pi signs from integer Machin
intervals. It never uses floating-point pi or an asymptotic sign prediction.

Run from the repository root:
  python workflows/experiments/salikhov_dyadic_intersection_20261016/sign_check.py --max-n 2000

The rational recurrence and local-pair transducer are imported from the
existing September 6 experiment, pinned at repository commit
2ab024737878cd9f1567cc296ef53f051a5ff10b.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "salikhov_mod5_support_20260906"))
from full_pair import evaluate, recurrence_coefficients


def v2_integer(n: int) -> int:
    if not n:
        raise ValueError("v2(0) has no finite integer value")
    n = abs(n)
    return (n & -n).bit_length() - 1


def power2(k: int) -> Q:
    return Q(2**k) if k >= 0 else Q(1, 2**(-k))


def arctan_fixed(q: int, scale: int) -> tuple[int, int]:
    """Return center,error with |scale*atan(1/q)-center| < error.

    Each retained term is rounded toward zero with error below one. The
    alternating-series omitted tail is below the first omitted term, which
    is below one in scaled units. Integer comparisons select the cutoff.
    """
    result = 0
    qpower = q
    j = 0
    while True:
        denominator = (2*j+1)*qpower
        term = scale // denominator
        if not term:
            return result, j+1
        result += term if j % 2 == 0 else -term
        qpower *= q*q
        j += 1


def pi_interval(bits: int) -> tuple[int, int, int, int]:
    scale = 1 << bits
    a, ea = arctan_fixed(5, scale)
    b, eb = arctan_fixed(239, scale)
    center = 16*a-4*b
    error = 16*ea+4*eb
    lo, hi = center-error, center+error
    assert 3*scale < lo < hi < 4*scale
    return lo, hi, scale, error


def family_data(n: int):
    if n < 4:
        return None
    k = v2_integer(n)
    m = n >> k
    return (k, m) if k >= 2 and m < 2**(k-1) else None


def mod5_rational(x: Q) -> int:
    assert x.denominator % 5
    return (x.numerator % 5)*pow(x.denominator % 5, -1, 5) % 5


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=2000)
    args = parser.parse_args()
    if args.max_n < 4:
        parser.error("--max-n must be at least 4")
    bits = 24*args.max_n+128
    lo, hi, scale, interval_error = pi_interval(bits)
    a = [Q(0), -Q(11272, 3), -Q(6156093056, 105)]
    b = [Q(1, 4), Q(1196), Q(18662336)]
    rows = []
    for n in range(3, args.max_n+1):
        coeff = recurrence_coefficients(n-3)
        aa = -sum(coeff[j]*a[j] for j in range(3))/coeff[3]
        bb = -sum(coeff[j]*b[j] for j in range(3))/coeff[3]
        a = a[1:] + [aa]
        b = b[1:] + [bb]
        data = family_data(n)
        if data is None:
            continue
        k, m = data
        normalizer = power2(2-(5*n)//2)
        qn, cn = normalizer*bb, normalizer*aa
        assert qn.denominator == 1
        multiplier_depth = v2_integer(qn.numerator)
        assert multiplier_depth == (3*m).bit_count() <= k
        approximant = -aa/bb
        P, Qden = approximant.numerator, approximant.denominator
        depth = v2_integer(P)
        lower_depth = 2*n-1-2*(n.bit_length()-1)
        assert Qden % 2 == 1 and depth >= lower_depth > 0
        s, power5 = 0, 1
        while power5*5 <= 4*n:
            power5 *= 5
            s += 1
        direct_pair = (int(qn) % 5, mod5_rational(power5*cn))
        pair = evaluate(n)
        assert direct_pair == pair
        lower_sign = lo*Qden-P*scale
        upper_sign = hi*Qden-P*scale
        if lower_sign > 0:
            sign = 1
        elif upper_sign < 0:
            sign = -1
        else:
            raise AssertionError(f"pi interval does not resolve n={n}; increase precision")
        rows.append({"n": n, "k": k, "m": m, "local_pair": list(pair),
                     "v2_q": multiplier_depth, "v2_reduced_numerator": depth,
                     "proved_lower_bound": lower_depth, "pi_minus_approximant_sign": sign})
    expected = sum(family_data(n) is not None for n in range(1, args.max_n+1))
    assert len(rows) == expected
    block_rows = []
    for k in sorted({r["k"] for r in rows}):
        block = [r for r in rows if r["k"] == k]
        zero = [r for r in block if r["local_pair"] == [0, 0]]
        counts = Counter(r["pi_minus_approximant_sign"] for r in zero)
        block_rows.append({"k": k, "population": len(block),
                           "complete_block": len(block) == 2**(k-2),
                           "zero_class": len(zero), "zero_class_positive": counts[1],
                           "zero_class_negative": counts[-1]})
    zero = [r for r in rows if r["local_pair"] == [0, 0]]
    counts = Counter(r["pi_minus_approximant_sign"] for r in zero)
    result = {"label": "experiment", "max_n": args.max_n,
              "pi_interval_bits": bits, "pi_interval_halfwidth_scaled": interval_error,
              "family_members": len(rows), "zero_class_members": len(zero),
              "zero_class_positive": counts[1], "zero_class_negative": counts[-1],
              "all_signs_certified_by_integer_intervals": True,
              "all_local_pairs_match_exact_rational_recurrence": True,
              "all_reduced_numerator_bounds_pass": True,
              "blocks": block_rows, "instances": rows}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
