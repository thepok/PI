#!/usr/bin/env python3
"""Exact finite checks for the forced Salikhov divisor and its sharp branch.

This is an experiment. The all-index multiplier and companion proofs are in
the linked mathematical notes. No pi digits, floating
point arithmetic, external packages, or network access are used.

The recurrence is the published oSALIKHOVpi3 recurrence, normalized from
E_n=-I_n/5 to I_n=a_n+b_n*pi. See the note for the primary source.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import gcd
from pathlib import Path


def recurrence_coefficients(n: int) -> tuple[int, int, int, int]:
    return (
        -1024 * (2*n+5) * (2*n+3) * (2*n+1) * (n+2) * (n+1)
        * (559455*n**4+5637736*n**3+21207869*n**2+35294652*n+21926016),
        64 * (2*n+5) * (2*n+3) * (n+2)
        * (1208982255*n**6+14601112006*n**5+71554462078*n**4
           +181444545414*n**3+250049018747*n**2+176898555884*n+50159702880),
        -6 * (2*n+5)
        * (440102548665*n**8+7075613606958*n**7+49182254436312*n**6
           +192978557313766*n**5+467319046780891*n**4+714892923466956*n**3
           +674376299494052*n**2+358497976451216*n+82191375084672),
        3 * (4*n+11) * (3*n+8) * (3*n+7) * (4*n+9) * (n+3)
        * (559455*n**4+3399916*n**3+7651391*n**2+7554302*n+2760952),
    )


def recurrence_pairs(bound: int):
    """Yield all pairs through bound, retaining only three large rational pairs."""
    a = [Q(0), -Q(11272, 3), -Q(6156093056, 105)]
    b = [Q(1, 4), Q(1196), Q(18662336)]
    for n in range(min(3, bound + 1)):
        yield n, a[n], b[n]
    for n in range(max(0, bound - 2)):
        p = recurrence_coefficients(n)
        next_a = -sum(p[j]*a[j] for j in range(3)) / p[3]
        next_b = -sum(p[j]*b[j] for j in range(3)) / p[3]
        a = a[1:] + [next_a]
        b = b[1:] + [next_b]
        yield n + 3, next_a, next_b


def integer_valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("The finite valuation helper is undefined at zero")
    value = abs(value)
    count = 0
    while value % prime == 0:
        value //= prime
        count += 1
    return count


def valuation(value: Q | int, prime: int = 5) -> int:
    value = Q(value)
    return (integer_valuation(value.numerator, prime)
            - integer_valuation(value.denominator, prime))


def unit_residue(value: Q | int, modulus: int = 5) -> int:
    """Remove all factors of five, then reduce the rational unit modulo 5^r."""
    value = Q(value)
    numerator, denominator = value.numerator, value.denominator
    if numerator == 0:
        raise ValueError("Zero has no unit part")
    while numerator % 5 == 0:
        numerator //= 5
    while denominator % 5 == 0:
        denominator //= 5
    return numerator * pow(denominator, -1, modulus) % modulus


def multiply(a: list[Q], b: list[Q], limit: int) -> list[Q]:
    result = [Q(0)] * min(len(a) + len(b) - 1, limit + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:max(0, limit + 1 - i)]):
            result[i+j] += x*y
    return result


def power(a: list[Q], exponent: int, limit: int) -> list[Q]:
    result = [Q(1)]
    while exponent:
        if exponent % 2:
            result = multiply(result, a, limit)
        exponent //= 2
        if exponent:
            a = multiply(a, a, limit)
    return result


def binomial_series(exponent: Q, degree: int) -> list[Q]:
    result = [Q(1)]
    for j in range(degree):
        result.append(result[-1] * (exponent-j) / (j+1))
    return result


def residue_formula(n: int) -> Q:
    degree = 3*n
    kernel = power([Q(32), Q(56), Q(25)], 2*n, degree)
    series = binomial_series(Q(2*n-1, 2), degree)
    return multiply(kernel, series, degree)[degree] / 4


def structural_checks() -> dict:
    # x^4+6x^2+25 = 25 K(t) after x^2=25(1+t).
    assert [25+6+1, 50+6, 25] == [32, 56, 25]
    ell = [((-1)**j * (1+pow(2, -j, 5))) % 5 for j in range(12)]
    assert ell == [2, 1, 0, 2] * 3
    f = multiply(binomial_series(Q(1, 2), 1), [Q(2), Q(1)], 1)
    assert f == [2, 2]
    for k in range(1, 5):
        m = (3*5**k+3)//2
        divided_B = (ell[(m-1) % 4] + 4*ell[(m-3) % 4]) % 5
        assert divided_B == (2 if k % 2 else 3)
        assert divided_B * pow(8, -1, 5) % 5 == (-1)**k % 5
        n = (5**k+1)//2
        assert (2-(5*n)//2+k) % 4 == 0
    return {"ell_period": ell[:4], "F_initial_coefficients": [2, 2]}


def avoider_instance(k: int, h: int, sign: int) -> None:
    assert k >= 1 and h >= 3 and sign in (-1, 1)
    modulus = 5**(k+1)
    factor = 9*2**(h-2)
    u = ((5**k-sign)*pow(factor, -1, modulus)) % modulus
    if u % 2 == 0:
        u += modulus
    numerator, denominator = 2**h*u, factor*u+sign
    assert u > 0 and u % 2 == 1 and denominator > 0
    assert gcd(numerator, denominator) == 1
    assert valuation(numerator, 2) == h
    assert valuation(denominator, 5) == k
    assert Q(4, 9)-Q(numerator, denominator) == Q(4*sign, 9*denominator)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terms", type=int, default=2000)
    parser.add_argument("--direct", type=int, default=12)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    if args.terms < 3 or args.direct < 0:
        parser.error("Require --terms >= 3 and --direct >= 0")

    structural = structural_checks()
    direct = {n: residue_formula(n) for n in range(args.direct+1)}
    branch_indices = {}
    k = 1
    while (5**k+1)//2 <= args.terms:
        branch_indices[(5**k+1)//2] = k
        k += 1
    sharp_branch, failures, depths = [], [], {}
    for n, a, b in recurrence_pairs(max(args.terms, args.direct)):
        if n <= args.direct:
            assert b == direct[n], ("residue formula", n)
        if not 1 <= n <= args.terms:
            continue
        bv, av = valuation(b), valuation(a)
        assert bv >= valuation(2*n-1), ("forced divisor", n)
        if n in (14, 70):
            depths[n] = max(0, bv-av)
        if n not in branch_indices:
            continue
        k = branch_indices[n]
        bu = unit_residue(b)
        qu = bu * pow(2, (2-(5*n)//2) % 4, 5) % 5
        assert bv == k and bu == (-1)**k % 5, ("sharp b branch", k, n)
        assert qu == pow(2, k, 5), ("sharp q branch", k, n)
        au = unit_residue(a)
        if av != 0 or au != (1+2*(-1)**k) % 5:
            failures.append({"k": k, "n": n, "a_valuation": av, "a_unit_mod5": au})
        sharp_branch.append({
            "k": k, "n": n, "b_valuation": bv, "b_unit_mod5": bu,
            "q_unit_mod5": qu, "a_valuation": av, "a_unit_mod5": au,
            "a_unit_mod625": unit_residue(a, 625),
            "reduced_denominator_valuation": max(0, bv-av),
        })
    if args.terms >= 70:
        assert [depths[14], depths[70]] == [1, 1]
    instances = 0
    for k in range(1, 9):
        for h in (3, 4, 17, 40):
            for sign in (-1, 1):
                avoider_instance(k, h, sign)
                instances += 1
    report = {
        "status": "experiment; all-index statements use the accompanying algebraic proofs",
        "structural_checks": structural,
        "residue_formula_indices": [0, args.direct],
        "divisor_indices": [1, args.terms],
        "sharp_branch": sharp_branch,
        "companion_congruence_failures": failures,
        "naive_scaling_counterexample": (
            {"n": 14, "five_n": 70, "depths": [depths[14], depths[70]]}
            if args.terms >= 70 else None
        ),
        "avoider_instances": instances,
    }
    output = json.dumps(report, indent=2) + "\n"
    if args.json:
        args.json.write_text(output, encoding="utf-8")
    print(output, end="")
    if failures:
        raise SystemExit("Companion congruence falsified in the requested finite range")


if __name__ == "__main__":
    main()
