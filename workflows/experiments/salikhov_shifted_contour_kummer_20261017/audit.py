#!/usr/bin/env python3
"""Exact audit of the shifted-contour coefficient and carry budget.

The proof is in the accompanying note. Finite tests here independently
crosscheck the coefficient recurrence with its defining expansion, then
test the deep-denominator valuation equality and all polynomial term bounds.
"""
import argparse
from collections import Counter
from fractions import Fraction
import importlib.util
from math import comb
from pathlib import Path
import json


def vp(value, prime=5):
    if not value:
        return None
    value = abs(value)
    result = 0
    while value % prime == 0:
        result += 1
        value //= prime
    return result


def floorlog5(value):
    result = 0
    while value >= 5:
        value //= 5
        result += 1
    return result


def coefficients(n):
    """Exact differential-equation recurrence for the generating function."""
    values = [1]
    for k in range(2*n-1):
        numerator = (87*n+25+19*k)*values[k]
        if k >= 1:
            numerator += (250*n+25+125*k)*values[k-1]
        if k >= 2:
            numerator += 625*(k-n-1)*values[k-2]
        quotient, remainder = divmod(numerator, k+1)
        assert remainder == 0
        values.append(quotient)
    return values


def coefficient_by_expansion(n, k):
    return sum(
        25**(u+v)*comb(2*n,u)*comb(2*n-u,k-2*u-v)
        *6**(k-2*u-v)*comb(3*n+v,v)
        for u in range(k//2+1)
        for v in range(k-2*u+1)
    )


def carries(n, length):
    count, power = 0, 1
    for _ in range(length):
        power *= 5
        count += (2*n % power) < (power+1)//2
    return count


def load_source(repo_root):
    relative = Path("workflows/experiments/salikhov_mod5_support_20260906/full_pair.py")
    roots = [repo_root] if repo_root else [Path.cwd(), *Path(__file__).resolve().parents]
    for root in roots:
        path = root / relative
        if path.is_file():
            spec = importlib.util.spec_from_file_location("shifted_contour_source",path)
            source = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(source)
            return source
    raise FileNotFoundError("Supply --repo-root for the PI checkout containing "+str(relative))


def polynomial_multiply(a,b,limit,modulus):
    result=[0]*min(len(a)+len(b)-1,limit+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j <= limit:
                result[i+j]=(result[i+j]+x*y)%modulus
    return result


def polynomial_power(a,exponent,limit,modulus):
    result=[1]
    while exponent:
        if exponent%2:
            result=polynomial_multiply(result,a,limit,modulus)
        exponent//=2
        if exponent:
            a=polynomial_multiply(a,a,limit,modulus)
    return result


def direct_endpoint(n,unit,modulus):
    """Compute 5^L Dtilde directly from the partial-fraction and polynomial formula."""
    length=floorlog5(4*n)
    limit=3*n
    quadratic=[1,-2,1]
    quartic=[32,-112,156,-100,25]
    base=polynomial_multiply(quadratic,
             polynomial_multiply(quartic,quartic,limit,modulus),limit,modulus)
    numerator=polynomial_power(base,n,limit,modulus)
    inverse=[comb(3*n+k,k)*pow(2,-(3*n+1+k),modulus)%modulus
             for k in range(limit+1)]
    pole=polynomial_multiply(numerator,inverse,limit,modulus)
    left=(3+unit)*pow(4,-1,modulus)%modulus
    right=(2-unit)*pow(2,-1,modulus)%modulus
    beta=(-1+2*unit)%modulus

    def scaled_inverse(j):
        order=vp(j)
        assert order <= length
        return 5**(length-order)*pow(j//5**order,-1,modulus)%modulus

    answer=0
    for j in range(1,3*n+1):
        answer+=(2*(-1)**n*pole[3*n-j]*scaled_inverse(j)
                 *(pow(left,j,modulus)-pow(right,j,modulus)))
    for k,value in enumerate(coefficients(n)):
        j=4*n-1-2*k
        answer-=10*value*scaled_inverse(j)*pow(beta,j,modulus)
    return answer%modulus


def actual_contour_check(source,limit):
    """Independent exact recurrence/Hensel verification, adapted from peer review."""
    a,_=source.recurrence_sequences(limit)
    d=[Fraction(0),Fraction(1658),Fraction(2716506572,105)]
    for n in range(limit-2):
        p=source.recurrence_coefficients(n)
        d.append(-sum(p[k]*d[n+k] for k in range(3))/p[3])
    modulus,unit=5,2
    for _ in range(49):
        new_modulus=5*modulus
        unit=(unit-(unit*unit+1)*pow(2*unit,-1,new_modulus))%new_modulus
        modulus=new_modulus
    assert (unit*unit+1)%modulus == 0 and unit%5 == 2
    margins,examples=Counter(),[]
    direct_checks=0
    for n in range(1,limit+1):
        length=floorlog5(4*n)
        cutoff=floorlog5(2*length+1)
        carry=carries(n,length)

        def residue(value):
            scaled=value*5**length
            assert scaled.denominator%5
            return scaled.numerator*pow(scaled.denominator,-1,modulus)%modulus

        shifted=(residue(d[n])+unit*residue(a[n]))%modulus
        assert shifted, (n,"Increase precision to resolve the valuation")
        observed=vp(shifted)-length
        bound=1-max(cutoff,length-carry)
        assert observed >= bound
        margins[observed-bound]+=1
        if n <= 12:
            assert direct_endpoint(n,unit,modulus) == shifted
            direct_checks+=1
        if n <= 15 or n in (32,36,37,38,125,250,500,1000):
            examples.append({"n":n,"L":length,"H":cutoff,"K":carry,
                             "actual_shifted_valuation":observed,"proved_bound":bound})
    return {"limit":limit,"exact_recurrence_checks":limit,
            "precision_base_five_digits":50,"resolved_valuations":limit,
            "direct_endpoint_identity_checks":direct_checks,
            "equalities":margins[0],"margin_histogram":dict(sorted(margins.items())),
            "representative_values":examples}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root",type=Path)
    parser.add_argument("--limit",type=int,default=1000)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    if args.limit < 12:
        parser.error("--limit must be at least12 to include the endpoint comparisons")
    expansion_checks = 0
    for n in range(1, 11):
        values = coefficients(n)
        for k, value in enumerate(values):
            assert value == coefficient_by_expansion(n,k)
            expansion_checks += 1

    deep_checks, all_term_checks, exact_carry_checks = 0, 0, 0
    sharp_examples, strata = [], []
    for n in [*range(1, 257), 312, 625, 1000, 1563]:
        length = floorlog5(4*n)
        cutoff = floorlog5(2*length+1)
        carry = carries(n,length)
        bound = 1-max(cutoff,length-carry)
        minimum, local_deep = None, 0
        for k, value in enumerate(coefficients(n)):
            j = 4*n-1-2*k
            order = vp(j)
            coefficient_order = vp(value)
            term_order = 1+coefficient_order-order
            assert term_order >= bound
            minimum = term_order if minimum is None else min(minimum,term_order)
            all_term_checks += 1
            if 5**order > 2*length+1:
                leader_order = vp(comb(2*n,k))
                assert coefficient_order == leader_order
                assert leader_order >= carries(n,order)
                deep_checks += 1
                local_deep += 1
            if n <= 32:
                direct = sum(
                    (2*n//5**i)-(k//5**i)-((2*n-k)//5**i)
                    for i in range(1, floorlog5(2*n)+1)
                )
                assert direct == vp(comb(2*n,k))
                exact_carry_checks += 1
        if minimum == bound and len(sharp_examples) < 12:
            sharp_examples.append({"n":n,"L":length,"H":cutoff,
                                   "K":carry,"polynomial_minimum":minimum})
        if n in (7,32,36,125,250,256,312,625,1000,1563):
            strata.append({"n":n,"L":length,"H":cutoff,"K":carry,
                           "proved_bound":bound,"minimum_polynomial_term":minimum,
                           "deep_coefficient_checks":local_deep})

    endpoints = [Fraction(0),Fraction(1,4),Fraction(1,3),Fraction(1,2),
                 Fraction(2,3),Fraction(3,4),Fraction(1)]
    score, carry_vector, cost = [], [], []
    transitions = []
    for state in range(6):
        lo,hi = endpoints[state:state+2]
        x=(lo+hi)/2
        fl=lambda z:z.numerator//z.denominator
        c=-4*fl(2*x)+fl(4*x)+fl(3*x)
        kappa=int(x<Fraction(1,4) or Fraction(1,2)<x<Fraction(3,4))
        cost.append(c)
        carry_vector.append(kappa)
        score.append(c+kappa-1)
        row=[]
        for digit in range(5):
            y=(x+digit)/5
            destination=next(i for i in range(6) if endpoints[i]<y<endpoints[i+1])
            assert endpoints[destination] <= (lo+digit)/5
            assert (hi+digit)/5 <= endpoints[destination+1]
            row.append(destination)
        transitions.append(row)
    assert score == [0,0,1,-1,0,0]
    assert carry_vector == [1,0,0,1,1,0]
    for state in range(6):
        for digit in range(5):
            assert transitions[5-state][4-digit] == 5-transitions[state][digit]
        assert score[5-state] == -score[state]

    triple_checks=0
    for length in range(3,9):
        modulus=5**length
        for n in range(36,modulus,125):
            higher=carries(n,length)-1
            assert [carries(n+r,length) for r in range(3)] == [higher+1,higher,higher+2]
            triple_checks += 1

    contour=actual_contour_check(load_source(args.repo_root),args.limit)
    certificate={
        "status":"passed",
        "finite_evidence_only":True,
        "defining_expansion_crosschecks":expansion_checks,
        "deep_leading_coefficient_equalities":deep_checks,
        "all_polynomial_term_bound_checks":all_term_checks,
        "legendre_binomial_crosschecks":exact_carry_checks,
        "triple_carry_shift_checks":triple_checks,
        "cost_vector":cost,"carry_vector":carry_vector,"net_score":score,
        "digit_transitions":transitions,
        "sharp_polynomial_examples":sharp_examples,
        "representative_strata":strata,
        "independent_actual_contour_crosscheck":contour,
        "scope":"This independently checks finite coefficient and carry arithmetic. The proof supplies the universal claim; the predecessor supplies the actual contour and Casoratian.",
    }
    path=args.json or Path(__file__).with_name("certificate.json")
    path.write_text(json.dumps(certificate,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"passed","deep_equalities":deep_checks,
                      "term_bounds":all_term_checks,"triple_checks":triple_checks,
                      "actual_contour_checks":contour["exact_recurrence_checks"],
                      "actual_contour_equalities":contour["equalities"],
                      "certificate":str(path)},sort_keys=True))


if __name__ == "__main__":
    main()
