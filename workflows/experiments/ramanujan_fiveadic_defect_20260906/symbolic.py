#!/usr/bin/env python3
"""Coefficientwise certificate for the normalized fivefold Ramanujan defect.

Standard-library-only. No values of pi, and no loop over integer cutoffs N.

For K=20 this proves, in the Tate algebra Z_5<x>,
    f - L(P_K) in 5**K Z_5<x>,
where f=(H*B-5*(6*x+1))/125, L(P)=((2*x+1)**3/32)*P(x+1)-x**3*P.
Consequently, for EVERY integer N>=1,
    v_5(U_N-P_K(N)) >= K-3*v_5(N)-3*v_5(binomial(2*N,N)).
It does NOT prove that the residual vanishes at infinite precision.

Certified truncations:
 E(t)=prod(5*t+a,a=1..4)/24-1 is in 125*Z_5[t], degree 4.
 Polynomial summation q -> sum_{j=0}^{x-1}q(j), degree d, loses at most
 floor(log_5(d+1)) in coefficient valuation (falling-factorial basis).
 Thus the m-th summand of log G has coefficient valuation at least
 3*m-v_5(m)-floor(log_5(4*m+1)) >= m+1. Terms are retained exactly
 when this lower bound is below the requested precision.
 log(256) terms beyond 2*W have valuation >= W.
 log H belongs to 5*Z_5<x>. Terms exp(log H) of index j>2*K have
 valuation >= j-v_5(j!) >= 3*j/4 > K. Working precision W=2*K+10
 safely accounts for all divisions by j! before reducing to output 5**K.
 In B, the x**j coefficient of (a+5*x)**(-3), a=1,2,3,4,
 is divisible by 5**j; truncation at degree K is therefore valid mod 5**K.
 The raw numerator is computed at K+3 before division by 125.

Ascending coefficient order is used throughout.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path


def v5(n: int) -> int:
    if n == 0:
        raise ValueError("v5(0) is not used by this certificate")
    n = abs(n)
    e = 0
    while n % 5 == 0:
        n //= 5
        e += 1
    return e


def floor_log5(n: int) -> int:
    if n < 1:
        raise ValueError("positive argument required")
    e = 0
    while n >= 5:
        n //= 5
        e += 1
    return e


def trim(a: list) -> list:
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a: list[int], b: list[int], modulus: int) -> list[int]:
    c = [0] * max(len(a), len(b))
    for j, x in enumerate(a):
        c[j] = x
    for j, x in enumerate(b):
        c[j] += x
    return trim([x % modulus for x in c])


def scale(a: list[int], scalar: int, modulus: int) -> list[int]:
    return trim([(x * scalar) % modulus for x in a])


def mul(a: list[int], b: list[int], modulus: int) -> list[int]:
    if not a or not b:
        return []
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    c[i+j] += x*y
    return trim([x % modulus for x in c])


def qmul(a: list[F], b: list[F]) -> list[F]:
    if not a or not b:
        return []
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    c[i+j] += x*y
    return trim(c)


def qmod(q: F, modulus: int) -> int:
    if q.denominator % 5 == 0:
        raise ArithmeticError("nonintegral rational coefficient")
    return q.numerator * pow(q.denominator, -1, modulus) % modulus


def bernoulli_numbers(n: int) -> list[F]:
    # B_1=-1/2, so (B_{j+1}(x)-B_{j+1})/(j+1) sums t**j.
    bs = [F(1)]
    for j in range(1, n+1):
        bs.append(-sum((comb(j+1,k)*bs[k] for k in range(j)), F(0))/(j+1))
    return bs


def log_H(precision: int) -> list[int]:
    """Exact polynomial representative for log(H) modulo 5**precision."""
    W = precision
    modulus = 5**W
    E = [F(0), F(125,12), F(875,24), F(625,12), F(625,24)]
    indices = [m for m in range(1, W)
               if 3*m-v5(m)-floor_log5(4*m+1) < W]
    max_m = max(indices, default=0)
    selected = set(indices)
    power = [F(1)]
    log_R: list[F] = []
    for m in range(1, max_m+1):
        power = qmul(power, E)
        if m in selected:
            if len(log_R) < len(power):
                log_R.extend([F(0)]*(len(power)-len(log_R)))
            factor = F((-1)**(m+1), m)
            for j, value in enumerate(power):
                log_R[j] += factor*value
    degree = max(len(log_R)-1, 0)
    bs = bernoulli_numbers(degree)
    out = [F(0)] * (degree+2)
    # 3*[sum_{t<2x}log R(t) - 2*sum_{t<x}log R(t)]
    for j, c in enumerate(log_R):
        if c:
            for i in range(1,j+2):
                out[i] += (3*c * F(comb(j+1,i),j+1)
                           * bs[j+1-i] * (2**i-2))
    log256 = sum((F((-1)**(j+1)*255**j,j)
                  for j in range(1,2*W+1)), F(0))
    out[1] -= 4*log256
    answer = trim([qmod(c, modulus) for c in out])
    assert all(c % 5 == 0 for c in answer)
    return answer


def H_mod(precision: int) -> list[int]:
    K = precision
    W = 2*K+10
    modulus = 5**K
    work_modulus = 5**W
    ell = log_H(W)
    power = [1]
    answer = [1]
    for j in range(1,2*K+1):
        power = mul(power,ell,work_modulus)
        fac = factorial(j)
        exponent = v5(fac)
        ppart = 5**exponent
        assert W-exponent >= K
        assert all(c % ppart == 0 for c in power)
        inverse_unit = pow(fac//ppart,-1,modulus)
        term = [(c//ppart)*inverse_unit % modulus for c in power]
        answer = add(answer,term,modulus)
    return trim(answer)


def B_mod(precision: int) -> list[int]:
    K = precision
    modulus = 5**K
    answer: list[int] = []
    product = [1]
    inverse32 = pow(32,-1,modulus)
    for a in range(5):
        answer = add(answer,mul([6*a+1,30],product,modulus),modulus)
        if a < 4:
            numerator = [comb(3,j)*(2*a+1)**(3-j)*10**j % modulus
                         for j in range(4)]
            denominator = [(-1)**j*comb(j+2,2)*5**j
                           *pow(a+1,-j-3,modulus) % modulus
                           for j in range(K)]
            product = scale(mul(mul(product,numerator,modulus),
                                denominator,modulus),inverse32,modulus)
    return trim(answer)


def L(poly: list[int], modulus: int) -> list[int]:
    shifted = [0]*len(poly)
    for j,c in enumerate(poly):
        for i in range(j+1):
            shifted[i] += c*comb(j,i)
    shifted = [c % modulus for c in shifted]
    first = scale(mul([1,6,12,8],shifted,modulus),pow(32,-1,modulus),modulus)
    second = [0,0,0]+scale(poly,-1,modulus)
    return add(first,second,modulus)


def reduce_L(poly: list[int], precision: int) -> tuple[list[int],list[int]]:
    modulus = 5**precision
    remainder = trim([c % modulus for c in poly])
    quotient = [0]*max(0,len(remainder)-3)
    inverse_lead = -4*pow(3,-1,modulus) % modulus
    while len(remainder) >= 4:
        j = len(remainder)-4
        c = remainder[-1]*inverse_lead % modulus
        quotient[j] = c
        remainder = add(remainder,scale(L([0]*j+[c],modulus),-1,modulus),modulus)
    return trim(quotient),trim(remainder)


def certificate(precision: int) -> dict:
    if precision < 2:
        raise ValueError("output precision must be at least 2")
    raw_precision = precision+3
    raw_modulus = 5**raw_precision
    H = H_mod(raw_precision)
    B = B_mod(raw_precision)
    raw = add(mul(H,B,raw_modulus),[-5,-30],raw_modulus)
    assert all(c % 125 == 0 for c in raw), "forcing not integral"
    forcing = trim([c//125 for c in raw])
    P,R = reduce_L(forcing,precision)
    modulus = 5**precision
    assert add(L(P,modulus),R,modulus) == forcing
    assert trim([c % 25 for c in P]) == [12]
    # The actual selected initial value, not a freely chosen analytic solution.
    U1 = F(-16008833,16777216)
    f0 = forcing[0] if forcing else 0
    assert f0 == qmod(U1/F(32),modulus)
    return {
        "output_precision_exponent": precision,
        "raw_forcing_precision_exponent": raw_precision,
        "H_coefficients_mod_raw": H,
        "B_coefficients_mod_raw": B,
        "forcing_coefficients_mod_output": forcing,
        "P_coefficients_mod_output": P,
        "quadratic_remainder_coefficients_mod_output": R,
        "forcing_degree": len(forcing)-1,
        "P_degree": len(P)-1,
        "P_mod_25": trim([c % 25 for c in P]),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision",type=int,default=20,
                        help="output exponent K (not guard precision); default 20")
    parser.add_argument("--json",type=Path,help="write the full polynomial certificate")
    args = parser.parse_args()
    result = certificate(args.precision)
    if args.json:
        args.json.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print("Output precision: 5^"+str(args.precision))
    print("Forcing degree:",result["forcing_degree"])
    print("Polynomial degree:",result["P_degree"])
    print("Quadratic remainder:",result["quadratic_remainder_coefficients_mod_output"])
    print("P modulo 25:",result["P_mod_25"])
    print("Actual initial-value check: passed")
    print("P coefficients:",result["P_coefficients_mod_output"])
    if result["quadratic_remainder_coefficients_mod_output"]:
        print("Nonzero obstruction: the proposed Tate-algebra solution is falsified.")
    else:
        print("Coefficientwise identity f=L(P) certified at this output precision.")
        print("This does not prove vanishing of the obstruction at infinite precision.")


if __name__ == "__main__":
    main()
