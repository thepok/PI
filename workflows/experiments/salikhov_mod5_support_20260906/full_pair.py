#!/usr/bin/env python3
"""Exact certificate for the modified-Salikhov full local pair modulo five.

Standard library only; no pi evaluation, digit expansion, or network access.

Sources of the integral and recurrence (the recurrence uses E_n=-I_n/5):
  https://arxiv.org/html/1912.06345v2
  https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt

Proves finite identities by exhausting all reachable Cartier/transducer states.
The accompanying analytic argument, not finite sampling, proves the sign law.

Run: python salikhov_full_pair_certificate.py
Optional: --direct 20 --recurrence 300 --counts 10
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from fractions import Fraction as Q
from math import comb, gcd
from typing import Sequence


def mul(a: Sequence, b: Sequence, limit: int | None = None) -> list:
    size = len(a) + len(b) - 1
    if limit is not None:
        size = min(size, limit + 1)
    c = [0] * size
    for i, x in enumerate(a):
        for j, y in enumerate(b[:max(0, size-i)]):
            c[i+j] += x*y
    return c


def power(a: Sequence, n: int, limit: int | None = None) -> list:
    r = [1]
    while n:
        if n & 1:
            r = mul(r, a, limit)
        n //= 2
        if n:
            a = mul(a, a, limit)
    return r


def gm(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def gp(a: tuple[Q, Q], n: int) -> tuple[Q, Q]:
    r = (Q(1), Q(0))
    while n:
        if n & 1:
            r = gm(r, a)
        n //= 2
        if n:
            a = gm(a, a)
    return r


def p2(k: int) -> Q:
    return Q(2**k) if k >= 0 else Q(1, 2**(-k))


def exact_companion(n: int) -> tuple[Q, Q]:
    """Return (a_n,b_n) by exact coefficient extraction and endpoint integration."""
    H = [32, -112, 156, -100, 25]
    F = mul([1, -2, 1], mul(H, H))
    num = power(F, n, 3*n)
    inv = [Q(comb(3*n+k, k), 2**(3*n+1+k)) for k in range(3*n+1)]
    A = mul(num, inv, 3*n)  # A[m]=C_{n,3n-m}=A_{n,3n-m}/5^(3n-m)
    b = Q((-1)**n, 2)*A[3*n]
    a = Q(0)
    # i E_j = -2 Im(((2+i)/2)^j + ((3+i)/4)^j).
    for j in range(1, 3*n+1):
        Ej = -2*(gp((Q(1), Q(1, 2)), j)[1]
                 + gp((Q(3, 4), Q(1, 4)), j)[1])
        a += (-1)**(n+1)*A[3*n-j]*Ej/j
    if n:
        nump = power([1, 6, 25], 2*n, 2*n-1)
        invp = [comb(3*n+k, k)*25**k for k in range(2*n)]
        coeff = mul(nump, invp, 2*n-1)
        for k in range(2*n):
            j = 4*n-1-2*k
            Zj = -2*gp((Q(-1), Q(2)), j)[1]
            a += 5*coeff[k]*Zj/j
    return a, b


def recurrence_coefficients(n):
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
        *(559455*n**4+3399916*n**3+7651391*n**2+7554302*n+2760952)
    )


def recurrence_sequences(N: int) -> tuple[list[Q], list[Q]]:
    a = [Q(0), -Q(11272, 3), -Q(6156093056, 105)]
    b = [Q(1, 4), Q(1196), Q(18662336)]
    for n in range(max(0, N-2)):
        p = recurrence_coefficients(n)
        for seq in (a, b):
            seq.append(-sum(p[j]*seq[n+j] for j in range(3))/p[3])
    return a[:N+1], b[:N+1]


def coefficients_from_values(values: list[int]) -> list[Q]:
    """Newton interpolation, for the explicitly degree <=9 recurrence polynomials."""
    differences = list(map(Q, values))
    result = [Q(0)]*len(values)
    basis = [Q(1)]
    for k in range(len(values)):
        for j, v in enumerate(basis):
            result[j] += differences[0]*v
        differences = [b-a for a, b in zip(differences, differences[1:])]
        basis = [v/Q(k+1) for v in mul(basis, [-k, 1])]
    return result


def recurrence_certificates() -> None:
    P = [coefficients_from_values([recurrence_coefficients(n)[j] for n in range(10)])
         for j in range(4)]
    chi = [-2048, 138304, -2359989, 108]
    C = [p[9] for p in P]
    D = [p[8] for p in P]
    assert C == [2237820*v for v in chi]
    assert [D[j]-Q(j, 2)*C[j] for j in range(4)] == [39334594*v for v in chi]
    assert Q(39334594, 2237820) == Q(10019, 570)
    # This monomial-coefficient positivity proves b_(n+3)>10000*b_(n+2)
    # inductively, starting from b_2>10000*b_1, b_0,b_1>0.
    dominant = [-10000*P[2][k]-P[1][k]-100000000*P[3][k] for k in range(10)]
    assert all(v > 0 for v in dominant)
    a, b, c, d = 108, -2359989, 138304, -2048
    disc = b*b*c*c-4*a*c**3-4*b**3*d-27*a*a*d*d+18*a*b*c*d
    assert disc == -57*4475640000**2
    assert all(sum(chi[j]*x**j for j in range(4)) % 11 for x in range(11))
    # The nonreal pair is not purely imaginary: its real partner is not b/a.
    x = Q(2359989, 108)
    assert sum(chi[j]*x**j for j in range(4)) != 0
    print('Recurrence: exponent -1/2; positive dominant coefficient; S3 discriminant certified.')


def trim(a: Sequence[int]) -> tuple[int, ...]:
    a = [v % 5 for v in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a or [0])


def fm(a, b):
    return trim(mul(a, b))


def fp(a, n):
    r = (1,)
    for _ in range(n):
        r = fm(r, a)
    return r


def series_div(num, den, degree):
    r = []
    for k in range(degree+1):
        v = (num[k] if k < len(num) else 0)
        v -= sum(den[j]*r[k-j] for j in range(1, min(k, len(den)-1)+1))
        r.append(v*pow(den[0], -1, 5) % 5)
    return r


# Compact full-pair scheme. State 3 is the single absorbing zero state.
DELTA = [
    [0,1,2,3,4], [1,1,2,3,4], [5,3,6,4,4], [3,3,3,3,3],
    [5,7,3,4,4], [5,1,2,3,4], [0,6,2,3,4], [1,6,8,4,4],
    [9,6,7,4,4], [9,1,2,3,4],
]
MULT = [
    [1,1,4,0,2], [1,1,4,0,2], [1,0,4,3,3], [0,0,0,0,0],
    [1,3,0,2,1], [1,1,4,0,2], [1,1,4,0,2], [1,2,4,2,1],
    [1,4,4,1,4], [1,1,4,0,2],
]
RATIO = [0,1,4,None,4,4,0,1,3,3]
COMPACT_START = (0,1,0,0)  # shape, q, parity(n), parity(number of digits read)
SINK = None


def compact_step(st, digit):
    if st is SINK:
        return SINK
    sigma, q, e, p = st
    if MULT[sigma][digit] == 0:
        return SINK
    # Parentheses are essential: -(digit//2), not (-digit)//2.
    factor = (-1)**(p*digit)*pow(2, (-(digit//2)-e*(digit % 2)) % 4, 5)
    return (DELTA[sigma][digit], q*MULT[sigma][digit]*factor % 5,
            (e+digit) % 2, 1-p)


def compact_output(st):
    if st is SINK:
        return (0,0)
    sigma, q, _, _ = st
    return q, RATIO[sigma]*q % 5


def evaluate(n: int):
    st = COMPACT_START
    while n:
        st = compact_step(st, n % 5)
        n //= 5
    return compact_output(st)


def build_and_certify_pair():
    F = fm(fp((4,1), 2), fp((2,3,1), 2))
    D = fp((2,4), 3)
    S0 = fp((2,4), 2)
    factors = [fm(fp(F,a), fp(D,4-a)) for a in range(5)]

    def section(S,a,b):
        return trim(fm(S, factors[a])[b::5])

    base = [(S0,0)]
    base_index = {base[0]:0}
    BE = []
    for S, carry in base:
        row = []
        for digit in range(5):
            residue, newcarry = (3*digit+carry) % 5, (3*digit+carry)//5
            new = (section(S,digit,residue), newcarry)
            if new not in base_index:
                base_index[new] = len(base)
                base.append(new)
            row.append(base_index[new])
        BE.append(row)
    assert len(base) == 27

    def base_output(i):
        S, carry = base[i]
        while carry:
            S = section(S,0,carry % 5)
            carry //= 5
        return 2*S[0] % 5

    high, low = [], []
    for S, carry in base:
        f = series_div(S,D,2)
        high.append(sum(w*f[carry-u] for u,w in ((1,1),(2,3),(3,1))
                        if 0 <= carry-u <= 2) % 5)
        g = series_div(fm(S,F),fm(D,D),2)
        low.append((g[2]+3*g[1]+g[0]) % 5)
    phi = [(-1)**n*pow(2, (1-(5*n//2)) % 4, 5) % 5 for n in range(8)]

    def raw_output(st):
        i, cmp, R, res, par = st
        return phi[res]*base_output(i) % 5, -2*phi[res]*R % 5

    def raw_step(st,digit):
        i, cmp, R, res, par = st
        ii = BE[i][digit]
        cc = cmp if digit == 1 else (1 if digit > 1 else -1)
        RR = R
        if digit:
            if cc > 0:
                RR = high[ii]
            else:
                assert digit == 1 and base[i][1] == 0
                RR = low[i]
        return ii, cc, RR, (res+digit*(1 if par == 0 else 5)) % 8, 1-par

    # Exhaustive finite bisimulation with the analytic Cartier construction.
    raw_start = (0,0,0,0,0)
    associated = {raw_start:COMPACT_START}
    queue = deque([raw_start])
    while queue:
        raw = queue.popleft()
        st = associated[raw]
        assert raw_output(raw) == compact_output(st)
        for digit in range(5):
            rr, ss = raw_step(raw,digit), compact_step(st,digit)
            if rr in associated:
                assert associated[rr] == ss
            else:
                associated[rr] = ss
                queue.append(rr)
    assert len(associated) == 713
    assert len(set(associated.values())) == 145
    assert set(associated.values()) == {SINK} | {
        (sigma,q,e,p) for sigma in range(10) if sigma != 3
        for q in range(1,5) for e in range(2) for p in range(2)}

    states = [COMPACT_START]
    index = {COMPACT_START:0}
    E = []
    for st in states:
        row = []
        for digit in range(5):
            new = compact_step(st,digit)
            if new not in index:
                index[new] = len(states)
                states.append(new)
            row.append(index[new])
        E.append(row)
    O = [compact_output(st) for st in states]
    assert all(O[row[0]] == O[i] for i,row in enumerate(E))
    assert len(set(O)) == 17
    assert set(O) == {(0,0)} | {(q,v) for q in range(1,5)
                               for v in range(5) if v != 2*q % 5}

    # Minimality: partition refinement from the exact pair outputs.
    labels = {z:j for j,z in enumerate(sorted(set(O)))}
    part = [labels[z] for z in O]
    while True:
        lab, new = {}, []
        for i,row in enumerate(E):
            sig = (O[i], *(part[j] for j in row))
            if sig not in lab:
                lab[sig] = len(lab)
            new.append(lab[sig])
        if new == part:
            break
        part = new
    assert len(set(part)) == 145
    print('Cartier states 27; reachable raw pair states 713; minimal full-pair states 145.')
    return states,E,O,index[SINK]


def graph_certificates(states,E,O,sink):
    S = set(range(len(E))) - {sink}
    assert E[sink] == [sink]*5
    diameter, rootdist = 0, None
    for initial in sorted(S):
        dist = {initial:0}
        queue = deque([initial])
        while queue:
            i = queue.popleft()
            for j in E[i]:
                if j in S and j not in dist:
                    dist[j] = dist[i]+1
                    queue.append(j)
        assert set(dist) == S
        diameter = max(diameter,max(dist.values()))
        if initial == 0:
            rootdist = dist
    assert diameter == 8
    period = 0
    for i in S:
        for j in E[i]:
            if j in S:
                period = gcd(period, rootdist[i]+1-rootdist[j])
    assert period == 2
    assert Counter(rootdist[i] % 2 for i in S) == {0:72,1:72}
    for parity in (0,1):
        assert {O[i] for i in S if rootdist[i] % 2 == parity} == set(O)-{(0,0)}

    # Every row has two length-two paths, remaining in S, with a common
    # endpoint and numerical value difference 2 or 8. These are the precise
    # witnesses used in the Perron-normalized contraction proof.
    histogram = Counter()
    for i in S:
        paths = {}
        for d,j in enumerate(E[i]):
            if j not in S:
                continue
            for e,k in enumerate(E[j]):
                if k in S:
                    paths.setdefault(k,[]).append(d+5*e)
        diffs = [b-a for vals in paths.values() for a in vals for b in vals
                 if b-a in (2,8)]
        assert diffs
        histogram[min(diffs)] += 1
    assert histogram == {2:128,8:16}

    # The established support recurrence is certified componentwise here too.
    def action(v):
        return [sum(v[j] for j in row) for row in E]
    V = [[int(z != (0,0)) for z in O]]
    for _ in range(4):
        V.append(action(V[-1]))
    assert all(V[4][i]-5*V[3][i]+3*V[2][i]+3*V[1][i]-2*V[0][i] == 0
               for i in range(len(E)))
    assert [v[0] for v in V] == [1,4,16,65,267]
    print('Recurrent components: 144-state period-two component + absorbing zero state.')
    print('Nonzero component: diameter 8; cyclic classes 72+72; all 16 outputs in each.')
    print('Two-step collision differences:', dict(sorted(histogram.items())))
    print('Valid uniform contraction constant: kappa = 1/(16*5^10).')
    print('Support generating function: (1-z-z^2)/(1-5z+3z^2+3z^3-2z^4).')


def f5(x: Q) -> int:
    assert x.denominator % 5
    return x.numerator*pow(x.denominator,-1,5) % 5


def arithmetic_checks(directN,recurrenceN):
    aa,bb = recurrence_sequences(max(directN,recurrenceN,3))
    for n in range(directN+1):
        assert exact_companion(n) == (aa[n],bb[n]), n
    for n in range(recurrenceN+1):
        t = 5*n//2
        q = p2(2-t)*bb[n]
        assert q.denominator == 1
        if n:
            power5 = 1
            while power5*5 <= 4*n:
                power5 *= 5
            v = power5*p2(2-t)*aa[n]
            pair = (f5(q),f5(v))
        else:
            pair = (1,0)  # v_0 is an auxiliary convention only.
        assert evaluate(n) == pair, (n,evaluate(n),pair)
        assert bb[n] > 0
    print(f'Exact companion formula agrees with published recurrence for n=0..{directN}.')
    print(f'Full-pair scheme agrees with exact recurrence for n=0..{recurrenceN}.')
    print('Initial (a_n,b_n):')
    for n in range(4):
        print(n, str(aa[n]), str(bb[n]))


def counts(E,O,Lmax):
    v = [0]*len(E)
    v[0] = 1
    for L in range(Lmax+1):
        c = Counter()
        for i,x in enumerate(v):
            c[O[i]] += x
        c[(1,0)] -= 1  # omit n=0, including at L=0
        if L:
            print('L=',L, 'counts=',dict(sorted((z,x) for z,x in c.items() if x)))
        w = [0]*len(E)
        for i,row in enumerate(E):
            for j in row:
                w[j] += v[i]
        v = w


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct',type=int,default=12)
    parser.add_argument('--recurrence',type=int,default=200)
    parser.add_argument('--counts',type=int,default=6)
    args = parser.parse_args()
    if min(args.direct,args.recurrence,args.counts) < 0:
        parser.error('bounds must be nonnegative')
    recurrence_certificates()
    states,E,O,sink = build_and_certify_pair()
    graph_certificates(states,E,O,sink)
    arithmetic_checks(args.direct,args.recurrence)
    counts(E,O,args.counts)
    print('All exact certificates passed. No digits of pi were evaluated.')


if __name__ == '__main__':
    main()

