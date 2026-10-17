"""Exact audit of moment-cancelled positive Pythagorean pi carriers.

Finite assertions support the accompanying proof sketch; they do not prove
any decimal-word occurrence statement. Standard library only.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import comb, gcd, isqrt, lcm
import argparse
import json
from pathlib import Path


def triangle(k):
    a,b,c=1,0,1
    for _ in range(k):
        a,b=3*a-4*b,4*a+3*b
        c*=5
    a,b=sorted((abs(a),abs(b)))
    assert a*a+b*b==c*c and gcd(a,b)==1
    return a,b,c


def weights(ts):
    ss=[F(a+b,c) for a,b,c in ts]
    tt=[s*s for s in ss]
    d=[]
    for i,t in enumerate(tt):
        q=ss[i]
        for j,u in enumerate(tt):
            if i!=j:q*=t-u
        d.append(1/q)
    scale=sum(d)
    return [q/scale for q in d]


def moment(ts,ws,h):
    return sum(w*(F(a,c)**h+F(b,c)**h) for (a,b,c),w in zip(ts,ws))


def primes(n):
    ok=bytearray(b'\x01')*(n+1)
    if n>=0:ok[0]=0
    if n>=1:ok[1]=0
    for p in range(2,isqrt(n)+1):
        if ok[p]:
            ok[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if ok[p]]


def rough_part(n):
    for p in (2,5):
        while n%p==0:n//=p
    return n


def valuation5(x):
    x=F(x)
    assert x
    a,b=abs(x.numerator),x.denominator
    out=0
    while a%5==0:a//=5;out+=1
    while b%5==0:b//=5;out-=1
    return out


def rough_bound(N,K,ps=None):
    X=2*N+1
    M=max(X//(2*K+1),isqrt(X))
    out=1
    for p in (ps if ps is not None else primes(M)):
        if p>M:break
        if p in (2,5):continue
        v=p
        while v<=X//p:v*=p
        out*=v
    return out


def certificate(max_n=160):
    # All four points have both normalized legs <= 4/5.
    exponents=[1,6,11,16]
    K=len(exponents)-1
    ts=[triangle(k) for k in exponents]
    assert all(5*b<=4*c for a,b,c in ts)
    ws=weights(ts)
    assert sum(ws)==1
    assert all(moment(ts,ws,2*n+1)==0 for n in range(K))
    scale=lcm(*(w.denominator for w in ws))
    assert scale%5!=0 and all(valuation5(w)>=0 for w in ws)
    C=ts[-1][2]
    v0=exponents[0]+2*sum(exponents[1:])
    S=exponents[-1]
    A=[(a*(C//c),b*(C//c)) for a,b,c in ts]
    iw=[int(scale*w) for w in ws]
    assert all(sum(w*(a**h+b**h) for w,(a,b) in zip(iw,A))==0
               for h in range(1,2*K,2))

    ordered=sorted(zip(ts,ws),key=lambda v:F(v[0][0]+v[0][1],v[0][2]))
    (a0,b0,c0),w0=ordered[0]
    assert w0>0
    x0=F(b0,c0)
    x1=max(F(b,c) for (a,b,c),w in ordered[1:])
    assert x1<x0
    absrest=sum(abs(w) for t,w in ordered[1:])
    n0=0
    while 4*absrest*(x1/x0)**(2*n0+1)>w0:n0+=1
    assert n0==57

    all_primes=primes(2*max_n+1)
    positive=[]
    negative=[]
    partial=F(0)
    denominator_rows=[]
    prime_checks=0
    for n in range(max_n+1):
        m=moment(ts,ws,2*n+1)
        if m>0:positive.append(n)
        if m<0:negative.append(n)
        if n>=n0:assert m>0
        if n>=K:
            assert valuation5(m)==-v0-2*(n-K)*S
        term=scale*F(comb(2*n,n),4**n*(2*n+1))*m
        partial+=term
        if n>=K and 2*n-1<5**S:
            assert valuation5(partial)==valuation5(term)
            assert partial.numerator%5!=0
        d=rough_part(partial.denominator)
        bound=rough_bound(n,K,all_primes)
        assert bound%d==0, (n,d,bound)
        X=2*n+1
        M=max(X//(2*K+1),isqrt(X))
        for p in all_primes:
            if p<=M or p in (2,5):continue
            if p>X:break
            assert term.denominator%p!=0
            prime_checks+=1
        if n in (20,40,80,160):
            denominator_rows.append({
                'N':n,'rough_denominator':str(d),
                'rough_bound':str(bound),
                'smooth_denominator_decimal_digits':len(str(partial.denominator//d)),
                'prefix_v5':valuation5(partial),
            })

    # Exact upper bounds for cleared *infinite* tails use the proved geometric
    # majorant, not digits of pi and not numerical summation.
    rho=F(16,25)
    upper_constant=2*scale*sum(abs(w) for w in ws)*F(4,5)/(1-rho)
    cleared=[]
    for N in (1000,2000,4000):
        B=rough_bound(N,K)
        value=B*upper_constant*rho**(N+1)/(2*N+3)
        k=0
        if value<1:
            while value*10**(k+1)<1:k+=1
        else:
            while value>=10**k:k+=1
            k=-k
        cleared.append({'N':N,'rough_bound_bits':B.bit_length(),
                        'certified_upper_lt_10_power':-k,
                        'inequality_checked': bool(value< F(10)**(-k))})
        assert value< F(10)**(-k)
    # Exact elementary exponential margin for K=3, rho=16/25.
    assert 16**8<25**7
    return {
        'status':'experiment',
        'claim_scope':'Exact finite arithmetic audit plus exact checks of constants in a written proof sketch; no V1/CW0 claim.',
        'K':K,'gaussian_exponents':exponents,
        'triangles':[list(t) for t in ts],
        'weights':[str(w) for w in ws],
        'integer_scale':str(scale),
        'annihilated_odd_moments':[1,3,5],
        'five_adic_law':{'v0':v0,'largest_exponent':S,
            'moment_valuation':'-v0 - 2*(n-K)*S for every n>=K',
            'prefix_valuation_range':'2*N-1 < 5^S',
            'reduced_prefix_numerator_is_5_unit':True},
        'coefficient_positivity_from_n':n0,
        'last_negative_coefficient_in_audit':max(negative),
        'negative_coefficient_indices':negative,
        'max_n':max_n,'large_prime_term_checks':prime_checks,
        'denominator_samples':denominator_rows,
        'cleared_infinite_tail_upper_bounds':cleared,
        'elementary_rate_margin':{'left':16**8,'right':25**7},
        'limitations':[
            'The nonsmooth clearing multiplier depends on N.',
            'The remaining powers of 2 and 5 in the rational prefix grow with N.',
            'No ordered decimal residue or prescribed word is forced.',
            'The proof sketch, not a finite audit, supplies the all-N conclusion.'
        ]
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-n',type=int,default=160)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=certificate(args.max_n)
    payload=json.dumps(data,indent=2)+'\n'
    if args.output:args.output.write_text(payload)
    print(json.dumps({'status':'PASS','max_n':args.max_n,
        'large_prime_term_checks':data['large_prime_term_checks'],
        'positive_from':data['coefficient_positivity_from_n'],
        'cleared_tail_bounds':data['cleared_infinite_tail_upper_bounds'],
        'certificate_sha256':sha256(payload.encode()).hexdigest()},indent=2))
