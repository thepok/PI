#!/usr/bin/env python3
"""Exact checks accompanying the all-index congruence
  q_n == binom(n,n/4) mod 2**(v2(n)+1),  4 | n, n>0,
for the published modified-Salikhov recurrence.

It implies v2(q_(2**k*m))=popcount(3*m) whenever k>=2, m odd,
and popcount(3*m)<=k. Together with the previously proved companion
bound this leaves linear divisibility in the reduced numerator.

The proof is the ramified-ring coefficient argument in the answer. Finite
recurrence checks are implementation tests, NOT the proof of all indices.
No pi evaluation, decimal digits, floating point, network, or dependencies.

Source: https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt
Run: python salikhov_multiplier_cancellation_certificate.py --terms 1000 --direct 16
"""
from fractions import Fraction as Q
from math import comb
import argparse


def rec(n):
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
        *(559455*n**4+3399916*n**3+7651391*n**2+7554302*n+2760952))


def seq(N):
    a=[Q(0),-Q(11272,3),-Q(6156093056,105)]
    b=[Q(1,4),Q(1196),Q(18662336)]
    for n in range(max(0,N-2)):
        p=rec(n)
        for x in (a,b):
            x.append(-sum(p[j]*x[n+j] for j in range(3))/p[3])
    return a[:N+1],b[:N+1]


def vi(x):
    x=abs(x)
    if not x: raise ValueError('v2(0) is not finite')
    return (x & -x).bit_length()-1


def val(x):
    x=Q(x)
    return vi(x.numerator)-vi(x.denominator)


def p2(k):
    return Q(2**k) if k>=0 else Q(1,2**(-k))


# Z[sqrt(2)]: pairs a+b*tau with tau**2=2.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def times(x,y): return (x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
ZERO=(0,0)
ONE=(1,0)
TAU=(0,1)


def pmul(a,b):
    r=[ZERO]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):r[j+k]=add(r[j+k],times(x,y))
    return r


def ppow(a,n):
    r=[ONE]
    while n:
        if n&1:r=pmul(r,a)
        n//=2
        if n:a=pmul(a,a)
    return r


def structural_certificate():
    # H(2*tau*z) = 32*h(z).
    H=[32,-112,156,-100,25]
    h=[ONE,(0,-7),(39,0),(0,-50),(50,0)]
    w=ONE
    for j,c in enumerate(H):
        assert times((c,0),w)==times((32,0),h[j])
        w=times(w,(0,2))
    # U=N/D and U == (1+z^4)(1+tau*z) mod 2, coefficientwise.
    N=pmul(ppow([ONE,(0,-2)],2),ppow(h,2))
    D=ppow([ONE,(0,-1)],3)
    W=pmul([ONE,ZERO,ZERO,ZERO,ONE],[ONE,TAU])
    WD=pmul(W,D)
    for j in range(max(len(N),len(WD))):
        e=add(N[j] if j<len(N) else ZERO,
              neg(WD[j] if j<len(WD) else ZERO))
        assert e[0]%2==0 and e[1]%2==0,(j,e)
    assert D[0]==ONE
    # For v2(n)=2, (1+x)^n == (1+x^4)^m in F_2[[x]], m odd.
    # Hence the only exceptional low-order sum 1+sum_{j=1}^4 binom(n,j)
    # has parity 1+1=0. The proof does not extrapolate from a finite m-range.
    print('Exact ramified rescaling and polynomial identity U == (1+z^4)(1+tau*z) mod 2 certified.')


def mul_int(a,b,limit):
    r=[0]*min(len(a)+len(b)-1,limit+1)
    for j,x in enumerate(a):
        for k,y in enumerate(b[:max(0,len(r)-j)]):r[j+k]+=x*y
    return r


def pow_int(a,n,limit):
    r=[1]
    while n:
        if n&1:r=mul_int(r,a,limit)
        n//=2
        if n:a=mul_int(a,a,limit)
    return r


def direct_q(n):
    H=[32,-112,156,-100,25]
    F=mul_int([1,-2,1],mul_int(H,H,10),10)
    A=pow_int(F,n,3*n)
    C=sum(Q(a*comb(6*n-j,3*n-j),2**(6*n+1-j))
          for j,a in enumerate(A))
    return (-1)**n*p2(1-5*n//2)*C


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms',type=int,default=1000)
    parser.add_argument('--direct',type=int,default=16)
    args=parser.parse_args()
    if args.terms<4 or args.direct<0:
        parser.error('--terms must be >=4 and --direct nonnegative')
    structural_certificate()
    a,b=seq(max(args.terms,args.direct))
    for n in range(args.direct+1):
        assert direct_q(n)==p2(2-5*n//2)*b[n],n
    print(f'Original rational coefficient extraction agrees with recurrence at n=0..{args.direct}.')
    exact_cases=0
    bounded_family_cases=0
    for n in range(4,args.terms+1,4):
        k=vi(n);m=n//2**k
        q=p2(2-5*n//2)*b[n]
        assert q.denominator==1
        delta=q-comb(n,n//4)
        assert not delta or val(delta)>=k+1,(n,k,val(delta))
        s=(3*m).bit_count()
        assert vi(comb(n,n//4))==s
        if s<=k:
            exact_cases+=1
            assert val(q)==s,(n,val(q),s)
            r=2*n+1-((4*n+1).bit_length()-1)
            c=p2(2-5*n//2)*a[n]
            assert val(c)>=r
            rat=-a[n]/b[n]
            assert rat.denominator%2==1
            assert vi(rat.numerator)==val(c)-s
            assert vi(rat.numerator)>=r-s>0
        if m<2**(k-1):
            bounded_family_cases+=1
            assert s<=k
    print(f'Congruence checked for every positive multiple of 4 through {args.terms}.')
    print(f'Exact multiplier valuation and surviving reduced-numerator depth checked in {exact_cases} admissible cases.')
    print(f'The square-root-size subfamily contributes {bounded_family_cases} of these cases.')
    print('All-index validity is supplied by the proof, not by these finite tests.')


if __name__=='__main__':main()

