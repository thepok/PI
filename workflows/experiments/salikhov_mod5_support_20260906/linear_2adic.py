#!/usr/bin/env python3
"""Exact checks of a linear-depth 2-adic companion bound for the published
modified-Salikhov integral. No pi evaluation, digits, or floating-point arithmetic.

Bound tested for every n>=1:
  v_2(c_n) >= 2*n + 1 - floor(log_2(4*n+1)),
  c_n = 2**(2-floor(5*n/2))*a_n.

Also checks the endpoint factorization and a finite truncation of the 2-adic
primitive against the independently generated rational companion. The omitted
primitive tail has a proved lower valuation, not an estimated numerical error.

Run: python salikhov_linear_2adic_test.py --terms 400 --primitive-orders 6
Source of recurrence: https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt
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
    a = [Q(0), -Q(11272,3), -Q(6156093056,105)]
    b = [Q(1,4), Q(1196), Q(18662336)]
    for n in range(max(0,N-2)):
        p=rec(n)
        for s in (a,b):
            s.append(-sum(p[j]*s[n+j] for j in range(3))/p[3])
    return a[:N+1],b[:N+1]


def v2int(x):
    x=abs(x)
    if not x: raise ValueError('valuation of zero requested')
    return (x & -x).bit_length()-1


def v2(x):
    x=Q(x)
    return v2int(x.numerator)-v2int(x.denominator)


def p2(k):
    return Q(2**k) if k>=0 else Q(1,2**(-k))


# Gaussian rational arithmetic, representing x+y*i by (x,y).
def G(x,y=0): return Q(x),Q(y)
ZERO,ONE,I = G(0),G(1),G(0,1)
def add(a,b): return a[0]+b[0],a[1]+b[1]
def neg(a): return -a[0],-a[1]
def sub(a,b): return add(a,neg(b))
def mul(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def inv(a):
    d=a[0]*a[0]+a[1]*a[1]
    return a[0]/d,-a[1]/d

def div(a,b): return mul(a,inv(b))
def pw(a,n):
    if n<0:return pw(inv(a),-n)
    r=ONE
    while n:
        if n&1:r=mul(r,a)
        a=mul(a,a);n//=2
    return r

def val(a):
    # In Q_2(i), v_2(Norm(a))=2*v_2(a).
    if a==ZERO:return None
    return Q(v2(a[0]*a[0]+a[1]*a[1]),2)

def poly_mul(a,b,J):
    out=[ZERO]*min(len(a)+len(b)-1,J+1)
    for j,x in enumerate(a):
        for k,y in enumerate(b[:len(out)-j]):
            out[j+k]=add(out[j+k],mul(x,y))
    return out

def poly_power(a,n,J):
    r=[ONE]
    while n:
        if n&1:r=poly_mul(r,a,J)
        a=poly_mul(a,a,J);n//=2
    return r

def inverse_linear(w,k,J):
    out=[];v=ONE
    for j in range(J+1):
        out.append(mul(G((-1)**j*comb(k+j-1,j)),v));v=mul(v,w)
    return out


def certify_endpoints():
    alpha,beta=G(-1,-2),G(-1,2)
    delta=G(0,4)
    u=div(delta,add(G(5),alpha))
    v=neg(div(delta,sub(G(5),alpha)))
    assert val(u)==1 and val(v)==Q(1,2)
    assert val(G(7,-1))==Q(1,2)
    ratio=div(mul(add(G(5),beta),sub(G(5),alpha)),
              mul(add(G(5),alpha),sub(G(5),beta)))
    assert ratio==I and pw(ratio,4)==ONE
    # R quartic under x=alpha+4*i*t.
    x=[alpha,delta]
    x2=poly_power(x,2,4);x4=poly_power(x,4,4)
    left=x4[:]
    for j,a in enumerate(x2):left[j]=add(left[j],mul(G(6),a))
    left[0]=add(left[0],G(25))
    right=poly_mul([ZERO,G(-1),ONE],[G(-1),G(0,2)],4)
    right=poly_mul(right,[G(-1,-2),G(0,2)],4)
    right=[mul(G(-64),a) for a in right]
    assert left==right
    return alpha,u,v


def primitive_test(n,a,alpha,u,v):
    J=4*n+72
    U=poly_power([ZERO,G(-1),ONE],2*n,J)
    for factor in ([alpha,G(0,4)],[G(-1),G(0,2)],
                   [G(-1,-2),G(0,2)]):
        U=poly_mul(U,poly_power(factor,2*n,J),J)
    U=poly_mul(U,inverse_linear(u,3*n+1,J),J)
    U=poly_mul(U,inverse_linear(v,3*n+1,J),J)
    for j,coef in enumerate(U):
        if coef!=ZERO:assert val(coef)>=max(Q(0),Q(j-4*n,2))
    C=mul(G(5*(-1)**n*2**(6*n)),pw(G(7,-1),-3*n-1))
    assert val(C)==Q(9*n-1,2)
    integral=ZERO
    for j,coef in enumerate(U):integral=add(integral,mul(G(Q(1,j+1)),coef))
    err=sub(G(a),mul(C,integral))
    # For j>J, (j-4*n)/2-log2(j+1) is increasing.
    ceil_log=(J+1).bit_length()  # ceil(log2(J+2))
    tail_lower=val(C)+Q(J+1-4*n,2)-ceil_log
    assert err==ZERO or val(err)>=tail_lower,(n,val(err),tail_lower)
    return tail_lower


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--terms',type=int,default=400)
    p.add_argument('--primitive-orders',type=int,default=6)
    args=p.parse_args()
    if args.terms<1 or args.primitive_orders<0:
        p.error('terms must be positive and primitive-orders nonnegative')
    a,b=seq(max(args.terms,args.primitive_orders))
    worst=None
    for n in range(1,args.terms+1):
        c=p2(2-5*n//2)*a[n]
        r=2*n+1-((4*n+1).bit_length()-1)
        excess=v2(c)-r
        assert excess>=0,(n,v2(c),r)
        worst=excess if worst is None else min(worst,excess)
    print(f'Companion bound checked at n=1..{args.terms}; minimum excess={worst}.')
    alpha,u,v=certify_endpoints()
    print('Endpoint factorization, valuations, and logarithmic ratio i certified.')
    for n in range(1,args.primitive_orders+1):
        lower=primitive_test(n,a[n],alpha,u,v)
        print(f'n={n}: primitive agrees with a_n modulo valuation >= {lower}.')
    print('These finite checks support implementation; the coefficient/tail argument proves the all-n bound.')

if __name__=='__main__':main()

