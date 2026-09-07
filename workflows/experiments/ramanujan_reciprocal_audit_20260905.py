#!/usr/bin/env python3
"""Exact algebra certificates and numerical diagnostics for the Ramanujan reciprocal.

Requires: Python >=3.10, sympy, mpmath.
Run: python ramanujan_reciprocal_audit.py --n 1000 --precision 80

The polynomial identities are exact symbolic computations.  The coefficient scan
is finite, and the mpmath diagnostics are not interval-certified.  The infinite
sign conclusions use the induction in the accompanying proof sketch.  Nothing
here is a Lean verification or a proof of a pi-digit occurrence theorem.
"""
from __future__ import annotations
import argparse
import platform
from math import comb
from time import perf_counter
import sympy as sp
import mpmath as mp

P8_ASC = [95940, 508108, 1529306, 2795373, 2948477, 1797616,
          626040, 115632, 8784]
P11_ASC = [244539576, 981843408, 2562779172, 5175230883,
           6760542367, 5486363918, 2813807241, 920957279,
           189234184, 23024952, 1436688, 30384]


def exact_algebra() -> None:
    n = sp.symbols('n')
    q = lambda t: (6*t+1)*(2*t-1)**3/(8*t**3*(6*t-5))
    assert sp.expand(8*(n+1)**3*(6*n+1)-(6*n+7)*(2*n+1)**3 - (24*n*(n+1)**2+1)) == 0
    qprime = 3*(2*n-1)**2*(12*n**2-12*n-5)/(8*n**4*(6*n-5)**2)
    assert sp.cancel(sp.diff(q(n), n)-qprime) == 0
    assert q(sp.Integer(4))-q(sp.Integer(1)) == sp.Rational(63,9728)
    U = (sp.Rational(7,8)*q(n-2)*(q(n)-q(n-1))
         -sp.Rational(41,512)*(q(n)-q(n-2)))
    V = (-sp.Rational(23,8)*q(n-2)*q(n-3)*(q(n)-q(n-1))
         +sp.Rational(937,512)*q(n-3)*(q(n)-q(n-2))
         -sp.Rational(861,4096)*(q(n)-q(n-3)))
    P8 = sum(sp.Integer(a)*(n-3)**j for j,a in enumerate(P8_ASC))
    P11 = sum(sp.Integer(a)*(n-4)**j for j,a in enumerate(P11_ASC))
    den8 = 2048*n**3*(n-2)**2*(n-1)**3*(6*n-17)*(6*n-5)
    den11 = 32768*n**3*(n-3)**2*(n-2)**3*(n-1)**3*(6*n-23)*(6*n-5)
    assert sp.cancel(U-3*P8/den8) == 0
    assert sp.cancel(V-3*P11/den11) == 0
    assert all(a>0 for a in P8_ASC+P11_ASC)
    print('PASS: normalized coefficient monotonicity polynomial identity')
    print('PASS: q derivative identity and q(4)>q(1)')
    print('PASS: U(n)=3 P8(n-3)/den8, exactly; all P8 coefficients positive')
    print('PASS: V(n)=3 P11(n-4)/den11, exactly; all P11 coefficients positive')
    print('P8 ascending coefficients:', P8_ASC)
    print('P11 ascending coefficients:', P11_ASC)

    # Independent formal local-series check through the terms needed for kappa.
    u, A, C = sp.symbols('u A C', nonzero=True)
    y = A*(1+u**2/sp.Integer(8)+25*u**4/sp.Integer(384)) + C*(u+3*u**3/sp.Integer(8)+147*u**5/sp.Integer(640))
    f = sp.expand(y*y - 6*(1-u*u)/u*y*sp.diff(y,u))
    assert sp.expand(f).coeff(u,-1) == -6*A*C
    assert sp.expand(f).coeff(u,0) == -A*A/2-6*C*C
    assert sp.expand(f).coeff(u,1) == -A*C
    print('PASS: local f coefficients u^(-1), u^0, u^1')


def exact_coefficients(N: int) -> tuple[list[int], list[int]]:
    start=perf_counter()
    c=[(6*j+1)*comb(2*j,j)**3 for j in range(N+1)]
    rho=[1]
    for j in range(1,N+1):
        rho.append(-sum(c[k]*rho[j-k] for k in range(1,j+1)))
    eta=[1]+[rho[j]-128*rho[j-1] for j in range(1,N+1)]
    assert [j for j in range(1,N+1) if rho[j]>=0] == [2]
    assert [j for j in range(1,N+1) if eta[j]<=0] == [1,3]
    assert all(abs(rho[j])<=64**j for j in range(N+1))
    assert all(abs(eta[j])<3*64**j for j in range(1,N+1))
    print(f'Exact integer recurrence through N={N}: {perf_counter()-start:.3f} seconds')
    print('rho[0:8]:', rho[:8])
    print('eta[0:8]:', eta[:8])
    print('Nonnegative rho indices 1..N: [2]')
    print('Nonpositive eta indices 1..N: [1, 3]')
    print('PASS: finite coefficient magnitude bounds')
    print('Maximum bit length of abs(rho):', max(abs(v).bit_length() for v in rho))
    return rho,eta


def diagnostics(rho: list[int], eta: list[int], precision: int) -> None:
    mp.mp.dps=precision
    N=len(rho)-1
    A=mp.sqrt(mp.pi)/mp.gamma(mp.mpf(3)/4)**2
    C=-2*mp.sqrt(mp.pi)/mp.gamma(mp.mpf(1)/4)**2
    d=-A*A/2-6*C*C
    sigma=-mp.pi*d/6
    kappa=mp.mpf(5)/8-mp.mpf(3)/2*sigma*sigma
    lc=mp.sqrt(mp.pi)/12
    print(f'Mpmath diagnostics at {precision} decimal digits (not interval-certified):')
    for name,value in [('sigma',sigma),('kappa',kappa),('sqrt(pi)/12',lc),('sqrt(pi)/36',lc/3)]:
        print(name,mp.nstr(value,28))
    print('n, rho/leading, n*(rho/leading-1), eta/leading, n*(eta/leading-1)')
    for n in [20,100,500,1000]:
        if n>N: continue
        scale=lc*mp.mpf(n)**(-mp.mpf('1.5'))
        rr=(mp.mpf(rho[n])/mp.mpf(64)**n)/(-scale)
        er=(mp.mpf(eta[n])/mp.mpf(64)**n)/scale
        print(n,*(mp.nstr(x,19) for x in [rr,n*(rr-1),er,n*(er-1)]))
    print('M, 4^M*T_M/leading, 4^M*S_M/leading (tails truncated at N)')
    for M in [10,100,500]:
        if M+30>=N: continue
        tt=mp.fsum(mp.mpf(rho[m])/mp.mpf(64)**m*mp.mpf(4)**(M-m) for m in range(M+1,N+1))
        ss=mp.fsum(mp.mpf(eta[m])/mp.mpf(64)**m*mp.mpf(4)**(M-m) for m in range(M+1,N+1))
        scale=lc/3*mp.mpf(M)**(-mp.mpf('1.5'))
        print(M,mp.nstr(tt/(-scale),19),mp.nstr(ss/scale,19))
    print('Proved truncation bounds before rounding: |T remainder| <= 4^(-N)/3; |S remainder| <= 4^(-N).')
    print('No rounding-error bound is claimed for the mpmath output.')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,default=1000)
    parser.add_argument('--precision',type=int,default=80)
    args=parser.parse_args()
    if args.n<8: parser.error('--n must be at least 8')
    if args.precision<30: parser.error('--precision must be at least 30')
    print('Python',platform.python_version(),'SymPy',sp.__version__,'mpmath',mp.__version__)
    start=perf_counter()
    exact_algebra()
    rho,eta=exact_coefficients(args.n)
    diagnostics(rho,eta,args.precision)
    print(f'Total elapsed: {perf_counter()-start:.3f} seconds')
    print('No Lean run performed; finite scans do not prove the infinite sign conclusions.')

if __name__=='__main__':
    main()
