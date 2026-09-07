#!/usr/bin/env python3
"""Finite algebra checks for the no-0^L SFT Fourier-slicing proof sketch.

These checks are not an infinite-dimensional theorem verification and do not
provide numerical continued-fraction Fourier constants or a Markov constant.
Run: python p1prime_sft_fourier_audit.py
Requires Python 3.10+ and NumPy.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import log
import numpy as np

@dataclass
class Model:
    b: int
    L: int
    lam: float
    h: np.ndarray
    words: list[tuple[int, ...]]
    end: np.ndarray
    prob: np.ndarray
    P: np.ndarray


def model(b: int, L: int) -> Model:
    if b < 2 or L < 2:
        raise ValueError('Need b >= 2 and L >= 2')
    lo, hi = 1., float(b)
    for _ in range(90):
        z = (lo + hi) / 2
        if (b-1) * sum(z**(-j) for j in range(1, L+1)) > 1:
            lo = z
        else:
            hi = z
    lam = (lo + hi) / 2
    h = np.array([(b-1)*sum(lam**(-j) for j in range(1,L-u+1))
                  for u in range(L)])
    words = list(product(range(b), repeat=L))
    end = np.full((L, b**L), -1, dtype=int)
    prob = np.zeros((L, b**L))
    P = np.zeros((L,L))
    for u in range(L):
        for a, w in enumerate(words):
            v = u
            for digit in w:
                v = v+1 if digit == 0 else 0
                if v == L:
                    break
            else:
                end[u,a] = v
                prob[u,a] = lam**(-L)*h[v]/h[u]
                P[u,v] += prob[u,a]
    return Model(b,L,lam,h,words,end,prob,P)


def test_counts_and_rows(m: Model) -> None:
    b,L = m.b,m.L
    c=(b-1)/b
    assert np.allclose(m.P.sum(axis=1),1, atol=3e-13)
    assert c-1e-13 <= m.h.min() and m.h.max() <= 1+1e-13
    for u in range(L):
        for v in range(L):
            predicted = (b-1)*(b**(L-v-1) - (b**(u-v-1) if u>v else 0))
            actual = int((m.end[u] == v).sum())
            assert actual == predicted, (b,L,u,v,actual,predicted)
            for a in range(b**L):
                formula = a >= b**u and a % b**v == 0 and a % b**(v+1) != 0
                assert (m.end[u,a] == v) == formula
    R=c**(-2)
    for v in range(L):
        assert m.P[:,v].max()/m.P[:,v].min() <= R+1e-11
    assert (b/m.lam)**L <= 2+1e-12


def kernels(m: Model, constraints: dict[int,int], n: int):
    """Positions in constraints are zero-indexed; n counts whole L-blocks."""
    allowed=[]
    clean=[]
    for j in range(n):
        local={p-j*m.L:d for p,d in constraints.items() if j*m.L<=p<(j+1)*m.L}
        allowed.append(np.array([all(w[p]==d for p,d in local.items()) for w in m.words]))
        clean.append(not local)
    H=np.ones(m.L)
    out=[None]*n
    ratios=[]
    for j in range(n-1,-1,-1):
        numer=np.zeros_like(m.prob)
        for u in range(m.L):
            mask=allowed[j] & (m.end[u]>=0)
            numer[u,mask]=m.prob[u,mask]*H[m.end[u,mask]]
        denom=numer.sum(axis=1)
        Q=np.divide(numer,denom[:,None],out=np.zeros_like(numer),where=denom[:,None]>0)
        out[j]=Q
        if clean[j] and (j==n-1 or clean[j+1]):
            valid=m.prob>0
            ratios.extend((Q[valid]/m.prob[valid]).tolist())
        if denom.max()==0:
            return None
        H=denom/denom.max()
    if H[0]==0:
        return None
    R=(m.b/(m.b-1))**2
    if ratios:
        assert max(ratios) <= R+2e-11, (m.b,m.L,max(ratios),R)
    assert all(np.all(Q.sum(axis=1)<=1+2e-13) for Q in out)
    return out


def matrix(m:Model,Q:np.ndarray,t:float)->np.ndarray:
    phase=np.exp(-2j*np.pi*np.arange(m.b**m.L)*t)
    A=np.zeros((m.L,m.L),dtype=complex)
    for u in range(m.L):
        for v in range(m.L):
            mask=m.end[u]==v
            A[u,v]=(Q[u,mask]*phase[mask]).sum()
    return A


def direct_prefixes(m:Model, constraints:dict[int,int], n:int):
    rows=[]
    for blocks in product(range(m.b**m.L),repeat=n):
        state=0
        prior=1.
        number=0
        for j,a in enumerate(blocks):
            if any(m.words[a][p-j*m.L]!=d for p,d in constraints.items()
                   if j*m.L<=p<(j+1)*m.L):
                break
            v=m.end[state,a]
            if v<0:
                break
            prior*=m.prob[state,a]
            state=v
            number=number*m.b**m.L+a
        else:
            rows.append((blocks,number,prior))
    total=sum(x[2] for x in rows)
    return [(bl,num,p/total) for bl,num,p in rows] if total else []


def test_conditioned_fourier(m:Model,constraints:dict[int,int],n:int)->None:
    Q=kernels(m,constraints,n)
    direct=direct_prefixes(m,constraints,n)
    assert (Q is not None)==bool(direct)
    if Q is None:
        return
    for blocks,number,p in direct:
        state=0
        got=1.
        for j,a in enumerate(blocks):
            got*=Q[j][state,a]
            state=m.end[state,a]
        assert abs(got-p)<2e-12
    B=m.b**m.L
    for k in [0,1,2,3,7,11,B,B+1,B**n-1,B**n,B**n+1]:
        v=np.eye(m.L,dtype=complex)[0]
        for j in range(n):
            v=v@matrix(m,Q[j],k/B**(j+1))
        tail=np.exp(-1j*np.pi*k/B**n)*np.sinc(k/B**n)
        got=v.sum()*tail
        expected=sum(p*np.exp(-2j*np.pi*k*num/B**n) for _,num,p in direct)*tail
        assert abs(got-expected)<2e-10, (k,got,expected)
    # Exact k=k'+ell*B^{J-1} product identity and inequality at J=2.
    if n>=2:
        J=2
        S=0.
        for k in range(B**J):
            v=np.eye(m.L,dtype=complex)[0]
            for j in range(J):
                v=v@matrix(m,Q[j],k/B**(j+1))
            S+=np.abs(v).sum()
        regrouped=0.
        bound=0.
        for kp in range(B**(J-1)):
            v=np.eye(m.L,dtype=complex)[0]@matrix(m,Q[0],kp/B)
            C=np.zeros(m.L)
            for ell in range(B):
                A=matrix(m,Q[J-1],kp/B**J+ell/B)
                regrouped+=np.abs(v@A).sum()
                C+=np.abs(A).sum(axis=1)
            bound+=np.abs(v).sum()*C.max()
        assert abs(S-regrouped)<2e-9
        assert S<=bound+2e-9


def test_shift_bounds(m:Model)->None:
    B=m.b**m.L
    raw_bound=m.b*m.L*(m.b/m.lam)**m.L*(2+m.L*log(m.b))
    # Check the shifted block matrix norm on several genuinely shifted grids.
    for t in [0.,0.037/B,0.47/B,0.999/B,0.1234567]:
        sums=np.zeros(m.L)
        for ell in range(B):
            sums+=np.abs(matrix(m,m.prob,t+ell/B)).sum(axis=1)
        assert sums.max()<=raw_bound+1e-8


def stress_conditioning(m:Model)->None:
    # A long forced nonzero packet, plus constraints beyond it.  Probability of
    # conditioning can be tiny; normalization of backward likelihoods avoids
    # underflow without changing the Doob ratios.
    n=550
    F={p:1 for p in range(43*m.L,397*m.L)}
    F.update({p:1 for p in range(430*m.L,432*m.L)})
    assert kernels(m,F,n) is not None
    # Right edge of an almost-maximal zero-run: compatible with reset digits.
    F={p:1 for p in range(25*m.L,26*m.L)}
    for j in [7,19,42,59]:
        F.update({j*m.L+i:0 for i in range(1,m.L)})
    assert kernels(m,F,80) is not None


def main()->None:
    count=0
    for b in range(2,5):
        for L in range(2,6):
            m=model(b,L)
            test_counts_and_rows(m)
            if b**L<=128:
                test_shift_bounds(m)
            count+=1
    rng=np.random.default_rng(6127)
    scenarios=0
    for b,L,n in [(2,2,5),(2,3,3),(3,2,3)]:
        m=model(b,L)
        tests=[{}, {L:1}, {p:1 for p in range(L,2*L)},
               {p:0 for p in range(L,2*L-1)}]
        for _ in range(12):
            tests.append({p:int(rng.integers(b)) for p in range(n*L) if rng.random()<.35})
        for F in tests:
            test_conditioned_fourier(m,F,n)
            scenarios+=1
    stress_conditioning(model(2,5))
    print(f'PASS: exact word/count formulas and row comparability for {count} (b,L) models.')
    print(f'PASS: {scenarios} finite conditioning/Fourier scenarios; matrix regrouping checks.')
    print('PASS: shifted block-mask bounds on sampled grids; long-packet conditioning stress tests.')
    print('These finite checks are not a verification of the infinite proof or a numerical kappa certificate.')

if __name__=='__main__':
    main()

