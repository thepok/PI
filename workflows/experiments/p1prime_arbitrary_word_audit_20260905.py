"""Finite checks for the arbitrary single forbidden-word proof sketch.
Requires Python 3.10+ and NumPy. Prints results without writing files.
Exact finite identities/inequalities and floating Fourier samples are checked;
this does not verify an infinite proof or certify a Fourier-decay exponent.
"""
from itertools import product
from fractions import Fraction
import math, json
import numpy as np


def transition_table(w: str, b: int = 10):
    m = len(w)
    tab = []
    for u in range(m):
        row = []
        for d in range(b):
            text = w[:u] + str(d)
            if text.endswith(w):
                row.append(-1)
            else:
                row.append(max([0] + [v for v in range(1, m) if text.endswith(w[:v])]))
        tab.append(row)
    return tab


def follow(tab, u, z):
    for c in z:
        u = tab[u][int(c)]
        if u < 0:
            return -1
    return u


def prefix_exclusions(w, u):
    m = len(w)
    candidates = []
    for r in range(1, m+1):
        ell = m-r
        if ell == 0 or (ell <= u and w[:u].endswith(w[:ell])):
            candidates.append(w[m-r:])
    # Inclusion-maximal prefix cylinders = strings with no shorter selected prefix.
    out = []
    for p in sorted(candidates, key=len):
        if not any(p.startswith(q) for q in out):
            out.append(p)
    return out


def suffix_exclusions(w, v):
    candidates = [w[:t] for t in range(v+1, len(w)) if v == 0 or w[:t].endswith(w[:v])]
    out = []
    for p in sorted(candidates, key=len):
        if not any(p.endswith(q) for q in out):
            out.append(p)
    return out


def exact_class(w, u, v, z):
    left = 1 - sum(z.startswith(p) for p in prefix_exclusions(w, u))
    right = int(v == 0 or z.endswith(w[:v])) - sum(z.endswith(p) for p in suffix_exclusions(w, v))
    return left*right


def matrices(w, b=10):
    tab = transition_table(w, b)
    m = len(w)
    D = np.zeros((m, m), dtype=object)
    for u in range(m):
        for v in tab[u]:
            if v >= 0:
                D[u,v] += 1
    N = np.linalg.matrix_power(D, m)
    N2 = N @ N
    return tab, N, N2


def check_counts(w):
    tab,N,N2=matrices(w)
    m=len(w); B=10**m
    assert all(9*sum(N[u,:]) >= 8*B for u in range(m))
    for u in range(m):
        for v in range(m):
            # Uniform suffix-conditioned bound; no reset word or Perron vector.
            assert 2*int(N2[u,v]) >= 10**(2*m-v), (w,u,v)
            assert Fraction(N2[u,v],10**(2*m-v)) >= Fraction(2,3)-Fraction(m+1,B)
            assert int(N2[u,v]) <= 10**(2*m-v)
    ratio=max(Fraction(max(N2[:,v]),min(N2[:,v])) for v in range(m))
    return {'word':w,'length':m,
            'min_suffix_conditioned_survival':float(min(Fraction(N2[u,v],10**(2*m-v)) for u in range(m) for v in range(m))),
            'min_row_survival':float(min(Fraction(sum(N[u,:]),B) for u in range(m))),
            'actual_two_block_column_ratio':float(ratio),
            'proved_comparison_bound':2}


def restricted_growth(n):
    def rec(a, top):
        if len(a)==n:
            yield ''.join(map(str,a)); return
        for x in range(top+2):
            yield from rec(a+[x],max(top,x))
    yield from rec([0],0)


def main():
    # Exact arithmetic for the analytic sufficient thresholds, not a finite
    # verification of the underlying infinite-dimensional theorem.
    assert (20*81**4)**9 < 10**81
    assert (20*187**4)**18 < 10**187
    # Exhaustive algebra, including every decimal word of lengths 2 and 3.
    words=[''.join(x) for m in (2,3) for x in product('0123456789',repeat=m)]
    words += ['0000','0101','0123','0010','0110','0909','9999','0120']
    checks=0
    sampled_masks=[]
    for w in words:
        m=len(w); tab=transition_table(w)
        E=[prefix_exclusions(w,u) for u in range(m)]
        T=[suffix_exclusions(w,v) for v in range(m)]
        B=10**m
        counts=np.zeros((m,m),dtype=np.int64)
        vals=np.zeros((m,m,B),dtype=np.float64) if m==4 else None
        for a in range(B):
            z=f'{a:0{m}d}'
            right=[int(v==0 or z.endswith(w[:v]))-sum(z.endswith(p) for p in T[v]) for v in range(m)]
            for u in range(m):
                actual=follow(tab,u,z)
                left=1-sum(z.startswith(p) for p in E[u])
                got=[left*r for r in right]
                assert got==[int(actual==v) for v in range(m)], (w,u,z,actual,got)
                if actual>=0:
                    counts[u,actual]+=1
                    if vals is not None: vals[u,actual,a]=1/B
                checks+=m
        _,N,_=matrices(w)
        assert np.array_equal(counts,N)
        if vals is not None:
            maxsample=0.0
            for shift in [0.0,.125,.5,.8125]:
                coeff=np.fft.fft(vals*np.exp(-2j*np.pi*np.arange(B)*shift/B),axis=2)
                maxsample=max(maxsample,float(np.max(np.sum(np.abs(coeff),axis=(1,2)))))
            bound=m*(m+1)**2*(2+math.log(B))
            assert maxsample <= bound
            sampled_masks.append({'word':w,'sampled_max_raw_shifted_mask':maxsample,'proved_raw_bound':bound})
    # Counts depend only on equality pattern, not names of the digits.
    comparison_total=0
    worst=(0.0,None)
    for m in range(2,9):
        for w in restricted_growth(m):
            row=check_counts(w)
            comparison_total+=1
            if row['actual_two_block_column_ratio']>worst[0]:
                worst=(row['actual_two_block_column_ratio'],w)
    rng=np.random.default_rng(934815)
    longwords=[]
    for m in (10,16,32,64):
        longwords.extend(['0'*m, '0'*(m-1)+'1', ('01'*m)[:m],
                          ('0123456789'*m)[:m],
                          ''.join(map(str,rng.integers(0,10,m)))])
    longrows=[check_counts(w) for w in longwords]
    result={'decimal_word_sets_checked':len(words),'exact_entry_membership_comparisons':checks,
            'equality_patterns_checked_lengths_2_to_8':comparison_total,
            'largest_observed_two_block_column_ratio':worst,
            'shifted_mask_samples':sampled_masks,'long_word_checks':longrows}
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
