"""Independent digit/block conditional-count and Fourier product checks.

Requires Python 3.10+ and NumPy. Prints results without writing files.
These are finite experiments, not verification of the infinite proof.
"""
from itertools import product
from fractions import Fraction
import json
import numpy as np
from p1prime_arbitrary_word_audit_20260905 import transition_table, follow


def run_case(w, case):
    m=len(w); n=8; N=m*n; B=10**m
    tab=transition_table(w)
    beta=next(str(d) for d in range(1,9) if str(d) not in (w[0],w[-1]))
    period=beta*m+w[:-1]+beta*m
    reference=(period*(N//len(period)+1))[:N]
    assert follow(tab,0,reference)>=0
    if case==0:
        forced={i:reference[i] for i in range(4*m,7*m)}
    elif case==1:
        forced={i:reference[i] for i in range(3*m+1,7*m-1)}
        forced.update({m:reference[m],N-1:reference[N-1]})
    else:
        forced={i:reference[i] for i in range(0,m-1)}
        forced.update({i:reference[i] for i in range(5*m,N)})
    # Independent digit-level suffix counts.
    Gd=[[0]*m for _ in range(N+1)]; Gd[N]=[1]*m
    for pos in range(N-1,-1,-1):
        for u in range(m):
            Gd[pos][u]=sum(Gd[pos+1][v] for digit,v in enumerate(tab[u])
                          if v>=0 and (pos not in forced or int(forced[pos])==digit))
    assert Gd[0][0]>0
    words=[f'{a:0{m}d}' for a in range(B)]
    ends=[[follow(tab,u,z) for z in words] for u in range(m)]
    Gb=[[0]*m for _ in range(n+1)]; Gb[n]=[1]*m
    masks=[]; good=[]
    for j in range(n):
        good.append([all((j*m+i not in forced or forced[j*m+i]==c) for i,c in enumerate(z)) for z in words])
    for j in range(n-1,-1,-1):
        for u in range(m):
            Gb[j][u]=sum(Gb[j+1][v] for a,v in enumerate(ends[u]) if v>=0 and good[j][a])
        assert Gb[j]==Gd[j*m]
    comparison=Fraction(9,4)
    maxratio=Fraction(0)
    clean=[not any(j*m<=pos<(j+1)*m for pos in forced) for j in range(n)]
    row_tests=0
    for j in range(n):
        vals=np.zeros((m,m,B),dtype=float)
        for u in range(m):
            total=Fraction(0)
            for a,v in enumerate(ends[u]):
                if v<0: continue
                # This is where the current-block chi_j is indispensable.
                q=Fraction(Gb[j+1][v],Gb[j][u]) if good[j][a] and Gb[j][u]>0 else Fraction(0)
                total+=q
                vals[u,v,a]=float(q)
            assert total==int(Gb[j][u]>0)
            row_tests+=1
        masks.append(vals)
        if clean[j] and all(clean[k] for k in range(j+1,min(j+3,n))):
            for u in range(m):
                assert Gb[j][u]>0
                for v in range(m):
                    ratio=Fraction(B*Gb[j+1][v],Gb[j][u])
                    assert ratio<=comparison
                    maxratio=max(maxratio,ratio)
    # Compare actual characteristic functions computed by independent algorithms.
    maxerr=0.0
    for k in [0,1,3,17,B-1,B+7]:
        z=np.zeros(m,dtype=complex);z[0]=1
        for pos in range(N):
            out=np.zeros(m,dtype=complex)
            for u in range(m):
                for digit,v in enumerate(tab[u]):
                    if v>=0 and (pos not in forced or int(forced[pos])==digit):
                        out[v]+=z[u]*np.exp(-2j*np.pi*k*digit/(10**(pos+1)))
            z=out
        direct=z.sum()/Gb[0][0]
        z=np.zeros(m,dtype=complex);z[0]=1
        for j in range(n):
            phase=np.exp(-2j*np.pi*np.arange(B)*k/(B**(j+1)))
            z=z@np.einsum('uva,a->uv',masks[j],phase)
        via_block=z.sum()
        tail=np.exp(-1j*np.pi*k/(10**N))*np.sinc(k/(10**N))
        error=abs((direct-via_block)*tail)
        assert error<1e-10, (w,case,k,error)
        maxerr=max(maxerr,error)
    return {'word':w,'case':case,'horizon_digits':N,'forced_positions':len(forced),
            'conditional_row_checks':row_tests,'max_clean_likelihood_ratio':float(maxratio),
            'proved_likelihood_bound':float(comparison),
            'max_digit_block_fourier_error':maxerr}

def scalar_tail_regression():
    """A real conditioned-word example where scalar tail truncation fails."""
    w = '01'
    m, B, n, k = 2, 100, 3, 50
    tab = transition_table(w)
    words = [f'{a:02d}' for a in range(B)]
    ends = [[follow(tab, u, z) for z in words] for u in range(m)]
    allowed = [[True]*B, [True]*B, [z == '22' for z in words]]
    counts = [[0]*m for _ in range(n+1)]
    counts[n] = [1]*m
    masks = [np.zeros((m, m, B)) for _ in range(n)]
    for j in range(n-1, -1, -1):
        for u in range(m):
            counts[j][u] = sum(counts[j+1][v] for a, v in enumerate(ends[u])
                               if v >= 0 and allowed[j][a])
            for a, v in enumerate(ends[u]):
                if v >= 0 and allowed[j][a] and counts[j][u]:
                    masks[j][u, v, a] = counts[j+1][v]/counts[j][u]
    matrices = [
        np.einsum('uva,a->uv', masks[j],
                  np.exp(-2j*np.pi*np.arange(B)*k/(B**(j+1))))
        for j in range(n)
    ]
    row = np.array([1., 0.]) @ matrices[0]
    scalar = abs(row.sum())
    actual = abs((row @ matrices[1] @ matrices[2]).sum()) * abs(np.sinc(k/B**n))
    row_bound = sum(abs(row))
    assert actual > 10*scalar
    assert actual <= row_bound + 1e-12
    print('scalar-tail regression:', 'truncated_scalar', scalar,
          'actual_coefficient', actual, 'row_l1_bound', row_bound)


if __name__=='__main__':
    scalar_tail_regression()
    results=[run_case(w,case) for w in ('00','01','000','001','010','012') for case in range(3)]
    print('scenarios',len(results),'rows',sum(r['conditional_row_checks'] for r in results),
          'max_error',max(r['max_digit_block_fourier_error'] for r in results))
