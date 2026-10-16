#!/usr/bin/env python3
"""Falsification audit for the failure-tree Fourier bound (standard library).

Combinatorial identities and threshold comparisons use exact integers.
Shifted Dirichlet samples use floating point and are experiments only.
"""
from fractions import Fraction
from itertools import product
from math import factorial, log, pi, sin


def failure_parents(word):
    return [-1] + [
        max(k for k in range(t) if k == 0 or word[t-k:t] == word[:k])
        for t in range(1, len(word))
    ]


def transitions(base, word):
    result = []
    m = len(word)
    for state in range(m):
        row = []
        for digit in range(base):
            tail = word[:state] + (digit,)
            if len(tail) >= m and tail[-m:] == word:
                row.append(-1)
            else:
                row.append(max(k for k in range(min(m-1, len(tail))+1)
                               if k == 0 or tail[-k:] == word[:k]))
        result.append(row)
    return result


def forbidden_prefixes(word, state):
    m = len(word)
    possibilities = []
    for r in range(1, m+1):
        overlap = m-r
        if overlap <= state and (overlap == 0 or word[state-overlap:state] == word[:overlap]):
            possibilities.append(word[overlap:])
    return [p for p in possibilities
            if not any(len(q) < len(p) and p[:len(q)] == q for q in possibilities)]


def audit_autocorrelation(base, word, table):
    """Compare overlap counts with independent first-hit automaton counts."""
    m = len(word)
    counts = [1] + [0]*(m-1)
    avoiding, first_hit = [1], [0]
    for n in range(1, 3*m+1):
        following = [0]*m
        rejected = 0
        for state, count in enumerate(counts):
            for target in table[state]:
                if target < 0:
                    rejected += count
                else:
                    following[target] += count
        counts = following
        avoiding.append(sum(counts))
        first_hit.append(rejected)
        assert rejected == base*avoiding[n-1]-avoiding[n]
    overlaps = [d for d in range(m) if word[d:] == word[:m-d]]
    for n in range(2*m+1):
        assert avoiding[n] == sum(first_hit[n+m-d] for d in overlaps)
    return 2*m+1


def audit_family(base, m):
    words = blocks = initial_checks = correlation_checks = 0
    all_blocks = list(product(range(base), repeat=m))
    for word in product(range(base), repeat=m):
        parents = failure_parents(word)
        table = transitions(base, word)
        correlation_checks += audit_autocorrelation(base, word, table)
        forbidden = [forbidden_prefixes(word, state) for state in range(m)]
        assert len(parents) + sum(p >= 0 for p in parents) == 2*m-1
        for family in forbidden:
            assert len({len(p) for p in family}) == len(family)
            assert all(not (len(p) <= len(q) and q[:len(p)] == p)
                       for i,p in enumerate(family) for j,q in enumerate(family) if i != j)
        for block in all_blocks:
            suffixes = [t for t in range(m) if t == 0 or block[-t:] == word[:t]]
            terminal = max(suffixes)
            expanded = [0]*m
            for t in suffixes:
                expanded[t] += 1
                if t:
                    expanded[parents[t]] -= 1
            assert expanded == [int(v == terminal) for v in range(m)]
            for state in range(m):
                current = state
                for digit in block:
                    current = table[current][digit]
                    if current < 0:
                        break
                survives = not any(block[:len(p)] == p for p in forbidden[state])
                assert survives == (current >= 0)
                if survives:
                    assert current == terminal
                initial_checks += 1
            blocks += 1
        words += 1
    return words, blocks, initial_checks, correlation_checks


def audit_counting_and_threshold():
    for m in range(2, 100):
        weights = [1] + [2]*(m-1)
        total = sum(weights[t] for r in range(m+1) for t in range(m))
        positive = sum(weights[t] for r in range(m+1) for t in range(m) if r+t<m)
        free_length = sum(weights[t]*max(m-r-t,0) for r in range(m+1) for t in range(m))
        assert total == (m+1)*(2*m-1)
        assert positive == m*m
        assert free_length == m*(m+1)*(2*m+1)//6
    x = Fraction(7, 3)
    assert sum(x**k / factorial(k) for k in range(12)) > 10
    gamma = lambda m: Fraction(10001,10000)*Fraction(14*m**3+129*m*m+34*m-27, 27)
    assert 10001*24 < 10*9**23
    assert gamma(24) == Fraction(895519543,90000)
    assert gamma(24) < 10**4
    assert all(gamma(m)**6 >= 10**m for m in range(2,24))
    m,r = 24,20000
    # A small-integer certificate for [8*10^23*gamma(24)^20000]^6
    # <10^480000: do not construct the million-digit intermediate powers.
    assert gamma(m)/10**4 < Fraction(249,250)
    assert Fraction(250,249)**250 >= 1+Fraction(250,249) > 2
    assert Fraction(249,250)**250 < Fraction(1,2)
    assert r == 250*80
    assert 8*10**23 < 2**80
    assert gamma(m) > m
    assert m**2 > 2+6*m
    assert 8*10**(m-1) < 10**m
    return gamma(24)


def audit_dirichlet_samples():
    comparisons, worst_ratio = 0, 0.0
    for n,q in ((1,10),(2,16),(8,64),(10,100),(27,729),(100,1000),(256,4096)):
        for shift in (0.0,0.03125,0.125,0.375,0.5,0.9375):
            actual = 0.0
            for j in range(q):
                angle = (j+shift)/q
                denominator = sin(pi*angle)
                actual += n if abs(denominator)<1e-14 else abs(sin(pi*n*angle)/denominator)
            actual /= q
            bound = 1.0 if n == 1 else 3.0 + (2.0/3.0)*log(n)
            assert actual <= bound + 1e-10
            worst_ratio = max(worst_ratio,actual/bound)
            comparisons += 1
    return comparisons,worst_ratio


def main():
    totals = [0,0,0,0]
    for base,m in [(2,m) for m in range(2,9)] + [(3,m) for m in range(2,6)] + [(10,2),(10,3)]:
        result = audit_family(base,m)
        totals = [a+b for a,b in zip(totals,result)]
        print(f"PASS combinatorics: base={base}, length={m}, words={result[0]}, blocks={result[1]}, state checks={result[2]}", flush=True)
    gamma = audit_counting_and_threshold()
    samples,ratio = audit_dirichlet_samples()
    print(f"PASS totals: {totals[0]} words; {totals[1]} exact suffix-vector identities; {totals[2]} initial-state survival/terminal checks.")
    print(f"PASS {totals[3]} exact first-occurrence/autocorrelation identities.")
    print(f"PASS exact threshold: G_24={gamma}<10^4; m=24,r=20000 small-integer macroblock certificate.")
    print("PASS exact ln(10)<7/3 certificate and weighted-term identities for 2<=m<=99.")
    print(f"PASS {samples} sampled shifted Dirichlet bounds; largest sampled actual/bound={ratio:.9g}.")
    print("Status: experiment; exact identities are finite checks, not a proof of the general theorem.")


if __name__ == "__main__":
    main()

