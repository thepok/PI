# Canonical carry-tail rigidity target

Define

```text
nu_k=120*k^2+151*k+47
D_k=(2*k+1)*(4*k+3)*(8*k+1)*(8*k+5)
c_k=nu_k/D_k
A_n=sum_(k=0)^n c_k/16^k
R_n=(10^n-16)*A_n
a_n=floor(R_n+1/2)
e_n=R_n-a_n in [-1/2,1/2)
b_n=a_(n+1)-10*a_n in Z.
```

Under the recorded `literature-checked` Furstenberg density input, the accepted
bridge reduces V1 to

```text
liminf_(n->infinity) |e_n|=0.
```

First prove the exact carry-tail identity

```text
10^N*pi = a_N + sum_(r>=0) b_(N+r)/10^(r+1)       (N>=0).
```

Derive it by iterating the carry recurrence and proving
`10^(-L)*R_(N+L)->10^N*pi`; check boundedness and the frozen half-open tie
convention. Deduce that the canonical carry tail cannot be eventually periodic,
because an eventually periodic decimal series is rational whereas pi is
irrational. This exact lemma is only the entry point, not the hard result.

The hard question is:

```text
(AR_eta)  For every eta>0:
          if there exists N0 such that |e_n|>=eta for every n>=N0,
          then there exist p>=1 and N1 such that
          b_(n+p)=b_n for every n>=N1.

(CTR_eta) For every eta>0:
          if there exists N0 such that |e_n|>=eta for every n>=N0,
          then there exists N such that
          sum_(r>=0) b_(N+r)/10^(r+1) is rational.
```

Any positive mechanism must essentially use the full cross-depth numerator.
With `Lambda_n=lcm(D_0,...,D_n)`, the exact unreduced representation is

```text
S_n=sum_(k=0)^n nu_k*16^(n-k)*(Lambda_n/D_k),
A_n=S_n/(16^n*Lambda_n).
```

Prove `(AR_eta)`, prove the explicitly weaker `(CTR_eta)`, or give an exact
obstruction showing why the canonical `S_n` cannot yield either rigidity
statement. A countermodel is relevant only if it preserves the canonical `S_n`
at every depth; finite computation may falsify a proposed lemma but is never
proof evidence.

Strict exclusions: denominator-size or gcd-only estimates; selected-prime or
finite-fiber marginals; endpoint matrix/shear telescoping; the complete product
formula; generic carry-language entropy; modified forcing; noncanonical initial
phases; or claiming finite alphabet implies periodicity. V1 remains open.
