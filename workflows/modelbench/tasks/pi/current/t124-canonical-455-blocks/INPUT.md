# Canonical 455-block target

Define the canonical BBP data

```text
nu_k=120*k^2+151*k+47
D_k=(2*k+1)*(4*k+3)*(8*k+1)*(8*k+5)
A_n=sum_(k=0)^n (nu_k/D_k)/16^k
R_n=(10^n-16)*A_n=a_n+e_n
a_n=floor(R_n+1/2),  e_n in [-1/2,1/2)
b_n=a_(n+1)-10*a_n.
```

Let

```text
L_455(N)=max{L>=0 : b_(N+r)=455 for every 0<=r<L}.
```

This maximum is finite and well-defined: `L=0` always qualifies, while T123's
proved non-eventual-periodicity excludes a tail that is constantly `455`.

The accepted T122 separator gives a noncanonical bounded solution of the same
actual first-order forcing whose carry is `455` forever. Therefore this task
must distinguish the canonical rational phase.

First prove the exact shadowing lemma. If `N>=2` and `L<=L_455(N)`, then
comparison with the bounded `455` solution gives

```text
|10^N*pi-a_N-455/9| < 10^(-L).
```

Derive it directly from the two first-order recurrences, including the
half-open centered bounds and all endpoint indices. Explain why the known
irrationality measure of pi yields only a linear upper bound for `L_455(N)`.
This entry lemma and the linear bound are not sufficient progress.

The hard target is the narrower canonical quantitative statement

```text
for every eps>0, there exists N0 such that for every N>=N0,
L_455(N)<=eps*N.
```

This question is currently incomparable with `(D)` and V1 and is not
sufficient for either: controlling one carry word does not force returns, while
`(D)` alone supplies no quantitative bound on gaps between returns.

Any positive proof must essentially use the selected full numerator across
depth. With `Lambda_n=lcm(D_0,...,D_n)`, use

```text
S_n=sum_(k=0)^n nu_k*16^(n-k)*(Lambda_n/D_k),
A_n=S_n/(16^n*Lambda_n),
```

or an exactly equivalent reduced cross-index numerator. Prove the sublinear
bound, prove a concrete asymptotic improvement over the existing linear
irrationality-measure exponent, or give an exact obstruction explaining why
the canonical `S_n` arithmetic cannot improve that exponent.

Strict exclusions: merely rederiving the shadowing identity or a linear bound;
denominator-size/gcd-only estimates; isolated-prime or finite-fiber marginals;
endpoint matrix telescoping; product-formula identities; generic carry
languages; modified forcing; noncanonical phases; finite experiments as proof;
or any all-eta implication equivalent to `(D)`. V1 remains open.
