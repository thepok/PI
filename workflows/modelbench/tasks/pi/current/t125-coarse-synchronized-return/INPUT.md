# Canonical T125 target: one coarse synchronized return

For `N>=2`, define the canonical BBP data

```text
nu_k=120*k^2+151*k+47
D_k=(2*k+1)*(4*k+3)*(8*k+1)*(8*k+5)
Lambda_N=lcm(D_0,...,D_N)
S_N=sum_(k=0)^N nu_k*16^(N-k)*(Lambda_N/D_k)
M_N=16^N*Lambda_N
A_N=S_N/M_N
q_N=10^N-16
z_N=||q_N*pi||
```

Here `||x||` is distance to the nearest integer.  For an even positive integer
`M`, let `center_M(t)` be the unique representative of `t mod M` in
`[-M/2,M/2)`.  Then exactly

```text
||q_N*A_N||=|center_(M_N)(q_N*S_N)|/M_N.
```

## Target

Prove the following `conjecture`:

```text
there exist infinitely many N with z_N<1/4.
```

Equivalently, for infinitely many prescribed denominators `q_N`, there is an
integer `m_N` such that

```text
|pi-m_N/q_N|<1/(4*q_N).
```

This fixed-radius target is strictly weaker than
`liminf_N z_N=0`: a sequence can enter `(0,1/4)` infinitely often while
remaining uniformly separated from zero.  It is not a decimal-run statement
and does not imply V1.

## Required reduction, not acceptance

Prove carefully from the positive BBP tail that

```text
|z_N-||q_N*A_N||| <= eps_N,
eps_N=(5/8)^N/(15*(N+1)^2).
```

It therefore suffices to prove at infinitely many unbounded `N` that

```text
|center_(M_N)(q_N*S_N)|/M_N < 1/4-eps_N.
```

The exact reduction and any finite verification are not a result for T125.
Chen--Ye--Zheng gives an infinite omega-limit set and excursions away from
zero for related fixed decimal orbits, but does not locate this orbit inside
the radius-`1/4` neighborhood of zero.

The exact integral depth update is available.  Put

```text
h_N=gcd(Lambda_N,D_(N+1)),
g_N=D_(N+1)/h_N=Lambda_(N+1)/Lambda_N.
```

Then

```text
S_(N+1)=16*g_N*S_N+nu_(N+1)*Lambda_N/h_N.
```

Put

```text
u_(N+1)=nu_(N+1)*Lambda_N/h_N,
q_N*S_N=w_N*M_N+R_N,
R_N=center_(M_N)(q_N*S_N).
```

The exact half-open centered successor is

```text
R_(N+1)=center_(M_(N+1))(
  160*g_N*R_N + 2304*g_N*S_N + q_(N+1)*u_(N+1)),
M_(N+1)=16*g_N*M_N,
q_(N+1)=10*q_N+144.
```

Do not hide the generally nonintegral quantity `Lambda_N/D_(N+1)` inside a
parenthesized expression.  Any claimed arithmetic leverage must use the old
full numerator `S_N` jointly with the fresh integral summand and must depend
essentially on `R_N` or `w_N`.  It must fail under arbitrary same-fiber or
initial-phase replacement.  Any fixed bounded-degree/height expression that,
after division by powers of `M_N`, `q_N`, and `N`, reduces to a continuous
polynomial in `A_N` is only smooth asymptotic bookkeeping and does not qualify.

## Acceptance

Accept only one of:

1. an exact cross-depth argument proving the centered inequality at infinitely
   many `N`, using the selected full numerators `S_N` at unboundedly many
   depths; or
2. an explicit unbounded insertion subsequence and a uniform fresh-term
   transversality or successor-branch exclusion lemma that uses both terms in
   the displayed centered recurrence, depends essentially on `R_N` or `w_N`,
   excludes at least one outer-quarter successor branch, and fails under
   arbitrary same-fiber replacement; or
3. a sharply scoped no-go for a named natural full-`S_N` mechanism, whose
   hypotheses are stated independently of the desired conclusion.

A positive proof must exhibit an explicit cross-depth invariant, sign change,
collective congruence, or auxiliary integer and prove the nontrivial bound that
forces the centered ratio below `1/4`.  State every quantifier and half-open
endpoint.

Strict exclusions: denominator magnitude, gcd growth, or valuations alone;
isolated-prime and finite-fiber marginals; generic DFT or energy bounds;
endpoint telescoping; product-formula identities; an affine form made trivial
by imposing a zero constant term; generic carry language; noncanonical or
modified forcing; finite experiments as proof; generic one-step branch measure,
exact-orbit injectivity, or irrational-orbit counterexamples; decimal-run
translations; smooth fixed-polynomial asymptotics of `A_N`; and
any statement equivalent to `liminf_N z_N=0`.  V1 remains open.
