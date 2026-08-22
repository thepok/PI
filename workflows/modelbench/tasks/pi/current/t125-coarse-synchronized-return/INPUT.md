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

## Acceptance

Accept only one of:

1. an exact cross-depth argument proving the centered inequality at infinitely
   many `N`, using the selected full numerators `S_N` at unboundedly many
   depths; or
2. a sharply scoped no-go for a named natural full-`S_N` mechanism, whose
   hypotheses are stated independently of the desired conclusion.

A positive proof must exhibit an explicit cross-depth invariant, sign change,
collective congruence, or auxiliary integer and prove the nontrivial bound that
forces the centered ratio below `1/4`.  State every quantifier and half-open
endpoint.

Strict exclusions: denominator magnitude, gcd growth, or valuations alone;
isolated-prime and finite-fiber marginals; generic DFT or energy bounds;
endpoint telescoping; product-formula identities; an affine form made trivial
by imposing a zero constant term; generic carry language; noncanonical or
modified forcing; finite experiments as proof; decimal-run translations; and
any statement equivalent to `liminf_N z_N=0`.  V1 remains open.
