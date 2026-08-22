# T125 endpoint Cramer-resultant no-go

Date: 2026-08-22 UTC

Status: `proof sketch`

Provenance: ChatGPT Pro model answer
[`workflows/state/chatgpt-pro/t125-block-arithmetic-pro-20260822/answer.md`](../../../../workflows/state/chatgpt-pro/t125-block-arithmetic-pro-20260822/answer.md),
SHA-256
`e7485748cdbaee1f111fd61a221bff1ae55856940e21118e683476beef10e752`.
Independent audit found that the source used a nonprimitive full-modulus
multiple when describing the whole resultant module.  The statement below
includes the required primitive normalization and does not retain that
overclaim.

## Exact block notation

For every canonical depth `N>=2` and block length `L>=1`, put

```text
a=10^L,
G=product_(i=0)^(L-1) g_(N+i)=Lambda_(N+L)/Lambda_N,
B=16^L*G=M_(N+L)/M_N,
c=16*(a-1),
q=q_N,        M=M_N,        S=S_N,        w=w_N,        R=R_N,
q'=q_(N+L),  M'=M_(N+L),                            R'=R_(N+L),
U=sum_(i=1)^L 16^(L-i)*(product_(t=i)^(L-1) g_(N+t))*u_(N+i),
K=w_(N+L)-a*w_N.
```

Empty products equal one.  Iteration of the exact integral recurrence gives

```text
q'=a*q+c,       M'=B*M,       S_(N+L)=B*S+U.
```

The two endpoint equations are

```text
q*S-M*w=R,
q'*B*S-a*M'*w=R'-q'*U+M'*K.
```

## Primitive rank-one resultant

An integer row combination `(lambda,mu)` eliminates `S` exactly when
`lambda*q+mu*q'*B=0`.  With

```text
gamma=gcd(q,q'*B),
```

all such pairs are the integer multiples of the primitive pair

```text
(q'*B/gamma,-q/gamma).
```

Define the unscaled identity and its primitive generator by

```text
J =q'*(B*R+q*U)-q*R'=M'*(q*K-c*w),
J0=J/gamma.
```

The primitive row combination proves `J0` is an integer.  To retain its exact
forced divisor, put

```text
eta=gcd(gamma,M'),       M0=M'/eta.
```

Writing `gamma=eta*gamma_1` and `M'=eta*M0`, with
`gcd(gamma_1,M0)=1`, the equality `J=M'*(q*K-c*w)` implies
`gamma_1 | (q*K-c*w)`.  Hence

```text
M0 | J0.
```

This `M0`, not the source answer's unscaled full `M'`, is the divisor attached
to the primitive generator of the rank-one module.

## Strict obstruction bounds

Let

```text
r=R/M,       r'=R'/M',       tau=U/M'=A_(N+L)-A_N,
eps_N=(5/8)^N/(15*(N+1)^2).
```

Positivity of the BBP tail gives, uniformly in `L`,

```text
0<q*tau<q*(pi-A_N)<eps_N.
```

Also

```text
J/M'=q'*r-q*r'+q*q'*tau,       |r'|<=1/2.
```

If the initial endpoint is in the fixed-margin avoidance annulus

```text
|R|/M >= 1/4-eps_N,
```

then `eps_N<=5/1728`, `q>=84`, and `q'>10*q` give

```text
|J|/M' > q*(839/432).
```

Since `gamma<=q` and `eta>=1`, the primitive divisor ratio satisfies

```text
|J0|/M0=(eta/gamma)*|J|/M' > 839/432 > 1.
```

Under the stronger outer-quarter hypothesis `|R|/M>=1/4`, the corresponding
strict bounds are

```text
|J|/M' > q*(1703/864),
|J0|/M0 > 1703/864 > 1.
```

Thus neither the primitive endpoint resultant nor any nonzero integer multiple
of it can furnish a nonzero integer strictly smaller than its forced divisor
on either stated avoidance class.

## Integral 12-gauge boundary

For every `n>=2`, both `q_n` and `M_n` are divisible by 12.  For any fixed
integer `m>=0`, define along the whole future tail

```text
S~_n=S_n+m*M_n/12,
w~_n=w_n+m*q_n/12.
```

These are positive integral states and satisfy

```text
q_n*S~_n=w~_n*M_n+R_n,
S~_(n+1)=16*g_n*S~_n+u_(n+1).
```

Therefore every intermediate half-open remainder is unchanged.  For every
block, `U~_(N,L)=U_(N,L)`, while

```text
K~_(N,L)=K_(N,L)+m*c/12.
```

It follows that `q*K~-c*w~=q*K-c*w`; consequently `J`, `J0`, and every
outer/inner status in the block are preserved.  This is an infinite
noncanonical gauge family: it changes `S_n/M_n` by `m/12` and therefore does
not preserve the selected canonical BBP partial sum.

For `L=1`, one has `a=10`, `B=16*g_N`, `c=144`, `U=u_(N+1)`, and `K=k_N`.
The block identity then specializes exactly to the known P2 identity

```text
M_(N+1)*(q_N*k_N-144*w_N)
 =q_(N+1)*(16*g_N*R_N+q_N*u_(N+1))-q_N*R_(N+1).
```

The separate same-fiber successor-coset classification is recorded in
[`20260822-t125-same-fiber-successor-coset.md`](../intermediate/20260822-t125-same-fiber-successor-coset.md).

## Exact scope

This no-go closes only integer linear combinations of the two block endpoint
equations that eliminate the common prefix numerator `S_N`.  It does not cover
determinants or inequalities retaining `S_N`, the individual fresh BBP
summands or intermediate quotients, nonlinear centered or modular auxiliaries,
or any argument selecting the canonical row against the 12-gauge family.  The
gauge is a noncanonical sensitivity test, not canonical information, and its
lesson overlaps the initial-phase freedom already recorded at T122.

No return is produced or excluded for the canonical sequence.  This is not
canonical progress toward T125, proves no `(D)`, and gives no V1 progress.  No
novelty or literature claim is made.
