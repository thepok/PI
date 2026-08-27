# T127 three-depth exterior gauge shear

Date: 2026-08-22 UTC

Status: `proof sketch`

Provenance: ChatGPT Pro model answer
[`workflows/state/chatgpt-pro/t127-three-depth-gauge-curvature-pro-20260822/answer.md`](../../../../workflows/state/chatgpt-pro/t127-three-depth-gauge-curvature-pro-20260822/answer.md),
SHA-256
`1c7113094156f8ecfb9d28697b885a243ce440ed40b1bd204a8d4949006c4132`.
The statement below is the independently audited algebraic salvage, not the
source answer's broader no-go claim.

## Three-depth row reduction

Fix `n>=2` and write the data at depths `n,n+1,n+2` as rows

```text
X_i=(S_i,M_i,w_i,q_i),                 i=0,1,2.
```

Put `S=S_0`, `M=M_0`, `w=w_0`, `q=q_0`,

```text
a=M_1/M=16*g_n,       b=M_2/M_1=16*g_(n+1),
u=S_1-a*S,            v=S_2-b*S_1,
p_1=w_1-a*w,          p_2=w_2-b*w_1,
r_1=q_1-a*q,          r_2=q_2-b*q_1.
```

Here `u=u_(n+1)>0` and `v=u_(n+2)>0` are the two separate actual fresh BBP
numerators.  The determinant-one row reduction is

```text
X_0                  = (S,M,w,q),
X_1-a*X_0            = (u,0,p_1,r_1),
X_2-b*X_1            = (v,0,p_2,r_2).
```

Define

```text
AA=u*r_2-v*r_1,
BB=u*p_2-v*p_1,
CC=p_1*r_2-p_2*r_1.
```

In the indicated column order, its four `3 x 3` minors are exactly

```text
P_1=P_(S,M,w)=-M*BB,
P_2=P_(S,M,q)=-M*AA,
P_3=P_(S,w,q)=S*CC-w*AA+q*BB,
P_4=P_(M,w,q)=M*CC.
```

## Exact residue eliminations

The endpoint equations first give

```text
R_1=a*r_1*S+a^2*R_0-a*M*p_1+q_1*u,
R_2=b*r_2*(a*S+u)+b^2*R_1-a*b*M*p_2+q_2*v.
```

Eliminating `p_1,p_2`, while retaining `u,v` separately, yields

```text
M_2*BB
 = a*b*AA*S + b*r_2*u^2 + r_2*u*v
   - b*a^2*v*R_0 + b^2*u*R_1 + b*v*R_1 - u*R_2,

M_2*CC
 = a^2*b*r_2*R_0 - b*(r_2+b*r_1)*R_1 + r_1*R_2
   + a*b*q*r_2*u - r_1*q_2*v.
```

These are exact integer identities; they make no distribution or
nonvanishing assertion.

## Positive propagated gauge and shear

Let `d=gcd(q,M)` and `c=gcd(d,144)`.  Preservation at depth `n+1` is equivalent
to `d | 144*t`, and this condition preserves every later centered remainder as
well.  Writing `t=(d/c)*m`, the propagated gauge is

```text
S_i(m)=S_i+(m/c)*M_i,
w_i(m)=w_i+(m/c)*q_i,                  i=0,1,2.
```

All displayed values are integral because `c` divides every relevant `M_i`
and `q_i`.  The admissible integers `m` are those for which the shifted
numerators remain positive.  They form a lower-bounded half-line containing
all sufficiently large positive integers; they are not a two-sided unbounded
family.

The fresh terms and all three centered remainders stay fixed, while

```text
p_j(m)=p_j+(m/c)*r_j,                  j=1,2,
AA(m)=AA,       CC(m)=CC,       BB(m)=BB+(m/c)*AA.
```

Consequently the exterior coordinates undergo the exact shear

```text
P_1(m)=P_1+(m/c)*P_2,       P_2(m)=P_2,
P_3(m)=P_3+(m/c)*P_4,       P_4(m)=P_4.
```

## Narrow affine-orbit theorem

Let

```text
J=rho+alpha*P_1+beta*P_2+gamma*P_3+delta*P_4,
```

where all five coefficients are integer-valued and invariant under the
displayed gauge.  Then

```text
J(m)=J(0)+(m*M/c)*(gamma*CC-alpha*AA).
```

If the slope vanishes, `J` is gauge invariant.  This includes the invariant
combination

```text
CC*P_1+AA*P_3=(P_4*P_1-P_2*P_3)/M,
```

whose possible arithmetic use remains open.  If the slope is nonzero, then
`|J(m)|` is unbounded as admissible `m` tends to positive infinity.  Therefore
such a gauge-sensitive affine form cannot obey a uniform finite absolute bound
whose bound data are themselves gauge invariant and whose quantifiers cover
the entire positive same-fiber family.

## Scope

This does not establish a maximal invariant ring or a maximal natural class.
It does not give opposite signs on the admissible half-line and does not rule
out a fixed-sign law.  It does not address a theorem restricted to the
canonical selector `m=0`, a divisor or bound that changes with the gauge,
nonlinear or nonpolynomial constructions, or a proof using independent
canonical arithmetic.  The gauge family is noncanonical, so this is not
canonical progress toward T125 or `(D)`, and it gives no V1 progress.  No
novelty or literature claim is made.
