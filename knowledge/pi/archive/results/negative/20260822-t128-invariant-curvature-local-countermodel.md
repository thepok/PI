# T128: invariant quadratic curvature has an exact local outer countermodel

Date: 2026-08-22 UTC

Status: `proof sketch`

Pro provenance:
`workflows/state/chatgpt-pro/t128-primitive-curvature-pro-20260822/answer.md`,
SHA-256
`6c41773a9f95f51cab6e4f0278169d551e0ba63ac69e660591146cf2a3fa6867`.
The Pro browser completed cleanly in Pro mode and closed without intervention.
Three independent audits recomputed the algebra and accepted the result only
with the local-versus-canonical scope firewall below.

## Three-depth data

Fix `n>=2`, abbreviate `M=M_n`, `S=S_n`, `q=q_n`, `R=R_n`, and put

```text
M_(n+1)=aM,                  M_(n+2)=abM,
S_(n+1)=aS+u,               S_(n+2)=abS+bu+v,
p1=w_(n+1)-a*w_n,           p2=w_(n+2)-b*w_(n+1),
r1=q_(n+1)-a*q_n,           r2=q_(n+2)-b*q_(n+1),
AA=u*r2-v*r1,               BB=u*p2-v*p1,
CC=p1*r2-p2*r1,             H=q*AA-M*CC.
```

For the four three-depth minors from T127, the gauge-invariant curvature is

```text
Q=CC*P1+AA*P3=(P4*P1-P2*P3)/M.
```

## Exact residue cancellation

Subtracting the consecutive centering equations gives

```text
aM*p1  = a*r1*S + q_(n+1)*u - R_(n+1) + a^2*R,
abM*p2 = ab*r2*S + b*r2*u + q_(n+2)*v
          - R_(n+2) + b^2*R_(n+1).
```

Eliminating `p1,p2` yields

```text
abM*BB=ab*AA*S+E,
```

where

```text
E=b*r2*u^2+r2*u*v-b*a^2*v*R
  +(b^2*u+b*v)*R_(n+1)-u*R_(n+2).
```

Using `M*w=q*S-R` in the definition of `Q` then gives the exact identity

```text
abM*Q=ab*AA^2*R+H*E.                         (1)
```

This confirms that the apparent dependence on the base numerator cancels to
an affine integer form in the three residues.

## Primitive content

Expanding the right side of (1), its constant and three residue coefficients
are

```text
H*r2*u*(b*u+v),
ab*AA^2-b*a^2*v*H,
H*b*(b*u+v),
-H*u.
```

Since

```text
gcd(r2*u*(b*u+v), b*(b*u+v), u)=gcd(u,b*v),
```

their exact nonnegative content is

```text
g=gcd(ab*AA^2, H*gcd(u,b*v)).                 (2)
```

For `g>0`, divide the affine form by `g` to obtain the content-one form
`phi`.  Put

```text
c=gcd(abM,g),    Delta=abM/c,    kappa=g/c.
```

Then `gcd(Delta,kappa)=1`, and (1) is exactly

```text
kappa*phi=Delta*Q,
Delta | phi,                    kappa | Q.     (3)
```

The intersection factor `c` is essential: the primitive divisor is not in
general `abM/g`.  If `g=0`, then `AA=H=CC=0` and `Q=0`, so the curvature is
degenerate rather than obstructive.

## Cofinite integral outer countermodel

For every `n>=50`, retain the actual canonical coefficient tuple
`(a,b,M_j,q_j,u,v,r1,r2)` but choose a separate integral entry phase.  For
`j in {n,n+1,n+2}`, define

```text
m_j=10^j/64,
T_n=0,                 T_(n+1)=u,              T_(n+2)=b*u+v,
S~_j=63*M_j/64+T_j,
w~_j=63*m_j-16,
R~_j=M_j/4+q_j*T_j.
```

All quantities are integral.  The base identity

```text
q_j*(63*M_j/64)=(63*m_j-16)*M_j+M_j/4
```

proves the three exact centering equations

```text
q_j*S~_j=w~_j*M_j+R~_j.
```

The choices of `T_j` also give the exact inhomogeneous recurrences

```text
S~_(n+1)=a*S~_n+u,
S~_(n+2)=b*S~_(n+1)+v.
```

The elementary coefficient bounds

```text
nu_k/D_k < 5/(8*k^2),       q_k/16^k < (5/8)^k
```

give

```text
0 < q_(n+1)*u/M_(n+1) < (5/8)^(n+2)/(n+1)^2 < 1/4,

0 < q_(n+2)*(b*u+v)/M_(n+2)
  < 10*(5/8)^(n+2)/(n+1)^2+(5/8)^(n+3)/(n+2)^2
  < 10/51^2+1/52^2 < 1/4.
```

Therefore all three are their unique half-open centered representatives and

```text
M_j/4 <= R~_j < M_j/2,
```

with equality at the lower boundary only at depth `n`.  Thus the strict target
`|R_j|/M_j < 1/4-eps_j` fails at all three depths.

## Nondegeneracy of the selected coefficients

The countermodel is not supported by a zero `AA`.  Put `j=n+1`,

```text
alpha=Lambda_j/Lambda_(j-1),      beta=Lambda_(j+1)/Lambda_j,
X=nu_j*D_(j+1),                   Y=beta*nu_(j+1)*D_j.
```

An exact common-denominator expansion is

```text
AA=Lambda_j/(D_j*D_(j+1)) * (10^n*A+16*B),
A=(100-160*beta)*X+(16*alpha-10)*Y,
B=(16*beta-1)*X+(1-16*alpha)*Y.
```

Simultaneous `A=B=0` would imply

```text
128*alpha*beta-88*alpha+5=0,
```

which is impossible for positive integers `alpha,beta`.  The elementary
bounds `alpha<=D_j`, `beta<=D_(j+1)` give

```text
16*|B| < 10^17*(n+1)^14 < 10^n             (n>=50).
```

Hence either the `10^n*A` term dominates or `A=0,B!=0`; in both cases
`AA!=0`.

Recomputing `p1,p2,CC,H,Q` from the constructed integral state satisfies (1),
(2), and the primitive split (3).  Explicitly, if

```text
L0=(a-1)*r2-(b-1)*r1,
K0=(b-1)*u-(a-1)*v,
```

then

```text
CC~=L0/4,
BB~=63*AA/64+K0/4,
H~=q*AA-M*L0/4,
E~=abM*K0/4,
Q~=(AA^2+H~*K0)/4 in Z.
```

Thus this is an exact integral three-depth state satisfying the universal curvature
identity and its state-specific primitive divisibility, not a free real-box
example, a tautological divisibility, or a residue-preserving gauge ray.

## Exact scope of the no-go

The construction preserves the actual local coefficient data, fresh terms,
two numerator recurrences, and three centered equations.  It proves that no
universal local implication from those data plus the curvature identity and
primitive split recomputed at the candidate state can force a strict
three-depth return.

It does **not** preserve the canonical finite-sum numerator `S_n`, the
canonical quotient increments `p1,p2`, or the numerical canonical values of
`CC,H,Q,g,Delta,kappa`.  It therefore does not close an argument using a new
canonical-specific sign, valuation, divisor, selector, or global-prefix
property.  In particular this is not an absolute STOP for every use of the
canonical curvature.

The retained conclusion is only a local structural no-go for the most natural
gauge-invariant quadratic curvature.  It gives no canonical return, no T125 or
`(D)` progress, and no V1 progress.

V1 remains open.
