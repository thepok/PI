# Central carrier and annular flux

Date: 2026-08-28 UTC

Claim label: universal identities and inequalities are `proof sketch`
(independently audited); the fixed hard-node values are an `experiment`.
This isolates a new positive central-carrier mechanism, but does not prove an
unbounded actual-π shell or endpoint estimate.

## Exact literal refinement carrier

For the T128 boundary kernel define

```text
Phi_m(y)=kappa_m(y/m).
```

Direct factorization gives

```text
Phi_m(y)=Lambda(y)*R_m(y),

Lambda(y)=(pi^2/2)*(1-4*y^2)*(sin(pi*y)/(pi*y))^4,

R_m(y)=sinc(pi*(1+2*y)/(2*m))*sinc(pi*(1-2*y)/(2*m))
       /sinc(pi*y/m)^4.
```

The power series for `log sinc` proves, for every integer `b>=1`, `m>=2`,
and `|y|<=1/2`,

```text
0 <= Phi_m(y) <= Phi_(b*m)(y) <= Lambda(y).
```

The inequalities are strict for `b>1` and `|y|<1/2`.  If an actual-π suffix
lies in the interior of the parent cylinder and
`y=q*(x_(n+1)-c_(q,A))`, its literal predecessor child keeps exactly this
normalized radius and receives `Phi_(10q)(y)>=Phi_q(y)>0`; every sibling is
nonpositive.  Interior membership is essential at the abstract level; π's
irrationality excludes rational cylinder endpoints.

## The carrier pays its local siblings

For the ten child kernels `K_d(a,s)` and

```text
b_q=1-cos(pi/(10*q)),
a_q=1-cos(pi/q),
delta_q=100*b_q-a_q,
```

root-of-unity summation gives exactly

```text
sum_(d<10) K_d(a,s)-kappa_q(s)
 = sin(pi*q*s)^4/(q^2*sin(pi*s)^4)
   *(delta_q-66*b_q*sin(pi*s)^2).
```

Elementary directed cosine bounds show that, for `q>=1000` and `|y|<=0.35`,

```text
0 <= -sum_(d != a) K_d(a,y/q)
     <= Phi_(10q)(y)-Phi_q(y).
```

Thus the refinement gain of one sufficiently central literal occurrence pays
the complete negative mass sent to all nine siblings.  The analogous
ten-point DFT estimate retains all five real character blocks: after
dephasing by the named predecessor digit, every sector lies within the same
refinement-gain radius of the literal one-hot carrier.

This monotonicity cannot be extended through the sign boundary.  It reverses
immediately outside `|y|=1/2`.  The useful universal exterior estimate is

```text
0 <= -Phi_m(y)
  <= pi^2*(4*y^2-1)*sin(pi*y)^4/(32*y^4)
  <= pi^2/(8*y^2),       1/2<|y|<=m/2.
```

Consequently, if `B_n=floor(m*x_n)` and `rho_m(B_n,C)` is circular label
distance, the total negative lobe at target `C` is bounded by the weighted
near-miss count

```text
N_(m,C)(W)
 <= (pi^2/8)*sum_(j>=1)
      #{n in W: rho_m(B_n,C)=j}/(j-1/2)^2.
```

Generic occupancy does not sign or sufficiently sharpen this target-specific
quantity.

## Exact carrier/remainder split

T174 splits each normalized signed surplus exactly into positive cylinder
mass, negative-lobe mass, primitive-shift endpoint, zero coefficient, and the
registered potential.  Applying that split separately to parent, old-child,
and fresh-child windows yields exact core vectors

```text
g_d^circ, d_d^circ, f_d^circ=g_d^circ+d_d^circ
```

built from positive cylinder masses and exact zero/potential terms, plus
signed remainder vectors `a_d,b_d,c_d` containing negative lobes and
endpoints.  For the **actual** sign sets

```text
P={d:D_d>0 and F_d>0},
O={d:D_d*F_d<0},
```

one obtains exactly

```text
J0/q^2 = Jcirc-C,

Jcirc=sum_(d in P) d_d^circ*f_d^circ
      -(1/4)*sum_(d in O)(g_d^circ)^2.
```

Here `C` is the explicit expansion remainder from the negative-lobe and
endpoint vectors.  It is signed, not universally a nonnegative flux.  Also,
`Jcirc` is not determined by positive occurrences alone because its index sets
`P,O` come from the complete actual scores.

## Hard-node result and exact remaining boundary

At `(q,A)=(10000,1334)`, the pinned π prefix has exactly two old parent
occurrences, with normalized radii in `(0.2574,0.2575)` and
`(0.1776,0.1777)`, and the unique relevant fresh child-`5` occurrence has
radius in `(-0.0977,-0.0976)`.  All lie in the sibling-payment region.  The
existing outward replay supplies the actual sign sets `P={5}`, `O={8}`.
Independent recomputation gives

```text
Jcirc ~= 55.600526,
```

and conservative analytic bounds support `Jcirc>54.4563`.  Because the
endpoint monotonicity used in those conservative substitutions was not itself
certified by a directed evaluator, retain the numerical statement as an
`experiment`, not a theorem.  The actual value satisfies

```text
J0/q^2 ~= 17.27272354,
C ~= 38.32780002.
```

The new carrier mechanism therefore explains a large positive core at the
hard node; accumulated target-specific annular mass and primitive endpoints
consume most of it.

At a fixed node the exact remaining inequality is `Jcirc>C`.  An all-scale
route must additionally construct the growing-horizon path, prove recurring
`Jcirc>0`, control the changing sign sets, and eventually supply word
coverage.  Reopen this route only with an actual-π weighted near-miss and
endpoint theorem strong enough for those literal recursively reached targets;
further kernel algebra or generic occupancy is not progress.
