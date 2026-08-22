# T125 same-fiber successor coset

Date: 2026-08-22 UTC

Status: `proof sketch`

This note retains one exact sensitivity lemma from the rejected
[Oxzen P2 memo](../../../../workflows/state/runs/t125-centered-portfolio-oxzen-wave-d/work/oxzen-pi-t125-p2-full-composite-defect/MEMO.md),
SHA-256
`7364b9ba603eb664a163ed0db3e6050f63c27b16737a6e5dabf9f42ceeeab09e`.
The run failed its artifact contract, and independent semantic review rejected
the memo's claimed `Outcome: STOP`.  The false STOP is not retained here.

## Exact local hypotheses

Fix a canonical depth `N>=2`.  Suppress the depth subscripts and write

```text
q*S=w*M+R,                 R=center_M(q*S),
d=gcd(q,M),                q'=10*q+144,
M'=16*g*M,
E=160*g*R+2304*g*S+q'*u,
R'=center_(M')(E).
```

Here `q,M,g,S,u` are positive integers, `R,w` are integers, and every center
uses the representative in `[-M/2,M/2)`.  In the canonical application,
`g=g_N`, `u=u_(N+1)`, `M'=M_(N+1)`, and `R'=R_(N+1)`.

Every integer solution in the same depth-`N` fiber with `q,M,R` fixed is

```text
S(t)=S+t*M/d,
w(t)=w+t*q/d                         (t in Z),
```

subject to `S(t)>0`.  Keep `g,u` fixed, extend by
`S_(N+1)(t)=16*g*S(t)+u`, and center the resulting successor phase.  Direct
substitution gives

```text
E(t)=E+144*t*M'/d,
R_(N+1)(t)=center_(M')(E+144*t*M'/d).
```

## Successor-coset classification

Put

```text
m=d/gcd(d,144).
```

Because `d` divides `M`, the step `144*M'/d` is integral.  Its additive order
modulo `M'` is exactly `m`, since

```text
gcd(M',144*M'/d)=(M'/d)*gcd(d,144)=M'/m.
```

Consequently the attainable successor residues are exactly the `m` points

```text
{ E+j*M'/m (mod M') : 0<=j<m }.
```

The positivity restriction does not remove any of these points.  For every
class `j mod m`, one may choose an arbitrarily large integer `t` in that class;
then `S(t)>0`.  Thus all `m` points have positive same-fiber realizations.

Their half-open centered representatives have the following exact geometry.

- If `m=1`, the successor residue at depth `N+1` is rigid under every allowed
  same-fiber replacement.
- If `m=2`, the two successor residues are antipodal.  At least one has
  absolute centered value at most `M'/4`; equality for the nearer choice occurs
  only when the pair is exactly on the two quarter boundaries.  An outer
  successor is also available.  This does not force a strict central hit.
- If `m>=3`, one successor has absolute centered value at most
  `M'/(2*m)<M'/4`, while another successor is in the outer half-circle.  Hence
  both inner and outer successor behavior at depth `N+1` can occur inside the
  same noncanonical fiber.  The first assertion is the nearest-point bound for
  an equally spaced `m`-grid; the second follows because an interval of length
  `M'/2` cannot contain the whole grid when `m>=3`.

## Arbitrary block-length corollary

The classification is not special to one successor.  Fix `L>=1` and write

```text
C_L=16*(10^L-1),
q_end=10^L*q+C_L,
M_end=B*M,
S_end=B*S+U,
```

where the actual block numerator `U` is held fixed.  Propagating the same
depth-`N` fiber replacement gives

```text
S_end(t)=S_end+t*M_end/d,
R_end(t)=center_(M_end)(R_end+t*q_end*M_end/d).
```

Since `q_end` is congruent to `C_L` modulo `d`, the endpoint orbit has exactly

```text
m_L=d/gcd(d,q_end)=d/gcd(d,C_L)
```

equally spaced points modulo `M_end`.  Positivity again removes no class,
because every class of `t mod m_L` has arbitrarily large positive
representatives.  The same rigid (`m_L=1`), antipodal (`m_L=2`), and
inner-and-outer (`m_L>=3`) geometry therefore holds at every fixed block
length.  This extension remains noncanonical: it classifies replacements of
the base numerator while the actual fresh block `U` is frozen.

There is also an exact rigidity progression.  Write

```text
d=2^a*d_odd.
```

The odd factor is coprime to `10`, because `d` divides `q=10^N-16`, which is
odd-prime-to-`5`.  Since `v_2(C_L)=4`, the condition `m_L=1`, equivalently
`d | C_L`, is exactly

```text
a<=4  and  ord_(d_odd)(10) | L.
```

Here `v_2(d)=2,3,8,4` for `N=2,3,4,N>=5`, respectively.  Thus for every fixed
`N != 4`, every positive multiple of `ord_(d_odd)(10)` is a rigid block
length.  For `N=4`, rigidity is impossible and every `m_L` is divisible by
`2^(8-4)=16`.  This arithmetic progression classifies only the noncanonical
fiber orbit; it does not select or constrain the canonical endpoint residue.

## Scope

This is a same-fiber sensitivity statement only.  Except at the original
parameter, the replacements need not be the selected canonical BBP numerator.
The classification therefore shows only what the displayed recurrence permits
after noncanonical phase replacement.  It proves no canonical successor is
inner or outer, closes no canonical mechanism, and is not a `STOP` for T125.
It supplies no canonical return, no fixed-radius progress, no statement about
`(D)`, and no V1 progress.
