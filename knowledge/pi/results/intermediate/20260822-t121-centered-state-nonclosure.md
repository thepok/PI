# T121 exact centered update and pair-state nonclosure

Date: 2026-08-22 UTC

Status: `proof sketch`

## Exact update

Let

```text
A_N=P_N/Q_N,  gcd(P_N,Q_N)=1,  Q_N>0,
t_N=10^N-16,
Delta_N=center_(Q_N)(t_N*P_N),
```

where `center_m(z)=z-m*floor(z/m+1/2)` fixes the half-tie convention and
`|Delta_N|/Q_N=||(10^N-16)A_N||`.  Reduce the next BBP increment as

```text
A_(N+1)-A_N=u_N/v_N,  gcd(u_N,v_N)=1,  v_N>0,
X_N=P_N*v_N+u_N*Q_N,
Y_N=Q_N*v_N,
h_N=gcd(abs(X_N),Y_N).
```

Then `P_(N+1)=X_N/h_N`, `Q_(N+1)=Y_N/h_N`, and direct expansion using
`t_(N+1)=10*t_N+144` gives

```text
h_N*Delta_(N+1)
  = center_(Y_N)(10*v_N*Delta_N
                 +144*v_N*P_N
                 +t_(N+1)*u_N*Q_N).
```

The identity was independently reviewed algebraically.  A deterministic
exhaustive replay over 101528 small signed rational updates also matched both
sides, but that replay is only `experiment` evidence.

## Pair-state nonclosure

The compressed pair `(Delta_N,Q_N)` determines only

```text
t_N*P_N = Delta_N (mod Q_N).
```

Writing `d_N=gcd(t_N,Q_N)`, this congruence is solvable exactly when `d_N`
divides `Delta_N`; its unrestricted solution set modulo `Q_N` then has
`d_N` elements.  Reducedness can remove lifts but need not select one.

An exact witness uses the actual `N=2` BBP increment
`u_2/v_2=79/15590400`.  Here `t_2=84`.  The two reduced inputs `1/3` and
`2/3` have the identical compressed pair `(Delta_2,Q_2)=(0,3)`, but

```text
P_2=1: h=9, (P_3,Q_3,Delta_3)=(1732293, 5196800,25912)
P_2=2: h=3, (P_3,Q_3,Delta_3)=(10393679,15590400,77736).
```

Therefore no universal function of only
`(N,Delta_N,Q_N,u_N,v_N)` can recover the next centered pair for every reduced
rational input under the actual BBP-form update.

## Scope and next obligation

This is not a counterexample trajectory for the canonical BBP partial sums.
It proves no failure of a BBP-specialized invariant.  It also does not apply
when the nearest-integer carry is retained, because

```text
P_N=(Delta_N+a_N*Q_N)/t_N.
```

Thus the original pair-only cocycle request is under-specified, while the
augmented state `(Delta_N,Q_N,a_N)` is complete but may merely re-encode the
full numerator.  The live T121 question is whether the canonical cross-index
BBP coupling supplies a non-tautological invariant or descent on this complete
state.  No such mechanism is currently known, and V1 remains open.
