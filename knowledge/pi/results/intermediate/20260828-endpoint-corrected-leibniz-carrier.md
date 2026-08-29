# Endpoint-corrected Leibniz carrier

Date: 2026-08-28 UTC

Claim label: `proof sketch` (independently audited).  This is a new
π-specific one-sided carrier construction that removes the recorded
Machin/private-prime **magnitude** obstruction.  It does not prove the missing
target-signed same-child inequality.

## Fixed-order carrier

Let `p>=17` be prime with `p=1 mod 4`, put `M=(p-3)/2`, and define

```text
L_p = 4*sum_(k=0)^M (-1)^k/(2*k+1),
t(x) = (1-x)^4/4,
P0(x) = 1-x/2+(1-x)^2/4,
P2(x) = P0(x)*(1-t(x)),
c_p = L_p+4*integral_[0,1] x^(p-1)*P2(x) dx.
```

The identities `(1+x^2)*P0(x)=1+t(x)` and
`P2(x)=(1-t(x)^2)/(1+x^2)` give the exact distinguished remainder

```text
pi-c_p = (1/4)*integral_[0,1]
           x^(p-1)*(1-x)^8/(1+x^2) dx > 0.
```

If `D_p=product_(j=0)^8 (p+j)`, beta integration yields

```text
5040/D_p < pi-c_p < 10080/D_p.
```

Moreover `P2(0)=15/16`, so

```text
c_p = beta_p + 15/(4*p),
```

where `beta_p` has denominator coprime to `p`.  Thus the carrier retains an
exact private coordinate of scale `p^-1` while its directed actual-π error is
`O(p^-9)`.

For every fixed even `R>=2`, the same construction with

```text
P_R = P0*sum_(j=0)^(R-1) (-t)^j
```

gives

```text
pi-c_(p,R) = 4^(1-R)*integral_[0,1]
               x^(p-1)*(1-x)^(4*R)/(1+x^2) dx,

(4^(1-R)/2)*(4*R)!/product_(j=0)^(4*R)(p+j)
  < pi-c_(p,R)
  < 4^(1-R)*(4*R)!/product_(j=0)^(4*R)(p+j).
```

For `p>4*R`, one also has
`c_(p,R)=beta_(p,R)+4*(1-4^(-R))/p`, with `p`-free denominator for
`beta_(p,R)`.  A nontrivial private coordinate additionally requires
`p` not dividing `4^R-1`.

## Correct private phase and transfer

For `R=2`, choose `nu` with `4*nu=15 mod p` and put
`s=(4*nu-15)/p`.  If `eta=e(1/p)`, the correct factorization is

```text
e(m*c_p) = e(m*(beta_p-s/4))*eta^(nu*m).
```

The fourth-root term `e(-m*s/4)` is part of the `p`-free channel; omitting it
is incorrect.  Once included, choosing `p` larger than a fixed T179 packet's
complete frequency span makes its private residues distinct.  The usual
cyclotomic-field intersection argument then proves nonvanishing of a
nontrivial **complex** packet.  It does not prove that its target-rotated real
part is nonzero or positive.

For a real finite Fourier polynomial

```text
P(x)=P_const+Re sum_m a_m*e(m*x),
M2(P)=(2*pi)^2*sum_m |a_m|*m^2,
lambda_p=5040/D_p,
u_p=10080/D_p,
```

Taylor's theorem gives the oriented bound

```text
P(pi) >= P(c_p)
         +lambda_p*(P'(c_p))^+
         -u_p*(P'(c_p))^-
         -(u_p^2/2)*M2(P).
```

Applied separately to the literal full-sector `D_d` and `F_d=G_d+D_d`, this
preserves the same child, target rotation, and all five real character
blocks.  The bound is rigorously decidable in principle, but is not a bare
cyclotomic expression: its derivatives contain `pi` and `pi^2`, which require
certified real bounds.

## Exact remaining boundary

A nonzero zero-mean trigonometric packet takes both signs under `p`-free
rational translation.  Therefore private factorization, formal nonvanishing,
full Galois orbits, and unsigned norms do not determine the distinguished real
sign at the specific corrected `p`-free coordinate of `c_p`.

The construction genuinely reverses the earlier scalar scale mismatch:
private phase is `Theta(p^-1)` while phase-transfer error for a fixed packet
is `O(m_max*p^-9)`, or `O_R(m_max*p^(-(4*R+1)))`.  But no lower bound for the
complete carrier packet and no same-child alignment has been proved.

Reopen only by fixing an all-scale prime rule independently of observed
signs and proving the distinguished-coordinate cone inequality

```text
max_(d<10) min(L_p(D_d),L_p(F_d)) > 0
```

along a recursively constructed path.  More denominator, nonvanishing, or
carrier-accuracy work alone does not advance T189.

## Recurrence--transfer incompatibility for `R=2`

A later independent audit closes the most natural all-scale prime rule.  For
`q=10^k`, let

```text
p(q) = least prime divisor of cyclotomicPolynomial(q,10).
```

Since this cyclotomic value is `1 mod 10`, `p(q)` does not divide `q`; hence
`ord_(p(q))(10)=q`, `p(q)=1 mod 4`, and `p(q)<=10^q-1`.  The private phase
therefore repeats after exactly `q` decimal shifts.  The corrected `p`-free
factor remains scale dependent and carries the entire unknown real sign.

More strongly, as a `proof sketch`, for every `q>=10`, target `A`, child `d`,
and every `R=2` endpoint prime satisfying `p<=10^q-1`,

```text
L_p(D_d) < 0.
```

The proof is uniform.  The complete fresh packet has coefficient load `<7`
but contains the unique terminal mode

```text
frequency m_*=(2*(10q)-1)*10^(10q-1),
coefficient magnitude 1/(2*(10q)).
```

Thus `|D_d|<631*q^2` and the first derivative has the corresponding linear
frequency bound, while the absolute curvature load is
`>180*q*10^(20q-2)`.  The carrier width obeys
`u_p>19*10^(-9q)`.  Substitution into the audited Taylor functional leaves a
negative quadratic term larger than both possible positive terms.  This is a
failure of the global `R=2` certificate, not a proof that the exact carrier
scores lack a common-positive child.

There is a useful exact recurrence consumer.  Put

```text
P=B(q,A,q),
b_d=B(10q,A+dq,q),
R_d=B(10q,A+dq,10q)-10*b_d.
```

Then

```text
G_d=b_d-P,
D_d=9*b_d+R_d,
F_d=10*b_d+R_d-P.
```

Hence `P>0`, `G_d>=0`, and `R_d>=0` imply `D_d,F_d>=9P>0`.  A decimal
replacement orbit whose complete period divides `q` has `R_d=0`, so the
orbit-parametric version of the T172 coefficient argument gives quantitative
regeneration.  This is only a `proof sketch`: the current Lean T172 theorem is
specialized to `piOrbit`, and the periodic theorem is replacement-stable, not
π-specific progress.  The recorded periodic separator also shows that a
generic retaining child can instead have `R_d<-9P`.

Therefore the recurrence-matched rule and, more generally, all small-prime
`R=2` Taylor-cone proofs are closed.  Large primes, higher correction order,
and phase-resolved packet-level integral arguments remain open.  Reopening
the endpoint route requires a direct distinguished-real sign for the complete
target-rotated packet, not private recurrence or the global curvature bound.

## Large-prime phase-resolved boundary

The small-prime curvature obstruction does not extend to an exact large-`p`
endpoint comparison.  For any real finite Fourier polynomial

```text
P(x)=P_const+Re sum_m b_m*e(m*x),
delta_p=pi-c_p,
mu_p=(pi+c_p)/2,
```

one has exactly

```text
P(pi)-P(c_p)
 = -2*sum_m sin(pi*m*delta_p)*Im(b_m*e(m*mu_p)).
```

The positive endpoint integral is only a cumulative parametrization of the
ordinary line integral from `c_p` to `pi`; changing variables recovers
`integral P'` and supplies no independent stationary-phase contribution.

If the carrier is so large that every active frequency satisfies
`m*delta_p<=1/2`, all sine multipliers are positive.  On each primitive ray,
the lacunary temporal layers then obey the audited `proof sketch`

```text
|sum_(n=N)^(H-1) sin(pi*u*10^n*delta_p)*e(u*10^n*mu_p)
 -sin(pi*u*10^(H-1)*delta_p)*e(u*10^(H-1)*mu_p)|
 < (pi/18)*sin(pi*u*10^(H-1)*delta_p).
```

Thus the last temporal layer controls each ray within relative radius
`pi/18`.  This is before real projection and each ray has its own terminal
phase; it gives no common half-plane or cross-ray sign.  The top nine edge
modes structurally occupy every nonzero residue sector, but their aggregated
sector values can still cancel.

There is also an exact fixed-node stabilization boundary.  Each literal
`D_d(x)` and `F_d(x)` is a nonzero trigonometric polynomial with algebraic
coefficients and exact top frequency `(2Q-1)*10^(Q-1)`.  Hence, for fixed
`(q,A)`, there is a positive left root radius `rho_(q,A)` such that every
sufficiently large carrier `c_p=pi-delta_p` with `delta_p<rho_(q,A)` has the
same coordinate signs as the first nonzero left germs at π.  If all twenty
actual values are nonzero, the carrier FMR witness set eventually equals the
actual-π witness set exactly.

Therefore asymptotically large carriers normally preserve rather than create
a sign.  A genuinely carrier-created witness requires an oriented crossing
of an explicit packet zero; no all-scale lower bound on the changing root
radii is known.  Reopen the large-prime route only with cross-ray target-phase
control or an oriented root crossing along the growing path, not with further
accuracy or raywise estimates.
