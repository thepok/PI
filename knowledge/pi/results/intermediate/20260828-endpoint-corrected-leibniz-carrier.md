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
