# Machin positive-remainder sign loss for the complete T189 nonzero sector

Date: 2026-08-27 UTC

Claim labels: cited T138/T142/T169/T179 components are `machine-checked`; the
combined specialization and numerical exponent audit below are `proof sketch`.
No target-signed estimate for pi is proved.

## Exact literal target phase

Let `Q=10q`, let

```text
C = decimalCylinderCenter Q (A+d*q),
z_pi = exp(2*pi*i*pi) = exp(2*i*pi^2),
```

and write `alpha_Q(h)` for T138's positive boundary coefficient. Combining
T177's child character with T179's fine frequencies `h=10*ell+r` gives

```text
Xi_d(q,A;N,H) = Re[10 * sum_(1<=h<=2Q-1, 10∤h)
  alpha_Q(h) e(-h*C) sum_(n=N)^(H-1) z_pi^(h*10^n)].
```

The target center, the factor ten, and every nonzero predecessor frequency
are retained. This is the T189 nonzero-sector block increment, not a rational
shadow and not the complete T128 kernel (the `10|h` zero sector is absent).

For

```text
U=(5+i)/(5-i),  V=(239+i)/(239-i),
Lambda=8*Log(U)-2*Log(V),
```

the principal logarithms give

```text
Log(U)=2*i*atan(1/5),
Log(V)=2*i*atan(1/239),
Lambda=i*pi,
z_pi=exp(-2*i*Lambda^2).
```

Thus a direct complex-log attack reaches a lacunary polynomial at a
log-square exponential. Linear forms in logarithms do not themselves control
its real target sign.

## Exact two-sign obstruction

Define the complete one-step nonzero-sector observable

```text
F_(Q,C)(x) = 10 Re sum_(1<=h<=2Q-1, 10∤h)
  alpha_Q(h)e(h*(x-C)).
```

For any `0<epsilon<1`, the continuous periodic difference

```text
D_epsilon(x)=F_(Q,C)(x+epsilon)-F_(Q,C)(x)
```

has integral zero. It is nonzero: its positive frequency-one coefficient is

```text
5*alpha_Q(1)*e(-C)*(e(epsilon)-1),
```

and T138 gives `alpha_Q(1)>0`. Hence `D_epsilon` assumes both strict signs.
Even a positive, exactly bounded Machin or Padé remainder can therefore move
the complete nonzero sector either way, depending on the carrier phase.
Remainder positivity alone supplies no drift.

## The tail is quantitatively negligible

Let `rho=2/125`. T169's moving single-rate Machin carrier and the positive
coefficient load give, for `Q=10^k` and a nonempty fresh block,

```text
abs(Xi_d(pi)-Xi_d(Machin carrier))
  < 40*pi*positiveBoundaryLoad(Q)/(1-rho) * rho^(N+k).
```

T142 gives the safe load bound `<7` (in fact `<5` follows from the registered
pointwise estimate). At `Q=10000`, `k=4`, and `N=10000`, the conservative
right side is

```text
< 0.9281524 * 10^-17963 < 10^-17963.
```

This is enormously smaller than the experimental `Xi_3` value near `43`.
The alternating positive arctangent remainder neither creates nor materially
changes the observed sign. Almost all sign information is already an exact
property of the moving rational carrier's numerator and complementary
denominator.

The surviving Machin route must prove a one-sided estimate for that literal
carrier arithmetic, or find an integral representation of the entire
target-weighted `F_(Q,C)` with a genuinely signed kernel. Faster approximation,
tail positivity, scalar Padé nonvanishing, and tighter error constants do not
cross the boundary.

## Exact numerator-blind decimal-transfer limit

There is a narrower exact separator at the digit-transfer layer. Let `A/B` be
a nonnegative rational lower carrier, let `eta>0`, and write

```text
10^H*A = B*Q_H + R_H,   0<=R_H<B,
C_H = B-R_H.
```

Then

```text
floor(10^H*(A/B+eta)) = floor(10^H*A/B)
  iff B*10^H*eta < C_H.
```

After removing `g=gcd(B,10^H)`, put `D=B/g` and

```text
Gamma_H = D - ((10^H/g)*A mod D).
```

The same criterion is `D*10^H*eta<Gamma_H`. Thus an open one-sided enclosure
`A/B < pi < A/B+E` transfers the first `H` fractional digits whenever
`D*10^H*E<=Gamma_H`. The canonical non-9 decimal convention and a common
nonnegative integer part are understood.

Uniformly over all numerators with `gcd(D,10)=1`, this is possible exactly in
the numerator-blind regime

```text
D*10^H*E <= 1.
```

Necessity follows by choosing `A` with `10^H*A=-1 mod D`, so `Gamma_H=1`,
and placing the perturbation across the next depth-`H` boundary. Both sides
of that boundary contain quadratic irrationals of irrationality exponent two.

This sharpens the local hostile-boundary statement but does not improve the
T189 carrier route: T169 already transfers the complete phase polynomial
directly with the tiny error above, without requiring digit equality. The
remaining problem is the signed value of the actual rational carrier, not
decimal-prefix stability.

## Terminal private-prime fiber separator

There is a stronger but still narrowly scoped obstruction for terminal Machin
truncations.  Let `p=4*S+5>239` be prime, write the exact terminal common
denominator as `L_S=p*D_S`, and write the reduced numerator as `V_S`.  The
terminal `239`-branch gives exactly

```text
V_S = -4*D_S*239^(-p)  (mod p).
```

Hence the normalized private coordinate

```text
beta_p = V_S*D_S^(-1) = -4*239^(-1)  (mod p),
```

where Fermat removes the exponent.  If `1<=beta_p<p` and
`mu_p*p=4 (mod 239)`, `1<=mu_p<=238`, then this also has the exact directed
Archimedean form

```text
beta_p/p = mu_p/239 - 4/(239*p).
```

Fix the complete complementary CRT coordinate modulo `D_S` and vary the
private `p`-cyclotomic embedding.  Under the explicit coprimality and
frequency-separation hypotheses, the resulting finite T189 values have zero
first moment and a positive exact second moment over the fiber.  Equivalently,
the carrier phases form a translated `1/p` mesh.  For any fixed horizon and
sufficiently large terminal `p`, one nonidentity member shadows the certified
`x=1/3` fixed-point separator closely enough to fall below the robust T189
threshold.

The scope is essential.  The bad conjugate replaces the distinguished
private coordinate `beta_p` by `t*beta_p`; it does **not** preserve that exact
coordinate, and only the identity carrier is close to pi.  The separator
therefore rules out estimates that are uniform over this private-prime fiber
or depend only on Galois-invariant data.  It does not rule out a one-sided
theorem that uses the distinguished joint `(beta_p, complementary CRT phase)`
at the identity embedding.  That joint ordered real inequality remains the
missing pi-specific input.
