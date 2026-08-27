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
