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

The obstruction persists for the complete literal fresh block, including all
primitive rays and every orbit time from `q` through `Q-1`.  Put `Q=10q`,
`B=A+d*q`, and

```text
F_(q,A,d)(x) = 10 Re sum_(u in primitiveBoundarySupport Q)
  primitiveRayCoefficient(Q,B,u) * sum_(n=q)^(Q-1) e(u*10^n*x).
```

T189 identifies `F_(q,A,d)(pi)=Delta_0+Xi_d`.  The top primitive ray
`u_*=2Q-1` has singleton fiber and nonzero coefficient `1/(2Q^2)` before
target rotation.  Hence its top temporal frequency

```text
m_*=(2Q-1)*10^(Q-1)
```

occurs uniquely in `F`.  For every `0<epsilon<1/m_*`, the difference
`F(x+epsilon)-F(x)` therefore remains a nonzero real trigonometric polynomial.
It has mean zero by translation invariance, so it assumes both strict signs.
This `proof sketch` closes the phase-uniform escape route for the whole T189
fresh primitive block, not merely a single time or predecessor sector.  It
does not determine the distinguished value at the Machin carrier; it shows
that remainder direction and magnitude alone cannot orient that value.
For the nonzero T179 innovation alone, the sector-relevant coefficient
`h=5` at its final time is already unique and nonzero (T138 applies for
`q>=3`).  Consequently the same two-sign conclusion holds throughout the
larger window `0<epsilon<1/(5*10^(H-1))`; no global top-frequency argument is
needed.  This sharpens the mechanism-specific window but does not add a sign
at the distinguished carrier.

## Preferred-parity route fails on every legal first child of the seed

For `Y_d=D_d-(-G_d)_+`, let `M_even` and `M_odd` be its two five-digit parity
means.  An outward-interval replay (`experiment`) gives the exact FMR digit
set `{0,1,2,3,4,8,9}` at the certified positive seed `(1000,334,1000)`.  At
all seven legally reached `q=10000` nodes the larger complete parity mean has
the following rigorous upper bound:

```text
A= 334: -23409.1820      A=1334: -79591.9433
A=2334: -61176.5888      A=3334:  -8424.3011
A=4334: -51209.6093      A=8334: -20813.5090
A=9334: -39062.4354
```

The deterministic transfer-shadow lemma is immediate.  If actual and carrier
arrays obey `|D_d-D_d°|<=E_D` and `|G_d-G_d°|<=E_G`, the one-Lipschitz map
`x |-> (-x)_+` gives

```text
|Y_d-Y_d°| <= E_D+E_G,
max_p M_p° < E_D+E_G-8424.
```

Thus the stronger p-free preferred-parity premise is impossible at the next
recursion from this seed; no derivative estimate or sharper T169 constant can
reverse the actual endpoint's sign.  This closes only the parity average.
Literal FMR survives uniquely at `d=5` for `A=1334`, so full multi-sector
same-child transport remains open.  The reduction is a `proof sketch`, the
finite leaves are an `experiment`, and the primitive-ray digitwise transfer
adaptation is not a new Lean declaration.  Corrected reproducibility sources
are in [`audit/computational/t189-pfree-parity`](../../../../audit/computational/t189-pfree-parity/README.md).

There is a mechanism-specific strengthening for arguments using only
branch-invariant Machin-logarithm data.  With

```text
U=(5+i)/(5-i), V=(239+i)/(239-i),
Lambda=8*Log(U)-2*Log(V)=i*pi,
```

integer branch changes generate exactly

```text
Lambda_m=i*pi*(4m+1),
z_m=exp(-2*i*Lambda_m^2)=exp(2*pi*i*pi*(4m+1)^2).
```

Weyl's polynomial theorem makes `(z_m)` equidistributed on the unit circle.
The complete fixed-horizon literal fresh expression is a nonzero zero-mean
real trigonometric polynomial in `z`: its top temporal frequency is unique.
It therefore takes both strict signs on infinitely many branch lifts.  Thus
relations invariant under these logarithm branches cannot orient the literal
T189 sign.  This does **not** exclude genuinely principal-branch or
distinguished-embedding information; supplying quantitative angular control
from precisely such information remains the possible Machin escape route.

## Natural-horizon valuation cost of a scalar phase pulse

There is a narrow asymptotic obstruction even before target centering.  Let
`B=10^v*u`, `10∤u`, and let `L=B*pi-a>0`.  For `n=v+t`, the elementary
identity

```text
e(u*fract(10^n*pi)) = e(10^t*L)
```

does give a strict first-quadrant phase when `0<10^t*L<1/4`.  It is an
uncentred scalar pulse, not a sign for T179.  The pulse inequality implies

```text
|pi-a/B| < 1/(4*u*10^n).
```

[Zeilberger--Zudilin](https://arxiv.org/abs/1912.06345) prove
`mu(pi)<=7.103205334137...`.  Thus, for every fixed
`mu>7.103205334137...` and all sufficiently large `B`, comparison with the
irrationality-measure lower bound gives

```text
n < mu*v+(mu-1)*log_10(u)-log_10(4).
```

If this scalar is identified with one supported T179 primitive frequency,
then `u<=20q-1`; requiring a pulse at `n>=q` therefore forces

```text
v >= (1/7.104-o(1))*q.
```

This is only a `proof sketch` asymptotic necessary condition for the scalar
pulse architecture.  The cited irrationality-exponent statement supplies no
explicit finite onset here.  It does not prove that every Padé,
hypergeometric, or Machin family has only logarithmic reach: such a conclusion
would additionally require a family-specific upper bound on `v_10(B)` or a
lower bound on the complementary cofactor `u`.  After target rotation the
pulse still has either sign, and one frequency still does not control the
complete T179 sector.

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

## Fixed-carrier exactification collapse

A checked `proof sketch` also closes the variant that fixes one rational
Machin lower approximant `M_K` across the whole horizon and expands the
literal target-rotated `D_d,T_d=D_d+G_d` branches at `M_K`.  Strict rational
bounds

```text
0 < L_K < pi-M_K < U_K
```

give exact algebraic lower certificates after replacing the remaining `pi`
and `pi^2` factors by the same rational enclosure.  For each fixed
`q,A,d`, these certificates converge from below to the actual `D_d(pi)` and
`T_d(pi)`.  Consequently

```text
exists K: carrierLower_K(D_d)>0 and carrierLower_K(T_d)>0
```

is equivalent to the original strict same-digit FMR event.  An unrestricted
carrier depth therefore exactifies FMR rather than weakening it.

There is also a coefficient-independent fresh-branch resolution barrier.  If
`Q=10q`, the first- and second-derivative absolute loads satisfy

```text
H_D/S_D >= (10^Q+10^q)/11.
```

For a fixed carrier to turn a nonpositive rational-center fresh score into a
positive lower certificate, it is necessary that

```text
(4*K+5)*5^(4*K+5) > (48/11)*(10^Q+10^q),
```

hence `K > 0.3576691395*Q-O(log Q)`.  This is necessary, not sufficient; past
that scale only convergence as `K -> infinity` is guaranteed.  Thus the
one-sided remainder cannot supply an independent macroscopic source of fresh
positivity between a coarse rational carrier and the fully resolved original
event.

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
