# Boundary-matched cosine–Fejér minorant for decimal-cylinder hitting

Status: `proof sketch`

Date: 2026-08-24 UTC

Source branch and commit:
`pi-core-consolidation` at
`c150af557774e37f959b9660df7961e3aeb798f4`.

## Claim boundary

T128 machine-checks the finite Fourier closed form, outside-sign property,
coefficientwise domination of the old Jackson coefficients, positive explicit
zero-mode lower bound, and the resulting finite directional hitting consumer.
T129 now machine-checks the exact Jackson and boundary signed zero modes and
their strict boundary-matching gain for every `q > 1`. T130 checks the
piecewise cubic coefficient/cross-determinant algebra, the exact aggregation
gain identity, and the actual normalized improvement at frequency `2q-1`.
T131 checks the general positive-support frequency-fiber count and resulting
actual aggregated Fejer-square coefficient formula. T132 checks the signed
edge-fiber formula, actual Jackson and boundary coefficient formulas, and full
strict normalized coefficientwise improvement on the positive support. This
note retains `proof sketch` status because only its exact `q=10` directional
separator is machine-checked in T133; the larger aggregate separator and
all-scale fixed-pi implications have not been formalized.

The verified Jackson consumer uses a trigonometric minorant whose positive core
is strictly narrower than the target interval.  This note changes the kernel,
not merely the representation or the order of a triangle inequality: replace
the Jackson boundary parameter by the exact cosine value at the boundary of a
length-`1/q` cylinder.

The resulting minorant has all of the following properties.

- It is nonpositive at every point outside the target half-open cylinder and
  strictly positive throughout the open interior.
- Its zero Fourier coefficient is positive and explicit.
- All of its Fourier coefficients on the finite support are positive.
- Within the full one-parameter family
  `(cos(2*pi*t) - beta) * Fejer_q(t)^2`, it simultaneously minimizes every
  nonzero coefficient after normalization by the zero coefficient, among all
  parameters that have the required outside sign and positive zero mode.
- Its aggregate and directional hitting predicates are strictly weaker than
  the corresponding machine-checked T123/T124 predicates, with
  exact separators at the actual decimal scale `q = 10` (still `proof sketch`).

No fixed-pi estimate is proved.  Consequently this note proves no density,
normality, canonical V1, prescribed decimal occurrence, or fixed-pi
cancellation.  No claim of literature novelty or global extremality is made;
the extremality statement is only for the explicitly defined one-parameter
cosine–Fejér-squared family.

## 1. The unused strip in the verified Jackson kernel

Write

\[
 e_h(t)=\exp(2\pi i h t)
\]

and let the normalized Fejér factor already used in
`T6PiNaturalScaleResonanceObstruction.lean` be

\[
 F_q(t)=\frac1q\left|\sum_{r=0}^{q-1}e_r(t)\right|^2.
\]

The order-`q` Jackson minorant underlying T19, T120, T121, T123, and T124 is

\[
 J_q(t)
 =\left(\cos(2\pi t)-\beta_J(q)\right)F_q(t)^2,
 \qquad
 \beta_J(q)=1-\frac2{q^2}.
 \tag{1}
\]

Indeed, the verified closed form is

\[
 \frac2{q^2}F_q(t)^2
 -\frac12\left|(1-e_1(t))F_q(t)\right|^2,
\]

and `|1-e_1(t)|^2 = 2-2 cos(2*pi*t)`.

The existing outside-sign proof uses

\[
 |\sin(\pi t)|\ge \frac1q.
\]

At the actual boundary `|t| = 1/(2q)`, however,

\[
 |\sin(\pi t)|=\sin\frac{\pi}{2q}>\frac1q
 \qquad(q\ge2).
\]

Thus (1) becomes negative before reaching the cylinder boundary.  Its positive
radius is

\[
 \rho_J(q)=\frac{\arcsin(1/q)}{\pi}
 <\frac1{2q}
 \qquad(q>1),
 \tag{2}
\]

where the strict inequality is the strict secant bound
`arcsin u < (pi/2) u` for `0 < u < 1`.

## 2. The boundary-matched kernel

For `q >= 2`, put

\[
 \gamma_q=\cos\frac{\pi}{q}
\]

and define

\[
 \boxed{
 K_q(t)=\left(\cos(2\pi t)-\gamma_q\right)F_q(t)^2.
 }
 \tag{3}
\]

The new kernel dominates the old one pointwise.  Let

\[
 \delta_q=\beta_J(q)-\gamma_q
 =1-\frac2{q^2}-\cos\frac{\pi}{q}.
\]

Then

\[
 K_q(t)=J_q(t)+\delta_qF_q(t)^2.
 \tag{4}
\]

Moreover `delta_q > 0`.  Indeed,

\[
 1-\cos\frac\pi q
 =2\sin^2\frac{\pi}{2q}
 >\frac2{q^2},
\]

using the strict chord inequality
`sin x > 2x/pi` for `0 < x < pi/2`.

### Exact sign geometry

Let `L=1/q`, let `[a,a+L)` be contained in `[0,1]`, and let

\[
 c=a+\frac L2,\qquad t=x-c,
\]

with `x in [0,1)`.

If `x` is outside `[a,a+L)`, then the endpoint argument already present in
`T27FiniteExponentialCylinderCoverage.lean` gives

\[
 \frac L2\le |t|\le 1-\frac L2.
\]

Equivalently, the circle distance of `t` from an integer is at least `L/2`.
Therefore

\[
 \cos(2\pi t)\le \cos(\pi L)=\gamma_q,
\]

and hence

\[
 K_q(t)\le0.
 \tag{5}
\]

If `a < x < a+L`, then `|t|<L/2`, so
`cos(2*pi*t)>gamma_q`.  Also `F_q(t)>0`: the nonzero zeros of `F_q`
are at integer multiples of `1/q`, and none lies in `|t|<1/(2q)`.
Consequently

\[
 K_q(t)>0.
 \tag{6}
\]

At both geometric boundaries `t=+-1/(2q)`, the cosine factor vanishes while
`F_q(t)>0`.  Thus the sign change in (3) occurs exactly at the cylinder
boundaries.  The left endpoint belongs to the half-open cylinder but has
kernel value zero; this does not affect the hitting implication, because a
positive empirical average still forces a point in the open interior.

### Strict improvement over the Jackson directional kernel

The strip in (2) is genuinely nonempty.  For every `q >= 3`, take
`t=1/(3q)`.  Then `|t|<1/(2q)`, hence `K_q(t)>0`, while

\[
 q\sin\frac{\pi}{3q}>1,
\]

so `J_q(t)<0`.  One elementary verification is

\[
 q\sin\frac{\pi}{3q}
 >\frac\pi3-\frac{\pi^3}{162q^2}
 \ge \frac{157}{150}-\frac{(22/7)^3}{1458}
 =1+\frac{317243}{12502350}>1.
 \tag{7}
\]

This uses `sin y > y-y^3/6`, `157/50 < pi < 22/7`, and `q >= 3`.

## 3. Fourier coefficients and the exact zero mode

Define the triangular Fejér coefficients

\[
 a_q(m)=
 \begin{cases}
 (q-|m|)/q,& |m|<q,\\
 0,& |m|\ge q,
 \end{cases}
\]

and their convolution

\[
 B_q(h)=\sum_{m\in\mathbb Z}a_q(m)a_q(h-m).
 \tag{8}
\]

Thus `B_q(h)` is the coefficient of `e_h` in `F_q^2`.  Put

\[
 M_q(h)=\frac{B_q(h-1)+B_q(h+1)}2.
\]

For the family

\[
 P_{q,\beta}(t)=\left(\cos(2\pi t)-\beta\right)F_q(t)^2,
\]

the coefficient at frequency `h` is

\[
 C_{q,\beta}(h)=M_q(h)-\beta B_q(h).
 \tag{9}
\]

The boundary-matched coefficients are

\[
 C_q(h)=C_{q,\gamma_q}(h).
\]

The two central convolution values are

\[
 B_q(0)=\frac{2q^2+1}{3q},
 \qquad
 B_q(1)=\frac{2(q^2-1)}{3q}.
 \tag{10}
\]

Since `M_q(0)=B_q(1)`, the zero coefficient is

\[
 \boxed{
 C_q(0)
 =\frac{2(q^2-1)-(2q^2+1)\cos(\pi/q)}{3q}.
 }
 \tag{11}
\]

It is positive.  In fact

\[
 \gamma_q<\beta_J(q)
 <\frac{B_q(1)}{B_q(0)},
\]

where the first inequality is `delta_q>0` and

\[
 \frac{B_q(1)}{B_q(0)}-\beta_J(q)
 =\frac{q^2+2}{q^2(2q^2+1)}>0.
 \tag{12}
\]

The full coefficient sum is the value of the polynomial at zero:

\[
 \boxed{
 \sum_h C_q(h)=K_q(0)=q^2\left(1-\cos\frac\pi q\right).
 }
 \tag{13}
\]

## 4. Exact extremality inside the cosine–Fejér-squared family

The outside-sign requirement for `P_{q,beta}` is equivalent to

\[
 \beta\ge\gamma_q.
 \tag{14}
\]

Sufficiency follows from (5).  Necessity is forced by the right endpoint of
`[0,1/q)`: at `t=1/(2q)`, the Fejér factor is nonzero and the cosine is
exactly `gamma_q`.

The zero mode is positive precisely when

\[
 \beta<\frac{B_q(1)}{B_q(0)}.
 \tag{15}
\]

For `1 <= h <= 2q-1`, define

\[
 Q_q(h)=B_q(0)M_q(h)-B_q(1)B_q(h).
 \tag{16}
\]

Direct substitution of the finite convolution formulas gives

\[
 Q_q(h)=
 \frac{h(h^2-2qh+2q^2)}{2q^3}
 \qquad(1\le h\le q),
 \tag{17}
\]

and

\[
 Q_q(h)=
 \frac{(2q-h)(h^2-4qh+6q^2)}{6q^3}
 \qquad(q\le h\le2q-1).
 \tag{18}
\]

The two expressions agree at `h=q`, where both equal `1/2`.  They are
strictly positive, since

\[
 h^2-2qh+2q^2=(h-q)^2+q^2
\]

and

\[
 h^2-4qh+6q^2=(h-2q)^2+2q^2.
\]

For every parameter satisfying (14)--(15), all nonzero coefficients are
positive.  If `B_q(h)>0`, then (16)--(18) give
`M_q(h)/B_q(h) > B_q(1)/B_q(0) > beta`; at the endpoint
`|h|=2q-1`, one has `B_q(h)=0` and `M_q(h)>0`.  Symmetry handles negative
frequencies.  More importantly, the normalized weight

\[
 r_{q,h}(\beta)
 =\frac{C_{q,\beta}(h)}{C_{q,\beta}(0)}
\]

obeys

\[
 \boxed{
 \frac{d}{d\beta}r_{q,h}(\beta)
 =\frac{Q_q(h)}{(B_q(1)-\beta B_q(0))^2}>0.
 }
 \tag{19}
\]

Equivalently, without invoking calculus, whenever
`gamma_q <= beta_1 < beta_2 < B_q(1)/B_q(0)`,

\[
 r_{q,h}(\beta_2)-r_{q,h}(\beta_1)
 =\frac{(\beta_2-\beta_1)Q_q(h)}
 {(B_q(1)-\beta_2B_q(0))(B_q(1)-\beta_1B_q(0))}>0.
 \tag{20}
\]

Therefore the smallest admissible parameter

\[
 \beta=\gamma_q=\cos(\pi/q)
\]

simultaneously minimizes every normalized nonzero Fourier coefficient in the
entire useful family (14)--(15).  This is the precise family-level extremality
claim; no larger class of trigonometric minorants is covered.

## 5. Aggregate and directional finite consumers

For a finite sample `x_0,...,x_{N-1}`, let

\[
 S_h(x,N)=\sum_{n<N}e_h(x_n).
\]

Define the boundary aggregate load

\[
 \mathcal L_q^{\rm bdry}(x,N)
 =\frac1N\sum_{0<|h|\le2q-1}C_q(h)|S_h(x,N)|.
 \tag{21}
\]

For a target interval centered at `c`, define

\[
 Z_q^{\rm bdry}(x,N,c)
 =\sum_{0<|h|\le2q-1}
 C_q(h)e_h(-c)S_h(x,N)
\]

and the directional defect

\[
 D_q^{\rm bdry}(x,N,a)
 =-\frac1N\Re Z_q^{\rm bdry}
 \left(x,N,a+\frac1{2q}\right).
 \tag{22}
\]

If the first `N>0` sample points lie in `[0,1)` and avoid
`[a,a+1/q)`, then (5), summed over the sample, gives

\[
 C_q(0)\le D_q^{\rm bdry}(x,N,a)
 \le \mathcal L_q^{\rm bdry}(x,N).
 \tag{23}
\]

Consequently either strict inequality

\[
 D_q^{\rm bdry}(x,N,a)<C_q(0)
 \tag{24}
\]

or

\[
 \mathcal L_q^{\rm bdry}(x,N)<C_q(0)
 \tag{25}
\]

forces a hit in the target cylinder.

### Coefficientwise domination of the aggregated Jackson premise

Let `A_q(h)` denote the frequency-aggregated Jackson coefficients used by
the machine-checked T123 consumer, and let

\[
 A_q(0)=\frac{q^2+2}{3q^3}.
\]

Since

\[
 C_q(h)=A_q(h)+\delta_qB_q(h),
\]

the factorization (16) gives, for every nonzero supported frequency,

\[
 \boxed{
 C_q(0)A_q(h)-A_q(0)C_q(h)
 =\delta_qQ_q(|h|)>0.
 }
 \tag{26}
\]

Hence

\[
 \frac{C_q(h)}{C_q(0)}
 <\frac{A_q(h)}{A_q(0)}
 \qquad(0<|h|\le2q-1).
 \tag{27}
\]

For every finite sample,

\[
 \boxed{
 \frac{\mathcal L_q^{\rm bdry}(x,N)}{C_q(0)}
 \le
 \frac{\mathcal L_q^{\rm agg}(x,N)}{A_q(0)},
 }
 \tag{28}
\]

with strict inequality whenever at least one supported exponential sum is
nonzero.  Thus the aggregated Jackson smallness premise implies (25), and the
current unaggregated T120 premise implies it through the machine-checked
raw-to-aggregated comparison in T123.

This is not a scaling artifact: every individual normalized nonzero weight is
strictly smaller.

### Domination of the directional Jackson premise

Equation (4) gives `K_q(t) >= J_q(t)` pointwise.  Therefore a positive
empirical average of the centered Jackson kernel implies a positive empirical
average of the centered boundary kernel.  Equivalently, the machine-checked
T124 directional Jackson premise implies (24).

The implication is strict at the actual decimal scale.  Take

\[
 q=10,\qquad a=0,\qquad N=1,\qquad x_0=\frac1{12},
\]

so the cylinder center is `c=1/20` and `x_0-c=1/30`.  By (7),

\[
 K_{10}(1/30)>0>J_{10}(1/30).
 \tag{29}
\]

Thus the boundary directional criterion succeeds while the current Jackson
directional criterion fails.

## 6. Exact aggregate separator at `q = 10`

The normalized comparison (28) is also strict at the level of the threshold
predicates for an actual finite sequence.

Let `N=26` and use the complete `26`-point grid with `0` replaced by a second
copy of `1/26`:

\[
 x_0=\frac1{26},
 \qquad
 x_j=\frac j{26}\quad(1\le j<26).
 \tag{30}
\]

For `1 <= h <= 19`, the complete-grid sum vanishes, so

\[
 S_h(x,26)=e_h(1/26)-1,
 \qquad
 \frac{|S_h(x,26)|}{26}
 =\frac{\sin(\pi r_h/26)}{13},
\]

where

\[
 r_h=\min(h,26-h)\in\{1,\ldots,13\}.
 \tag{31}
\]

For the aggregated Jackson coefficients, direct finite summation gives

\[
 \sum_{h=1}^{19}r_hA_{10}(h)=\frac{4608}{625}.
 \tag{32}
\]

Using `sin(pi*r/26) >= r/13` on `1 <= r <= 13`,

\[
 \mathcal L_{10}^{\rm agg}(x,26)
 \ge\frac2{169}\frac{4608}{625}
 =\frac{9216}{105625}
 >\frac{17}{500}=A_{10}(0),
 \tag{33}
\]

with exact gap `22499/422500`.

For the boundary coefficients, write

\[
 \gamma=\cos\frac\pi{10}.
\]

Then

\[
 C_{10}(0)=\frac{66-67\gamma}{10},
 \tag{34}
\]

and the exact weighted moments from (30)--(31) are

\[
 \sum_{h=1}^{19}r_hC_{10}(h)
 =\frac{9(2577-2546\gamma)}{100},
 \tag{35}
\]

\[
 \sum_{h=1}^{19}r_h^3C_{10}(h)
 =\frac{3(454699-441156\gamma)}{100},
 \tag{36}
\]

\[
 \sum_{h=1}^{19}r_h^5C_{10}(h)
 =\frac{3(43167431-41414828\gamma)}{100}.
 \tag{37}
\]

On `[0,pi/2]`,

\[
 \sin u\le u-\frac{u^3}{6}+\frac{u^5}{120}.
\]

Together with

\[
 \frac{951}{1000}<\gamma<\frac{119}{125},
 \qquad
 \frac{157}{50}<\pi<\frac{22}{7},
 \tag{38}
\]

this yields the rational upper bound

\[
 \mathcal L_{10}^{\rm bdry}(x,26)
 <
 \frac{220454069602381739591}
 {1014052235787500000000}.
 \tag{39}
\]

The cosine bounds in (38) follow from
`gamma^2=(5+sqrt(5))/8`,
`559/250 < sqrt(5) < 9/4`, and exact squaring.  Since

\[
 C_{10}(0)>\frac{277}{1250},
\]

one has

\[
 \frac{277}{1250}
 -
 \frac{220454069602381739591}
 {1014052235787500000000}
 =
 \frac{4259905848128260409}
 {1014052235787500000000}>0.
 \tag{40}
\]

Combining (33) and (39)--(40),

\[
 \boxed{
 \mathcal L_{10}^{\rm bdry}(x,26)<C_{10}(0),
 \qquad
 \mathcal L_{10}^{\rm agg}(x,26)>A_{10}(0).
 }
 \tag{41}
\]

This is an exact threshold-crossing separator between the boundary aggregate
criterion and the preceding aggregated Jackson criterion.  It uses no pi
orbit computation.

## 7. Conditional fixed-pi premises

Let

\[
 x_n=\{10^n\pi\}.
\]

A scale-uniform aggregate premise

\[
 \forall k\ge1\ \exists N>0:\qquad
 \mathcal L_{10^k}^{\rm bdry}(x,N)<C_{10^k}(0)
 \tag{42}
\]

would imply that every decimal cylinder of length `k` is hit before that `N`,
by (25).  Therefore (42) would imply canonical V1.  Equation (28) shows that
(42) is strictly weaker at the finite-predicate level than the T123 aggregated Jackson premise.

The smallest premise exposed by this note is word-dependent and directional.
For a nonempty word `s`, let

\[
 q_s=10^{|s|},
 \qquad
 c_s=\operatorname{decimalCylinderLeft}(s)+\frac1{2q_s}.
\]

The premise

\[
 \forall s\ne[]\ \exists N_s>0:\qquad
 -\frac1{N_s}\Re
 \sum_{0<|h|\le2q_s-1}
 C_{q_s}(h)e_h(-c_s)S_h(x,N_s)
 <C_{q_s}(0)
 \tag{43}
\]

would imply that every nonempty decimal word occurs.  The empty word is
trivial, so (43) would imply canonical V1.

No estimate of the form (42) or (43) is proved for pi.

## 8. Relation to the negative-result memory

This mechanism does not use any route retired in
`t120_t119_metric_nearpair_and_forcing_obstructions_20260822.md`.  It assumes
no BBP independence, no conversion of a determinant bound into recurrence, no
denominator-to-Archimedean separation, and no fixed-prime residue lower bound.
It also does not evade the newer same-mesh occupancy no-go: the boundary load
still depends on phase-sensitive Fourier sums and is not determined by a cell
occupancy vector alone.

It improves the verified finite Fourier consumer by matching the minorant to
the exact geometric boundary.

The improvement is downstream of both losses already removed in the trusted
core: T123 frequency aggregation and T124 retention of the signed centered
real part.  It is therefore a new kernel mechanism, not another equivalent
interface to T120.

## 9. Exact remaining gap

The smallest live external obligation is precisely (43): for each prescribed
nonempty decimal word, prove a finite signed, center-dependent cancellation
estimate for the boundary coefficients `C_q(h)`.

No theorem currently in the repository controls this sum for the fixed pi
orbit.  The arithmetic argument must retain the target phase `e_h(-c_s)`.
Taking absolute values recovers the stronger aggregate premise (42), and
replacing `C_q` by the Jackson coefficients recovers the stronger
machine-checked T124 directional premise.

T128 closes the first finite formalization slice.  It defines the
boundary-matched minorant and its finite Fourier presentation and reuses the
generic directional consumer already proved in T124.  In the list below,
items 1 and 4 are machine-checked except that open-interior positivity was not
needed; the zero-mode lower bound in item 2 is machine-checked, as is raw
coefficientwise domination before normalization in item 5.  The remaining
sharper statements are still open formalization work:

1. the outside nonpositivity and open-interior positivity in (5)--(6);
2. the zero mode (11), coefficient positivity, and total mass (13);
3. the factorization (17)--(19);
4. the empty-cylinder consumers (23)--(25);
5. the normalized Jackson domination (26)--(28);
6. the strict directional separator (29);
7. the exact aggregate separator (30)--(41); and
8. the boundary-specific conditional implications (42)--(43) to canonical V1,
   preferably by reusing the word-cylinder proof pattern already checked in
   T123/T124.

The T128--T133 declarations are registered in `audit/AxiomAudit.lean`. This
broader note keeps the label
`proof sketch` until the remaining normalized comparisons, separators, and
fixed-pi implication are checked.

## 10. Verification performed

- The convolution formulas, zero modes, and factorizations were derived by
  exact finite algebra from (8)--(9).
- The identities (17)--(18) were independently checked against direct finite
  convolution for every integer `2 <= q <= 100` and every supported frequency.
- Positivity and normalized domination were checked symbolically and against
  the same finite range.
- The `q=10` moment identities (32), (35)--(37) were recomputed directly from
  the finite coefficient definitions, not inferred numerically.
- Every comparison in (33) and (38)--(40) was reduced to exact rational
  arithmetic.  Floating-point values were not used in the proof.
- The endpoint/wrap convention was checked against the exact inequalities in
  `T27FiniteExponentialCylinderCoverage.lean`; the argument uses both
  `|t| >= 1/(2q)` and `|t| <= 1-1/(2q)`.

The T128 finite-kernel/hitting-consumer slice, T129 exact zero-mode slice, and
T130 cubic algebra/actual outer-endpoint slice, T131 general main-fiber count,
and T132 signed edge/full actual normalized-domination slice are Lean kernel
verified. T133 also checks the `q=10` directional Boundary-vs-Jackson
separator. No Lean verification is claimed here for the aggregate separator
or fixed-pi premise.
