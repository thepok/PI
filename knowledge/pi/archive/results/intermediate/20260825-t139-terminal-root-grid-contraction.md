# T139 terminal root-grid contraction

Status: `machine-checked` (T149 exact root-grid projection, T150 kernel floors,
T151 projected-layer floor, T152 endpoint contraction, and T153 exact
natural-horizon consumer, plus T156 scalar threshold closure, hit consumer,
and missed-cylinder contrapositive); `proof sketch` (the closed-form
endpoint-budget evaluation and stronger AV endpoint constant)

This note records the independently audited mathematical core of the
2026-08-25 ChatGPT Pro AW memo and the compatible initial-side improvements in
the later AX and AV memos. The AW root-grid chain and its scalar natural-scale
closure are now machine-checked in T149--T153 and T156; the AV strengthening
remains `proof sketch`.
These results improve only the literal valuation-positive endpoint sector of
T139; the actual-pi primitive/off-diagonal estimate remains open.

The verified modules and public declarations are:

- [`T149T149BoundaryRootGridProjection.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T149T149BoundaryRootGridProjection.lean):
  `Theory.PiDigits.BoundaryRootGridProjection.rootGridProjection_eq` and
  `Theory.PiDigits.BoundaryRootGridProjection.boundaryLayerPolynomial_eq_divisible`;
- [`T150T150BoundaryKernelFloors.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T150T150BoundaryKernelFloors.lean):
  `Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_193` and
  `Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_eight_mul_sq_div`;
- [`T151T151BoundaryProjectedLayerFloor.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T151T151BoundaryProjectedLayerFloor.lean):
  `Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt`;
- [`T152T152BoundaryRootGridEndpoint.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T152T152BoundaryRootGridEndpoint.lean):
  `Theory.PiDigits.BoundaryRootGridEndpoint.primitiveBoundaryEndpoint_re_gt_neg_two_budget_add`;
- [`T153T153BoundaryRootGridNaturalConsumer.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T153T153BoundaryRootGridNaturalConsumer.lean):
  `Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge`;
- [`T156T156BoundaryNaturalThresholdClosure.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T156T156BoundaryNaturalThresholdClosure.lean):
  `Theory.PiDigits.BoundaryNaturalThresholdClosure.rootGridNaturalThreshold_lt_neg_861`,
  `Theory.PiDigits.BoundaryNaturalThresholdClosure.piOrbit_hit_of_primitiveBoundary_ge_neg_861`,
  and
  `Theory.PiDigits.BoundaryNaturalThresholdClosure.primitiveBoundary_lt_neg_861_of_piOrbit_misses`.

The complete `lake build TheoryLib` and strict
`pwsh workflows/verification/check.ps1` gate pass for this chain through T156.

## Setup

Fix `k >= 3`, `q = 10^k`, `0 <= A < q`, and

\[
K_q(t)=(\cos(2\pi t)-\cos(\pi/q))F_q(t)^2,
\qquad
F_q(t)=\frac1q\left|\sum_{j=0}^{q-1}e(jt)\right|^2.
\]

Write

\[
K_q(t)=\alpha_q(0)+2\operatorname{Re}
\sum_{h=1}^{2q-1}\alpha_q(h)e(ht),
\]

where the positive-frequency coefficients are positive. In the T139
primitive-ray decomposition let

\[
Z_{q,A}(N)=\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N),
\qquad
\mathcal B_{q,A}(N)=T_{q,A}(N)-I_{q,A},
\]

and let `E_q` be the exact endpoint budget. The already machine-checked
decimal-layer identities give

\[
E_q=\sum_{s=1}^k M_{q,s}.
\]

The further closed-form evaluation

\[
E_q=\frac{(1-\cos(\pi/q))q(q-1)}{18}
-\frac{k}{2}\alpha_q(0)<\frac{\pi^2}{36}
\]

remains `proof sketch`; none of T149--T153 requires it as a verified premise.

## Root-grid projection

For an integer `d >= 1`, define the divisibility-layer polynomial

\[
P_{q,d}(t)=
\sum_{\substack{1\le h\le2q-1\\d\mid h}}
\alpha_q(h)e\!\left(\frac hd t\right).
\]

T149 machine-checks the exact pointwise root-of-unity identity

\[
\boxed{
\alpha_q(0)+2\operatorname{Re}P_{q,d}(t)
=\frac1d\sum_{r=0}^{d-1}K_q\!\left(\frac{t+r}{d}\right).}
\]

through `rootGridProjection_eq`, and identifies each decimal layer with this
divisibility projection through `boundaryLayerPolynomial_eq_divisible`. This
averages spatial translates only to project onto one divisibility layer; it
does not average over target words. T150 machine-checks, for `q >= 1000` and
the unit-period representative `0 <= t < 1`,

\[
K_q(t)>-\frac{193}{1000}
\]

as `boundaryMinorant_re_gt_neg_193`. It also machine-checks
`boundaryMinorant_re_gt_neg_eight_mul_sq_div` on the separated representative
`1/(2d) <= t <= 1-1/(2d)`. T151 combines those T150 floors with T149 and
machine-checks, for `d >= 10` and every real `t`,

\[
\operatorname{Re}P_{q,d}(t)>
-\frac{193}{2000d}
-\frac{4d(d-1)}{9q^2}
-\frac{\alpha_q(0)}2.
\]

as `divisibleBoundaryPolynomial_re_gt`. The proof uses the global floor for
the at most one root-grid point within circle distance `1/(2d)` of an integer
and the sharper sidelobe estimate `K_q(t)>-8d^2/(9q^2)` at every other grid
point.

## Endpoint contraction

Apply the projection bound to the first two terminal decimal layers
`d=10,100`, use the machine-checked scalar bounds

\[
M_{q,1}>\frac{49}{200},\qquad
M_{q,2}>\frac{23}{1000},\qquad
\alpha_q(0)<\frac{12}{5q}\le\frac3{1250},
\]

and bound all later terminal layers by their masses. T147 supplies the
machine-checked strict initial estimate

\[
|I_{q,A}|<E_q-\frac7{500}
\]

T152 combines these inputs and machine-checks the resulting endpoint
improvement, uniformly in `A` and `N`, as
`primitiveBoundaryEndpoint_re_gt_neg_two_budget_add`:

\[
\boxed{
\operatorname{Re}\mathcal B_{q,A}(N)>
-2E_q+\frac{52909}{200000}.}
\]

The exact rational saving comes from

\[
\frac{49}{200}+\frac{23}{1000}-\frac3{1250}
-\frac{193}{20000}-\frac{193}{200000}
-\frac{111}{25000}+\frac7{500}
=\frac{52909}{200000},
\]

where `4440/q^2 <= 111/25000`. T147 alone supplied only the real-part
consequence `Re B > -2E_q+7/500`; the extra saving is
`50109/200000`.

### Stronger initial-side combination (`proof sketch`)

An independent audit of the later AV calculation gives, uniformly for
`k >= 3`, every target and every horizon,

\[
\boxed{|I_{q,A}|<E_q-\frac3{125},
\qquad |\mathcal B_{q,A}(N)|<2E_q-\frac3{125}.}
\]

The initial estimate supersedes the earlier AX proof-sketch saving
`1983/100000`: `3/125 = 2400/100000`. Replacing the machine-checked `7/500`
initial saving in the AW terminal root-grid argument by `3/125` yields

\[
\boxed{
\operatorname{Re}\mathcal B_{q,A}(N)>
-2E_q+\frac{54909}{200000}.}
\]

This improves the earlier AX/AW combined proof-sketch constant `2163/8000`
by exactly `417/100000`. It remains endpoint-sector polish pending Lean
verification; it supplies no primitive or off-diagonal cancellation.

## Conditional natural-horizon consumer

Define

\[
R_q=2E_q-\frac{52909}{200000}-\frac{q\alpha_q(0)}2.
\]

At the natural horizon `N=q`, T153 transports the T152 inequality through the
exact T139 defect identity. Its theorem
`piOrbit_hit_of_rootGrid_primitiveBoundary_ge` machine-checks that

\[
\operatorname{Re}Z_{q,A}(q)\ge R_q
\]

forces a hit of the cylinder `[A/q,(A+1)/q)`. The separate audited scalar
comparison is now machine-checked by T156 as
`rootGridNaturalThreshold_lt_neg_861`:

\[
\boxed{R_q< -\frac{861}{1000}.}
\]

Consequently T156's `piOrbit_hit_of_primitiveBoundary_ge_neg_861`
machine-checks the simpler non-strict sufficient premise

\[
\boxed{
\operatorname{Re}Z_{q,A}(q)\ge-\frac{861}{1000}.}
\]

T156's `primitiveBoundary_lt_neg_861_of_piOrbit_misses` machine-checks the
strict contrapositive: a target cylinder missed by the first `q` orbit points
must have `Re Z_(q,A)(q) < -861/1000`. This is a strictly weaker sufficient
lower-bound requirement than the earlier `-5413/9000` threshold. It remains a
generic implication; T156 supplies no premise proving a hit or primitive
lower bound for any particular target.

Using the stronger combined endpoint saving above, define instead

\[
R_q^*=2E_q-\frac{54909}{200000}-\frac{q\alpha_q(0)}2.
\]

This is smaller than the earlier AX/AW value by `417/100000`. In particular,
the already audited weaker scalar consequence remains valid:

\[
R_q^*<-\frac{8669}{10000}.
\]

Consequently the still-unformalized, non-strict premise

\[
\boxed{
\operatorname{Re}Z_{q,A}(q)\ge-\frac{8669}{10000}}
\]

is sufficient for the corresponding target hit. This is deliberately not
advertised as an optimized scalar threshold for the new endpoint constant;
it only records a previously audited clean consequence. Neither premise is an
actual-pi estimate.

## Claim boundary

The T149 root-grid identity, T150 kernel floors, T151 projected-layer bound,
T152 endpoint inequality with saving `52909/200000`, and T153 exact
scale-dependent natural-horizon consumer are `machine-checked`. T156's generic
scalar comparison producing `-861/1000`, its hit consumer, and its strict
missed-cylinder contrapositive are also `machine-checked`. The convenient
closed-form evaluation of `E_q` displayed above remains `proof sketch`; T156
derives the needed bound without formalizing that equality. The stronger AV
initial saving `3/125`, combined endpoint saving `54909/200000`, and inherited
scalar threshold `-8669/10000` also remain `proof sketch` pending Lean
verification. They supersede the weaker AX initial and combined constants.
Even the machine-checked part is an unconditional actual-pi endpoint
contraction plus a conditional hit consumer, not primitive cancellation.

The live arithmetic gap is unchanged in kind: no current result proves

\[
\operatorname{Re}
\sum_{u\in\mathcal P_q}p_{q,A}(u)
\sum_{n=0}^{q-1}e(u10^n\pi)
\ge-\frac{8669}{10000}
\]

uniformly for `q=10^k`, `k>=3`, and `A<q`. In particular, the surviving
target-dependent endpoint-free singleton correlation and the required signed
off-diagonal actual-pi structure remain uncontrolled. This proves neither
T124, density, normality, nor V1.
