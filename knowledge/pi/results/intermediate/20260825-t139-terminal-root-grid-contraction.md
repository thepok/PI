# T139 terminal root-grid contraction

Status: `machine-checked` (T149 exact root-grid projection, T150 kernel floors,
T151 projected-layer floor, T152 endpoint contraction, and T153 exact
natural-horizon consumer); `proof sketch` (the `-861/1000` scalar consequence
and closed-form endpoint-budget evaluation, plus the stronger AX constants)

This note records the independently audited mathematical core of the
2026-08-25 ChatGPT Pro AW memo and the compatible initial-side improvement in
the later AX memo. The AW root-grid chain is now machine-checked in T149--T153;
the later scalar simplification and AX strengthening remain `proof sketch`.
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
  `Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge`.

The complete `lake build TheoryLib` and strict
`pwsh workflows/verification/check.ps1` gate pass for this chain.

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

An independent audit of the AX calculation gives the sharper initial estimate

\[
|I_{q,A}|<E_q-\frac{1983}{100000}.
\]

The exact rational replay uses

\[
q^2(1-\cos(\pi/q))>\frac{49345}{10000},
\qquad q\alpha_q(0)<\frac{23}{10},
\]

and hence

\[
M_{q,1}>\frac{9823}{40000},\qquad
M_{q,2}>\frac{9409}{400000}.
\]

The fixed relation between the first two initial phases gives the dichotomy

\[
\|\theta_1\|_{\mathbb T}\ge\frac1{280}
\quad\text{or}\quad
\|\theta_2\|_{\mathbb T}>\frac{3329}{14000}.
\]

The corresponding sine and Abel bounds are

\[
\sin(\pi/280)>\frac{500}{45149},\qquad
\sin(3329\pi/14000)>\frac{1000}{1477},
\]

\[
|P_{q,1}(\theta_1)|<\frac{45149}{200000},\qquad
|P_{q,2}(\theta_2)|<\frac{1477}{400000}.
\]

These caps are exactly the displayed mass floors minus `1983/100000`.
Replacing the `7/500` initial saving in the terminal root-grid argument by
this stronger value therefore yields

\[
\boxed{
\operatorname{Re}\mathcal B_{q,A}(N)>
-2E_q+\frac{2163}{8000}.}
\]

This is a modest strengthening of `52909/200000`, not a new source of
primitive cancellation. It remains pending Lean verification.

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
comparison `R_q < -861/1000` remains `proof sketch`; it yields the simpler
non-strict sufficient premise

\[
\boxed{
\operatorname{Re}Z_{q,A}(q)\ge-\frac{861}{1000}.}
\]

Equivalently, a target cylinder missed by the first `q` orbit points must have
`Re Z_(q,A)(q) < -861/1000`. This is a strictly weaker sufficient lower-bound
requirement than the earlier `-5413/9000` threshold.

Using the stronger combined endpoint saving above, define instead

\[
R_q^*=2E_q-\frac{2163}{8000}-\frac{q\alpha_q(0)}2.
\]

The same scalar calculation gives

\[
R_q^*<-\frac{78029502281}{90000000000}
<-\frac{8669}{10000}.
\]

Consequently the still-unformalized, non-strict premise

\[
\boxed{
\operatorname{Re}Z_{q,A}(q)\ge-\frac{8669}{10000}}
\]

is sufficient for the corresponding target hit. This supersedes the
`-861/1000` proof-sketch threshold once the stronger initial calculation is
included; neither premise is an actual-pi estimate.

## Claim boundary

The T149 root-grid identity, T150 kernel floors, T151 projected-layer bound,
T152 endpoint inequality with saving `52909/200000`, and T153 exact
scale-dependent natural-horizon consumer are `machine-checked`. The scalar
endpoint-budget evaluation and comparison producing `-861/1000` are still
`proof sketch`. The stronger AX initial saving `1983/100000`, combined
endpoint saving `2163/8000`, and scalar threshold `-8669/10000` also remain
`proof sketch` pending Lean verification.
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
