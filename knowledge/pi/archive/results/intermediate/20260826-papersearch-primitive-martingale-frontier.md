# PaperSearch primitive-martingale frontier

Status: `proof sketch`; the cited source statements and the bounded
applicability search are `literature-checked`.

Date: 2026-08-26 UTC

This note records one new structural synthesis found through the local
PaperSearch corpus and independently audited against the Lean source. It does
not prove a fixed-pi estimate, V1, density, disjunctivity, or normality.

## Exact primitive observable

Fix `k >= 3`, put `q = 10^k`, and let `0 <= A < q`. With the T139 primitive
ray coefficients, define

\[
 P_{q,A}(x)=\sum_{u\in\mathcal P_q}p_{q,A}(u)e(ux),\qquad
 f_{q,A}(x)=\Re P_{q,A}(x),
\]

and

\[
 Z^x_{q,A}(N)=\sum_{n<N}P_{q,A}(\{10^n x\}).
\]

Every retained primitive frequency is not divisible by ten. Hence the decimal
Perron operator

\[
 (\mathcal L_{10}g)(x)=\frac1{10}\sum_{r=0}^9
 g\!\left(\frac{x+r}{10}\right)
\]

satisfies the exact identity

\[
 \mathcal L_{10}f_{q,A}=0. \tag{1}
\]

For Lebesgue measure and `T(x)={10x}`, the stationary sequence
`f_(q,A) circ T^n` is therefore a reverse martingale-difference sequence for
the decreasing filtration `T^(-n) B`.

Parseval gives

\[
 \sigma_{q,A}^2=\int_0^1 f_{q,A}(x)^2\,dx
 =\frac12\sum_{u\in\mathcal P_q}|p_{q,A}(u)|^2. \tag{2}
\]

For `h=q+j`, where `1 <= j <= q/2` and `10` does not divide `j`, the decimal
ray is a singleton and the checked coefficient formula gives

\[
 |p_{q,A}(h)|
 =\frac{q-j}{2q^2}
  +(1-\cos(\pi/q))\frac{(q-j)^3-(q-j)}{6q^2}
 \ge \frac1{4q}.
\]

There are exactly `9q/20` such frequencies, so

\[
 \boxed{\sigma_{q,A}^2\ge\frac9{640q}.} \tag{3}
\]

The independent audit checked the frequency set, singleton count,
normalization, and target independence of this bound directly against T139.

## Metric theorem and exact scope

Cuny--Merlevede,
[*Strong invariance principles with rate for reverse martingales and
applications*](https://arxiv.org/abs/1209.3677), Corollary `corFLIL`, gives the
Strassen functional LIL for stationary ergodic square-integrable reverse
martingale differences. Equations (1)--(3) meet its hypotheses. Therefore,
for Lebesgue-almost every `x`,

\[
 \limsup_{N\to\infty}
 \frac{\Re Z^x_{q,A}(N)}{\sqrt{2N\log\log N}}
 =\sigma_{q,A}\ge\frac3{\sqrt{640q}}, \tag{4}
\]

with the corresponding negative liminf. A countable intersection makes (4)
simultaneous over all decimal pairs `(k,A)` for almost every `x`.

This is a complete target-signed primitive-polynomial statement, not a
coordinatewise or unsigned estimate. Its fatal limitation is the exceptional
set: the theorem provides no criterion placing the named point `x=pi` in its
full-measure set. The current T148 Lean consumer is also specialized to
`piOrbit`, so the metric theorem and that declaration cannot be composed into
a pi theorem.

## Later-horizon fixed-pi consumer

The existing T148 and T156 constants give a particularly short surviving
fixed-pi target. Write

\[
 Z^\pi_{q,A}(N)=\operatorname{primitiveBoundaryFourierSum}(q,A,N).
\]

The independent audit checked from T145--T148 and T156 that

\[
 4E_{q,A}-\frac7{250}
 <q\alpha_q-\frac{122091}{100000}<q\alpha_q,
\]

where `E_(q,A)` is the endpoint budget and `alpha_q` the boundary zero
coefficient. T145/T147 also give `4E_(q,A)-7/250 > 0`. Consequently, for
`N >= q`,

\[
 \boxed{
 N\ge q\quad\text{and}\quad \Re Z^\pi_{q,A}(N)\ge0
 \quad\Longrightarrow\quad
 \text{the target }A\text{ is hit}.} \tag{5}
\]

Thus the wordwise fixed-pi positive-excursion statement

\[
 \forall k\ge3\ \forall A<10^k\ \exists N\ge10^k:\quad
 \Re Z^\pi_{10^k,A}(N)\ge0 \tag{PE}
\]

would feed the checked T148 consumer directly. It permits target-dependent
late horizons and is compatible with the recorded failure at the universal
natural horizon `N=q`. `(PE)` remains a `conjecture`; neither (4),
irrationality, transcendence, nor the variance calculation proves it for pi.

The actual delayed-BBP or T169 Machin formulation must retain the complete
joint numerator/complementary-denominator phase. A horizon-uniform transfer
error is only bounded noise beside (PE); it does not select the required sign.

## Deduplicated PaperSearch applicability trail

PaperSearch was queried iteratively across fixed lacunary orbits, maximal
gaps, shrinking targets, reverse martingales, hypergeometric/Pade recurrences,
varying moduli, Kloosterman sums, modular inverses, and Fourier-decaying
measures. Peres--Yang `2606.28860` and Chen--Ye--Zheng `2604.14036` were
rediscovered but not promoted: both had already been source-audited in the
repository's 2026-08-13 archive.

Three primary sources absent from the repository were checked:

- Tan--Zhou, [arXiv:2409.03331](https://arxiv.org/abs/2409.03331), Theorem
  1.8, gives quantitative lacunary shrinking-target counts under logarithmic
  Fourier decay, but only `mu`-almost everywhere. `delta_pi` has Fourier
  transform of modulus one, and support membership does not license evaluation
  at a zero-mass named point.
- Aistleitner--Fruhwirth--Prochno,
  [arXiv:2511.15595](https://arxiv.org/abs/2511.15595), gives
  resonance-sensitive Gaussian tails for a fixed trigonometric polynomial and
  Lebesgue-random starting point. It neither selects pi nor supplies constants
  for the growing-degree, target-dependent T148 family.
- Ho, [arXiv:2604.18535](https://arxiv.org/abs/2604.18535), shows that broad
  integrability and Fourier-tail regularity alone do not control lacunary
  averages. It is negative context, not a counterexample to the finite T128
  polynomial or a statement at pi.

A separate bounded search of finite-field dynamics, modular hyperbolas,
incomplete Kloosterman sums, finite-field hypergeometric sums, Pade
asymptotics, and recurrence orders found no theorem for the actual Machin
carrier. The exact mismatch is twofold: those results average many states in
one fixed modulus and/or retain only local residues, whereas T169 exposes one
selected state at each changing composite modulus and the target sign depends
on its complete complementary denominator. Any reuse of this literature must
first derive a genuine long family inside an actual carrier modulus while
preserving the complementary CRT phase.

## Attempt ledger

1. **Primitive reverse-martingale LIL.** Exact and quantitatively nondegenerate
   under Lebesgue measure; first fatal line is specialization of an a.e. theorem
   to pi. Reopen with a pointwise arithmetic theorem selecting the actual pi or
   delayed-carrier sequence.
2. **Fixed-modulus finite-field/Kloosterman cancellation.** Available theorems
   sum many states in one modulus; the carrier is a selected diagonal through
   changing moduli. Reopen with an actual intra-modulus family that retains the
   complementary phase.
3. **T169-rate rational shadow plus strong Diophantine properties.** Generic
   digit-omitting Cantor carriers can have the same geometric transfer rate;
   this mostly specializes the already recorded all-degree Cantor separator.
   Reopen only with actual Machin numerator/denominator coupling.
