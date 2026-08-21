---
id: external-20260821-1922Z-archimedean-three-adic-fiber-separator
author: external-gpt-pro
created_utc: 2026-08-21T19:22:24Z
base_branch: pi-core-consolidation
base_commit: afe40f38784a9fdeb46683d7da783cb546591769
status: external-unreviewed
kind: directional-research
claim_levels:
  - proof sketch
  - literature-checked
primary_area:
  - Diophantine approximation
  - three-adic arithmetic
  - decimal dynamics
  - BBP rational shadows
---

# Finite three-adic BBP fibers are Archimedean-dense

## Executive judgment

Pause every proposed hidden-carry argument whose non-Archimedean input is exhausted by the conclusions of T87, T89, and T94--T97 and whose Archimedean input is exhausted by one-sided geometric approximation, fixed-length decimal-boundary stability, and a T106-type forced-orbit identity. Those interfaces are jointly insufficient.

The decisive separator is a scaled-fiber density theorem. At epoch `t`, fix any residue of `3^(2*t) q` modulo `3^(2*t+2)`. Rationals `q` with that exact residue are dense in the real line: with denominator `3^(2*t) * 10^K`, the admissible real lattice has mesh exactly `9 / 10^K`. Consequently the entire actual diagonal residue sequence of the selected BBP partial sums can be copied, with its SP1 transition and inverse-system coherence, onto rational shadows converging from below to an arbitrary real target at an arbitrarily prescribed rate.

Taking the target to be a rational translate of the base-10 Thue--Morse--Mahler number yields an irrational number of irrationality exponent `2` whose decimal digits are only `1` and `2`. It satisfies the repository's source-style `IrrationalityMeasureBelow · 8`, yet it is not decimal-disjunctive. The copied shadows can additionally satisfy the BBP tail scale and every algebraic moving-coordinate identity used in T106.

Therefore the current route survives only if it uses a genuinely joint BBP invariant: the specific exact numerator/denominator or coefficient structure must constrain the real phase in a way not preserved by same-fiber replacement. More finite three-adic coherence, by itself, should be deprioritized.

## Repository state used

### Branch and trust boundary

Analysis was performed on branch `pi-core-consolidation` at commit

```text
afe40f38784a9fdeb46683d7da783cb546591769
```

The branch advanced during this research pass from `29c038face4253ca9c88d9a7a1c99bc09f7dc21d` by thirteen commits. The deltas changed only root coordination material, the `ResearchAgents/` to `GPTPro/` control-plane consolidation, and cleanup of obsolete coordination stubs; no `TheoryLib/`, `audit/`, or `knowledge/pi/` mathematical file used below changed. The later SHA is therefore the recorded base.

The repository's proof authority is `TheoryLib/` plus registration in `audit/AxiomAudit.lean`. The trust policy in `knowledge/pi/verified/TRUST.md` permits only `propext`, `Classical.choice`, and `Quot.sound`. The audit imports the T17, T35, and T77--T106 modules used below. A declaration being imported and axiom-clean establishes only its theorem statement, not the truth of an external premise appearing in that statement.

### Machine-checked repository facts used

The following are used as theorem statements, with no strengthening.

1. `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`
   - `PowerTenDiophantine` is the exact restricted power-of-ten approximation predicate.

2. `TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean`
   - `decimalPrefixFloor_eq_of_powerTenDiophantine` gives one-sided decimal-grid stability.
   - `eventually_decimalBlockCode_sevenOversampled_eq` gives eventual fixed-length code equality under an exponent-eight power-of-ten lower bound and a `16^(-K)` lower-approximation tail.
   - `irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine` converts the source-style irrationality-measure premise to the restricted predicate.

3. `TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean`
   - `selectedDepth` is the selected endpoint depth.

4. `TheoryLib/PiQuantitativeBlockHitting/T87T87LiteralSP1Packaging.lean`
   - `selectedDepth_even_step` identifies consecutive positive even selected depths.
   - `literal_sp1` proves the finite rational congruence `9 * B_(next) - B_(current) = 1 (mod 9)` in `RatCongruentThree` form.

5. `TheoryLib/PiQuantitativeBlockHitting/T89T89SelectedDepthScaledIntegrality.lean`
   - `scaled_bbpPartial_three_integral` proves three-adic integrality of `3^(2*t) * bbpPartial (selectedDepth (2*t))`.

6. `TheoryLib/PiQuantitativeBlockHitting/T94T94SelectedResidueTransition.lean`
   - `evenScaledResidue_step` proves the exact finite `ZMod` transition at precision `3^(2*t+2)`.

7. `TheoryLib/PiQuantitativeBlockHitting/T95T95ThreeLocalCoherence.lean`
   - `threeLocalResidue_cast_down` proves compatibility under reduction of precision.
   - `evenScaledResidue_coherent` gives the adjacent inverse-system identity.

8. `TheoryLib/PiQuantitativeBlockHitting/T96T96SelectedRationalCauchy.lean`
   - `evenScaledPartial_cauchy` gives rational three-adic Cauchy congruence at the precision selected by the smaller index.

9. `TheoryLib/PiQuantitativeBlockHitting/T97T97SelectedResidueCauchy.lean`
   - `evenScaledResidue_cast_down_cauchy` gives the corresponding finite-residue cast-down identity.

10. `TheoryLib/PiQuantitativeBlockHitting/T104T104BBPSeriesIdentity.lean`
    - `bbpRealTerm_hasSum_pi` proves the BBP series identity in Lean.
    - `pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq` gives eventual fixed-length decimal-code equality under the explicit external hypothesis `IrrationalityMeasureBelow Real.pi 8`.

11. `TheoryLib/PiQuantitativeBlockHitting/T105T105BBPCodeCoverage.lean`
    - `bbpPartial_arbitrarilyLateCode_iff_pi` identifies arbitrarily-late recurrence of each fixed arithmetic code for the sevenfold BBP shadows with the corresponding property for `pi`, under the explicit source hypothesis; it proves no code occurs.

12. `TheoryLib/PiQuantitativeBlockHitting/T106T106BBPForcedOrbit.lean`
    - `sampledBBPForcing_eq_cast_rat` and `sampledBBPForcingRat_eq_sevenTerms` identify the real forcing with an exact rational seven-term BBP increment;
    - `sampledBBPForcingRat_pos` and `sampledBBPOrbit_succ` give positivity and the exact forced recurrence;
    - `pi_sub_sampledBBPValue_lt_pow16`, `sampledBBPError_nonneg`, `sampledBBPError_lt_geometric`, and `summable_sampledBBPError` give the one-sided geometric and summability bounds;
    - `sampledBBPForcing_eq_error_coboundary` is the exact coboundary identity;
    - `fract_sampledBBPOrbit_add_error` recovers the actual decimal orbit of `pi` modulo one.

### Source-asserted research records used

These are not treated as Lean theorems unless independently represented above.

- `knowledge/pi/workstreams/pi-quantitative-block-hitting/program.json`, agenda records `T87`--`T106`, and the corresponding entries inspected in `knowledge.jsonl` and `log.jsonl` were used to reconstruct the promotion history and the currently stated bottleneck.
- `knowledge/pi/workstreams/pi-quantitative-block-hitting/director-state.json` records `removed-workflow-record://theory-director-pi-quantitative-block-hitting-1784752092971105059`; it was used only as continuation metadata, not as mathematical evidence.
- `knowledge/pi/results/negative/ultrapi/bbp_fiber_matching_no_go_20260813.md` supplies a same-forcing separator after rationality of the finite truncations is dropped. Its explicit limitation is that exact rationality is not preserved.
- `knowledge/pi/results/negative/ultrapi/bbp_odd_lcm_carry_no_go_20260813.md` shows that fresh odd LCM growth and unit residues cannot see the carry after normalization, and that bounded carry gaps are the wrong target.
- `knowledge/pi/results/negative/ultrapi/fixed_modulus_adversarial.md` and `multiprime_adversarial.md` show analogous phase freedom for other rational-shadow interfaces.
- `knowledge/pi/handoffs/review/RESEARCH_SUMMARY_20260809.md` is used only as a review-level description of the broader fixed-phase bottleneck.

### Repository material inspected for orientation

The current versions of `README.md`, `GOAL.md`, `AGENTS.md`, `VERIFICATION.md`, `knowledge/pi/README.md`, `knowledge/pi/OVERVIEW.md`, `knowledge/pi/verified/TRUST.md`, `knowledge/pi/verified/INDEX.md`, `knowledge/pi/workstreams/`, `knowledge/pi/results/negative/`, `knowledge/pi/handoffs/`, and `audit/AxiomAudit.lean` were inspected. After the branch moved, `GPTPro/AGENTS.md`, `GPTPro/README.md`, and the complete `GPTPro/Tasks/` listing were checked for duplicate work; the listed tasks concern the minimal frontier, the appearance-ratio route, Salikhov/power-ten input, post-T17 cancellation, parameter growth, deterministic cancellation search, and statement integrity rather than this same-fiber separator. The external-handoff contract governing this pass permits writes only under `knowledge/pi/handoffs/external/`, so no coordination task file was claimed or modified.

## Exact bottleneck

Write

\[
D_t=\operatorname{selectedDepth}(2t),\qquad
B_t=\operatorname{bbpPartial}(D_t),\qquad
S_t=3^{2t}B_t
\]

for `t >= 1`. T89 makes `S_t` three-adically integral. Let

\[
r_t=\operatorname{res}_{2t+2}(S_t)
   \in \mathbf Z/3^{2t+2}\mathbf Z.
\]

T94 and T95 imply

\[
\operatorname{cast}_{2t+2}(r_{t+1})
   =r_t+3^{2t}\pmod {3^{2t+2}}.                 \tag{1}
\]

T96 and T97 give the resulting lower-precision Cauchy compatibility. These statements determine an inverse system of finite three-adic residues. They do not determine where `B_t` lies in the real topology.

On the Archimedean side, for any lower rational shadow `a_N` of a target `x`, set

\[
X_N=\{10^N a_N\},\qquad
E_N=10^N(x-a_N),\qquad
F_N=10^{N+1}(a_{N+1}-a_N).
\]

Then the identities

\[
X_{N+1}=\{10X_N+F_N\},\qquad
F_N=10E_N-E_{N+1},\qquad
\{X_N+E_N\}=\{10^Nx\}                         \tag{2}
\]

are algebraic for every sequence `a_N`; they are not a mixing mechanism. T106 proves these identities for the exact sevenfold BBP shadows and also proves the relevant error estimates, but the recurrence alone introduces no independent phase information.

For a length-`m` word with integer code `j`, let

\[
I_{j,m}=\left[\frac{j}{10^m},\frac{j+1}{10^m}\right).
\]

After T35/T104, the remaining positive task is a rational-shadow hitting statement, for example

\[
\forall m\ge1\ \forall j<10^m\ \forall L\ \exists N\ge L:\quad
\{10^N\operatorname{bbpPartial}(7N)\}\in I_{j,m},             \tag{3}
\]

or a quantitatively stronger inner-cylinder version. The tail and decimal-boundary machinery transfer (3) to `pi`; they do not prove (3).

The exact hidden-carry question is therefore:

> Which property of the *specific* BBP numerators, denominators, and cross-index coefficient relations constrains the real phases in (3), rather than merely fixing finite three-adic fibers and a small error?

The contribution below proves that the finite fibers themselves impose no such constraint, even when their exact actual values are retained.

## Candidate directions considered

### 1. Treat the T106 forced recurrence as a perturbed expanding map

**Required new input.** A mixing, discrepancy, or covering theorem for a nonautonomous map with the exact BBP forcing.

**Expected leverage.** Direct access to rational-shadow cylinder hits.

**Principal failure mode.** Equation (2) is a moving-coordinate rewriting of the target orbit. Positivity, rationality, geometric decay, and summability of the forcing can all occur for non-disjunctive targets.

**Falsifiability.** The combined-interface separator below satisfies the entire abstract envelope and misses a one-digit word.

**Recommendation.** Deprioritize every version that uses only the size, sign, rationality, or summability of the forcing. Exact seven-term coefficient arithmetic remains outside this closure.

### 2. Extract a real conclusion from T87/T89/T94--T97 alone

**Required new input.** A theorem converting the selected inverse system of three-adic residues into real phase information.

**Expected leverage.** It would exploit the most distinctive verified arithmetic in the selected BBP route.

**Principal failure mode.** Each finite scaled residue fiber is Archimedean-dense, with explicit mesh `9 / 10^K` at the precision used by T94. Even the exact actual diagonal residue sequence can be copied onto shadows converging to an arbitrary target.

**Falsifiability.** Proposition 1 and Theorem 3 below give an exact adversarial construction.

**Recommendation.** Close this abstract route. Do not add more cast-down or Cauchy lemmas unless a proposed next theorem uses data not invariant under same-fiber replacement.

### 3. Add the known irrationality-measure input

**Required new input.** The source-style bound `IrrationalityMeasureBelow x 8`, or only its `PowerTenDiophantine` consequence.

**Expected leverage.** It eliminates decimal-boundary ambiguity for sufficiently accurate one-sided shadows.

**Principal failure mode.** Boundary stability is not cylinder coverage. The explicit Thue--Morse target below has irrationality exponent `2`, hence satisfies the stronger source-style premise, while its decimal alphabet is only `{1,2}`.

**Falsifiability.** Bugeaud's theorem and the digitwise construction give a source-matched counterexample.

**Recommendation.** Retain the input for transfer, but do not count it as progress on hitting.

### 4. Use an exact mixed BBP phase anchor

**Required new input.** A statement involving the actual reduced numerator/denominator, exact BBP coefficient sum, or a cross-index relation that changes under same-fiber replacement and forces a real cylinder or a nontrivial discrepancy estimate.

**Expected leverage.** This is the only BBP route considered here not closed by the separator.

**Principal failure mode.** A proposed mixed statistic may secretly factor through the already-insufficient residue and error data.

**Falsifiability.** Apply the same-fiber substitution test before formalization; then test the full-denominator fiber experiment proposed below.

**Recommendation.** This is the primary surviving direction. Demand a concrete phase-sensitive invariant before further large formal investment.

## Primary contribution

The main contribution is a no-go theorem for the abstract Archimedean/non-Archimedean bridge. It has three layers:

1. a general density theorem for scaled finite three-adic fibers;
2. a splicing theorem copying an arbitrary coherent residue sequence onto shadows approaching any real target at any prescribed rate;
3. a source-matched non-disjunctive target with irrationality exponent `2`, showing that adding T35's external Diophantine premise does not repair the bridge.

The construction is deliberately stronger than a generic “there are many rationals” observation: it retains the exact actual diagonal residues of the selected BBP sequence, hence retains the conclusions of T87, T89, and T94--T97.

## Precise statements

### Definition 1: localized residues and scaled fibers

Let

\[
\mathbf Z_{(3)}=\left\{\frac ab\in\mathbf Q:3\nmid b\right\}.
\]

For `m >= 0`, let

\[
\operatorname{res}_m:\mathbf Z_{(3)}\to\mathbf Z/3^m\mathbf Z
\]

be reduction modulo `3^m`. For natural numbers `t,m` and `r in Z/3^m Z`, define

\[
\mathcal F(t,m,r)=
\left\{q\in\mathbf Q:
3^{2t}q\in\mathbf Z_{(3)},\ 
\operatorname{res}_m(3^{2t}q)=r
\right\}.                                            \tag{4}
\]

### Proposition 1: Archimedean density of every scaled finite fiber

**Claim level: `proof sketch`.**

For all natural numbers `t,m` with `2t <= m`, every `r in Z/3^m Z`, and every real `u<v`, there are integers `K>=0` and `A` such that

\[
q=\frac{A}{3^{2t}10^K}\in(u,v)\cap\mathcal F(t,m,r).             \tag{5}
\]

More precisely, for every sufficiently large `K`, the admissible values in (5) form a translate of a real lattice of mesh

\[
\frac{3^{m-2t}}{10^K}.                              \tag{6}
\]

In the T94 precision `m=2t+2`, the mesh is exactly `9/10^K`, independently of `t`.

### Proposition 2: coherent-fiber splicing

**Claim level: `proof sketch`.**

Let `r_t in Z/3^(2t+2) Z` for every `t>=1`, and suppose

\[
\operatorname{cast}_{2t+2}(r_{t+1})
   =r_t+3^{2t}\pmod {3^{2t+2}}                      \tag{7}
\]

for every `t>=1`. Let `theta` be any real number and let `delta_t>0` with `delta_t -> 0`. Then there is a strictly increasing sequence `q_t in Q`, `t>=1`, such that

\[
\theta-\delta_t<q_t<\theta,                         \tag{8}
\]

\[
3^{2t}q_t\in\mathbf Z_{(3)},\qquad
\operatorname{res}_{2t+2}(3^{2t}q_t)=r_t.           \tag{9}
\]

It follows that for every `t>=1`,

\[
3^{2(t+1)}q_{t+1}
 \equiv 3^{2t}q_t+3^{2t}
 \pmod {3^{2t+2}},                                  \tag{10}
\]

and therefore

\[
9q_{t+1}-q_t\equiv1\pmod 9                          \tag{11}
\]

in the rational three-adic sense. Moreover, for `1<=s<=t`,

\[
3^{2t}q_t\equiv3^{2s}q_s\pmod {3^{2s}}.             \tag{12}
\]

Thus (9)--(12) reproduce scaled integrality, literal SP1, the T94 step, and the T95--T97 inverse-system/Cauchy conclusions.

### Definition 2: the source-matched non-disjunctive target

Let `(tau_k)_(k>=0)` be the Thue--Morse sequence,

\[
\tau_0=0,\qquad \tau_{2k}=\tau_k,\qquad
\tau_{2k+1}=1-\tau_k.
\]

Define the base-10 Thue--Morse--Mahler number and its rational translate by

\[
\xi=\sum_{k=0}^{\infty}\tau_k10^{-k},\qquad
\theta_*=\frac19+\xi.                               \tag{13}
\]

Because `tau_0=0`, the canonical decimal expansion of `theta_*` is

\[
0.(1+\tau_1)(1+\tau_2)(1+\tau_3)\ldots,             \tag{14}
\]

so every decimal digit is `1` or `2` and no carry occurs in (13). In particular, the one-letter word `3` never occurs.

### Proposition 3: Diophantine strength of the target

**Claim level: `literature-checked` plus elementary derivation.**

The irrationality exponent of `xi` is `2`. Rational translation preserves the irrationality exponent, so the irrationality exponent of `theta_*` is also `2`. Consequently

\[
\operatorname{IrrationalityMeasureBelow}(\theta_*,8)             \tag{15}
\]

holds in the exact source-style sense of T4; one may take the witness `mu=3`. The constants are effective.

Independently of the global theorem, (14) gives the elementary restricted estimate

\[
\left|\theta_*-\frac p{10^n}\right|
 \ge \frac1{9\,10^n}
 \ge \frac1{10^{8n}}                                \tag{16}
\]

for every `n>=1` and every integer `p`. Thus `PowerTenDiophantine theta_* 8 1` holds directly.

### Theorem 3: combined-interface separator

**Claim level: `proof sketch`; central statement.**

Let `D_t=selectedDepth(2t)`, let `B_t` be the actual finite BBP partial at depth `D_t`, and let

\[
r_t=\operatorname{res}_{2t+2}(3^{2t}B_t).           \tag{17}
\]

There exist rational numbers `q_t`, `t>=1`, with all of the following properties.

1. `q_t` is strictly increasing and `q_t < theta_*`.
2. The exact actual diagonal residue is copied:
   \[
   \operatorname{res}_{2t+2}(3^{2t}q_t)=r_t.
   \]
3. `3^(2t) q_t` is three-adically integral.
4. Equations (10), (11), and (12) hold; hence the T87, T89, and T94--T97 output interfaces hold for the copied sequence.
5. The Archimedean error can be required to satisfy simultaneously
   \[
   0<\theta_*-q_t<16^{-D_t},                         \tag{18}
   \]
   and, with `rho=10/16^7`,
   \[
   0<E_t:=10^t(\theta_*-q_t)<\rho^t.                 \tag{19}
   \]
6. The errors are summable.
7. With
   \[
   X_t=\{10^tq_t\},\qquad
   F_t=10^{t+1}(q_{t+1}-q_t),                        \tag{20}
   \]
   the forcing is positive and rational, and
   \[
   X_{t+1}=\{10X_t+F_t\},                            \tag{21}
   \]
   \[
   F_t=10E_t-E_{t+1},                                \tag{22}
   \]
   \[
   \{X_t+E_t\}=\{10^t\theta_*\}.                    \tag{23}
   \]
8. The sampled family extends to a rational sequence `a_K`, `K>=0`, with `a_(7*t)=q_t` for every `t>=1`, `a_K<=theta_*`, and
   \[
   0<\theta_*-a_K<16^{-K}.
   \]
9. For every fixed block length `m`, the arithmetic decimal block code of `q_t` at position `t` eventually equals that of `theta_*` at position `t`.
10. `IrrationalityMeasureBelow theta_* 8` holds.
11. `theta_*` is not decimal-disjunctive because digit `3` never occurs.

Therefore no implication from properties 2--10 to decimal disjunctivity is valid. This remains true when the copied residues in property 2 are the exact residues of the actual BBP selected partial sums, rather than an arbitrary toy residue sequence.

### Route-closure corollary

Any successful proof using the selected three-adic route must invoke at least one hypothesis that is not invariant under replacing `B_t` by another rational in the same fiber

\[
\mathcal F(t,2t+2,r_t).                              \tag{24}
\]

The following data are invariant under such a replacement after applying Proposition 2 and therefore cannot suffice as the only phase input:

- the exact finite residues `r_t` at the registered precisions;
- literal SP1 and the scaled step recurrence;
- denominator valuation bounded by `2t` and scaled three-integrality;
- finite cast-down coherence and rational three-adic Cauchy structure;
- arbitrary prescribed one-sided Archimedean convergence rates;
- source-style irrationality measure below `8` of the target;
- fixed-length decimal-boundary stability;
- positivity, rationality, summability, and coboundary form of a T106-type forcing.

What remains outside the closure is the exact identity

\[
B_t=\operatorname{bbpPartial}(D_t),                  \tag{25}
\]

including the full reduced numerator/denominator, the four-pole coefficient structure, exact relations to nonselected depths, and the exact seven-term forcing of T106. A viable bridge must exploit some part of (25) that does not factor through (24).

## Argument or derivation

### Proof of Proposition 1

Choose an integer representative `c` of `r`. For a natural number `K`, impose

\[
A\equiv c10^K\pmod {3^m}.                            \tag{26}
\]

Then

\[
q=\frac{A}{3^{2t}10^K},\qquad
3^{2t}q=\frac A{10^K}.                               \tag{27}
\]

The denominator in the second fraction is prime to `3`, so it lies in `Z_(3)`. Since `10^K` is a unit modulo `3^m`, (26) gives

\[
\operatorname{res}_m(3^{2t}q)=c=r.                  \tag{28}
\]

The integers satisfying (26) form one arithmetic progression of step `3^m`. After division by `3^(2t)10^K`, the corresponding real rationals form one translated lattice of mesh (6). Choose `K` so that this mesh is less than `v-u`. Every open interval of length greater than the mesh meets every translate of that lattice. This gives (5).

Cancellation in the displayed fraction can only reduce the three-primary denominator of `q`; it cannot destroy (27) or (28). Thus the reduced denominator has three-adic valuation at most `2t`, which is the valuation scale relevant to T89.

### Proof of Proposition 2

Construct `q_t` recursively. For `t=1`, apply Proposition 1 to the nonempty interval `(theta-delta_1,theta)`. Having chosen `q_(t-1)<theta`, apply Proposition 1 to

\[
\left(\max\{q_{t-1},\theta-\delta_t\},\theta\right). \tag{29}
\]

This interval is nonempty, so the next choice is strictly larger, lies below `theta`, has the required residue, and satisfies (8). Since `delta_t` tends to zero, `q_t` tends to `theta`.

Equation (7) and the exact copied residues give (10). Factoring its difference yields

\[
3^{2(t+1)}q_{t+1}-3^{2t}q_t-3^{2t}
=3^{2t}\bigl(9q_{t+1}-q_t-1\bigr).                 \tag{30}
\]

Divisibility of the left side by `3^(2t+2)` therefore gives (11). Reducing each adjacent step modulo `3^(2t)` kills the increment `3^(2t)`; iterating and reducing further gives (12).

### Instantiation with the actual BBP residue system

For the actual `r_t` in (17), T89 supplies the integrality needed to define the residues. T94 gives the step at precision `2t+2`; T95 identifies the cast-down of the next diagonal residue with that step. Thus (7) holds exactly, not heuristically. Proposition 2 can therefore copy the actual registered residue system.

Choose

\[
\delta_t=
\min\left\{16^{-D_t},\ \rho^t10^{-t},\ 2^{-t}\right\}.           \tag{31}
\]

Then (18), (19), and convergence follow immediately. This choice is not an approximation to the actual BBP partial sums; it is an adversarial sequence in the same finite three-adic fibers.

### Proof of the moving-coordinate identities

Strict increase gives `F_t>0`, and rationality of `q_t` gives rationality of `F_t`. Algebra gives

\[
\begin{aligned}
10E_t-E_{t+1}
&=10^{t+1}(\theta_*-q_t)
  -10^{t+1}(\theta_*-q_{t+1})\\
&=10^{t+1}(q_{t+1}-q_t)=F_t,
\end{aligned}
\]

which is (22). Also

\[
10^{t+1}q_{t+1}=10(10^tq_t)+F_t.
\]

Taking fractional parts gives (21), because subtracting the integer part of `10^t q_t` changes the right side by an integer multiple of `10`. Finally,

\[
10^tq_t+E_t=10^t\theta_*,
\]

which gives (23). No dynamical theorem enters these identities.

From (19), `sum_t E_t` converges. From (22) and positivity,

\[
0<F_t<10E_t<10\rho^t,
\]

so the forcing is summable as well.

### Decimal-boundary stability for the separator

For every decimal shift `n`, the fractional part of `10^n theta_*` has all digits in `{1,2}`. Hence it lies in `[1/9,2/9]`, giving (16). The target is uniformly far from both endpoints of every power-of-ten grid after the corresponding scaling.

Property (19) gives `theta_*-q_t<16^(-7*t)`. Assign `a_(7*t)=q_t` for `t>=1`. At all remaining indices `K`, choose any rational `a_K` in the nonempty interval `(theta_*-16^(-K),theta_*)`; choose the finitely many initial sampled values similarly. This produces the literal one-sided geometric-tail premise used by T35.

For fixed block length `m`, (31) is eventually smaller than

\[
10^{-8(t+m)},
\]

because `16^(7t)` eventually dominates `10^(8(t+m))`, exactly the numerical comparison formalized in T35. Since `q_t<theta_*`, the same one-sided grid-stability argument gives eventual equality of the two prefix floors at `t` and `t+m`, hence equality of the block codes. Equivalently, the generic T35 theorem applies to the extension `a_K` at the sampled indices `7*t`. The separator therefore does not exploit hidden boundary crossings.

### Literature substitution for the target

Yann Bugeaud's 2011 paper proves in its Section 2 unnumbered Theorem that, for every integer base `b>=2`, the Thue--Morse--Mahler number

\[
\xi_{\tau,b}=\sum_{k\ge0}\tau_kb^{-k}
\]

has irrationality exponent exactly `2`. Remark 2.1 states the corresponding lower bounds effectively. Substituting `b=10` gives the claim for `xi` in (13).

Adding the rational number `1/9` preserves the irrationality exponent. Explicitly, a rational approximation `p/q` to `theta_*` gives the approximation `(9p-q)/(9q)` to `xi`; conversely the same relation runs backward. Fixed factors of `9` alter constants and onsets, not the exponent. Thus `theta_*` has exponent `2`.

To match the repository's exact predicate, take `mu=3<8`. Given positive `epsilon`, set

\[
\eta=\frac{1+\epsilon}{2}>0.
\]

Apply Bugeaud's effective estimate to `xi` at exponent `2+eta`, with numerator `9p-q` and denominator `9q`. For an arbitrary rational `p/q`, the translation identity gives

\[
\left|\theta_*-\frac pq\right|
 =\left|\xi-\frac{9p-q}{9q}\right|
 >(9q)^{-(2+\eta)}
\]

once `q` exceeds an effective onset. Since

\[
3+\epsilon-(2+\eta)=\eta>0,
\]

enlarge the onset until `q^eta>9^(2+eta)`. Then

\[
(9q)^{-(2+\eta)}>q^{-(3+\epsilon)}.
\]

This is exactly the strict inequality and quantifier order required by T4. The onset remains effective.

### Why this is not already the same-forcing separator

The existing BBP fiber-matching no-go preserves the exact BBP forcing and target recurrence while allowing nonrational shadows. The separator here goes in the complementary direction:

- it preserves rational shadows;
- it preserves the exact actual finite selected three-adic residues and all registered coherence conclusions;
- it preserves arbitrary BBP-strength tail schedules and the source-level Diophantine premise;
- it does **not** preserve the exact identity of the shadows as BBP partial sums or the exact seven-term forcing formula.

Together the two separators isolate the surviving information as the joint compatibility of exact BBP rational arithmetic with real phase. Neither projection alone is sufficient.

## Falsification and adversarial tests

### Test 1: explicit elementary replay

Before using the actual residue sequence, one can check the mechanism without any choice construction. Let

\[
\theta=\frac19,\qquad K_t=9t+8,\qquad
q_t=\frac{1-10^{-K_t}}9.
\]

Then `q_t` is the `K_t`-digit truncation of `0.111...`, so it increases to `theta`. Its reduced numerator is the repunit of length `K_t`, which is congruent to `K_t=8 (mod 9)`. Since `10^(K_t)=1 (mod 9)`, one has

\[
q_t\equiv-1\pmod9.
\]

Therefore

\[
9q_{t+1}-q_t\equiv1\pmod9
\]

and the scaled T94-type recurrence follows. The scaled error is exactly

\[
E_t=\frac1{9\,10^{8t+8}}.
\]

Since `10^9>16^7`, this is smaller than `(10/16^7)^t`. The forced-orbit identities are exact, while the target orbit is the constant point `1/9` and is visibly not disjunctive. This replay checks the algebraic skeleton but does not copy the actual BBP residues or global irrationality.

### Test 2: exact-residue substitution

For a finite range of epochs, compute the actual diagonal residues `r_t`, construct `A_t` from (26) in a prescribed narrow interval around `theta_*`, and verify:

- the copied diagonal residue;
- the T94 step after cast-down;
- literal SP1;
- the T96 congruence at every lower epoch;
- the real interval and tail inequalities.

This is an `experiment`, not evidence for the infinite theorem. Its purpose is to catch convention errors in the intended formalization: precision `2t+2`, the scaling `3^(2t)`, denominator orientation, and the cast map.

Possible outcomes:

- A successful replay supports the formal statement and detects no hidden coupling in the registered interfaces.
- A failure caused by an implementation convention should lead to correction of the formal signature, not rejection of the mathematical lattice argument.
- A failure because some claimed property uses more than the copied residues identifies precisely the BBP-specific input that escaped the no-go; that would be valuable.

### Test 3: full-denominator fiber experiment

The separator permits new denominators. The next high-information experiment should freeze the actual reduced denominator as well.

Write the actual selected partial as `P_t/Q_t` in lowest terms and define, for fixed `m`,

\[
\mathcal C_{t,m}=
\left\{
\left\lfloor10^m\{10^tA/Q_t\}\right\rfloor:
0\le A<Q_t,\ \gcd(A,Q_t)=1,
\operatorname{res}_{2t+2}(3^{2t}A/Q_t)=r_t
\right\}.                                           \tag{32}
\]

Compute (32) exactly by congruence classes and interval arithmetic, not by floating point and not by iterating all numerators when a CRT reduction is available.

Competing outcomes are sharply informative:

1. If `C_(t,m)` is all of `{0,...,10^m-1}` for increasing exact ranges, then even full-denominator plus selected-residue data have no local digit leverage at those scales.
2. If some cylinders are systematically excluded, record the exact modulus, numerator restriction, and scale. That restriction is a candidate mixed phase anchor.
3. If the answer oscillates with `t`, identify which denominator factors control the change; a stable asymptotic theorem would still be required.

Finite results remain an `experiment`. They cannot prove coverage or failure of coverage for `pi`.

### Boundary and degeneracy checks

- **Open intervals:** Proposition 1 uses strict real intervals. Choosing mesh strictly smaller than interval length handles endpoint coincidences.
- **Cancellation:** Reducing `A/(3^(2t)10^K)` can remove powers of `3`, but cannot change the scaled rational `A/10^K` or its residue.
- **Zero modulus:** The intended use has `t>=1` and precision `2t+2`; no `ZMod 1` edge case is needed.
- **Decimal convention:** `theta_*` has no terminal-nine ambiguity; its canonical digits are in `{1,2}`.
- **Global versus restricted Diophantine input:** Proposition 3 supplies both the global source-style premise and the direct power-of-ten premise.
- **Uniformity in block length:** Code stability is only eventual for each fixed `m`, matching T35/T104. No uniform-in-`m` claim is made.
- **Exact BBP arithmetic:** The construction intentionally does not preserve (25), the exact denominator, or the seven-term forcing. Any argument using those data is not refuted until its use is made explicit.

### What would falsify the route-closure recommendation

A valid counter to the recommendation would be an exact theorem or counterexample showing that a proposed downstream hypothesis is *not* preserved by the splicing construction and that the nonpreserved hypothesis follows from the existing exact BBP definitions. Merely restating the residues at higher precision, adding another cast-down identity, or invoking smaller Archimedean tails does not suffice: Proposition 1 works at every finite precision and every prescribed positive error scale.

## Recommended system tasks

### Task 1: formalize the scaled-fiber density theorem

**Exact target.** Add a small abstract theorem, separate from the concrete BBP namespaces, of the following mathematical form:

```text
for t m with 2*t <= m, r : ZMod (3^m), and u < v,
there exists q : Q in (u,v) such that
3^(2*t) * q is three-integral and has local residue r at precision m.
```

A useful stronger conclusion records a witness `K,A` with `q=A/(3^(2*t)*10^K)` and the congruence `A = r*10^K (mod 3^m)`.

**Required inputs.** Existing `threeLocalResidue`, `ZMod` cast/unit lemmas, elementary Archimedean bounds, and density of a rational arithmetic progression after choosing large `K`.

**Acceptance criterion.** Lean compilation; registration in `audit/AxiomAudit.lean`; axiom output within the allowlist; an explicit corollary at `m=2*t+2` recording mesh `9/10^K`. The theorem must make no statement about `pi`, BBP partials, carries, or digits.

**Expected information gain.** Converts the central no-go from a prose observation into a reusable machine-checked adversarial interface.

**Explicit non-claims.** No actual BBP numerator is altered; no statement about V1 is proved or refuted.

### Task 2: formalize the coherent-splicing finite-prefix corollary

**Exact target.** For every finite `T`, every coherent residue family `r_t : ZMod (3^(2*t+2))` for `1<=t<=T`, every real `theta`, and positive tolerances `delta_t`, construct rational `q_t` satisfying (8)--(12) through `T`.

A finite-prefix theorem is sufficient for Lean and avoids unnecessary choice infrastructure. The infinite sequence in Proposition 2 then follows at `proof sketch` level by dependent choice, or can be formalized later if useful.

**Required inputs.** Task 1 and existing congruence/cast-down lemmas.

**Acceptance criterion.** Exact preservation of the diagonal residues and adjacent step; a checked derivation of literal SP1 from the scaled step; no hidden assumption that the rationals are concrete BBP partials.

**Expected information gain.** Makes the same-fiber substitution test available to every future proposed bridge.

**Explicit non-claims.** Finite splicing is not a target-number construction and is not a distribution theorem.

### Task 3: create a reviewed negative-result record

**Exact target.** After mathematical review, promote the route-closure corollary to `knowledge/pi/results/negative/` with links to T87, T89, T94--T97, T35, T104, T106, the existing BBP fiber no-go, and Bugeaud's source.

**Required inputs.** Reviewed proof of Propositions 1--3; exact source pin for Bugeaud; optionally the finite replay from Test 2.

**Acceptance criterion.** The record states exactly which class of abstract bridges is closed and lists (25) and the exact seven-term forcing as outside the conclusion. It labels the derivation `proof sketch` unless Task 1/2 have passed the independent gate. V1 is explicitly left open.

**Expected information gain.** Prevents repeated investment in higher finite residue precision without a phase-sensitive coupling.

**Explicit non-claims.** No exhaustive literature or novelty claim; no closure of all BBP methods.

### Task 4: run the full-denominator fiber experiment before proposing a new BBP bridge

**Exact target.** Compute the sets (32) for the largest exact range feasible without heuristic sampling, beginning with `t=1,2,...` and `m=1,...,6`. Record factorization assumptions, exact cardinalities, missing codes, and CRT reductions.

**Required inputs.** Exact selected partial numerators/denominators, actual local residues, exact integer arithmetic, and interval/cylinder conventions from T35.

**Acceptance criterion.** Reproducible source and output; no floating-point decisions; separate results for same local residue and same full denominator plus local residue; both positive and negative outcomes interpreted as above.

**Expected information gain.** Determines whether the surviving denominator/numerator coupling shows any finite real-phase rigidity at all.

**Explicit non-claims.** No finite range proves an asymptotic statement, density, disjunctivity, or V1.

## Integration recommendation

- **Formalization task:** Proposition 1 and the finite-prefix form of Proposition 2 should become small abstract Lean tasks. They have high reuse value and a clear acceptance gate.
- **Experiment:** Run the full-denominator fiber test (32) only after the abstract separator is accepted, so the experiment targets the genuinely surviving data.
- **Negative-result record:** Promote the route-closure corollary after review. It complements rather than duplicates `bbp_fiber_matching_no_go_20260813.md`.
- **Literature record:** Record Bugeaud's theorem as a source for the adversarial target, not as evidence about `pi`.
- **Workstream change:** Mark more finite three-adic coherence plus smaller tail as closed unless accompanied by an explicit same-fiber-sensitive invariant. Redirect BBP work toward the exact full numerator/denominator and coefficient coupling.
- **No repository action:** Do not alter T87--T106, `audit/AxiomAudit.lean`, or the verified overview merely on the basis of this unreviewed handoff.

## Risks and explicit non-claims

1. The separator is not a counterexample involving `pi`. It is a counterexample to a class of abstract implications.
2. It does not preserve the identity `q_t=bbpPartial(selectedDepth(2*t))`.
3. It does not preserve the exact reduced denominator, the exact odd numerator, the four-pole term decomposition, or the exact seven-term forcing in T106.
4. It therefore does not prove that every BBP route is impossible. It identifies the minimum kind of BBP-specific information a surviving route must use.
5. Matching every registered finite three-adic residue does not amount to matching a completed three-adic number together with an Archimedean embedding; no canonical continuous map from the three-adic completion to the real circle is being asserted.
6. The Bugeaud theorem concerns an explicit Thue--Morse--Mahler number, not `pi`. Its role is adversarial: it prevents the irrationality-measure premise from being mistaken for a phase-distribution input.
7. The rational-translation step and the conversion to the repository predicate are elementary derivations, not statements quoted verbatim from Bugeaud.
8. The literature search was targeted to the counterexample source. It is not an exhaustive search and makes no novelty certification.
9. No statement in this handoff has status `machine-checked` unless it is explicitly identified above as an existing repository declaration.
10. V1 remains open.

## Sources

### Repository evidence

- `README.md`
- `GOAL.md`
- `AGENTS.md`
- `VERIFICATION.md`
- `GPTPro/AGENTS.md`
- `GPTPro/README.md`
- `GPTPro/Tasks/`
- `knowledge/pi/README.md`
- `knowledge/pi/OVERVIEW.md`
- `knowledge/pi/verified/TRUST.md`
- `knowledge/pi/verified/INDEX.md`
- `audit/AxiomAudit.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`
  - `PowerTenDiophantine`
- `TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean`
  - `decimalPrefixFloor_eq_of_powerTenDiophantine`
  - `eventually_decimalBlockCode_sevenOversampled_eq`
  - `irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine`
- `TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean`
  - `selectedDepth`
- `TheoryLib/PiQuantitativeBlockHitting/T87T87LiteralSP1Packaging.lean`
  - `selectedDepth_even_step`
  - `literal_sp1`
- `TheoryLib/PiQuantitativeBlockHitting/T89T89SelectedDepthScaledIntegrality.lean`
  - `scaled_bbpPartial_three_integral`
- `TheoryLib/PiQuantitativeBlockHitting/T94T94SelectedResidueTransition.lean`
  - `evenScaledResidue_step`
- `TheoryLib/PiQuantitativeBlockHitting/T95T95ThreeLocalCoherence.lean`
  - `threeLocalResidue_cast_down`
  - `evenScaledResidue_coherent`
- `TheoryLib/PiQuantitativeBlockHitting/T96T96SelectedRationalCauchy.lean`
  - `evenScaledPartial_cauchy`
- `TheoryLib/PiQuantitativeBlockHitting/T97T97SelectedResidueCauchy.lean`
  - `evenScaledResidue_cast_down_cauchy`
- `TheoryLib/PiQuantitativeBlockHitting/T104T104BBPSeriesIdentity.lean`
  - `bbpRealTerm_hasSum_pi`
  - `pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq`
- `TheoryLib/PiQuantitativeBlockHitting/T105T105BBPCodeCoverage.lean`
  - `bbpPartial_arbitrarilyLateCode_iff_pi`
- `TheoryLib/PiQuantitativeBlockHitting/T106T106BBPForcedOrbit.lean`
  - `sampledBBPForcing_eq_cast_rat`
  - `sampledBBPForcingRat_eq_sevenTerms`
  - `sampledBBPForcingRat_pos`
  - `sampledBBPOrbit_succ`
  - `pi_sub_sampledBBPValue_lt_pow16`
  - `sampledBBPError_nonneg`
  - `sampledBBPError_lt_geometric`
  - `summable_sampledBBPError`
  - `sampledBBPForcing_eq_error_coboundary`
  - `fract_sampledBBPOrbit_add_error`
- `knowledge/pi/results/negative/ultrapi/bbp_fiber_matching_no_go_20260813.md`
- `knowledge/pi/results/negative/ultrapi/bbp_odd_lcm_carry_no_go_20260813.md`
- `knowledge/pi/results/negative/ultrapi/fixed_modulus_adversarial.md`
- `knowledge/pi/results/negative/ultrapi/multiprime_adversarial.md`
- `knowledge/pi/handoffs/review/RESEARCH_SUMMARY_20260809.md`

### External evidence

**Yann Bugeaud.** On the rational approximation to the Thue--Morse--Mahler numbers. *Annales de l'Institut Fourier* 61 (2011), no. 5, 2065--2076. DOI `10.5802/aif.2666`.

- **Source identifier:** DOI `10.5802/aif.2666`.
- **Exact locator:** Section 2, unnumbered Theorem; effectiveness in Remark 2.1.
- **Hypotheses:** `(tau_k)` is the Thue--Morse sequence with `tau_0=0`, `tau_(2k)=tau_k`, `tau_(2k+1)=1-tau_k`; `b>=2` is an integer.
- **Conclusion:** The irrationality exponent of `sum_(k>=0) tau_k b^(-k)` is exactly `2`. Remark 2.1 states an effective onset for every positive epsilon.
- **Fixed-pi status:** The theorem does not concern `pi`.
- **Effectivity:** Yes, according to Remark 2.1.
- **Use here:** Substitute `b=10`, then apply the elementary rational-translation argument to `theta_*=1/9+xi`. This supplies a non-disjunctive target satisfying the repository's source-style irrationality-measure premise. It does not instantiate any theorem about `pi`.
