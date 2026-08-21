# AllMath pi research: independent expert review brief

Date: 2026-08-09 UTC  
Audience: mathematicians in dynamics, harmonic analysis, Diophantine approximation, symbolic dynamics, or arithmetic normality  
Purpose: independent assessment and concrete suggestions; this is not a manuscript and makes no solution claim

## Executive assessment

The work is mathematically useful as a reduction, obstruction, and falsification program. It is not presently a credible proof of any new theorem about the decimal digits of \(\pi\).

Three focused programs are open:

1. a lacunary near-return bound for \(\{10^j\pi\}\);
2. positive base-10 factor entropy of the decimal word of \(\pi\); and
3. uniform decay of long-lag equal-block collisions.

The strongest accepted work has done four things.

- It fixed the quantifiers and conventions of each target and built exact conditional implication chains.
- It converted collision questions into nonnegative cylinder/Walsh energies and explicit Fourier or square-function estimates.
- It showed that multiplier-10 telescoping, coefficient magnitudes, stopping rules, generic metric results, ordinary irrationality-measure bounds, and several exact representations of \(\pi\) do not by themselves supply the required pointwise cancellation.
- It checked that appropriately relaxed analogues hold for almost every phase, while carefully keeping those results separate from fixed \(\pi\).

The remaining gap is not formal bookkeeping. It is a genuinely \(\pi\)-specific estimate at exponentially growing decimal frequencies, uniformly over a coupled range of block lengths, lags, starts, and frequencies. In the current state there is no `candidate resolution` or `verified resolution` for any of these three questions.

## Claim-status discipline

This brief uses the repository's exact claim vocabulary:

- `experiment`: computed finite cases only;
- `conjecture`: a precise unproved statement;
- `proof sketch`: a prose argument that may have unchecked gaps;
- `machine-checked`: Lean accepts the stated theorem and its axiom audit is clean;
- `literature-checked`: a dated search and pinned sources are recorded;
- `candidate resolution`: both machine-checked and literature-checked, awaiting expert review;
- `verified resolution`: independent experts checked statement, proof, and novelty.

A `machine-checked` reduction proves only the implication encoded in its theorem type. It does not prove that its hypotheses hold for \(\pi\), that the hypothesis is weaker than the target, or that the route is novel.

## The three canonical targets

### 1. Lacunary near-return sparsity

For \(n,N\geq1\), define the ordered, diagonal-inclusive count

\[
Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
\|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\]

The `conjecture` is

\[
\forall A\geq1\ \exists n_0\ \forall n\geq n_0\ \exists N\geq1:
\quad AnQ_\pi(n,N)\leq N^2. \tag{NR}
\]

The order of quantifiers matters: \(N\) may depend on \(A,n\); the diagonal is retained; and the cutoff is strict. The project has machine-checked that (NR) would imply superlinear decimal factor complexity, but not full digit disjunctivity or normality.

Canonical source: [`problems/local/pi-lacunary-near-return-sparsity.txt`](../../../problems/local/pi-lacunary-near-return-sparsity.txt).

### 2. Positive decimal factor entropy

Let \(p_\pi(n)\) be the number of distinct length-\(n\) factors in the infinite decimal word of \(\pi\). The `conjecture` is

\[
\exists\eta>0\ \exists N\ \forall n\geq N:
\quad p_\pi(n)\geq10^{\eta n}. \tag{ENT}
\]

Equivalently, the base-10 factor entropy is positive. This is strictly weaker than full entropy and does not imply that every finite word occurs. The checked entropy-threshold ladder can certify all words of a fixed length only after the entropy lower bound exceeds the corresponding forbidden-word threshold.

Canonical source: [`problems/local/pi-positive-decimal-factor-entropy.txt`](../../../problems/local/pi-positive-decimal-factor-entropy.txt).

### 3. Long-lag block-collision decay

Let \(B_\pi(i,m)\) be the length-\(m\) decimal block starting at position \(i+1\), and define

\[
R_\pi(m,N)=\#\{(i,j)<N:\ |i-j|\geq m,
B_\pi(i,m)=B_\pi(j,m)\}.
\]

The `conjecture` is

\[
\forall s\in(0,1)\ \exists C_s\geq1\ \forall m,N\geq1:
\quad R_\pi(m,N)\leq C_s\bigl(N+N^2 10^{-sm}\bigr). \tag{LL}
\]

Pairs are ordered; the lag condition removes the diagonal and overlapping blocks. The additive \(N\) term is essential at finite sample sizes. A checked implication chain connects (LL) to positive lower block density and hence to occurrence of every finite decimal word, but the fixed-\(\pi\) premise remains open.

Canonical source: [`problems/local/pi-long-lag-block-collision-decay.txt`](../../../problems/local/pi-long-lag-block-collision-decay.txt).

## Strongest accepted reductions

### A. Collision energy is the canonical nonnegative interface

For empirical orbit points \(x_j=\{10^j\pi\}\), equal length-\(m\) decimal cylinders give an ordered, diagonal-inclusive collision energy. In symbolic notation, if \(C_w(N)\) counts occurrences of a word \(w\) among the first \(N\) starts, then

\[
\sum_w\left(\frac{C_w(N)}N-10^{-m}\right)^2
=\frac1{N^2}\sum_w C_w(N)^2-10^{-m}. \tag{1}
\]

Thus excess collision mass is exactly an \(L^2\) block-frequency error. The lacunary program's T7 gives a `machine-checked` finite cylinder-energy formulation equivalent, up to explicit neighboring-cylinder constants, to (NR). The positive-entropy program's T2/T4/T7/T26/T27 chain gives `machine-checked` sufficient collision and Fejér-energy criteria for (ENT), while retaining all hypotheses. The long-lag program's T1--T3 chain gives a `machine-checked` route from (LL) through total energy to digit disjunctivity.

This interface is preferable to a small signed residual: all energy terms are nonnegative, diagonal contributions and multiplicities are visible, and no cancellation is silently interpreted as randomness.

Relevant accepted library locations:

- `TheoryLib/PiPositiveDecimalFactorEntropy/T1CanonicalEntropy.lean`
- `TheoryLib/PiPositiveDecimalFactorEntropy/T2T2ExponentialCollisionCriterion.lean`
- `TheoryLib/PiPositiveDecimalFactorEntropy/T7T7FejerSpectralCriterion.lean`
- `TheoryLib/PiPositiveDecimalFactorEntropy/T26T26SparseLongBandFejer.lean`
- `TheoryLib/PiPositiveDecimalFactorEntropy/T27T27SparseMicroscopicEquivalence.lean`
- `TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean`
- `TheoryLib/PiLongLagBlockCollisionDecay/T3T3CollisionDecayImpliesDisjunctive.lean`

### B. Failure forces structured Fourier resonance, but not a contradiction

The near-return program converts a failure of (NR) into a bad long lag and a low-harmonic exponential sum involving

\[
h(10^r-1)10^j\pi.
\]

Further autocorrelation and shared-chain reductions force compatible multiscale resonances. These are necessary obstructions to failure, not upper bounds. The deductions expose where phase information must enter but do not conflict with known irrationality bounds for \(\pi\).

The conceptual reason is the multiplier-10 identity. For

\[
S_N(h)=\sum_{j=0}^{N-1}e(h10^j\pi),\qquad e(x)=e^{2\pi ix},
\]

one has

\[
S_N(10^r h)=S_N(h)+O(r), \tag{2}
\]

with the exact endpoint phases retained in the checked modules. Moving upward along a decimal frequency ray therefore shifts the same orbit window; it does not create automatic oscillation.

### C. A scale-matched square-function frontier survives random-model calibration

The long-lag program's T29 defines an exact width-weighted square-function condition over canonical blocks and frequencies through \(10^m\). Its fixed-\(\pi\) instance is still a `conjecture` (program C2/G10).

Program-local T97 supplies a crucial calibration:

- `machine-checked`: the exact bridge from the T90 variable-phase critical-band observable to T31's cross-block weighted-GCD second-moment estimate, including signs, orientations, block widths, frequency endpoints, multiplicities, and independence of the auxiliary parameter \(Q_0\);
- `proof sketch`: Chebyshev, finite-union, summability, and Borel--Cantelli steps showing the eventual constant-relaxed condition for Lebesgue-almost every phase.

This validates the normalization as plausible in a coupled random-phase model. It gives no estimate at \(\alpha=\pi\).

Artifact: [`work/theory/pi-long-lag-block-collision-decay/library/t97/T97_EXACT_VARIABLE_PHASE_BRIDGE.md`](../../theory/pi-long-lag-block-collision-decay/library/t97/T97_EXACT_VARIABLE_PHASE_BRIDGE.md); accepted Lean copy: `TheoryLib/PiLongLagBlockCollisionDecay/T97T97VariablePhaseBridge.lean`.

## Program-local task crosswalk and decisive findings

Task numbers are local to each program. The following entries must not be conflated.

### Near-return T55, T56, T57, T67, T78, T79

#### T55: exact multiplier-10 pairing (`machine-checked`)

T55 proves a signed frequency pairing, phase transport, the one-step telescope, exact endpoint terms, and a decomposition of a fixed Fejér stratum into an endpoint budget plus a terminal shell

\[
(R-1)/10<u\leq R-1.
\]

It then proves that an explicit top-shell correlation hypothesis implies the earlier strict Fejér threshold and its conditional downstream consequences. The top-shell estimate remains an unproved hypothesis. T55 does not prove fixed-\(\pi\) cancellation, (NR), equidistribution, or normality.

Artifacts:

- `TheoryLib/PiLacunaryNearReturnSparsity/T55SignedMultiplierTenPairing.lean`
- [`work/theory/pi-lacunary-near-return-sparsity/library/t55/SignedMultiplierTenPairing.lean`](../../theory/pi-lacunary-near-return-sparsity/library/t55/SignedMultiplierTenPairing.lean)
- axiom registrations in [`audit/AxiomAudit.lean`](../../../audit/AxiomAudit.lean), lines containing `SignedMultiplierTenPairingT55`.

#### T56: stopping rules hit a phase-blind barrier (`proof sketch`)

T56 optimizes every orbitwise stopping selector after T55's exact telescoping. Immediate stopping is uniquely optimal before collision collection; after complete legal collision collection all selectors tie. Immediate stopping retains the full original positive-frequency range. On an exact legal family, the optimized phase-blind guaranteed lower bound is zero while T55 needs a strict positive threshold; the uncertainty radius exceeds the required excess by a factor \(4(R-1)/(R-4)>4\).

This is a method-specific obstruction to coefficient magnitudes plus triangle inequalities. It is not a counterexample to the Fejér claim or to (NR).

Artifact: [`work/theory/pi-lacunary-near-return-sparsity/library/t56/REPORT.md`](../../theory/pi-lacunary-near-return-sparsity/library/t56/REPORT.md).

#### T57: the proposed first-sign localization fails (`proof sketch`)

T57 verifies the stopped-cost finite difference and strict discrete convexity, but gives a legal T55 tuple in which the first-sign rule's unique minimizer is the final orbit vertex, still inside T55's terminal shell. Therefore the rule does not universally produce a smaller lower-orbit block. This is an exact same-domain refutation of that proposed localization, not a refutation of T55's hypothesis.

Artifact: [`work/theory/pi-lacunary-near-return-sparsity/library/t57/REPORT.md`](../../theory/pi-lacunary-near-return-sparsity/library/t57/REPORT.md).

#### T67: terminal-ray strength and Walsh comparison (`machine-checked`)

T67 proves the exact finite empirical Fourier invariance defect along decimal rays, identifies the literal terminal shell, establishes a qualified UPRID-to-threshold implication, and proves an exact Walsh Parseval identity equating centered Walsh energy with normalized decimal-cylinder collision energy. It also constructs abstract sparse-ray and bulk-shell separators.

The separators are deliberately abstract Fourier arrays, not genuine orbit measures. Their role is logical: a bulk shell average can dilute one persistent decimal ray, whereas a per-ray or non-diluting condition can be strong enough to imply the target. T67 does not assert that any separator is realized by \(\pi\).

Artifacts:

- [`work/theory/pi-lacunary-near-return-sparsity/library/t67/REPORT.md`](../../theory/pi-lacunary-near-return-sparsity/library/t67/REPORT.md)
- `TheoryLib/PiLacunaryNearReturnSparsity/T67TerminalRayStrength.lean`
- `audit/AxiomAudit.lean`, registrations containing `TerminalRayStrengthT67`.

#### T78: factorial-series route obstruction (`proof sketch`; source portion `literature-checked`)

T78 independently derives

\[
\pi=\sum_{k\geq0}\frac{2^{k+1}(k!)^2}{(2k+1)!},
\]

then computes exact common and reduced denominators, prime valuations, truncation tails, the power-of-5 transient, residue periods, collision multiplicities, and short-arc occupancy bounds. Combining the exact tail lower bound with the pinned irrationality-measure result yields an eventual family-wide obstruction: every truncation accurate enough for uniform absolute-error transfer over \(0\leq i,j<N\) has reduced coprime cofactor \(m_K\) with

\[
\sqrt{m_K}>N.
\]

Thus a rational-orbit method with a positive square-root-modulus leading cost cannot improve the available length-\(N\) scale on this family. The conclusion is route-specific. It does not exclude cancellation in the truncation error, an estimate without square-root-modulus cost, or another representation.

Artifacts:

- [`work/theory/pi-lacunary-near-return-sparsity/library/t78/REPORT.md`](../../theory/pi-lacunary-near-return-sparsity/library/t78/REPORT.md)
- [`work/theory/pi-lacunary-near-return-sparsity/library/t78/SOURCE_PINS.md`](../../theory/pi-lacunary-near-return-sparsity/library/t78/SOURCE_PINS.md)
- key sources: [Euler E212](https://scholarlycommons.pacific.edu/euler-works/212), [Li E854](https://doi.org/10.2307/2304741), [Rabinowitz--Wagon](https://doi.org/10.1080/00029890.1995.11990560), [Zeilberger--Zudilin irrationality measure](https://doi.org/10.2140/moscow.2020.9.407), and [Bailey--Crandall](https://doi.org/10.1080/10586458.2002.10504704).

#### T79: final arithmetic-opportunity scout (`proof sketch`; source audit `literature-checked`)

After excluding already audited BBP, Zudilin/Bailey--Crandall, and factorial routes, T79 retains one two-term Machin-like specialization from Abrarov--Quine. It derives an exact rational series, a uniform transfer schedule, reduced 2- and 5-adic valuations, the coprime post-transient modulus, multiplicative order, and exact equality-collision formula. A prime \(P=147153121\) survives in the reduced denominator with exponent \(2K-1\), forcing

\[
\sqrt{m_K}\geq P^{K-1/2}>N
\]

throughout the transfer range. Hence the same square-root-modulus approach cannot provide the length-\(\leq N\) Fourier cancellation required by the accepted frontier. A qualitatively different estimate for the exact modular exponential sum is not ruled out.

Artifacts:

- [`work/theory/pi-lacunary-near-return-sparsity/library/t79/REPORT.md`](../../theory/pi-lacunary-near-return-sparsity/library/t79/REPORT.md)
- [`work/theory/pi-lacunary-near-return-sparsity/library/t79/SOURCE_PINS.md`](../../theory/pi-lacunary-near-return-sparsity/library/t79/SOURCE_PINS.md)
- primary source: [Abrarov--Quine, arXiv:1706.08835v3](https://arxiv.org/abs/1706.08835v3).

The dated narrow delta search in [`work/theory/pi-lacunary-near-return-sparsity/DIRECTION.md`](../../theory/pi-lacunary-near-return-sparsity/DIRECTION.md) is `literature-checked` only for its stated 2025--2026 queries. It found no new representation meeting the quantitative bridge requirement; it is not an exhaustive closure of the literature.

### Positive-entropy T55, T56, T57, T67, T78, T79, T97, T98

#### T55: semantic persistence (`proof sketch`, using machine-checked inputs)

This is a compactness and graph-translation result for the times-16 transversal branch. It relates infinite endpoint-safe cores to compatible all-depth paths with arbitrarily late deviations. It neither proves the persistence hypothesis for \(\pi\) nor resolves the quantitative transversal criterion.

Artifact: [`work/theory/pi-positive-decimal-factor-entropy/library/t55/T55_SEMANTIC_PERSISTENCE.md`](../../theory/pi-positive-decimal-factor-entropy/library/t55/T55_SEMANTIC_PERSISTENCE.md).

#### T56: exact sparse lag-sector audit (`machine-checked` plus a replayed abstract obstruction)

At the sparse scale

\[
L_n=10^{\lfloor n/2\rfloor},\qquad H_n=10^n/2,
\]

T56 gives the exact ordered, diagonal-inclusive lag decomposition and partitions every off-diagonal contribution into short and long sectors. Accepted long-sector hypotheses could give \(O(L_n)\), but the unconditional short-sector bound is only \(2nL_n\). A replayed abstract incidence family shows that combinatorics alone cannot improve this to a uniform multiple of \(L_n\). The exact missing input is an all-short-sector fixed-\(\pi\) estimate; T56 does not say it is false.

Artifacts:

- [`work/theory/pi-positive-decimal-factor-entropy/library/t56/T56_LAG_SECTOR_AUDIT.md`](../../theory/pi-positive-decimal-factor-entropy/library/t56/T56_LAG_SECTOR_AUDIT.md)
- `TheoryLib/PiPositiveDecimalFactorEntropy/T56T56LagSectorAudit.lean`.

#### T57: universal finite-core extinction is false (`machine-checked`)

T57 constructs a compact times-10-invariant sibling set \(X=\{0\}\cup\{10^{-k}:k\geq1\}\) and, for every \(m\geq2\), a length-\(m\) word whose core persists through \(2^m\) times-16 iterates. It proves the literal negation of the previously proposed universal linear finite-core hypothesis. This refutes only that sufficient certificate, not the actual times-16 orbit closure of \(\pi\), (ENT), or digit disjunctivity.

Artifact: `TheoryLib/PiPositiveDecimalFactorEntropy/T57T57MovingWordCoreObstruction.lean`.

#### T67: short-lag periodic-component audit (`proof sketch`)

T67 translates short-lag block overlaps into periodic components and shows that individual Fine--Wilf-style window control does not automatically control aggregate cluster multiplicity. The missing input is a uniform bound on the total multiplicity/overlap load of periodic clusters. This is again a reduction, not a fixed-\(\pi\) estimate.

Artifact: [`work/theory/pi-positive-decimal-factor-entropy/library/t67/T67_SHORT_LAG_PERIODIC_COMPONENTS.md`](../../theory/pi-positive-decimal-factor-entropy/library/t67/T67_SHORT_LAG_PERIODIC_COMPONENTS.md).

#### T78: square-sparse projected-phase countermodel (`machine-checked`)

T78 constructs irrational sibling reals with scale-dependent sparse decimal blocks for which the proposed projected-periodicity certificate fails at every allowed depth. The witness real and forbidden word vary with the scale. It therefore refutes a universal sufficient certificate, not any statement about one fixed real, and especially not \(\pi\).

Artifact: `TheoryLib/PiPositiveDecimalFactorEntropy/T78T78SquareSparseProjectedPhaseObstruction.lean`.

#### T79: restricted-denominator source audit (`literature-checked`)

T79 checks rational approximation with denominators involving powers of 2 and 5, repunit factors, multiplicative semigroups, algebraic S-units, Padé constructions, and BBP truncations against the exact short-sector/Vaaler quantifiers. No retained theorem simultaneously covers fixed \(\pi\), every large \(n\), all required \(r,j,h\), the strict neighborhood, the arithmetic mask, sign-changing coefficients, and an \(O(L_n)\) aggregate.

This is a negative result about the bounded pinned corpus, not a logical impossibility theorem.

Artifacts:

- [`work/theory/pi-positive-decimal-factor-entropy/library/t79/T79_RESTRICTED_DENOMINATOR_AUDIT.md`](../../theory/pi-positive-decimal-factor-entropy/library/t79/T79_RESTRICTED_DENOMINATOR_AUDIT.md)
- [`work/theory/pi-positive-decimal-factor-entropy/library/t79/SOURCE_MANIFEST.md`](../../theory/pi-positive-decimal-factor-entropy/library/t79/SOURCE_MANIFEST.md).

#### T97: certified finite long-sector census (`experiment`)

T97 exhaustively counts the complete T56 long-lag sector for \(2\leq n\leq12\) with certified decimal intervals and zero unresolved boundary cases. At the mandatory scales the ordered long-sector totals are \(2,0,0,0,2,0,0,0,4,0,2\). The sparse counts are useful calibration but prove no uniform estimate and provide no statistical sample of independent scales.

Artifact: [`work/theory/pi-positive-decimal-factor-entropy/library/t97/T97_LONG_SECTOR_CENSUS.md`](../../theory/pi-positive-decimal-factor-entropy/library/t97/T97_LONG_SECTOR_CENSUS.md).

#### T98: Champernowne boundary-scale obstruction (`experiment` plus elementary obstruction)

For the literal T56 sample length \(L_n=10^{\lfloor n/2\rfloor}\), every length-\(n\) Champernowne block among the first \(L_n\) starts crosses an integer-concatenation boundary for \(n\geq4\). Therefore the classical fixed-word, long-epoch normality mechanism has no vanishing boundary error at this scale and does not control the literal block-collision statistic or the complete C7 Fejér energy. This does not show that Champernowne fails the estimate by another method and says nothing about \(\pi\).

Artifacts:

- [`work/theory/pi-positive-decimal-factor-entropy/library/t98/T98_CHAMPERNOWNE_OBSTRUCTION.md`](../../theory/pi-positive-decimal-factor-entropy/library/t98/T98_CHAMPERNOWNE_OBSTRUCTION.md)
- historical construction: [Champernowne (1933)](https://doi.org/10.1112/jlms/s1-8.4.254).

## What is now known not to be enough

The following are not being treated as routes to a fixed-\(\pi\) proof without new input.

1. **Ordinary irrationality measure.** A bound \(\|q\pi\|\gtrsim q^{1-\mu-\varepsilon}\) is exponentially tiny when \(q\) is comparable to \(10^N\), while collision questions live at polynomial-in-\(N\) normalizations and require aggregate multiplicity control.
2. **Generic lacunary theorems.** Almost-everywhere pair correlation and square-function estimates validate scales but do not specialize to the single phase \(\pi\).
3. **Multiplier-10 recurrence alone.** Equation (2) transports rather than destroys a large Fourier coefficient. Invariant subsequential measures can satisfy \(\widehat\mu(10h)=\widehat\mu(h)\) without being Lebesgue.
4. **Bulk terminal-shell averages.** A sparse bad ray can be diluted unless the norm is pointwise, per-ray, Carleson-like, or an unnormalized positive energy.
5. **Coefficient magnitudes and stopping rules.** T56/T57 show that these cannot remove the terminal phase obstruction.
6. **Finite digit statistics.** T97 is an `experiment`; even exact certification through \(n=12\) supplies no asymptotic law.
7. **Normal deterministic comparators.** T98 shows that a known normality proof can be misaligned with the growing-word/growing-sample regime.
8. **Currently audited rational representations.** Zudilin's corrected version, the factorial series, and the retained Machin-like family do not meet the needed range through the available square-root-modulus machinery.

## The remaining genuinely pi-specific inputs

The open program goals are deliberately narrow.

- Near-return G11: control simultaneous intermediate resonances along one autocorrelation chain strongly enough to defeat the decimal preperiod obstruction.
- Near-return G19: synchronize one-row Fourier criteria across a positive-density triangular family of depths.
- Positive-entropy G14: prove the complete fixed-\(\pi\) short/long lag-sector estimate equivalent to the sparse C7 frontier.
- Long-lag G10: prove or refute T29's exact all-scale fixed-\(\pi\) width-weighted square-function premise.

Any serious next route must introduce a concrete arithmetic property of \(\pi\) and prove a quantitative bridge to one of these exact observables. A new identity for \(\pi\) is not enough. It must survive the following scale audit:

\[
\text{truncation error},\quad
\text{reduced modulus},\quad
\operatorname{ord}_q(10),\quad
\text{available orbit length},\quad
\text{frequency gcd},\quad
\text{short-arc occupancy/cancellation}.
\]

## Questions for independent expert review

1. **Strength of the terminal-ray condition.** For genuine empirical orbit measures, is the qualified UPRID/top-shell hypothesis in T67 strictly weaker than Weyl equidistribution, equivalent to it after the \(O(r/N)\) decimal-ray defect, or stronger? Please identify the weakest natural non-diluting norm that still feeds T55/T61.

2. **A realizable sparse-ray separator.** T67's sparse-ray counterexamples are abstract arrays. Can one realize an analogous separator as Fourier coefficients of a positive \(T_{10}\)-invariant probability measure, or does positive-definiteness eliminate the abstract obstruction? A theorem either way would materially sharpen the frontier.

3. **Walsh-to-Fourier bridge with carries.** Is there a sharp inequality comparing the exact decimal Walsh collision energy (1) with the terminal ordinary-Fourier ray energy, with constants uniform in depth and an explicit carry/boundary term? Can the carry term be made lower order at any useful \((m,N)\) scale?

4. **Fixed-\(\pi\) source of cancellation.** Is there any known arithmetic representation of \(\pi\) that yields exponential sums over \(10^j\) modulo a modulus whose square-root barrier is below the available orbit length? Candidates must be assessed after reduction, not at their common denominator.

5. **Beyond square-root-modulus bounds.** For the exact modular sums left in near-return T78/T79, can special modulus structure, prime-power stationary phase, sum-product estimates, or trace-function methods give cancellation for length only logarithmic in the modulus? If not, is there a theorem that cleanly rules out this parameter range for the relevant families?

6. **Short-sector cluster multiplicity.** Can runs/periodicity theory, Fine--Wilf, or additive combinatorics prove the exact all-short-sector aggregate needed by positive-entropy T56 from a weaker pointwise hypothesis? Please check whether the missing factor \(n\) is genuinely necessary by constructing or excluding a fixed infinite-word countermodel.

7. **T29 square function.** Does the all-scale fixed-\(\pi\) width-weighted square function conceal an equivalent, more arithmetic formulation (for example a weighted additive-energy count among repunits or a transfer-operator norm) that avoids explicit pointwise Fourier cancellation?

8. **Almost-everywhere closure.** Is the proof-sketch probability closure in long-lag T97 correct with the stated one-sided event, critical-band count, \(Q_0\)-uniformity, and constant \(940452800\)? Formalizing this would not solve the \(\pi\) case, but a flaw would invalidate the current random-model calibration.

9. **Route-specific obstruction checks.** Are the denominator reductions and eventual inequalities in near-return T78 and T79 correct? In particular, does any cancellation in the reduced numerator remove the claimed surviving prime-power factor, or is the unique minimum-valuation argument decisive?

10. **Alternative target with actual leverage.** Is there a strictly weaker fixed-\(\pi\) statement than (NR), (ENT), and (LL) that is both arithmetically approachable and provably improves the known Morse--Hedlund linear complexity baseline or certifies new decimal words? A useful answer should include the exact implication and the arithmetic theorem likely to prove its premise.

## Recommended review order

For a two-hour first pass:

1. read the three canonical problem files;
2. inspect T55 and T67 in the near-return program for the exact terminal obstruction;
3. inspect positive-entropy T56 for the literal residual estimate;
4. inspect long-lag T29 and program-local T97 for the square-function normalization and metric calibration;
5. inspect near-return T78/T79 only if evaluating arithmetic representations; and
6. treat all finite tables as `experiment`, not evidence of an asymptotic theorem.

## Authoritative local map

- Program state and open goals:
  - [`work/theory/pi-lacunary-near-return-sparsity/program.json`](../../theory/pi-lacunary-near-return-sparsity/program.json)
  - [`work/theory/pi-positive-decimal-factor-entropy/program.json`](../../theory/pi-positive-decimal-factor-entropy/program.json)
  - [`work/theory/pi-long-lag-block-collision-decay/program.json`](../../theory/pi-long-lag-block-collision-decay/program.json)
- Current strategy constraints:
  - [`work/theory/pi-lacunary-near-return-sparsity/DIRECTION.md`](../../theory/pi-lacunary-near-return-sparsity/DIRECTION.md)
  - [`work/theory/pi-positive-decimal-factor-entropy/DIRECTION.md`](../../theory/pi-positive-decimal-factor-entropy/DIRECTION.md)
  - [`work/theory/pi-long-lag-block-collision-decay/DIRECTION.md`](../../theory/pi-long-lag-block-collision-decay/DIRECTION.md)
- Accepted Lean library: `TheoryLib/PiLacunaryNearReturnSparsity/`, `TheoryLib/PiPositiveDecimalFactorEntropy/`, and `TheoryLib/PiLongLagBlockCollisionDecay/`.
- Axiom registry: [`audit/AxiomAudit.lean`](../../../audit/AxiomAudit.lean).

## Bottom line

The project has correctly isolated a small number of exact fixed-\(\pi\) frontiers and has eliminated several attractive but inadequate proof architectures. That is substantive progress in understanding what would constitute a proof. It is not yet progress toward a fixed-\(\pi\) estimate in the sense of a new upper bound, entropy lower bound, or digit theorem.

The most valuable expert response would be one of:

- a correction to a stated reduction or obstruction;
- a proof that one frontier is merely equivalent to the original genericity problem and should be retired;
- a natural positive-definite/Walsh reformulation that removes an artificial loss; or
- a concrete arithmetic theorem about \(\pi\) whose hypotheses quantitatively match one displayed fixed-\(\pi\) observable.

