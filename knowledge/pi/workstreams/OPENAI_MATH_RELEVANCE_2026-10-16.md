# Relevance of `openai/math` to Pi Lab

Review date: 2026-10-16 UTC; native-verification evidence updated 2026-10-17 UTC.
Review label: `literature-checked` for the source inventory and statement comparisons.
The proposed mathematical transfers below are `proof sketch`; no upstream theorem
is admitted to Pi Lab's `machine-checked` core by this review.
The completed external native check in section 3 is `machine-checked` evidence
for the explicitly repeated upstream statements under their native toolchain.

## Decision and scope

There is useful material. The highest-priority item is family **017**, which
states **the irrationality exponent of π is exactly 2** and supplies a substantial
Lean implementation. Its isolated native build, kernel recheck, literal
statement checks, and four axiom reports now pass as documented in section 3.
Porting that proof could discharge Pi Lab's external irrationality-measure premises and sharpen existing upper
bounds on constant and periodic digit runs. It does **not** establish a prescribed
digit occurrence, CW0, CW9, E, normality, or V1.

The next useful items are explicit finite Fourier-to-window counting lemmas
behind family **025**, and self-similar coding/dimension interfaces in family
**148**. Their hypotheses and the overlap with existing PI consumers matter more
than the catalogue headlines. Several other families clarify why measure-level
or generic-point statements do not settle a question about the fixed number π.

| Repository | Reviewed commit | Role |
| --- | --- | --- |
| [`openai/math`][upstream-snapshot] | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` | Source collection, including the October 12 revision |
| [`thepok/PI`][pi-snapshot] | `2ab024737878cd9f1567cc296ef53f051a5ff10b` | Target definitions, existing consumers and admission rules |

The review screened the **372 family descriptions and 719 manuscript abstracts**
in the [catalogue][catalogue] and [overview][overview], searched Lean scope notes
and relevant filenames, and followed the sources and implementation statements
listed below. Family 017 received a static import/declaration audit as well.
This is not a correctness review of all 719 papers or every lemma in the large
Lean library. No advertised decimal-normality, digit-universality, or BBP result
was found in that catalogue. The upstream [README][upstream-readme] itself
distinguishes results at different verification stages.

The acceptance target remains
[`Theory.PiDigits.V1`](../../../TheoryLib/PiDigits/T7Statements.lean): every finite
decimal word occurs contiguously, including leading-zero words and overlaps.
The authoritative research map remains [FRONTIER](../../../FRONTIER.md).

## 1. Family 017: the exact claim and its potential contribution

### Source statement

OpenAI, *The irrationality exponent of π is 2*, September 24, 2026,
[Theorem 1.1, `thm:main`][pi-paper-main], claims

$$
\forall \nu>2\;\exists Q(\nu)\;\forall p,q\in\mathbb Z,
\quad q\ge Q(\nu)\Longrightarrow
\left|\pi-\frac pq\right|\ge q^{-\nu}.
$$

The statement includes unreduced fractions and arbitrary integer numerators.
The paper explicitly makes the threshold **ineffective**. It does not give
a computable denominator cutoff, a uniform positive constant in
`|π-p/q| ≥ c/q²`, or bounded continued-fraction partial quotients. Its proof does
not use the earlier `7.103205334137…` irrationality bound as a premise.

The [actual implementation][pi-main] uses the ordinary `Real.pi` and exports:

| Lean declaration under `OAI.PiExponent` | Purpose |
| --- | --- |
| `pi_eventual_lower_bound` | Natural-denominator interface, convenient for PI |
| `pi_integer_eventual_lower_bound` | All-integer formulation |
| `pi_irrationalityExponent_eq_two` | Exact supremum characterization |
| `main` | The conjunction selected by the comparator |
| `flint_hills_summable` | Additional sine-series consequence |

The [series section][pi-series] also claims convergence of the classical
Flint–Hills series `Σ_{n≥1} 1/(n³ sin² n)`, with angles in radians. More
generally, for a,b>0 it gives convergence of `Σ_{n≥1} n^(−a)|sin n|^(−b)`
exactly when `a>max(1,b)`. The classical case has the additional Lean
declaration above; this does not make either series claim part of the selected
exponent comparator. These are useful related facts about π, without a decimal
word-occurrence conclusion.

In [Statement.lean][pi-statement], `EventualLowerBound x` means precisely:

```text
For every real ν > 2, there is Q : ℕ with Q ≥ 2 such that
for every p : ℤ and q : ℕ with q ≥ Q,
    q^(-ν) ≤ |x - p/q|.
```

This is a substantive candidate input to PI. File presence, an unconditional
theorem declaration, and a matching statement do not substitute for compiling
and auditing its proof; see section 3.

### Exact adapters into PI

**Status: `proof sketch`, conditional on a verified upstream lower bound.**
There are two different PI predicates, and conflating their strictness would
produce an incorrect adapter.

**Exponent at most two.**
[`T204ConstantRunBound.IrrationalityExponentAtMost`](../../../TheoryLib/PiQuantitativeBlockHitting/T204T204ConstantRunBound.lean)
uses a non-strict lower bound. Instantiate the upstream theorem at `ν=2+ε`
and convert `q^(-ν)` to `1/q^ν`. This gives
`IrrationalityExponentAtMost Real.pi 2` directly.

**Measure strictly below any B>2.**
[`T4.IrrationalityMeasureBelow`](../../../TheoryLib/PiLongLagBlockCollisionDecay/T4T4PublishedIrrationalityOnset.lean)
requires a witness `μ < B` and a **strict** lower inequality. Choose `μ=2`.
For the requested `ε>0`, apply the upstream bound at `ν=2+ε/2`. Since `q≥Q≥2`,

$$
\frac{1}{q^{2+\varepsilon}}
<\frac{1}{q^{2+\varepsilon/2}}
\le\left|\pi-\frac pq\right|.
$$

Thus the bound supplies PI's interfaces at **B=8 and B=9**, or any B>2.
It does **not** supply `IrrationalityMeasureBelow Real.pi 2`: that predicate
requires an exponent witness strictly less than two. In particular, using
`measureBelow_implies_exponentAtMost` with M=2 is the wrong route; use the direct
non-strict adapter instead.

### Consequences for existing consumers

All consequences in this subsection remain conditional on the upstream proof
being verified and integrated.

| Existing PI component | What the new input would supply | Remaining limitation |
| --- | --- | --- |
| [T4 published-irrationality interface](../../../TheoryLib/PiLongLagBlockCollisionDecay/T4T4PublishedIrrationalityOnset.lean) | Discharge the explicit `IrrationalityMeasureBelow Real.pi 8` source premise | Its collision-decay reductions remain conditional on their other premises |
| [T204 constant-run bounds](../../../TheoryLib/PiQuantitativeBlockHitting/T204T204ConstantRunBound.lean) | Use M=2 in the repaired zero-run and nine-run consumers | Upper bounds on runs, not their existence |
| [T36 periodic-window gap](../../../TheoryLib/PiPositiveDecimalFactorEntropy/T36T36DecimalPeriodicWindowGap.lean) | Use an effective-exponent premise at any `2+ε`, with an existential onset | No effective onset and no new block occurrence |
| [T14 digit changes](../../../TheoryLib/PiDigits/T14IrrationalityMeasureDigitChanges.lean) | Discharge its exponent-below-eight source premise | Its existing coefficient stays `1/log 8`; sharper checkpoints require a separate generalization |
| [T194 and the first open rung](FIRST_OPEN_PI_LEMMA.md#machine-checked-foothold-and-exact-remaining-correlation) | Supply the below-eight or below-nine premise for the adaptive central-return foothold | The selected target is adaptive; the rest of the same child's fresh block still needs a signed bound |

For constant runs, apply
`Theory.PiDigits.T204ConstantRunBound.zeroRun_eventually_bounded_of_nonneg`
with `Real.pi_pos.le`, and
`Theory.PiDigits.T204ConstantRunBound.nineRun_eventually_bounded`, both with M=2
and π's irrationality. Taking the maximum of their onsets gives

$$
\forall\varepsilon>0\;\exists N_\varepsilon\;\forall n\ge N_\varepsilon\;\forall L,
\quad
(\operatorname{ZeroRunAt}(\pi,n,L)\lor\operatorname{NineRunAt}(\pi,n,L))
\Longrightarrow L\le(1+\varepsilon)n.
$$

Here positions are zero-based. The coefficient improves from the
`6.103205334138+ε` coming from the safely rounded bound in the
[target specification](TARGET_SPECIFICATION_v1.md) to `1+ε`.
An ineffective `N_ε` cannot be turned into a certified finite search limit.
Use the repaired nonnegative-real zero-run theorem directly: T204's
`HypothesisForms` convenience consumers retain an invalid universal zero-run
contract over negative reals and are not the appropriate adapter.

For a period-p window of length L starting at a, T36's
`DecimalFactorComplexity.PeriodicWindowGap.effectiveIrrationality_periodic_window_gap`
uses the displayed denominator `q=10^a(10^p-1)`. After the required denominator
onset, the input at `2+ε` gives

$$
L\le(1+\varepsilon)a+(2+\varepsilon)p+1.
$$

Use the same epsilon slack for T36's strict inequality and the integer shift
from π to π−3 for its expansion witness. This concerns all sufficiently large
displayed denominators, not only reduced ones. Neither this estimate nor the
unchanged T14 digit-change bound determines which digits or words occur.

## 2. An explicit separator: exponent two is insufficient for V1

**Literature input: `literature-checked`; digit consequences: `proof sketch`.**
Let the Thue–Morse sequence satisfy

$$
t_0=0,\qquad t_{2k}=t_k,\qquad t_{2k+1}=1-t_k,
\qquad \xi=\sum_{k\ge0}t_k10^{-k}.
$$

[Bugeaud's theorem][bugeaud] gives **μ(ξ)=2**. Its decimal expansion uses only
0 and 1, so the one-digit word `2` never occurs. Also every three consecutive
Thue–Morse symbols contain an even/odd pair with different values; hence `000`
does not occur, and there are no nines. This already prevents CW0 and CW9.
PI previously records this example in its
[pathwise separator discussion](../results/negative/20260829-pathwise-cross-energy-heredity-separator.md).

The same obstruction survives finite-prefix evidence. If `0≤P<10^N` is an
integer written as exactly N digits, including leading zeros, `(P+ξ)/10^N`
has that fractional prefix and a 0/1 tail. Its exponent is
still two by invariance under nonzero rational affine transformations, but
the word consisting of N+1 copies of `2` is absent. This construction is a
reasoning consequence of the cited example, not a new result of `openai/math`.

Consequently, even a successful verification of family 017 does not meet
the reopening condition of
[`route-run-bounds`](../entries/route-run-bounds.md). The new result strengthens
the approximation input; a decimal target still needs additional information.
It also does not establish that π is badly approximable, so it cannot supply
the fixed positive Markov constant in the BA–ALA intersection problems.

This distinction must be stated carefully for exact identities. The exact
BBP series and Machin identities identify π; it would be false to say that
arbitrary word-avoiders satisfy those same identities. What has failed to
provide V1 is the known use of those identities and the weaker approximation,
valuation or unsigned-statistic consequences extracted from them. A future
target-sensitive consequence is not ruled out.

## 3. Formalization status, trust boundary and compatibility

The [family scope note][pi-scope] selects the full exponent-two statement.
The [comparator configuration][pi-comparator] points to
`OAI.NumberTheory.PiExponent.Main`, checks `OAI.PiExponent.main`, and permits
only `propext`, `Quot.sound`, and `Classical.choice`. It has
`enable_nanoda: false`; an independent Nanoda check is not enabled by this
configuration.

The [comparator challenge file][pi-challenge] deliberately ends in `sorry`:
it is a target specification. The solution is the separate implementation
module. Treating the challenge placeholder as a hole in the solution would
be an incorrect audit. Conversely, an allowed-axiom configuration alone is
not evidence that the comparator was run successfully.

The review's static traversal of `Main`'s local import graph found **869
PiExponent Lean files**, totaling **4,321,464 bytes**, with no missing local
imports. All files in that subtree were in the closure. External imports were
Mathlib modules and `Lean.Elab.Tactic.Omega`. A text scan found no occurrences
of `sorry`, `admit`, `native_decide`, `sorryAx`, explicit `axiom`, `unsafe`,
`implemented_by`, `extern`, `ofReduceBool`, `elab_rules`, or `macro_rules` in
that subtree. This is a useful initial check, **not** a kernel axiom audit,
semantic proof review, or build result.

Two scope details are easy to miss:

- `flint_hills_summable` is present in `Main.lean`, but the chosen comparator
  theorem does not include it. The scope note's exclusion of that consequence
  from the selected statement is therefore consistent with the implementation.
- At this snapshot, [formalization.yaml][formalization] has no PiExponent or
  irrationality-exponent-of-π entry, although the scope and comparator files
  exist; its global `review.status` is `unchecked`. The catalogue is not a
  substitute for checking the actual selected theorem and configuration.

| Dependency | `openai/math` | PI at the reviewed base |
| --- | --- | --- |
| Lean | [4.34.1][upstream-toolchain] | [4.30.0](../../../lean-toolchain) |
| Mathlib commit | [`d13f23b723b8a846827a245b89c10fc7d3f11612`][upstream-manifest] | [`c5ea00351c28e24afc9f0f84379aa41082b1188f`](../../../lake-manifest.json) |

A one-file copy of `Main.lean` cannot import the proof. The isolated native
validation package in [PR #12](https://github.com/thepok/PI/pull/12) uses the
PiExponent closure and its matching Mathlib without the upstream library's
unrelated dependencies. PI's pinned toolchain remains an acceptance requirement.

### Completed native verification, 2026-10-17

The [native workflow run](https://github.com/thepok/PI/actions/runs/39036618132)
at PI commit `eccc5666959284183b855442ff77eda04642484a` completed successfully
at 14:30:42 UTC. Its [verification job](https://github.com/thepok/PI/actions/runs/39036618132/job/117407671035)
records successful native compilation, the separate bundled `leanchecker`
environment recheck, and the final literal-statement/axiom gate. This review
downloaded the resulting artifact and checked its digest and report, rather
than inferring upstream verification from this documentation PR's green CI.

The pinned source is still `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
All 869 proof modules and all nine dependency pins were checked before and after
the final gate. The actual compiler was Lean 4.34.1. The
[literal gate](https://github.com/thepok/PI/blob/eccc5666959284183b855442ff77eda04642484a/workflows/verification/pi_exponent_upstream_20261016/PiExponentGate.lean)
repeats the natural- and integer-denominator approximation bounds using
`Real.pi`, the exact exponent-two supremum statement, and the Flint--Hills
summability statement. The checked `main` lower bound is

\[
\forall\nu>2\;\exists Q\ge2\;\forall p,q\in\mathbb Z,\quad
q\ge Q\Longrightarrow q^{-\nu}\le|\pi-p/q|.
\]

Each of the four transitive axiom reports contains exactly
`propext`, `Classical.choice`, and `Quot.sound`:

- `OAI.PiExponent.main`;
- `OAI.PiExponent.pi_eventual_lower_bound`;
- `OAI.PiExponent.pi_irrationalityExponent_eq_two`;
- `OAI.PiExponent.flint_hills_summable`.

The [artifact](https://github.com/thepok/PI/actions/runs/39036618132/artifacts/12103733632)
has ZIP SHA-256
`57138fa33a3d9251b72c23ec3642117c714a6c1b6f1e4f4c35f0fe1c2aa6e763`.
Its completed `report.json` has SHA-256
`1cf10d8347fa36350c02d64f57f7610d813c5a6e7a22fd35c7cadb3fa7cb6bbd`;
its `axioms.log` has SHA-256
`626e8b07aa2ff4c3f7bc2b52fe160e7270435b1473a9e7261358adf18fe7aba5`,
matching the report's recorded digest. The report phase is
`native statement and axiom checks passed`.

This is completed native `machine-checked` evidence for the explicit upstream
statements. Comparator and Nanoda were not run by this workflow. The proof is
not yet ported to PI's Lean 4.30.0 core, and this documentation update changes
no Lean declarations, axioms, dependencies, or target statements. Its
consequences for PI's exact predicates remain the adapters stated in section 1;
the decimal-occurrence and target-sign gaps in section 2 are unchanged.

### Concrete verification and integration tasks

1. Preserve the completed native run and its exact pins. To reproduce it, use
   the isolated driver in PR #12; a prepared report alone is not a passed run.
2. If the upstream Comparator protocol is required, run
   `lake env comparator ComparatorChallenges/PiExponent.json` from `lean/`
   using its pinned environment. The upstream
   [verification instructions][comparator-readme] require Comparator, Landrun
   and lean4export. This is a remaining check, not a result claimed here.
3. Decide between backporting the required closure to PI's pinned versions
   and a separately reviewed toolchain migration. Verify the statements against
   standard `Real.pi`, rational approximation and the exact PI predicates.
4. Only after the proof is accepted, implement the two adapters from section 1,
   register every supporting theorem in `audit/AxiomAudit.lean`, and run
   `pwsh workflows/verification/check.ps1`. A source scan cannot justify an
   unconditional PI theorem or an upgrade to the `machine-checked` label.

The existing historical irrationality bound and explicit-premise interfaces
remain useful while this work is pending.

## 4. Reusable components inside family 017

### The proof's π-specific mechanism

The [interpolation theorem][pi-interpolation], `geom:interpolation` (Theorem 2.1),
constructs full-rank packets of coefficients after the substitution
`Y=1+t`, `X_i=c_ji+u_i+log(1+t)` with weighted-simplex monomials.
Its assumptions include positive rational weights, coordinatewise distinct
centers, and the displayed volume inequalities
`K θ^m < 1` and `K (w₀/v₀) θ^m < 1`.

The significant order of choices is: fix the dimension and initial parameters;
choose successive coordinate weights with thresholds independent of the centers;
then choose the centers; only then let a sufficiently divisible polynomial
degree grow. Counting more coefficients than constraints is not a proof of
full rank at these special centers. The source supplies a substantial
multiplicity/geometry argument for that step.

The [determinant argument][pi-determinant] uses rational approximations to
the **exact periods `2π·i·j` of the exponential function**, with i²=−1 and
integer j. Thus it uses an
identity specific to π. A nonzero Gaussian-integer determinant after denominator
clearing gives an absolute-value lower bound. On the analytic side, repeated
Taylor degrees within one transverse-index group annihilate determinant terms;
the resulting saving involves sums of squared group sizes. Large transverse
indices instead supply small approximation-error factors. The
[parameter argument][pi-conclusion] balances these alternatives for each ν>2.

This is a useful method for logarithmic/period-carrier research. However,
the final bounds take absolute values. Neither exported irrationality bound
selects a decimal target, an approximation sign, a numerator residue, or PI's
same-child sector sign. The Taylor-index group counts are not PI's digit-block
collision energy.
Any proposed phase-sensitive extraction from the earlier expansion remains a
research question requiring a new, exact statement and the existing admission
tests; the paper does not supply that extraction.

### Direct decimal-prefix adaptation audit (2026-10-17)

The [follow-up interpolation audit](../results/negative/20261017-openai-math-interpolation-audit.md)
records a precise limit of the proposed adaptation. The source's parameter
inequalities are feasible exactly for approximation exponent greater than
two. Under avoidance of a fixed zero word, decimal-floor approximations
have effective exponent at most one plus the word length divided by the
prefix length, so they eventually fall outside that regime.

A separate Hermite interpolation proof also rules out obtaining a new
uniform power-of-two or power-of-five divisor merely from proportional
Taylor packets on all word-avoiding prefixes, even when the polynomial
degree grows after the prefix depth is fixed. Its exact degree and jet
conditions are stated, and the checker contains every finite input. This
does not exclude arithmetic special to the actual pi prefixes or an
estimate retaining the phases of the full determinant expansion. No
such target-dependent estimate is supplied by this audit.

### Smaller Lean modules worth knowing about

These are implementation references; their transfer to PI has not been compiled.

| Upstream file | Declaration or content | Possible use and constraint |
| --- | --- | --- |
| [Analysis/FiniteSpacing.lean][finite-spacing] | `sum_inv_sq_le_two_div_sq_indexed` | For d>0, finitely many values at least d with pairwise d-separation have inverse-square sum at most `2/d²`; useful for certified singular-sum bounds |
| [Analysis/DyadicSpacing.lean][dyadic-spacing] | `integerDistance_block_sum`; `summable_inverse_cube_integerDistance` | Converts a global Diophantine spacing hypothesis into a dyadic aggregate bound; does not establish that hypothesis for new sequences |
| [Approximation/Arithmetic.lean][arithmetic] | `cleared_det_norm_bound`; `cleared_det_log_bound_of_entries` | Tracks exact denominator clearing and lower bounds for nonzero determinants; nonvanishing and integrality must be proved |
| [Analysis/FiniteDeterminantCollision.lean][finite-collision] | `finite_collision_bound` | Finite multilinear expansions and repeated-row cancellation |
| [Analysis/CollisionOccupancy.lean][collision-occupancy] | `nat_occupancy_square_lower_bound` | A finite occupancy/Cauchy–Schwarz estimate, without digit-distribution content |

For example, `integerDistance_block_sum` assumes
`‖qα‖ ≥ c q^(1−ν)` for **every positive integer q**, with c>0 and ν>1. For
every integer K≥1 it gives

$$
\sum_{K\le q<2K}\frac{1}{\|q\alpha\|^2}
\le\frac{4}{\bigl(c(2K)^{1-\nu}\bigr)^2}.
$$

For ν<5/2 the weighted dyadic bounds yield the summability result used in the
[sine-series consequence][pi-series]. This is a statement about ordinary
integer multiples and aggregate closeness. It provides no lower recurrence or
prescribed hit for the lacunary sequence `{10^n π}`.

The released [reasoning summary][pi-trace], Part II §45, pages 39–40, is useful
as a reading guide. It separates an earlier claimed `62/25` approach from the
later exponent-two argument, which does not assume that earlier bound. Its
reusable audit lessons are to account for every denominator/factorial cost,
prove nonvanishing separately from dimension counts, test overgeneralizations
against Liouville examples, and preserve the order of parameter choices.
The summary is research history, not an additional verification certificate.

## 5. Family 025: finite Fourier bounds imply window counts

The *Short Egyptian fractions* headline hides relevant helper results.
In [RationalDiscrepancy.lean][rational-discrepancy],
`OAI.Problem337.rational_small_interval_of_fourier` and its `_finset` version
concern a finite family of **rational** phases `x_ω ∈ [0,1)`. Writing N for its
size, they assume

$$
0<\delta\le\frac1{65536},\qquad
\left|\sum_\omega e^{2\pi i\ell x_\omega}\right|\le N\delta^3
\quad\left(1\le\ell\le\lfloor\delta^{-4}\rfloor\right)
$$

and conclude `#{ω : x_ω < δ} ≥ δN/2`. For N>0 this forces a hit. No common
denominator is required as an input; the implementation constructs one.

The residue variant
`OAI.ShortEgyptian.indexed_residue_discrepancy` in
[EmpiricalDiscrepancy.lean][empirical-discrepancy] takes a nonempty family
`v_i ∈ ZMod q`, q>0, `0<δ≤1/256`, and H≥1 with `1≤2Hδ⁴`. If all normalized
character averages for `1≤ℓ≤H` have norm at most δ³, it concludes

```text
#{i : val(-v_i) < δq} ≥ δN/2.
```

**The count is on negative residues.** Preserve that convention, or explicitly
replace v with −v. Frequencies are interpreted modulo q; H≥q would include
the trivial character at ℓ=q and make the smallness premise impossible.
The related [WindowDiscrepancy][window-discrepancy] and
[FourierDiscrepancy][fourier-discrepancy] files expose smoothing and explicit
window-error budgets. These are potential interfaces for finite residue
certificates, not estimates already proved for π.

PI already has real-phase consumers in
[T27FiniteExponentialCylinderCoverage](../../../TheoryLib/PiDigits/T27FiniteExponentialCylinderCoverage.lean),
including `decimalCylinder_covered_of_firstFrequencyBound` and
`pi_everyLengthKWord_occurs_of_finiteExponentialBounds`, and in
[T3FiniteFourierLowerDensity](../../../TheoryLib/PiPositiveLowerBlockDensity/T3T3FiniteFourierLowerDensity.lean).
Consequently the upstream lemmas are comparison material, not a missing V1
implication. Import only if their exact constants or finite-residue interfaces
serve a particular task better. Replacing irrational π phases with rational
ones would require an explicit phase-error bound and a cylinder-boundary
margin. The missing cancellation hypotheses still need to be proved for π.

## 6. Family 148: self-similar coding and dimension

The [scope note][selfsimilar-scope] and
[main statement][selfsimilar-statement] describe a finite stationary system
`φ_i(x)=r_i x+t_i`, with `0<|r_i|<1`, positive weights p_i summing to one,
and a self-similar probability measure μ. The claimed formula is

$$
\underline{\dim}_{H}\mu
=\min\left(1,\frac{h_{\mathrm{RW}}}{\chi}\right),
\qquad \chi=-\sum_i p_i\log|r_i|.
$$

The entropy rate counts complete random affine compositions, including slopes
and offsets; it and χ use the same logarithmic base. The main statement permits
exact overlaps and unequal or signed
ratios. The [attractor corollary][selfsimilar-corollaries] additionally requires
**no exact overlaps** and gives `dim_H K=min(1,s)` for the similarity dimension
specified by `Σ_i |r_i|^s=1`. Neither is an absolute-continuity assertion.

Useful implementation locators under `lean/OAI/MeasureTheory/SelfSimilar/` are
[Main.lean][selfsimilar-main] (`OAI.EntropyRateDimension.entropy_rate_dimension`),
[AttractorFormula.lean][attractor] (`OAI.CorSetReference.cor_set`),
[Coding.lean][coding] (infinite coding sums and geometric bounds), and
[NoOverlaps.lean][no-overlaps] (the complete-map injectivity convention).
The small [DigitSumset.lean][digit-sumset] counting bound is also potentially
reusable. These implementation sources and comparator statements were inspected,
but their full dependency closures were not compiled or axiom-audited here.

### A safe connection to forbidden words

**Status: `proof sketch`; elementary comparison, not a new PI result.**
For a forbidden word w of length k≥1, set `B=10^k`, `m=value(w)` and
`D={0,…,B−1}\{m}`. The maps `φ_d(x)=(x+d)/B` code numbers whose **aligned**
length-k blocks omit w. Distinct finite words give distinct affine maps: the
slope determines the length and the base-B integer determines the digits.
The corresponding dimension is

$$
\frac{\log(B-1)}{\log B}
=\frac{\log(10^k-1)}{k\log 10}<1.
$$

The full overlapping word-avoidance set is contained in this aligned-block
attractor, with the usual endpoint convention accounted for. The sets need not
be equal: for k≥2, concatenating allowed blocks can create w across their
boundaries (for example, `10` followed by `01` creates the forbidden word `00`).
The formula therefore gives a coarse upper bound, not the exact SFT/Perron
dimension of the full forbidden language. The upper bound already follows
from covering with `(B−1)^n` intervals of length `B^(−n)`; it is not a reason
to import the entire new dimension theorem.

### What remains missing for P1 and the pruning program

- [T212](../../../TheoryLib/PiQuantitativeBlockHitting/T212T212AvoidanceDimensionAlignment.lean)
  retains a graph/SFT/Perron dimension input. A stationary full-shift IFS theorem
  does not directly identify the overlapping forbidden-word SFT.
- [T219/T220](../entries/T220.md) use prefix-dependent or nonstationary pruning,
  which is not automatically a finite stationary IFS.
- [T227](../entries/T227.md) and
  [P1](OPEN_PROBLEMS.md) need the BA–ALA intersection and compatibility with
  sparse prescribed packets. Dimension of the unpruned attractor supplies
  neither bad approximability nor a **single positive Markov constant κ chosen
  before branching and retained throughout the construction**.
- Dimension below one or measure zero does not exclude the particular point π.

Family 148 is useful for coding and benchmark models. It does not discharge
those inputs, solve P1, or provide a new active route to V1.

## 7. Other relevant families and their exact boundaries

### Family 022: inhomogeneous approximation and the fixed-point gap

The [weak inhomogeneous Duffin–Schaeffer manuscript][duffin-schaeffer],
`thm:main`, fixes a real shift γ and a finite-valued nonnegative ψ. Divergence
of `Σ_q φ(q)ψ(q)/q` implies `‖qx−γ‖<ψ(q)` infinitely often for
**Lebesgue-almost every x**. Numerators are unrestricted; this is not the
stronger coprime-numerator assertion. No rate is supplied, and the exceptional
null set may depend on γ and ψ. No family-022 Lean formalization is advertised
in the reviewed catalogue.

A precise decimal specialization illustrates the boundary. For a length-k
word of value m, choose `γ=(m+1/2)/10^k` and `δ=1/(2·10^k)`. Set `ψ(q)=δ`
for `q=10^n`, n≥1, and zero otherwise. Since `φ(10^n)/10^n=2/5`, the sum
diverges. The conclusion gives infinitely many visits to that cylinder's open
interior for almost every x; a countable intersection handles all words.
**It does not permit substituting x=π.** Allowing an arbitrary prescribed shift
does not remove the exceptional-set problem for the prescribed point.

### Family 084: all centers, but a constructed target set

The [general geometric-progression paper][geometric-avoidance] constructs,
for each fixed `r∈(0,1)` and `0<η<1`, a compact `E⊆[0,1]` of measure
greater than `1−η` such that for every real x and nonzero s, some
`x+s r^n`, n≥1, lies outside E. It genuinely has an all-center conclusion.
Its finite-scale random tests, boundary stability and deterministic repair of
exceptional centers are potentially useful methodology.

The set E is constructed by the theorem; it cannot be replaced by a prescribed
decimal cylinder or word-avoidance set. The progression contracts, unlike
`{10^n π}`. Substituting r=1/10 does not fix either mismatch. Moreover,
[the Lean scope][dyadic-scope] covers only the **dyadic companion r=1/2**,
via `OAI.Problem310.dyadic_affine_avoidance`, not the whole family headline.
The implementation [GlobalFromPeriodic.lean][global-from-periodic] contains
`avoidance_of_periodic_hitting`, a possible finite-to-global reference.

### Metric and Fourier families worth distinguishing

| Family and source | Supplied object | Why it does not provide the PI input |
| --- | --- | --- |
| [145: multiple mixing][mixing] | Mixing of all finite orders for an invertible mixing probability-preserving transformation | A measure-correlation statement does not certify the selected π orbit. The decimal map is also noninvertible; a natural extension would still leave the fixed-point gap |
| [154: pointwise multiple ergodic averages][pointwise] | Almost-everywhere convergence for a fixed tuple of bounded functions in an invertible mixing system | The exceptional set can depend on the system and tuple. No family-154 formalization is advertised, and no π-genericity input is supplied |
| [153: Bernoulli convolutions][bernoulli] | An arithmetic classification of random ±1 series laws by an infinite approximation condition | The parameter controls a probability law, not whether π belongs to a particular support. The criterion is not a finite membership algorithm; no family-153 formalization is advertised |
| [075: Fourier convergence in L log L][fourier-convergence] | Almost-everywhere convergence of ordinary Fourier partial sums of a function | This is different from cancellation of `Σ_{n<N} exp(2πih10^nπ)` at a fixed π |

For family 153, dimension, absolute continuity, and fixed-point membership
are distinct questions. At contraction 1/10, the binary-digit measure already
has an elementary small-dimensional support; knowing its singularity does not
exclude π from it. For 145/154, proving that a measure is mixing does not prove
that a named point is generic for that measure.

### Other screened overlaps

The following catalogue matches were checked for relevance and should not be
promoted into new PI routes without a concrete additional theorem. The source
for the family descriptions is the pinned [catalogue][catalogue].

| Families | Reason for not pursuing them as supplied PI inputs |
| --- | --- |
| 005, Catalan irrationality | A different constant; useful historical inspiration for 017, not a π-digit conclusion |
| 007, multiplicative two-point correlations; 023, cubic Gauss-sum moments | Different arithmetic sequences and averaging variables; π's digits are not supplied with those hypotheses |
| 015, torus-packet equidistribution | Averages over arithmetic packets of orbits, not the single decimal orbit |
| 073, Falconer distances | Positive measure of a distance set does not identify a prescribed point |
| 076, ultraflat Littlewood polynomials | Constructs signs at each length; does not control π's prescribed signs |
| 077–080, restriction/smoothing/convergence | Different oscillatory operators; no identified transfer to the required lacunary sums |
| 109, integer multiplication; 130, Fourier-transform algorithms | Computation of finite quantities does not prove cancellation or infinite word occurrence; no practical PI drop-in was identified |
| 144, 146, 150, 152, other dynamics | Different dynamical systems or model constructions, with no identification of π's orbit |
| 159, arithmetic progressions; 182, polynomial-difference avoidance | Configurations in sets of positions do not force arbitrary adjacent digit words |
| 242, single-fold Diophantine representation | Re-encodes existence questions without solving the resulting π-specific obligations |

Filename matches also need semantic checking: upstream
`NumberTheory/TotientAsymptotic/PublishedNormality.lean` concerns an
`IsNormalPrime` predicate, not base-ten normality. Jacobsthal's
`AllLabelDiscrepancy.lean` belongs to a prime-divisor state system and does not
establish PI's ALA property.

## 8. Priority and reopening conditions

The practical next action is **validate family 017 and its exact adapter**,
then assess the cost of a compatible port. That could replace a real external
premise in the verified core. The smaller spacing or discrepancy lemmas are
worth extracting only when a particular proof needs their exact interface;
PI already has strong Fourier consumers.

For progress on V1 itself, the missing result remains one of the target-signed
inputs in [FIRST_OPEN_PI_LEMMA](FIRST_OPEN_PI_LEMMA.md). For example, the direct
flexible-horizon route asks, for each `q=10^k`, k≥3, and each prescribed A<q,
for an N≥q satisfying

$$
\operatorname{Re}(\operatorname{primitiveBoundaryFourierSum}(q,A,N))
\ge-\frac{122091}{200000}.
$$

The existing derivation of sufficiency is labelled `proof sketch` there.
The alternative T189 route needs an unbounded compatible selector of the same
child with both positive fresh surplus and positive combined capital. Neither
an approximation lower bound, a finite Fourier consumer, an attractor dimension
formula nor an almost-everywhere theorem provides either input.

No closed route is reopened by this review. Reopening requires the exact
π-specific target/sign statement, a separator on which that statement fails,
and its connection to a prescribed hit or the literal same-child inequality.
That preserves the value of the new source without confusing stronger
irrationality information with a proof of digit occurrence.

## Source links

Upstream links below pin the reviewed commit rather than a moving branch.
For manuscript attribution, use the author/date/title and citation block in
the [family-017 manuscript directory][pi-paper-citation]. The Bugeaud reference
is a separate published primary source, already used in PI.

[upstream-snapshot]: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a
[pi-snapshot]: https://github.com/thepok/PI/tree/2ab024737878cd9f1567cc296ef53f051a5ff10b
[catalogue]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/CONTENTS.md
[overview]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/overview.tex
[upstream-readme]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/README.md
[pi-paper-main]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex
[pi-paper-citation]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/README.md
[pi-interpolation]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/interpolation.tex
[pi-determinant]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/determinant.tex
[pi-conclusion]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/conclusion.tex
[pi-series]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/series.tex
[pi-main]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Main.lean
[pi-statement]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Statement.lean
[pi-scope]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/017.md
[pi-comparator]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/PiExponent.json
[pi-challenge]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/PiExponent.lean
[formalization]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/formalization.yaml
[upstream-toolchain]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/lean-toolchain
[upstream-manifest]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/lake-manifest.json
[comparator-readme]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/README.md
[pi-trace]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/reasoning_traces/irrationality-exponent-of-pi.pdf
[bugeaud]: https://aif.centre-mersenne.org/articles/10.5802/aif.2666/
[finite-spacing]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/FiniteSpacing.lean
[dyadic-spacing]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/DyadicSpacing.lean
[arithmetic]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/Arithmetic.lean
[finite-collision]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/FiniteDeterminantCollision.lean
[collision-occupancy]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionOccupancy.lean
[rational-discrepancy]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/EgyptianFractions/RationalDiscrepancy.lean
[empirical-discrepancy]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/EmpiricalDiscrepancy.lean
[window-discrepancy]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean
[fourier-discrepancy]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FourierDiscrepancy.lean
[selfsimilar-scope]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/148.md
[selfsimilar-statement]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SelfSimilar.lean
[selfsimilar-corollaries]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SelfSimilarCorollaries.lean
[selfsimilar-main]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Main.lean
[attractor]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/AttractorFormula.lean
[coding]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Coding.lean
[no-overlaps]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/NoOverlaps.lean
[digit-sumset]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/DigitSumset.lean
[duffin-schaeffer]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-weak-inhomogeneous-Duffin-Schaeffer-conjecture-September-25-2026/build/sections/introduction.tex
[geometric-avoidance]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/01-introduction.tex
[dyadic-scope]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/084.md
[global-from-periodic]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean
[mixing]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/145.md
[pointwise]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Pointwise-Multiple-Ergodic-Averages-for-Mixing-Transformations-October-4-2026/build/sections/introduction.tex
[bernoulli]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026/build/main.tex
[fourier-convergence]: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/075.md
