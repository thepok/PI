# RA-0002 — exact sufficient-condition frontier to canonical V1

Agent: `pro-20260821T194452Z-gpt56pro-7f3c`

This is a theorem-level repository audit. `machine-checked` below means an exact
Lean declaration already present in `TheoryLib/`; this document, the graph, and
the countermodel introduce no new theorem and do not prove V1.

## Result

Canonical decimal disjunctivity of π remains open.

The smallest direct Fourier sufficient predicate currently encoded is
`Theory.PiDigits.ExactNaturalScaleResonance.PiNaturalScaleCancellationExact`
in
`TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean`.
It requires, separately for each positive word length, one finite prefix with
simultaneous cancellation through frequency `2 * 10^k`, and
`piNaturalScaleCancellationExact_implies_canonicalV1` closes it directly to V1.

The best bounded next formal task is the already-open `GP-0002`, not a new task:
package the exact contrapositive of T17 so that a power-of-ten Diophantine
premise plus an eventual strict upper bound for T17's precise aggregated Fourier
quantity implies `C1`. This is narrower than “prove V1”, adds no analytic claim,
and isolates the real quantitative obligation.

The dependency graph is [`frontier.dot`](frontier.dot). The explicit
appearance-ratio falsification is [`COUNTERMODEL.md`](COUNTERMODEL.md), and
source blobs plus verification scope are in
[`VERIFICATION.md`](VERIFICATION.md).

## Trust boundary and central-audit caveat

Status vocabulary:

- **machine-checked:** exact declaration in the current `TheoryLib/`.
- **external premise:** source-shaped proposition retained as a hypothesis; not
  independently proved by this audit.
- **open:** no checked inhabitant/result for fixed π.
- **proof sketch:** proposed composition not promoted to `TheoryLib/`.

Concurrent task `RA-0003` found a selective central `#print axioms`
registration gap for representative T1–T17 endtheorems, including T17's final
obstruction theorem. The subsequent completed task `GP-0006` registered all
nine endpoints in `audit/AxiomAudit.lean` and recorded a passing current
repository gate. This repaired audit coverage without changing any theorem,
proof, premise, or the conjectural status of C1/V1.

## 1. Exact target and checked endpoints

### Canonical V1

Path: `TheoryLib/PiDigits/T7Statements.lean`

Declaration: `Theory.PiDigits.V1`

```lean
def V1 : Prop :=
  ∀ s : List (Fin 10), ∃ n : ℕ,
    ∀ i : ℕ, ∀ hi : i < s.length,
      piDigit (n + i) = s.get ⟨i, hi⟩
```

Leading-zero words, overlaps, and the empty word are included.

Path: `TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean`

Declaration: `Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense`

This machine-checked theorem identifies V1 with density of the exact orbit
`fract (10^n * π)`.

### Quantitative endpoint C1

Path:
`TheoryLib/PiQuantitativeBlockHitting/T1PiQuantitativeBlockHitting.lean`

Declarations:

- `Theory.PiDigits.QuantitativeBlockHitting.C1`
- `Theory.PiDigits.QuantitativeBlockHitting.C1_implies_canonicalV1`

```lean
∃ C : ℕ, 1 ≤ C ∧
  ∀ k : ℕ, 1 ≤ k →
    CoversAllLengthKWordsBy piDigit k (C * k * 10^k)
```

`C1` is stronger than V1 because it imposes one common
`O(k * 10^k)` full-containment deadline.

### Entropy endpoint

Path:
`TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean`

Declarations:

- `canonicalV1_iff_pi_maximalFactorComplexity`
- `pi_factorEntropy_eq_logTen_iff_canonicalV1`

Maximal factor complexity/entropy is equivalent to V1, not an already-proved
weaker premise.

## 2. Fourier/cancellation routes

### T19: smallest direct checked Fourier frontier

Path:
`TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean`

Declaration:
`Theory.PiDigits.ExactNaturalScaleResonance.PiNaturalScaleCancellationExact`

```lean
∀ k : ℕ, 1 ≤ k →
  ∃ N : ℕ, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * 10^k →
      ‖exponentialSum piFractionalOrbit N h‖ / (N : ℝ) <
        1 / (24 * (10 : ℝ)^k) +
        1 / (12 * ((10 : ℝ)^k)^3)
```

Checked conclusion:
`piNaturalScaleCancellationExact_implies_canonicalV1`.

Open edge, status **open analytic premise**: prove the displayed predicate for
`Theory.PiDigits.T27.piFractionalOrbit`.

Why existing results do not close it:

- `TheoryLib/PiDigits/T26WeylCancellationV1.lean` closes full fixed-frequency
  Weyl cancellation to V1, but that premise is stronger and also open.
- T27/T28 give additive gaps only on moving selected frequencies and moving
  first-occurrence cutoffs.
- T29's conditional saving remains a fixed number below `1`; T19 requires
  `O(10^-k)` normalized cancellation simultaneously through `2 * 10^k`.

### T3 finite-certificate route to C1

Path:
`TheoryLib/PiQuantitativeBlockHitting/T3UniformPiAnalyticCover.lean`

Declarations:

- `PiFiniteFrequencyCertificate`
- `UniformPiFiniteFrequencyCertificates`
- `uniformPiFiniteFrequencyCertificates_implies_C1`
- `explicit_uniform_pi_finiteFrequencyBounds_imply_C1`

For each `k`, a certificate uses `N,H,B`, `0 < N`, a common bound at all
nonzero `|h| ≤ H`, and

```text
H*B + N / ((H+1) * (10^-k)^2) < N.
```

Uniform certificates with `N ≤ C*k*10^k` imply C1. This is quantitative and
therefore stronger than T19's one-prefix-per-scale route to V1.

### T17 obstruction and the exact post-T17 target

Path:
`TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`

Definition:

```lean
def PowerTenDiophantine (x : ℝ) (mu A : ℕ) : Prop :=
  ∀ t : ℕ, A ≤ t → ∀ p : ℤ,
    1 / (10 : ℝ)^(mu*t) ≤
      |x - (p : ℝ) / (10 : ℝ)^t|
```

Checked theorem:
`not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine`.

Assumptions:

```text
1 ≤ mu
PowerTenDiophantine π mu A
¬ C1
```

For every `C,K` with `1 ≤ C` and `1 ≤ K`, it returns a
`k ≥ K`, `k ≥ A`, `k ≥ 1`, using exactly

```text
q = 10^k
D = C*k*q
N = D-k+1
r = (mu-1)*D+1
M = 2*10^(2*k+r),
```

and proves

```text
N/(2*q) ≤
  aggregatedFourierSum piFractionalOrbit N q M.
```

`aggregatedFourierSum` is defined in
`TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean`.

#### Recommended bounded theorem (`GP-0002`)

Status: **proof sketch**, already assigned.

A logically sufficient exact interface is:

```lean
theorem eventual_exact_aggregatedFourier_smallness_implies_C1
    (mu A : ℕ) (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (C K : ℕ) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hsmall : ∀ k : ℕ, K ≤ k →
      let q : ℕ := 10^k
      let D : ℕ := C*k*q
      let N : ℕ := D-k+1
      let r : ℕ := (mu-1)*D+1
      let M : ℕ := 2*10^(2*k+r)
      aggregatedFourierSum piFractionalOrbit N q M <
        (N : ℝ) / (2*q)) :
    C1
```

Proof: assume `¬ C1`, instantiate T17 with the same `C,K`, and contradict its
lower bound with `hsmall k`. No finite-small-`k` repair is needed: T17 produces
a bad `k` beyond every positive `K`.

Remaining open edges after this package:

1. **External/number-theoretic premise**
   `PowerTenDiophantine Real.pi mu A`.
   `T35T35OversampledBBPGridStability.lean` conditionally derives the
   `mu = 8` form from the explicit source-shaped premise
   `IrrationalityMeasureBelow Real.pi 8`; that source premise is not discharged
   in Lean. Existing task `GP-0001` owns this bridge.
2. **Pi-specific analytic premise**
   prove the strict aggregate upper bound for one fixed `C` and all
   sufficiently large `k`.

T14 gives a finite dichotomy, T17 gives only the lower obstruction under
`¬ C1`, T27–T29 do not control the entire nonnegative aggregate through `M`,
and BBP recurrences do not supply cancellation.

## 3. Appearance-ratio route

Path:
`TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean`

Checked declaration:
`pi_manyLastFirstOccurrenceLinearGapFrequencies_spec`.

For every `m ≥ 3`, at least `10^m/16` frequencies have additive gap

```text
piFactorComplexity(m) / 32
  ≤ L_m - |S_h(L_m)|,
```

where `L_m = piLastFirstOccurrencePrefixLength m`.

Path:
`TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean`

Checked conditional declaration:
`pi_manyLastFirstOccurrenceRelativeGapFrequencies_spec`.

Assumptions for one `m,C`:

```text
3 ≤ m
0 < C
L_m ≤ C * piFactorComplexity(m).
```

Conclusion: at least `10^m/16` selected frequencies satisfy

```text
|S_h(L_m)| / L_m ≤ 1 - 1/(32*C).
```

Open edge, status **open**: a uniform ratio of the form

```text
∃ C : ℕ, 0 < C ∧
  ∀ m : ℕ, 3 ≤ m →
    L_m ≤ C * piFactorComplexity(m).
```

Even this does not imply V1. It controls only a moving subset with a fixed
relative saving and does not imply T19 or maximal factor complexity.

Falsification check: the constant-zero stream has `p(m)=1` and `L(m)=1` for
every positive `m`, so the strongest ratio holds with `C=1`, yet the word `[1]`
never occurs. See `COUNTERMODEL.md`.

## 4. Fixed-sixteen-return route

Path:
`TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean`

Definition:

```lean
def FixedSixteenReturn : Prop :=
  circleMul 16 (piCircleOrbit 0) ∈ piOrbitClosure
```

Checked declarations:

- `fixedSixteenReturn_iff_metric`
- `v1_implies_fixedSixteenReturn`
- `fixedSixteenReturn_implies_piOrbitClosure_eq_univ`
- `piOrbitClosure_eq_univ_implies_v1`
- `v1_iff_fixedSixteenReturn`

The metric form is

```text
∀ epsilon > 0, ∃ n,
  dist(circleMul 16 (piCircleOrbit 0), piCircleOrbit n) < epsilon.
```

The reverse route retains the explicit premise

```text
Dense (tenSixteenOrbit (piCircleOrbit 0)).
```

Open edges: that joint-orbit density premise and `FixedSixteenReturn` itself.
Under the density premise, the checked equivalence makes the return exactly
V1-strength, not a weakening.

`T70T70EmpiricalRigidityBridge.lean` retains explicit empirical-measure,
ergodicity/invariance, nonsingularity, support, and Furstenberg-source
hypotheses; it constructs no measure satisfying them for π.

## 5. BBP forced-orbit route

### Checked arithmetic and forcing

Paths:

- `T104T104BBPSeriesIdentity.lean`
- `T106T106BBPForcedOrbit.lean`

under `TheoryLib/PiQuantitativeBlockHitting/`.

Load-bearing declarations include:

- `bbpRealTerm_hasSum_pi`
- `sampledBBPOrbit_succ`
- `sampledBBPError_lt_geometric`
- `summable_sampledBBPError`
- `sampledBBPForcing_eq_error_coboundary`
- `fract_sampledBBPOrbit_add_error`

They prove the BBP identity, the exact recurrence

```text
v_(N+1) = fract(10*v_N + eta_N),
eta_N = 10*e_N - e_(N+1),
fract(v_N + e_N) = fract(10^N*pi),
```

and geometric/summable coordinate error.

### T107: Weyl transfer

Path:
`TheoryLib/PiQuantitativeBlockHitting/T107T107BBPWeylTransfer.lean`

Checked declarations:

- `summable_norm_phase_pi_sub_phase_sampledBBP`
- `realWeylCancellation_iff_of_summable_phase_discrepancy`
- `realWeylCancellation_sampledBBP_iff_pi`
- `sampledBBP_weylCancellation_implies_canonicalV1`

Exact endpoint:

```text
RealWeylCancellation sampledBBPOrbit
  ↔ RealWeylCancellation (fun N => 10^N * π).
```

Open edge: prove either side. T107 transfers cancellation; it proves neither.

### T108: circle-density transfer

Path:
`TheoryLib/PiQuantitativeBlockHitting/T108T108BBPCircleDensityTransfer.lean`

Definition:

```lean
def SampledBBPOrbitCircleDenseArbitrarilyLate : Prop :=
  ∀ y : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
    ∃ n : ℕ, N ≤ n ∧
      dist ((sampledBBPOrbit n : ℝ) : UnitAddCircle) y < r
```

Checked declarations:

- `tendsto_circleDist_sampledBBP_pi_zero`
- `sampledBBP_circleDense_iff_pi_circleDense`
- `sampledBBP_circleDense_implies_canonicalV1`
- `canonicalV1_iff_sampledBBPOrbitCircleDenseArbitrarilyLate`

Thus sampled-BBP arbitrarily-late circle density is exactly V1-equivalent.
Open edge: prove that density predicate. It is a reformulation, not a shortcut.

### T105/T109: code and symbolic packaging

Paths:

- `T105T105BBPCodeCoverage.lean`
- `T109T109BBPSymbolicPackaging.lean`
- `T37T37FloorSymbolicBridge.lean`

under `TheoryLib/PiQuantitativeBlockHitting/`.

Checked declarations include:

- `bbpPartial_arbitrarilyLateCode_iff_pi`
- `eventually_bbpBlockCode_eq_piCylinderCode`
- `pi_eventually_bbpPartial_code_eq_blockAt_wordValue`
- `decimalBlockCode_pi_eq_piCylinderCode_val`
- `decimalBlockCode_pi_eq_blockAt_wordValue`

T109's same-position arithmetic-to-symbolic identities retain the explicit
external premise `IrrationalityMeasureBelow Real.pi 8`.

Exact open occurrence edge:

```text
∀ m : ℕ, ∀ b : ℤ,
  0 ≤ b → b < 10^m →
    ArbitrarilyLateCode
      (fun N => bbpRealPartial (7*N)) m b.
```

T105/T109 transfer prescribed-code recurrence but do not produce it.
A recurrence formula, summable coboundary, vanishing coordinate error, or exact
symbolic identity does not imply mixing, density, or target-cylinder visits.

## 6. Other direct sufficient predicates

### Positive lower block density

Path:
`TheoryLib/PiPositiveLowerBlockDensity/T1PiPositiveLowerBlockDensity.lean`

Declarations:

- `PiPositiveLowerBlockDensity`
- `piPositiveLowerBlockDensity_implies_T7V1`

Exact open premise:

```text
∀ nonempty decimal word w,
  0 < liminf_N blockFrequency(piDigit,w,N).
```

This is substantially stronger than one occurrence.

### Long-lag collision decay

Paths:

- `TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean`
- `TheoryLib/PiLongLagBlockCollisionDecay/T3T3CollisionDecayImpliesDisjunctive.lean`

The open canonical premise is

```text
∀ s : ℝ, 0 < s → s < 1 →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ m N ≥ 1,
      R_pi(m,N) ≤ C * (N + N^2 * 10^(-s*m)).
```

Checked theorem
`piLongLagBlockCollisionDecay_implies_everyFiniteDecimalWordOccurs`
closes it to V1 via positive lower block density. The premise is much stronger
than T19.

## 7. Ranking by required new mathematical strength

| Rank | Route | Remaining new π-specific content |
|---:|---|---|
| 1 | T19 exact natural-scale cancellation | One finite prefix per `k`, simultaneous `O(10^-k)` cancellation through `2*10^k` |
| 2 | Post-T17 aggregate route to C1 | Power-ten Diophantine input plus eventual exact aggregate upper bound at prescribed `N,q,M` |
| 3 | T108 sampled-BBP circle density | Arbitrarily-late density; exactly V1-equivalent |
| 4 | Fixed-sixteen return | Joint-orbit density premise plus fixed return; V1-equivalent under that premise |
| 5 | T107 sampled-BBP Weyl cancellation | Ordinary fixed-frequency Weyl cancellation in transferred coordinates; stronger than V1 |
| 6 | BBP prescribed-code recurrence | External source premise plus arbitrary-late occurrence of every valid code |
| 7 | Appearance ratio | Uniform ratio plus another genuinely sufficient coverage/cancellation theorem |
| 8 | Positive density / long-lag decay | Positive frequency for every word or uniform all-scale collision bounds |

This ranking measures quantified new mathematical strength, not apparent
elegance or expected difficulty.

## 8. Recommended next action and unresolved bottleneck

Execute existing task `GP-0002`. Do not duplicate it.

Acceptance should retain T17's exact `q,D,N,r,M`, use the same `C` in the
upper-bound premise and T17 instantiation, require an eventual
`∀ k ≥ K` strict upper bound, conclude `C1`, and run the full Lean/build/audit
gate if promoted.

After that formal package, the selected route's real bottleneck is:

```text
for one fixed C and all sufficiently large k,

aggregatedFourierSum piFractionalOrbit
  (C*k*10^k-k+1)
  (10^k)
  (2*10^(2*k + (mu-1)*(C*k*10^k)+1))
<
  (C*k*10^k-k+1) / (2*10^k),
```

interpreted through T17's exact definitions, together with a justified
`PowerTenDiophantine π mu A` premise.

The alternative weaker-to-V1 bottleneck is T19's
`PiNaturalScaleCancellationExact`.

## 9. Rejected shortcuts and limitations

- No model output, literature summary, finite experiment, or green build proves
  V1.
- Qualitative fixed-frequency cancellation does not automatically supply a
  growing-frequency uniform estimate.
- Additive gaps are not relative cancellation without ambient-length control.
- A uniform appearance ratio alone is false as a generic sufficient condition.
- T107–T109 remove BBP transfer ambiguity but establish no cancellation,
  density, prescribed-code recurrence, or mixing.
- Furstenberg and irrationality-measure source statements remain explicit
  assumptions where cited.
- No `.lean` file was changed by RA-0002. The concurrent GP-0006 audit-only
  edit is separately verified and changes no theorem statement or proof.
- `~/.Codex/skills/marcel-judgment/SKILL.md`, referenced by the root
  instructions, was absent in this environment; no replacement was invented.
