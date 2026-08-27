# RA-0004 — appearance-ratio route audit

Agent: `pro-20260821T201954Z-gpt56pro-8c4d`  
Branch: `pi-core-consolidation`  
Audit date: 2026-08-21  
Claim class: repository-interface audit plus a generic `proof sketch` separator; no main-claim proof.

## Decision

**Close T28 → T29 as a standalone route to T19 or canonical V1.** Keep the existing theorems as a useful quantitative diagnostic, but do not treat a bound on the appearance ratio as the next decisive bottleneck.

The reason is stronger than “the ratio is currently unknown.” Even the mathematically best possible ratio, `L_m = p_pi(m)`, lets the exposed T27/T29 mechanism prove only

\[
  \frac{|S_{L_m}(h)|}{L_m}\le \frac{31}{32}
\]

on a moving selected subset of frequencies. T19 instead requires one cutoff at each length for **every** nonzero frequency up to `2 * 10^m`, with normalized norm of order `10^{-m}`. Solving the appearance-ratio problem would therefore leave both dominant gaps intact: frequency coverage and cancellation strength.

There is also a reusable generic separator. A recurrent disjunctive decimal stream can have maximal ordinary complexity, maximal recurrent complexity, and maximal factor entropy while its last-first-occurrence ratio grows faster than any prescribed sequence. Thus factor-language information, even at its maximal endpoint, does not control appearance time.

## Exact quantities: do not conflate them

Fix a positive block length `m` and write `q_m = 10^m`.

| Symbol in this audit | Repository object | Meaning |
|---|---|---|
| `p_m` | `piFactorComplexity m` | Number of distinct length-`m` factors occurring anywhere in the infinite pi digit stream. This is ordinary factor complexity; it contains no occurrence-time information. |
| `p_m^rec` | `recurrentFactorComplexity piDigit m` | Number of length-`m` factors occurring beyond every threshold. This is a different subtype and can be strictly smaller than `p_m`. |
| `a_m(i)` | `piFactorFirstOccurrence m i` | Least start of the `i`th canonical distinct length-`m` factor. |
| `L_m^sum` | `piFirstOccurrencePrefixLength m` | `1 + sum_i a_m(i)`. T23 uses this deliberately loose orbit-prefix cutoff. |
| `L_m` | `piLastFirstOccurrencePrefixLength m` | `1 + max_i a_m(i)`. T28 proves this is the least positive prefix of **start positions/orbit points** containing all canonical first occurrences. |
| `D_m` | not separately named | Number of decimal digits needed to witness all blocks whose starts are `< L_m`: for `m > 0`, `D_m = L_m + m - 1`. A start-prefix of length `L_m` is not a digit prefix of the same length. |
| `F_m` | `piManyLastFirstOccurrenceLinearGapFrequencies m` | A scale-dependent subset of `Fin (10^m)`; `r` represents frequency `r.val + 1`. |

Two immediate cardinality facts matter:

1. `piLastFirstOccurrenceEmbedding m : Fin p_m ↪ Fin L_m` gives `p_m ≤ L_m`.
2. `piLastFirstOccurrencePrefixLength_le_sumPrefixLength` gives `L_m ≤ L_m^sum`.

Hence every natural appearance-ratio constant satisfies `C ≥ 1`. The ideal case `C = 1` is already insufficient for T19.

For a generic finite-alphabet stream, the same minimal cutoff can be characterized as

\[
  L_s(m)=\min\{N>0:\#\{\operatorname{blockAt}(s,m,i):i<N\}=p_s(m)\}.
\]

This is a cover time of the global factor language by start positions. It is not a complexity count, recurrence count, entropy, collision energy, or digit-prefix length.

## Exact theorem/interface map

### T23: selected first occurrences and the loose cutoff

[`T23T23MorseHedlundFrequencyDefect.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T23T23MorseHedlundFrequencyDefect.lean) supplies the support used by T26–T29:

- `piFactorRepresentative m` canonically enumerates the `p_m` distinct factors.
- `piFactorFirstOccurrence m i` is the least start of representative `i`.
- `piFactorFirstOccurrence_injective` proves different factors have different first starts.
- `piFirstOccurrencePrefixLength m = 1 + sum_i a_m(i)`.
- `piFirstOccurrenceEmbedding m` embeds the selected starts into that prefix.
- `piFirstOccurrenceCylinderCode_injective` and `piFirstOccurrenceEmbedding_mem_cell` put the selected orbit points in pairwise distinct decimal cells.

The file explicitly leaves the cutoff and intervening multiplicities uncontrolled.

### T26: many frequencies with quadratic full-prefix defect

[`T26T26ManyFrequencyFirstOccurrenceDefect.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T26T26ManyFrequencyFirstOccurrenceDefect.lean) proves:

- `q_le_sixteen_mul_card_largeEnergyFrequencies`: at least `q/16` frequencies have selected pair energy at least `P(P-3)/4`.
- `q_le_sixteen_mul_card_largeFullDefectFrequencies`: the selected defect transfers monotonically to an ambient prefix.
- `pi_q_le_sixteen_mul_card_manyFirstOccurrenceDefectFrequencies` and `pi_manyFirstOccurrenceDefectFrequencies_spec`: for every `m ≥ 3`, at least one sixteenth of frequencies `1, ..., 10^m` have a quadratic defect at the cutoff `L_m^sum`.

This is an absolute defect against `(L_m^sum)^2`, not normalized cancellation.

### T27: quadratic defect to additive linear gap

[`T27T27ManyFrequencyLinearGap.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T27T27ManyFrequencyLinearGap.lean) proves:

- `norm_selectedSupport_le_thirtyOne_mul_div_thirtyTwo`: a retained selected sum has norm at most `31P/32`.
- `norm_ambientSum_le_selected_add_complement`: the uncontrolled complement costs exactly at most `N-P` by the triangle inequality.
- `selected_norm_bound_implies_ambient_additiveGap`: the resulting ambient gap is only `P/32`.
- `pi_manyFirstOccurrenceLinearGapFrequencies_spec`: at `N = L_m^sum`, every retained frequency has gap at least `p_m/32 ≥ (m+1)/32`.

The complement estimate is the structural loss. It preserves an additive saving but can destroy a selected relative saving when `N/P` is large.

### T28: replace the sum cutoff by the true cover time

[`T28T28LastFirstOccurrenceLinearGap.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean) proves:

- `piLastFirstOccurrencePrefixLength m = 1 + sup_i a_m(i)`.
- `piLastFirstOccurrencePrefixLength_isLeast`: exact least-positive-prefix characterization.
- `piLastFirstOccurrencePrefixLength_le_sumPrefixLength`.
- `piManyLastFirstOccurrenceLinearGapFrequencies_eq_sumPrefix_set`: changing the ambient cutoff does not change the selected-support good set at the same `m`.
- `pi_manyLastFirstOccurrenceLinearGapFrequencies_spec`: at least `q_m/16` retained frequencies satisfy

\[
  \frac{p_m}{32}\le L_m-|S_{L_m}(h)|.
\]

This is the strongest unconditional endpoint of the first-occurrence chain.

### T29: conditional normalization

[`T29T29AppearanceRatioRelativeGap.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean) contains the exact bridge:

- `normalized_norm_le_one_sub_inv_thirtyTwo_mul_of_appearanceRatio` converts `N ≤ C P` and gap `P/32` into

\[
  |z|/N\le 1-1/(32C).
\]

- `pi_manyLastFirstOccurrenceRelativeGapFrequencies_spec` applies it at one fixed pair `(m,C)` under

\[
  L_m\le C p_m.
\]

No global appearance-ratio predicate is defined, no such bound is proved for pi, and the selected set remains `F_m`.

### T30: maximal entropy identifies which words occur, not when

[`T30T30MaximalEntropyEquivalence.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean) proves:

- `factorEntropy_eq_logTen_iff_disjunctive` for an arbitrary decimal stream.
- `canonicalV1_iff_pi_maximalFactorComplexity`.
- `pi_factorEntropy_eq_logTen_iff_canonicalV1`.

These are exact endpoint equivalences. They do not provide a first-occurrence modulus. The generic separator below shows that no such modulus follows from the generic maximal-entropy or maximal-complexity conclusions.

### T19: the actual natural-scale sufficient condition

[`T19T19ExactNaturalScaleResonance.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean) defines

```text
PiNaturalScaleCancellationExact :=
  ∀ k, 1 ≤ k → ∃ N, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * 10^k →
      ‖S_N(h)‖ / N < 1/(24*10^k) + 1/(12*10^(3*k)).
```

and proves `piNaturalScaleCancellationExact_implies_canonicalV1`. The premise remains open.

## Quantifier audit

T29 exposes, schematically,

\[
\forall m\ge3\;\forall C>0:\quad
  L_m\le Cp_m\Longrightarrow
  \left(|F_m|\ge q_m/16\ \land\
  \forall h\in F_m,\ |S_{L_m}(h)|/L_m\le1-1/(32C)\right).
\]

T19 requires

\[
\forall k\ge1\;\exists N>0\;\forall h\in\mathbb Z,
  0<|h|\le2q_k:\quad
  |S_N(h)|/N < \frac1{24q_k}+\frac1{12q_k^3}.
\]

The gaps are literal:

1. **Selected versus universal frequencies.** T29 guarantees only a subset of at least `q_m/16` inside `1, ..., q_m`. T19 quantifies over every nonzero frequency through `2q_m`.
2. **Constant relative gap versus small norm.** Even `C=1` gives only `31/32`; T19's threshold tends to zero like `1/(24q_m)`.
3. **Moving, non-coherent sets.** `F_m` depends on `m`. T28 proves equality only between two cutoff presentations at the same length; it proves no nesting or cross-scale coherence.
4. **Per-scale versus uniform appearance control.** T29 accepts a fresh `C` at each invocation. A common spectral saving needs one `C` over the relevant unbounded set of lengths.
5. **No interpolation theorem.** Ordinary factor complexity is nondecreasing, but no monotonicity of `L_m/p_m` or of `F_m` is supplied. A subsequence estimate cannot silently be promoted to every length.

The fact that T19 may choose a cutoff `N` is not the problem: T29 already supplies a positive candidate `N=L_m`. The failure is the strength and scope of the frequency conclusion at that cutoff.

## What the genuinely missing appearance hypothesis is

At a single fixed `m`, the premise `L_m ≤ C p_m` is vacuous as an existence statement: `p_m ≥ 1`, so one may take `C=L_m`. This yields the useless scale-dependent estimate `1-1/(32L_m)`.

The weakest bounded-ratio condition that gives a **common T29 saving on arbitrarily large scales** is

```text
AppearanceRatioFrequentlyBounded :=
  ∃ C : ℕ, 0 < C ∧ ∀ M : ℕ, ∃ m : ℕ,
    max M 3 ≤ m ∧ L_m ≤ C * p_m.
```

The weakest bounded-ratio condition that gives a **common T29 saving at every sufficiently large scale** is

```text
AppearanceRatioEventuallyBounded :=
  ∃ C : ℕ, 0 < C ∧ ∃ M : ℕ, ∀ m : ℕ,
    max M 3 ≤ m → L_m ≤ C * p_m.
```

For this natural-number sequence, eventual boundedness is equivalent to a bound for all `m ≥ 3` after enlarging `C` to absorb finitely many exceptional lengths. This is the normalized global hypothesis that T29 itself omits.

It is sufficient only for T29's fixed relative saving. It is **not** sufficient for T19 or V1. No choice of positive integer `C` makes

\[
  1-\frac1{32C}=O(10^{-m}).
\]

An additional theorem must control the complement and all frequencies; appearance time alone cannot do that.

## Sharp finite-sum obstruction inside the exposed bridge

The complement loss in T27 is sharp under the hypotheses visible to `selected_norm_bound_implies_ambient_additiveGap`.

Take `P` divisible by `64`. Among the `P` selected unit phases, put `63P/64` at `+1` and `P/64` at `-1`. Their sum is exactly `31P/32`. Put all `N-P` complement phases at `+1`. Then the full norm is

\[
  (N-P)+\frac{31P}{32}=N-\frac{P}{32}.
\]

If `N=CP`, normalization gives equality in T29's displayed bound:

\[
  \frac{|S_N|}{N}=1-\frac1{32C}.
\]

This does not claim that these phases arise from the pi orbit or satisfy T26's cell geometry. It proves the narrower and exact point needed here: the generic selected-norm plus cardinality data exposed to T27/T29 contain no stronger conclusion. Any improvement must use new structure of the omitted orbit points, not a better rearrangement of the existing triangle-inequality argument.

## Generic maximal-language separator

**Claim class: `proof sketch`; generic stream theorem, not machine-checked in this task.**

### Proposition

For every prescribed sequence `A_m ≥ 1`, there is a decimal stream `s : ℕ → Fin 10` such that, for every `m ≥ 1`:

1. every finite decimal word occurs beyond every threshold;
2. `p_s(m) = p_s^rec(m) = 10^m`;
3. the factor entropy is maximal (`log 10`, or `1` in base-ten normalization);
4. the first occurrence of the word `9^m` starts at some `t_m ≥ A_m 10^m`;
5. consequently `L_s(m) > A_m p_s(m)`.

Thus bounded appearance ratio is not implied by disjunctivity, maximal ordinary factor complexity, maximal recurrent factor complexity, maximal factor entropy, or even the conjunction of all four.

### Construction

For each `m ≥ 1`, choose an arbitrary enumeration of every nonempty decimal word of length at most `m`. Let `E_m` be their concatenation with a block `0^m` before and after every enumerated word. Recursively build finite prefixes

\[
  U_m=U_{m-1}\;0^{D_m}\;9^m\;0^m\;E_m,
\]

starting from the empty word. Choose `D_m` large enough that the displayed special occurrence of `9^m` begins at a start `t_m ≥ A_m 10^m`. Let `s` be the unique infinite stream having all `U_m` as prefixes.

### Verification of the exact hypotheses

- Every component of a stage `< m` has length at most `m-1`, and the inserted zero separators prevent runs of `9` from joining across components. Hence the prefix before the special stage-`m` target contains no `9^m`.
- The padding before the target consists only of zeros. Therefore the displayed `9^m` is its first occurrence, exactly at `t_m`.
- Any fixed word `w` of length `r` occurs inside `E_m` for every `m ≥ r`. These occurrences occur at unbounded positions, so `w` is recurrent, not merely present once.
- Hence all `10^m` length-`m` words are ordinary and recurrent factors. Their ordinary and recurrent complexities are both exactly `10^m`, and the standard maximal-complexity/entropy interfaces apply.
- Since `L_s(m)` is one plus the latest first occurrence, `L_s(m) ≥ t_m+1 > A_m 10^m = A_m p_s(m)`.

Taking `A_m → ∞` gives unbounded ratio; choosing `A_m` to dominate an arbitrary proposed rate gives arbitrarily bad ratio. No finite digit experiment is used.

The separator deliberately makes no claim about `PiLongLagBlockCollisionDecay`; its long zero pads can create large collision islands. It refutes only implications from the exact language/entropy/recurrent hypotheses listed above.

## Do existing neighboring results approach the ratio?

| Repository line | What is actually controlled | Relation to `L_m / p_m` |
|---|---|---|
| Ordinary factor complexity in [`T1DecimalFactorComplexity.lean`](../../../TheoryLib/PiDecimalFactorComplexity/T1DecimalFactorComplexity.lean) and the pi Morse–Hedlund lower bound | Cardinality of the global factor set; for pi at least `m+1`. | No occurrence-time modulus. The maximal-language separator rules out a generic implication even at `p_m=10^m`. |
| Positive/maximal entropy in [`T1CanonicalEntropy.lean`](../../../TheoryLib/PiPositiveDecimalFactorEntropy/T1CanonicalEntropy.lean) and T30 | Exponential or maximal growth of global factor counts. Positive entropy for pi is open; maximal entropy is equivalent to V1. | Entropy forgets first-occurrence positions. Maximal entropy still permits arbitrary appearance delay in the separator. |
| Recurrent language in [`T31T31RecurrentFactorComplexity.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T31T31RecurrentFactorComplexity.lean) and [`T32T32RecurrentRightSpecial.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T32T32RecurrentRightSpecial.lean) | `p_pi^rec(m) ≥ m+1`, strict recurrent growth, and an unspecified recurrent right-special factor. | Recurrence says “after every threshold,” but supplies no uniform witness function. The separator has all `10^m` factors recurrent and still has arbitrary first delays. |
| Sharp recurrent separator in [`T33T33RecurrentSharpnessSeparator.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T33T33RecurrentSharpnessSeparator.lean) | An aperiodic spike stream with exactly `m+1` recurrent factors. | Confirms that the unconditional recurrent lower bounds are sharp, but does not itself address maximal recurrent language. The separator above closes that stronger generic loophole. |
| Recurrent-value transfers in [`T34T34RecurrentCellTransfer.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T34T34RecurrentCellTransfer.lean) and [`T39T39EventualRecurrentTransfer.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T39T39EventualRecurrentTransfer.lean) | Transfer of which values recur, sometimes conditionally and sometimes with exact eventual equality. | Eventual/recurrent membership is transferred without a quantitative cutoff, so first-occurrence cover time is still absent. |
| Long-lag collisions in [`T1T1LongLagBlockCollisionDecay.lean`](../../../TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean) | The open predicate `PiLongLagBlockCollisionDecay` bounds aggregate ordered equal-block pairs uniformly in `m,N` for each fixed `s<1`; the file proves that this predicate would imply positive lower block density. | No proved fixed-pi instance is supplied. If the open predicate were proved, it would bypass this route by implying the stronger density/V1 target. The current finite collision interfaces do not isolate the last unseen factor or prove `L_m ≤ C p_m`. |
| Sparse periodic islands in [`T19T19SparsePeriodicIslands.lean`](../../../TheoryLib/PiLongLagBlockCollisionDecay/T19T19SparsePeriodicIslands.lean) | A reusable mechanism forcing excessive collision counts. | This is a negative collision obstruction, not an upper bound on appearance time. |
| Positive lower block density in [`T1PiPositiveLowerBlockDensity.lean`](../../../TheoryLib/PiPositiveLowerBlockDensity/T1PiPositiveLowerBlockDensity.lean) | An open per-word positive-liminf statement, proved conditionally to imply V1. | Per-word positivity without an explicit length-uniform density modulus does not state a linear cover-time bound. It is already stronger than the target occurrence conjecture and is not an available premise. |

A collision estimate can lower-bound the number of distinct cells seen in a finite prefix through Cauchy–Schwarz. That is still a lower bound on prefix diversity, not an assertion that every globally occurring factor has appeared. The last rare factor can remain delayed unless one proves a uniform per-factor occupancy or waiting-time estimate. No inspected theorem supplies that estimate.

## Bounded continuation program, only if the route is retained

The appearance-ratio question is mathematically clean, but it should be separated from the main V1 route.

A useful formal package would consist of:

1. A generic `lastFirstOccurrencePrefixLength` and the identity with the least `N` at which prefix factor count equals global factor complexity.
2. Global predicates matching the two quantifier forms above: `AppearanceRatioFrequentlyBounded` and `AppearanceRatioEventuallyBounded`.
3. A wrapper theorem lifting T29 to a common relative saving under `AppearanceRatioEventuallyBounded`.
4. A formal generic separator such as `exists_recurrentDisjunctive_unboundedAppearanceRatio`, preventing later work from inferring timing from language size or recurrence.

An actual fixed-pi proof of the ratio would need a new quantitative recurrence statement of the form

\[
  \forall m\ge M\;\forall w\in\operatorname{Factor}(\pi,m),\quad
  \operatorname{firstOccurrence}(w)<C\,p_m.
\]

Aggregate factor counts, entropy, and recurrence do not imply this. A long-lag or spectral approach would have to add a **uniform rare-cell exclusion** theorem, not merely an average collision bound.

Even after such a proof, a V1 continuation would still require two independent upgrades:

- control of all natural-scale frequencies, including the complement of `F_m` and frequencies between `q_m` and `2q_m`;
- amplification from a fixed relative saving to normalized size `O(q_m^{-1})` at one common cutoff.

Those are the real unresolved bottlenecks.

## Recommendation

- **Close** the appearance-ratio route as a standalone proof strategy for T19 or V1.
- **Retain** T28 and T29 as exact machine-readable diagnostics: they quantify how much of the selected first-occurrence saving survives an ambient prefix.
- **Do not prioritize** a fixed-pi proof of `L_m = O(p_m)` unless it has independent combinatorial value or comes bundled with complement/all-frequency control.
- **Prioritize instead** a fixed-pi natural-scale cancellation theorem, an equivalent prescribed-cell steering theorem, or a new mechanism that controls the omitted orbit visits rather than only their number.

## Verification evidence and limitations

- Inspected the repository-root control files, GPTPro coordination files, every task file, the exact T23 and T26–T30 interfaces, T19's sufficient condition, the ordinary/recurrent complexity modules, the entropy modules, the recurrent transfer modules, the canonical long-lag predicate, the sparse-island obstruction, and `knowledge/pi/OVERVIEW.md`.
- Checked theorem quantifier order directly from the Lean source and separated `L_m^sum`, `L_m`, and the actual digit-prefix length `L_m+m-1`.
- Checked the algebraic sharpness example symbolically; it exactly attains the T27/T29 exposed bound for `64 | P` and `N=CP`.
- Checked the generic separator against the hypotheses it refutes: every finite word occurs in every sufficiently late enumeration stage, while `9^m` is excluded before its prescribed special target by zero-separated stage construction.
- No Lean source changed, so `lake build TheoryLib` and `workflows/verification/check.ps1` were not applicable to this documentation-only task. No fresh Lean build is claimed.
- The generic separator is a `proof sketch`, not a machine-checked theorem. It makes no claim about pi and no claim that the constructed stream satisfies the long-lag collision-decay predicate.
