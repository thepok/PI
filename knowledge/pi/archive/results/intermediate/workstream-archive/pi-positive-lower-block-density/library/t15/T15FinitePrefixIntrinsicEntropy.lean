import TheoryLib.PiPositiveLowerBlockDensity.T9T9FinitePrefixEntropyDeficit
import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T14T14PrefixAutomatonCertificates

/-!
# T15: intrinsic forbidden-language entropy in finite pi prefixes

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion involving pi is a necessary consequence of the literal
negation of canonical C1. Nothing here asserts that C1 fails for pi.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators Matrix

namespace Theory.PiDigits.PositiveLowerBlockDensity.T15

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T9
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T14

/-- The length-`L` words avoiding `v` at every relative offset, represented
as a finset in T9's empirical alphabet. -/
def forbiddenWords {ell : ℕ} (v : DecimalWord ell) (L : ℕ) :
    Finset (Fin L → Fin 10) :=
  Finset.univ.filter fun u => ∀ r : Fin (L + 1), ¬OccursAt v u r.val

/-- The finite support used here has exactly T13's intrinsic language count. -/
theorem forbiddenWords_card {ell : ℕ} (v : DecimalWord ell) (L : ℕ) :
    (forbiddenWords v L).card = forbiddenWordCount v L := by
  classical
  letI : Fintype (ForbiddenLanguage v L) := Fintype.ofFinite _
  let e : {u // u ∈ forbiddenWords v L} ≃ ForbiddenLanguage v L := {
    toFun := fun u => ⟨u.1, (Finset.mem_filter.mp u.2).2⟩
    invFun := fun u =>
      ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold forbiddenWordCount
  rw [← Fintype.card_coe]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr e

theorem occursAt_range {ell L : ℕ} {v : DecimalWord ell}
    {u : DecimalWord L} {r : ℕ} (h : OccursAt v u r) : r + ell ≤ L := by
  exact h.choose

theorem occursAt_apply {ell L : ℕ} {v : DecimalWord ell}
    {u : DecimalWord L} {r : ℕ} (h : OccursAt v u r) (i : Fin ell) :
    u ⟨r + i.val,
      lt_of_lt_of_le (Nat.add_lt_add_left i.isLt r) (occursAt_range h)⟩ = v i := by
  exact h.choose_spec i

/-- Fully contained sample starts at which `v` occurs at relative offset `r`. -/
def badStartsAtOffset (s : ℕ → Fin 10) (N L : ℕ) {ell : ℕ}
    (v : DecimalWord ell) (r : Fin (L + 1)) :
    Finset (FullyContainedStart N L) :=
  Finset.univ.filter fun n => OccursAt v (prefixWord s N L n) r.val

/-- Fully contained sample starts whose length-`L` word contains `v` at some
relative offset. -/
def occurrenceContaminatedStarts (s : ℕ → Fin 10) (N L : ℕ) {ell : ℕ}
    (v : DecimalWord ell) : Finset (FullyContainedStart N L) :=
  Finset.univ.filter fun n => ∃ r : Fin (L + 1),
    OccursAt v (prefixWord s N L n) r.val

/-- Shifting by an arbitrary relative occurrence offset injects contaminated
starts into T1's overlapping occurrence count. -/
theorem badStartsAtOffset_card_le_blockCount (s : ℕ → Fin 10)
    {N L ell : ℕ} (hell : 0 < ell) (hfull : L ≤ N)
    (v : DecimalWord ell) (r : Fin (L + 1)) :
    (badStartsAtOffset s N L v r).card ≤
      blockCount s (List.ofFn v) N := by
  classical
  let target : Finset (Fin N) := Finset.univ.filter fun q =>
    ∀ i : Fin ell, s (q.val + i.val) = v i
  let shift : {n // n ∈ badStartsAtOffset s N L v r} →
      {q // q ∈ target} := fun n => by
    have hnfull : n.val.val + L ≤ N :=
      (fullContainment_bookkeeping hfull).2 n.val
    have hocc := (Finset.mem_filter.mp n.2).2
    have hrange := occursAt_range hocc
    have hshiftlt : n.val.val + r.val < N := by omega
    refine ⟨⟨n.val.val + r.val, hshiftlt⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    have hm := occursAt_apply hocc i
    simpa [prefixWord, Nat.add_assoc] using hm
  have hinjective : Function.Injective shift := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg (fun q : {q // q ∈ target} => q.val.val) hab
    dsimp [shift] at hval
    apply Fin.ext
    exact Nat.add_right_cancel hval
  have hcard := Finset.card_le_card_of_injective hinjective
  have htarget : target.card = blockCount s (List.ofFn v) N := by
    unfold target blockCount
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i
      simpa only [List.get_ofFn] using h (Fin.cast (by simp) i)
    · intro h i
      simpa only [List.get_ofFn] using h (Fin.cast (by simp) i)
  simpa [htarget] using hcard

/-- Union over every relative offset gives the required arbitrary-offset
finite contamination bound. -/
theorem occurrenceContaminatedStarts_card_le (s : ℕ → Fin 10)
    {N L ell : ℕ} (hell : 0 < ell) (hfull : L ≤ N)
    (v : DecimalWord ell) :
    (occurrenceContaminatedStarts s N L v).card ≤
      (L + 1) * blockCount s (List.ofFn v) N := by
  classical
  have heq : occurrenceContaminatedStarts s N L v =
      (Finset.univ : Finset (Fin (L + 1))).biUnion
        (badStartsAtOffset s N L v) := by
    ext n
    simp [occurrenceContaminatedStarts, badStartsAtOffset]
  rw [heq]
  calc
    ((Finset.univ : Finset (Fin (L + 1))).biUnion
        (badStartsAtOffset s N L v)).card ≤
        ∑ r : Fin (L + 1), (badStartsAtOffset s N L v r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r : Fin (L + 1), blockCount s (List.ofFn v) N := by
      apply Finset.sum_le_sum
      intro r _
      exact badStartsAtOffset_card_le_blockCount s hell hfull v r
    _ = (L + 1) * blockCount s (List.ofFn v) N := by simp

/-- The empirical mass outside T13's forbidden language is exactly the
fraction of occurrence-contaminated fully contained starts. -/
theorem forbiddenExceptionalMass_eq_contaminatedFraction
    (s : ℕ → Fin 10) {N L ell : ℕ} (v : DecimalWord ell) :
    (∑ u ∈ (forbiddenWords v L)ᶜ,
        fullyContainedWordProbability s N L u) =
      (occurrenceContaminatedStarts s N L v).card /
        ((N + 1 - L : ℕ) : ℝ) := by
  classical
  let good := forbiddenWords v L
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (FullyContainedStart N L)))
    (t := goodᶜ) (g := prefixWord s N L)
  have hfiltered :
      (Finset.univ.filter fun n : FullyContainedStart N L =>
          prefixWord s N L n ∈ goodᶜ) =
        occurrenceContaminatedStarts s N L v := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    simp [good, forbiddenWords, occurrenceContaminatedStarts]
  have hcount :
      (∑ u ∈ goodᶜ, fullyContainedWordCount s N L u) =
        (occurrenceContaminatedStarts s N L v).card := by
    rw [← hfiltered]
    simpa [fullyContainedWordCount] using hfiber
  simp only [fullyContainedWordProbability, ← Finset.sum_div]
  rw [← Nat.cast_sum, hcount]

/-- If the prefix has room for twice the sampled block length, the empirical
mass of words containing `v` is at most twice the number of possible relative
offsets times the overlapping frequency of `v`. -/
theorem forbiddenExceptionalMass_le (s : ℕ → Fin 10)
    {N L ell : ℕ} (hell : 0 < ell) (hL : 0 < L) (hroom : 2 * L ≤ N)
    (v : DecimalWord ell) :
    (∑ u ∈ (forbiddenWords v L)ᶜ,
        fullyContainedWordProbability s N L u) ≤
      2 * (L + 1) * blockFrequency s (List.ofFn v) N := by
  classical
  have hfull : L ≤ N := by omega
  rw [forbiddenExceptionalMass_eq_contaminatedFraction s v]
  have hcard := occurrenceContaminatedStarts_card_le s hell hfull v
  have hN : 0 < N := by omega
  have hsample : 0 < N + 1 - L := by omega
  have hcastCard :
      ((occurrenceContaminatedStarts s N L v).card : ℝ) ≤
        ((L + 1) * blockCount s (List.ofFn v) N : ℕ) := by
    exact_mod_cast hcard
  have hdenCompare :
      (1 : ℝ) / (N + 1 - L : ℕ) ≤ 2 / (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
    exact_mod_cast (by omega : N ≤ 2 * (N + 1 - L))
  calc
    (occurrenceContaminatedStarts s N L v).card /
        ((N + 1 - L : ℕ) : ℝ) ≤
      ((L + 1) * blockCount s (List.ofFn v) N : ℕ) /
        ((N + 1 - L : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hcastCard (by positivity)
    _ = (((L + 1) * blockCount s (List.ofFn v) N : ℕ) : ℝ) *
        (1 / (N + 1 - L : ℕ)) := by ring
    _ ≤ (((L + 1) * blockCount s (List.ofFn v) N : ℕ) : ℝ) *
        (2 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hdenCompare (by positivity)
    _ = 2 * (L + 1) * blockFrequency s (List.ofFn v) N := by
      unfold blockFrequency
      push_cast
      ring

/-- Shannon entropy bound using the full overlapping forbidden language as
the ordinary support. -/
theorem finitePrefix_intrinsicShannonEntropy_bound (s : ℕ → Fin 10)
    {N L ell : ℕ} (hell : 0 < ell) (hL : 0 < L) (hroom : 2 * L ≤ N)
    (v : DecimalWord ell) :
    fullyContainedShannonEntropy s N L ≤
      Real.log (forbiddenWordCount v L : ℕ) + Real.log 2 +
        (2 * (L + 1) * blockFrequency s (List.ofFn v) N) *
          Real.log (10 ^ L : ℕ) := by
  classical
  let p : (Fin L → Fin 10) → ℝ := fullyContainedWordProbability s N L
  let good := forbiddenWords v L
  have hp0 : ∀ u, 0 ≤ p u := fun u =>
    fullyContainedWordProbability_nonneg s N L u
  have hp1 : ∑ u, p u = 1 :=
    sum_fullyContainedWordProbability s (by omega)
  have hgood : good.card ≤ forbiddenWordCount v L := by
    simp [good, forbiddenWords_card]
  have hcard : Fintype.card (Fin L → Fin 10) ≤ 10 ^ L := by simp
  have hq : ∑ u ∈ goodᶜ, p u ≤
      2 * (L + 1) * blockFrequency s (List.ofFn v) N := by
    exact forbiddenExceptionalMass_le s hell hL hroom v
  exact contaminatedSupport_entropy_bound p good hp0 hp1 hgood hcard hq

/-- Fraction of the prefix length occupied by one sampled block. -/
def containmentRatio (cutoffs scales : ℕ → ℕ) (j : ℕ) : ℝ :=
  (scales j : ℝ) / (cutoffs j : ℝ)

/-- Actual empirical mass of fully contained blocks which contain `v` at an
arbitrary relative offset. -/
def occurrenceContamination {ell : ℕ} (v : DecimalWord ell)
    (cutoffs scales : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ u ∈ (forbiddenWords v (scales j))ᶜ,
    fullyContainedWordProbability Theory.PiDigits.piDigit
      (cutoffs j) (scales j) u

/-- Per-digit empirical Shannon entropy of fully contained blocks. -/
def normalizedPrefixEntropy (cutoffs scales : ℕ → ℕ) (j : ℕ) : ℝ :=
  fullyContainedShannonEntropy Theory.PiDigits.piDigit
    (cutoffs j) (scales j) / (scales j : ℝ)

/-- The convergent upper envelope: intrinsic language log-count, suffix
bookkeeping, and occurrence contamination. -/
def intrinsicEntropyUpperBound {ell : ℕ} (v : DecimalWord ell)
    (cutoffs scales : ℕ → ℕ) (j : ℕ) : ℝ :=
  forbiddenLogRatio v (scales j) + Real.log 2 / (scales j : ℝ) +
    (2 * (scales j + 1) *
      blockFrequency Theory.PiDigits.piDigit (List.ofFn v) (cutoffs j)) *
      Real.log 10

theorem fullyContainedWordProbability_le_one (s : ℕ → Fin 10)
    {N L : ℕ} (hLN : L ≤ N) (u : Fin L → Fin 10) :
    fullyContainedWordProbability s N L u ≤ 1 := by
  have hcount : fullyContainedWordCount s N L u ≤ N + 1 - L := by
    unfold fullyContainedWordCount
    calc
      (Finset.univ.filter fun n : FullyContainedStart N L =>
          prefixWord s N L n = u).card ≤
          (Finset.univ : Finset (FullyContainedStart N L)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = N + 1 - L := by simp [FullyContainedStart]
  unfold fullyContainedWordProbability
  have hden : (0 : ℝ) < (N + 1 - L : ℕ) := by
    exact_mod_cast (by omega : 0 < N + 1 - L)
  rw [div_le_one hden]
  exact_mod_cast hcount

theorem fullyContainedShannonEntropy_nonneg (s : ℕ → Fin 10)
    {N L : ℕ} (hLN : L ≤ N) :
    0 ≤ fullyContainedShannonEntropy s N L := by
  unfold fullyContainedShannonEntropy
  exact Finset.sum_nonneg fun u _ => Real.negMulLog_nonneg
    (fullyContainedWordProbability_nonneg s N L u)
    (fullyContainedWordProbability_le_one s hLN u)

/-- The finite entropy estimate in the normalized form used for passage to
the intrinsic entropy limit. -/
theorem normalizedPrefixEntropy_le_intrinsicEntropyUpperBound
    {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (cutoffs scales : ℕ → ℕ) (j : ℕ)
    (hscale : 0 < scales j) (hroom : 2 * scales j ≤ cutoffs j) :
    normalizedPrefixEntropy cutoffs scales j ≤
      intrinsicEntropyUpperBound v cutoffs scales j := by
  have hfinite := finitePrefix_intrinsicShannonEntropy_bound
    Theory.PiDigits.piDigit hell hscale hroom v
  have hscaleReal : (0 : ℝ) < scales j := by exact_mod_cast hscale
  calc
    normalizedPrefixEntropy cutoffs scales j ≤
        (Real.log (forbiddenWordCount v (scales j) : ℕ) + Real.log 2 +
          (2 * (scales j + 1) *
            blockFrequency Theory.PiDigits.piDigit (List.ofFn v) (cutoffs j)) *
            Real.log (10 ^ scales j : ℕ)) / (scales j : ℝ) :=
      div_le_div_of_nonneg_right hfinite hscaleReal.le
    _ = intrinsicEntropyUpperBound v cutoffs scales j := by
      rw [Nat.cast_pow, Real.log_pow]
      unfold intrinsicEntropyUpperBound
      unfold forbiddenLogRatio
      push_cast
      field_simp [hscaleReal.ne']

/-- Slow-scale diagonal selection from a fixed zero-liminf forbidden word.
This is the reusable bridge between T9's cutoff selector and T13's intrinsic
entropy limit. -/
theorem zero_liminf_exists_intrinsicFinitePrefixScales
    {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (hzero : liminf
      (blockFrequency Theory.PiDigits.piDigit (List.ofFn v)) atTop = 0) :
    ∃ cutoffs scales : ℕ → ℕ,
      StrictMono cutoffs ∧ StrictMono scales ∧ Tendsto scales atTop atTop ∧
      (∀ j, 2 * scales j ≤ cutoffs j) ∧
      Tendsto (containmentRatio cutoffs scales) atTop (𝓝 0) ∧
      Tendsto (occurrenceContamination v cutoffs scales) atTop (𝓝 0) ∧
      Tendsto (intrinsicEntropyUpperBound v cutoffs scales) atTop
        (𝓝 (forbiddenEntropy v)) ∧
      limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
        forbiddenEntropy v := by
  let scales := divergingBlockScales ell
  let error : ℕ → ℝ := fun j =>
    1 / (2 * ((scales j + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ))
  let requirement : ℕ → ℕ := fun j => (j + 2) * scales j
  have hscalePos (j : ℕ) : 0 < scales j := by
    dsimp [scales, divergingBlockScales]
    omega
  have herrorPos (j : ℕ) : 0 < error j := by
    dsimp [error]
    positivity
  have hwitness : ∀ j B : ℕ, ∃ N : ℕ,
      B ≤ N ∧
        blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤ error j := by
    intro j B
    exact arbitrarilyLate_blockFrequency_le (List.ofFn v) hzero B (herrorPos j)
  let cutoffs := selectedPrefixCutoffs
    (blockFrequency Theory.PiDigits.piDigit (List.ofFn v))
    error requirement hwitness
  have hcutoffs : StrictMono cutoffs :=
    selectedPrefixCutoffs_strictMono _ _ _ hwitness
  have hscales : StrictMono scales := divergingBlockScales_strictMono ell
  have hscalesTop : Tendsto scales atTop atTop :=
    divergingBlockScales_tendsto_atTop ell
  have hrequirement (j : ℕ) : requirement j ≤ cutoffs j := by
    exact selectedPrefixCutoffs_requirement _ _ _ hwitness j
  have hroom (j : ℕ) : 2 * scales j ≤ cutoffs j := by
    have hreq := hrequirement j
    dsimp [requirement] at hreq
    have : 2 * scales j ≤ (j + 2) * scales j := by
      exact Nat.mul_le_mul_right (scales j) (by omega)
    exact this.trans hreq
  have hfrequency (j : ℕ) :
      blockFrequency Theory.PiDigits.piDigit (List.ofFn v) (cutoffs j) ≤
        error j :=
    selectedPrefixCutoffs_error _ _ _ hwitness j
  let q : ℕ → ℝ := fun j =>
    2 * (scales j + 1) *
      blockFrequency Theory.PiDigits.piDigit (List.ofFn v) (cutoffs j)
  have hq0 (j : ℕ) : 0 ≤ q j := by
    dsimp [q]
    exact mul_nonneg (by positivity)
      (blockFrequency_nonneg Theory.PiDigits.piDigit (List.ofFn v) (cutoffs j))
  have hq (j : ℕ) : q j ≤ 1 / (j + 1 : ℕ) := by
    have hfactor : (0 : ℝ) ≤ 2 * (scales j + 1) := by positivity
    calc
      q j ≤ 2 * (scales j + 1) * error j :=
        mul_le_mul_of_nonneg_left (hfrequency j) hfactor
      _ = 1 / (j + 1 : ℕ) := by
        dsimp [error]
        have hs : (0 : ℝ) < scales j + 1 := by positivity
        have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
        push_cast
        field_simp
  have hqTop : Tendsto q atTop (𝓝 0) :=
    tendsto_zero_of_nonneg_le_const_div_succ q 1 hq0 hq
  have hcontainment0 (j : ℕ) : 0 ≤ containmentRatio cutoffs scales j := by
    unfold containmentRatio
    positivity
  have hcontainment (j : ℕ) :
      containmentRatio cutoffs scales j ≤ 1 / (j + 1 : ℕ) := by
    have hreq := hrequirement j
    dsimp [requirement] at hreq
    have hweaker : (j + 1) * scales j ≤ cutoffs j := by
      exact (Nat.mul_le_mul_right (scales j) (by omega : j + 1 ≤ j + 2)).trans hreq
    have hcutoffPos : (0 : ℝ) < cutoffs j := by
      exact_mod_cast (lt_of_lt_of_le (hscalePos j) ((Nat.le_mul_of_pos_left
        (scales j) (by omega : 0 < j + 2)).trans hreq))
    have hjPos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    unfold containmentRatio
    rw [div_le_div_iff₀ hcutoffPos hjPos]
    norm_num
    exact_mod_cast (by simpa [Nat.mul_comm] using hweaker)
  have hcontainmentTop :
      Tendsto (containmentRatio cutoffs scales) atTop (𝓝 0) :=
    tendsto_zero_of_nonneg_le_const_div_succ
      (containmentRatio cutoffs scales) 1 hcontainment0 hcontainment
  have hcontamination0 (j : ℕ) :
      0 ≤ occurrenceContamination v cutoffs scales j := by
    unfold occurrenceContamination
    exact Finset.sum_nonneg fun u _ =>
      fullyContainedWordProbability_nonneg _ _ _ u
  have hcontamination (j : ℕ) :
      occurrenceContamination v cutoffs scales j ≤ q j := by
    exact forbiddenExceptionalMass_le Theory.PiDigits.piDigit hell
      (hscalePos j) (hroom j) v
  have hcontaminationTop :
      Tendsto (occurrenceContamination v cutoffs scales) atTop (𝓝 0) :=
    squeeze_zero hcontamination0 hcontamination hqTop
  have hratioTop : Tendsto (fun j => forbiddenLogRatio v (scales j)) atTop
      (𝓝 (forbiddenEntropy v)) :=
    (forbiddenLogRatio_tendsto_entropy v hell).comp hscalesTop
  have hoverheadTop : Tendsto (fun j => Real.log 2 / (scales j : ℝ)) atTop
      (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).comp hscalesTop
  have hqLogTop : Tendsto (fun j => q j * Real.log 10) atTop (𝓝 0) := by
    simpa using hqTop.mul_const (Real.log 10)
  have hupperTop : Tendsto (intrinsicEntropyUpperBound v cutoffs scales) atTop
      (𝓝 (forbiddenEntropy v)) := by
    simpa [intrinsicEntropyUpperBound, q] using
      (hratioTop.add hoverheadTop).add hqLogTop
  have hpointwise (j : ℕ) : normalizedPrefixEntropy cutoffs scales j ≤
      intrinsicEntropyUpperBound v cutoffs scales j :=
    normalizedPrefixEntropy_le_intrinsicEntropyUpperBound hell v cutoffs scales j
      (hscalePos j) (hroom j)
  have hentropy0 (j : ℕ) : 0 ≤ normalizedPrefixEntropy cutoffs scales j := by
    unfold normalizedPrefixEntropy
    have hscaleCutoff : scales j ≤ cutoffs j := by
      have := hroom j
      omega
    exact div_nonneg
      (fullyContainedShannonEntropy_nonneg _ hscaleCutoff)
      (by positivity)
  have hcobounded : atTop.IsCoboundedUnder (· ≤ ·)
      (normalizedPrefixEntropy cutoffs scales) :=
    isCoboundedUnder_le_of_le atTop hentropy0
  have hlimsup : limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
      forbiddenEntropy v := by
    calc
      limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
          limsup (intrinsicEntropyUpperBound v cutoffs scales) atTop :=
        limsup_le_limsup (Eventually.of_forall hpointwise) hcobounded
          hupperTop.isBoundedUnder_le
      _ = forbiddenEntropy v := hupperTop.limsup_eq
  exact ⟨cutoffs, scales, hcutoffs, hscales, hscalesTop, hroom,
    hcontainmentTop, hcontaminationTop, hupperTop, hlimsup⟩

/-- Any exact rational T14 supersolution sharpens the intrinsic normalized
finite-prefix entropy bound to `log lambda`. -/
theorem normalized_limsup_le_log_of_rationalCertificate
    {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (cutoffs scales : ℕ → ℕ)
    (hintrinsic : limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
      forbiddenEntropy v)
    (x : PrefixState ell hell → ℚ) (lambda : ℚ)
    (hlambda : 1 ≤ lambda) (hlambdaTen : lambda < 10)
    (hx : ∀ i, 1 ≤ x i)
    (hcert : ∀ i, ∑ j : PrefixState ell hell,
      (forbiddenTransitionMatrix hell v i j : ℚ) * x j ≤ lambda * x i) :
    limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
        Real.log (lambda : ℝ) ∧
      Real.log (lambda : ℝ) < Real.log 10 := by
  have hentropy := weighted_entropy_certificate hell v x lambda hlambda hx hcert
  have hlambdaPosQ : (0 : ℚ) < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hlambdaPos : (0 : ℝ) < (lambda : ℝ) := by exact_mod_cast hlambdaPosQ
  have hlambdaTenReal : (lambda : ℝ) < 10 := by exact_mod_cast hlambdaTen
  refine ⟨hintrinsic.trans hentropy, ?_⟩
  exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hlambdaPos)
    (Set.mem_Ioi.mpr (by norm_num)) hlambdaTenReal

/-- Necessary-only T15 conclusion. Literal failure of canonical C1 yields a
nonempty forbidden word and growing finite pi-prefix scales with vanishing
boundary loss and arbitrary-offset occurrence contamination. Their normalized
fully contained Shannon entropy has intrinsic limsup below full decimal
entropy, and every T14 rational certificate gives its advertised refinement.
No failure or truth of C1 is asserted. -/
theorem not_piPositiveLowerBlockDensity_implies_intrinsicFinitePrefixEntropy
    (hnot : ¬PiPositiveLowerBlockDensity) :
    ∃ ell : ℕ, ∃ hell : 0 < ell, ∃ v : DecimalWord ell,
      ∃ cutoffs scales : ℕ → ℕ,
        StrictMono cutoffs ∧ StrictMono scales ∧ Tendsto scales atTop atTop ∧
        (∀ j, 2 * scales j ≤ cutoffs j) ∧
        Tendsto (containmentRatio cutoffs scales) atTop (𝓝 0) ∧
        Tendsto (occurrenceContamination v cutoffs scales) atTop (𝓝 0) ∧
        limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
          forbiddenEntropy v ∧
        forbiddenEntropy v < Real.log 10 ∧
        ∀ (x : PrefixState ell hell → ℚ) (lambda : ℚ),
          1 ≤ lambda → lambda < 10 → (∀ i, 1 ≤ x i) →
          (∀ i, ∑ j : PrefixState ell hell,
            (forbiddenTransitionMatrix hell v i j : ℚ) * x j ≤
              lambda * x i) →
          limsup (normalizedPrefixEntropy cutoffs scales) atTop ≤
              Real.log (lambda : ℝ) ∧
            Real.log (lambda : ℝ) < Real.log 10 := by
  obtain ⟨ell, hell, v, hzero⟩ := not_C1_exists_zero_liminf hnot
  obtain ⟨cutoffs, scales, hcutoffs, hscales, hscalesTop, hroom,
      hcontainment, hcontamination, _hupper, hlimsup⟩ :=
    zero_liminf_exists_intrinsicFinitePrefixScales hell v hzero
  have hstrict : forbiddenEntropy v < Real.log 10 :=
    (forbiddenEntropy_le_q_rate v hell).trans_lt
      (forbiddenQ_rate_lt_log_ten v hell)
  refine ⟨ell, hell, v, cutoffs, scales, hcutoffs, hscales, hscalesTop,
    hroom, hcontainment, hcontamination, hlimsup, hstrict, ?_⟩
  intro x lambda hlambda hlambdaTen hx hcert
  exact normalized_limsup_le_log_of_rationalCertificate hell v cutoffs scales
    hlimsup x lambda hlambda hlambdaTen hx hcert

end Theory.PiDigits.PositiveLowerBlockDensity.T15

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.forbiddenWords_card
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.occurrenceContaminatedStarts_card_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.forbiddenExceptionalMass_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.finitePrefix_intrinsicShannonEntropy_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.zero_liminf_exists_intrinsicFinitePrefixScales
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.normalized_limsup_le_log_of_rationalCertificate
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T15.not_piPositiveLowerBlockDensity_implies_intrinsicFinitePrefixEntropy
