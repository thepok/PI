import Mathlib.Analysis.Subadditive
import TheoryLib.PiPositiveLowerBlockDensity.T12T12OverlappingForbiddenWordDimension

/-!
# T13: intrinsic entropy of an overlapping forbidden-word language

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

Every conclusion involving pi is a necessary consequence of the literal
negation of canonical C1. Nothing here asserts that C1 fails for pi.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T13

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T10
open Theory.PiDigits.PositiveLowerBlockDensity.T11
open Theory.PiDigits.PositiveLowerBlockDensity.T12

/-- The cardinality `a_v(n)` of the length-`n` overlapping language avoiding
the forbidden decimal word `v`. -/
def forbiddenWordCount {ell : ℕ} (v : DecimalWord ell) (n : ℕ) : ℕ :=
  Nat.card (ForbiddenLanguage v n)

/-- Positive natural lengths, used to state the entropy infimum without a
spurious division by zero. -/
abbrev PositiveLength := {n : ℕ // 0 < n}

/-- The normalized logarithmic forbidden-language count. -/
def forbiddenLogRatio {ell : ℕ} (v : DecimalWord ell) (n : ℕ) : ℝ :=
  Real.log (forbiddenWordCount v n : ℝ) / (n : ℝ)

/-- The intrinsic forbidden-language entropy, defined as the infimum over all
positive lengths. -/
def forbiddenEntropy {ell : ℕ} (v : DecimalWord ell) : ℝ :=
  ⨅ n : PositiveLength, forbiddenLogRatio v n

/-- A nonempty forbidden word always has at least one avoiding word of every
length. -/
theorem forbiddenWordCount_pos {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) (n : ℕ) :
    0 < forbiddenWordCount v n := by
  haveI : Nonempty (ForbiddenLanguage v n) :=
    ⟨⟨constantAvoidingWord v hell n, constantAvoidingWord_mem v hell n⟩⟩
  exact Nat.card_pos

/-- Restrict a word of length `n + m` to its first `n` digits. -/
def takeWord (n m : ℕ) (w : DecimalWord (n + m)) : DecimalWord n :=
  fun i => w ⟨i.val, by omega⟩

/-- Restrict a word of length `n + m` to its final `m` digits. -/
def dropWord (n m : ℕ) (w : DecimalWord (n + m)) : DecimalWord m :=
  fun i => w ⟨n + i.val, by omega⟩

theorem occursAt_takeWord {ell n m : ℕ} (v : DecimalWord ell)
    (w : DecimalWord (n + m)) (r : ℕ)
    (hocc : OccursAt v (takeWord n m w) r) :
    OccursAt v w r := by
  obtain ⟨hrange, hmatch⟩ := hocc
  refine ⟨by omega, ?_⟩
  intro j
  simpa [takeWord] using hmatch j

theorem occursAt_dropWord {ell n m : ℕ} (v : DecimalWord ell)
    (w : DecimalWord (n + m)) (r : ℕ)
    (hocc : OccursAt v (dropWord n m w) r) :
    OccursAt v w (n + r) := by
  obtain ⟨hrange, hmatch⟩ := hocc
  refine ⟨by omega, ?_⟩
  intro j
  simpa [dropWord, Nat.add_assoc] using hmatch j

/-- Splitting an avoiding word at an arbitrary position gives two avoiding
words. -/
def splitAvoidingWord {ell : ℕ} (v : DecimalWord ell) (n m : ℕ) :
    ForbiddenLanguage v (n + m) →
      ForbiddenLanguage v n × ForbiddenLanguage v m := fun w =>
  (⟨takeWord n m w.1, fun r hocc =>
      w.2 ⟨r.val, by omega⟩ (occursAt_takeWord v w.1 r.val hocc)⟩,
    ⟨dropWord n m w.1, fun r hocc =>
      w.2 ⟨n + r.val, by omega⟩ (occursAt_dropWord v w.1 r.val hocc)⟩)

theorem take_drop_injective (n m : ℕ) :
    Function.Injective (fun w : DecimalWord (n + m) =>
      (takeWord n m w, dropWord n m w)) := by
  intro a b hab
  funext i
  by_cases hi : i.val < n
  · have hleft := congrFun (congrArg Prod.fst hab) (⟨i.val, hi⟩ : Fin n)
    simpa [takeWord] using hleft
  · have hj : i.val - n < m := by omega
    have hright := congrFun (congrArg Prod.snd hab)
      (⟨i.val - n, hj⟩ : Fin m)
    simpa [dropWord, Nat.add_sub_of_le (Nat.le_of_not_gt hi)] using hright

theorem splitAvoidingWord_injective {ell : ℕ} (v : DecimalWord ell)
    (n m : ℕ) : Function.Injective (splitAvoidingWord v n m) := by
  intro a b hab
  apply Subtype.ext
  apply take_drop_injective n m
  exact congrArg (fun p => (p.1.1, p.2.1)) hab

/-- The overlapping forbidden-language counts are submultiplicative. -/
theorem forbiddenWordCount_submultiplicative {ell : ℕ}
    (v : DecimalWord ell) (n m : ℕ) :
    forbiddenWordCount v (n + m) ≤
      forbiddenWordCount v n * forbiddenWordCount v m := by
  have hcard := Nat.card_le_card_of_injective (splitAvoidingWord v n m)
    (splitAvoidingWord_injective v n m)
  rw [Nat.card_prod] at hcard
  simpa only [forbiddenWordCount] using hcard

/-- Logarithms turn forbidden-language submultiplicativity into a real
subadditive sequence. -/
theorem forbiddenLogCount_subadditive {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) :
    Subadditive (fun n => Real.log (forbiddenWordCount v n : ℝ)) := by
  intro n m
  have hnpos : (0 : ℝ) < forbiddenWordCount v n := by
    exact_mod_cast forbiddenWordCount_pos v hell n
  have hmpos : (0 : ℝ) < forbiddenWordCount v m := by
    exact_mod_cast forbiddenWordCount_pos v hell m
  have hnmpos : (0 : ℝ) < forbiddenWordCount v (n + m) := by
    exact_mod_cast forbiddenWordCount_pos v hell (n + m)
  have hcount : (forbiddenWordCount v (n + m) : ℝ) ≤
      (forbiddenWordCount v n : ℝ) * forbiddenWordCount v m := by
    exact_mod_cast forbiddenWordCount_submultiplicative v n m
  calc
    Real.log (forbiddenWordCount v (n + m) : ℝ) ≤
        Real.log ((forbiddenWordCount v n : ℝ) * forbiddenWordCount v m) :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hnmpos) (Set.mem_Ioi.mpr (mul_pos hnpos hmpos)) hcount
    _ = Real.log (forbiddenWordCount v n : ℝ) +
        Real.log (forbiddenWordCount v m : ℝ) :=
      Real.log_mul hnpos.ne' hmpos.ne'

theorem forbiddenLogRatio_nonneg {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) (n : ℕ) : 0 ≤ forbiddenLogRatio v n := by
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast (forbiddenWordCount_pos v hell n)
  · positivity

theorem forbiddenLogRatio_bddBelow {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) :
    BddBelow (Set.range (forbiddenLogRatio v)) := by
  exact ⟨0, by rintro _ ⟨n, rfl⟩; exact forbiddenLogRatio_nonneg v hell n⟩

theorem forbiddenPositiveLogRatio_bddBelow {ell : ℕ}
    (v : DecimalWord ell) (hell : 0 < ell) :
    BddBelow (Set.range (fun n : PositiveLength => forbiddenLogRatio v n)) := by
  exact ⟨0, by
    rintro _ ⟨n, rfl⟩
    exact forbiddenLogRatio_nonneg v hell n⟩

/-- Fekete's lemma gives convergence of the normalized log-counts to their
intrinsic entropy. -/
theorem forbiddenLogRatio_tendsto_entropy {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) :
    Tendsto (forbiddenLogRatio v) atTop (𝓝 (forbiddenEntropy v)) := by
  let hsub : Subadditive (fun n => Real.log (forbiddenWordCount v n : ℝ)) :=
    forbiddenLogCount_subadditive v hell
  have hbdd : BddBelow (Set.range (fun n : ℕ =>
      Real.log (forbiddenWordCount v n : ℝ) / (n : ℝ))) := by
    simpa only [forbiddenLogRatio] using forbiddenLogRatio_bddBelow v hell
  have ht := hsub.tendsto_lim hbdd
  have heq : hsub.lim = forbiddenEntropy v := by
    apply le_antisymm
    · rw [forbiddenEntropy]
      apply le_ciInf
      intro n
      exact hsub.lim_le_div hbdd n.property.ne'
    · apply ge_of_tendsto ht
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact ciInf_le
        (forbiddenPositiveLogRatio_bddBelow v hell) (⟨n, hn⟩ : PositiveLength)
  rw [heq] at ht
  simpa only [forbiddenLogRatio] using ht

/-- Infimum characterization of the intrinsic entropy. -/
theorem forbiddenEntropy_eq_iInf {ell : ℕ} (v : DecimalWord ell) :
    forbiddenEntropy v =
      ⨅ n : PositiveLength, forbiddenLogRatio v n := rfl

theorem forbiddenEntropy_le_ratio {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) {n : ℕ} (hn : 0 < n) :
    forbiddenEntropy v ≤ forbiddenLogRatio v n := by
  exact ciInf_le (forbiddenPositiveLogRatio_bddBelow v hell)
    (⟨n, hn⟩ : PositiveLength)

theorem forbiddenEntropy_nonneg {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) : 0 ≤ forbiddenEntropy v := by
  rw [forbiddenEntropy]
  apply le_ciInf
  intro n
  exact forbiddenLogRatio_nonneg v hell n

/-- Positive aligned atoms at any decimal scale inject into tuples of avoiding
words at that scale. -/
theorem positive_mass_atom_count_le_forbiddenWordCount_pow
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell : ℕ} (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0)
    (k m : ℕ) :
    Nat.card (PositiveAlignedAtom ν k m) ≤ forbiddenWordCount v k ^ m := by
  let encode : PositiveAlignedAtom ν k m →
      (Fin m → ForbiddenLanguage v k) := fun c j =>
    ⟨(decimalWordIndexEquiv k).symm (c.1 j), by
      intro r hocc
      have hz : (ν : Measure UnitAddCircle)
          (decimalCylinder k (c.1 j)) = 0 := by
        simpa using arbitraryShift_zero_mass_transfer ν hinvariant v hzero
          ((decimalWordIndexEquiv k).symm (c.1 j)) r.val hocc
      have hwhole := zero_mass_transfer_to_aligned_position ν hinvariant
        (c.1 j) hz c.1 j rfl
      have hp := c.2
      rw [hwhole] at hp
      exact (lt_self_iff_false 0).mp hp⟩
  have hinjective : Function.Injective encode := by
    intro c d hcd
    apply Subtype.ext
    funext j
    have hj := congrArg Subtype.val (congrFun hcd j)
    exact (decimalWordIndexEquiv k).symm.injective hj
  have hcard := Nat.card_le_card_of_injective encode hinjective
  rw [Nat.card_fun, Nat.card_fin] at hcard
  simpa only [forbiddenWordCount] using hcard

/-- A single set retaining all positive aligned cylinders at every positive
block scale. -/
def entropyFullMassSet (ν : ProbabilityMeasure UnitAddCircle) :
    Set UnitAddCircle :=
  ⋂ k : PositiveLength, fullMassHaarNullIntersection ν k

theorem entropyFullMassSet_measurable
    (ν : ProbabilityMeasure UnitAddCircle) :
    MeasurableSet (entropyFullMassSet ν) := by
  exact MeasurableSet.iInter fun k =>
    fullMassHaarNullIntersection_measurable ν k

theorem entropyFullMassSet_full_measure
    (ν : ProbabilityMeasure UnitAddCircle) :
    (ν : Measure UnitAddCircle) (entropyFullMassSet ν) = 1 := by
  have hcomplEach (k : PositiveLength) :
      (ν : Measure UnitAddCircle)
          (fullMassHaarNullIntersection ν k)ᶜ = 0 := by
    rw [measure_compl (fullMassHaarNullIntersection_measurable ν k)
      (measure_lt_top (ν : Measure UnitAddCircle) _).ne,
      fullMassHaarNullIntersection_full_measure, measure_univ]
    simp
  have hcompl : (ν : Measure UnitAddCircle) (entropyFullMassSet ν)ᶜ = 0 := by
    rw [entropyFullMassSet, compl_iInter]
    exact measure_iUnion_null hcomplEach
  calc
    (ν : Measure UnitAddCircle) (entropyFullMassSet ν) =
        (ν : Measure UnitAddCircle) Set.univ :=
      measure_of_measure_compl_eq_zero hcompl
    _ = 1 := measure_univ

/-- Variable-cardinality decimal covers give the exact intrinsic entropy
Hausdorff-dimension bound. The proof applies T12's fixed exponential cover
bound at every positive block length and then takes their intersection. -/
theorem entropyFullMassSet_dimH_le
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0) :
    dimH (entropyFullMassSet ν) ≤
      ENNReal.ofReal (forbiddenEntropy v / Real.log 10) := by
  have hdim (k : PositiveLength) :
      dimH (entropyFullMassSet ν) ≤
        ENNReal.ofReal (forbiddenLogRatio v k / Real.log 10) := by
    calc
      dimH (entropyFullMassSet ν) ≤
          dimH (fullMassHaarNullIntersection ν k) :=
        dimH_mono (iInter_subset _ k)
      _ ≤ ENNReal.ofReal
          (Real.log (forbiddenWordCount v k : ℝ) /
            (((k : ℕ) : ℝ) * Real.log 10)) :=
        fullMassIntersection_dimH_le_of_atom_growth ν k.property
          (forbiddenWordCount_pos v hell k)
          (positive_mass_atom_count_le_forbiddenWordCount_pow
            ν hinvariant v hzero k)
      _ = ENNReal.ofReal (forbiddenLogRatio v k / Real.log 10) := by
        congr 1
        simp only [forbiddenLogRatio]
        field_simp
  calc
    dimH (entropyFullMassSet ν) ≤
        ⨅ k : PositiveLength,
          ENNReal.ofReal (forbiddenLogRatio v k / Real.log 10) :=
      le_iInf hdim
    _ = ENNReal.ofReal (forbiddenEntropy v / Real.log 10) := by
      symm
      rw [forbiddenEntropy, div_eq_mul_inv,
        Real.iInf_mul_of_nonneg (inv_nonneg.mpr (Real.log_nonneg (by norm_num))),
        ENNReal.ofReal_iInf]
      rfl

/-- The intrinsic entropy is bounded by T12's two-block growth rate. -/
theorem forbiddenEntropy_le_q_rate {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) :
    forbiddenEntropy v ≤
      Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) := by
  have h := forbiddenEntropy_le_ratio v hell (n := 2 * ell) (by omega)
  simpa [forbiddenLogRatio, forbiddenWordCount, forbiddenQ] using h

/-- T12's `q_v` estimate is strictly below full decimal entropy. -/
theorem forbiddenQ_rate_lt_log_ten {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) :
    Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) < Real.log 10 := by
  have hpowpos : 0 < 10 ^ ell := pow_pos (by norm_num) ell
  have hbase : 10 ^ ell - 1 < 10 ^ ell := Nat.sub_lt hpowpos (by omega)
  have hsquare : (10 ^ ell - 1) ^ 2 < (10 ^ ell) ^ 2 :=
    pow_lt_pow_left₀ hbase (Nat.zero_le _) (by norm_num)
  have hq : forbiddenQ v < 10 ^ (2 * ell) := by
    calc
      forbiddenQ v ≤ (10 ^ ell - 1) ^ 2 := forbiddenQ_le_two_half_bound v
      _ < (10 ^ ell) ^ 2 := hsquare
      _ = 10 ^ (2 * ell) := by rw [← pow_mul]; congr 1; omega
  have hqpos : (0 : ℝ) < forbiddenQ v := by
    exact_mod_cast forbiddenQ_pos v hell
  have htenpowpos : (0 : ℝ) < (10 ^ (2 * ell) : ℕ) := by positivity
  have hlog : Real.log (forbiddenQ v : ℝ) <
      Real.log ((10 ^ (2 * ell) : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr hqpos
    · exact Set.mem_Ioi.mpr htenpowpos
    · exact_mod_cast hq
  have hden : (0 : ℝ) < ((2 * ell : ℕ) : ℝ) := by positivity
  calc
    Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) <
        Real.log ((10 ^ (2 * ell) : ℕ) : ℝ) / ((2 * ell : ℕ) : ℝ) :=
      div_lt_div_of_pos_right hlog hden
    _ = Real.log 10 := by
      rw [Nat.cast_pow, Real.log_pow]
      field_simp
      norm_num

theorem forbiddenEntropy_le_q_rate_lt_log_ten {ell : ℕ}
    (v : DecimalWord ell) (hell : 0 < ell) :
    forbiddenEntropy v ≤
        Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) ∧
      Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) < Real.log 10 :=
  ⟨forbiddenEntropy_le_q_rate v hell, forbiddenQ_rate_lt_log_ten v hell⟩

/-- Necessary-only T13 conclusion. Literal failure of canonical C1 produces
an invariant pi empirical cluster carried by a full-mass set whose Hausdorff
dimension is controlled by the intrinsic overlapping forbidden-language
entropy. -/
theorem not_piPositiveLowerBlockDensity_implies_intrinsic_entropy_bound
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ ell : ℕ, 0 < ell ∧ ∃ v : DecimalWord ell,
        (ν : Measure UnitAddCircle)
            (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0 ∧
        Tendsto (forbiddenLogRatio v) atTop (𝓝 (forbiddenEntropy v)) ∧
        forbiddenEntropy v =
          ⨅ n : PositiveLength, forbiddenLogRatio v n ∧
        ∃ E : Set UnitAddCircle,
          MeasurableSet E ∧ (ν : Measure UnitAddCircle) E = 1 ∧
          dimH E ≤ ENNReal.ofReal (forbiddenEntropy v / Real.log 10) ∧
          forbiddenEntropy v ≤
              Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) ∧
          Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) < Real.log 10 := by
  obtain ⟨ν, hcluster, hinvariant, sourceWord, hsourcePos, hsourceZero,
      _hcount, _hentropy, _hrate⟩ :=
    T8.not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit hnot
  let ell := sourceWord.length
  let v : DecimalWord ell :=
    (decimalWordIndexEquiv ell).symm (wordIndex sourceWord)
  have hvzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0 := by
    simpa [v] using hsourceZero
  refine ⟨ν, hcluster, hinvariant, ell, hsourcePos, v, hvzero,
    forbiddenLogRatio_tendsto_entropy v hsourcePos,
    forbiddenEntropy_eq_iInf v, entropyFullMassSet ν,
    entropyFullMassSet_measurable ν, entropyFullMassSet_full_measure ν,
    entropyFullMassSet_dimH_le ν hinvariant hsourcePos v hvzero,
    forbiddenEntropy_le_q_rate v hsourcePos,
    forbiddenQ_rate_lt_log_ten v hsourcePos⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T13

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenWordCount_pos
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenWordCount_submultiplicative
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenLogRatio_tendsto_entropy
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenEntropy_eq_iInf
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.entropyFullMassSet_dimH_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenEntropy_le_q_rate_lt_log_ten
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T13.not_piPositiveLowerBlockDensity_implies_intrinsic_entropy_bound
