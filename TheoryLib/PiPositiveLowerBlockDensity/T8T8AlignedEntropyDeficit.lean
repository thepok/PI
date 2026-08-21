import TheoryLib.PiPositiveLowerBlockDensity.T7T7InvariantEmpiricalCluster
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# T8: aligned entropy deficit forced by failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of the literal negation of
canonical C1. It makes no unconditional assertion about pi or C1. Entropy uses
the natural logarithm, and only the lengths aligned to the extracted word are
considered.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T8

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7

/-- The canonical representative of a point of `R/Z` in `[0,1)`. -/
def unitCoordinate (x : UnitAddCircle) : ℝ :=
  AddCircle.equivIco 1 0 x

theorem unitCoordinate_nonneg (x : UnitAddCircle) : 0 ≤ unitCoordinate x :=
  (AddCircle.equivIco 1 0 x).property.1

theorem unitCoordinate_lt_one (x : UnitAddCircle) : unitCoordinate x < 1 := by
  simpa [unitCoordinate] using (AddCircle.equivIco 1 0 x).property.2

theorem coe_unitCoordinate (x : UnitAddCircle) :
    (unitCoordinate x : UnitAddCircle) = x := by
  simpa [unitCoordinate] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) x)

theorem unitCoordinate_measurable : Measurable unitCoordinate := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

/-- The index of the canonical length-`n` half-open decimal cylinder containing
`x`. -/
def decimalCode (n : ℕ) (x : UnitAddCircle) : Fin (10 ^ n) := by
  let q : ℕ := 10 ^ n
  refine ⟨⌊unitCoordinate x * (q : ℝ)⌋₊, ?_⟩
  apply (Nat.floor_lt (mul_nonneg (unitCoordinate_nonneg x) (Nat.cast_nonneg q))).2
  have hq : 0 < (q : ℝ) := by positivity
  change unitCoordinate x * (q : ℝ) < (q : ℝ)
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right (unitCoordinate_lt_one x) hq)

/-- The canonical boundary-safe cylinder `[a/10^n,(a+1)/10^n)` on `R/Z`. -/
def decimalCylinder (n : ℕ) (a : Fin (10 ^ n)) : Set UnitAddCircle :=
  decimalCode n ⁻¹' {a}

theorem mem_decimalCylinder_iff (n : ℕ) (a : Fin (10 ^ n))
    (x : UnitAddCircle) :
    x ∈ decimalCylinder n a ↔
      unitCoordinate x ∈ Set.Ico
        ((a : ℕ) / (10 ^ n : ℝ)) (((a : ℕ) + 1) / (10 ^ n : ℝ)) := by
  have hq : 0 < (10 ^ n : ℝ) := by positivity
  have hx0 : 0 ≤ unitCoordinate x * (10 ^ n : ℝ) :=
    mul_nonneg (unitCoordinate_nonneg x) hq.le
  simp only [decimalCylinder, Set.mem_preimage, Set.mem_singleton_iff]
  unfold decimalCode
  dsimp only
  rw [Fin.ext_iff]
  change ⌊unitCoordinate x * (10 ^ n : ℕ)⌋₊ = (a : ℕ) ↔ _
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hx0 ⊢
  rw [Nat.floor_eq_iff hx0]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨(div_le_iff₀ hq).2 hl,
      (lt_div_iff₀ hq).2 (by simpa only [Nat.cast_add, Nat.cast_one] using hr)⟩
  · rintro ⟨hl, hr⟩
    exact ⟨(div_le_iff₀ hq).1 hl,
      by simpa only [Nat.cast_add, Nat.cast_one] using (lt_div_iff₀ hq).1 hr⟩

theorem decimalCylinder_measurable (n : ℕ) (a : Fin (10 ^ n)) :
    MeasurableSet (decimalCylinder n a) := by
  rw [Set.ext_iff.mpr (fun x => mem_decimalCylinder_iff n a x)]
  exact measurableSet_Ico.preimage unitCoordinate_measurable

theorem decimalCode_measurable (n : ℕ) : Measurable (decimalCode n) := by
  apply measurable_to_countable'
  intro a
  exact decimalCylinder_measurable n a

/-- Turn a decimal word into its numerical cylinder index. -/
def wordIndex (w : List (Fin 10)) : Fin (10 ^ w.length) :=
  ⟨Theory.PiDigits.T20.wordValue w,
    Theory.PiDigits.T20.wordValue_lt_pow_length w⟩

theorem wordValue_append_digit (w : List (Fin 10)) (d : Fin 10) :
    Theory.PiDigits.T20.wordValue (w ++ [d]) =
      10 * Theory.PiDigits.T20.wordValue w + d.val := by
  induction w with
  | nil => simp [Theory.PiDigits.T20.wordValue]
  | cons e w ih =>
      simp only [List.cons_append, Theory.PiDigits.T20.wordValue,
        List.length_append, List.length_singleton, Nat.add_comm, pow_succ, ih]
      ring

/-- Appending digit four selects a child cylinder strictly inside T7's open
middle-half cylinder ball. -/
def innerChild (w : List (Fin 10)) : List (Fin 10) :=
  w ++ [⟨4, by omega⟩]

@[simp] theorem innerChild_length (w : List (Fin 10)) :
    (innerChild w).length = w.length + 1 := by
  simp [innerChild]

/-- Named boundary-safe subcylinder extraction. -/
theorem boundarySafe_subcylinder_extraction (w : List (Fin 10)) :
    (innerChild w).length > 0 ∧
      decimalCylinder (innerChild w).length (wordIndex (innerChild w)) ⊆
        decimalInnerSet w := by
  constructor
  · simp [innerChild]
  · intro x hx
    rw [mem_decimalCylinder_iff] at hx
    have hpow : 0 < (10 : ℝ) ^ w.length := by positivity
    have hleftEq :
        ((Theory.PiDigits.T20.wordValue (innerChild w) : ℝ) /
            (10 : ℝ) ^ (innerChild w).length) =
          Theory.PiDigits.T27.decimalCylinderLeft w +
            (4 / 10 : ℝ) *
              Theory.PiDigits.T27.decimalCylinderLength w.length := by
      simp only [innerChild, wordValue_append_digit, List.length_append,
        List.length_singleton, Nat.add_comm, pow_succ,
        Theory.PiDigits.T27.decimalCylinderLeft,
        Theory.PiDigits.T27.decimalCylinderLength, inv_eq_one_div]
      push_cast
      field_simp
      ring
    have hrightEq :
        (((Theory.PiDigits.T20.wordValue (innerChild w) : ℝ) + 1) /
            (10 : ℝ) ^ (innerChild w).length) = decimalCylinderCenter w := by
      simp only [innerChild, wordValue_append_digit, List.length_append,
        List.length_singleton, Nat.add_comm, pow_succ, decimalCylinderCenter,
        Theory.PiDigits.T27.decimalCylinderLeft,
        Theory.PiDigits.T27.decimalCylinderLength, inv_eq_one_div]
      push_cast
      field_simp
      ring
    have hleft :
        Theory.PiDigits.T27.decimalCylinderLeft w +
            (4 / 10 : ℝ) * Theory.PiDigits.T27.decimalCylinderLength w.length ≤
          unitCoordinate x := by
      rw [← hleftEq]
      exact hx.1
    have hright : unitCoordinate x < decimalCylinderCenter w := by
      rw [← hrightEq]
      simpa only [wordIndex] using hx.2
    rw [decimalInnerSet, Metric.mem_ball, ← coe_unitCoordinate x, dist_eq_norm,
      ← QuotientAddGroup.mk_sub]
    apply lt_of_le_of_lt QuotientAddGroup.norm_mk_le_norm
    change |unitCoordinate x - decimalCylinderCenter w| <
      decimalCylinderInnerRadius w
    rw [abs_of_nonpos (sub_nonpos.mpr hright.le)]
    unfold decimalCylinderCenter decimalCylinderInnerRadius
    have hlen := Theory.PiDigits.T27.decimalCylinderLength_pos w.length
    linarith

/-- The aligned code records the `m` successive length-`k` decimal chunks. -/
def alignedDecimalCode (k m : ℕ) (x : UnitAddCircle) :
    Fin m → Fin (10 ^ k) :=
  fun j => decimalCode k ((timesTen^[j.val * k]) x)

/-- A length-`m*k` aligned decimal cylinder, represented by its `m` chunks. -/
def alignedDecimalCylinder (k m : ℕ) (c : Fin m → Fin (10 ^ k)) :
    Set UnitAddCircle :=
  alignedDecimalCode k m ⁻¹' {c}

theorem alignedDecimalCode_measurable (k m : ℕ) :
    Measurable (alignedDecimalCode k m) := by
  apply measurable_pi_lambda
  intro j
  exact (decimalCode_measurable k).comp
    (timesTen_continuous.iterate (j.val * k)).measurable

theorem alignedDecimalCylinder_measurable (k m : ℕ)
    (c : Fin m → Fin (10 ^ k)) :
    MeasurableSet (alignedDecimalCylinder k m c) := by
  exact (measurableSet_singleton c).preimage (alignedDecimalCode_measurable k m)

/-- T7 invariance transfers the measure of a measurable set to every iterated
preimage. -/
theorem invariant_iterate_preimage_measure (ν : ProbabilityMeasure UnitAddCircle)
    (hinvariant : timesTenMap ν = ν) (A : Set UnitAddCircle)
    (hA : MeasurableSet A) (r : ℕ) :
    (ν : Measure UnitAddCircle) ((timesTen^[r]) ⁻¹' A) =
      (ν : Measure UnitAddCircle) A := by
  have hstep (B : Set UnitAddCircle) (hB : MeasurableSet B) :
      (ν : Measure UnitAddCircle) (timesTen ⁻¹' B) =
        (ν : Measure UnitAddCircle) B := by
    calc
      (ν : Measure UnitAddCircle) (timesTen ⁻¹' B) =
          Measure.map timesTen (ν : Measure UnitAddCircle) B := by
        rw [Measure.map_apply timesTen_continuous.measurable hB]
      _ = (timesTenMap ν : Measure UnitAddCircle) B := by
        simp only [timesTenMap, ProbabilityMeasure.toMeasure_map]
      _ = (ν : Measure UnitAddCircle) B := by rw [hinvariant]
  induction r with
  | zero => simp
  | succ r ih =>
      change (ν : Measure UnitAddCircle)
        ((timesTen^[Nat.succ r]) ⁻¹' A) = _
      rw [Function.iterate_succ]
      change (ν : Measure UnitAddCircle)
        (timesTen ⁻¹' ((timesTen^[r]) ⁻¹' A)) = _
      exact (hstep ((timesTen^[r]) ⁻¹' A)
        (hA.preimage (timesTen_continuous.iterate r).measurable)).trans ih

/-- Named zero-mass transfer: any aligned cylinder having the forbidden chunk
at one aligned position has zero mass. -/
theorem zero_mass_transfer_to_aligned_position
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k m : ℕ} (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0)
    (c : Fin m → Fin (10 ^ k)) (j : Fin m) (hcj : c j = a) :
    (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c) = 0 := by
  have hsubset : alignedDecimalCylinder k m c ⊆
      (timesTen^[j.val * k]) ⁻¹' decimalCylinder k a := by
    intro x hx
    have hcode : alignedDecimalCode k m x = c := hx
    change decimalCode k ((timesTen^[j.val * k]) x) = a
    exact (congrFun hcode j).trans hcj
  apply bot_unique
  calc
    (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c) ≤
        (ν : Measure UnitAddCircle)
          ((timesTen^[j.val * k]) ⁻¹' decimalCylinder k a) :=
      measure_mono hsubset
    _ = (ν : Measure UnitAddCircle) (decimalCylinder k a) :=
      invariant_iterate_preimage_measure ν hinvariant _
        (decimalCylinder_measurable k a) _
    _ = 0 := hzero

/-- Aligned cylinders carrying positive mass. -/
def PositiveAlignedAtom (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) :=
  {c : Fin m → Fin (10 ^ k) //
    0 < (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c)}

/-- Named positive-atom count. One forbidden chunk leaves at most
`(10^k-1)^m` positive length-`m*k` cylinders. -/
theorem positive_mass_atom_count
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0)
    (m : ℕ) :
    Nat.card (PositiveAlignedAtom ν k m) ≤ (10 ^ k - 1) ^ m := by
  let encode : PositiveAlignedAtom ν k m →
      (Fin m → {b : Fin (10 ^ k) // b ≠ a}) := fun c j =>
    ⟨c.1 j, by
      intro hcj
      have hz := zero_mass_transfer_to_aligned_position ν hinvariant a hzero c.1 j hcj
      have hp := c.2
      rw [hz] at hp
      exact (lt_self_iff_false 0).mp hp⟩
  have hinjective : Function.Injective encode := by
    intro c d hcd
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun hcd j)
  have hcard := Nat.card_le_card_of_injective encode hinjective
  have hallowed : Nat.card {b : Fin (10 ^ k) // b ≠ a} = 10 ^ k - 1 := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  rw [Nat.card_fun, Nat.card_fin, hallowed] at hcard
  exact hcard

/-- Shannon entropy of the finite aligned decimal-cylinder distribution. -/
def alignedShannonEntropy (ν : ProbabilityMeasure UnitAddCircle)
    (k m : ℕ) : ℝ :=
  ∑ c : Fin m → Fin (10 ^ k),
    Real.negMulLog
      ((ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c)).toReal

/-- Reusable finite Shannon inequality: a probability vector with at most `M`
positive entries has entropy at most `log M`. -/
theorem finiteShannonEntropy_le_log_support
    {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤
      Real.log (Nat.card {i : ι // 0 < p i}) := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => 0 < p i
  have hp_zero {i : ι} (hi : i ∉ S) : p i = 0 := by
    have hnpos : ¬0 < p i := by simpa [S] using hi
    exact le_antisymm (not_lt.mp hnpos) (hp0 i)
  have hsumS : (∑ i ∈ S, p i) = 1 := by
    calc
      (∑ i ∈ S, p i) = ∑ i, p i := by
        apply Finset.sum_subset (by simp [S])
        intro i _ hi
        exact hp_zero hi
      _ = 1 := hp1
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsumS
    simp at hsumS
  have hScard : 0 < S.card := Finset.card_pos.mpr hSne
  have hweights : (∑ _i ∈ S, ((S.card : ℝ)⁻¹)) = 1 := by
    simp [hScard.ne']
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := S) (w := fun _i => (S.card : ℝ)⁻¹) (p := p)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg S.card)) hweights
    (fun i _ => hp0 i)
  have hjensen' :
      (S.card : ℝ)⁻¹ * (∑ i ∈ S, Real.negMulLog (p i)) ≤
        Real.negMulLog ((S.card : ℝ)⁻¹) := by
    simpa only [smul_eq_mul, Function.comp_apply, ← Finset.mul_sum,
      hsumS, mul_one] using hjensen
  have hcardReal : 0 < (S.card : ℝ) := by exact_mod_cast hScard
  have hsupportBound :
      (∑ i ∈ S, Real.negMulLog (p i)) ≤ Real.log (S.card : ℝ) := by
    calc
      (∑ i ∈ S, Real.negMulLog (p i)) =
          (S.card : ℝ) *
            ((S.card : ℝ)⁻¹ * (∑ i ∈ S, Real.negMulLog (p i))) := by
        field_simp
      _ ≤ (S.card : ℝ) * Real.negMulLog ((S.card : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hjensen' hcardReal.le
      _ = Real.log (S.card : ℝ) := by
        rw [Real.negMulLog, Real.log_inv]
        field_simp
  have hentropySupport :
      ∑ i, Real.negMulLog (p i) =
        (∑ i ∈ S, Real.negMulLog (p i)) := by
    symm
    apply Finset.sum_subset (by simp [S])
    intro i _ hi
    rw [hp_zero hi, Real.negMulLog_zero]
  have hcardEq : Nat.card {i : ι // 0 < p i} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hentropySupport, hcardEq]
  exact hsupportBound

/-- Named finite entropy bound for the invariant decimal-cylinder
distribution. -/
theorem finite_alignedShannonEntropy_bound
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    alignedShannonEntropy ν k m ≤ m * Real.log (10 ^ k - 1 : ℕ) := by
  classical
  let p : (Fin m → Fin (10 ^ k)) → ℝ := fun c =>
    ((ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c)).toReal
  have hp0 : ∀ c, 0 ≤ p c := fun _ => ENNReal.toReal_nonneg
  have hsumENN :
      ∑ c : Fin m → Fin (10 ^ k),
          (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c) = 1 := by
    have hpartition := sum_measure_preimage_singleton
      (μ := (ν : Measure UnitAddCircle))
      (Finset.univ : Finset (Fin m → Fin (10 ^ k)))
      (fun c _ => alignedDecimalCylinder_measurable k m c)
    simpa only [alignedDecimalCylinder, Finset.coe_univ, Set.preimage_univ,
      measure_univ, ENNReal.coe_one, Finset.sum_filter, Finset.mem_univ,
      ↓reduceIte] using hpartition
  have hp1 : ∑ c, p c = 1 := by
    rw [← ENNReal.toReal_sum (fun c _ =>
      (measure_lt_top (ν : Measure UnitAddCircle)
        (alignedDecimalCylinder k m c)).ne)]
    simp only [p, hsumENN, ENNReal.toReal_one]
  have hentropy := finiteShannonEntropy_le_log_support p hp0 hp1
  have hpos_iff (c : Fin m → Fin (10 ^ k)) :
      0 < p c ↔
        0 < (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c) := by
    simp only [p, ENNReal.toReal_pos_iff]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, measure_lt_top (ν : Measure UnitAddCircle) _⟩
  let supportEquiv : {c // 0 < p c} ≃ PositiveAlignedAtom ν k m :=
    { toFun := fun c => ⟨c.1, (hpos_iff c.1).mp c.2⟩
      invFun := fun c => ⟨c.1, (hpos_iff c.1).mpr c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsupportCard : Nat.card {c // 0 < p c} ≤ (10 ^ k - 1) ^ m := by
    rw [Nat.card_congr supportEquiv]
    exact positive_mass_atom_count ν hinvariant a hzero m
  have hsupportNonempty : Nonempty {c // 0 < p c} := by
    by_contra h
    have hall : ∀ c, p c = 0 := by
      intro c
      apply le_antisymm
      · exact not_lt.mp (fun hc => h ⟨⟨c, hc⟩⟩)
      · exact hp0 c
    have : (0 : ℝ) = 1 := by simpa [hall] using hp1
    norm_num at this
  have hsupportPos : 0 < Nat.card {c // 0 < p c} := Nat.card_pos
  have hApos : 0 < (10 ^ k - 1) ^ m := by
    have : 0 < 10 ^ k - 1 := by
      have hten : 10 ≤ 10 ^ k := by
        simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
      omega
    positivity
  have hlog :
      Real.log (Nat.card {c // 0 < p c}) ≤
        Real.log ((10 ^ k - 1) ^ m : ℕ) := by
    exact Real.log_le_log (by exact_mod_cast hsupportPos)
      (by exact_mod_cast hsupportCard)
  calc
    alignedShannonEntropy ν k m = ∑ c, Real.negMulLog (p c) := rfl
    _ ≤ Real.log (Nat.card {c // 0 < p c}) := hentropy
    _ ≤ Real.log ((10 ^ k - 1) ^ m : ℕ) := hlog
    _ = m * Real.log (10 ^ k - 1 : ℕ) := by
      rw [Nat.cast_pow, Real.log_pow]

/-- Entropy per digit along lengths `m*k`, indexed from `m=1`. -/
def alignedEntropyRate (ν : ProbabilityMeasure UnitAddCircle) (k : ℕ) : ℝ :=
  limsup (fun n => alignedShannonEntropy ν k (n + 1) /
    (((n + 1) * k : ℕ) : ℝ)) atTop

/-- Named strict aligned entropy-rate deficit. -/
theorem strict_aligned_entropyRate_deficit
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0) :
    alignedEntropyRate ν k ≤ Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) ∧
      alignedEntropyRate ν k < Real.log 10 := by
  have hterm (n : ℕ) :
      alignedShannonEntropy ν k (n + 1) /
          (((n + 1) * k : ℕ) : ℝ) ≤
        Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) := by
    have hentropy := finite_alignedShannonEntropy_bound ν hinvariant hk a hzero
      (n + 1) (by omega)
    have hmreal : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity : 0 < (((n + 1) * k : ℕ) : ℝ))]
    calc
      alignedShannonEntropy ν k (n + 1) ≤
          (n + 1) * Real.log (10 ^ k - 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hentropy
      _ = (Real.log (10 ^ k - 1 : ℕ) / (k : ℝ)) *
          (((n + 1) * k : ℕ) : ℝ) := by
        push_cast
        field_simp
  have hnonneg (n : ℕ) :
      0 ≤ alignedShannonEntropy ν k (n + 1) /
        (((n + 1) * k : ℕ) : ℝ) := by
    apply div_nonneg
    · unfold alignedShannonEntropy
      apply Finset.sum_nonneg
      intro c _
      apply Real.negMulLog_nonneg ENNReal.toReal_nonneg
      have hmeasure :
          (ν : Measure UnitAddCircle)
              (alignedDecimalCylinder k (n + 1) c) ≤ 1 := by
        calc
          (ν : Measure UnitAddCircle)
              (alignedDecimalCylinder k (n + 1) c) ≤
              (ν : Measure UnitAddCircle) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have htoReal := (ENNReal.toReal_le_toReal
        (measure_lt_top (ν : Measure UnitAddCircle)
          (alignedDecimalCylinder k (n + 1) c)).ne (by simp)).2 hmeasure
      simpa using htoReal
    · positivity
  have hcobounded : atTop.IsCoboundedUnder (· ≤ ·)
      (fun n => alignedShannonEntropy ν k (n + 1) /
        (((n + 1) * k : ℕ) : ℝ)) :=
    Filter.isCoboundedUnder_le_of_le atTop hnonneg
  have hrate : alignedEntropyRate ν k ≤
      Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) := by
    exact limsup_le_of_le hcobounded (Eventually.of_forall hterm)
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
  have hA : 0 < 10 ^ k - 1 := by omega
  have hpowpos : 0 < 10 ^ k := pow_pos (by norm_num) k
  have hlt : 10 ^ k - 1 < 10 ^ k := Nat.sub_lt hpowpos (by norm_num)
  have hloglt : Real.log (10 ^ k - 1 : ℕ) < Real.log (10 ^ k : ℕ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hA)
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hpowpos)
    · exact_mod_cast hlt
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hstrict : Real.log (10 ^ k - 1 : ℕ) / (k : ℝ) < Real.log 10 := by
    rw [div_lt_iff₀ hkreal]
    rw [Nat.cast_pow, Real.log_pow] at hloglt
    simpa [mul_comm] using hloglt
  exact ⟨hrate, hrate.trans_lt hstrict⟩

/-- Necessary-only T8 conclusion. Literal failure of canonical C1 yields one
invariant pi empirical cluster with an explicit missing subcylinder and a
strict aligned entropy-rate deficit. No failure or truth of C1 is asserted. -/
theorem not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ v : List (Fin 10), 0 < v.length ∧
        (ν : Measure UnitAddCircle)
            (decimalCylinder v.length (wordIndex v)) = 0 ∧
        (∀ m : ℕ, 1 ≤ m →
          Nat.card (PositiveAlignedAtom ν v.length m) ≤
            (10 ^ v.length - 1) ^ m) ∧
        (∀ m : ℕ, 1 ≤ m →
          alignedShannonEntropy ν v.length m ≤
            m * Real.log (10 ^ v.length - 1 : ℕ)) ∧
        alignedEntropyRate ν v.length < Real.log 10 := by
  obtain ⟨k, hk, w, hw, h, hh0, hhbound, eta, heta, hetapos,
      cutoffs, hcutoffs, hcutoffBounds, ν, hν, hcluster, hinvariant,
      hopen, hinnerNonempty, hinnerSubset, hinnerZero, hcoeff, hcoeffPowers⟩ :=
    T7.not_piPositiveLowerBlockDensity_implies_invariant_resonant_cluster hnot
  let v := innerChild w
  have hvpos : 0 < v.length := by
    exact (boundarySafe_subcylinder_extraction w).1
  have hvsubset : decimalCylinder v.length (wordIndex v) ⊆ decimalInnerSet w := by
    exact (boundarySafe_subcylinder_extraction w).2
  have hvzero :
      (ν : Measure UnitAddCircle) (decimalCylinder v.length (wordIndex v)) = 0 := by
    apply bot_unique
    calc
      (ν : Measure UnitAddCircle) (decimalCylinder v.length (wordIndex v)) ≤
          (ν : Measure UnitAddCircle) (decimalInnerSet w) := measure_mono hvsubset
      _ = 0 := hinnerZero
  have hcount (m : ℕ) (_hm : 1 ≤ m) :
      Nat.card (PositiveAlignedAtom ν v.length m) ≤
        (10 ^ v.length - 1) ^ m :=
    positive_mass_atom_count ν hinvariant (wordIndex v) hvzero m
  have hentropy (m : ℕ) (hm : 1 ≤ m) :
      alignedShannonEntropy ν v.length m ≤
        m * Real.log (10 ^ v.length - 1 : ℕ) :=
    finite_alignedShannonEntropy_bound ν hinvariant hvpos (wordIndex v) hvzero m hm
  have hrate : alignedEntropyRate ν v.length < Real.log 10 :=
    (strict_aligned_entropyRate_deficit ν hinvariant hvpos (wordIndex v) hvzero).2
  exact ⟨ν, hcluster, hinvariant, v, hvpos, hvzero, hcount, hentropy, hrate⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T8

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.mem_decimalCylinder_iff
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.boundarySafe_subcylinder_extraction
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.zero_mass_transfer_to_aligned_position
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.positive_mass_atom_count
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.finiteShannonEntropy_le_log_support
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.finite_alignedShannonEntropy_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.strict_aligned_entropyRate_deficit
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T8.not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit
