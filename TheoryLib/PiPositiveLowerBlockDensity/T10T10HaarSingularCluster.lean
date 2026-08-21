import TheoryLib.PiPositiveLowerBlockDensity.T8T8AlignedEntropyDeficit
import Mathlib.Data.Fin.Rev
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# T10: Haar-singular empirical cluster forced by failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of the literal negation of
canonical C1. It makes no unconditional assertion about pi or C1.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T10

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- Concatenate `m` length-`k` chunks, reversing the little-endian convention
of `finFunctionFinEquiv` to match decimal order. -/
def alignedIndexEquiv (k m : ℕ) :
    (Fin m → Fin (10 ^ k)) ≃ Fin (10 ^ (m * k)) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl _)).trans
    (finFunctionFinEquiv.trans (finCongr (by simp [pow_mul, Nat.mul_comm])))

/-- The aligned chunk code is exactly the ordinary length-`m * k` decimal
code, up to `alignedIndexEquiv`. -/
theorem alignedIndexEquiv_alignedDecimalCode (k m : ℕ) (x : UnitAddCircle) :
    alignedIndexEquiv k m (alignedDecimalCode k m x) =
      decimalCode (m * k) x := by
  have hcoord (z : UnitAddCircle) (n : ℕ) :
      unitCoordinate ((timesTen^[n]) z) =
        Int.fract (unitCoordinate z * (10 : ℝ) ^ n) := by
    have hit : (timesTen^[n]) z =
        ((unitCoordinate z * (10 : ℝ) ^ n : ℝ) : UnitAddCircle) := by
      induction n with
      | zero => simpa using (coe_unitCoordinate z).symm
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          unfold timesTen
          rw [← AddCircle.coe_nsmul]
          congr 1
          norm_num
          ring
    rw [hit]
    simp [unitCoordinate]
  have hfloor (a : ℝ) (q : ℕ) (ha : 0 ≤ a) :
      ⌊a * q⌋₊ = ⌊a⌋₊ * q + ⌊Int.fract a * q⌋₊ := by
    have ha_bounds : (⌊a⌋₊ : ℝ) ≤ a ∧ a < (⌊a⌋₊ : ℝ) + 1 :=
      ⟨Nat.floor_le ha, Nat.lt_floor_add_one a⟩
    have hifloor : ⌊a⌋ = (⌊a⌋₊ : ℤ) := by
      rw [Int.floor_eq_iff]
      exact_mod_cast ha_bounds
    have hadecomp : a = (⌊a⌋₊ : ℝ) + Int.fract a := by
      rw [Int.fract, hifloor]
      push_cast
      ring
    rw [Nat.floor_eq_iff (mul_nonneg ha (Nat.cast_nonneg q))]
    constructor
    · calc
        ((⌊a⌋₊ * q + ⌊Int.fract a * q⌋₊ : ℕ) : ℝ) =
            (⌊a⌋₊ : ℝ) * q + (⌊Int.fract a * q⌋₊ : ℝ) := by
          push_cast
          ring
        _ ≤ (⌊a⌋₊ : ℝ) * q + Int.fract a * q := by
          gcongr
          exact Nat.floor_le
            (mul_nonneg (Int.fract_nonneg a) (Nat.cast_nonneg q))
        _ = a * q := by nlinarith [hadecomp]
    · calc
        a * q = (⌊a⌋₊ : ℝ) * q + Int.fract a * q := by
          nlinarith [hadecomp]
        _ < (⌊a⌋₊ : ℝ) * q + (⌊Int.fract a * q⌋₊ : ℝ) + 1 := by
          linarith [Nat.lt_floor_add_one ((Int.fract a : ℝ) * q)]
        _ = ((⌊a⌋₊ * q + ⌊Int.fract a * q⌋₊ : ℕ) : ℝ) + 1 := by
          push_cast
          ring
  apply Fin.ext
  simp only [alignedIndexEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply,
    finFunctionFinEquiv_apply, finCongr_apply, Fin.val_cast]
  induction m generalizing x with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, decimalCode,
        Fin.val_mk, Nat.zero_mul, pow_zero, Nat.cast_one, mul_one]
      symm
      rw [Nat.floor_eq_iff (unitCoordinate_nonneg x)]
      exact ⟨by simpa only [Nat.cast_zero] using unitCoordinate_nonneg x,
        by simpa using unitCoordinate_lt_one x⟩
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp [alignedDecimalCode]
      have hs := ih ((timesTen^[k]) x)
      simp [alignedDecimalCode] at hs
      have hs' :
          ∑ i : Fin m,
              (decimalCode k ((timesTen^[(m - i.val) * k]) x)).val *
                (10 ^ k) ^ i.val =
            (decimalCode (m * k) ((timesTen^[k]) x)).val := by
        rw [← hs]
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg
          (fun z => (decimalCode k z).val * (10 ^ k) ^ i.val)
        rw [← Function.iterate_add_apply]
        congr 1
        symm
        have hi : m - (i.val + 1) + 1 = m - i.val := by omega
        calc
          (m - (i.val + 1)) * k + k =
              (m - (i.val + 1) + 1) * k := by ring
          _ = (m - i.val) * k := by rw [hi]
      rw [hs']
      simp only [decimalCode, Fin.val_mk]
      rw [hcoord]
      have hpow : (10 ^ k) ^ m = 10 ^ (m * k) := by
        rw [← pow_mul, Nat.mul_comm]
      rw [hpow]
      norm_cast
      rw [add_comm, ← hfloor]
      · congr 1
        push_cast
        simp only [Nat.succ_mul, pow_add]
        ring
      · exact mul_nonneg (unitCoordinate_nonneg x) (by positivity)

/-- An aligned chunk fiber is the ordinary decimal cylinder obtained by
concatenating its chunks. -/
theorem alignedDecimalCylinder_eq_decimalCylinder (k m : ℕ)
    (c : Fin m → Fin (10 ^ k)) :
    alignedDecimalCylinder k m c =
      decimalCylinder (m * k) (alignedIndexEquiv k m c) := by
  ext x
  simp only [alignedDecimalCylinder, decimalCylinder, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [← alignedIndexEquiv_alignedDecimalCode k m x]
    exact congrArg (alignedIndexEquiv k m) hx
  · intro hx
    apply (alignedIndexEquiv k m).injective
    rw [alignedIndexEquiv_alignedDecimalCode]
    exact hx

/-- Every ordinary length-`n` decimal cylinder has Haar mass `10⁻ⁿ`. -/
theorem haar_decimalCylinder (n : ℕ) (a : Fin (10 ^ n)) :
    volume (decimalCylinder n a) = ((10 : ENNReal) ^ n)⁻¹ := by
  let q : ℝ := (10 : ℝ) ^ n
  have hq : 0 < q := by positivity
  have hcoord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
      unitCoordinate (x : UnitAddCircle) = x := by
    exact congrArg Subtype.val
      (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0)
        (show x ∈ Set.Ico (0 : ℝ) (0 + 1) by simpa using ⟨hx0, hx1⟩))
  have hcoord_one : unitCoordinate ((1 : ℝ) : UnitAddCircle) = 0 := by
    rw [show ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by
      norm_num]
    exact hcoord le_rfl zero_lt_one
  rw [AddCircle.add_projection_respects_measure 1 0
    (decimalCylinder_measurable n a)]
  simp only [zero_add]
  have har : ((a : ℕ) + 1 : ℝ) / q ≤ 1 := by
    rw [div_le_one hq]
    have harNat : (a : ℕ) + 1 ≤ 10 ^ n := Nat.succ_le_iff.mpr a.isLt
    have harReal : (((a : ℕ) + 1 : ℕ) : ℝ) ≤ ((10 ^ n : ℕ) : ℝ) := by
      exact_mod_cast harNat
    simpa [q] using harReal
  by_cases ha : (a : ℕ) = 0
  · have hset :
        ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹' decimalCylinder n a) ∩
            Set.Ioc 0 1 =
          Set.Ioo 0 (1 / q) ∪ {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc,
        Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxCylinder, hx0, hx1⟩
        by_cases hxOne : x = 1
        · exact Or.inr hxOne
        · left
          have hxlt : x < 1 := lt_of_le_of_ne hx1 hxOne
          rw [mem_decimalCylinder_iff, hcoord hx0.le hxlt] at hxCylinder
          refine ⟨hx0, ?_⟩
          calc
            x < ((a : ℕ) + 1 : ℝ) / (10 : ℝ) ^ n := hxCylinder.2
            _ = 1 / q := by rw [ha]; simp [q]
      · rintro (hx | rfl)
        · have hxlt : x < 1 := hx.2.trans_le (by simpa [ha] using har)
          refine ⟨?_, hx.1, hxlt.le⟩
          rw [mem_decimalCylinder_iff, hcoord hx.1.le hxlt]
          constructor
          · simpa [ha] using hx.1.le
          · calc
              x < 1 / q := hx.2
              _ = ((a : ℕ) + 1 : ℝ) / (10 : ℝ) ^ n := by
                rw [ha]
                simp [q]
        · refine ⟨?_, by norm_num, by norm_num⟩
          rw [mem_decimalCylinder_iff, hcoord_one]
          constructor
          · rw [ha]
            norm_num
          · positivity
    have hdis : Disjoint (Set.Ioo 0 (1 / q)) ({1} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr (by
        intro hx
        have hxq : 1 / q ≤ 1 := by simpa [ha] using har
        exact not_lt_of_ge hxq hx.2)
    rw [hset, measure_union hdis (measurableSet_singleton (1 : ℝ)),
      Real.volume_Ioo, Real.volume_singleton, add_zero]
    · have hdiff : 1 / q - 0 = q⁻¹ := by ring
      rw [hdiff, ENNReal.ofReal_inv_of_pos hq]
      simp [q]
  · have hal : 0 < (a : ℝ) / q := div_pos (by exact_mod_cast Nat.pos_of_ne_zero ha) hq
    have hset :
        ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹' decimalCylinder n a) ∩
            Set.Ioc 0 1 =
          Set.Ico ((a : ℕ) / q) (((a : ℕ) + 1) / q) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc,
        Set.mem_Ico]
      constructor
      · rintro ⟨hxCylinder, hx0, hx1⟩
        have hxOne : x ≠ 1 := by
          intro hx
          subst x
          rw [mem_decimalCylinder_iff, hcoord_one] at hxCylinder
          exact (not_le_of_gt hal) (by simpa [q] using hxCylinder.1)
        have hxlt : x < 1 := lt_of_le_of_ne hx1 hxOne
        rw [mem_decimalCylinder_iff, hcoord hx0.le hxlt] at hxCylinder
        simpa [q] using hxCylinder
      · intro hx
        have hx0 : 0 < x := hal.trans_le (by simpa [q] using hx.1)
        have hxlt : x < 1 := (by simpa [q] using hx.2.trans_le har)
        refine ⟨?_, hx0, hxlt.le⟩
        rw [mem_decimalCylinder_iff, hcoord hx0.le hxlt]
        simpa [q] using hx
    rw [hset, Real.volume_Ico]
    have hdiff : (((a : ℕ) + 1 : ℝ) / q) - (a : ℕ) / q = q⁻¹ := by
      field_simp
      ring
    rw [hdiff, ENNReal.ofReal_inv_of_pos hq]
    simp [q]

/-- Every aligned length-`m * k` decimal cylinder has its expected normalized
Haar mass. -/
theorem haar_alignedDecimalCylinder (k m : ℕ)
    (c : Fin m → Fin (10 ^ k)) :
    volume (alignedDecimalCylinder k m c) =
      ((10 : ENNReal) ^ (m * k))⁻¹ := by
  rw [alignedDecimalCylinder_eq_decimalCylinder, haar_decimalCylinder]

/-- The union of exactly those aligned cylinders carrying positive `ν`-mass. -/
def positiveAlignedCylinderUnion (ν : ProbabilityMeasure UnitAddCircle)
    (k m : ℕ) : Set UnitAddCircle :=
  ⋃ c : PositiveAlignedAtom ν k m, alignedDecimalCylinder k m c.1

/-- Named cylinder-union membership theorem. -/
theorem mem_positiveAlignedCylinderUnion_iff
    (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) (x : UnitAddCircle) :
    x ∈ positiveAlignedCylinderUnion ν k m ↔
      ∃ c : Fin m → Fin (10 ^ k),
        0 < (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c) ∧
          x ∈ alignedDecimalCylinder k m c := by
  simp only [positiveAlignedCylinderUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hx⟩
    exact ⟨c.1, c.2, hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨⟨c, hc⟩, hx⟩

theorem positiveAlignedCylinderUnion_measurable
    (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) :
    MeasurableSet (positiveAlignedCylinderUnion ν k m) := by
  classical
  letI : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  exact MeasurableSet.iUnion fun c =>
    alignedDecimalCylinder_measurable k m c.1

/-- The positive aligned cylinders contain `ν`-almost every point. -/
theorem positiveAlignedCylinderUnion_full_measure
    (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) :
    (ν : Measure UnitAddCircle) (positiveAlignedCylinderUnion ν k m) = 1 := by
  classical
  letI : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  let ZeroAtom := {c : Fin m → Fin (10 ^ k) //
    ¬0 < (ν : Measure UnitAddCircle) (alignedDecimalCylinder k m c)}
  have hcompl : (ν : Measure UnitAddCircle)
      (positiveAlignedCylinderUnion ν k m)ᶜ = 0 := by
    apply measure_mono_null (t := ⋃ c : ZeroAtom,
      alignedDecimalCylinder k m c.1)
    · intro x hx
      let c := alignedDecimalCode k m x
      have hxc : x ∈ alignedDecimalCylinder k m c := by
        change alignedDecimalCode k m x = c
        rfl
      have hc0 : ¬0 < (ν : Measure UnitAddCircle)
          (alignedDecimalCylinder k m c) := by
        intro hc
        exact hx (Set.mem_iUnion.2 ⟨⟨c, hc⟩, hxc⟩)
      exact Set.mem_iUnion.2 ⟨⟨c, hc0⟩, hxc⟩
    · apply measure_iUnion_null
      intro c
      exact nonpos_iff_eq_zero.mp (not_lt.mp c.2)
  calc
    (ν : Measure UnitAddCircle) (positiveAlignedCylinderUnion ν k m) =
        (ν : Measure UnitAddCircle) Set.univ :=
      measure_of_measure_compl_eq_zero hcompl
    _ = 1 := measure_univ

/-- Named geometric Haar bound. One forbidden length-`k` chunk removes at
least one of the `10^k` choices at every aligned position. -/
theorem positiveAlignedCylinderUnion_haar_le
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0)
    (m : ℕ) :
    volume (positiveAlignedCylinderUnion ν k m) ≤
      (((10 ^ k - 1 : ℕ) : ENNReal) / ((10 ^ k : ℕ) : ENNReal)) ^ m := by
  classical
  letI : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  have hcount := positive_mass_atom_count ν hinvariant a hzero m
  calc
    volume (positiveAlignedCylinderUnion ν k m) ≤
        ∑' c : PositiveAlignedAtom ν k m,
          volume (alignedDecimalCylinder k m c.1) :=
      measure_iUnion_le _
    _ = (Nat.card (PositiveAlignedAtom ν k m) : ENNReal) *
        ((10 : ENNReal) ^ (m * k))⁻¹ := by
      rw [tsum_fintype]
      simp_rw [haar_alignedDecimalCylinder]
      simp [Nat.card_eq_fintype_card]
    _ ≤ (((10 ^ k - 1) ^ m : ℕ) : ENNReal) *
        ((10 : ENNReal) ^ (m * k))⁻¹ := by
      gcongr
    _ = (((10 ^ k - 1 : ℕ) : ENNReal) /
        ((10 ^ k : ℕ) : ENNReal)) ^ m := by
      simp only [Nat.cast_pow]
      rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]
      congr 1
      congr 1
      rw [← pow_mul, Nat.mul_comm]
      norm_num

/-- The countable intersection of all positive aligned-cylinder unions. -/
def fullMassHaarNullIntersection (ν : ProbabilityMeasure UnitAddCircle)
    (k : ℕ) : Set UnitAddCircle :=
  ⋂ m : ℕ, positiveAlignedCylinderUnion ν k m

theorem fullMassHaarNullIntersection_measurable
    (ν : ProbabilityMeasure UnitAddCircle) (k : ℕ) :
    MeasurableSet (fullMassHaarNullIntersection ν k) := by
  exact MeasurableSet.iInter fun m =>
    positiveAlignedCylinderUnion_measurable ν k m

theorem fullMassHaarNullIntersection_full_measure
    (ν : ProbabilityMeasure UnitAddCircle) (k : ℕ) :
    (ν : Measure UnitAddCircle) (fullMassHaarNullIntersection ν k) = 1 := by
  have hcomplEach (m : ℕ) :
      (ν : Measure UnitAddCircle)
          (positiveAlignedCylinderUnion ν k m)ᶜ = 0 := by
    rw [measure_compl (positiveAlignedCylinderUnion_measurable ν k m)
      (measure_lt_top (ν : Measure UnitAddCircle) _).ne,
      positiveAlignedCylinderUnion_full_measure, measure_univ]
    simp
  have hcompl : (ν : Measure UnitAddCircle)
      (fullMassHaarNullIntersection ν k)ᶜ = 0 := by
    rw [fullMassHaarNullIntersection, compl_iInter]
    exact measure_iUnion_null hcomplEach
  calc
    (ν : Measure UnitAddCircle) (fullMassHaarNullIntersection ν k) =
        (ν : Measure UnitAddCircle) Set.univ :=
      measure_of_measure_compl_eq_zero hcompl
    _ = 1 := measure_univ

theorem fullMassHaarNullIntersection_haar_zero
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (_hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0) :
    volume (fullMassHaarNullIntersection ν k) = 0 := by
  let q : ENNReal :=
    ((10 ^ k - 1 : ℕ) : ENNReal) / ((10 ^ k : ℕ) : ENNReal)
  have hq : q < 1 := by
    apply (ENNReal.div_lt_iff (Or.inl (by positivity))
      (Or.inl (by simp))).2
    simp only [one_mul]
    exact_mod_cast Nat.sub_lt (pow_pos (by norm_num) k) (by norm_num : 0 < 1)
  have hbound (m : ℕ) :
      volume (fullMassHaarNullIntersection ν k) ≤ q ^ m := by
    calc
      volume (fullMassHaarNullIntersection ν k) ≤
          volume (positiveAlignedCylinderUnion ν k m) :=
        measure_mono (iInter_subset _ m)
      _ ≤ q ^ m := positiveAlignedCylinderUnion_haar_le
        ν hinvariant a hzero m
  apply bot_unique
  exact ge_of_tendsto'
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hbound

/-- Named full-mass Haar-null intersection theorem. -/
theorem fullMassHaarNullIntersection_spec
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0) :
    MeasurableSet (fullMassHaarNullIntersection ν k) ∧
      (ν : Measure UnitAddCircle) (fullMassHaarNullIntersection ν k) = 1 ∧
      volume (fullMassHaarNullIntersection ν k) = 0 := by
  exact ⟨fullMassHaarNullIntersection_measurable ν k,
    fullMassHaarNullIntersection_full_measure ν k,
    fullMassHaarNullIntersection_haar_zero ν hinvariant hk a hzero⟩

/-- An invariant probability measure missing one nonempty decimal cylinder is
mutually singular with normalized Haar measure. -/
theorem mutuallySingular_haar_of_invariant_missingCylinder
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0) :
    (ν : Measure UnitAddCircle) ⟂ₘ volume := by
  let S := fullMassHaarNullIntersection ν k
  have hSmeas : MeasurableSet S := fullMassHaarNullIntersection_measurable ν k
  have hSfull : (ν : Measure UnitAddCircle) S = 1 :=
    fullMassHaarNullIntersection_full_measure ν k
  have hScompl : (ν : Measure UnitAddCircle) Sᶜ = 0 := by
    rw [measure_compl hSmeas (measure_lt_top (ν : Measure UnitAddCircle) _).ne,
      hSfull, measure_univ]
    simp
  have hSzero : volume S = 0 :=
    fullMassHaarNullIntersection_haar_zero ν hinvariant hk a hzero
  exact ⟨Sᶜ, hSmeas.compl, hScompl, by simpa using hSzero⟩

/-- Necessary-only T10 conclusion. Literal failure of canonical C1 yields an
invariant pi empirical cluster carried by measurable unions of positive-mass
aligned decimal cylinders. Their Haar masses decay geometrically, and their
full-`ν` intersection witnesses mutual singularity with Haar measure. This
theorem makes no unconditional assertion about pi or C1. -/
theorem not_piPositiveLowerBlockDensity_implies_haar_singular_cluster
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ k : ℕ, 0 < k ∧ ∃ a : Fin (10 ^ k),
        (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0 ∧
        let E : ℕ → Set UnitAddCircle :=
          fun m => positiveAlignedCylinderUnion ν k m
        let S : Set UnitAddCircle := ⋂ m : ℕ, E m
        (∀ m : ℕ, MeasurableSet (E m)) ∧
          (∀ m : ℕ, (ν : Measure UnitAddCircle) (E m) = 1) ∧
          (∀ m : ℕ, volume (E m) ≤
            (((10 ^ k - 1 : ℕ) : ENNReal) /
              ((10 ^ k : ℕ) : ENNReal)) ^ m) ∧
          MeasurableSet S ∧
          (ν : Measure UnitAddCircle) S = 1 ∧
          volume S = 0 ∧
          (ν : Measure UnitAddCircle) ⟂ₘ volume := by
  obtain ⟨ν, hcluster, hinvariant, v, hvpos, hzero, hcount,
      hentropy, hrate⟩ :=
    T8.not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit hnot
  refine ⟨ν, hcluster, hinvariant, v.length, hvpos, wordIndex v, hzero, ?_⟩
  dsimp only
  refine ⟨positiveAlignedCylinderUnion_measurable ν v.length,
    positiveAlignedCylinderUnion_full_measure ν v.length,
    positiveAlignedCylinderUnion_haar_le ν hinvariant (wordIndex v) hzero,
    ?_⟩
  change MeasurableSet (fullMassHaarNullIntersection ν v.length) ∧
    (ν : Measure UnitAddCircle)
        (fullMassHaarNullIntersection ν v.length) = 1 ∧
    volume (fullMassHaarNullIntersection ν v.length) = 0 ∧
    (ν : Measure UnitAddCircle) ⟂ₘ volume
  exact ⟨fullMassHaarNullIntersection_measurable ν v.length,
    fullMassHaarNullIntersection_full_measure ν v.length,
    fullMassHaarNullIntersection_haar_zero ν hinvariant hvpos
      (wordIndex v) hzero,
    mutuallySingular_haar_of_invariant_missingCylinder ν hinvariant hvpos
      (wordIndex v) hzero⟩

end Theory.PiDigits.PositiveLowerBlockDensity.T10

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.haar_alignedDecimalCylinder
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.mem_positiveAlignedCylinderUnion_iff
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.positiveAlignedCylinderUnion_full_measure
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.positiveAlignedCylinderUnion_haar_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.fullMassHaarNullIntersection_spec
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.mutuallySingular_haar_of_invariant_missingCylinder
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T10.not_piPositiveLowerBlockDensity_implies_haar_singular_cluster
