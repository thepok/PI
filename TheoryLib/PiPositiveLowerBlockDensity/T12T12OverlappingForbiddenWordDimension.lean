import TheoryLib.PiPositiveLowerBlockDensity.T8T8AlignedEntropyDeficit
import TheoryLib.PiPositiveLowerBlockDensity.T11T11HausdorffDimensionDefect

/-!
# T12: overlapping forbidden-word dimension bound under failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only necessary consequences of the literal negation of
canonical C1. It makes no unconditional assertion about pi or C1.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T12

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T10
open Theory.PiDigits.PositiveLowerBlockDensity.T11

/-- Length-`n` decimal words, in left-to-right order. The expression `10 ^ 1`
keeps these words definitionally compatible with T10's one-digit chunks. -/
abbrev DecimalWord (n : ℕ) := Fin n → Fin (10 ^ 1)

/-- The numerical decimal-cylinder index of a fixed-length word. -/
def decimalWordIndexEquiv (n : ℕ) : DecimalWord n ≃ Fin (10 ^ n) :=
  (alignedIndexEquiv 1 n).trans (finCongr (by simp))

theorem decimalCylinder_cast_length {n m : ℕ} (h : n = m)
    (a : Fin (10 ^ n)) :
    decimalCylinder n a =
      decimalCylinder m (Fin.cast (congrArg (fun t : ℕ => 10 ^ t) h) a) := by
  subst m
  rfl

theorem alignedDecimalCylinder_one_eq_decimalCylinder (n : ℕ)
    (w : DecimalWord n) :
    alignedDecimalCylinder 1 n w =
      decimalCylinder n (decimalWordIndexEquiv n w) := by
  calc
    alignedDecimalCylinder 1 n w =
        decimalCylinder (n * 1) (alignedIndexEquiv 1 n w) :=
      alignedDecimalCylinder_eq_decimalCylinder 1 n w
    _ = decimalCylinder n
        (Fin.cast (congrArg (fun t : ℕ => 10 ^ t) (Nat.mul_one n))
          (alignedIndexEquiv 1 n w)) :=
      decimalCylinder_cast_length (Nat.mul_one n) _
    _ = decimalCylinder n (decimalWordIndexEquiv n w) := by
      congr 1

/-- A word `v` occurs contiguously in `w` beginning at shift `r`. -/
def OccursAt {ell n : ℕ} (v : DecimalWord ell) (w : DecimalWord n)
    (r : ℕ) : Prop :=
  ∃ h : r + ell ≤ n,
    ∀ j : Fin ell, w ⟨r + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) h⟩ = v j

instance {ell n : ℕ} (v : DecimalWord ell) (w : DecimalWord n) (r : ℕ) :
    Decidable (OccursAt v w r) := Classical.propDecidable _

/-- The finite language of length-`n` decimal words containing no contiguous
copy of `v`. -/
def ForbiddenLanguage {ell : ℕ} (v : DecimalWord ell) (n : ℕ) :=
  {w : DecimalWord n // ∀ r : Fin (n + 1), ¬ OccursAt v w r.val}

instance forbiddenLanguage_finite {ell : ℕ} (v : DecimalWord ell) (n : ℕ) :
    Finite (ForbiddenLanguage v n) := by
  letI : Fintype (DecimalWord n) := inferInstance
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The refined two-block growth constant. -/
def forbiddenQ {ell : ℕ} (v : DecimalWord ell) : ℕ :=
  Nat.card (ForbiddenLanguage v (2 * ell))

theorem alignedDecimalCode_one_apply (n : ℕ) (x : UnitAddCircle) (i : Fin n) :
    alignedDecimalCode 1 n x i = decimalCode 1 ((timesTen^[i.val]) x) := by
  simp [alignedDecimalCode]

/-- Boundary-safe arbitrary-shift transfer at the level of decimal cylinders. -/
theorem arbitraryShift_cylinder_subset {ell n : ℕ} (v : DecimalWord ell)
    (w : DecimalWord n) (r : ℕ) (hocc : OccursAt v w r) :
    decimalCylinder n (decimalWordIndexEquiv n w) ⊆
      (timesTen^[r]) ⁻¹' decimalCylinder ell (decimalWordIndexEquiv ell v) := by
  obtain ⟨hrange, hmatch⟩ := hocc
  intro x hx
  have hxAligned : x ∈ alignedDecimalCylinder 1 n w := by
    rw [alignedDecimalCylinder_one_eq_decimalCylinder]
    exact hx
  have hcode : alignedDecimalCode 1 n x = w := hxAligned
  have hshifted : alignedDecimalCode 1 ell ((timesTen^[r]) x) = v := by
    funext j
    let i : Fin n :=
      ⟨r + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) hrange⟩
    calc
      alignedDecimalCode 1 ell ((timesTen^[r]) x) j =
          decimalCode 1 ((timesTen^[j.val]) ((timesTen^[r]) x)) :=
        alignedDecimalCode_one_apply ell ((timesTen^[r]) x) j
      _ = decimalCode 1 ((timesTen^[r + j.val]) x) := by
        rw [add_comm, Function.iterate_add_apply]
      _ = alignedDecimalCode 1 n x i := by
        rw [alignedDecimalCode_one_apply]
      _ = w i := congrFun hcode i
      _ = v j := hmatch j
  have hshiftedMem :
      (timesTen^[r]) x ∈ alignedDecimalCylinder 1 ell v := hshifted
  rw [alignedDecimalCylinder_one_eq_decimalCylinder] at hshiftedMem
  exact hshiftedMem

/-- Invariance transfers a zero-mass forbidden cylinder to every occurrence at
an arbitrary shift, including shifts crossing later block boundaries. -/
theorem arbitraryShift_zero_mass_transfer
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell n : ℕ} (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0)
    (w : DecimalWord n) (r : ℕ) (hocc : OccursAt v w r) :
    (ν : Measure UnitAddCircle)
      (decimalCylinder n (decimalWordIndexEquiv n w)) = 0 := by
  apply bot_unique
  calc
    (ν : Measure UnitAddCircle)
        (decimalCylinder n (decimalWordIndexEquiv n w)) ≤
        (ν : Measure UnitAddCircle)
          ((timesTen^[r]) ⁻¹' decimalCylinder ell (decimalWordIndexEquiv ell v)) :=
      measure_mono (arbitraryShift_cylinder_subset v w r hocc)
    _ = (ν : Measure UnitAddCircle)
        (decimalCylinder ell (decimalWordIndexEquiv ell v)) :=
      invariant_iterate_preimage_measure ν hinvariant _
        (decimalCylinder_measurable ell (decimalWordIndexEquiv ell v)) r
    _ = 0 := hzero

/-- The union of all length-`n` cylinders whose words avoid `v`. -/
def forbiddenLanguageCylinderUnion {ell : ℕ} (v : DecimalWord ell) (n : ℕ) :
    Set UnitAddCircle :=
  ⋃ w : ForbiddenLanguage v n,
    decimalCylinder n (decimalWordIndexEquiv n w.1)

theorem forbiddenLanguageCylinderUnion_measurable {ell : ℕ}
    (v : DecimalWord ell) (n : ℕ) :
    MeasurableSet (forbiddenLanguageCylinderUnion v n) := by
  classical
  letI : Fintype (DecimalWord n) := inferInstance
  letI : Finite (ForbiddenLanguage v n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ForbiddenLanguage v n) := Fintype.ofFinite _
  exact MeasurableSet.iUnion fun w =>
    decimalCylinder_measurable n (decimalWordIndexEquiv n w.1)

/-- At every length, the cylinders indexed by the forbidden-word language have
full mass for an invariant measure whose `v` cylinder has zero mass. -/
theorem forbiddenLanguage_cylinders_full_mass
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell : ℕ} (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0)
    (n : ℕ) :
    (ν : Measure UnitAddCircle) (forbiddenLanguageCylinderUnion v n) = 1 := by
  classical
  let BadWord := {w : DecimalWord n //
    ∃ r : Fin (n + 1), OccursAt v w r.val}
  letI : Fintype (DecimalWord n) := inferInstance
  letI : Finite BadWord :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype BadWord := Fintype.ofFinite _
  have hcompl : (ν : Measure UnitAddCircle)
      (forbiddenLanguageCylinderUnion v n)ᶜ = 0 := by
    apply measure_mono_null (t := ⋃ w : BadWord,
      decimalCylinder n (decimalWordIndexEquiv n w.1))
    · intro x hx
      let w : DecimalWord n :=
        (decimalWordIndexEquiv n).symm (decimalCode n x)
      have hxw : x ∈ decimalCylinder n (decimalWordIndexEquiv n w) := by
        change decimalCode n x = decimalWordIndexEquiv n w
        simp [w]
      by_cases hav : ∀ r : Fin (n + 1), ¬ OccursAt v w r.val
      · exact False.elim (hx (Set.mem_iUnion.2 ⟨⟨w, hav⟩, hxw⟩))
      · have hbad : ∃ r : Fin (n + 1), OccursAt v w r.val := by
          simpa using hav
        exact Set.mem_iUnion.2 ⟨⟨w, hbad⟩, hxw⟩
    · apply measure_iUnion_null
      intro w
      obtain ⟨r, hr⟩ := w.2
      exact arbitraryShift_zero_mass_transfer ν hinvariant v hzero w.1 r.val hr
  calc
    (ν : Measure UnitAddCircle) (forbiddenLanguageCylinderUnion v n) =
        (ν : Measure UnitAddCircle) Set.univ :=
      measure_of_measure_compl_eq_zero hcompl
    _ = 1 := measure_univ

/-- Positive length-`2*m*ell` cylinders can use only the `q_v` allowed
length-`2*ell` chunks, giving the refined `q_v^m` count. -/
theorem positive_mass_forbidden_cylinder_count
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell : ℕ} (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0)
    (m : ℕ) :
    Nat.card (PositiveAlignedAtom ν (2 * ell) m) ≤ forbiddenQ v ^ m := by
  let encode : PositiveAlignedAtom ν (2 * ell) m →
      (Fin m → ForbiddenLanguage v (2 * ell)) := fun c j =>
    ⟨(decimalWordIndexEquiv (2 * ell)).symm (c.1 j), by
      intro r hocc
      have hz : (ν : Measure UnitAddCircle)
          (decimalCylinder (2 * ell) (c.1 j)) = 0 := by
        simpa using arbitraryShift_zero_mass_transfer ν hinvariant v hzero
          ((decimalWordIndexEquiv (2 * ell)).symm (c.1 j)) r.val hocc
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
    exact (decimalWordIndexEquiv (2 * ell)).symm.injective hj
  have hcard := Nat.card_le_card_of_injective encode hinjective
  rw [Nat.card_fun, Nat.card_fin] at hcard
  simpa only [forbiddenQ] using hcard

/-- First length-`ell` half of a length-`2*ell` word. -/
def leftHalf {ell : ℕ} (w : DecimalWord (2 * ell)) : DecimalWord ell :=
  fun i => w ⟨i.val, by omega⟩

/-- Second length-`ell` half of a length-`2*ell` word. -/
def rightHalf {ell : ℕ} (w : DecimalWord (2 * ell)) : DecimalWord ell :=
  fun i => w ⟨ell + i.val, by omega⟩

theorem halves_injective {ell : ℕ} :
    Function.Injective (fun w : DecimalWord (2 * ell) =>
      (leftHalf w, rightHalf w)) := by
  intro a b hab
  funext i
  by_cases hi : i.val < ell
  · have hleft := congrFun (congrArg Prod.fst hab) ⟨i.val, hi⟩
    exact hleft
  · have hj : i.val - ell < ell := by omega
    have hright := congrFun (congrArg Prod.snd hab) ⟨i.val - ell, hj⟩
    simpa [rightHalf, Nat.add_sub_of_le (Nat.le_of_not_gt hi)] using hright

/-- Length-`ell` blocks other than the forbidden block itself. -/
def NonForbiddenBlock {ell : ℕ} (v : DecimalWord ell) :=
  {w : DecimalWord ell // w ≠ v}

instance nonForbiddenBlock_finite {ell : ℕ} (v : DecimalWord ell) :
    Finite (NonForbiddenBlock v) := by
  letI : Fintype (DecimalWord ell) := inferInstance
  exact Finite.of_injective Subtype.val Subtype.val_injective

theorem nonForbiddenBlock_card {ell : ℕ} (v : DecimalWord ell) :
    Nat.card (NonForbiddenBlock v) = 10 ^ ell - 1 := by
  letI : Fintype (DecimalWord ell) := inferInstance
  letI : Fintype (NonForbiddenBlock v) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  simp [NonForbiddenBlock, Fintype.card_subtype_compl]

/-- Splitting an avoiding word into its two halves lands among pairs in which
neither half equals `v`. -/
def avoidingHalfPair {ell : ℕ} (v : DecimalWord ell) :
    ForbiddenLanguage v (2 * ell) →
      NonForbiddenBlock v × NonForbiddenBlock v := fun w =>
  ⟨⟨leftHalf w.1, by
      intro hleft
      have hocc : OccursAt v w.1 0 := by
        refine ⟨by omega, ?_⟩
        intro j
        simpa [leftHalf] using congrFun hleft j
      exact w.2 ⟨0, by omega⟩ hocc⟩,
    ⟨rightHalf w.1, by
      intro hright
      have hocc : OccursAt v w.1 ell := by
        refine ⟨by omega, ?_⟩
        intro j
        simpa [rightHalf] using congrFun hright j
      exact w.2 ⟨ell, by omega⟩ hocc⟩⟩

theorem avoidingHalfPair_injective {ell : ℕ} (v : DecimalWord ell) :
    Function.Injective (avoidingHalfPair v) := by
  intro a b hab
  apply Subtype.ext
  apply halves_injective
  exact congrArg (fun p => (p.1.1, p.2.1)) hab

/-- Basic two-half bound for the refined language constant. -/
theorem forbiddenQ_le_two_half_bound {ell : ℕ} (v : DecimalWord ell) :
    forbiddenQ v ≤ (10 ^ ell - 1) ^ 2 := by
  have hcard := Nat.card_le_card_of_injective (avoidingHalfPair v)
    (avoidingHalfPair_injective v)
  rw [Nat.card_prod, nonForbiddenBlock_card] at hcard
  simpa [forbiddenQ, pow_two] using hcard

/-- A decimal digit different from the supplied digit. -/
def otherDigit (d : Fin (10 ^ 1)) : Fin (10 ^ 1) :=
  if d.val = 0 then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

theorem otherDigit_ne (d : Fin (10 ^ 1)) : otherDigit d ≠ d := by
  by_cases hd : d.val = 0
  · intro h
    have := congrArg Fin.val h
    simp [otherDigit, hd] at this
  · intro h
    have := congrArg Fin.val h
    simp [otherDigit, hd] at this
    exact hd this.symm

/-- Left half of an explicit pair whose concatenation contains `v` across the
central boundary. -/
def crossBoundaryLeft {ell : ℕ} (v : DecimalWord ell) (hell : 2 ≤ ell) :
    DecimalWord ell := fun i =>
  if i.val = 0 then otherDigit (v ⟨0, by omega⟩)
  else if i.val = ell - 1 then v ⟨0, by omega⟩
  else v i

/-- Right half of the explicit cross-boundary witness. -/
def crossBoundaryRight {ell : ℕ} (v : DecimalWord ell) (hell : 2 ≤ ell) :
    DecimalWord ell := fun i =>
  if hi : i.val < ell - 1 then v ⟨i.val + 1, by omega⟩
  else otherDigit (v ⟨ell - 1, by omega⟩)

theorem crossBoundaryLeft_ne {ell : ℕ} (v : DecimalWord ell)
    (hell : 2 ≤ ell) : crossBoundaryLeft v hell ≠ v := by
  intro h
  have h0 := congrFun h (⟨0, by omega⟩ : Fin ell)
  exact otherDigit_ne (v ⟨0, by omega⟩) (by
    simpa [crossBoundaryLeft] using h0)

theorem crossBoundaryRight_ne {ell : ℕ} (v : DecimalWord ell)
    (hell : 2 ≤ ell) : crossBoundaryRight v hell ≠ v := by
  intro h
  have hlast := congrFun h (⟨ell - 1, by omega⟩ : Fin ell)
  exact otherDigit_ne (v ⟨ell - 1, by omega⟩) (by
    simpa [crossBoundaryRight] using hlast)

/-- The explicit pair of individually allowed halves excluded by the
overlapping language because `v` crosses their central boundary. -/
def crossBoundaryPair {ell : ℕ} (v : DecimalWord ell) (hell : 2 ≤ ell) :
    NonForbiddenBlock v × NonForbiddenBlock v :=
  (⟨crossBoundaryLeft v hell, crossBoundaryLeft_ne v hell⟩,
    ⟨crossBoundaryRight v hell, crossBoundaryRight_ne v hell⟩)

theorem crossBoundary_occurs_of_halves {ell : ℕ} (v : DecimalWord ell)
    (hell : 2 ≤ ell) (w : DecimalWord (2 * ell))
    (hleft : leftHalf w = crossBoundaryLeft v hell)
    (hright : rightHalf w = crossBoundaryRight v hell) :
    OccursAt v w (ell - 1) := by
  refine ⟨by omega, ?_⟩
  intro j
  by_cases hj : j.val = 0
  · have hjfin : j = (⟨0, by omega⟩ : Fin ell) := Fin.ext hj
    rw [hjfin]
    have h := congrFun hleft (⟨ell - 1, by omega⟩ : Fin ell)
    have hlastne : ell - 1 ≠ 0 := by omega
    simpa [leftHalf, crossBoundaryLeft, hlastne] using h
  · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
    have hindex : j.val - 1 < ell := by omega
    have h := congrFun hright (⟨j.val - 1, hindex⟩ : Fin ell)
    have hcond : j.val - 1 < ell - 1 := by omega
    have h' :
        w ⟨ell + (j.val - 1), by omega⟩ =
          v ⟨j.val - 1 + 1, by omega⟩ := by
      simpa [rightHalf, crossBoundaryRight, hcond] using h
    have hglobal :
        (⟨ell - 1 + j.val, by omega⟩ : Fin (2 * ell)) =
          ⟨ell + (j.val - 1), by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    have hjfin : j = (⟨j.val - 1 + 1, by omega⟩ : Fin ell) := by
      apply Fin.ext
      simp only
      omega
    calc
      w ⟨ell - 1 + j.val, by omega⟩ =
          w ⟨ell + (j.val - 1), by omega⟩ := congrArg w hglobal
      _ = v ⟨j.val - 1 + 1, by omega⟩ := h'
      _ = v j := congrArg v hjfin.symm

/-- Explicit strict cross-boundary inequality: for `ell ≥ 2`, at least one
pair of non-forbidden halves is absent from the avoiding language. -/
theorem forbiddenQ_strict_two_half_bound {ell : ℕ} (v : DecimalWord ell)
    (hell : 2 ≤ ell) :
    forbiddenQ v < (10 ^ ell - 1) ^ 2 := by
  letI : Fintype (DecimalWord ell) := inferInstance
  letI : Fintype (DecimalWord (2 * ell)) := inferInstance
  letI : Fintype (ForbiddenLanguage v (2 * ell)) := Fintype.ofFinite _
  letI : Fintype (NonForbiddenBlock v) := Fintype.ofFinite _
  have hnotSurj : ¬Function.Surjective (avoidingHalfPair v) := by
    intro hsurj
    obtain ⟨w, hw⟩ := hsurj (crossBoundaryPair v hell)
    have hocc : OccursAt v w.1 (ell - 1) :=
      crossBoundary_occurs_of_halves v hell w.1
        (congrArg (fun p => p.1.1) hw)
        (congrArg (fun p => p.2.1) hw)
    exact w.2 ⟨ell - 1, by omega⟩ hocc
  have hcard := Fintype.card_lt_of_injective_not_surjective
    (avoidingHalfPair v) (avoidingHalfPair_injective v) hnotSurj
  rw [Fintype.card_prod] at hcard
  have hallowed : Fintype.card (NonForbiddenBlock v) = 10 ^ ell - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact nonForbiddenBlock_card v
  rw [hallowed] at hcard
  simpa [forbiddenQ, Nat.card_eq_fintype_card, pow_two] using hcard

theorem avoidingHalfPair_surjective_length_one (v : DecimalWord 1) :
    Function.Surjective (avoidingHalfPair v) := by
  intro p
  let w : DecimalWord 2 := fun i =>
    if i.val = 0 then p.1.1 ⟨0, by omega⟩ else p.2.1 ⟨0, by omega⟩
  have hwAvoids : ∀ r : Fin (2 + 1), ¬ OccursAt v w r.val := by
    intro r hocc
    obtain ⟨hrange, hmatch⟩ := hocc
    have hm := hmatch (⟨0, by omega⟩ : Fin 1)
    by_cases hr : r.val = 0
    · apply p.1.2
      funext j
      have hj : j = (⟨0, by omega⟩ : Fin 1) := Fin.eq_zero j
      rw [hj]
      simpa [w, hr] using hm
    · have hr1 : r.val = 1 := by omega
      apply p.2.2
      funext j
      have hj : j = (⟨0, by omega⟩ : Fin 1) := Fin.eq_zero j
      rw [hj]
      simpa [w, hr1] using hm
  refine ⟨⟨w, hwAvoids⟩, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext j
    have hj : j = (⟨0, by omega⟩ : Fin 1) := Fin.eq_zero j
    rw [hj]
    simp [avoidingHalfPair, leftHalf, w]
  · apply Subtype.ext
    funext j
    have hj : j = (⟨0, by omega⟩ : Fin 1) := Fin.eq_zero j
    rw [hj]
    simp [avoidingHalfPair, rightHalf, w]

/-- Exact one-digit case: avoiding one digit for two places gives `9^2`. -/
theorem forbiddenQ_length_one (v : DecimalWord 1) : forbiddenQ v = 81 := by
  letI : Fintype (DecimalWord 1) := inferInstance
  letI : Fintype (DecimalWord 2) := inferInstance
  letI : Fintype (ForbiddenLanguage v 2) := Fintype.ofFinite _
  letI : Fintype (NonForbiddenBlock v) := Fintype.ofFinite _
  have hcard := Fintype.card_congr (Equiv.ofBijective (avoidingHalfPair v)
    ⟨avoidingHalfPair_injective v, avoidingHalfPair_surjective_length_one v⟩)
  rw [Fintype.card_prod] at hcard
  have hallowed : Fintype.card (NonForbiddenBlock v) = 9 := by
    rw [← Nat.card_eq_fintype_card, nonForbiddenBlock_card]
    norm_num
  rw [hallowed] at hcard
  simpa [forbiddenQ, Nat.card_eq_fintype_card] using hcard

theorem forbiddenQ_eq_81_of_length_eq_one {ell : ℕ} (v : DecimalWord ell)
    (hell : ell = 1) : forbiddenQ v = 81 := by
  subst ell
  exact forbiddenQ_length_one v

/-- A constant word using a digit different from the first digit of `v`
avoids every nonempty `v`. -/
def constantAvoidingWord {ell : ℕ} (v : DecimalWord ell) (hell : 0 < ell)
    (n : ℕ) : DecimalWord n :=
  fun _ => otherDigit (v ⟨0, hell⟩)

theorem constantAvoidingWord_mem {ell : ℕ} (v : DecimalWord ell)
    (hell : 0 < ell) (n : ℕ) :
    ∀ r : Fin (n + 1), ¬ OccursAt v (constantAvoidingWord v hell n) r.val := by
  intro r hocc
  obtain ⟨_hrange, hmatch⟩ := hocc
  have h0 := hmatch (⟨0, hell⟩ : Fin ell)
  exact otherDigit_ne (v ⟨0, hell⟩) (by
    simpa [constantAvoidingWord] using h0)

theorem forbiddenQ_pos {ell : ℕ} (v : DecimalWord ell) (hell : 0 < ell) :
    0 < forbiddenQ v := by
  haveI : Nonempty (ForbiddenLanguage v (2 * ell)) :=
    ⟨constantAvoidingWord v hell (2 * ell),
      constantAvoidingWord_mem v hell (2 * ell)⟩
  exact Nat.card_pos

/-- Generic version of T11's cover-to-dimension argument with an arbitrary
exponential bound `A^m` on the positive length-`m*k` cylinders. -/
theorem fullMassIntersection_dimH_le_of_atom_growth
    (ν : ProbabilityMeasure UnitAddCircle) {k A : ℕ}
    (hk : 0 < k) (hA : 0 < A)
    (hcount : ∀ m : ℕ, Nat.card (PositiveAlignedAtom ν k m) ≤ A ^ m) :
    dimH (fullMassHaarNullIntersection ν k) ≤
      ENNReal.ofReal (Real.log (A : ℝ) / ((k : ℝ) * Real.log 10)) := by
  classical
  let B : ℕ := 10 ^ k
  have hA1 : 1 ≤ A := hA
  have hB1 : 1 < B := by
    dsimp [B]
    have hten : 10 ≤ 10 ^ k := by
      simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
    omega
  have hdnonneg :
      0 ≤ Real.log (A : ℝ) / ((k : ℝ) * Real.log 10) := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hA1))
      (mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num)))
  let d : ℝ≥0 :=
    ⟨Real.log (A : ℝ) / ((k : ℝ) * Real.log 10), hdnonneg⟩
  have hd_real : (d : ℝ) = Real.log (A : ℝ) / Real.log (B : ℝ) := by
    change Real.log (A : ℝ) / ((k : ℝ) * Real.log 10) = _
    dsimp [B]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hscale (m : ℕ) :
      ENNReal.ofReal (decimalScale (m * k)) =
        (B : ENNReal)⁻¹ ^ m := by
    simp [decimalScale, B, ENNReal.ofReal_inv_of_pos, Nat.mul_comm]
    rw [← ENNReal.inv_pow, ← pow_mul]
  have hBpow : (B : ENNReal) ^ (d : ℝ) = (A : ENNReal) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
      (ENNReal.rpow_ne_top_of_nonneg d.coe_nonneg
        (ENNReal.natCast_ne_top B))
      (ENNReal.natCast_ne_top A)]
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, hd_real, Real.log_div_log]
    exact Real.rpow_logb
      (by exact_mod_cast zero_lt_one.trans hB1)
      (by exact_mod_cast hB1.ne')
      (by exact_mod_cast hA)
  have hunit :
      (A : ENNReal) * ((B : ENNReal)⁻¹ ^ (d : ℝ)) = 1 := by
    rw [ENNReal.inv_rpow, hBpow]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast hA.ne') (ENNReal.natCast_ne_top A)
  have hcomm (m : ℕ) :
      (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) =
        (((B : ENNReal)⁻¹ ^ (d : ℝ)) ^ m) := by
    calc
      (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) =
          (B : ENNReal)⁻¹ ^ ((m : ℝ) * (d : ℝ)) :=
        (ENNReal.rpow_natCast_mul _ m (d : ℝ)).symm
      _ = (B : ENNReal)⁻¹ ^ ((d : ℝ) * (m : ℝ)) := by rw [mul_comm]
      _ = (((B : ENNReal)⁻¹ ^ (d : ℝ)) ^ m) :=
        ENNReal.rpow_mul_natCast _ (d : ℝ) m
  have hcriticalPower (m : ℕ) :
      ((A ^ m : ℕ) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) = 1 := by
    rw [Nat.cast_pow, hcomm, ← mul_pow, hunit, one_pow]
  letI (m : ℕ) : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  let t : (m : ℕ) → PositiveAlignedAtom ν k m → Set UnitAddCircle :=
    fun m c => alignedDecimalCylinder k m c.1
  let r : ℕ → ENNReal := fun m => (B : ENNReal)⁻¹ ^ m
  have hr : Tendsto r atTop (nhds 0) := by
    apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    exact ENNReal.inv_lt_one.mpr (by exact_mod_cast hB1)
  have hdiam (m : ℕ) (c : PositiveAlignedAtom ν k m) :
      Metric.ediam (t m c) ≤ r m := by
    dsimp only [t, r]
    rw [alignedDecimalCylinder_eq_decimalCylinder]
    exact (decimalCylinder_ediam_le (m * k)
      (alignedIndexEquiv k m c.1)).trans_eq (hscale m)
  have hcover (m : ℕ) :
      fullMassHaarNullIntersection ν k ⊆ ⋃ c, t m c := by
    intro x hx
    have hxm : x ∈ positiveAlignedCylinderUnion ν k m :=
      Set.mem_iInter.mp hx m
    simpa only [t, positiveAlignedCylinderUnion] using hxm
  have hsum (m : ℕ) :
      ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ) ≤ (1 : ENNReal) := by
    calc
      ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ) ≤
          ∑ _c : PositiveAlignedAtom ν k m,
            ((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ) :=
        Finset.sum_le_sum fun c _ =>
          ENNReal.rpow_le_rpow (hdiam m c) d.coe_nonneg
      _ = (Nat.card (PositiveAlignedAtom ν k m) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) := by
        rw [Nat.card_eq_fintype_card, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((A ^ m : ℕ) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) := by
        gcongr
        exact_mod_cast hcount m
      _ = 1 := hcriticalPower m
  have hmeasure := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (d : ℝ) (fullMassHaarNullIntersection ν k) r hr t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  have hlim :
      liminf (fun m => ∑ c : PositiveAlignedAtom ν k m,
        Metric.ediam (t m c) ^ (d : ℝ)) atTop ≤ (1 : ENNReal) := by
    calc
      liminf (fun m => ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ)) atTop ≤
          liminf (fun _m : ℕ => (1 : ENNReal)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hsum)
      _ = 1 := Filter.liminf_const 1
  have hdim : dimH (fullMassHaarNullIntersection ν k) ≤ (d : ENNReal) := by
    apply dimH_le_of_hausdorffMeasure_ne_top
    exact ((hmeasure.trans hlim).trans_lt ENNReal.one_lt_top).ne
  calc
    dimH (fullMassHaarNullIntersection ν k) ≤ (d : ENNReal) := hdim
    _ = ENNReal.ofReal
        (Real.log (A : ℝ) / ((k : ℝ) * Real.log 10)) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl

/-- The refined critical dimension from the length-`2*ell` language. -/
def forbiddenCriticalDimension {ell : ℕ} (v : DecimalWord ell) : ℝ :=
  Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) * Real.log 10)

theorem forbidden_fullMassIntersection_dimH_le
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {ell : ℕ} (hell : 0 < ell) (v : DecimalWord ell)
    (hzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0) :
    dimH (fullMassHaarNullIntersection ν (2 * ell)) ≤
      ENNReal.ofReal (forbiddenCriticalDimension v) := by
  have h := fullMassIntersection_dimH_le_of_atom_growth ν
    (k := 2 * ell) (A := forbiddenQ v) (by omega) (forbiddenQ_pos v hell)
    (positive_mass_forbidden_cylinder_count ν hinvariant v hzero)
  simpa [forbiddenCriticalDimension] using h

/-- The refined dimension expression is exactly `log 9 / log 10` when the
forbidden word has length one. -/
theorem forbiddenCriticalDimension_length_one (v : DecimalWord 1) :
    forbiddenCriticalDimension v = Real.log 9 / Real.log 10 := by
  rw [forbiddenCriticalDimension, forbiddenQ_length_one]
  norm_num
  rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.log_pow]
  ring

theorem forbiddenCriticalDimension_eq_log9_of_length_eq_one
    {ell : ℕ} (v : DecimalWord ell) (hell : ell = 1) :
    forbiddenCriticalDimension v = Real.log 9 / Real.log 10 := by
  subst ell
  exact forbiddenCriticalDimension_length_one v

/-- For `ell ≥ 2`, the explicit cross-boundary witness makes the refined
dimension bound strictly smaller than T11's aligned-block bound. -/
theorem forbiddenCriticalDimension_lt_T11 {ell : ℕ} (v : DecimalWord ell)
    (hell : 2 ≤ ell) :
    forbiddenCriticalDimension v < criticalDimension ell := by
  have hqpos : 0 < forbiddenQ v := forbiddenQ_pos v (by omega)
  have hApos : 0 < 10 ^ ell - 1 := by
    have hten : 10 ≤ 10 ^ ell := by
      simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) (by omega : 0 < ell)
    omega
  have hstrict := forbiddenQ_strict_two_half_bound v hell
  have hlog : Real.log (forbiddenQ v : ℝ) <
      Real.log (((10 ^ ell - 1) ^ 2 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hqpos)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact_mod_cast hstrict
  have hden : 0 < (((2 * ell : ℕ) : ℝ) * Real.log 10) := by
    positivity
  unfold forbiddenCriticalDimension criticalDimension
  calc
    Real.log (forbiddenQ v : ℝ) /
          (((2 * ell : ℕ) : ℝ) * Real.log 10) <
        Real.log (((10 ^ ell - 1) ^ 2 : ℕ) : ℝ) /
          (((2 * ell : ℕ) : ℝ) * Real.log 10) :=
      div_lt_div_of_pos_right hlog hden
    _ = Real.log (10 ^ ell - 1 : ℕ) /
          ((ell : ℝ) * Real.log 10) := by
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      ring

/-- Necessary-only T12 conclusion. Literal failure of canonical C1 yields an
invariant pi empirical cluster carried by an overlapping forbidden-word
language with the refined dimension bound. No failure or truth of C1 is
asserted unconditionally. -/
theorem not_piPositiveLowerBlockDensity_implies_overlapping_dimension_bound
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ ell : ℕ, 1 ≤ ell ∧ ∃ v : DecimalWord ell,
        (ν : Measure UnitAddCircle)
            (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0 ∧
        (∀ n : ℕ,
          (ν : Measure UnitAddCircle) (forbiddenLanguageCylinderUnion v n) = 1) ∧
        (∀ (n : ℕ) (w : DecimalWord n) (r : ℕ), OccursAt v w r →
          (ν : Measure UnitAddCircle)
            (decimalCylinder n (decimalWordIndexEquiv n w)) = 0) ∧
        (∀ m : ℕ, Nat.card (PositiveAlignedAtom ν (2 * ell) m) ≤
          forbiddenQ v ^ m) ∧
        forbiddenQ v ≤ (10 ^ ell - 1) ^ 2 ∧
        ((ell = 1 ∧ forbiddenQ v = 81 ∧
            forbiddenCriticalDimension v = Real.log 9 / Real.log 10) ∨
          (2 ≤ ell ∧ forbiddenQ v < (10 ^ ell - 1) ^ 2 ∧
            forbiddenCriticalDimension v < criticalDimension ell)) ∧
        ∃ E : Set UnitAddCircle,
          MeasurableSet E ∧ (ν : Measure UnitAddCircle) E = 1 ∧
          dimH E ≤ ENNReal.ofReal (forbiddenCriticalDimension v) := by
  obtain ⟨ν, hcluster, hinvariant, sourceWord, hsourcePos, hsourceZero,
      _hcount, _hentropy, _hrate⟩ :=
    T8.not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit hnot
  let ell := sourceWord.length
  let v : DecimalWord ell :=
    (decimalWordIndexEquiv ell).symm (wordIndex sourceWord)
  have hvzero : (ν : Measure UnitAddCircle)
      (decimalCylinder ell (decimalWordIndexEquiv ell v)) = 0 := by
    simpa [v] using hsourceZero
  have hcases :
      (ell = 1 ∧ forbiddenQ v = 81 ∧
          forbiddenCriticalDimension v = Real.log 9 / Real.log 10) ∨
        (2 ≤ ell ∧ forbiddenQ v < (10 ^ ell - 1) ^ 2 ∧
          forbiddenCriticalDimension v < criticalDimension ell) := by
    by_cases hone : ell = 1
    · exact Or.inl ⟨hone, forbiddenQ_eq_81_of_length_eq_one v hone,
        forbiddenCriticalDimension_eq_log9_of_length_eq_one v hone⟩
    · have hell : 2 ≤ ell := by omega
      exact Or.inr ⟨hell, forbiddenQ_strict_two_half_bound v hell,
        forbiddenCriticalDimension_lt_T11 v hell⟩
  let E := fullMassHaarNullIntersection ν (2 * ell)
  refine ⟨ν, hcluster, hinvariant, ell, hsourcePos, v, hvzero, ?_, ?_, ?_,
    forbiddenQ_le_two_half_bound v, hcases, E, ?_, ?_, ?_⟩
  · intro n
    exact forbiddenLanguage_cylinders_full_mass ν hinvariant v hvzero n
  · intro n w r hocc
    exact arbitraryShift_zero_mass_transfer ν hinvariant v hvzero w r hocc
  · intro m
    exact positive_mass_forbidden_cylinder_count ν hinvariant v hvzero m
  · exact fullMassHaarNullIntersection_measurable ν (2 * ell)
  · exact fullMassHaarNullIntersection_full_measure ν (2 * ell)
  · exact forbidden_fullMassIntersection_dimH_le ν hinvariant hsourcePos v hvzero

end Theory.PiDigits.PositiveLowerBlockDensity.T12

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.arbitraryShift_zero_mass_transfer
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbiddenLanguage_cylinders_full_mass
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.positive_mass_forbidden_cylinder_count
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbiddenQ_strict_two_half_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbiddenQ_length_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbiddenCriticalDimension_length_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbidden_fullMassIntersection_dimH_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.forbiddenCriticalDimension_lt_T11
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T12.not_piPositiveLowerBlockDensity_implies_overlapping_dimension_bound
