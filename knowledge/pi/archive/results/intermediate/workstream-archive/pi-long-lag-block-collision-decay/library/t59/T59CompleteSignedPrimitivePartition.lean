import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T49T49PrimitiveIncidenceAssembly
import TheoryLib.PiLongLagBlockCollisionDecay.T56T56SignedPrimitiveResiduePairing

/-!
# T59: complete signed primitive partition

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module formalizes the finite partition proposed by the unverified T58
note, without importing that note or taking any T58 claim as a premise.  It is
only about the residual sparse-Fourier sibling A12.  It proves no `EBox`
bound, defect bound, width-weighted square-function estimate, C2, C1, or
canonical collision estimate.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T59

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T34
open Theory.PiDigits.LongLagBlockCollisionDecay.T49
open Theory.PiDigits.LongLagBlockCollisionDecay.T56

abbrev RecordOrientation := Bool × Bool

/-- The two literal record Booleans of a positive primitive pair. -/
def recordOrientation (p : PrimitiveRecordPair) : RecordOrientation :=
  (p.1.1, p.2.1)

/-- Realized primitive values inside one exact T49 valuation stratum. -/
def primitiveValueParameters
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) (ell : ℕ) : Finset ℕ :=
  (primitiveValuationStratum μ c Q0 m N B ell).image blockDifferenceValue

/-- The exact valuation-value-orientation fiber of T49's primitive domain. -/
def primitiveOrientationFiber
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock)
    (ell d : ℕ) (omega : RecordOrientation) : Finset PrimitiveRecordPair :=
  (primitiveRecordDomain μ c Q0 m N B).filter fun p =>
    tenValuation (blockDifferenceValue p) = ell ∧
      blockDifferenceValue p = d ∧ recordOrientation p = omega

theorem mem_primitiveOrientationFiber_iff
    {μ c : ℝ} {Q0 m N ell d : ℕ} {B : DyadicBlock}
    {omega : RecordOrientation} {p : PrimitiveRecordPair} :
    p ∈ primitiveOrientationFiber μ c Q0 m N B ell d omega ↔
      p ∈ primitiveRecordDomain μ c Q0 m N B ∧
      tenValuation (blockDifferenceValue p) = ell ∧
      blockDifferenceValue p = d ∧ recordOrientation p = omega := by
  simp [primitiveOrientationFiber]

/-- Nested finite union of all realized valuation, value, and orientation
fibers.  The equality is an exhaustive disjoint-by-index partition: membership
in a fiber fixes all three displayed indices. -/
theorem primitiveRecordDomain_eq_fiber_biUnion
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock) :
    primitiveRecordDomain μ c Q0 m N B =
      (primitiveValuationParameters μ c Q0 m N B).biUnion fun ell =>
        (primitiveValueParameters μ c Q0 m N B ell).biUnion fun d =>
          (Finset.univ : Finset RecordOrientation).biUnion fun omega =>
            primitiveOrientationFiber μ c Q0 m N B ell d omega := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hp
    let ell := tenValuation (blockDifferenceValue p)
    let d := blockDifferenceValue p
    let omega := recordOrientation p
    refine ⟨ell, ?_, d, ?_, omega, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hp, rfl, rfl, rfl⟩
  · rintro ⟨ell, hell, d, hd, omega, hp⟩
    exact (Finset.mem_filter.mp hp).1

theorem primitiveOrientationFiber_disjoint
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock)
    {ell d ell' d' : ℕ} {omega omega' : RecordOrientation}
    (hne : ell ≠ ell' ∨ d ≠ d' ∨ omega ≠ omega') :
    Disjoint
      (primitiveOrientationFiber μ c Q0 m N B ell d omega)
      (primitiveOrientationFiber μ c Q0 m N B ell' d' omega') := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  have h := (mem_primitiveOrientationFiber_iff.mp hp)
  have h' := (mem_primitiveOrientationFiber_iff.mp hp')
  rcases hne with hne | hne | hne
  · exact hne (h.2.1.symm.trans h'.2.1)
  · exact hne (h.2.2.1.symm.trans h'.2.2.1)
  · exact hne (h.2.2.2.symm.trans h'.2.2.2)

/-- Exact finite regrouping over the full T49 primitive domain. -/
theorem sum_primitiveRecordDomain_eq_fibers
    (μ c : ℝ) (Q0 m N : ℕ) (B : DyadicBlock)
    (f : PrimitiveRecordPair → ℝ) :
    (∑ p ∈ primitiveRecordDomain μ c Q0 m N B, f p) =
      ∑ ell ∈ primitiveValuationParameters μ c Q0 m N B,
        ∑ d ∈ primitiveValueParameters μ c Q0 m N B ell,
          ∑ omega : RecordOrientation,
            ∑ p ∈ primitiveOrientationFiber μ c Q0 m N B ell d omega,
              f p := by
  classical
  symm
  calc
    (∑ ell ∈ primitiveValuationParameters μ c Q0 m N B,
        ∑ d ∈ primitiveValueParameters μ c Q0 m N B ell,
          ∑ omega : RecordOrientation,
            ∑ p ∈ primitiveOrientationFiber μ c Q0 m N B ell d omega,
              f p) =
        ∑ ell ∈ primitiveValuationParameters μ c Q0 m N B,
          ∑ d ∈ primitiveValueParameters μ c Q0 m N B ell,
            ∑ p ∈ (primitiveValuationStratum μ c Q0 m N B ell).filter
              (fun p => blockDifferenceValue p = d), f p := by
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro d hd
      have h := Finset.sum_fiberwise_of_maps_to
        (s := (primitiveValuationStratum μ c Q0 m N B ell).filter
          (fun p => blockDifferenceValue p = d))
        (t := (Finset.univ : Finset RecordOrientation))
        (g := recordOrientation) (fun p hp => Finset.mem_univ _) f
      have heq (omega : RecordOrientation) :
          ((primitiveValuationStratum μ c Q0 m N B ell).filter
            (fun p => blockDifferenceValue p = d)).filter
              (fun p => recordOrientation p = omega) =
            primitiveOrientationFiber μ c Q0 m N B ell d omega := by
        ext p
        simp [primitiveOrientationFiber, primitiveValuationStratum, and_assoc]
      simpa only [heq] using h
    _ = ∑ ell ∈ primitiveValuationParameters μ c Q0 m N B,
          ∑ p ∈ primitiveValuationStratum μ c Q0 m N B ell, f p := by
      apply Finset.sum_congr rfl
      intro ell hell
      exact Finset.sum_fiberwise_of_maps_to
        (s := primitiveValuationStratum μ c Q0 m N B ell)
        (t := primitiveValueParameters μ c Q0 m N B ell)
        (g := blockDifferenceValue)
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) f
    _ = ∑ p ∈ primitiveRecordDomain μ c Q0 m N B, f p := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := primitiveRecordDomain μ c Q0 m N B)
        (t := primitiveValuationParameters μ c Q0 m N B)
        (g := fun p => tenValuation (blockDifferenceValue p))
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) f

/-- Swapping the two records is the positive/negative phase-orientation
involution used by T31. -/
def swapOrientation (p : PrimitiveRecordPair) : PrimitiveRecordPair := p.swap

theorem swapOrientation_involutive : Function.Involutive swapOrientation := by
  intro p
  rcases p with ⟨q, r⟩
  rfl

/-- The sign attached to T31's Boolean orientation. -/
def phaseOrientationSign (b : Bool) : ℤ := if b then -1 else 1

/-- The complete two-element signed orbit of one positive representative. -/
def primitiveSignedOrbit (p : PrimitiveRecordPair) : Finset PrimitiveRecordPair :=
  (Finset.univ : Finset Bool).image fun b => orientPositiveDifference (b, p)

/-- Every orientation carries the literal signed frequency `+d` or `-d`. -/
theorem orientPositiveDifference_sign
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain μ c Q0 m N B) (b : Bool) :
    signedDecimalFrequency (orientPositiveDifference (b, p)).1 -
        signedDecimalFrequency (orientPositiveDifference (b, p)).2 =
      phaseOrientationSign b * (blockDifferenceValue p : ℤ) := by
  have hp' : p ∈ primitiveBlockDifferenceDomain μ c Q0 m N B := hp
  have hvalue := blockPositiveDifferenceValue_cast
    (primitiveBlockDifferenceDomain_subset hp')
  cases b <;> simp [orientPositiveDifference, phaseOrientationSign] <;> omega

theorem primitiveSignedOrbit_card
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p : PrimitiveRecordPair}
    (hp : p ∈ primitiveRecordDomain μ c Q0 m N B) :
    (primitiveSignedOrbit p).card = 2 := by
  classical
  have hp' : p ∈ primitiveBlockDifferenceDomain μ c Q0 m N B := hp
  have hpPos := primitiveBlockDifferenceDomain_subset hp'
  unfold primitiveSignedOrbit
  rw [Finset.card_image_iff.mpr]
  · decide
  · intro b hb b' hb' heq
    exact congrArg Prod.fst (orientPositiveDifference_injOn_block μ c Q0 m N B
      (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, hpPos⟩)
      (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, hpPos⟩)
      (by simpa using heq))

/-- Reversal of one ordered record exchanges its endpoints. -/
def reverseOrderedRecord (q : OrderedLongPair) : OrderedLongPair := (!q.1, q.2)

theorem reverseOrderedRecord_involutive : Function.Involutive reverseOrderedRecord := by
  intro q
  rcases q with ⟨b, r, n⟩
  cases b <;> rfl

theorem reverseOrderedRecord_coordinateRecord (x y : ℕ) (hxy : x ≠ y) :
    reverseOrderedRecord (coordinateRecord x y) = coordinateRecord y x := by
  by_cases hyx : y < x
  · have hxy : ¬x < y := by omega
    simp [reverseOrderedRecord, coordinateRecord, hyx, hxy]
  · have hxy' : x < y := by omega
    simp [reverseOrderedRecord, coordinateRecord, hyx, hxy']

/-- Reverse both ordered records and swap their positive/negative roles. -/
def simultaneousReversal (p : PrimitiveRecordPair) : PrimitiveRecordPair :=
  (reverseOrderedRecord p.2, reverseOrderedRecord p.1)

theorem simultaneousReversal_involutive : Function.Involutive simultaneousReversal := by
  intro p
  rcases p with ⟨q, r⟩
  change (reverseOrderedRecord (reverseOrderedRecord q),
    reverseOrderedRecord (reverseOrderedRecord r)) = (q, r)
  rw [reverseOrderedRecord_involutive q, reverseOrderedRecord_involutive r]

theorem simultaneousReversal_selected_rows
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    simultaneousReversal (residueOnePair x .row00) = residueOnePair x .row11 ∧
    simultaneousReversal (residueOnePair x .row01) = residueOnePair x .row10 ∧
    simultaneousReversal (residueNinePair x .row00) = residueNinePair x .row11 ∧
    simultaneousReversal (residueNinePair x .row01) = residueNinePair x .row10 := by
  have h := boxQuartet_ordered hx
  repeat' apply And.intro
  all_goals
    simp only [simultaneousReversal, residueOnePair, residueNinePair]
    apply Prod.ext <;>
      apply reverseOrderedRecord_coordinateRecord <;> omega

/-- The two selected T56 primitive record images. -/
def selectedRecordDomain (t : ℕ) : Finset PrimitiveRecordPair :=
  residueOneRecordDomain t ∪ residueNineRecordDomain t

/-- The two selected T56 primitive-value images. -/
def selectedValueDomain (t : ℕ) : Finset ℕ :=
  (boxQuartetDomain t).image residueOneValue ∪
    (boxQuartetDomain t).image residueNineValue

/-- Both selected T56 fibers are displayed as full ambient T49 value fibers,
not merely as four chosen records. -/
theorem selectedAmbientFourFibers_exact
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    residueOneAmbientFiber Q0 t x = residueOneFiber x ∧
    (residueOneAmbientFiber Q0 t x).card = 4 ∧
    residueNineAmbientFiber Q0 t x = residueNineFiber x ∧
    (residueNineAmbientFiber Q0 t x).card = 4 := by
  exact ⟨(residueOne_ambientFourFiber_classification Q0 hx).1,
    (residueOne_ambientFourFiber_classification Q0 hx).2,
    (residueNine_ambientFourFiber_classification Q0 hx).1,
    (residueNine_ambientFourFiber_classification Q0 hx).2⟩

theorem residueRecordDomains_disjoint (t : ℕ) :
    Disjoint (residueOneRecordDomain t) (residueNineRecordDomain t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp1 hp9
  obtain ⟨x, hx, row, hp⟩ := residueOneRecordDomain_mem_iff.mp hp1
  obtain ⟨y, hy, row', hp'⟩ := residueNineRecordDomain_mem_iff.mp hp9
  subst p
  have h1 := (residue_record_valuation_fiber_audit 0 hx row).2.1
  have h9 := (residue_record_valuation_fiber_audit 0 hy row').2.2.2
  rw [hp'] at h1
  omega

theorem selectedRecordDomain_subset_primitive (Q0 t : ℕ) :
    selectedRecordDomain t ⊆
      primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) := by
  intro p hp
  rw [selectedRecordDomain, Finset.mem_union] at hp
  exact hp.elim
    (fun h => residueOneRecordDomain_subset_primitive Q0 t h)
    (fun h => residueNineRecordDomain_subset_primitive Q0 t h)

/-- Exact equivalence between the selected record images and selected values
inside the full ambient T49 primitive domain. -/
theorem mem_selectedRecordDomain_iff
    (Q0 t : ℕ) {p : PrimitiveRecordPair} :
    p ∈ selectedRecordDomain t ↔
      p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
        blockDifferenceValue p ∈ selectedValueDomain t := by
  classical
  constructor
  · intro hp
    refine ⟨selectedRecordDomain_subset_primitive Q0 t hp, ?_⟩
    rw [selectedRecordDomain, Finset.mem_union] at hp
    rw [selectedValueDomain, Finset.mem_union]
    rcases hp with hp | hp
    · obtain ⟨x, hx, row, rfl⟩ := residueOneRecordDomain_mem_iff.mp hp
      exact Or.inl (Finset.mem_image.mpr
        ⟨x, hx, (residueOne_blockDifferenceValue Q0 hx row).symm⟩)
    · obtain ⟨x, hx, row, rfl⟩ := residueNineRecordDomain_mem_iff.mp hp
      exact Or.inr (Finset.mem_image.mpr
        ⟨x, hx, (residueNine_blockDifferenceValue Q0 hx row).symm⟩)
  · rintro ⟨hp, hv⟩
    rw [selectedValueDomain, Finset.mem_union] at hv
    rw [selectedRecordDomain, Finset.mem_union]
    rcases hv with hv | hv
    · obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hv
      obtain ⟨row, hrow⟩ :=
        (residueOne_ambientPrimitiveValueFiber_iff Q0 hx).mp
          ⟨hp, heq.symm⟩
      exact Or.inl (residueOneRecordDomain_mem_iff.mpr
        ⟨x, hx, row, hrow⟩)
    · obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hv
      obtain ⟨row, hrow⟩ :=
        (residueNine_ambientPrimitiveValueFiber_iff Q0 hx).mp
          ⟨hp, heq.symm⟩
      exact Or.inr (residueNineRecordDomain_mem_iff.mpr
        ⟨x, hx, row, hrow⟩)

/-- The complementary unmatched defect, as a literal finite difference. -/
def unmatchedDefect (Q0 t : ℕ) : Finset PrimitiveRecordPair :=
  primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) \
    selectedRecordDomain t

/-- Exact unmatched-value membership; no unspecified remainder is hidden. -/
theorem mem_unmatchedDefect_iff
    (Q0 t : ℕ) {p : PrimitiveRecordPair} :
    p ∈ unmatchedDefect Q0 t ↔
      p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
        ∀ x ∈ boxQuartetDomain t,
          blockDifferenceValue p ≠ residueOneValue x ∧
          blockDifferenceValue p ≠ residueNineValue x := by
  classical
  rw [unmatchedDefect, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    intro x hx
    constructor
    · intro heq
      apply hnot
      apply (mem_selectedRecordDomain_iff Q0 t).mpr
      refine ⟨hp, ?_⟩
      rw [selectedValueDomain, Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩)
    · intro heq
      apply hnot
      apply (mem_selectedRecordDomain_iff Q0 t).mpr
      refine ⟨hp, ?_⟩
      rw [selectedValueDomain, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨x, hx, heq.symm⟩)
  · rintro ⟨hp, hall⟩
    refine ⟨hp, ?_⟩
    intro hsel
    have hv := (mem_selectedRecordDomain_iff Q0 t).mp hsel |>.2
    rw [selectedValueDomain, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hv
      exact (hall x hx).1 heq.symm
    · obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hv
      exact (hall x hx).2 heq.symm

def defectValuationParameters (Q0 t : ℕ) : Finset ℕ :=
  (unmatchedDefect Q0 t).image fun p => tenValuation (blockDifferenceValue p)

def defectValueParameters (Q0 t ell : ℕ) : Finset ℕ :=
  ((unmatchedDefect Q0 t).filter fun p =>
    tenValuation (blockDifferenceValue p) = ell).image blockDifferenceValue

def defectOrientationFiber
    (Q0 t ell d : ℕ) (omega : RecordOrientation) : Finset PrimitiveRecordPair :=
  (unmatchedDefect Q0 t).filter fun p =>
    tenValuation (blockDifferenceValue p) = ell ∧
      blockDifferenceValue p = d ∧ recordOrientation p = omega

theorem mem_defectOrientationFiber_iff
    {Q0 t ell d : ℕ} {omega : RecordOrientation} {p : PrimitiveRecordPair} :
    p ∈ defectOrientationFiber Q0 t ell d omega ↔
      p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
      (∀ x ∈ boxQuartetDomain t,
        blockDifferenceValue p ≠ residueOneValue x ∧
        blockDifferenceValue p ≠ residueNineValue x) ∧
      tenValuation (blockDifferenceValue p) = ell ∧
      blockDifferenceValue p = d ∧ recordOrientation p = omega := by
  rw [defectOrientationFiber, Finset.mem_filter, mem_unmatchedDefect_iff]
  tauto

theorem unmatchedDefect_eq_fiber_biUnion (Q0 t : ℕ) :
    unmatchedDefect Q0 t =
      (defectValuationParameters Q0 t).biUnion fun ell =>
        (defectValueParameters Q0 t ell).biUnion fun d =>
          (Finset.univ : Finset RecordOrientation).biUnion fun omega =>
            defectOrientationFiber Q0 t ell d omega := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hp
    let ell := tenValuation (blockDifferenceValue p)
    let d := blockDifferenceValue p
    let omega := recordOrientation p
    refine ⟨ell, ?_, d, ?_, omega, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hp, rfl, rfl, rfl⟩
  · rintro ⟨ell, hell, d, hd, omega, hp⟩
    exact (Finset.mem_filter.mp hp).1

theorem sum_unmatchedDefect_eq_fibers
    (Q0 t : ℕ) (f : PrimitiveRecordPair → ℝ) :
    (∑ p ∈ unmatchedDefect Q0 t, f p) =
      ∑ ell ∈ defectValuationParameters Q0 t,
        ∑ d ∈ defectValueParameters Q0 t ell,
          ∑ omega : RecordOrientation,
            ∑ p ∈ defectOrientationFiber Q0 t ell d omega, f p := by
  classical
  symm
  calc
    (∑ ell ∈ defectValuationParameters Q0 t,
        ∑ d ∈ defectValueParameters Q0 t ell,
          ∑ omega : RecordOrientation,
            ∑ p ∈ defectOrientationFiber Q0 t ell d omega, f p) =
        ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ d ∈ defectValueParameters Q0 t ell,
            ∑ p ∈ (unmatchedDefect Q0 t).filter
              (fun p => tenValuation (blockDifferenceValue p) = ell ∧
                blockDifferenceValue p = d), f p := by
      apply Finset.sum_congr rfl
      intro ell hell
      apply Finset.sum_congr rfl
      intro d hd
      have h := Finset.sum_fiberwise_of_maps_to
        (s := (unmatchedDefect Q0 t).filter fun p =>
          tenValuation (blockDifferenceValue p) = ell ∧
            blockDifferenceValue p = d)
        (t := (Finset.univ : Finset RecordOrientation))
        (g := recordOrientation) (fun p hp => Finset.mem_univ _) f
      have heq (omega : RecordOrientation) :
          ((unmatchedDefect Q0 t).filter fun p =>
            tenValuation (blockDifferenceValue p) = ell ∧
              blockDifferenceValue p = d).filter
                (fun p => recordOrientation p = omega) =
            defectOrientationFiber Q0 t ell d omega := by
        ext p
        simp [defectOrientationFiber, and_assoc]
      simpa only [heq] using h
    _ = ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ p ∈ (unmatchedDefect Q0 t).filter
            (fun p => tenValuation (blockDifferenceValue p) = ell), f p := by
      apply Finset.sum_congr rfl
      intro ell hell
      have h := Finset.sum_fiberwise_of_maps_to
        (s := (unmatchedDefect Q0 t).filter fun p =>
          tenValuation (blockDifferenceValue p) = ell)
        (t := defectValueParameters Q0 t ell)
        (g := blockDifferenceValue)
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) f
      have heq (d : ℕ) :
          ((unmatchedDefect Q0 t).filter fun p =>
            tenValuation (blockDifferenceValue p) = ell).filter
              (fun p => blockDifferenceValue p = d) =
            (unmatchedDefect Q0 t).filter fun p =>
              tenValuation (blockDifferenceValue p) = ell ∧
                blockDifferenceValue p = d := by
        ext p
        simp only [Finset.mem_filter]
        tauto
      simpa only [defectValueParameters, heq] using h
    _ = ∑ p ∈ unmatchedDefect Q0 t, f p := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := unmatchedDefect Q0 t)
        (t := defectValuationParameters Q0 t)
        (g := fun p => tenValuation (blockDifferenceValue p))
        (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) f

/-- The selected residue-one, selected residue-nine, and unmatched pieces are
pairwise disjoint and exhaust the exact T49 primitive domain. -/
theorem selected_defect_exhaustive_partition (Q0 t : ℕ) :
    Disjoint (residueOneRecordDomain t) (residueNineRecordDomain t) ∧
    Disjoint (selectedRecordDomain t) (unmatchedDefect Q0 t) ∧
    primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) =
      selectedRecordDomain t ∪ unmatchedDefect Q0 t := by
  classical
  refine ⟨residueRecordDomains_disjoint t, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hsel hdef
    exact (Finset.mem_sdiff.mp hdef).2 hsel
  · ext p
    constructor
    · intro hp
      by_cases hsel : p ∈ selectedRecordDomain t
      · exact Finset.mem_union_left _ hsel
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hp, hsel⟩)
    · intro hp
      rw [Finset.mem_union] at hp
      exact hp.elim
        (fun h => selectedRecordDomain_subset_primitive Q0 t h)
        (fun h => (Finset.mem_sdiff.mp h).1)

/-- The exact signed primitive domain before conjugate orientations are
collapsed to a real kernel. -/
def signedPrimitiveDomain (Q0 t : ℕ) : Finset PrimitiveRecordPair :=
  ((Finset.univ : Finset Bool) ×ˢ
    primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t)).image
      orientPositiveDifference

def signedSelectedDomain (t : ℕ) : Finset PrimitiveRecordPair :=
  ((Finset.univ : Finset Bool) ×ˢ selectedRecordDomain t).image
    orientPositiveDifference

def signedDefectDomain (Q0 t : ℕ) : Finset PrimitiveRecordPair :=
  ((Finset.univ : Finset Bool) ×ˢ unmatchedDefect Q0 t).image
    orientPositiveDifference

theorem signed_selected_defect_partition (Q0 t : ℕ) :
    Disjoint (signedSelectedDomain t) (signedDefectDomain Q0 t) ∧
      signedPrimitiveDomain Q0 t =
        signedSelectedDomain t ∪ signedDefectDomain Q0 t := by
  classical
  have hpart := selected_defect_exhaustive_partition Q0 t
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hsel hdef
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hsel
    obtain ⟨b, hb, hbq⟩ := Finset.mem_image.mp hdef
    have haProd := Finset.mem_product.mp ha
    have hbProd := Finset.mem_product.mp hb
    have haPrim := selectedRecordDomain_subset_primitive Q0 t haProd.2
    have hbPrim := (Finset.mem_sdiff.mp hbProd.2).1
    have haPrim' : a.2 ∈ primitiveBlockDifferenceDomain
        8 1 Q0 1 (boxEndpoint t) (boxBlock t) := haPrim
    have hbPrim' : b.2 ∈ primitiveBlockDifferenceDomain
        8 1 Q0 1 (boxEndpoint t) (boxBlock t) := hbPrim
    have hab := orientPositiveDifference_injOn_block
      8 1 Q0 1 (boxEndpoint t) (boxBlock t)
      (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, primitiveBlockDifferenceDomain_subset haPrim'⟩)
      (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, primitiveBlockDifferenceDomain_subset hbPrim'⟩)
      (haq.trans hbq.symm)
    have hp : a.2 = b.2 := congrArg Prod.snd hab
    exact Finset.disjoint_left.mp hpart.2.1 haProd.2 (hp ▸ hbProd.2)
  · ext q
    constructor
    · intro hq
      obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
      have haProd := Finset.mem_product.mp ha
      rw [hpart.2.2, Finset.mem_union] at haProd
      rw [Finset.mem_union]
      rcases haProd.2 with hsel | hdef
      · left
        exact Finset.mem_image.mpr
          ⟨a, Finset.mem_product.mpr ⟨haProd.1, hsel⟩, haq⟩
      · right
        exact Finset.mem_image.mpr
          ⟨a, Finset.mem_product.mpr ⟨haProd.1, hdef⟩, haq⟩
    · intro hq
      rw [Finset.mem_union] at hq
      rcases hq with hq | hq
      · obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
        have haProd := Finset.mem_product.mp ha
        exact Finset.mem_image.mpr ⟨a, Finset.mem_product.mpr
          ⟨haProd.1, selectedRecordDomain_subset_primitive Q0 t haProd.2⟩, haq⟩
      · obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
        have haProd := Finset.mem_product.mp ha
        exact Finset.mem_image.mpr ⟨a, Finset.mem_product.mpr
          ⟨haProd.1, (Finset.mem_sdiff.mp haProd.2).1⟩, haq⟩

/-- Exact signed defect regrouping.  The literal inclusive frequency endpoints
`1` and `10`, valuation, value, orientation, and block width all occur in the
theorem type. -/
theorem defect_signed_regrouping (Q0 t : ℕ) :
    2 * (∑ p ∈ unmatchedDefect Q0 t,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
          (blockDifferenceValue p : ℝ))) /
        widthWeight (boxBlock t)) =
      (2 / widthWeight (boxBlock t)) *
        ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ d ∈ defectValueParameters Q0 t ell,
            ∑ omega : RecordOrientation,
              ((defectOrientationFiber Q0 t ell d omega).card : ℝ) *
                ∑ h ∈ Finset.Icc (1 : ℕ) 10,
                  Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) := by
  classical
  let K : ℕ → ℝ := fun d =>
    ∑ h ∈ Finset.Icc (1 : ℕ) 10,
      Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ))
  have hsum := sum_unmatchedDefect_eq_fibers Q0 t
    (fun p => K (blockDifferenceValue p))
  have hgroup :
      (∑ ell ∈ defectValuationParameters Q0 t,
        ∑ d ∈ defectValueParameters Q0 t ell,
          ∑ omega : RecordOrientation,
            ∑ p ∈ defectOrientationFiber Q0 t ell d omega,
              K (blockDifferenceValue p)) =
        ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ d ∈ defectValueParameters Q0 t ell,
            ∑ omega : RecordOrientation,
              ((defectOrientationFiber Q0 t ell d omega).card : ℝ) * K d := by
    apply Finset.sum_congr rfl
    intro ell hell
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro omega homega
    calc
      (∑ p ∈ defectOrientationFiber Q0 t ell d omega,
          K (blockDifferenceValue p)) =
          ∑ p ∈ defectOrientationFiber Q0 t ell d omega, K d := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(mem_defectOrientationFiber_iff.mp hp).2.2.2.1]
      _ = ((defectOrientationFiber Q0 t ell d omega).card : ℝ) * K d := by
        rw [Finset.sum_const, nsmul_eq_mul]
  change 2 * (∑ p ∈ unmatchedDefect Q0 t,
      K (blockDifferenceValue p) / widthWeight (boxBlock t)) = _
  calc
    2 * (∑ p ∈ unmatchedDefect Q0 t,
        K (blockDifferenceValue p) / widthWeight (boxBlock t)) =
        (2 / widthWeight (boxBlock t)) *
          ∑ p ∈ unmatchedDefect Q0 t, K (blockDifferenceValue p) := by
      rw [← Finset.sum_div]
      ring
    _ = (2 / widthWeight (boxBlock t)) *
        ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ d ∈ defectValueParameters Q0 t ell,
            ∑ omega : RecordOrientation,
              ∑ p ∈ defectOrientationFiber Q0 t ell d omega,
                K (blockDifferenceValue p) := by rw [hsum]
    _ = (2 / widthWeight (boxBlock t)) *
        ∑ ell ∈ defectValuationParameters Q0 t,
          ∑ d ∈ defectValueParameters Q0 t ell,
            ∑ omega : RecordOrientation,
              ((defectOrientationFiber Q0 t ell d omega).card : ℝ) * K d := by
      rw [hgroup]

/-- Final exact signed decomposition at every T56 dyadic one-block scale.
There are no absolute values and no bound on either displayed contribution. -/
theorem primitiveSectorContribution_eq_selected_EBox_add_defect
    (Q0 t : ℕ) :
    primitiveSectorContribution 8 1 Q0 1 (boxEndpoint t) Real.pi =
      16 * EBox t / widthWeight (boxBlock t) +
        (2 / widthWeight (boxBlock t)) *
          ∑ ell ∈ defectValuationParameters Q0 t,
            ∑ d ∈ defectValueParameters Q0 t ell,
              ∑ omega : RecordOrientation,
                ((defectOrientationFiber Q0 t ell d omega).card : ℝ) *
                  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
                    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) := by
  classical
  have hpart := selected_defect_exhaustive_partition Q0 t
  have hselected :
      2 * (∑ p ∈ selectedRecordDomain t,
        inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
          widthWeight (boxBlock t)) =
        16 * EBox t / widthWeight (boxBlock t) := by
    calc
      2 * (∑ p ∈ selectedRecordDomain t,
          inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
            widthWeight (boxBlock t)) =
          2 * ((∑ p ∈ residueOneRecordDomain t,
              inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
                widthWeight (boxBlock t)) +
            ∑ p ∈ residueNineRecordDomain t,
              inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
                widthWeight (boxBlock t)) := by
        rw [selectedRecordDomain,
          Finset.sum_union (residueRecordDomains_disjoint t)]
      _ = boxDeduplicatedSignedContribution Q0 t := by
        rfl
      _ = boxSignedContribution Q0 t :=
        (boxSignedContribution_eq_deduplicated Q0 t).symm
      _ = 16 / widthWeight (boxBlock t) * EBox t :=
        boxSignedContribution_eq_EBox Q0 t
      _ = 16 * EBox t / widthWeight (boxBlock t) := by ring
  have hdefect :
      2 * (∑ p ∈ unmatchedDefect Q0 t,
        inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
          widthWeight (boxBlock t)) =
        (2 / widthWeight (boxBlock t)) *
          ∑ ell ∈ defectValuationParameters Q0 t,
            ∑ d ∈ defectValueParameters Q0 t ell,
              ∑ omega : RecordOrientation,
                ((defectOrientationFiber Q0 t ell d omega).card : ℝ) *
                  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
                    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) := by
    simpa only [inclusiveRealKernel_one_eq_cosineSum] using
      defect_signed_regrouping Q0 t
  unfold primitiveSectorContribution
  rw [translatedCanonicalBlocks_boxEndpoint]
  simp only [List.map_singleton, List.sum_singleton]
  rw [hpart.2.2, Finset.sum_union hpart.2.1]
  calc
    2 * ((∑ p ∈ selectedRecordDomain t,
          inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
            widthWeight (boxBlock t)) +
        ∑ p ∈ unmatchedDefect Q0 t,
          inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
            widthWeight (boxBlock t)) =
        2 * (∑ p ∈ selectedRecordDomain t,
          inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
            widthWeight (boxBlock t)) +
        2 * (∑ p ∈ unmatchedDefect Q0 t,
          inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
            widthWeight (boxBlock t)) := by ring
    _ = _ := by rw [hselected, hdefect]

end Theory.PiDigits.LongLagBlockCollisionDecay.T59

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.mem_primitiveOrientationFiber_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.primitiveRecordDomain_eq_fiber_biUnion
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.primitiveOrientationFiber_disjoint
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.sum_primitiveRecordDomain_eq_fibers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.swapOrientation_involutive
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.orientPositiveDifference_sign
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.simultaneousReversal_involutive
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.simultaneousReversal_selected_rows
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.selectedAmbientFourFibers_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.mem_selectedRecordDomain_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.mem_unmatchedDefect_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.mem_defectOrientationFiber_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.unmatchedDefect_eq_fiber_biUnion
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.selected_defect_exhaustive_partition
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.signed_selected_defect_partition
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.defect_signed_regrouping
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T59.primitiveSectorContribution_eq_selected_EBox_add_defect
