import TheoryLib.PiQuantitativeBlockHitting.T172T172PositiveLeftExtensionTransport

/-!
# T177: predecessor-digit DFT of the complete primitive boundary score

This module Fourier-resolves the ten literal left children of a decimal
cylinder.  The zero digit character is exactly the T172 parent-plus-remainder
transport.  DFT inversion retains each child, the complete primitive score,
and its exact target phase.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.PredecessorDigitDFT

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PositiveLeftExtensionTransport

abbrev phase := Theory.PiDigits.T27.phase

/-- The `r`-th character sector of the ten left children.  The positive sign
is chosen so that a fine frequency `h` survives precisely when `h ≡ r [MOD 10]`.
-/
def predecessorDigitSector (q A N r : ℕ) : ℂ :=
  ∑ d ∈ range 10,
    phase (r : ℤ) ((d : ℝ) / 10) *
      primitiveBoundaryFourierSum (10 * q) (A + d * q) N

/-- The zero digit sector is exactly the T172 left-extension transport. -/
theorem predecessorDigitSector_zero (q A N : ℕ) :
    predecessorDigitSector q A N 0 =
      primitiveBoundaryFourierSum q A N + leftExtensionRemainder q A N := by
  simp only [predecessorDigitSector, Nat.cast_zero,
    Theory.PiDigits.T27.phase_zero, one_mul]
  exact primitiveBoundaryFourierSum_leftExtension q A N

private lemma digit_character_orthogonality
    (d e : ℕ) (hd : d < 10) (he : e < 10) :
    (∑ r ∈ range 10,
      phase (-(r : ℤ)) ((d : ℝ) / 10) *
        phase (r : ℤ) ((e : ℝ) / 10)) =
      if d = e then 10 else 0 := by
  classical
  by_cases hde : d = e
  · subst e
    simp only [if_pos]
    have hone (r : ℕ) :
        phase (-(r : ℤ)) ((d : ℝ) / 10) *
            phase (r : ℤ) ((d : ℝ) / 10) = 1 := by
      unfold phase Theory.PiDigits.T27.phase
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 1
      push_cast
      ring
    simp_rw [hone]
    norm_num
  · simp only [if_neg hde]
    by_cases hle : d < e
    · let k := e - d
      have hk0 : 0 < k := by omega
      have hk10 : k < 10 := by omega
      have hterm (r : ℕ) :
          phase (-(r : ℤ)) ((d : ℝ) / 10) *
              phase (r : ℤ) ((e : ℝ) / 10) =
            phase (k : ℤ) ((r : ℝ) / 10) := by
        unfold phase Theory.PiDigits.T27.phase
        rw [← Complex.exp_add]
        apply congrArg Complex.exp
        dsimp [k]
        push_cast
        rw [Nat.cast_sub (Nat.le_of_lt hle)]
        ring
      simp_rw [hterm]
      simpa [Theory.PiDigits.T27.exponentialSum,
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid] using
        (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
          k 10 (by norm_num) hk0 hk10)
    · let k := d - e
      have hk0 : 0 < k := by omega
      have hk10 : k < 10 := by omega
      have hterm (r : ℕ) :
          phase (-(r : ℤ)) ((d : ℝ) / 10) *
              phase (r : ℤ) ((e : ℝ) / 10) =
            phase (-(k : ℤ)) ((r : ℝ) / 10) := by
        unfold phase Theory.PiDigits.T27.phase
        rw [← Complex.exp_add]
        apply congrArg Complex.exp
        dsimp [k]
        push_cast
        rw [Nat.cast_sub (by omega : e ≤ d)]
        ring
      simp_rw [hterm]
      have hpos :=
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
          k 10 (by norm_num) hk0 hk10
      have hneg := Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg
        (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 10) 10 (k : ℤ)
      rw [hpos, map_zero] at hneg
      simpa [Theory.PiDigits.T27.exponentialSum,
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid] using hneg

/-- Exact inverse DFT: every fine child is recovered from all ten character
sectors. -/
theorem primitiveBoundaryFourierSum_child_eq_sector_sum
    (q A N d : ℕ) (hd : d < 10) :
    primitiveBoundaryFourierSum (10 * q) (A + d * q) N =
      (1 / 10 : ℂ) *
        ∑ r ∈ range 10,
          phase (-(r : ℤ)) ((d : ℝ) / 10) *
            predecessorDigitSector q A N r := by
  classical
  unfold predecessorDigitSector
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcollapse (e : ℕ) (he : e ∈ range 10) :
      (∑ r ∈ range 10,
        phase (-(r : ℤ)) ((d : ℝ) / 10) *
          (phase (r : ℤ) ((e : ℝ) / 10) *
            primitiveBoundaryFourierSum (10 * q) (A + e * q) N)) =
        (if d = e then (10 : ℂ) else 0) *
          primitiveBoundaryFourierSum (10 * q) (A + e * q) N := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    rw [digit_character_orthogonality d e hd (Finset.mem_range.mp he)]
  simp_rw [← Finset.mul_sum]
  rw [show (∑ e ∈ range 10,
      ∑ r ∈ range 10,
        phase (-(r : ℤ)) ((d : ℝ) / 10) *
          (phase (r : ℤ) ((e : ℝ) / 10) *
            primitiveBoundaryFourierSum (10 * q) (A + e * q) N)) =
      ∑ e ∈ range 10,
        (if d = e then (10 : ℂ) else 0) *
          primitiveBoundaryFourierSum (10 * q) (A + e * q) N by
    apply Finset.sum_congr rfl
    intro e he
    exact hcollapse e he]
  simp only [ite_mul, zero_mul]
  simp [mem_range.mpr hd]

/-- The real contribution of the nine nonzero predecessor characters to a
specified child. -/
def predecessorNonzeroContribution (q A N d : ℕ) : ℝ :=
  (∑ r ∈ (Icc 1 9 : Finset ℕ),
    phase (-(r : ℤ)) ((d : ℝ) / 10) *
      predecessorDigitSector q A N r).re

/-- Child reconstruction split into the transported zero sector and the nine
genuinely digit-sensitive sectors. -/
theorem ten_mul_child_re_eq_zeroSector_add_nonzero
    (q A N d : ℕ) (hd : d < 10) :
    10 * (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re =
      (predecessorDigitSector q A N 0).re +
        predecessorNonzeroContribution q A N d := by
  have hinv := primitiveBoundaryFourierSum_child_eq_sector_sum q A N d hd
  apply_fun Complex.re at hinv
  have hrange : range 10 = insert 0 (Icc 1 9) := by
    ext r
    simp
    omega
  rw [hrange, sum_insert (by simp)] at hinv
  simp only [Nat.cast_zero, neg_zero,
    Theory.PiDigits.T27.phase_zero, one_mul] at hinv
  unfold predecessorNonzeroContribution
  rw [Complex.re_sum]
  simp only [Complex.mul_re, Complex.add_re] at hinv ⊢
  rw [Finset.sum_sub_distrib]
  norm_num at hinv
  linarith

/-- The nonzero character corrections have exact mean zero across the ten
children. -/
theorem sum_predecessorNonzeroContribution_eq_zero (q A N : ℕ) :
    (∑ d ∈ range 10, predecessorNonzeroContribution q A N d) = 0 := by
  have hpoint (d : ℕ) (hd : d ∈ range 10) :
      predecessorNonzeroContribution q A N d =
        10 * (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re -
          (predecessorDigitSector q A N 0).re := by
    linarith [ten_mul_child_re_eq_zeroSector_add_nonzero q A N d
      (Finset.mem_range.mp hd)]
  calc
    (∑ d ∈ range 10, predecessorNonzeroContribution q A N d) =
        ∑ d ∈ range 10,
          (10 * (primitiveBoundaryFourierSum (10 * q) (A + d * q) N).re -
            (predecessorDigitSector q A N 0).re) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hpoint d hd
    _ = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hzero : predecessorDigitSector q A N 0 =
          ∑ d ∈ range 10,
            primitiveBoundaryFourierSum (10 * q) (A + d * q) N := by
        simp only [predecessorDigitSector, Nat.cast_zero,
          Theory.PiDigits.T27.phase_zero, one_mul]
      rw [hzero, Complex.re_sum]
      ring

/-- At least one predecessor digit has nonnegative nonzero-character drift.
This is the exact DFT form of the Bellman selector. -/
theorem exists_predecessorNonzeroContribution_nonneg (q A N : ℕ) :
    ∃ d ∈ range 10, 0 ≤ predecessorNonzeroContribution q A N d := by
  by_contra h
  push Not at h
  have hsumlt :
      (∑ d ∈ range 10, predecessorNonzeroContribution q A N d) <
        ∑ _d ∈ range 10, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro d hd
      exact (h d hd).le
    · exact ⟨0, by simp, h 0 (by simp)⟩
  simp only [sum_const_zero] at hsumlt
  rw [sum_predecessorNonzeroContribution_eq_zero] at hsumlt
  exact lt_irrefl 0 hsumlt

#print axioms Theory.PiDigits.PredecessorDigitDFT.predecessorDigitSector_zero
#print axioms Theory.PiDigits.PredecessorDigitDFT.primitiveBoundaryFourierSum_child_eq_sector_sum
#print axioms Theory.PiDigits.PredecessorDigitDFT.ten_mul_child_re_eq_zeroSector_add_nonzero
#print axioms Theory.PiDigits.PredecessorDigitDFT.sum_predecessorNonzeroContribution_eq_zero
#print axioms Theory.PiDigits.PredecessorDigitDFT.exists_predecessorNonzeroContribution_nonneg

end Theory.PiDigits.PredecessorDigitDFT
