import TheoryLib.PiQuantitativeBlockHitting.T172T172PositiveLeftExtensionTransport

/-!
# T176: signed block Bellman transport

The T172 left-extension identity is stable under subtraction of two prefix
horizons.  Consequently it transports the signed score of every consecutive
orbit block, not only the score of an initial prefix.  The coarse potential
`7 / (3q)` absorbs the verified T172 defect with strict room.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.SignedBlockBellmanTransport

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PositiveLeftExtensionTransport
open Theory.PiDigits.LongLagBlockCollisionDecay.T16

abbrev phase := Theory.PiDigits.T27.phase

/-- The primitive signed score contributed by the consecutive orbit block
with start `M` and length `L`. -/
def primitiveBoundaryFourierBlockSum (q A M L : ℕ) : ℂ :=
  primitiveBoundaryFourierSum q A (M + L) -
    primitiveBoundaryFourierSum q A M

/-- The corresponding consecutive-block part of the T172 transport
remainder. -/
def leftExtensionBlockRemainder (q A M L : ℕ) : ℂ :=
  leftExtensionRemainder q A (M + L) - leftExtensionRemainder q A M

/-- Subtracting the T172 identities at horizons `M + L` and `M` gives the
exact ten-child identity for an arbitrary consecutive block. -/
theorem primitiveBoundaryFourierBlockSum_leftExtension
    (q A M L : ℕ) :
    (∑ d ∈ range 10,
      primitiveBoundaryFourierBlockSum (10 * q) (A + d * q) M L) =
        primitiveBoundaryFourierBlockSum q A M L +
          leftExtensionBlockRemainder q A M L := by
  unfold primitiveBoundaryFourierBlockSum leftExtensionBlockRemainder
  rw [sum_sub_distrib]
  rw [primitiveBoundaryFourierSum_leftExtension,
    primitiveBoundaryFourierSum_leftExtension]
  ring

private theorem exponentialSum_block_eq
    (M L : ℕ) (h : ℤ) :
    exponentialSum piOrbit (M + L) h - exponentialSum piOrbit M h =
      ∑ j ∈ range L, phase h (piOrbit (M + j)) := by
  unfold exponentialSum Theory.PiDigits.T27.exponentialSum
  rw [sum_range_add]
  ring

/-- A consecutive block of `L` unit phases has norm at most `L`. -/
private theorem norm_exponentialSum_block_le
    (M L : ℕ) (h : ℤ) :
    ‖exponentialSum piOrbit (M + L) h - exponentialSum piOrbit M h‖ ≤ L := by
  rw [exponentialSum_block_eq]
  exact Theory.PiDigits.PowerTenFrequencyShift.norm_sum_phase_range_le L M h

/-- Positivity of the coefficient defects converts the block remainder into
`L` times the exact defect mass.  Unlike a triangle bound on two prefixes,
this estimate depends only on the block length, not its start. -/
theorem norm_leftExtensionBlockRemainder_le
    (q A M L : ℕ)
    (hpos : ∀ h ∈ positiveBoundarySupport q,
      0 ≤ leftExtensionCoefficientDefect q h) :
    ‖leftExtensionBlockRemainder q A M L‖ ≤
      L * leftExtensionDefectMass q := by
  unfold leftExtensionBlockRemainder leftExtensionRemainder
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ h ∈ positiveBoundarySupport q,
        (leftExtensionCoefficientDefect q h : ℂ) *
          phase (-(h : ℤ)) (decimalCylinderCenter q A) *
          (exponentialSum piOrbit (M + L) (tenPrimitivePart h : ℤ) -
            exponentialSum piOrbit M (tenPrimitivePart h : ℤ))‖ ≤
        ∑ h ∈ positiveBoundarySupport q,
          ‖(leftExtensionCoefficientDefect q h : ℂ) *
            phase (-(h : ℤ)) (decimalCylinderCenter q A) *
            (exponentialSum piOrbit (M + L) (tenPrimitivePart h : ℤ) -
              exponentialSum piOrbit M (tenPrimitivePart h : ℤ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ positiveBoundarySupport q,
          leftExtensionCoefficientDefect q h * L := by
      apply sum_le_sum
      intro h hh
      rw [norm_mul, norm_mul, Complex.norm_real,
        Theory.PiDigits.T27.norm_phase]
      simp only [mul_one, Real.norm_eq_abs, abs_of_nonneg (hpos h hh)]
      exact mul_le_mul_of_nonneg_left
        (norm_exponentialSum_block_le M L (tenPrimitivePart h : ℤ))
        (hpos h hh)
    _ = L * leftExtensionDefectMass q := by
      unfold leftExtensionDefectMass
      rw [← sum_mul]
      ring

/-- Fully unconditional coarse block-remainder estimate on decimal scales. -/
theorem norm_leftExtensionBlockRemainder_lt
    (q A M L : ℕ) (hq : 1000 ≤ q) (hL : 0 < L) :
    ‖leftExtensionBlockRemainder q A M L‖ <
      L * (21 / (10 * (q : ℝ) ^ 2)) := by
  refine lt_of_le_of_lt
    (norm_leftExtensionBlockRemainder_le q A M L
      (fun h hh => (leftExtensionCoefficientDefect_pos q h hq hh).le)) ?_
  exact mul_lt_mul_of_pos_left (leftExtensionDefectMass_lt q hq)
    (by exact_mod_cast hL)

/-- One child retains at least one tenth of the parent block score after the
exact defect mass is deducted. -/
theorem exists_leftExtension_blockScore_ge
    (q A M L : ℕ)
    (hpos : ∀ h ∈ positiveBoundarySupport q,
      0 ≤ leftExtensionCoefficientDefect q h) :
    ∃ d < 10,
      ((primitiveBoundaryFourierBlockSum q A M L).re -
          L * leftExtensionDefectMass q) / 10 ≤
        (primitiveBoundaryFourierBlockSum
          (10 * q) (A + d * q) M L).re := by
  have hrem := norm_leftExtensionBlockRemainder_le q A M L hpos
  have hremre : -(L * leftExtensionDefectMass q) ≤
      (leftExtensionBlockRemainder q A M L).re := by
    have habs := Complex.abs_re_le_norm (leftExtensionBlockRemainder q A M L)
    have hre : -(leftExtensionBlockRemainder q A M L).re ≤
        ‖leftExtensionBlockRemainder q A M L‖ :=
      (neg_le_abs _).trans habs
    linarith
  have hsum :
      (primitiveBoundaryFourierBlockSum q A M L).re -
          L * leftExtensionDefectMass q ≤
        ∑ d ∈ range 10,
          (primitiveBoundaryFourierBlockSum
            (10 * q) (A + d * q) M L).re := by
    rw [← Complex.re_sum, primitiveBoundaryFourierBlockSum_leftExtension]
    simp only [Complex.add_re]
    linarith
  by_contra hnone
  push Not at hnone
  have hall : ∀ d ∈ range 10,
      (primitiveBoundaryFourierBlockSum
          (10 * q) (A + d * q) M L).re <
        ((primitiveBoundaryFourierBlockSum q A M L).re -
          L * leftExtensionDefectMass q) / 10 := by
    intro d hd
    exact hnone d (mem_range.mp hd)
  have hstrict :
      ∑ d ∈ range 10,
          (primitiveBoundaryFourierBlockSum
            (10 * q) (A + d * q) M L).re <
        ∑ _d ∈ range 10,
          (((primitiveBoundaryFourierBlockSum q A M L).re -
            L * leftExtensionDefectMass q) / 10) :=
    sum_lt_sum_of_nonempty (by simp) (fun d hd => hall d hd)
  simp only [sum_const, card_range, nsmul_eq_mul] at hstrict
  norm_num at hstrict
  linarith

/-- Coarse potential used by the signed max-plus Bellman step. -/
def signedBlockPotential (q : ℕ) : ℝ := 7 / (3 * (q : ℝ))

/-- Strict max-plus Bellman transport.  Strictness comes from the strict T172
defect-mass estimate and therefore requires a nonempty block (`L > 0`). -/
theorem exists_leftExtension_block_bellman_gt
    (q A M L : ℕ) (hq : 1000 ≤ q) (hL : 0 < L) :
    ∃ d < 10,
      (10 * q : ℕ) *
            (primitiveBoundaryFourierBlockSum
              (10 * q) (A + d * q) M L).re -
          L * signedBlockPotential (10 * q) >
        q * (primitiveBoundaryFourierBlockSum q A M L).re -
          L * signedBlockPotential q := by
  obtain ⟨d, hd, hscore⟩ := exists_leftExtension_blockScore_ge q A M L
    (fun h hh => (leftExtensionCoefficientDefect_pos q h hq hh).le)
  refine ⟨d, hd, ?_⟩
  have hmass := leftExtensionDefectMass_lt q hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hscaled :
      (q : ℝ) * L * leftExtensionDefectMass q <
        L * (signedBlockPotential q - signedBlockPotential (10 * q)) := by
    calc
      (q : ℝ) * L * leftExtensionDefectMass q <
          (q : ℝ) * L * (21 / (10 * (q : ℝ) ^ 2)) := by
        exact mul_lt_mul_of_pos_left hmass (mul_pos hq0 hLR)
      _ = L * (signedBlockPotential q - signedBlockPotential (10 * q)) := by
        unfold signedBlockPotential
        push_cast
        field_simp
        ring
  have hscoreScaled :
      (q : ℝ) *
          ((primitiveBoundaryFourierBlockSum q A M L).re -
            L * leftExtensionDefectMass q) ≤
        ((10 * q : ℕ) : ℝ) *
          (primitiveBoundaryFourierBlockSum
            (10 * q) (A + d * q) M L).re := by
    have := mul_le_mul_of_nonneg_left hscore (show (0 : ℝ) ≤ 10 * q by positivity)
    norm_num at this ⊢
    nlinarith
  push_cast
  nlinarith

/-- Prefix specialization of the strict Bellman step. -/
theorem exists_leftExtension_prefix_bellman_gt
    (q A L : ℕ) (hq : 1000 ≤ q) (hL : 0 < L) :
    ∃ d < 10,
      (10 * q : ℕ) *
            (primitiveBoundaryFourierSum (10 * q) (A + d * q) L).re -
          L * signedBlockPotential (10 * q) >
        q * (primitiveBoundaryFourierSum q A L).re -
          L * signedBlockPotential q := by
  simpa [primitiveBoundaryFourierBlockSum, primitiveBoundaryFourierSum,
    exponentialSum, Theory.PiDigits.T27.exponentialSum] using
    exists_leftExtension_block_bellman_gt q A 0 L hq hL

end Theory.PiDigits.SignedBlockBellmanTransport

#print axioms Theory.PiDigits.SignedBlockBellmanTransport.primitiveBoundaryFourierBlockSum_leftExtension
#print axioms Theory.PiDigits.SignedBlockBellmanTransport.norm_leftExtensionBlockRemainder_lt
#print axioms Theory.PiDigits.SignedBlockBellmanTransport.exists_leftExtension_block_bellman_gt
#print axioms Theory.PiDigits.SignedBlockBellmanTransport.exists_leftExtension_prefix_bellman_gt
