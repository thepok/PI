import TheoryLib.PiQuantitativeBlockHitting.T155T155DelayedBBPPhaseTransfer

/-!
# T160: delayed BBP transfer across an exact decimal resonance

Two pi phases at decimal indices `n+r` and `n`, with frequencies `h` and
`-10^r h`, have product exactly one.  Applying the pointwise T155 transfer to
both factors shows that the corresponding delayed BBP phases remain close to
one whenever both frequencies lie in their individual transfer windows.

This closes only the defect accounting for a preselected resonant pair.  It
provides no cancellation, no abundance of useful pairs, and no V1 conclusion.
-/

noncomputable section

namespace Theory.PiDigits.T160DelayedBBPDecimalResonance

open Theory.PiDigits.T155DelayedBBPPhaseTransfer

/-- Exact decimal resonance of the two genuine pi phases. -/
theorem pi_decimal_resonant_phase_product
    (h : ℤ) (n r : ℕ) :
    Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + r) * Real.pi) *
        Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
          ((10 : ℝ) ^ n * Real.pi) = 1 := by
  have hshift :
      Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
          ((10 : ℝ) ^ n * Real.pi) =
        Theory.PiDigits.T27.phase (-h)
          ((10 : ℝ) ^ (n + r) * Real.pi) := by
    unfold Theory.PiDigits.T27.phase
    congr 1
    push_cast
    rw [pow_add]
    ring
  rw [hshift, ← Theory.PiDigits.T27.phase_add, add_neg_cancel,
    Theory.PiDigits.T27.phase_zero]

/-- A two-factor T155 transfer bound compatible with the exact decimal
resonance.  Both frequencies must lie in the natural window belonging to the
delay used for that factor. -/
theorem norm_delayedBBP_resonant_product_sub_one_lt
    (h : ℤ) (k0 k1 n r : ℕ)
    (hlater : h.natAbs < 2 * 10 ^ k1)
    (hearlier : (-((10 : ℤ) ^ r * h)).natAbs < 2 * 10 ^ k0) :
    ‖Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) *
          Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
            (delayedBBPValue k0 n) - 1‖ <
      4 * Real.pi *
        (Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + r + k1) +
          Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + k0)) := by
  have hlaterError := norm_phase_pi_sub_delayedBBPValue_lt
    h k1 (n + r) hlater
  have hearlierError := norm_phase_pi_sub_delayedBBPValue_lt
    (-((10 : ℤ) ^ r * h)) k0 n hearlier
  have hresonance := pi_decimal_resonant_phase_product h n r
  calc
    ‖Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) *
          Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
            (delayedBBPValue k0 n) - 1‖ =
        ‖Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) *
            Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
              (delayedBBPValue k0 n) -
          Theory.PiDigits.T27.phase h
              ((10 : ℝ) ^ (n + r) * Real.pi) *
            Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
              ((10 : ℝ) ^ n * Real.pi)‖ := by rw [hresonance]
    _ = ‖(Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) -
              Theory.PiDigits.T27.phase h
                ((10 : ℝ) ^ (n + r) * Real.pi)) *
            Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
              (delayedBBPValue k0 n) +
          Theory.PiDigits.T27.phase h
              ((10 : ℝ) ^ (n + r) * Real.pi) *
            (Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                (delayedBBPValue k0 n) -
              Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                ((10 : ℝ) ^ n * Real.pi))‖ := by
      congr 1
      ring
    _ ≤ ‖Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) -
              Theory.PiDigits.T27.phase h
                ((10 : ℝ) ^ (n + r) * Real.pi)‖ +
          ‖Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                (delayedBBPValue k0 n) -
              Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                ((10 : ℝ) ^ n * Real.pi)‖ := by
      simpa [norm_mul, Theory.PiDigits.T27.norm_phase] using
        norm_add_le
          ((Theory.PiDigits.T27.phase h (delayedBBPValue k1 (n + r)) -
              Theory.PiDigits.T27.phase h
                ((10 : ℝ) ^ (n + r) * Real.pi)) *
            Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
              (delayedBBPValue k0 n))
          (Theory.PiDigits.T27.phase h
              ((10 : ℝ) ^ (n + r) * Real.pi) *
            (Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                (delayedBBPValue k0 n) -
              Theory.PiDigits.T27.phase (-((10 : ℤ) ^ r * h))
                ((10 : ℝ) ^ n * Real.pi)))
    _ < 4 * Real.pi *
          Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + r + k1) +
        4 * Real.pi *
          Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + k0) := by
      exact add_lt_add
        (by simpa only [norm_sub_rev] using hlaterError)
        (by simpa only [norm_sub_rev] using hearlierError)
    _ = 4 * Real.pi *
        (Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + r + k1) +
          Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + k0)) := by ring

/-- Under the two burn-in hypotheses, the resonant transfer is stated
directly for the actual delayed reduced-numerator phases. -/
theorem norm_delayedBBPNumerator_resonant_product_sub_one_lt
    (h : ℤ) (k0 k1 n r : ℕ)
    (hlater : h.natAbs < 2 * 10 ^ k1)
    (hearlier : (-((10 : ℤ) ^ r * h)).natAbs < 2 * 10 ^ k0)
    (hmLater : 2 ≤ (n + r) + k1)
    (hlogLater : Nat.log 5 (56 * ((n + r) + k1) + 5) ≤ n + r)
    (hmEarlier : 2 ≤ n + k0)
    (hlogEarlier : Nat.log 5 (56 * (n + k0) + 5) ≤ n) :
    ‖delayedBBPNumeratorPhase h k1 (n + r) *
          delayedBBPNumeratorPhase (-((10 : ℤ) ^ r * h)) k0 n - 1‖ <
      4 * Real.pi *
        (Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + r + k1) +
          Theory.PiDigits.T106BBPForcedOrbit.bbpErrorRatio ^ (n + k0)) := by
  rw [← phase_delayedBBPValue_eq_delayedBBPNumeratorPhase
      h k1 (n + r) hmLater hlogLater,
    ← phase_delayedBBPValue_eq_delayedBBPNumeratorPhase
      (-((10 : ℤ) ^ r * h)) k0 n hmEarlier hlogEarlier]
  exact norm_delayedBBP_resonant_product_sub_one_lt
    h k0 k1 n r hlater hearlier

end Theory.PiDigits.T160DelayedBBPDecimalResonance

#print axioms Theory.PiDigits.T160DelayedBBPDecimalResonance.pi_decimal_resonant_phase_product
#print axioms Theory.PiDigits.T160DelayedBBPDecimalResonance.norm_delayedBBP_resonant_product_sub_one_lt
#print axioms Theory.PiDigits.T160DelayedBBPDecimalResonance.norm_delayedBBPNumerator_resonant_product_sub_one_lt
