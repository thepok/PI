import TheoryLib.PiQuantitativeBlockHitting.T54T54ThreePrimaryNestedSchedule

/-!
# T55: exact coarse selector modulo a coprime factor

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For a reduced rational denominator split as `F * D`, write the numerator
residue as `F * c + r`, where `c` is the coarse quotient and `r` is the fine
remainder.  This module proves the exact selector identity in `ZMod D`:

`c = A * F⁻¹ - r * F⁻¹`.

The only arithmetic input is that `F` is a unit modulo `D`.  Thus the theorem
also records the obstruction exposed by the three-primary calculation: the
leading unit does not determine `c` unless the fine phase `r * F⁻¹` is
controlled.  These identities do not prove such control, a decimal cylinder
hit, normality, or the every-word conjecture for pi.
-/

namespace Theory.PiDigits.ThreePrimaryCoarseSelector

open Theory.PiDigits.MachinQuotientCarry

/-- Reduction modulo the full factored denominator does not change a natural
number after casting into `ZMod D`. -/
lemma fullRemainder_cast_zmod
    (A F D : ℕ) :
    (((A % (F * D) : ℕ) : ZMod D)) = (A : ZMod D) := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ D).2
  rw [Nat.mod_mod_of_dvd A]
  exact ⟨F, Nat.mul_comm F D⟩

/-- Before division by the unit `F`, the coarse selector is the exact
congruence `F*c = A-r` modulo `D`. -/
theorem coarse_selector_mul_eq
    (A F D : ℕ) :
    (F : ZMod D) * (coarseQuotient (A % (F * D)) F : ZMod D) =
      (A : ZMod D) - (fineRemainder (A % (F * D)) F : ZMod D) := by
  apply eq_sub_iff_add_eq.mpr
  have hsplit := coarse_mul_add_fine_eq (A % (F * D)) F
  have hsplitZ := congrArg (fun n : ℕ ↦ (n : ZMod D)) hsplit
  push_cast at hsplitZ
  exact hsplitZ.trans (fullRemainder_cast_zmod A F D)

/-- Exact coarse-selector identity.  The fine phase is indispensable: even
when `A * F⁻¹` is known, `c` is selected only after subtracting
`r * F⁻¹`. -/
theorem coarse_selector_zmod
    (A F D : ℕ) (hF : IsUnit (F : ZMod D)) :
    (coarseQuotient (A % (F * D)) F : ZMod D) =
      (A : ZMod D) * (F : ZMod D)⁻¹ -
        (fineRemainder (A % (F * D)) F : ZMod D) *
          (F : ZMod D)⁻¹ := by
  rw [← sub_mul]
  have hcancel : (F : ZMod D)⁻¹ * (F : ZMod D) = 1 := by
    simpa [mul_comm] using ZMod.mul_inv_of_unit (F : ZMod D) hF
  have hselector := coarse_selector_mul_eq A F D
  calc
    (coarseQuotient (A % (F * D)) F : ZMod D) =
        1 * (coarseQuotient (A % (F * D)) F : ZMod D) := by simp
    _ = ((F : ZMod D)⁻¹ * (F : ZMod D)) *
        (coarseQuotient (A % (F * D)) F : ZMod D) := by rw [hcancel]
    _ = (F : ZMod D)⁻¹ *
        ((F : ZMod D) *
          (coarseQuotient (A % (F * D)) F : ZMod D)) := by ring
    _ = (F : ZMod D)⁻¹ *
        ((A : ZMod D) -
          (fineRemainder (A % (F * D)) F : ZMod D)) := by rw [hselector]
    _ = ((A : ZMod D) -
          (fineRemainder (A % (F * D)) F : ZMod D)) *
        (F : ZMod D)⁻¹ := by ring

end Theory.PiDigits.ThreePrimaryCoarseSelector

#print axioms Theory.PiDigits.ThreePrimaryCoarseSelector.fullRemainder_cast_zmod
#print axioms Theory.PiDigits.ThreePrimaryCoarseSelector.coarse_selector_mul_eq
#print axioms Theory.PiDigits.ThreePrimaryCoarseSelector.coarse_selector_zmod
