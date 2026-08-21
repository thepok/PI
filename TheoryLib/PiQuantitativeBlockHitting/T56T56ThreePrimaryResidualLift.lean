import TheoryLib.PiQuantitativeBlockHitting.T55T55ThreePrimaryCoarseSelector

/-!
# T56: exact residual lift through one ternary selector level

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The three-primary selector has a complementary integral residual

`F * (C - L) + r = d * R`.

When the selected residue `C` and the leading residue `L` are lifted by one
ternary digit and the modulus changes from `d` to `3*d`, this module proves
the exact recurrence

`3 * R' = R + F * (u - v)`.

Modulo `F`, the residual therefore changes by multiplication with the inverse
of three.  This is a permutation of the fine residue classes, not a
contraction or an averaging statement.  The results below prove no decimal
cylinder hit, normality, or every-word statement for pi.
-/

namespace Theory.PiDigits.ThreePrimaryResidualLift

/-- The integral numerator left after separating the leading residue `L`
from the selected residue `C`. -/
def residualNumerator (F C L r : ℤ) : ℤ := F * (C - L) + r

/-- Lifting `C` and `L` by digits `u` and `v` changes the residual numerator
by the exact signed multiple `d * F * (u-v)`. -/
lemma residualNumerator_lift
    (F C L r u v d : ℤ) :
    residualNumerator F (C + d * u) (L + d * v) r =
      residualNumerator F C L r + d * F * (u - v) := by
  simp only [residualNumerator]
  ring

/-- If the old residual numerator is `d*R` and the lifted one is
`(3*d)*R'`, cancellation of the nonzero old modulus gives the exact ternary
residual recurrence. -/
theorem residual_ternary_recurrence
    (F C L r u v d R R' : ℤ)
    (hd : d ≠ 0)
    (hR : residualNumerator F C L r = d * R)
    (hR' : residualNumerator F (C + d * u) (L + d * v) r =
      (3 * d) * R') :
    3 * R' = R + F * (u - v) := by
  have hlift := residualNumerator_lift F C L r u v d
  rw [hR, hR'] at hlift
  have hfactor : d * (3 * R') = d * (R + F * (u - v)) := by
    calc
      d * (3 * R') = (3 * d) * R' := by ring
      _ = d * R + d * F * (u - v) := hlift
      _ = d * (R + F * (u - v)) := by ring
  exact mul_left_cancel₀ hd hfactor

/-- The exact integer recurrence reduces modulo `F` to multiplication by
`3⁻¹`.  Hence depth compatibility permutes the fine phases instead of
shrinking their magnitude. -/
theorem residual_eq_inv_three_mul_zmod
    (F : ℕ) (R R' z : ℤ)
    (hrec : 3 * R' = R + (F : ℤ) * z)
    (h3 : IsUnit (3 : ZMod F)) :
    (R' : ZMod F) = (3 : ZMod F)⁻¹ * (R : ZMod F) := by
  have hcast := congrArg (fun n : ℤ ↦ (n : ZMod F)) hrec
  push_cast at hcast
  have hthree : (3 : ZMod F) * (R' : ZMod F) = (R : ZMod F) := by
    simpa using hcast
  have hcancel : (3 : ZMod F)⁻¹ * (3 : ZMod F) = 1 := by
    simpa [mul_comm] using ZMod.mul_inv_of_unit (3 : ZMod F) h3
  calc
    (R' : ZMod F) = 1 * (R' : ZMod F) := by simp
    _ = ((3 : ZMod F)⁻¹ * (3 : ZMod F)) * (R' : ZMod F) := by rw [hcancel]
    _ = (3 : ZMod F)⁻¹ * ((3 : ZMod F) * (R' : ZMod F)) := by ring
    _ = (3 : ZMod F)⁻¹ * (R : ZMod F) := by rw [hthree]

end Theory.PiDigits.ThreePrimaryResidualLift

#print axioms Theory.PiDigits.ThreePrimaryResidualLift.residualNumerator_lift
#print axioms Theory.PiDigits.ThreePrimaryResidualLift.residual_ternary_recurrence
#print axioms Theory.PiDigits.ThreePrimaryResidualLift.residual_eq_inv_three_mul_zmod
