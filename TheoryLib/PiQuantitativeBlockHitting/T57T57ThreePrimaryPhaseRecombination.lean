import TheoryLib.PiQuantitativeBlockHitting.T56T56ThreePrimaryResidualLift

/-!
# T57: exact recombination and decimal transport of the fine phase

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

After a numerator is split as `b = F*c+r`, split the coarse quotient once
more as `c = C+d*t`.  If the selected residue `C` differs from a leading
residue `L` by

`F*(C-L)+r = d*R`,

then the scaled rational phase recombines exactly as

`b/(F*d) = t + L/d + R/F`.

The second part records the corresponding base-ten carry algebra at a fixed
selector depth.  It is an identity, not a cancellation, distribution, or
decimal-cylinder theorem, and proves no every-word statement for pi.
-/

namespace Theory.PiDigits.ThreePrimaryPhaseRecombination

open Theory.PiDigits.ThreePrimaryResidualLift

/-- Exact rational reconstruction of the selected-grid phase from its
leading residue and complementary residual. -/
theorem residual_phase_recombination
    (F d b c C L r R t : ℤ)
    (hF : F ≠ 0) (hd : d ≠ 0)
    (hb : b = F * c + r)
    (hc : c = C + d * t)
    (hR : residualNumerator F C L r = d * R) :
    (b : ℚ) / ((F : ℚ) * (d : ℚ)) =
      (t : ℚ) + (L : ℚ) / (d : ℚ) + (R : ℚ) / (F : ℚ) := by
  have hnum : b = F * d * t + F * L + d * R := by
    calc
      b = F * c + r := hb
      _ = F * (C + d * t) + r := by rw [hc]
      _ = F * d * t + F * L + residualNumerator F C L r := by
        simp only [residualNumerator]
        ring
      _ = F * d * t + F * L + d * R := by rw [hR]
  have hFq : (F : ℚ) ≠ 0 := by exact_mod_cast hF
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [hnum]
  push_cast
  field_simp [hFq, hdq]

/-- At fixed selector depth, simultaneous decimal carries change the
residual numerator by the exact quotient shown on the right. -/
lemma residualNumerator_decimal_lift
    (F C L r f d a v R : ℤ)
    (hR : residualNumerator F C L r = d * R) :
    residualNumerator F
        (10 * C + f - d * a)
        (10 * L - d * v)
        (10 * r - F * f) =
      d * (10 * R + F * (v - a)) := by
  calc
    residualNumerator F
        (10 * C + f - d * a)
        (10 * L - d * v)
        (10 * r - F * f) =
      10 * residualNumerator F C L r + d * F * (v - a) := by
        simp only [residualNumerator]
        ring
    _ = d * (10 * R + F * (v - a)) := by rw [hR]; ring

/-- If the new residual numerator is also written as `d*R'`, cancellation of
the nonzero selector modulus gives the exact same-depth decimal recurrence. -/
theorem residual_decimal_recurrence
    (F C L r f d a v R R' : ℤ)
    (hd : d ≠ 0)
    (hR : residualNumerator F C L r = d * R)
    (hR' : residualNumerator F
        (10 * C + f - d * a)
        (10 * L - d * v)
        (10 * r - F * f) = d * R') :
    R' = 10 * R + F * (v - a) := by
  have hlift := residualNumerator_decimal_lift F C L r f d a v R hR
  rw [hR'] at hlift
  exact mul_left_cancel₀ hd hlift

/-- The fixed-depth decimal recurrence reduces modulo `F` to multiplication
by ten.  This is an exact phase transport statement, not a saving estimate. -/
theorem residual_eq_ten_mul_zmod
    (F : ℕ) (R R' z : ℤ)
    (hrec : R' = 10 * R + (F : ℤ) * z) :
    (R' : ZMod F) = (10 : ZMod F) * (R : ZMod F) := by
  have hcast := congrArg (fun n : ℤ ↦ (n : ZMod F)) hrec
  push_cast at hcast
  simpa using hcast

end Theory.PiDigits.ThreePrimaryPhaseRecombination

#print axioms Theory.PiDigits.ThreePrimaryPhaseRecombination.residual_phase_recombination
#print axioms Theory.PiDigits.ThreePrimaryPhaseRecombination.residualNumerator_decimal_lift
#print axioms Theory.PiDigits.ThreePrimaryPhaseRecombination.residual_decimal_recurrence
#print axioms Theory.PiDigits.ThreePrimaryPhaseRecombination.residual_eq_ten_mul_zmod
