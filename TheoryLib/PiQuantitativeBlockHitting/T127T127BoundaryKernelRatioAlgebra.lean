import Mathlib

/-!
# T127: algebra for normalized boundary-kernel coefficients

This module isolates the elementary ratio comparison behind the proposed
boundary-matched cosine--Fejer kernel. It does not define that kernel or make
any claim about the decimal orbit of pi.
-/

namespace Theory.PiDigits.BoundaryKernelRatioAlgebra

/-- Exact difference formula for two normalized coefficients in an affine
one-parameter family. -/
lemma normalizedAffineCoefficient_sub
    (B0 B1 M B beta1 beta2 : ℝ)
    (hden1 : B1 - beta1 * B0 ≠ 0)
    (hden2 : B1 - beta2 * B0 ≠ 0) :
    (M - beta2 * B) / (B1 - beta2 * B0) -
        (M - beta1 * B) / (B1 - beta1 * B0) =
      (beta2 - beta1) * (B0 * M - B1 * B) /
        ((B1 - beta2 * B0) * (B1 - beta1 * B0)) := by
  have hden1' : B1 - B0 * beta1 ≠ 0 := by
    simpa [mul_comm] using hden1
  have hden2' : B1 - B0 * beta2 ≠ 0 := by
    simpa [mul_comm] using hden2
  field_simp [hden1, hden2, hden1', hden2']
  ring

/-- If the two zero modes are positive and the cross determinant is positive,
then increasing the affine parameter strictly increases the corresponding
normalized nonzero coefficient. -/
theorem normalizedAffineCoefficient_strictMono
    (B0 B1 M B beta1 beta2 : ℝ)
    (hbeta : beta1 < beta2)
    (hden1 : 0 < B1 - beta1 * B0)
    (hden2 : 0 < B1 - beta2 * B0)
    (hcross : 0 < B0 * M - B1 * B) :
    (M - beta1 * B) / (B1 - beta1 * B0) <
      (M - beta2 * B) / (B1 - beta2 * B0) := by
  rw [div_lt_div_iff₀ hden1 hden2]
  have hproduct : 0 < (beta2 - beta1) * (B0 * M - B1 * B) :=
    mul_pos (sub_pos.mpr hbeta) hcross
  have hid :
      (M - beta2 * B) * (B1 - beta1 * B0) -
          (M - beta1 * B) * (B1 - beta2 * B0) =
        (beta2 - beta1) * (B0 * M - B1 * B) := by
    ring
  nlinarith

end Theory.PiDigits.BoundaryKernelRatioAlgebra

#print axioms Theory.PiDigits.BoundaryKernelRatioAlgebra.normalizedAffineCoefficient_strictMono
