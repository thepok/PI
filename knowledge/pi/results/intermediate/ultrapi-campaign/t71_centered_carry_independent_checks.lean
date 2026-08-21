import TheoryLib.PiQuantitativeBlockHitting.T71T71CenteredCarryRecurrence

/-!
Independent type-surface and boundary checks for T71's generic centered-carry
algebra.  These examples pin the changing-denominator orientation, the sign
of the carry correction, and the lower-inclusive/upper-exclusive convention.
-/

namespace UltraPiT71IndependentChecks

open Theory.PiDigits.T71CenteredCarryRecurrence

/-- Pin uniqueness for the exact half-open centered representation. -/
example {D U z S z' S' : ℤ}
    (h : CenteredRepresentation D U z S)
    (h' : CenteredRepresentation D U z' S') :
    z = z' ∧ S = S' := by
  exact centeredRepresentation_unique h h'

/-- Pin the intended recurrence from the BBP report: the correction is
`-carry * D'`, with the new denominator `D' = scale * D`. -/
example {scale D D' U U' z z' S S' forcing carry : ℤ}
    (hD : D' = scale * D)
    (hU : U' = 10 * scale * U + forcing)
    (hS : S = U - D * z)
    (hS' : S' = U' - D' * z')
    (hcarry : carry = z' - 10 * z) :
    S' = 10 * scale * S + forcing - carry * D' := by
  exact centeredNumerator_step hD hU hS hS' hcarry

/-- Pin the advanced old quotient and its uncorrected new remainder. -/
example {scale D D' U U' z S forcing : ℤ}
    (hD : D' = scale * D)
    (hU : U' = 10 * scale * U + forcing)
    (hS : U = D * z + S) :
    U' = D' * (10 * z) + (10 * scale * S + forcing) := by
  exact advancedQuotient_representation hD hU hS

/-- Pin the zero-carry criterion, including both inequality orientations. -/
example {scale D D' U U' z z' S S' forcing carry : ℤ}
    (hcurrent : CenteredRepresentation D U z S)
    (hnext : CenteredRepresentation D' U' z' S')
    (hD : D' = scale * D)
    (hU : U' = 10 * scale * U + forcing)
    (hcarry : carry = z' - 10 * z) :
    carry = 0 ↔
      -D' ≤ 2 * (10 * scale * S + forcing) ∧
        2 * (10 * scale * S + forcing) < D' := by
  exact carry_eq_zero_iff_uncorrected_centered hcurrent hnext hD hU hcarry

/-- At the lower tie, `-D/2` belongs to the centered interval. -/
example : CenteredRepresentation 10 (-5) 0 (-5) := by
  norm_num [CenteredRepresentation]

/-- At the upper tie, `+D/2` does not belong to the centered interval. -/
example : ¬ CenteredRepresentation 10 5 0 5 := by
  norm_num [CenteredRepresentation]

/-- The upper tie is represented instead by advancing the quotient and using
the included lower endpoint. -/
example : CenteredRepresentation 10 5 1 (-5) := by
  norm_num [CenteredRepresentation]

/-- A lower-tie uncorrected remainder has zero carry. -/
example :
    (0 : ℤ) = 0 ↔
      -(10 : ℤ) ≤ (2 : ℤ) * (10 * 1 * 0 + (-5)) ∧
        (2 : ℤ) * (10 * 1 * 0 + (-5)) < 10 := by
  have hcurrent : CenteredRepresentation 10 0 0 0 := by
    norm_num [CenteredRepresentation]
  have hnext : CenteredRepresentation 10 (-5) 0 (-5) := by
    norm_num [CenteredRepresentation]
  exact carry_eq_zero_iff_uncorrected_centered
    (base := 10) (scale := 1) (D := 10) (D' := 10)
    (U := 0) (U' := -5) (z := 0) (z' := 0)
    (S := 0) (S' := -5) (forcing := -5) (carry := 0)
    hcurrent hnext (by norm_num) (by norm_num) (by norm_num)

/-- An upper-tie uncorrected remainder advances the quotient, so its carry is
one and the strict upper inequality fails. -/
example :
    (1 : ℤ) = 0 ↔
      -(10 : ℤ) ≤ (2 : ℤ) * (10 * 1 * 0 + 5) ∧
        (2 : ℤ) * (10 * 1 * 0 + 5) < 10 := by
  have hcurrent : CenteredRepresentation 10 0 0 0 := by
    norm_num [CenteredRepresentation]
  have hnext : CenteredRepresentation 10 5 1 (-5) := by
    norm_num [CenteredRepresentation]
  exact carry_eq_zero_iff_uncorrected_centered
    (base := 10) (scale := 1) (D := 10) (D' := 10)
    (U := 0) (U' := 5) (z := 0) (z' := 1)
    (S := 0) (S' := -5) (forcing := 5) (carry := 1)
    hcurrent hnext (by norm_num) (by norm_num) (by norm_num)

end UltraPiT71IndependentChecks

#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.centeredRepresentation_unique
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.centeredNumerator_step
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.advancedQuotient_representation
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.carry_eq_zero_iff_uncorrected_centered
