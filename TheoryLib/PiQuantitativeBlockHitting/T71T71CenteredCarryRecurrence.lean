import TheoryLib.PiQuantitativeBlockHitting.T70T70EmpiricalRigidityBridge

/-!
# T71: centered carry recurrence

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module formalizes the integer algebra used by the sevenfold BBP
centered-carry reduction.  It is deliberately generic: it does not define the
BBP coefficients, prove their analytic sum is pi, prove a positive density of
nonzero carries, or prove the every-word conjecture.
-/

namespace Theory.PiDigits.T71CenteredCarryRecurrence

/-- `CenteredRepresentation D U z S` says that `z` is a nearest integer to
`U / D` under the half-open convention and that `S = U - D*z` is the
corresponding centered numerator.  The inequalities avoid any dependence on
a library rounding convention. -/
def CenteredRepresentation (D U z S : ℤ) : Prop :=
  0 < D ∧ U = D * z + S ∧ -D ≤ 2 * S ∧ 2 * S < D

/-- A half-open centered representative modulo a positive modulus is unique.
-/
theorem centeredRepresentation_unique
    {D U z S z' S' : ℤ}
    (h : CenteredRepresentation D U z S)
    (h' : CenteredRepresentation D U z' S') :
    z = z' ∧ S = S' := by
  rcases h with ⟨hD, hU, hSlow, hShigh⟩
  rcases h' with ⟨_, hU', hS'low, hS'high⟩
  have hdiff : D * (z - z') = S' - S := by
    linarith
  have hlower : -D < S' - S := by
    linarith
  have hupper : S' - S < D := by
    linarith
  have hz : z = z' := by
    by_contra hne
    have hcases : z - z' ≤ -1 ∨ 1 ≤ z - z' := by omega
    rcases hcases with hneg | hpos
    · have : D * (z - z') ≤ -D := by nlinarith
      linarith
    · have : D ≤ D * (z - z') := by nlinarith
      linarith
  refine ⟨hz, ?_⟩
  subst z'
  linarith

/-- Exact one-step centered-remainder algebra for a changing denominator.

The intended BBP substitution is `base = 10`, `scale = Λ_n`,
`forcing = J_n`, and `carry = z_{n+1} - 10*z_n`. -/
theorem centeredNumerator_step
    {base scale D D' U U' z z' S S' forcing carry : ℤ}
    (hD : D' = scale * D)
    (hU : U' = base * scale * U + forcing)
    (hS : S = U - D * z)
    (hS' : S' = U' - D' * z')
    (hcarry : carry = z' - base * z) :
    S' = base * scale * S + forcing - carry * D' := by
  subst D'
  subst U'
  subst S
  subst S'
  subst carry
  ring

/-- The candidate old quotient advanced by the radix has remainder
`base*scale*S + forcing` at the new denominator. -/
theorem advancedQuotient_representation
    {base scale D D' U U' z S forcing : ℤ}
    (hD : D' = scale * D)
    (hU : U' = base * scale * U + forcing)
    (hS : U = D * z + S) :
    U' = D' * (base * z) + (base * scale * S + forcing) := by
  subst D'
  subst U'
  rw [hS]
  ring

/-- The exact zero-carry test.  Once the current and next centered
representations are fixed, the carry vanishes exactly when the uncorrected
new numerator already lies in the next half-open centered interval. -/
theorem carry_eq_zero_iff_uncorrected_centered
    {base scale D D' U U' z z' S S' forcing carry : ℤ}
    (hcurrent : CenteredRepresentation D U z S)
    (hnext : CenteredRepresentation D' U' z' S')
    (hD : D' = scale * D)
    (hU : U' = base * scale * U + forcing)
    (hcarry : carry = z' - base * z) :
    carry = 0 ↔
      -D' ≤ 2 * (base * scale * S + forcing) ∧
        2 * (base * scale * S + forcing) < D' := by
  let T : ℤ := base * scale * S + forcing
  have hcandidate : U' = D' * (base * z) + T := by
    apply advancedQuotient_representation hD hU
    exact hcurrent.2.1
  constructor
  · intro hzero
    have hz' : z' = base * z := by
      rw [hcarry] at hzero
      linarith
    have hST : S' = T := by
      rw [hz'] at hnext
      linarith [hnext.2.1, hcandidate]
    simpa [hST] using And.intro hnext.2.2.1 hnext.2.2.2
  · rintro ⟨hTlow, hThigh⟩
    have hDpos : 0 < D' := hnext.1
    have hcand : CenteredRepresentation D' U' (base * z) T :=
      ⟨hDpos, hcandidate, hTlow, hThigh⟩
    have hz : base * z = z' :=
      (centeredRepresentation_unique hcand hnext).1
    rw [hcarry, ← hz]
    ring

end Theory.PiDigits.T71CenteredCarryRecurrence

#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.centeredRepresentation_unique
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.centeredNumerator_step
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.advancedQuotient_representation
#print axioms Theory.PiDigits.T71CenteredCarryRecurrence.carry_eq_zero_iff_uncorrected_centered
