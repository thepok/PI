import TheoryLib.PiQuantitativeBlockHitting.T85T85NonselectedColumnRationalResidues

/-!
# T86: finite rational nonselected endpoint congruence

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module combines the direct rational residues for the selected-boundary
and nonselected columns at a stable endpoint.  It establishes only a finite
rational congruence for `endpointDefect`; it makes no decimal-expansion, SP1,
or V1 claim.
-/

namespace Theory.PiDigits.T86NonselectedEndpointCongruence

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence T84SelectedBoundaryColumn
  T85NonselectedColumnRationalResidues

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The four direct rational nonselected pole columns combine to six modulo
nine. -/
theorem nonselectedColumn_congr_six (M : ℕ) :
    RatCongruentThree 2 (nonselectedColumn M) 6 := by
  have h := ratCongruentThree_add
    (nonselectedPoleOne_congr_six M) (nonselectedPoleTwo_congr_three M)
  have h' := ratCongruentThree_add h (nonselectedPoleThree_congr_six M)
  have h'' := ratCongruentThree_add h' (nonselectedPoleFour_congr_zero M)
  have hfifteen : RatCongruentThree 2 (15 : ℚ) 6 := by
    unfold RatCongruentThree
    right
    rw [show (15 : ℚ) - 6 = 9 by norm_num,
      show (9 : ℚ) = ((9 : ℕ) : ℚ) by norm_cast,
      padicValRat.of_nat, show (9 : ℕ) = 3 ^ 2 from by norm_num]
    rw [padicValNat.prime_pow (p := 3) 2]
  have hsum : RatCongruentThree 2 (nonselectedColumn M) 15 := by
    rw [nonselectedColumn]
    convert h'' using 1 <;> ring
  exact ratCongruentThree_trans hsum hfifteen

/-- Ten is one modulo nine in the rational three-adic sense. -/
theorem ten_congr_one : RatCongruentThree 2 (10 : ℚ) 1 := by
  unfold RatCongruentThree
  right
  rw [show (10 : ℚ) - 1 = 9 by norm_num,
    show (9 : ℚ) = ((9 : ℕ) : ℚ) by norm_cast,
    padicValRat.of_nat, show (9 : ℕ) = 3 ^ 2 from by norm_num]
  rw [padicValNat.prime_pow (p := 3) 2]

/-- At an endpoint with residue four modulo nine, the finite rational endpoint
defect is one modulo nine. -/
theorem endpointDefect_congr_one (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (endpointDefect M) 1 := by
  rw [endpointDefect_eq_selectedBoundary_add_nonselected]
  have h := ratCongruentThree_add
    (selectedBoundaryColumn_congr_four M hM)
    (nonselectedColumn_congr_six M)
  have hten : RatCongruentThree 2
      (selectedBoundaryColumn M + nonselectedColumn M) 10 := by
    convert h using 1 <;> norm_num
  exact ratCongruentThree_trans hten ten_congr_one

/-- The finite rational endpoint congruence holds at every positive even
selected depth. -/
theorem endpointDefect_congr_one_at_selectedDepth
    (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree 2 (endpointDefect (selectedDepth (2 * t))) 1 := by
  exact endpointDefect_congr_one (selectedDepth (2 * t))
    (selectedDepth_mod_nine_of_twice t ht)

end Theory.PiDigits.T86NonselectedEndpointCongruence

#print axioms Theory.PiDigits.T86NonselectedEndpointCongruence.nonselectedColumn_congr_six
#print axioms Theory.PiDigits.T86NonselectedEndpointCongruence.ten_congr_one
#print axioms Theory.PiDigits.T86NonselectedEndpointCongruence.endpointDefect_congr_one
#print axioms Theory.PiDigits.T86NonselectedEndpointCongruence.endpointDefect_congr_one_at_selectedDepth
