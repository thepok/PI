import TheoryLib.PiQuantitativeBlockHitting.T81T81SelectedPairedRationalResidues

/-!
# T82: selected paired-error column modulo nine

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module scales T81's selected paired-error residues to modulo nine and
aggregates exactly the four selected ranges.  It does not use the `ZMod`
ledger as a rational-congruence bridge and makes no claim about SP1 or V1.
-/

namespace Theory.PiDigits.T82SelectedPairedColumnModNine

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence T81SelectedPairedRationalResidues

/-- Multiplying a rational congruence modulo three by three yields a
congruence modulo nine. -/
theorem ratCongruentThree_scale_three {x c : ℚ}
    (h : RatCongruentThree 1 (x / 3) c) : RatCongruentThree 2 x (3 * c) := by
  rcases h with heq | hval
  · left
    have hx : x = 3 * (x / 3) := by field_simp
    rw [hx, heq]
  · right
    have hzero : padicValRat 3 (0 : ℚ) = 0 := by simp [padicValRat]
    have hne : x / 3 - c ≠ 0 := by
      intro hz
      rw [hz, hzero] at hval
      omega
    have hkey : x - 3 * c = 3 * (x / 3 - c) := by ring
    rw [hkey, padicValRat.mul (show (3 : ℚ) ≠ 0 by norm_num) hne]
    have hthree : padicValRat 3 (3 : ℚ) = 1 := by
      have hcast : (3 : ℚ) = ((3 : ℕ) : ℚ) := by norm_cast
      rw [hcast, padicValRat.of_nat, padicValNat_self (p := 3)]
      norm_num
    rw [hthree]
    omega

/-- The pole-one selected paired error is three modulo nine. -/
theorem pairedError_poleOne_congr_three (r : ℕ) :
    RatCongruentThree 2 (pairedError poleOne 1 r) 3 := by
  simpa using ratCongruentThree_scale_three (pairedError_poleOne_div_three_congr_one r)

/-- The pole-two selected paired error is three modulo nine. -/
theorem pairedError_poleTwo_congr_three (r : ℕ) :
    RatCongruentThree 2 (pairedError poleTwo 4 r) 3 := by
  simpa using ratCongruentThree_scale_three (pairedError_poleTwo_div_three_congr_one r)

/-- The pole-three selected paired error is six modulo nine. -/
theorem pairedError_poleThree_congr_six (r : ℕ) :
    RatCongruentThree 2 (pairedError poleThree 5 r) 6 := by
  convert ratCongruentThree_scale_three (pairedError_poleThree_div_three_congr_two r) using 1 <;> norm_num

/-- The pole-four selected paired error is six modulo nine. -/
theorem pairedError_poleFour_congr_six (r : ℕ) :
    RatCongruentThree 2 (pairedError poleFour 6 r) 6 := by
  convert ratCongruentThree_scale_three (pairedError_poleFour_div_three_congr_two r) using 1 <;> norm_num

/-- The first selected range has its exact symbolic constant. -/
theorem sum_pairedError_poleOne_congr_symbolic (M : ℕ) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 2), pairedError poleOne 1 r)
      (3 * (M + 2 : ℕ)) := by
  have h := ratCongruentThree_sum (S := Finset.range (M + 2))
    (f := fun r ↦ pairedError poleOne 1 r) (g := fun _ ↦ (3 : ℚ))
    (fun r _ ↦ pairedError_poleOne_congr_three r)
  simpa [mul_comm] using h

/-- The second selected range has its exact symbolic constant. -/
theorem sum_pairedError_poleTwo_congr_symbolic (M : ℕ) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 2), pairedError poleTwo 4 r)
      (3 * (M + 2 : ℕ)) := by
  have h := ratCongruentThree_sum (S := Finset.range (M + 2))
    (f := fun r ↦ pairedError poleTwo 4 r) (g := fun _ ↦ (3 : ℚ))
    (fun r _ ↦ pairedError_poleTwo_congr_three r)
  simpa [mul_comm] using h

/-- The third selected range has its exact symbolic constant. -/
theorem sum_pairedError_poleThree_congr_symbolic (M : ℕ) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 1), pairedError poleThree 5 r)
      (6 * (M + 1 : ℕ)) := by
  have h := ratCongruentThree_sum (S := Finset.range (M + 1))
    (f := fun r ↦ pairedError poleThree 5 r) (g := fun _ ↦ (6 : ℚ))
    (fun r _ ↦ pairedError_poleThree_congr_six r)
  simpa [mul_comm] using h

/-- The fourth selected range has its exact symbolic constant. -/
theorem sum_pairedError_poleFour_congr_symbolic (M : ℕ) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 1), pairedError poleFour 6 r)
      (6 * (M + 1 : ℕ)) := by
  have h := ratCongruentThree_sum (S := Finset.range (M + 1))
    (f := fun r ↦ pairedError poleFour 6 r) (g := fun _ ↦ (6 : ℚ))
    (fun r _ ↦ pairedError_poleFour_congr_six r)
  simpa [mul_comm] using h

/-- Nine has three-adic valuation two. -/
theorem padicValRat_three_nine : padicValRat 3 (9 : ℚ) = 2 := by
  have hcast : (9 : ℚ) = ((9 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat]
  have hsplit : (9 : ℕ) = 3 * 3 := by norm_num
  rw [hsplit, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self (p := 3)]
  norm_num

/-- The first two symbolic selected-pair constants vanish modulo nine at a
stable endpoint. -/
theorem three_mul_M_add_two_congr_zero (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (3 * (M + 2 : ℕ)) 0 := by
  have hdecomp : M = 9 * (M / 9) + 4 := by
    have h := Nat.mod_add_div M 9
    omega
  unfold RatCongruentThree
  right
  let q : ℕ := M / 9
  have hdecompq : M = 9 * q + 4 := by simpa [q] using hdecomp
  have hqne : ((3 * q + 2 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show 3 * q + 2 ≠ 0 by omega)
  have hnat : 3 * (M + 2) = 9 * (3 * q + 2) := by
    rw [hdecompq]
    omega
  have hfactor : (3 : ℚ) * ((M + 2 : ℕ) : ℚ) - 0 =
      9 * ((3 * q + 2 : ℕ) : ℚ) := by
    norm_num
    exact_mod_cast hnat
  rw [hfactor, padicValRat.mul (by norm_num) hqne, padicValRat_three_nine]
  have hnonneg : 0 ≤ padicValRat 3 ((3 * q + 2 : ℕ) : ℚ) := by
    rw [padicValRat.of_nat]
    exact_mod_cast Nat.zero_le _
  omega

/-- The last two symbolic selected-pair constants are three modulo nine at a
stable endpoint. -/
theorem six_mul_M_add_one_congr_three (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (6 * (M + 1 : ℕ)) 3 := by
  have hdecomp : M = 9 * (M / 9) + 4 := by
    have h := Nat.mod_add_div M 9
    omega
  unfold RatCongruentThree
  right
  let q : ℕ := M / 9
  have hdecompq : M = 9 * q + 4 := by simpa [q] using hdecomp
  have hqne : ((6 * q + 3 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show 6 * q + 3 ≠ 0 by omega)
  have hnat : 6 * (M + 1) = 9 * (6 * q + 3) + 3 := by
    rw [hdecompq]
    omega
  have hrat : (6 : ℚ) * ((M : ℚ) + 1) =
      9 * ((6 : ℚ) * (q : ℚ) + 3) + 3 := by
    exact_mod_cast hnat
  have hfactor : (6 : ℚ) * ((M + 1 : ℕ) : ℚ) - 3 =
      9 * ((6 * q + 3 : ℕ) : ℚ) := by
    norm_num
    linarith
  rw [hfactor, padicValRat.mul (by norm_num) hqne, padicValRat_three_nine]
  have hnonneg : 0 ≤ padicValRat 3 ((6 * q + 3 : ℕ) : ℚ) := by
    rw [padicValRat.of_nat]
    exact_mod_cast Nat.zero_le _
  omega

/-- The four selected ranges realize the rational selected-pair column at a
stable endpoint. -/
theorem selectedPairedSums_congr_column (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 2), pairedError poleOne 1 r) 0 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 2), pairedError poleTwo 4 r) 0 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 1), pairedError poleThree 5 r) 3 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (M + 1), pairedError poleFour 6 r) 3 := by
  exact ⟨ratCongruentThree_trans (sum_pairedError_poleOne_congr_symbolic M)
      (three_mul_M_add_two_congr_zero M hM),
    ratCongruentThree_trans (sum_pairedError_poleTwo_congr_symbolic M)
      (three_mul_M_add_two_congr_zero M hM),
    ratCongruentThree_trans (sum_pairedError_poleThree_congr_symbolic M)
      (six_mul_M_add_one_congr_three M hM),
    ratCongruentThree_trans (sum_pairedError_poleFour_congr_symbolic M)
      (six_mul_M_add_one_congr_three M hM)⟩

/-- The selected-pair column holds at every positive even half-epoch. -/
theorem selectedPairedSums_congr_column_at_selectedDepth (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree 2
      (∑ r ∈ Finset.range (selectedDepth (2 * t) + 2), pairedError poleOne 1 r) 0 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (selectedDepth (2 * t) + 2), pairedError poleTwo 4 r) 0 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (selectedDepth (2 * t) + 1), pairedError poleThree 5 r) 3 ∧
    RatCongruentThree 2
      (∑ r ∈ Finset.range (selectedDepth (2 * t) + 1), pairedError poleFour 6 r) 3 := by
  exact selectedPairedSums_congr_column (selectedDepth (2 * t))
    (selectedDepth_mod_nine_of_twice t ht)

end Theory.PiDigits.T82SelectedPairedColumnModNine

#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.ratCongruentThree_scale_three
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.pairedError_poleOne_congr_three
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.pairedError_poleTwo_congr_three
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.pairedError_poleThree_congr_six
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.pairedError_poleFour_congr_six
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.sum_pairedError_poleOne_congr_symbolic
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.sum_pairedError_poleTwo_congr_symbolic
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.sum_pairedError_poleThree_congr_symbolic
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.sum_pairedError_poleFour_congr_symbolic
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.padicValRat_three_nine
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.three_mul_M_add_two_congr_zero
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.six_mul_M_add_one_congr_three
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.selectedPairedSums_congr_column
#print axioms Theory.PiDigits.T82SelectedPairedColumnModNine.selectedPairedSums_congr_column_at_selectedDepth
