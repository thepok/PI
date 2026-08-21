import TheoryLib.PiQuantitativeBlockHitting.T83T83RegularBoundaryRationalResidues

/-!
# T84: selected paired and regular-boundary column

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module combines the machine-checked selected paired-error column and
regular boundary column into one direct rational residue. It also partitions
the exact endpoint defect into that selected boundary column and the remaining
nonselected column. It makes no rational residue claim about
`nonselectedColumn` or `endpointDefect`, and no claim about SP1 or V1.
-/

open scoped BigOperators

namespace Theory.PiDigits.T84SelectedBoundaryColumn

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence T82SelectedPairedColumnModNine
  T83RegularBoundaryRationalResidues

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The four selected paired-error sums with the T82 ranges. -/
def selectedPairedColumn (M : ℕ) : ℚ :=
  (∑ r ∈ Finset.range (M + 2), pairedError poleOne 1 r) +
  (∑ r ∈ Finset.range (M + 2), pairedError poleTwo 4 r) +
  (∑ r ∈ Finset.range (M + 1), pairedError poleThree 5 r) +
  ∑ r ∈ Finset.range (M + 1), pairedError poleFour 6 r

/-- The two regular boundary terms at depth `M + 1`. -/
def regularBoundaryColumn (M : ℕ) : ℚ :=
  poleOne (M + 1) + poleTwo (M + 1)

/-- The selected paired and regular-boundary columns combined. -/
def selectedBoundaryColumn (M : ℕ) : ℚ :=
  selectedPairedColumn M + regularBoundaryColumn M

/-- The complete-block and tail complements, in pole order. -/
def nonselectedColumn (M : ℕ) : ℚ :=
  completeNonselected poleOne 1 M + tailNonselected poleOne 1 M +
  completeNonselected poleTwo 4 M + tailNonselected poleTwo 4 M +
  completeNonselected poleThree 5 M + tailNonselected poleThree 5 M +
  completeNonselected poleFour 6 M + tailNonselected poleFour 6 M

/-- At a stable endpoint, the selected paired-error column is six modulo
nine in the rational three-adic sense. -/
theorem selectedPairedColumn_congr_six (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (selectedPairedColumn M) 6 := by
  rcases selectedPairedSums_congr_column M hM with ⟨h1, h2, h3, h4⟩
  have h12 := ratCongruentThree_add h1 h2
  have h123 := ratCongruentThree_add h12 h3
  have h1234 := ratCongruentThree_add h123 h4
  convert h1234 using 1 <;> norm_num

/-- At a stable endpoint, the regular boundary column is seven modulo nine
in the rational three-adic sense. -/
theorem regularBoundaryColumn_congr_seven (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (regularBoundaryColumn M) 7 := by
  have h := ratCongruentThree_add
    (poleOne_boundary_congr_two M hM) (poleTwo_boundary_congr_five M hM)
  convert h using 1 <;> norm_num

/-- Thirteen is four modulo nine in the rational three-adic sense. -/
theorem thirteen_congr_four : RatCongruentThree 2 (13 : ℚ) 4 := by
  unfold RatCongruentThree
  right
  have hsub : (13 : ℚ) - 4 = 9 := by norm_num
  rw [hsub, padicValRat_three_nine]
  norm_num

/-- At a stable endpoint, the selected paired and regular-boundary columns
combine to four modulo nine in the rational three-adic sense. -/
theorem selectedBoundaryColumn_congr_four (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (selectedBoundaryColumn M) 4 := by
  have h := ratCongruentThree_add
    (selectedPairedColumn_congr_six M hM)
    (regularBoundaryColumn_congr_seven M hM)
  have h13 : RatCongruentThree 2 (selectedBoundaryColumn M) 13 := by
    convert h using 1 <;> norm_num
  exact ratCongruentThree_trans h13 thirteen_congr_four

/-- The selected paired and regular-boundary column residue holds at every
positive even half-epoch. -/
theorem selectedBoundaryColumn_congr_four_at_selectedDepth
    (t : ℕ) (ht : 1 ≤ t) :
    RatCongruentThree 2 (selectedBoundaryColumn (selectedDepth (2 * t))) 4 := by
  exact selectedBoundaryColumn_congr_four (selectedDepth (2 * t))
    (selectedDepth_mod_nine_of_twice t ht)

/-- The exact endpoint defect partitions into the selected boundary column and
the nonselected column. This is an algebraic rearrangement, not a residue
claim. -/
theorem endpointDefect_eq_selectedBoundary_add_nonselected (M : ℕ) :
    endpointDefect M = selectedBoundaryColumn M + nonselectedColumn M := by
  rw [endpointDefect_eq_shell]
  simp only [endpointDefectShell, poleOneShell, poleTwoShell, poleThreeShell,
    poleFourShell, selectedBoundaryColumn, selectedPairedColumn,
    regularBoundaryColumn, nonselectedColumn]
  ring

end Theory.PiDigits.T84SelectedBoundaryColumn

#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.selectedPairedColumn
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.regularBoundaryColumn
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.selectedBoundaryColumn
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.nonselectedColumn
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.selectedPairedColumn_congr_six
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.regularBoundaryColumn_congr_seven
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.thirteen_congr_four
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.selectedBoundaryColumn_congr_four
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.selectedBoundaryColumn_congr_four_at_selectedDepth
#print axioms Theory.PiDigits.T84SelectedBoundaryColumn.endpointDefect_eq_selectedBoundary_add_nonselected
