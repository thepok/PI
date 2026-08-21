import TheoryLib.PiQuantitativeBlockHitting.T74T74ThreePrimaryDecimation

/-!
# T77: exact selected three-adic BBP defect shell

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module formalizes the exact finite-sum decomposition and the stable
residue ledger behind the proposed congruence

`9 * B_(9*M+13) - B_M = 1 (mod 9)` when `M = 4 (mod 9)`.

The rational-to-residue bridge for the paired errors is deliberately not
asserted here: proving it uniformly requires a localized binomial lemma after
arbitrarily large powers of three have been cancelled from a pole denominator.
Consequently this file proves the exact shell identity and its finite residue
ledger, but it does not claim the rational congruence, selected-path escape, or
any decimal-word theorem for pi.
-/

open scoped BigOperators

namespace Theory.PiDigits.T77SelectedPadicDefectShell

open T74ThreePrimaryDecimation

/-- A partial sum of one rational pole, through index `M` inclusive. -/
def polePartial (f : ℕ → ℚ) (M : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (M + 1), f k

/-- The canonical four-pole BBP rational coefficient through index `M`. -/
def bbpPartial (M : ℕ) : ℚ :=
  polePartial poleOne M + polePartial poleTwo M +
    polePartial poleThree M + polePartial poleFour M

/-- The ninefold endpoint defect at the stable endpoint `9*M+13`. -/
def endpointDefect (M : ℕ) : ℚ :=
  9 * bbpPartial (9 * M + 13) - bbpPartial M

/-- The terms in complete nine-blocks outside the selected residue `d`. -/
def completeNonselected (f : ℕ → ℚ) (d M : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (M + 1),
    ∑ s ∈ Finset.range 9 with s ≠ d, 9 * f (9 * r + s)

/-- The terms in the last five-residue block outside the selected residue. -/
def tailNonselected (f : ℕ → ℚ) (d M : ℕ) : ℚ :=
  ∑ s ∈ Finset.range 5 with s ≠ d, 9 * f (9 * (M + 1) + s)

/-- The exact paired error attached to a residue lift. -/
def pairedError (f : ℕ → ℚ) (d r : ℕ) : ℚ :=
  9 * f (9 * r + d) - f r

/-- The pole-one part of the proposed defect shell. -/
def poleOneShell (M : ℕ) : ℚ :=
  poleOne (M + 1) +
    (∑ r ∈ Finset.range (M + 2), pairedError poleOne 1 r) +
    completeNonselected poleOne 1 M + tailNonselected poleOne 1 M

/-- The pole-two part of the proposed defect shell. -/
def poleTwoShell (M : ℕ) : ℚ :=
  poleTwo (M + 1) +
    (∑ r ∈ Finset.range (M + 2), pairedError poleTwo 4 r) +
    completeNonselected poleTwo 4 M + tailNonselected poleTwo 4 M

/-- The pole-three part of the proposed defect shell. -/
def poleThreeShell (M : ℕ) : ℚ :=
  (∑ r ∈ Finset.range (M + 1), pairedError poleThree 5 r) +
    completeNonselected poleThree 5 M + tailNonselected poleThree 5 M

/-- The pole-four part of the proposed defect shell. -/
def poleFourShell (M : ℕ) : ℚ :=
  (∑ r ∈ Finset.range (M + 1), pairedError poleFour 6 r) +
    completeNonselected poleFour 6 M + tailNonselected poleFour 6 M

/-- The four exact pole shells combined. -/
def endpointDefectShell (M : ℕ) : ℚ :=
  poleOneShell M + poleTwoShell M + poleThreeShell M + poleFourShell M

/-- A range ending five terms into a nine-block decomposes into complete
nine-blocks and one five-term tail. -/
theorem sum_range_nine_blocks_five_tail (f : ℕ → ℚ) (R : ℕ) :
    (∑ k ∈ Finset.range (9 * R + 5), f k) =
      (∑ r ∈ Finset.range R, ∑ s ∈ Finset.range 9, f (9 * r + s)) +
        ∑ s ∈ Finset.range 5, f (9 * R + s) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [show 9 * (R + 1) + 5 = (9 * R + 5) + 9 by omega]
      rw [Finset.sum_range_add, ih, Finset.sum_range_succ]
      simp only [Finset.sum_range_succ]
      ring_nf

/-- A finite sum splits into a selected member and the complementary filter. -/
theorem sum_eq_selected_add_complement (f : ℕ → ℚ) {N d : ℕ} (hd : d < N) :
    (∑ s ∈ Finset.range N, f s) =
      f d + ∑ s ∈ Finset.range N with s ≠ d, f s := by
  rw [Finset.filter_ne']
  exact (Finset.add_sum_erase (Finset.range N) f (Finset.mem_range.mpr hd)).symm

/-- A complete nine-block is its selected residue plus its complement. -/
theorem nine_block_selected_one (f : ℕ → ℚ) (r : ℕ) :
    (∑ s ∈ Finset.range 9, 9 * f (9 * r + s)) =
      9 * f (9 * r + 1) +
        ∑ s ∈ Finset.range 9 with s ≠ 1, 9 * f (9 * r + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * r + s)) (by omega)

/-- A complete nine-block is its selected residue plus its complement. -/
theorem nine_block_selected_four (f : ℕ → ℚ) (r : ℕ) :
    (∑ s ∈ Finset.range 9, 9 * f (9 * r + s)) =
      9 * f (9 * r + 4) +
        ∑ s ∈ Finset.range 9 with s ≠ 4, 9 * f (9 * r + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * r + s)) (by omega)

/-- A complete nine-block is its selected residue plus its complement. -/
theorem nine_block_selected_five (f : ℕ → ℚ) (r : ℕ) :
    (∑ s ∈ Finset.range 9, 9 * f (9 * r + s)) =
      9 * f (9 * r + 5) +
        ∑ s ∈ Finset.range 9 with s ≠ 5, 9 * f (9 * r + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * r + s)) (by omega)

/-- A complete nine-block is its selected residue plus its complement. -/
theorem nine_block_selected_six (f : ℕ → ℚ) (r : ℕ) :
    (∑ s ∈ Finset.range 9, 9 * f (9 * r + s)) =
      9 * f (9 * r + 6) +
        ∑ s ∈ Finset.range 9 with s ≠ 6, 9 * f (9 * r + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * r + s)) (by omega)

/-- The selected residue one occurs in the five-term tail. -/
theorem five_tail_selected_one (f : ℕ → ℚ) (R : ℕ) :
    (∑ s ∈ Finset.range 5, 9 * f (9 * R + s)) =
      9 * f (9 * R + 1) +
        ∑ s ∈ Finset.range 5 with s ≠ 1, 9 * f (9 * R + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * R + s)) (by omega)

/-- The selected residue four occurs in the five-term tail. -/
theorem five_tail_selected_four (f : ℕ → ℚ) (R : ℕ) :
    (∑ s ∈ Finset.range 5, 9 * f (9 * R + s)) =
      9 * f (9 * R + 4) +
        ∑ s ∈ Finset.range 5 with s ≠ 4, 9 * f (9 * R + s) := by
  exact sum_eq_selected_add_complement (fun s ↦ 9 * f (9 * R + s)) (by omega)

/-- Residue five does not occur in a five-term tail. -/
theorem five_tail_selected_five (f : ℕ → ℚ) (R : ℕ) :
    (∑ s ∈ Finset.range 5, 9 * f (9 * R + s)) =
      ∑ s ∈ Finset.range 5 with s ≠ 5, 9 * f (9 * R + s) := by
  apply Finset.sum_congr
  · ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro s hs
    rfl

/-- Residue six does not occur in a five-term tail. -/
theorem five_tail_selected_six (f : ℕ → ℚ) (R : ℕ) :
    (∑ s ∈ Finset.range 5, 9 * f (9 * R + s)) =
      ∑ s ∈ Finset.range 5 with s ≠ 6, 9 * f (9 * R + s) := by
  apply Finset.sum_congr
  · ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro s hs
    rfl

/-- When the selected residue occurs in the tail, the oversubtracted old term
is restored by the displayed boundary term. -/
theorem selected_with_boundary (f : ℕ → ℚ) (d M : ℕ) :
    (∑ r ∈ Finset.range (M + 1), 9 * f (9 * r + d)) +
          9 * f (9 * (M + 1) + d) - polePartial f M =
      f (M + 1) + ∑ r ∈ Finset.range (M + 2), pairedError f d r := by
  simp only [polePartial, pairedError, Finset.sum_range_succ,
    Finset.sum_sub_distrib]
  ring

/-- Without a selected tail term, subtracting the old partial sum pairs the
two ranges term by term. -/
theorem selected_without_boundary (f : ℕ → ℚ) (d M : ℕ) :
    (∑ r ∈ Finset.range (M + 1), 9 * f (9 * r + d)) - polePartial f M =
      ∑ r ∈ Finset.range (M + 1), pairedError f d r := by
  simp only [polePartial, pairedError, Finset.sum_sub_distrib]

/-- Exact rational shell identity for pole one. -/
theorem poleOne_defect_eq_shell (M : ℕ) :
    9 * polePartial poleOne (9 * M + 13) - polePartial poleOne M =
      poleOneShell M := by
  rw [polePartial, show 9 * M + 13 + 1 = 9 * (M + 1) + 5 by omega]
  rw [Finset.mul_sum, sum_range_nine_blocks_five_tail]
  simp_rw [nine_block_selected_one]
  rw [Finset.sum_add_distrib, five_tail_selected_one]
  have hselected := selected_with_boundary poleOne 1 M
  simp only [completeNonselected, tailNonselected, poleOneShell]
  linear_combination hselected

/-- Exact rational shell identity for pole two. -/
theorem poleTwo_defect_eq_shell (M : ℕ) :
    9 * polePartial poleTwo (9 * M + 13) - polePartial poleTwo M =
      poleTwoShell M := by
  rw [polePartial, show 9 * M + 13 + 1 = 9 * (M + 1) + 5 by omega]
  rw [Finset.mul_sum, sum_range_nine_blocks_five_tail]
  simp_rw [nine_block_selected_four]
  rw [Finset.sum_add_distrib, five_tail_selected_four]
  have hselected := selected_with_boundary poleTwo 4 M
  simp only [completeNonselected, tailNonselected, poleTwoShell]
  linear_combination hselected

/-- Exact rational shell identity for pole three. -/
theorem poleThree_defect_eq_shell (M : ℕ) :
    9 * polePartial poleThree (9 * M + 13) - polePartial poleThree M =
      poleThreeShell M := by
  rw [polePartial, show 9 * M + 13 + 1 = 9 * (M + 1) + 5 by omega]
  rw [Finset.mul_sum, sum_range_nine_blocks_five_tail]
  simp_rw [nine_block_selected_five]
  rw [Finset.sum_add_distrib, five_tail_selected_five]
  have hselected := selected_without_boundary poleThree 5 M
  simp only [completeNonselected, tailNonselected, poleThreeShell]
  linear_combination hselected

/-- Exact rational shell identity for pole four. -/
theorem poleFour_defect_eq_shell (M : ℕ) :
    9 * polePartial poleFour (9 * M + 13) - polePartial poleFour M =
      poleFourShell M := by
  rw [polePartial, show 9 * M + 13 + 1 = 9 * (M + 1) + 5 by omega]
  rw [Finset.mul_sum, sum_range_nine_blocks_five_tail]
  simp_rw [nine_block_selected_six]
  rw [Finset.sum_add_distrib, five_tail_selected_six]
  have hselected := selected_without_boundary poleFour 6 M
  simp only [completeNonselected, tailNonselected, poleFourShell]
  linear_combination hselected

/-- The BBP endpoint defect is exactly the sum of the four explicit shells. -/
theorem endpointDefect_eq_shell (M : ℕ) :
    endpointDefect M = endpointDefectShell M := by
  rw [endpointDefect, bbpPartial, bbpPartial]
  have h1 := poleOne_defect_eq_shell M
  have h2 := poleTwo_defect_eq_shell M
  have h3 := poleThree_defect_eq_shell M
  have h4 := poleFour_defect_eq_shell M
  simp only [endpointDefectShell]
  linear_combination h1 + h2 + h3 + h4

/-! ## Stable endpoint and residue ledger -/

/-- The selected BBP endpoint depth, written without a rational division. -/
def selectedDepth (e : ℕ) : ℕ :=
  (5 * 3 ^ e - 13) / 8

/-- Positive powers of nine occupy the stable residue nine modulo 72. -/
theorem nine_pow_mod_seventyTwo {t : ℕ} (ht : 1 ≤ t) :
    9 ^ t % 72 = 9 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction u with
  | zero => norm_num
  | succ u ih =>
      rw [show 1 + (u + 1) = (1 + u) + 1 by omega]
      rw [pow_succ, Nat.mul_mod, ih (by omega)]

/-- At every positive even half-epoch, the endpoint depth is four modulo
nine.  This includes the smallest intended epoch `e=2`. -/
theorem selectedDepth_mod_nine_of_twice (t : ℕ) (ht : 1 ≤ t) :
    selectedDepth (2 * t) % 9 = 4 := by
  have hpow : 3 ^ (2 * t) % 72 = 9 := by
    rw [show 3 ^ (2 * t) = 9 ^ t by
      rw [pow_mul]
      norm_num]
    exact nine_pow_mod_seventyTwo ht
  have hdecomp : 3 ^ (2 * t) = 72 * (3 ^ (2 * t) / 72) + 9 := by
    have h := Nat.mod_add_div (3 ^ (2 * t)) 72
    omega
  let q := 3 ^ (2 * t) / 72
  have hnumer : 5 * 3 ^ (2 * t) - 13 = 8 * (45 * q + 4) := by
    dsimp only [q]
    omega
  rw [selectedDepth, hnumer, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-- The residue data `(M+2,M+2,M+1,M+1)` reduce to `(0,0,2,2)` modulo
three whenever `M` is four modulo nine. -/
theorem pairCountResidue_of_endpoint (M : ℕ) (hM : M % 9 = 4) :
    ![(M + 2) % 3, (M + 2) % 3, (M + 1) % 3, (M + 1) % 3] =
      ![0, 0, 2, 2] := by
  have hdecomp : M = 9 * (M / 9) + 4 := by
    have h := Nat.mod_add_div M 9
    omega
  ext i
  fin_cases i <;> simp <;> omega

/-- The four inclusive pair counts modulo three. -/
def pairCountResidue (i : Fin 4) : ZMod 3 :=
  ![0, 0, 2, 2] i

/-- The four positive linear-denominator slopes. -/
def poleSlope (i : Fin 4) : ℕ :=
  ![8, 2, 8, 4] i

/-- The four positive linear-denominator intercepts. -/
def poleIntercept (i : Fin 4) : ℕ :=
  ![1, 1, 5, 3] i

/-- The four selected residue lifts. -/
def selectedLift (i : Fin 4) : ℕ :=
  ![1, 4, 5, 6] i

/-- The coefficients of the four poles after reduction modulo three. -/
def poleCoefficientModThree (i : Fin 4) : ZMod 3 :=
  ![1, 1, 2, 1] i

/-- The four exponent-fold multipliers. -/
def exponentMultiplierModThree (i : Fin 4) : ZMod 3 :=
  ![1, 1, 1, 2] i

/-- The paired-error totals, embedded in the multiples of three modulo nine. -/
def pairedResidue (i : Fin 4) : ZMod 9 :=
  3 * (pairCountResidue i * poleCoefficientModThree i *
    exponentMultiplierModThree i).val

/-- The actual height-one contribution of one nonselected residue.  The
division by three is ordinary natural-number division after the height-one
test; inversion takes place only in the field `ZMod 3`. -/
def heightOneNonselectedResidue (i : Fin 4) (s : ℕ) : ZMod 9 :=
  let A := poleSlope i * s + poleIntercept i
  if s = selectedLift i then 0
  else if A % 3 = 0 ∧ A % 9 ≠ 0 then
    3 * (poleCoefficientModThree i * ((A / 3 : ℕ) : ZMod 3)⁻¹).val
  else 0

/-- Every complete residue block has zero height-one complement total. -/
theorem heightOneNonselected_completeBlock_table :
    List.ofFn (fun i : Fin 4 ↦
      ∑ s ∈ Finset.range 9, heightOneNonselectedResidue i s) = [0, 0, 0, 0] := by
  decide

/-- Direct reduction of the actual nonselected final residues `0,...,4`. -/
def nonselectedTailResidue (i : Fin 4) : ZMod 9 :=
  ∑ s ∈ Finset.range 5, heightOneNonselectedResidue i s

/-- The four final-block totals are `(6,3,6,0)` modulo nine. -/
theorem nonselectedTailResidue_table :
    List.ofFn nonselectedTailResidue = [6, 3, 6, 0] := by
  decide

/-- Inversion of an integer prime to nine, inside `ZMod 9`. -/
def inverseModNine (n : ℕ) (h : Nat.Coprime n 9) : ZMod 9 :=
  (((ZMod.unitOfCoprime n h : (ZMod 9)ˣ)⁻¹ : (ZMod 9)ˣ) : ZMod 9)

/-- Direct reduction of the two actual regular boundary terms at residue five. -/
def regularBoundaryResidue (i : Fin 4) : ZMod 9 :=
  match i with
  | ⟨0, _⟩ => 4 * inverseModNine (41 * 16 ^ 5) (by norm_num)
  | ⟨1, _⟩ => -inverseModNine (2 * 11 * 16 ^ 5) (by norm_num)
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0

/-- The two actual boundary residues reduce to `(2,5,0,0)`. -/
theorem regularBoundaryResidue_table :
    List.ofFn regularBoundaryResidue = [2, 5, 0, 0] := by
  decide

/-- The complete pole residue recorded by the shell ledger. -/
def poleShellResidue (i : Fin 4) : ZMod 9 :=
  pairedResidue i + nonselectedTailResidue i + regularBoundaryResidue i

/-- The paired column of the stable shell is `(0,0,3,3)`. -/
theorem pairedResidue_table :
    (List.ofFn pairedResidue) = [0, 0, 3, 3] := by
  decide

/-- The four pole totals are `(8,8,0,3)` modulo nine. -/
theorem poleShellResidue_table :
    (List.ofFn poleShellResidue) = [8, 8, 0, 3] := by
  decide

/-- The stable residue ledger sums to one modulo nine. -/
theorem poleShellResidue_sum :
    ∑ i : Fin 4, poleShellResidue i = 1 := by
  decide

end Theory.PiDigits.T77SelectedPadicDefectShell

#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.sum_range_nine_blocks_five_tail
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.selected_with_boundary
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.selected_without_boundary
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleOne_defect_eq_shell
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleTwo_defect_eq_shell
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleThree_defect_eq_shell
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleFour_defect_eq_shell
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.endpointDefect_eq_shell
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.nine_pow_mod_seventyTwo
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.selectedDepth_mod_nine_of_twice
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.pairCountResidue_of_endpoint
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.heightOneNonselected_completeBlock_table
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.nonselectedTailResidue_table
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.regularBoundaryResidue_table
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.pairedResidue_table
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleShellResidue_table
#print axioms Theory.PiDigits.T77SelectedPadicDefectShell.poleShellResidue_sum
