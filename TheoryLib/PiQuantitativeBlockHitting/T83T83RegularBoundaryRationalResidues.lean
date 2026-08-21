import TheoryLib.PiQuantitativeBlockHitting.T82T82SelectedPairedColumnModNine

/-!
# T83: regular boundary rational residues

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module records direct rational residues behind the regular boundary of
the selected BBP column. It derives the pole-one and pole-two boundary
residues from their rational definitions, without using the `ZMod` ledger as
a rational bridge. It makes no claim about SP1 or V1.
-/

namespace Theory.PiDigits.T83RegularBoundaryRationalResidues

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Sixteen raised to the ninth power is one modulo nine. -/
theorem sixteen_pow_nine_mod_nine : Nat.ModEq 9 (16 ^ 9) 1 := by
  decide

/-- Any multiple of nine powers of sixteen stays one modulo nine. -/
theorem sixteen_pow_nine_mul_mod_nine (q : ℕ) :
    Nat.ModEq 9 (16 ^ (9 * q)) 1 := by
  rw [pow_mul]
  exact (sixteen_pow_nine_mod_nine.pow q).trans
    (by show (1 : ℕ) ^ q % 9 = 1 % 9; rw [one_pow])

/-- Sixteen to any multiple-of-nine power is one modulo nine in the rational
three-adic sense. The zero case is handled by equality because mathlib assigns
the finite valuation zero, rather than infinity, to the zero rational. -/
theorem ratCongruentThree_sixteen_pow_nine_one (q : ℕ) :
    RatCongruentThree 2 ((16 : ℚ) ^ (9 * q)) 1 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact Or.inl (by simp)
  · unfold RatCongruentThree
    right
    have hgt : 1 < 16 ^ (9 * q) :=
      one_lt_pow' (a := (16 : ℕ)) (by norm_num) (by omega)
    have hle : 1 ≤ 16 ^ (9 * q) := le_of_lt hgt
    have hdvd : 9 ∣ 16 ^ (9 * q) - 1 :=
      (Nat.modEq_iff_dvd' hle).mp (sixteen_pow_nine_mul_mod_nine q).symm
    have hnz : 16 ^ (9 * q) - 1 ≠ 0 := by omega
    have hsquare : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [hsquare] at hdvd
    have hvalnat : 2 ≤ padicValNat 3 (16 ^ (9 * q) - 1) :=
      (padicValNat_dvd_iff_le hnz).mp hdvd
    have hcast : ((16 ^ (9 * q) - 1 : ℕ) : ℚ) =
        (16 ^ (9 * q) : ℚ) - 1 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [← hcast, padicValRat.of_nat]
    exact_mod_cast hvalnat

/-- Powers `16 ^ (9 * q + 5)` are four modulo nine. -/
theorem sixteen_pow_mod_nine_aux (q : ℕ) :
    (16 : ℕ) ^ (9 * q + 5) % 9 = 4 := by
  have hkey : 9 * q + 5 = 3 * (3 * q + 1) + 2 := by omega
  have hpow3 : ∀ k : ℕ, ((16 : ℕ) ^ 3) ^ k % 9 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ, Nat.mul_mod, ih]
        norm_num
  rw [hkey, pow_add, pow_mul, Nat.mul_mod, hpow3]
  norm_num

/-- At a stable endpoint `M ≡ 4 (mod 9)`, the pole-one boundary term
`poleOne (M + 1)` is two modulo nine in the rational three-adic sense. -/
theorem poleOne_boundary_congr_two (M : ℕ) (hM : M % 9 = 4) :
    RatCongruentThree 2 (poleOne (M + 1)) 2 := by
  set D : ℕ := (8 * (M + 1) + 1) * 16 ^ (M + 1) with hD_def
  have hd : (8 * (M + 1) + 1) % 9 = 5 := by omega
  have hpow : (16 : ℕ) ^ (M + 1) % 9 = 4 := by
    have hkey : M + 1 = 9 * (M / 9) + 5 := by omega
    rw [hkey, sixteen_pow_mod_nine_aux]
  have hDres : D % 9 = 2 := by
    rw [hD_def, Nat.mul_mod, hd, hpow]
  have hDbig : 144 ≤ D := by
    rw [hD_def]
    have h1 : 9 ≤ 8 * (M + 1) + 1 := by omega
    have h2 : (16 : ℕ) ≤ 16 ^ (M + 1) := Nat.le_pow (by omega)
    have h3 := Nat.mul_le_mul h1 h2
    omega
  have hDne : D ≠ 0 := by omega
  have hrel : 2 * D = 9 * (2 * D / 9) + 4 := by
    have h4 : (2 * D) % 9 = 4 := by
      rw [Nat.mul_mod, hDres]
    have h := Nat.mod_add_div (2 * D) 9
    rw [h4] at h
    omega
  have hform : (poleOne (M + 1) : ℚ) - 2
      = 9 * (-(((2 * D / 9 : ℕ) : ℚ) / (D : ℚ))) := by
    rw [poleOne]
    have hDq : (D : ℚ) =
        (8 * ((M + 1 : ℕ) : ℚ) + 1) * (16 : ℚ) ^ (M + 1) := by
      rw [hD_def]
      push_cast
      norm_num
    rw [hDq]
    have hDqne : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
    have hcast : ((2 : ℚ) * (D : ℚ)) = 9 * (((2 * D / 9 : ℕ) : ℚ)) + 4 := by
      exact_mod_cast hrel
    field_simp
    linarith
  have hm : 0 < 2 * D / 9 := by omega
  have hD3 : D % 3 ≠ 0 := by omega
  have hvD : padicValNat 3 D = 0 :=
    padicValNat.eq_zero_of_not_dvd (by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact hD3)
  have hzne : (-(((2 * D / 9 : ℕ) : ℚ) / (D : ℚ))) ≠ 0 := by
    rw [neg_ne_zero]
    exact div_ne_zero (by exact_mod_cast (ne_of_gt hm)) (by exact_mod_cast hDne)
  unfold RatCongruentThree
  right
  rw [hform, padicValRat.mul (show (9 : ℚ) ≠ 0 by norm_num) hzne,
    Theory.PiDigits.T82SelectedPairedColumnModNine.padicValRat_three_nine]
  have hnn : (0 : ℤ) ≤ padicValRat 3 (-(((2 * D / 9 : ℕ) : ℚ) / (D : ℚ))) := by
    rw [padicValRat.neg,
      padicValRat.div (by exact_mod_cast (ne_of_gt hm)) (by exact_mod_cast hDne),
      padicValRat.of_nat, padicValRat.of_nat, hvD]
    simp
  omega

/-- At a stable endpoint `M ≡ 4 (mod 9)`, the pole-two boundary term
`poleTwo (M + 1)` is five modulo nine in the rational three-adic sense. -/
theorem poleTwo_boundary_congr_five (M : Nat) (hM : M % 9 = 4) :
    RatCongruentThree 2 (poleTwo (M + 1)) 5 := by
  have hdecomp : M = 9 * (M / 9) + 4 := by
    have h := Nat.mod_add_div M 9
    omega
  unfold RatCongruentThree
  right
  let q : ℕ := M / 9
  have hdecompq : M = 9 * q + 4 := by simpa [q] using hdecomp
  have h16nine : (16 : ℕ) ^ 9 % 9 = 1 := by norm_num
  have hpowmod : (16 : ℕ) ^ (M + 1) % 9 = 4 := by
    have hsplit : M + 1 = 5 + 9 * q := by rw [hdecompq]; omega
    have hexp : (16 : ℕ) ^ (M + 1) = 16 ^ 5 * (16 ^ 9) ^ q := by
      rw [hsplit, Nat.pow_add, Nat.pow_mul]
    have h1 : (16 : ℕ) ^ 5 % 9 = 4 := by norm_num
    have h2 : ((16 : ℕ) ^ 9) ^ q % 9 = 1 := by
      rw [Nat.pow_mod, h16nine, Nat.one_pow]
    rw [hexp, Nat.mul_mod, h1, h2]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 16 ^ (M + 1) = 9 * t + 4 := by
    refine ⟨(16 ^ (M + 1) - 4) / 9, ?_⟩
    have h1 := Nat.mod_add_div ((16 : ℕ) ^ (M + 1)) 9
    omega
  have hK : 10 * (2 * M + 3) * 16 ^ (M + 1) + 1
      = 9 * (80 * q + 49 + 10 * t * (2 * M + 3)) := by
    rw [ht]
    have hA : 2 * M + 3 = 18 * q + 11 := by rw [hdecompq]; omega
    rw [hA]
    ring
  have hNne : (10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ) ≠ 0 :=
    ne_of_gt (by positivity)
  have hDne : (2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) ≠ 0 :=
    ne_of_gt (by positivity)
  have hEne : ((16 ^ (M + 1) : ℕ) : ℚ) ≠ 0 := by
    have hEpos : (16 ^ (M + 1) : ℕ) ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast hEpos
  have hAne : ((2 * M + 3 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (show 2 * M + 3 ≠ 0 from by omega)
  have hNQne : (-(((10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ) : ℚ))) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast hNne)
  have hDQne : ((2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hDne
  have hNcast : (((10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ)) : ℚ)
      = (1 : ℚ) + 10 * ((2 * M + 3 : ℕ) : ℚ) * ((16 ^ (M + 1) : ℕ) : ℚ) := by
    push_cast
    ring
  have hDform : ((2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) : ℚ)
      = (2 : ℚ) * ((2 * M + 3 : ℕ) : ℚ) * ((16 ^ (M + 1) : ℕ) : ℚ) := by
    push_cast
    ring
  have hEform : ((16 ^ (M + 1) : ℕ) : ℚ) = (16 : ℚ) ^ (M + 1) := by
    rw [Nat.cast_pow]
    norm_num
  have hcast2 : (2 : ℚ) * ((M + 1 : ℕ) : ℚ) + 1 = ((2 * M + 3 : ℕ) : ℚ) := by
    push_cast
    ring
  have hrat : poleTwo (M + 1) - 5 =
      -(((10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ)) : ℚ) /
      ((2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) : ℚ) := by
    simp only [poleTwo]
    rw [hcast2, ← hEform, hNcast, hDform]
    field_simp
    ring
  rw [hrat, padicValRat.div hNQne hDQne, padicValRat.neg,
    padicValRat.of_nat, padicValRat.of_nat]
  have hNdvd : (3 : ℕ) ^ 2 ∣ (10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ) := by
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9]
    exact ⟨80 * q + 49 + 10 * t * (2 * M + 3), hK⟩
  have hNval : 2 ≤ padicValNat 3 (10 * (2 * M + 3) * 16 ^ (M + 1) + 1 : ℕ) :=
    (padicValNat_dvd_iff_le hNne).mp hNdvd
  have hDmod : (2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) % 3 = 1 := by
    have hA2 : (2 * (2 * M + 3)) % 3 = 1 := by omega
    have h16 : ((16 : ℕ) ^ (M + 1)) % 3 = 1 := by
      rw [Nat.pow_mod, show (16 : ℕ) % 3 = 1 from by norm_num, Nat.one_pow]
    rw [Nat.mul_mod, hA2, h16]
  have hDzero : padicValNat 3 (2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) = 0 := by
    by_contra hc
    have h1le : 1 ≤ padicValNat 3 (2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) := by omega
    have hdvd : (3 : ℕ) ∣ (2 * (2 * M + 3) * 16 ^ (M + 1) : ℕ) := by
      have h := (padicValNat_dvd_iff_le hDne).mpr h1le
      rwa [pow_one] at h
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    omega
  omega

/-- The two regular boundary terms at the selected depth of a positive even
half-epoch sum to seven modulo nine in the rational three-adic sense. -/
theorem regularBoundary_congr_seven_at_selectedDepth (t : Nat) (ht : 1 <= t) :
    RatCongruentThree 2
      (poleOne (selectedDepth (2 * t) + 1) + poleTwo (selectedDepth (2 * t) + 1)) 7 := by
  have hM : selectedDepth (2 * t) % 9 = 4 :=
    selectedDepth_mod_nine_of_twice t ht
  have h1 := poleOne_boundary_congr_two (selectedDepth (2 * t)) hM
  have h2 := poleTwo_boundary_congr_five (selectedDepth (2 * t)) hM
  have h := ratCongruentThree_add h1 h2
  rwa [show ((2 : ℚ) + 5) = 7 by norm_num] at h

end Theory.PiDigits.T83RegularBoundaryRationalResidues

#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.ratCongruentThree_sixteen_pow_nine_one
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.sixteen_pow_nine_mod_nine
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.sixteen_pow_nine_mul_mod_nine
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.sixteen_pow_mod_nine_aux
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.poleOne_boundary_congr_two
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.poleTwo_boundary_congr_five
#print axioms Theory.PiDigits.T83RegularBoundaryRationalResidues.regularBoundary_congr_seven_at_selectedDepth
