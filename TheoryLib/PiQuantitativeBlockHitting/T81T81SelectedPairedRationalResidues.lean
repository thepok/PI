import TheoryLib.PiQuantitativeBlockHitting.T80T80SelectedPairedQuotientFactorization

/-!
# T81: rational residues of the selected paired errors

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module transports T79's uniform quotient congruence through T80's four
exact paired-error factorizations.  It does not perform the later scaling to
modulo nine or claim SP1.
-/

namespace Theory.PiDigits.T81SelectedPairedRationalResidues

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence T79UniformCancelledQuotient
  T80SelectedPairedQuotientFactorization

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Every rational power of sixteen is a three-adic unit. -/
theorem padicValRat_three_sixteen_pow (n : ℕ) :
    padicValRat 3 ((16 : ℚ) ^ n) = 0 := by
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have hunit : padicValRat 3 (16 : ℚ) = 0 := by
    have hcast : (16 : ℚ) = ((16 : ℕ) : ℚ) := by norm_cast
    rw [hcast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 16) (by decide)]
    rfl
  rw [padicValRat.pow h16, hunit, mul_zero]

/-- The constant `-20` is one modulo three. -/
theorem constant_neg_twenty_congr_one : RatCongruentThree 1 (-20 : ℚ) 1 := by
  unfold RatCongruentThree
  refine Or.inr ?_
  have hsub : (-20 : ℚ) - 1 = -21 := by norm_num
  rw [hsub, padicValRat.neg]
  have hcast : (21 : ℚ) = ((21 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat]
  have hsplit : (21 : ℕ) = 3 * 7 := by norm_num
  have hunit : ¬ (3 : ℕ) ∣ 7 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num
  rw [hsplit, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self (p := 3), padicValNat.eq_zero_of_not_dvd hunit]

/-- The constant `10` is one modulo three. -/
theorem constant_ten_congr_one : RatCongruentThree 1 (10 : ℚ) 1 := by
  unfold RatCongruentThree
  refine Or.inr ?_
  have hsub : (10 : ℚ) - 1 = 9 := by norm_num
  rw [hsub]
  have hcast : (9 : ℚ) = ((9 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat]
  have hsplit : (9 : ℕ) = 3 * 3 := by norm_num
  rw [hsplit, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self (p := 3)]
  norm_num

/-- The constant `5` is two modulo three. -/
theorem constant_five_congr_two : RatCongruentThree 1 (5 : ℚ) 2 := by
  unfold RatCongruentThree
  refine Or.inr ?_
  have hsub : (5 : ℚ) - 2 = 3 := by norm_num
  rw [hsub]
  have hcast : (3 : ℚ) = ((3 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat, padicValNat_self (p := 3)]

/-- Every power of sixteen is one modulo three. -/
theorem ratCongruentThree_sixteen_pow_one (n : ℕ) :
    RatCongruentThree 1 ((16 : ℚ) ^ n) 1 := by
  cases n with
  | zero => norm_num [ratCongruentThree_refl]
  | succ n =>
    have hn : 1 ≤ n + 1 := by omega
    have hq := binomialQuotient_three_unit_and_congruent_one (n + 1) hn
    have hqne : binomialQuotient (n + 1) ≠ 0 := by
      unfold binomialQuotient
      apply div_ne_zero
      · have hpow : (1 : ℚ) < 16 ^ (n + 1) := by
          have hbase : (1 : ℚ) < 16 := by norm_num
          exact one_lt_pow₀ hbase (by omega)
        linarith
      · positivity
    unfold RatCongruentThree
    right
    have hfactor : ((16 : ℚ) ^ (n + 1) - 1) =
        (15 : ℚ) * ((n : ℚ) + 1) * binomialQuotient (n + 1) := by
      rw [binomialQuotient, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hfactor]
    have h15 : padicValRat 3 (15 : ℚ) = 1 := padicValRat_three_fifteen
    have hnatne : (n : ℚ) + 1 ≠ 0 := by positivity
    have hprodne : (15 : ℚ) * (n + 1) ≠ 0 := mul_ne_zero (by norm_num) hnatne
    have h15n : padicValRat 3 ((15 : ℚ) * ((n : ℚ) + 1)) =
        1 + padicValRat 3 ((n : ℚ) + 1) := by
      rw [padicValRat.mul (by norm_num) hnatne, h15]
    rw [padicValRat.mul hprodne hqne, h15n, hq.1]
    have hnonneg : 0 ≤ padicValRat 3 ((n : ℚ) + 1) := by
      rw [show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by push_cast; norm_num,
        padicValRat.of_nat]
      exact_mod_cast Nat.zero_le _
    omega

/-- The reciprocal of every power of sixteen is one modulo three. -/
theorem ratCongruentThree_sixteen_pow_inv_one (n : ℕ) :
    RatCongruentThree 1 (((16 : ℚ) ^ n)⁻¹) 1 := by
  have hpowne : (16 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowval : padicValRat 3 ((16 : ℚ) ^ n) = 0 :=
    padicValRat_three_sixteen_pow n
  have hinvne : ((16 : ℚ) ^ n)⁻¹ ≠ 0 := inv_ne_zero hpowne
  have hinvval : padicValRat 3 (((16 : ℚ) ^ n)⁻¹) = 0 := by
    rw [padicValRat.inv, hpowval]
    norm_num
  have h := ratCongruentThree_mul_unit hinvne hinvval
    (ratCongruentThree_sixteen_pow_one n)
  have h' : RatCongruentThree 1 1 (((16 : ℚ) ^ n)⁻¹) := by
    simpa [inv_mul_cancel₀ hpowne] using h
  exact ratCongruentThree_symm h'

/-- The constant `-20` is a three-adic unit. -/
theorem padicValRat_three_neg_twenty : padicValRat 3 (-20 : ℚ) = 0 := by
  rw [padicValRat.neg]
  have hcast : (20 : ℚ) = ((20 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := 20) (by decide)]
  rfl

/-- The constant `10` is a three-adic unit. -/
theorem padicValRat_three_ten : padicValRat 3 (10 : ℚ) = 0 := by
  have hcast : (10 : ℚ) = ((10 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := 10) (by decide)]
  rfl

/-- The constant `5` is a three-adic unit. -/
theorem padicValRat_three_five : padicValRat 3 (5 : ℚ) = 0 := by
  have hcast : (5 : ℚ) = ((5 : ℕ) : ℚ) := by norm_cast
  rw [hcast, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := 5) (by decide)]
  rfl

/-- The first T80 multiplier is one modulo three. -/
theorem poleOne_multiplier_congr_one (r : ℕ) :
    RatCongruentThree 1 ((-20 : ℚ) / 16 ^ (9 * r + 1)) 1 := by
  have h := ratCongruentThree_mul_unit (u := (-20 : ℚ)) (by norm_num)
    padicValRat_three_neg_twenty
    (ratCongruentThree_sixteen_pow_inv_one (9 * r + 1))
  have h' : RatCongruentThree 1 ((-20 : ℚ) / 16 ^ (9 * r + 1)) (-20 : ℚ) := by
    simpa [div_eq_mul_inv] using h
  exact ratCongruentThree_trans h' constant_neg_twenty_congr_one

/-- The second T80 multiplier is one modulo three. -/
theorem poleTwo_multiplier_congr_one (r : ℕ) :
    RatCongruentThree 1 ((10 : ℚ) / 16 ^ (9 * r + 4)) 1 := by
  have h := ratCongruentThree_mul_unit (u := (10 : ℚ)) (by norm_num)
    padicValRat_three_ten
    (ratCongruentThree_sixteen_pow_inv_one (9 * r + 4))
  have h' : RatCongruentThree 1 ((10 : ℚ) / 16 ^ (9 * r + 4)) (10 : ℚ) := by
    simpa [div_eq_mul_inv] using h
  exact ratCongruentThree_trans h' constant_ten_congr_one

/-- The third T80 multiplier is two modulo three. -/
theorem poleThree_multiplier_congr_two (r : ℕ) :
    RatCongruentThree 1 ((5 : ℚ) / 16 ^ (9 * r + 5)) 2 := by
  have h := ratCongruentThree_mul_unit (u := (5 : ℚ)) (by norm_num)
    padicValRat_three_five
    (ratCongruentThree_sixteen_pow_inv_one (9 * r + 5))
  have h' : RatCongruentThree 1 ((5 : ℚ) / 16 ^ (9 * r + 5)) (5 : ℚ) := by
    simpa [div_eq_mul_inv] using h
  exact ratCongruentThree_trans h' constant_five_congr_two

/-- The fourth T80 multiplier is two modulo three. -/
theorem poleFour_multiplier_congr_two (r : ℕ) :
    RatCongruentThree 1 ((5 : ℚ) / 16 ^ (9 * r + 6)) 2 := by
  have h := ratCongruentThree_mul_unit (u := (5 : ℚ)) (by norm_num)
    padicValRat_three_five
    (ratCongruentThree_sixteen_pow_inv_one (9 * r + 6))
  have h' : RatCongruentThree 1 ((5 : ℚ) / 16 ^ (9 * r + 6)) (5 : ℚ) := by
    simpa [div_eq_mul_inv] using h
  exact ratCongruentThree_trans h' constant_five_congr_two

/-- The pole-one selected paired error, after division by three, is one modulo
three. -/
theorem pairedError_poleOne_div_three_congr_one (r : ℕ) :
    RatCongruentThree 1 (pairedError poleOne 1 r / 3) 1 := by
  let u : ℚ := (-20 : ℚ) / 16 ^ (9 * r + 1)
  have hune : u ≠ 0 := by
    dsimp [u]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have huval : padicValRat 3 u = 0 := by
    dsimp [u]
    rw [padicValRat.div (by norm_num) (pow_ne_zero _ (by norm_num)),
      padicValRat_three_neg_twenty, padicValRat_three_sixteen_pow]
    norm_num
  have hq := binomialQuotient_three_unit_and_congruent_one (8 * r + 1) (by omega)
  have htransport : RatCongruentThree 1 (u * binomialQuotient (8 * r + 1)) u := by
    simpa using ratCongruentThree_mul_unit hune huval hq.2
  rw [pairedError_poleOne_factor]
  exact ratCongruentThree_trans htransport (poleOne_multiplier_congr_one r)

/-- The pole-two selected paired error, after division by three, is one modulo
three. -/
theorem pairedError_poleTwo_div_three_congr_one (r : ℕ) :
    RatCongruentThree 1 (pairedError poleTwo 4 r / 3) 1 := by
  let u : ℚ := (10 : ℚ) / 16 ^ (9 * r + 4)
  have hune : u ≠ 0 := by
    dsimp [u]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have huval : padicValRat 3 u = 0 := by
    dsimp [u]
    rw [padicValRat.div (by norm_num) (pow_ne_zero _ (by norm_num)),
      padicValRat_three_ten, padicValRat_three_sixteen_pow]
    norm_num
  have hq := binomialQuotient_three_unit_and_congruent_one (8 * r + 4) (by omega)
  have htransport : RatCongruentThree 1 (u * binomialQuotient (8 * r + 4)) u := by
    simpa using ratCongruentThree_mul_unit hune huval hq.2
  rw [pairedError_poleTwo_factor]
  exact ratCongruentThree_trans htransport (poleTwo_multiplier_congr_one r)

/-- The pole-three selected paired error, after division by three, is two
modulo three. -/
theorem pairedError_poleThree_div_three_congr_two (r : ℕ) :
    RatCongruentThree 1 (pairedError poleThree 5 r / 3) 2 := by
  let u : ℚ := (5 : ℚ) / 16 ^ (9 * r + 5)
  have hune : u ≠ 0 := by
    dsimp [u]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have huval : padicValRat 3 u = 0 := by
    dsimp [u]
    rw [padicValRat.div (by norm_num) (pow_ne_zero _ (by norm_num)),
      padicValRat_three_five, padicValRat_three_sixteen_pow]
    norm_num
  have hq := binomialQuotient_three_unit_and_congruent_one (8 * r + 5) (by omega)
  have htransport : RatCongruentThree 1 (u * binomialQuotient (8 * r + 5)) u := by
    simpa using ratCongruentThree_mul_unit hune huval hq.2
  rw [pairedError_poleThree_factor]
  exact ratCongruentThree_trans htransport (poleThree_multiplier_congr_two r)

/-- The pole-four selected paired error, after division by three, is two
modulo three. -/
theorem pairedError_poleFour_div_three_congr_two (r : ℕ) :
    RatCongruentThree 1 (pairedError poleFour 6 r / 3) 2 := by
  let u : ℚ := (5 : ℚ) / 16 ^ (9 * r + 6)
  have hune : u ≠ 0 := by
    dsimp [u]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have huval : padicValRat 3 u = 0 := by
    dsimp [u]
    rw [padicValRat.div (by norm_num) (pow_ne_zero _ (by norm_num)),
      padicValRat_three_five, padicValRat_three_sixteen_pow]
    norm_num
  have hq := binomialQuotient_three_unit_and_congruent_one (8 * r + 6) (by omega)
  have htransport : RatCongruentThree 1 (u * binomialQuotient (8 * r + 6)) u := by
    simpa using ratCongruentThree_mul_unit hune huval hq.2
  rw [pairedError_poleFour_factor]
  exact ratCongruentThree_trans htransport (poleFour_multiplier_congr_two r)

end Theory.PiDigits.T81SelectedPairedRationalResidues

#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.padicValRat_three_sixteen_pow
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.constant_neg_twenty_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.constant_ten_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.constant_five_congr_two
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.ratCongruentThree_sixteen_pow_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.ratCongruentThree_sixteen_pow_inv_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.padicValRat_three_neg_twenty
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.padicValRat_three_ten
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.padicValRat_three_five
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.poleOne_multiplier_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.poleTwo_multiplier_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.poleThree_multiplier_congr_two
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.poleFour_multiplier_congr_two
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.pairedError_poleOne_div_three_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.pairedError_poleTwo_div_three_congr_one
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.pairedError_poleThree_div_three_congr_two
#print axioms Theory.PiDigits.T81SelectedPairedRationalResidues.pairedError_poleFour_div_three_congr_two
