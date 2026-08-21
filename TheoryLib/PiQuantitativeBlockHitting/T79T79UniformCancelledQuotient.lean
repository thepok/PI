import TheoryLib.PiQuantitativeBlockHitting.T78T78SelectedPadicDefectCongruence

/-!
# T79: the uniform cancelled binomial quotient

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For positive `t`, this module proves that T78's cancelled quotient
`((16^t - 1) / (15*t))` is a three-adic unit congruent to one modulo three.
-/

namespace Theory.PiDigits.T79UniformCancelledQuotient

open T78SelectedPadicDefectCongruence

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The natural-number valuation of fifteen. -/
lemma padicValNat_three_fifteen : padicValNat 3 15 = 1 := by
  have h5 : padicValNat 3 5 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h3 : padicValNat 3 3 = 1 := by
    simpa using padicValNat.prime_pow (p := 3) (n := 1)
  have h : padicValNat 3 (3 * 5) = padicValNat 3 3 + padicValNat 3 5 :=
    padicValNat.mul (by norm_num) (by norm_num)
  rw [show (15 : ℕ) = 3 * 5 by norm_num, h, h3, h5]

/-- The cancelled-binomial valuation bound. -/
lemma padicValNat_choose_ge {t k : ℕ} (hk1 : 1 ≤ k) (hkt : k ≤ t) :
    padicValNat 3 t - padicValNat 3 k ≤ padicValNat 3 (Nat.choose t k) := by
  have hId : t * Nat.choose (t - 1) (k - 1) = Nat.choose t k * k := by
    have h := Nat.add_one_mul_choose_eq (t - 1) (k - 1)
    rwa [show t - 1 + 1 = t by omega, show k - 1 + 1 = k by omega] at h
  have hCne : Nat.choose (t - 1) (k - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h1 : padicValNat 3 (t * Nat.choose (t - 1) (k - 1)) =
      padicValNat 3 t + padicValNat 3 (Nat.choose (t - 1) (k - 1)) :=
    padicValNat.mul (by omega) hCne
  have h2 : padicValNat 3 (Nat.choose t k * k) =
      padicValNat 3 (Nat.choose t k) + padicValNat 3 k :=
    padicValNat.mul (Nat.choose_pos hkt).ne' (by omega)
  rw [hId] at h1
  omega

/-- Every nonconstant binomial term has the needed three-power factor. -/
lemma three_pow_dvd_choose_mul_fifteen_pow {t k : ℕ} (hk2 : 2 ≤ k) (hkt : k ≤ t) :
    (3 : ℕ) ^ (2 + padicValNat 3 t) ∣ Nat.choose t k * 15 ^ k := by
  have hCpos : Nat.choose t k ≠ 0 := (Nat.choose_pos hkt).ne'
  have hC : (3 : ℕ) ^ (padicValNat 3 t - padicValNat 3 k) ∣ Nat.choose t k :=
    (padicValNat_dvd_iff_le hCpos).mpr (padicValNat_choose_ge (by omega) hkt)
  have hle : 2 + padicValNat 3 t ≤ padicValNat 3 t - padicValNat 3 k + k := by
    have hk := padicValNat_three_le_sub_two hk2
    omega
  have hpow : (3 : ℕ) ^ (padicValNat 3 t - padicValNat 3 k + k) ∣
      Nat.choose t k * 3 ^ k := by
    rw [pow_add]
    exact mul_dvd_mul_right hC (3 ^ k)
  calc
    (3 : ℕ) ^ (2 + padicValNat 3 t) ∣
        (3 : ℕ) ^ (padicValNat 3 t - padicValNat 3 k + k) := pow_dvd_pow 3 hle
    _ ∣ Nat.choose t k * 3 ^ k := hpow
    _ ∣ Nat.choose t k * (3 ^ k * 5 ^ k) := mul_dvd_mul_left _ (by simp)
    _ = Nat.choose t k * 15 ^ k := by rw [← Nat.mul_pow]

/-- The binomial remainder after removing its constant and linear terms. -/
lemma three_pow_dvd_sixteen_pow_sub (t : ℕ) (ht : 2 ≤ t) :
    (3 : ℕ) ^ (2 + padicValNat 3 t) ∣ 16 ^ t - 1 - 15 * t := by
  have hbin : (16 : ℕ) ^ t =
      ∑ m ∈ Finset.range (t + 1), 15 ^ m * 1 ^ (t - m) * Nat.choose t m :=
    add_pow 15 1 t
  have hsplit : ∑ m ∈ Finset.range (t + 1), 15 ^ m * 1 ^ (t - m) * Nat.choose t m =
      1 + 15 * t + ∑ m ∈ Finset.range (t - 1),
        15 ^ (2 + m) * 1 ^ (t - (2 + m)) * Nat.choose t (2 + m) := by
    have h2 : t + 1 = 2 + (t - 1) := by omega
    rw [h2, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp [Nat.choose_one_right]
  have hexpr : (16 : ℕ) ^ t - 1 - 15 * t =
      ∑ m ∈ Finset.range (t - 1),
        15 ^ (2 + m) * 1 ^ (t - (2 + m)) * Nat.choose t (2 + m) := by
    omega
  rw [hexpr]
  refine Finset.dvd_sum fun m hm => ?_
  have hm1 : m < t - 1 := Finset.mem_range.mp hm
  rw [Nat.one_pow, mul_one, mul_comm (15 ^ (2 + m)) (Nat.choose t (2 + m))]
  exact three_pow_dvd_choose_mul_fifteen_pow (by omega) (by omega)

/-- The positivity estimate used to avoid truncated-subtraction degeneracies. -/
lemma fifteen_mul_lt_sixteen_pow : ∀ t : ℕ, 2 ≤ t → 15 * t + 1 < 16 ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · omega
      · norm_num
    · have h1 := ih hn2
      calc
        15 * (n + 1) + 1 = 15 * n + 16 := by ring
        _ < 16 * (15 * n + 1) := by omega
        _ < 16 * 16 ^ n := mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 16 ^ (n + 1) := by rw [mul_comm, pow_succ]

/-- The exact three-adic valuation of the numerator of the quotient. -/
lemma padicValNat_sixteen_pow_sub_one (t : ℕ) (ht : 2 ≤ t) :
    padicValNat 3 (16 ^ t - 1) = 1 + padicValNat 3 t := by
  have hDne : 16 ^ t - 1 - 15 * t ≠ 0 := by
    have h := fifteen_mul_lt_sixteen_pow t ht
    omega
  have hsum : 16 ^ t - 1 = 15 * t + (16 ^ t - 1 - 15 * t) := by omega
  have hvD : 2 + padicValNat 3 t ≤ padicValNat 3 (16 ^ t - 1 - 15 * t) :=
    (padicValNat_dvd_iff_le hDne).mp (three_pow_dvd_sixteen_pow_sub t ht)
  have hfif : padicValNat 3 (15 * t) = 1 + padicValNat 3 t := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_three_fifteen]
  have hdvdD : (3 : ℕ) ^ (1 + padicValNat 3 t) ∣ 16 ^ t - 1 - 15 * t :=
    (pow_dvd_pow 3 (by omega)).trans (three_pow_dvd_sixteen_pow_sub t ht)
  have hdvd15 : (3 : ℕ) ^ (1 + padicValNat 3 t) ∣ 15 * t :=
    (padicValNat_dvd_iff_le (by omega : (15 : ℕ) * t ≠ 0)).mpr (by omega)
  have hne1 : 16 ^ t - 1 ≠ 0 := by
    have h := fifteen_mul_lt_sixteen_pow t ht
    omega
  have hle : 1 + padicValNat 3 t ≤ padicValNat 3 (16 ^ t - 1) := by
    rw [← padicValNat_dvd_iff_le hne1, hsum]
    exact Nat.dvd_add hdvd15 hdvdD
  have hge : padicValNat 3 (16 ^ t - 1) ≤ 1 + padicValNat 3 t := by
    by_contra hcon
    have hcon2 : 2 + padicValNat 3 t ≤ padicValNat 3 (16 ^ t - 1) := by omega
    have hdvd : (3 : ℕ) ^ (2 + padicValNat 3 t) ∣ 16 ^ t - 1 :=
      (padicValNat_dvd_iff_le hne1).mpr hcon2
    have hdvdsum : (3 : ℕ) ^ (2 + padicValNat 3 t) ∣
        15 * t + (16 ^ t - 1 - 15 * t) := by
      rw [← hsum]
      exact hdvd
    have hsub : (3 : ℕ) ^ (2 + padicValNat 3 t) ∣ 15 * t :=
      (Nat.dvd_add_left (three_pow_dvd_sixteen_pow_sub t ht)).mp hdvdsum
    have hv15 : 2 + padicValNat 3 t ≤ padicValNat 3 (15 * t) :=
      (padicValNat_dvd_iff_le (by omega : (15 : ℕ) * t ≠ 0)).mp hsub
    rw [hfif] at hv15
    omega
  omega

/-- The valuation of a quotient of nonzero natural-number casts. -/
lemma padicValRat_nat_cast_div_nat_cast {p : ℕ} [Fact (Nat.Prime p)] {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValRat p ((m : ℚ) / (n : ℚ)) =
      (padicValNat p m : ℤ) - (padicValNat p n : ℤ) := by
  rw [padicValRat.div (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn),
    padicValRat_of_nat, padicValRat_of_nat]

/-- For positive indices, the cancelled binomial quotient is a three-adic unit
and is congruent to one modulo three. -/
theorem binomialQuotient_three_unit_and_congruent_one (t : ℕ) (ht : 1 ≤ t) :
    padicValRat 3 (binomialQuotient t) = 0 ∧
      RatCongruentThree 1 (binomialQuotient t) 1 := by
  rcases Nat.eq_or_lt_of_le ht with rfl | ht1
  · have hq : binomialQuotient 1 = 1 := by norm_num [binomialQuotient]
    exact ⟨by rw [hq]; exact padicValRat.one, Or.inl hq⟩
  · have ht2 : 2 ≤ t := ht1
    have hflt : 15 * t + 1 < 16 ^ t := fifteen_mul_lt_sixteen_pow t ht2
    have hpow16 : (1 : ℕ) ≤ 16 ^ t := by
      omega
    have hcastnum : ((16 : ℚ) ^ t - 1) = ((16 ^ t - 1 : ℕ) : ℚ) := by
      rw [← Nat.cast_ofNat, ← Nat.cast_pow, Nat.cast_sub hpow16]
      norm_num
    have hden : ((15 : ℚ) * (t : ℚ)) = ((15 * t : ℕ) : ℚ) := by
      push_cast
      rfl
    have hnumnat : (16 ^ t - 1 : ℕ) ≠ 0 := by
      have h := fifteen_mul_lt_sixteen_pow t ht2
      omega
    have hdennat : (15 * t : ℕ) ≠ 0 := by omega
    have hval16 : padicValNat 3 (16 ^ t - 1) = 1 + padicValNat 3 t :=
      padicValNat_sixteen_pow_sub_one t ht2
    have hfif : padicValNat 3 (15 * t) = 1 + padicValNat 3 t := by
      rw [padicValNat.mul (by norm_num) (by omega), padicValNat_three_fifteen]
    have hunit : padicValRat 3 (binomialQuotient t) = 0 := by
      rw [binomialQuotient, hcastnum, hden,
        padicValRat_nat_cast_div_nat_cast hnumnat hdennat]
      omega
    have hAB : ((16 : ℚ) ^ t - 1) - ((15 * t : ℕ) : ℚ) =
        ((16 ^ t - 1 - 15 * t : ℕ) : ℚ) := by
      rw [hcastnum, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        Nat.cast_sub hpow16]
    have hDne : (16 ^ t - 1 - 15 * t : ℕ) ≠ 0 := by
      have h := fifteen_mul_lt_sixteen_pow t ht2
      omega
    have hquotient : binomialQuotient t - 1 =
        ((16 ^ t - 1 - 15 * t : ℕ) : ℚ) / ((15 * t : ℕ) : ℚ) := by
      rw [binomialQuotient, hden]
      field_simp [hAB]
      exact hAB
    refine ⟨hunit, Or.inr ?_⟩
    rw [show binomialQuotient t - 1 =
        ((16 ^ t - 1 - 15 * t : ℕ) : ℚ) / ((15 * t : ℕ) : ℚ) from hquotient,
      padicValRat_nat_cast_div_nat_cast hDne hdennat]
    have hvD : 2 + padicValNat 3 t ≤ padicValNat 3 (16 ^ t - 1 - 15 * t) :=
      (padicValNat_dvd_iff_le hDne).mp (three_pow_dvd_sixteen_pow_sub t ht2)
    omega

end Theory.PiDigits.T79UniformCancelledQuotient

#print axioms Theory.PiDigits.T79UniformCancelledQuotient.padicValNat_three_fifteen
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.padicValNat_choose_ge
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.three_pow_dvd_choose_mul_fifteen_pow
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.three_pow_dvd_sixteen_pow_sub
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.fifteen_mul_lt_sixteen_pow
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.padicValNat_sixteen_pow_sub_one
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.padicValRat_nat_cast_div_nat_cast
#print axioms Theory.PiDigits.T79UniformCancelledQuotient.binomialQuotient_three_unit_and_congruent_one
