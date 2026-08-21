import TheoryLib.PiQuantitativeBlockHitting.T88T88SelectedDepthDenominatorValuations

/-!
# T89: selected-depth scaled integrality infrastructure

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module begins the finite rational three-adic integrality layer needed for
scaled BBP partial sums.  It records only a generic finite-sum valuation
closure lemma.  It makes no assertion about scaled BBP sums themselves, a
hidden carry, a decimal expansion, canonical V1, or an SP1 resolution.
-/

namespace Theory.PiDigits.T89SelectedDepthScaledIntegrality

open scoped BigOperators

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell

/-- A finite sum of three-adically integral rationals remains
three-adically integral, including when a summand or the whole sum is zero. -/
theorem padicValRat_three_finset_sum_nonneg {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℚ)
    (hf : ∀ x ∈ S, 0 ≤ padicValRat 3 (f x)) :
    0 ≤ padicValRat 3 (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, padicValRat.zero]
      norm_num
  | insert a S haS ih =>
      have hmem : ∀ x ∈ S, 0 ≤ padicValRat 3 (f x) :=
        fun x hx => hf x (Finset.mem_insert_of_mem hx)
      have h1 := ih hmem
      have h2 : 0 ≤ padicValRat 3 (f a) := hf a (Finset.mem_insert_self a S)
      rw [Finset.sum_insert haS]
      by_cases hzs : f a + ∑ x ∈ S, f x = 0
      · rw [hzs, padicValRat.zero]
      · have hmin := padicValRat.min_le_padicValRat_add (p := 3) hzs
        exact le_trans (le_min h2 h1) hmin

/-- Multiplication by a natural power of three distributes over the four
inclusive pole sums defining a BBP partial sum. -/
theorem scaled_bbpPartial_eq_scaled_pole_sums (e M : ℕ) :
    ((3 : ℚ) ^ e) * bbpPartial M
        = (∑ k ∈ Finset.range (M + 1), ((3 : ℚ) ^ e) * poleOne k)
        + (∑ k ∈ Finset.range (M + 1), ((3 : ℚ) ^ e) * poleTwo k)
        + (∑ k ∈ Finset.range (M + 1), ((3 : ℚ) ^ e) * poleThree k)
        + (∑ k ∈ Finset.range (M + 1), ((3 : ℚ) ^ e) * poleFour k) := by
  simp only [bbpPartial, polePartial]
  rw [mul_add, mul_add, mul_add]
  simp only [Finset.mul_sum]

/-- Scaling the third BBP pole by `3 ^ e` yields a three-adic integer whenever
`e` dominates the three-adic valuation of its linear denominator. -/
theorem poleThree_scaled_padicVal_nonneg_of_denominator_bound (e k : ℕ)
    (hden : padicValNat 3 (8 * k + 5) ≤ e) :
    0 ≤ padicValRat 3 ((3 : ℚ) ^ e * poleThree k) := by
  have h3ne : ((3 : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnatne : (8 * k + 5 : ℕ) ≠ 0 := by omega
  have hcastne : ((8 * k + 5 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnatne
  have h16ne : ((16 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hthreepow : padicValRat 3 ((3 : ℚ) ^ e) = e := by
    have hcast : ((3 : ℚ) ^ e) = ((3 ^ e : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast, padicValRat.of_nat, padicValNat.pow _ (by omega),
      padicValNat_self (p := 3)]
    norm_num
  have hexpr : ((3 : ℚ) ^ e * poleThree k) =
      -(((3 : ℚ) ^ e) / (((8 : ℚ) * k + 5) * ((16 : ℚ) ^ k))) := by
    simp only [poleThree]
    field_simp
  have hdenom : ((8 : ℚ) * k + 5) = ((8 * k + 5 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hexpr, hdenom, padicValRat.neg,
    padicValRat.div h3ne (mul_ne_zero hcastne h16ne),
    padicValRat.mul hcastne h16ne,
    padicValRat.of_nat,
    T81SelectedPairedRationalResidues.padicValRat_three_sixteen_pow k,
    hthreepow]
  omega

/-- Scaling the first BBP pole by `3 ^ e` yields a three-adic integer whenever
`e` dominates the three-adic valuation of its linear denominator. -/
theorem poleOne_scaled_padicVal_nonneg_of_denominator_bound (e k : ℕ)
    (hden : padicValNat 3 (8 * k + 1) ≤ e) :
    0 ≤ padicValRat 3 ((3 : ℚ) ^ e * poleOne k) := by
  have h3ne : ((3 : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnatne : (8 * k + 1 : ℕ) ≠ 0 := by omega
  have hcastne : ((8 * k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnatne
  have h16ne : ((16 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfour : padicValRat 3 (4 : ℚ) = 0 := by
    have hcast : (4 : ℚ) = ((4 : ℕ) : ℚ) := by norm_cast
    rw [hcast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 4) (by decide)]
    rfl
  have hthreepow : padicValRat 3 ((3 : ℚ) ^ e) = e := by
    have hcast : ((3 : ℚ) ^ e) = ((3 ^ e : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast, padicValRat.of_nat, padicValNat.pow _ (by omega),
      padicValNat_self (p := 3)]
    norm_num
  have hexpr : ((3 : ℚ) ^ e * poleOne k) =
      (((3 : ℚ) ^ e) * 4) / (((8 : ℚ) * k + 1) * ((16 : ℚ) ^ k)) := by
    simp only [poleOne]
    field_simp
  have hdenom : ((8 : ℚ) * k + 1) = ((8 * k + 1 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hexpr, hdenom,
    padicValRat.div (mul_ne_zero h3ne (by norm_num)) (mul_ne_zero hcastne h16ne),
    padicValRat.mul h3ne (by norm_num), hthreepow, hfour,
    padicValRat.mul hcastne h16ne,
    padicValRat.of_nat,
    T81SelectedPairedRationalResidues.padicValRat_three_sixteen_pow k]
  omega

/-- Scaling the second BBP pole by `3 ^ e` yields a three-adic integer whenever
`e` dominates the three-adic valuation of its linear denominator. -/
theorem poleTwo_scaled_padicVal_nonneg_of_denominator_bound (e k : ℕ)
    (hden : padicValNat 3 (2 * k + 1) ≤ e) :
    0 ≤ padicValRat 3 ((3 : ℚ) ^ e * poleTwo k) := by
  have h3ne : ((3 : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hnatne : (2 * k + 1 : ℕ) ≠ 0 := by omega
  have hcastne : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnatne
  have h16ne : ((16 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwoVal : padicValRat 3 (2 : ℚ) = 0 := by
    have hcast : (2 : ℚ) = ((2 : ℕ) : ℚ) := by norm_cast
    rw [hcast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by decide)]
    rfl
  have hthreepow : padicValRat 3 ((3 : ℚ) ^ e) = e := by
    have hcast : ((3 : ℚ) ^ e) = ((3 ^ e : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast, padicValRat.of_nat, padicValNat.pow _ (by omega),
      padicValNat_self (p := 3)]
    norm_num
  have hexpr : ((3 : ℚ) ^ e * poleTwo k) =
      -((3 : ℚ) ^ e) / ((2 : ℚ) * (((2 : ℚ) * k + 1) * ((16 : ℚ) ^ k))) := by
    simp only [poleTwo]
    field_simp
  have hdenom : ((2 : ℚ) * k + 1) = ((2 * k + 1 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hexpr, hdenom,
    padicValRat.div (neg_ne_zero.mpr h3ne)
      (mul_ne_zero htwo (mul_ne_zero hcastne h16ne)), padicValRat.neg,
    padicValRat.mul htwo (mul_ne_zero hcastne h16ne), htwoVal,
    padicValRat.mul hcastne h16ne, padicValRat.of_nat,
    T81SelectedPairedRationalResidues.padicValRat_three_sixteen_pow k,
    hthreepow]
  omega

/-- Scaling the fourth BBP pole by `3 ^ e` yields a three-adic integer whenever
`e` dominates the three-adic valuation of its linear denominator. -/
theorem poleFour_scaled_padicVal_nonneg_of_denominator_bound (e k : ℕ)
    (hden : padicValNat 3 (4 * k + 3) ≤ e) :
    0 ≤ padicValRat 3 ((3 : ℚ) ^ e * poleFour k) := by
  have h3ne : ((3 : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hnatne : (4 * k + 3 : ℕ) ≠ 0 := by omega
  have hcastne : ((4 * k + 3 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnatne
  have h16ne : ((16 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwoVal : padicValRat 3 (2 : ℚ) = 0 := by
    have hcast : (2 : ℚ) = ((2 : ℕ) : ℚ) := by norm_cast
    rw [hcast, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by decide)]
    rfl
  have hthreepow : padicValRat 3 ((3 : ℚ) ^ e) = e := by
    have hcast : ((3 : ℚ) ^ e) = ((3 ^ e : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast, padicValRat.of_nat, padicValNat.pow _ (by omega),
      padicValNat_self (p := 3)]
    norm_num
  have hexpr : ((3 : ℚ) ^ e * poleFour k) =
      -((3 : ℚ) ^ e) / ((2 : ℚ) * (((4 : ℚ) * k + 3) * ((16 : ℚ) ^ k))) := by
    simp only [poleFour]
    field_simp
  have hdenom : ((4 : ℚ) * k + 3) = ((4 * k + 3 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hexpr, hdenom,
    padicValRat.div (neg_ne_zero.mpr h3ne)
      (mul_ne_zero htwo (mul_ne_zero hcastne h16ne)), padicValRat.neg,
    padicValRat.mul htwo (mul_ne_zero hcastne h16ne), htwoVal,
    padicValRat.mul hcastne h16ne, padicValRat.of_nat,
    T81SelectedPairedRationalResidues.padicValRat_three_sixteen_pow k,
    hthreepow]
  omega

/-- At a positive even selected depth, multiplying the finite BBP partial sum
by `3 ^ (2 * t)` clears every three-adic denominator.  This is a finite
rational integrality statement only. -/
theorem scaled_bbpPartial_three_integral (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ padicValRat 3 ((3 : ℚ) ^ (2 * t) * bbpPartial (selectedDepth (2 * t))) := by
  have hstep : ∀ x y : ℚ, 0 ≤ padicValRat 3 x → 0 ≤ padicValRat 3 y →
      0 ≤ padicValRat 3 (x + y) := by
    intro x y hx hy
    by_cases hzero : x + y = 0
    · rw [hzero, padicValRat.zero]
    · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hzero)
  have hrange : ∀ k ∈ Finset.range (selectedDepth (2 * t) + 1),
      k ≤ selectedDepth (2 * t) := fun k hk =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : 0 ≤ padicValRat 3
      (∑ k ∈ Finset.range (selectedDepth (2 * t) + 1),
        ((3 : ℚ) ^ (2 * t)) * poleOne k) :=
    padicValRat_three_finset_sum_nonneg _ _ fun k hk =>
      poleOne_scaled_padicVal_nonneg_of_denominator_bound (2 * t) k
        (T88SelectedDepthDenominatorValuations.poleOne_denominator_val_le t k ht
          (hrange k hk))
  have h2 : 0 ≤ padicValRat 3
      (∑ k ∈ Finset.range (selectedDepth (2 * t) + 1),
        ((3 : ℚ) ^ (2 * t)) * poleTwo k) :=
    padicValRat_three_finset_sum_nonneg _ _ fun k hk =>
      poleTwo_scaled_padicVal_nonneg_of_denominator_bound (2 * t) k
        (T88SelectedDepthDenominatorValuations.poleTwo_denominator_val_le t k ht
          (hrange k hk))
  have h3 : 0 ≤ padicValRat 3
      (∑ k ∈ Finset.range (selectedDepth (2 * t) + 1),
        ((3 : ℚ) ^ (2 * t)) * poleThree k) :=
    padicValRat_three_finset_sum_nonneg _ _ fun k hk =>
      poleThree_scaled_padicVal_nonneg_of_denominator_bound (2 * t) k
        (le_trans
          (T88SelectedDepthDenominatorValuations.poleThree_denominator_val_le_sharp
            t k ht (hrange k hk)) (by omega))
  have h4 : 0 ≤ padicValRat 3
      (∑ k ∈ Finset.range (selectedDepth (2 * t) + 1),
        ((3 : ℚ) ^ (2 * t)) * poleFour k) :=
    padicValRat_three_finset_sum_nonneg _ _ fun k hk =>
      poleFour_scaled_padicVal_nonneg_of_denominator_bound (2 * t) k
        (le_trans
          (T88SelectedDepthDenominatorValuations.poleFour_denominator_val_le_sharp
            t k ht (hrange k hk)) (by omega))
  rw [scaled_bbpPartial_eq_scaled_pole_sums]
  exact hstep _ _ (hstep _ _ (hstep _ _ h1 h2) h3) h4

end Theory.PiDigits.T89SelectedDepthScaledIntegrality

#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.padicValRat_three_finset_sum_nonneg
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.scaled_bbpPartial_eq_scaled_pole_sums
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.poleThree_scaled_padicVal_nonneg_of_denominator_bound
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.poleOne_scaled_padicVal_nonneg_of_denominator_bound
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.poleTwo_scaled_padicVal_nonneg_of_denominator_bound
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.poleFour_scaled_padicVal_nonneg_of_denominator_bound
#print axioms Theory.PiDigits.T89SelectedDepthScaledIntegrality.scaled_bbpPartial_three_integral
