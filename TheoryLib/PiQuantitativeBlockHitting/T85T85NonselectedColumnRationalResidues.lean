import TheoryLib.PiQuantitativeBlockHitting.T84T84SelectedBoundaryColumn

/-!
# T85: shared rational support for the nonselected BBP column

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module provides only the common direct-rational valuation transport for
the future complete-block and tail analysis of the four nonselected BBP
poles.  It contains no pole residue, nonselected-column, endpoint-defect,
SP1, or V1 claim.
-/

namespace Theory.PiDigits.T85NonselectedColumnRationalResidues

open T74ThreePrimaryDecimation T77SelectedPadicDefectShell
  T78SelectedPadicDefectCongruence T81SelectedPairedRationalResidues
  T82SelectedPairedColumnModNine

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- A natural rational not divisible by three is a three-adic unit. -/
theorem padicValRat_nat_cast_zero_of_three_nondvd (a : ℕ)
    (ha : ¬ 3 ∣ a) : padicValRat 3 (a : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd ha]
  rfl

/-- Nine times a three-adic unit vanishes modulo nine. -/
theorem ratCongruentThree_nine_mul_unit_zero {u : ℚ}
    (hu : u ≠ 0) (hvu : padicValRat 3 u = 0) :
    RatCongruentThree 2 (9 * u) 0 := by
  unfold RatCongruentThree
  right
  rw [show (9 : ℚ) * u - 0 = 9 * u by ring,
    padicValRat.mul (by norm_num) hu, padicValRat_three_nine, hvu]
  norm_num

/-- A direct height-zero transport through a natural unit denominator. -/
theorem ratCongruentThree_nine_mul_div_unit_zero {c : ℚ} {a n : ℕ}
    (hc : c ≠ 0) (hvc : padicValRat 3 c = 0) (ha : ¬ 3 ∣ a) :
    RatCongruentThree 2 (9 * (c / (a : ℚ) / 16 ^ n)) 0 := by
  have ha0 : a ≠ 0 := by
    intro hzero
    apply ha
    simp [hzero]
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  apply ratCongruentThree_nine_mul_unit_zero
  · exact div_ne_zero (div_ne_zero hc haq)
      (pow_ne_zero _ (by norm_num))
  · rw [padicValRat.div
      (div_ne_zero hc haq)
      (pow_ne_zero _ (by norm_num)),
      padicValRat.div hc haq, hvc,
      padicValRat_nat_cast_zero_of_three_nondvd a ha,
      padicValRat_three_sixteen_pow n]
    norm_num

/-- An explicit one-factor-of-three denominator reduces a term modulo nine
to a modulo-three congruence of its unit quotient. -/
theorem ratCongruentThree_nine_mul_height_one {c d : ℚ} {b n : ℕ}
    (hb : b ≠ 0) (h : RatCongruentThree 1 (c / (b : ℚ) / 16 ^ n) d) :
    RatCongruentThree 2 (9 * (c / ((3 * b : ℕ) : ℚ) / 16 ^ n)) (3 * d) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hfactor :
      9 * (c / ((3 * b : ℕ) : ℚ) / 16 ^ n) = 3 * (c / (b : ℚ) / 16 ^ n) := by
    push_cast
    field_simp
    ring
  rw [hfactor]
  have hscaled := ratCongruentThree_scale_three
    (x := 3 * (c / (b : ℚ) / 16 ^ n)) (c := d) (by simpa using h)
  simpa using hscaled

/-- Powers of sixteen are one modulo three. -/
theorem sixteen_pow_mod_three (j : ℕ) : 16 ^ j % 3 = 1 := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ, Nat.mul_mod, ih, Nat.mul_mod]

/-- A product of two numbers not divisible by three is not divisible by
three. -/
theorem mul_mod_three_ne_zero {x y : ℕ}
    (hx : x % 3 ≠ 0) (hy : y % 3 ≠ 0) : (x * y) % 3 ≠ 0 := by
  intro h
  have hd : 3 ∣ x * y := Nat.dvd_of_mod_eq_zero h
  rcases (by norm_num : Nat.Prime 3).dvd_mul.mp hd with h1 | h1
  · exact hx (Nat.dvd_iff_mod_eq_zero.mp h1)
  · exact hy (Nat.dvd_iff_mod_eq_zero.mp h1)

/-- A fraction with numerator divisible by nine and denominator prime to
three vanishes modulo nine in the rational three-adic sense. -/
theorem ratCongruentTwo_of_nine_dvd_num (a b : ℕ) (hb : b ≠ 0)
    (ha : a % 9 = 0) (hb3 : b % 3 ≠ 0) :
    RatCongruentThree 2 ((a : ℚ) / (b : ℚ)) 0 := by
  by_cases ha0 : a = 0
  · left
    rw [ha0]
    simp
  · right
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
    rw [sub_zero, padicValRat.div haq hbq, padicValRat.of_nat,
      padicValRat.of_nat]
    have hanine : a = 9 * (a / 9) := by omega
    have hc9 : a / 9 ≠ 0 := by omega
    have hpow : padicValNat 3 a = padicValNat 3 9 + padicValNat 3 (a / 9) := by
      conv_lhs => rw [hanine]
      exact padicValNat.mul (p := 3) (by norm_num) hc9
    have hnine : padicValNat 3 9 = 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]
      exact padicValNat.prime_pow 2
    have hbval : padicValNat 3 b = 0 :=
      padicValNat.eq_zero_of_not_dvd
        (fun hd => hb3 (Nat.dvd_iff_mod_eq_zero.mp hd))
    rw [hpow, hnine, hbval]
    omega

/-- A nonselected pole-four term with a three-adic unit linear denominator
vanishes modulo nine. -/
theorem nonselectedTerm_poleFour_congr_zero (r s : ℕ)
    (hs : (36 * r + 4 * s + 3) % 3 ≠ 0) :
    RatCongruentThree 2 (9 * poleFour (9 * r + s)) 0 := by
  have hcoefficient : padicValRat 3 (-(1 : ℚ) / 2) = 0 := by
    have htwo : padicValRat 3 (2 : ℚ) = 0 := by
      change padicValRat 3 ((2 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide)]
      norm_num
    rw [padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
      padicValRat.one, htwo]
    norm_num
  have hden : ¬ 3 ∣ 4 * (9 * r + s) + 3 := by
    rw [show 4 * (9 * r + s) + 3 = 36 * r + 4 * s + 3 by omega]
    exact fun hd => hs (Nat.dvd_iff_mod_eq_zero.mp hd)
  simpa [poleFour] using
    (ratCongruentThree_nine_mul_div_unit_zero
      (c := -(1 : ℚ) / 2) (a := 4 * (9 * r + s) + 3) (n := 9 * r + s)
      (by norm_num) hcoefficient hden)

/-- The two height-one nonselected pole-four terms cancel modulo nine. -/
theorem pairTerms_poleFour_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (9 * poleFour (9 * r + 0) + 9 * poleFour (9 * r + 3)) 0 := by
  have hform : 9 * poleFour (9 * r + 0) + 9 * poleFour (9 * r + 3)
      = -(((3 * (4096 * (12 * r + 5) + (12 * r + 1)) : ℕ) : ℚ)
        / ((2 * (12 * r + 1) * (12 * r + 5) * 16 ^ (9 * r + 3) : ℕ) : ℚ)) := by
    simp only [poleFour]
    push_cast
    field_simp
    ring
  rw [hform]
  have ha9 : (3 * (4096 * (12 * r + 5) + (12 * r + 1))) % 9 = 0 := by
    have hN : (4096 * (12 * r + 5) + (12 * r + 1)) % 3 = 0 := by omega
    omega
  have hb3 : (2 * (12 * r + 1) * (12 * r + 5) * 16 ^ (9 * r + 3)) % 3 ≠ 0 := by
    refine mul_mod_three_ne_zero ?_ ?_
    · exact mul_mod_three_ne_zero (by omega) (by omega)
    · rw [sixteen_pow_mod_three]
      omega
  have h := ratCongruentTwo_of_nine_dvd_num _ _ (by positivity) ha9 hb3
  simpa using ratCongruentThree_neg h

/-- One complete nine-block complement of the selected pole-four residue
six vanishes modulo nine. -/
theorem completeBlock_poleFour_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 9 with s ≠ 6, 9 * poleFour (9 * r + s)) 0 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 6) (Finset.range 9)
      = insert 0 (insert 3
          (Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 6)
            (Finset.range 9))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 6)
        (Finset.range 9), 9 * poleFour (9 * r + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 6)
        (Finset.range 9))
      (f := fun s : ℕ => 9 * poleFour (9 * r + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleFour_congr_zero r s (by omega))
  have hcomb := ratCongruentThree_add (pairTerms_poleFour_congr_zero r) hrest
  rw [show (9 * poleFour (9 * r + 0) + (9 * poleFour (9 * r + 3) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 6)
      (Finset.range 9), 9 * poleFour (9 * r + s)) : ℚ)
      = ((9 * poleFour (9 * r + 0) + 9 * poleFour (9 * r + 3)) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 6)
      (Finset.range 9), 9 * poleFour (9 * r + s) : ℚ) from by ring]
  simpa using hcomb

/-- The five-term final-block complement of the selected pole-four residue
six vanishes modulo nine. -/
theorem tailBlock_poleFour_congr_zero (R : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 5 with s ≠ 6, 9 * poleFour (9 * R + s)) 0 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 6) (Finset.range 5)
      = insert 0 (insert 3
          (Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3) (Finset.range 5))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3)
        (Finset.range 5), 9 * poleFour (9 * R + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3)
        (Finset.range 5))
      (f := fun s : ℕ => 9 * poleFour (9 * R + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleFour_congr_zero R s (by omega))
  have hcomb := ratCongruentThree_add (pairTerms_poleFour_congr_zero R) hrest
  rw [show (9 * poleFour (9 * R + 0) + (9 * poleFour (9 * R + 3) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3)
      (Finset.range 5), 9 * poleFour (9 * R + s)) : ℚ)
      = ((9 * poleFour (9 * R + 0) + 9 * poleFour (9 * R + 3)) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 0 ∧ s ≠ 3)
      (Finset.range 5), 9 * poleFour (9 * R + s) : ℚ) from by ring]
  simpa using hcomb

/-- The complete-block nonselected pole-four column vanishes modulo nine. -/
theorem completeNonselected_poleFour_congr_zero (M : Nat) :
    RatCongruentThree 2 (completeNonselected poleFour 6 M) 0 := by
  unfold completeNonselected
  simpa using ratCongruentThree_sum
    (f := fun r : ℕ =>
      ∑ s ∈ Finset.range 9 with s ≠ 6, 9 * poleFour (9 * r + s))
    (g := fun _ => (0 : ℚ))
    (fun r _ => completeBlock_poleFour_congr_zero r)

/-- The five-term nonselected pole-four tail vanishes modulo nine. -/
theorem tailNonselected_poleFour_congr_zero (M : Nat) :
    RatCongruentThree 2 (tailNonselected poleFour 6 M) 0 :=
  tailBlock_poleFour_congr_zero (M + 1)

/-- The combined nonselected pole-four column vanishes modulo nine. -/
theorem nonselectedPoleFour_congr_zero (M : Nat) :
    RatCongruentThree 2
      (completeNonselected poleFour 6 M + tailNonselected poleFour 6 M) 0 := by
  simpa using ratCongruentThree_add
    (completeNonselected_poleFour_congr_zero M)
    (tailNonselected_poleFour_congr_zero M)

/-- A nonselected pole-three term with a three-adic unit linear denominator
vanishes modulo nine. -/
theorem nonselectedTerm_poleThree_congr_zero (r s : ℕ)
    (hs : (8 * s + 5) % 3 ≠ 0) :
    RatCongruentThree 2 (9 * poleThree (9 * r + s)) 0 := by
  have hcoefficient : padicValRat 3 (-(1 : ℚ)) = 0 := by
    rw [padicValRat.neg, padicValRat.one]
  have hden : ¬ 3 ∣ 8 * (9 * r + s) + 5 := by
    intro hd
    apply hs
    rw [← show (8 * (9 * r + s) + 5) % 3 = (8 * s + 5) % 3 by omega]
    exact Nat.dvd_iff_mod_eq_zero.mp hd
  simpa [poleThree] using
    (ratCongruentThree_nine_mul_div_unit_zero
      (c := -(1 : ℚ)) (a := 8 * (9 * r + s) + 5) (n := 9 * r + s)
      (by norm_num) hcoefficient hden)

/-- The two height-one nonselected pole-three terms cancel modulo nine. -/
theorem pairTerms_poleThree_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (9 * poleThree (9 * r + 2) + 9 * poleThree (9 * r + 8)) 0 := by
  let u : ℕ := (24 * r + 7) * 16 ^ (9 * r + 2)
  let v : ℕ := (24 * r + 23) * 16 ^ (9 * r + 8)
  have hu : u % 3 = 1 := by
    dsimp [u]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hv : v % 3 = 2 := by
    dsimp [v]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hnum : (u + v) % 3 = 0 := by omega
  have hden : (u * v) % 3 ≠ 0 := mul_mod_three_ne_zero (by omega) (by omega)
  have hform : 9 * poleThree (9 * r + 2) + 9 * poleThree (9 * r + 8)
      = -(((3 * (u + v) : ℕ) : ℚ) / ((u * v : ℕ) : ℚ)) := by
    dsimp [u, v]
    simp only [poleThree]
    push_cast
    field_simp
    ring
  rw [hform]
  have hzero := ratCongruentTwo_of_nine_dvd_num (3 * (u + v)) (u * v)
    (by positivity) (by omega) hden
  simpa using ratCongruentThree_neg hzero

/-- The height-one pole-three term at residue two is six modulo nine. -/
theorem tailHeightOne_poleThree_congr_six (R : ℕ) :
    RatCongruentThree 2 (9 * poleThree (9 * R + 2)) 6 := by
  let u : ℕ := (24 * R + 7) * 16 ^ (9 * R + 2)
  have hu : u % 3 = 1 := by
    dsimp [u]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hnum : (1 + 2 * u) % 3 = 0 := by omega
  have hden : u % 3 ≠ 0 := by omega
  have hform : 9 * poleThree (9 * R + 2) - 6
      = -(((3 * (1 + 2 * u) : ℕ) : ℚ) / (u : ℚ)) := by
    dsimp [u]
    simp only [poleThree]
    push_cast
    field_simp
    ring
  have hzero := ratCongruentTwo_of_nine_dvd_num (3 * (1 + 2 * u)) u
    (by positivity) (by omega) hden
  have hsub : RatCongruentThree 2 (9 * poleThree (9 * R + 2) - 6) 0 := by
    rw [hform]
    simpa using ratCongruentThree_neg hzero
  have h := ratCongruentThree_add hsub (ratCongruentThree_refl 2 6)
  simpa using h

/-- One complete nine-block complement of the selected pole-three residue
five vanishes modulo nine. -/
theorem completeBlock_poleThree_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 9 with s ≠ 5, 9 * poleThree (9 * r + s)) 0 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 5) (Finset.range 9)
      = insert 2 (insert 8
          (Finset.filter (fun s : ℕ => s ≠ 2 ∧ s ≠ 5 ∧ s ≠ 8)
            (Finset.range 9))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 2 ∧ s ≠ 5 ∧ s ≠ 8)
        (Finset.range 9), 9 * poleThree (9 * r + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 2 ∧ s ≠ 5 ∧ s ≠ 8)
        (Finset.range 9))
      (f := fun s : ℕ => 9 * poleThree (9 * r + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleThree_congr_zero r s (by omega))
  have hcomb := ratCongruentThree_add (pairTerms_poleThree_congr_zero r) hrest
  rw [show (9 * poleThree (9 * r + 2) + (9 * poleThree (9 * r + 8) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 2 ∧ s ≠ 5 ∧ s ≠ 8)
      (Finset.range 9), 9 * poleThree (9 * r + s)) : ℚ)
      = ((9 * poleThree (9 * r + 2) + 9 * poleThree (9 * r + 8)) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 2 ∧ s ≠ 5 ∧ s ≠ 8)
      (Finset.range 9), 9 * poleThree (9 * r + s) : ℚ) from by ring]
  simpa using hcomb

/-- The five-term complement of the selected pole-three residue five is six
modulo nine. -/
theorem tailBlock_poleThree_congr_six (R : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 5 with s ≠ 5, 9 * poleThree (9 * R + s)) 6 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 5) (Finset.range 5)
      = insert 2 (Finset.filter (fun s : ℕ => s ≠ 2) (Finset.range 5)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 2)
        (Finset.range 5), 9 * poleThree (9 * R + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 2) (Finset.range 5))
      (f := fun s : ℕ => 9 * poleThree (9 * R + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleThree_congr_zero R s (by omega))
  have hcomb := ratCongruentThree_add (tailHeightOne_poleThree_congr_six R) hrest
  simpa using hcomb

/-- The complete-block nonselected pole-three column vanishes modulo nine. -/
theorem completeNonselected_poleThree_congr_zero (M : Nat) :
    RatCongruentThree 2 (completeNonselected poleThree 5 M) 0 := by
  unfold completeNonselected
  simpa using ratCongruentThree_sum
    (f := fun r : ℕ =>
      ∑ s ∈ Finset.range 9 with s ≠ 5, 9 * poleThree (9 * r + s))
    (g := fun _ => (0 : ℚ))
    (fun r _ => completeBlock_poleThree_congr_zero r)

/-- The five-term nonselected pole-three tail is six modulo nine. -/
theorem tailNonselected_poleThree_congr_six (M : Nat) :
    RatCongruentThree 2 (tailNonselected poleThree 5 M) 6 :=
  tailBlock_poleThree_congr_six (M + 1)

/-- The combined nonselected pole-three column is six modulo nine. -/
theorem nonselectedPoleThree_congr_six (M : Nat) :
    RatCongruentThree 2
      (completeNonselected poleThree 5 M + tailNonselected poleThree 5 M) 6 := by
  simpa using ratCongruentThree_add
    (completeNonselected_poleThree_congr_zero M)
    (tailNonselected_poleThree_congr_six M)

/-- A nonselected pole-two term with a three-adic unit linear denominator
vanishes modulo nine. -/
theorem nonselectedTerm_poleTwo_congr_zero (r s : ℕ)
    (hs : (2 * (9 * r + s) + 1) % 3 ≠ 0) :
    RatCongruentThree 2 (9 * poleTwo (9 * r + s)) 0 := by
  have hcoefficient : padicValRat 3 (-(1 : ℚ) / 2) = 0 := by
    have htwo : padicValRat 3 (2 : ℚ) = 0 := by
      change padicValRat 3 ((2 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide)]
      norm_num
    rw [padicValRat.div (by norm_num) (by norm_num), padicValRat.neg,
      padicValRat.one, htwo]
    norm_num
  have hden : ¬ 3 ∣ 2 * (9 * r + s) + 1 :=
    fun hd => hs (Nat.dvd_iff_mod_eq_zero.mp hd)
  simpa [poleTwo] using
    (ratCongruentThree_nine_mul_div_unit_zero
      (c := -(1 : ℚ) / 2) (a := 2 * (9 * r + s) + 1) (n := 9 * r + s)
      (by norm_num) hcoefficient hden)

/-- The height-one nonselected pole-two term at residue one is three modulo
nine. -/
theorem term_poleTwo_s1_congr_three (r : ℕ) :
    RatCongruentThree 2 (9 * poleTwo (9 * r + 1)) 3 := by
  let u : ℕ := (6 * r + 1) * 16 ^ (9 * r + 1)
  have hu : u % 3 = 1 := by
    dsimp [u]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hnum : (1 + 2 * u) % 3 = 0 := by omega
  have hden : (2 * u) % 3 ≠ 0 := mul_mod_three_ne_zero (by norm_num) (by omega)
  have hform : 9 * poleTwo (9 * r + 1) - 3
      = -(((3 * (1 + 2 * u) : ℕ) : ℚ) / ((2 * u : ℕ) : ℚ)) := by
    dsimp [u]
    simp only [poleTwo]
    push_cast
    field_simp
    ring
  have hzero := ratCongruentTwo_of_nine_dvd_num (3 * (1 + 2 * u)) (2 * u)
    (by positivity) (by omega) hden
  have hsub : RatCongruentThree 2 (9 * poleTwo (9 * r + 1) - 3) 0 := by
    rw [hform]
    simpa using ratCongruentThree_neg hzero
  have h := ratCongruentThree_add hsub (ratCongruentThree_refl 2 3)
  simpa using h

/-- The height-one nonselected pole-two term at residue seven is six modulo
nine. -/
theorem term_poleTwo_s7_congr_six (r : ℕ) :
    RatCongruentThree 2 (9 * poleTwo (9 * r + 7)) 6 := by
  let u : ℕ := (6 * r + 5) * 16 ^ (9 * r + 7)
  have hu : u % 3 = 2 := by
    dsimp [u]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hnum : (1 + 4 * u) % 3 = 0 := by omega
  have hden : (2 * u) % 3 ≠ 0 := mul_mod_three_ne_zero (by norm_num) (by omega)
  have hform : 9 * poleTwo (9 * r + 7) - 6
      = -(((3 * (1 + 4 * u) : ℕ) : ℚ) / ((2 * u : ℕ) : ℚ)) := by
    dsimp [u]
    simp only [poleTwo]
    push_cast
    field_simp
    ring
  have hzero := ratCongruentTwo_of_nine_dvd_num (3 * (1 + 4 * u)) (2 * u)
    (by positivity) (by omega) hden
  have hsub : RatCongruentThree 2 (9 * poleTwo (9 * r + 7) - 6) 0 := by
    rw [hform]
    simpa using ratCongruentThree_neg hzero
  have h := ratCongruentThree_add hsub (ratCongruentThree_refl 2 6)
  simpa using h

/-- One complete nine-block complement of the selected pole-two residue four
vanishes modulo nine. -/
theorem completeBlock_poleTwo_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 9 with s ≠ 4, 9 * poleTwo (9 * r + s)) 0 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 4) (Finset.range 9)
      = insert 1 (insert 7
          (Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
            (Finset.range 9))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
        (Finset.range 9), 9 * poleTwo (9 * r + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
        (Finset.range 9))
      (f := fun s : ℕ => 9 * poleTwo (9 * r + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleTwo_congr_zero r s (by omega))
  have hpair := ratCongruentThree_add (term_poleTwo_s1_congr_three r)
    (term_poleTwo_s7_congr_six r)
  have hcomb := ratCongruentThree_add hpair hrest
  rw [show (9 * poleTwo (9 * r + 1) + (9 * poleTwo (9 * r + 7) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
      (Finset.range 9), 9 * poleTwo (9 * r + s)) : ℚ)
      = ((9 * poleTwo (9 * r + 1) + 9 * poleTwo (9 * r + 7)) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
      (Finset.range 9), 9 * poleTwo (9 * r + s) : ℚ) from by ring]
  have hnine : RatCongruentThree 2 (9 : ℚ) 0 := by
    simpa using ratCongruentThree_nine_mul_unit_zero (u := (1 : ℚ))
      (by norm_num) padicValRat.one
  have hpairzero : RatCongruentThree 2 ((3 : ℚ) + 6 + 0) 0 := by
    convert hnine using 1 <;> norm_num
  exact ratCongruentThree_trans hcomb hpairzero

/-- The five-term complement of the selected pole-two residue four is three
modulo nine. -/
theorem tailBlock_poleTwo_congr_three (R : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 5 with s ≠ 4, 9 * poleTwo (9 * R + s)) 3 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 4) (Finset.range 5)
      = insert 1 (Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4)
        (Finset.range 5)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4)
        (Finset.range 5), 9 * poleTwo (9 * R + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4) (Finset.range 5))
      (f := fun s : ℕ => 9 * poleTwo (9 * R + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleTwo_congr_zero R s (by omega))
  have hcomb := ratCongruentThree_add (term_poleTwo_s1_congr_three R) hrest
  simpa using hcomb

/-- The complete-block nonselected pole-two column vanishes modulo nine. -/
theorem completeNonselected_poleTwo_congr_zero (M : Nat) :
    RatCongruentThree 2 (completeNonselected poleTwo 4 M) 0 := by
  unfold completeNonselected
  simpa using ratCongruentThree_sum
    (f := fun r : ℕ =>
      ∑ s ∈ Finset.range 9 with s ≠ 4, 9 * poleTwo (9 * r + s))
    (g := fun _ => (0 : ℚ))
    (fun r _ => completeBlock_poleTwo_congr_zero r)

/-- The five-term nonselected pole-two tail is three modulo nine. -/
theorem tailNonselected_poleTwo_congr_three (M : Nat) :
    RatCongruentThree 2 (tailNonselected poleTwo 4 M) 3 :=
  tailBlock_poleTwo_congr_three (M + 1)

/-- The combined nonselected pole-two column is three modulo nine. -/
theorem nonselectedPoleTwo_congr_three (M : Nat) :
    RatCongruentThree 2
      (completeNonselected poleTwo 4 M + tailNonselected poleTwo 4 M) 3 := by
  simpa using ratCongruentThree_add
    (completeNonselected_poleTwo_congr_zero M)
    (tailNonselected_poleTwo_congr_three M)

/-- A nonselected pole-one term with a three-adic unit linear denominator
vanishes modulo nine. -/
theorem nonselectedTerm_poleOne_congr_zero (r s : ℕ)
    (hs : (72 * r + 8 * s + 1) % 3 ≠ 0) :
    RatCongruentThree 2 (9 * poleOne (9 * r + s)) 0 := by
  have hcoefficient : padicValRat 3 (4 : ℚ) = 0 := by
    change padicValRat 3 ((4 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide)]
    norm_num
  have hden : ¬ 3 ∣ 8 * (9 * r + s) + 1 := by
    rw [show 8 * (9 * r + s) + 1 = 72 * r + 8 * s + 1 by omega]
    exact fun hd => hs (Nat.dvd_iff_mod_eq_zero.mp hd)
  simpa [poleOne] using
    (ratCongruentThree_nine_mul_div_unit_zero
      (c := (4 : ℚ)) (a := 8 * (9 * r + s) + 1) (n := 9 * r + s)
      (by norm_num) hcoefficient hden)

/-- The height-one pole-one term at residue four is six modulo nine. -/
theorem heightOneFour_poleOne_congr_six (R : ℕ) :
    RatCongruentThree 2 (9 * poleOne (9 * R + 4)) 6 := by
  let u : ℕ := (24 * R + 11) * 16 ^ (9 * R + 4)
  let q : ℕ := u / 3
  have hu : u % 3 = 2 := by
    dsimp [u]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hu0 : u ≠ 0 := by
    dsimp [u]
    positivity
  have hdecomp : u = 3 * q + 2 := by
    dsimp [q]
    omega
  have hden : u % 3 ≠ 0 := by omega
  have huq : (u : ℚ) = 3 * (q : ℚ) + 2 := by
    exact_mod_cast hdecomp
  have hfactor : ((8 * (9 * R + 4) + 1 : ℕ) : ℚ)
      * (16 ^ (9 * R + 4) : ℚ) = 3 * (u : ℚ) := by
    dsimp [u]
    push_cast
    ring
  have hfactor' : (8 * (9 * (R : ℚ) + 4) + 1)
      * (16 ^ (9 * R + 4) : ℚ) = 3 * (u : ℚ) := by
    calc
      (8 * (9 * (R : ℚ) + 4) + 1) * (16 ^ (9 * R + 4) : ℚ)
          = ((8 * (9 * R + 4) + 1 : ℕ) : ℚ)
            * (16 ^ (9 * R + 4) : ℚ) := by push_cast; ring
      _ = 3 * (u : ℚ) := hfactor
  have hfactor'' : (8 * ((9 * R + 4 : ℕ) : ℚ) + 1)
      * (16 ^ (9 * R + 4) : ℚ) = 3 * (u : ℚ) := by
    convert hfactor' using 1 <;> push_cast <;> ring
  have hform : 9 * poleOne (9 * R + 4) - 6
      = -(((18 * q : ℕ) : ℚ) / (u : ℚ)) := by
    rw [poleOne]
    rw [div_div, hfactor'']
    rw [huq]
    norm_num [div_eq_mul_inv]
    field_simp
    ring
  have hzero := ratCongruentTwo_of_nine_dvd_num (18 * q) u
    hu0 (by omega) hden
  have hsub : RatCongruentThree 2 (9 * poleOne (9 * R + 4) - 6) 0 := by
    rw [hform]
    simpa using ratCongruentThree_neg hzero
  have h := ratCongruentThree_add hsub (ratCongruentThree_refl 2 6)
  simpa using h

/-- The height-one pole-one term at residue seven is three modulo nine. -/
theorem heightOneSeven_poleOne_congr_three (R : ℕ) :
    RatCongruentThree 2 (9 * poleOne (9 * R + 7)) 3 := by
  let v : ℕ := (24 * R + 19) * 16 ^ (9 * R + 7)
  let q : ℕ := v / 3
  have hv : v % 3 = 1 := by
    dsimp [v]
    rw [Nat.mul_mod, sixteen_pow_mod_three]
    omega
  have hv0 : v ≠ 0 := by
    dsimp [v]
    positivity
  have hdecomp : v = 3 * q + 1 := by
    dsimp [q]
    omega
  have hp : 1 ≤ 16 ^ (9 * R + 7) := Nat.one_le_pow _ _ (by norm_num)
  have hv_ge : 4 ≤ v := by
    dsimp [v]
    calc
      4 ≤ 19 * 1 := by norm_num
      _ ≤ (24 * R + 19) * 16 ^ (9 * R + 7) := by
        exact Nat.mul_le_mul (by omega) hp
  have hqpos : 0 < q := by omega
  have hden : v % 3 ≠ 0 := by omega
  have hvq : (v : ℚ) = 3 * (q : ℚ) + 1 := by
    exact_mod_cast hdecomp
  have hfactor : ((8 * (9 * R + 7) + 1 : ℕ) : ℚ)
      * (16 ^ (9 * R + 7) : ℚ) = 3 * (v : ℚ) := by
    dsimp [v]
    push_cast
    ring
  have hfactor' : (8 * (9 * (R : ℚ) + 7) + 1)
      * (16 ^ (9 * R + 7) : ℚ) = 3 * (v : ℚ) := by
    calc
      (8 * (9 * (R : ℚ) + 7) + 1) * (16 ^ (9 * R + 7) : ℚ)
          = ((8 * (9 * R + 7) + 1 : ℕ) : ℚ)
            * (16 ^ (9 * R + 7) : ℚ) := by push_cast; ring
      _ = 3 * (v : ℚ) := hfactor
  have hfactor'' : (8 * ((9 * R + 7 : ℕ) : ℚ) + 1)
      * (16 ^ (9 * R + 7) : ℚ) = 3 * (v : ℚ) := by
    convert hfactor' using 1 <;> push_cast <;> ring
  have hform : 9 * poleOne (9 * R + 7) - 3
      = -(((9 * (q - 1) : ℕ) : ℚ) / (v : ℚ)) := by
    rw [poleOne]
    rw [div_div, hfactor'']
    rw [hvq]
    norm_num [div_eq_mul_inv]
    field_simp
    rw [Nat.cast_sub (by omega)]
    ring
  have hzero := ratCongruentTwo_of_nine_dvd_num (9 * (q - 1)) v
    hv0 (by omega) hden
  have hsub : RatCongruentThree 2 (9 * poleOne (9 * R + 7) - 3) 0 := by
    rw [hform]
    simpa using ratCongruentThree_neg hzero
  have h := ratCongruentThree_add hsub (ratCongruentThree_refl 2 3)
  simpa using h

/-- The two height-one nonselected pole-one terms cancel modulo nine. -/
theorem pairTerms_poleOne_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (9 * poleOne (9 * r + 4) + 9 * poleOne (9 * r + 7)) 0 := by
  have h := ratCongruentThree_add
    (heightOneFour_poleOne_congr_six r) (heightOneSeven_poleOne_congr_three r)
  have h9 : RatCongruentThree 2
      (9 * poleOne (9 * r + 4) + 9 * poleOne (9 * r + 7)) 9 := by
    convert h using 1 <;> norm_num
  have hnine : RatCongruentThree 2 (9 : ℚ) 0 := by
    simpa using ratCongruentThree_nine_mul_unit_zero (u := (1 : ℚ))
      (by norm_num) padicValRat.one
  exact ratCongruentThree_trans h9 hnine

/-- One complete nine-block complement of the selected pole-one residue one
vanishes modulo nine. -/
theorem completeBlock_poleOne_congr_zero (r : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 9 with s ≠ 1, 9 * poleOne (9 * r + s)) 0 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 1) (Finset.range 9)
      = insert 4 (insert 7
          (Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
            (Finset.range 9))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
        (Finset.range 9), 9 * poleOne (9 * r + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
        (Finset.range 9))
      (f := fun s : ℕ => 9 * poleOne (9 * r + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleOne_congr_zero r s (by omega))
  have hcomb := ratCongruentThree_add (pairTerms_poleOne_congr_zero r) hrest
  rw [show (9 * poleOne (9 * r + 4) + (9 * poleOne (9 * r + 7) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
      (Finset.range 9), 9 * poleOne (9 * r + s)) : ℚ)
      = ((9 * poleOne (9 * r + 4) + 9 * poleOne (9 * r + 7)) +
    ∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4 ∧ s ≠ 7)
      (Finset.range 9), 9 * poleOne (9 * r + s) : ℚ) from by ring]
  simpa using hcomb

/-- The five-term complement of the selected pole-one residue one is six
modulo nine. -/
theorem tailBlock_poleOne_congr_six (R : ℕ) :
    RatCongruentThree 2
      (∑ s ∈ Finset.range 5 with s ≠ 1, 9 * poleOne (9 * R + s)) 6 := by
  classical
  have hset : Finset.filter (fun s : ℕ => s ≠ 1) (Finset.range 5)
      = insert 4
          (Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4) (Finset.range 5)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  have hrest : RatCongruentThree 2
      (∑ s ∈ Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4)
        (Finset.range 5), 9 * poleOne (9 * R + s)) 0 := by
    simpa using ratCongruentThree_sum
      (S := Finset.filter (fun s : ℕ => s ≠ 1 ∧ s ≠ 4) (Finset.range 5))
      (f := fun s : ℕ => 9 * poleOne (9 * R + s)) (g := fun _ => (0 : ℚ))
      (fun s hs => by
        simp only [Finset.mem_filter, Finset.mem_range] at hs
        exact nonselectedTerm_poleOne_congr_zero R s (by omega))
  have hcomb := ratCongruentThree_add (heightOneFour_poleOne_congr_six R) hrest
  simpa using hcomb

/-- The complete-block nonselected pole-one column vanishes modulo nine. -/
theorem completeNonselected_poleOne_congr_zero (M : Nat) :
    RatCongruentThree 2 (completeNonselected poleOne 1 M) 0 := by
  unfold completeNonselected
  simpa using ratCongruentThree_sum
    (f := fun r : ℕ =>
      ∑ s ∈ Finset.range 9 with s ≠ 1, 9 * poleOne (9 * r + s))
    (g := fun _ => (0 : ℚ))
    (fun r _ => completeBlock_poleOne_congr_zero r)

/-- The five-term nonselected pole-one tail is six modulo nine. -/
theorem tailNonselected_poleOne_congr_six (M : Nat) :
    RatCongruentThree 2 (tailNonselected poleOne 1 M) 6 :=
  tailBlock_poleOne_congr_six (M + 1)

/-- The combined nonselected pole-one column is six modulo nine. -/
theorem nonselectedPoleOne_congr_six (M : Nat) :
    RatCongruentThree 2
      (completeNonselected poleOne 1 M + tailNonselected poleOne 1 M) 6 := by
  simpa using ratCongruentThree_add
    (completeNonselected_poleOne_congr_zero M)
    (tailNonselected_poleOne_congr_six M)

end Theory.PiDigits.T85NonselectedColumnRationalResidues

#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.padicValRat_nat_cast_zero_of_three_nondvd
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.ratCongruentThree_nine_mul_unit_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.ratCongruentThree_nine_mul_div_unit_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.ratCongruentThree_nine_mul_height_one
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.sixteen_pow_mod_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.mul_mod_three_ne_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.ratCongruentTwo_of_nine_dvd_num
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedTerm_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.pairTerms_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeBlock_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailBlock_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeNonselected_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailNonselected_poleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedPoleFour_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedTerm_poleThree_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.pairTerms_poleThree_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailHeightOne_poleThree_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeBlock_poleThree_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailBlock_poleThree_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeNonselected_poleThree_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailNonselected_poleThree_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedPoleThree_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedTerm_poleTwo_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.term_poleTwo_s1_congr_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.term_poleTwo_s7_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeBlock_poleTwo_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailBlock_poleTwo_congr_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeNonselected_poleTwo_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailNonselected_poleTwo_congr_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedPoleTwo_congr_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedTerm_poleOne_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.heightOneFour_poleOne_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.heightOneSeven_poleOne_congr_three
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.pairTerms_poleOne_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeBlock_poleOne_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailBlock_poleOne_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.completeNonselected_poleOne_congr_zero
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.tailNonselected_poleOne_congr_six
#print axioms Theory.PiDigits.T85NonselectedColumnRationalResidues.nonselectedPoleOne_congr_six
