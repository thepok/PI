import TheoryLib.PiQuantitativeBlockHitting.T144T144BoundaryLayerMass

/-!
# T145: scalar bounds for the first two decimal boundary layers

This module supplies only explicit real inequalities for the exact T144
layer masses.  It contains no endpoint estimate or interval consumer.
-/

noncomputable section

namespace Theory.PiDigits.BoundaryLayerScalarBounds

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.BoundaryLayerMass

/-- Uniform explicit lower bound for the natural-scale cosine deficit. -/
theorem cosineDeficit_mul_sq_gt
    (q : ℕ) (hq : 1000 ≤ q) :
    4929 / 1000 < (1 - Real.cos (Real.pi / q)) * (q : ℝ) ^ 2 := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  let y : ℝ := Real.pi / (2 * q)
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyUpper : y < 2 / (q : ℝ) := by
    dsimp [y]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
    field_simp
    nlinarith [Real.pi_lt_four]
  have hyOne : y ≤ 1 := by
    have htwoDiv : 2 / (q : ℝ) ≤ 1 := by
      exact (div_le_one hqR).2 (by exact_mod_cast (show 2 ≤ q by omega))
    linarith
  have hsinRaw := Real.sin_gt_sub_cube hy0 hyOne
  have hyLower : 157 / (100 * (q : ℝ)) < y := by
    dsimp [y]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 100 * q)).2
    field_simp
    nlinarith [Real.pi_gt_d2]
  have hyCube : y ^ 3 < 8 / (q : ℝ) ^ 3 := by
    have hp := pow_lt_pow_left₀ hyUpper hy0.le (by norm_num : 3 ≠ 0)
    convert hp using 1 <;> ring
  have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hs := Nat.mul_self_le_mul_self hq
    norm_num [pow_two] at hs ⊢
    exact_mod_cast hs
  have hsinLower : 15699 / (10000 * (q : ℝ)) < Real.sin y := by
    have hpre : 15699 / (10000 * (q : ℝ)) < y - y ^ 3 / 4 := by
      field_simp at hyLower hyCube hqSq ⊢
      nlinarith
    exact hpre.trans hsinRaw
  have hsin0 : 0 < Real.sin y := lt_trans (by positivity) hsinLower
  have hsinSq : (15699 / (10000 * (q : ℝ))) ^ 2 < Real.sin y ^ 2 :=
    (sq_lt_sq₀ (by positivity) hsin0.le).2 hsinLower
  have hcos : Real.cos (Real.pi / q) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / (q : ℝ) = 2 * y by
      dsimp [y]
      field_simp]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  field_simp at hsinSq ⊢
  nlinarith [sq_pos_of_pos hqR]

private lemma cosineDeficit_lt_five_div_sq
    (q : ℕ) (hq : 0 < q) :
    1 - Real.cos (Real.pi / q) < 5 / (q : ℝ) ^ 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / q)
  have hpiSq : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hqR : (0 : ℝ) < q := by positivity
  have hsq : (Real.pi / q) ^ 2 / 2 < 5 / (q : ℝ) ^ 2 := by
    field_simp
    nlinarith [sq_pos_of_pos hqR]
  linarith

/-- Uniform explicit upper bound for the signed T128 zero coefficient. -/
theorem boundaryZeroCoefficient_lt_twelve_div_five_mul
    (q : ℕ) (hq : 1000 ≤ q) :
    boundaryZeroCoefficient q < 12 / (5 * (q : ℝ)) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hdelta := cosineDeficit_lt_five_div_sq q hq0
  rw [boundaryZeroCoefficient_eq q hq0]
  have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hs := Nat.mul_self_le_mul_self hq
    norm_num [pow_two] at hs ⊢
    exact_mod_cast hs
  field_simp at hdelta ⊢
  nlinarith [sq_pos_of_pos hqR]

private lemma pow_ten_ge_thousand (k : ℕ) (hk : 3 ≤ k) :
    1000 ≤ 10 ^ k := by
  calc
    1000 = 10 ^ 3 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- The first decimal valuation layer retains more than `49/200` mass. -/
theorem boundaryLayerMass_ten_gt
    (k : ℕ) (hk : 3 ≤ k) :
    49 / 200 < boundaryLayerMass (10 ^ k) 10 := by
  let q := 10 ^ k
  have hq : 1000 ≤ q := pow_ten_ge_thousand k hk
  have hdelta := cosineDeficit_mul_sq_gt q hq
  have hzero := boundaryZeroCoefficient_lt_twelve_div_five_mul q hq
  have hmass := boundaryLayerMass_pow_ten_eq k 1 (by norm_num) (by omega)
  norm_num at hmass
  rw [hmass]
  dsimp [q] at hdelta hzero
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  dsimp [q] at hqR
  have hzero' : boundaryZeroCoefficient (10 ^ k) < 3 / 1250 := by
    calc
      boundaryZeroCoefficient (10 ^ k) < 12 / (5 * ((10 ^ k : ℕ) : ℝ)) := hzero
      _ ≤ 3 / 1250 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (10 ^ k : ℕ))).2
        calc
          (12 : ℝ) = (3 / 250) * 1000 := by norm_num
          _ ≤ (3 / 250) * ((10 ^ k : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hqR (by norm_num)
          _ = (3 / 1250) * (5 * ((10 ^ k : ℕ) : ℝ)) := by ring
  norm_num at hdelta ⊢
  nlinarith

/-- The second decimal valuation layer retains more than `23/1000` mass. -/
theorem boundaryLayerMass_hundred_gt
    (k : ℕ) (hk : 3 ≤ k) :
    23 / 1000 < boundaryLayerMass (10 ^ k) 100 := by
  let q := 10 ^ k
  have hq : 1000 ≤ q := pow_ten_ge_thousand k hk
  have hdelta := cosineDeficit_mul_sq_gt q hq
  have hzero := boundaryZeroCoefficient_lt_twelve_div_five_mul q hq
  have hmass := boundaryLayerMass_pow_ten_eq k 2 (by norm_num) (by omega)
  norm_num at hmass
  rw [hmass]
  dsimp [q] at hdelta hzero
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  dsimp [q] at hqR
  have hzero' : boundaryZeroCoefficient (10 ^ k) < 3 / 1250 := by
    calc
      boundaryZeroCoefficient (10 ^ k) < 12 / (5 * ((10 ^ k : ℕ) : ℝ)) := hzero
      _ ≤ 3 / 1250 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (10 ^ k : ℕ))).2
        calc
          (12 : ℝ) = (3 / 250) * 1000 := by norm_num
          _ ≤ (3 / 250) * ((10 ^ k : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hqR (by norm_num)
          _ = (3 / 1250) * (5 * ((10 ^ k : ℕ) : ℝ)) := by ring
  norm_num at hdelta ⊢
  nlinarith

end Theory.PiDigits.BoundaryLayerScalarBounds

#print axioms Theory.PiDigits.BoundaryLayerScalarBounds.cosineDeficit_mul_sq_gt
#print axioms Theory.PiDigits.BoundaryLayerScalarBounds.boundaryZeroCoefficient_lt_twelve_div_five_mul
#print axioms Theory.PiDigits.BoundaryLayerScalarBounds.boundaryLayerMass_ten_gt
#print axioms Theory.PiDigits.BoundaryLayerScalarBounds.boundaryLayerMass_hundred_gt
