import TheoryLib.PiQuantitativeBlockHitting.T153T153BoundaryRootGridNaturalConsumer

/-!
# T156: scalar closure of the natural-horizon root-grid consumer

T153 leaves its sufficient primitive-frequency hypothesis at an exact
endpoint-budget threshold.  This file proves the uniform rational comparison
needed to replace that threshold by `-861/1000`, and records the logically
equivalent strict obstruction for any cylinder missed at the natural horizon.

This is a scalar endpoint calculation.  It supplies no primitive-frequency
cancellation estimate for the decimal orbit of pi.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Theory.PiDigits.BoundaryNaturalThresholdClosure

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.BoundaryLayerMass
open Theory.PiDigits.BoundaryEndpointContraction
open Theory.PiDigits.BoundaryRootGridNaturalConsumer
open Theory.PiDigits.PrimitiveRayBoundaryConsumer

private lemma pow_ten_ge_thousand (k : ℕ) (hk : 3 ≤ k) :
    1000 ≤ 10 ^ k := by
  calc
    1000 = 10 ^ 3 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- A slightly sharper rational lower bound for the natural-scale cosine
deficit than T145 needs. -/
theorem cosineDeficit_mul_sq_gt_98681_div_20000
    (q : ℕ) (hq : 1000 ≤ q) :
    98681 / 20000 <
      (1 - Real.cos (Real.pi / q)) * (q : ℝ) ^ 2 := by
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
  have hyLower : 157079 / (100000 * (q : ℝ)) < y := by
    dsimp [y]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 100000 * q)).2
    field_simp
    nlinarith [Real.pi_gt_d6]
  have hyCube : y ^ 3 < 8 / (q : ℝ) ^ 3 := by
    have hp := pow_lt_pow_left₀ hyUpper hy0.le (by norm_num : 3 ≠ 0)
    convert hp using 1 <;> ring
  have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hs := Nat.mul_self_le_mul_self hq
    norm_num [pow_two] at hs ⊢
    exact_mod_cast hs
  have hsinLower : 157068 / (100000 * (q : ℝ)) < Real.sin y := by
    have hpre : 157068 / (100000 * (q : ℝ)) < y - y ^ 3 / 4 := by
      field_simp at hyLower hyCube hqSq ⊢
      nlinarith
    exact hpre.trans hsinRaw
  have hsin0 : 0 < Real.sin y := lt_trans (by positivity) hsinLower
  have hsinSq : (157068 / (100000 * (q : ℝ))) ^ 2 < Real.sin y ^ 2 :=
    (sq_lt_sq₀ (by positivity) hsin0.le).2 hsinLower
  have hcos : Real.cos (Real.pi / q) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / (q : ℝ) = 2 * y by
      dsimp [y]
      field_simp]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  field_simp at hsinSq ⊢
  nlinarith [sq_pos_of_pos hqR]

private lemma boundaryZeroCoefficient_nonneg_of_thousand
    (q : ℕ) (hq : 1000 ≤ q) :
    0 ≤ boundaryZeroCoefficient q := by
  have hq0 : 0 < q := by omega
  have hdelta := cosineDeficit_mul_sq_gt_98681_div_20000 q hq
  rw [boundaryZeroCoefficient_eq q hq0]
  have hqR : (0 : ℝ) < q := by positivity
  field_simp at hdelta ⊢
  nlinarith [sq_pos_of_pos hqR]

private lemma inverse_pow_ten_sum_le_one_ninth (k : ℕ) :
    (∑ s ∈ Icc 1 k, (1 : ℝ) / (10 ^ s : ℕ)) ≤ 1 / 9 := by
  have hgeom := geom_sum_Ico_le_of_lt_one
    (m := 1) (n := k + 1) (x := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by
    ext s
    simp]
  convert hgeom using 1 <;> norm_num [div_pow]

/-- The exact T153 threshold is uniformly strictly below `-861/1000` at
every decimal scale `q = 10^k`, `k ≥ 3`. -/
theorem rootGridNaturalThreshold_lt_neg_861
    (k A : ℕ) (hk : 3 ≤ k) :
    2 * primitiveBoundaryEndpointBudget (10 ^ k) A - 52909 / 200000 -
        ((10 ^ k : ℕ) : ℝ) * boundaryZeroCoefficient (10 ^ k) / 2 <
      -(861 / 1000 : ℝ) := by
  let q : ℕ := 10 ^ k
  let delta : ℝ := 1 - Real.cos (Real.pi / q)
  let alpha : ℝ := boundaryZeroCoefficient q
  have hq : 1000 ≤ q := by exact pow_ten_ge_thousand k hk
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hdelta := cosineDeficit_mul_sq_gt_98681_div_20000 q hq
  have halpha : 0 ≤ alpha := by
    exact boundaryZeroCoefficient_nonneg_of_thousand q hq
  have hsum := inverse_pow_ten_sum_le_one_ninth k
  have hbudget := primitiveBoundaryEndpointBudget_eq_sum_layerMasses k A hk
  have hlayer :
      primitiveBoundaryEndpointBudget q A ≤
        delta * (q : ℝ) ^ 2 / 2 *
          (∑ s ∈ Icc 1 k, (1 : ℝ) / (10 ^ s : ℕ)) := by
    rw [show primitiveBoundaryEndpointBudget q A =
        ∑ s ∈ Icc 1 k, boundaryLayerMass q (10 ^ s) by
      simpa [q] using hbudget]
    calc
      (∑ s ∈ Icc 1 k, boundaryLayerMass q (10 ^ s)) =
          ∑ s ∈ Icc 1 k,
            (delta * (q : ℝ) ^ 2 / (10 ^ s : ℕ) - alpha) / 2 := by
        apply sum_congr rfl
        intro s hs
        have hs' := mem_Icc.mp hs
        rw [boundaryLayerMass_pow_ten_eq k s hs'.1 hs'.2]
      _ ≤ ∑ s ∈ Icc 1 k,
            delta * (q : ℝ) ^ 2 / 2 * ((1 : ℝ) / (10 ^ s : ℕ)) := by
        apply sum_le_sum
        intro s hs
        have hpow : (0 : ℝ) < (10 ^ s : ℕ) := by positivity
        dsimp [alpha] at halpha
        have hdelta0 : 0 ≤ delta := by
          dsimp [delta]
          nlinarith [Real.neg_one_le_cos (Real.pi / q)]
        field_simp
        nlinarith
      _ = delta * (q : ℝ) ^ 2 / 2 *
            (∑ s ∈ Icc 1 k, (1 : ℝ) / (10 ^ s : ℕ)) := by
        rw [mul_sum]
  have hbudgetUpper :
      2 * primitiveBoundaryEndpointBudget q A ≤
        delta * (q : ℝ) ^ 2 / 9 := by
    have hdelta0 : 0 ≤ delta := by
      dsimp [delta]
      nlinarith [Real.neg_one_le_cos (Real.pi / q)]
    have hcoef : 0 ≤ delta * (q : ℝ) ^ 2 / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hsum hcoef
    nlinarith [hlayer]
  have halphaEq := boundaryZeroCoefficient_eq q hq0
  dsimp [alpha, delta] at halphaEq hdelta hbudgetUpper ⊢
  rw [halphaEq]
  field_simp at hdelta ⊢
  nlinarith [hbudgetUpper, sq_pos_of_pos hqR]

/-- Clean scalar form of T153: the displayed primitive-frequency lower bound
forces the target cylinder to be hit by the first `10^k` orbit points. -/
theorem piOrbit_hit_of_primitiveBoundary_ge_neg_861
    (k A : ℕ) (hk : 3 ≤ k) (hA : A < 10 ^ k)
    (hprimitive : -(861 / 1000 : ℝ) ≤
      (primitiveBoundaryFourierSum (10 ^ k) A (10 ^ k)).re) :
    ∃ j : ℕ, j < 10 ^ k ∧ BoundaryRootGridNaturalConsumer.piOrbit j ∈
      Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ)) := by
  apply piOrbit_hit_of_rootGrid_primitiveBoundary_ge k A hk hA
  exact (rootGridNaturalThreshold_lt_neg_861 k A hk).le.trans hprimitive

/-- Contrapositive form: a cylinder missed at the natural horizon forces a
strict primitive-frequency deficit below `-861/1000`. -/
theorem primitiveBoundary_lt_neg_861_of_piOrbit_misses
    (k A : ℕ) (hk : 3 ≤ k) (hA : A < 10 ^ k)
    (hmiss : ¬ ∃ j : ℕ, j < 10 ^ k ∧ BoundaryRootGridNaturalConsumer.piOrbit j ∈
      Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ))) :
    (primitiveBoundaryFourierSum (10 ^ k) A (10 ^ k)).re <
      -(861 / 1000 : ℝ) := by
  by_contra hnot
  exact hmiss (piOrbit_hit_of_primitiveBoundary_ge_neg_861
    k A hk hA (le_of_not_gt hnot))

end Theory.PiDigits.BoundaryNaturalThresholdClosure

#print axioms Theory.PiDigits.BoundaryNaturalThresholdClosure.cosineDeficit_mul_sq_gt_98681_div_20000
#print axioms Theory.PiDigits.BoundaryNaturalThresholdClosure.rootGridNaturalThreshold_lt_neg_861
#print axioms Theory.PiDigits.BoundaryNaturalThresholdClosure.piOrbit_hit_of_primitiveBoundary_ge_neg_861
#print axioms Theory.PiDigits.BoundaryNaturalThresholdClosure.primitiveBoundary_lt_neg_861_of_piOrbit_misses
