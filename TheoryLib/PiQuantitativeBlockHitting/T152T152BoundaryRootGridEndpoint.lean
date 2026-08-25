import TheoryLib.PiQuantitativeBlockHitting.T151T151BoundaryProjectedLayerFloor
import TheoryLib.PiQuantitativeBlockHitting.T147T147BoundaryEndpointContraction

/-!
# T152: terminal root-grid contraction of the exact endpoint

The first two terminal decimal layers are bounded by T151's root-grid
projection instead of their coefficient masses.  The initial side retains
T147's independent strict saving.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.BoundaryRootGridEndpoint

open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryEndpointLayers
open Theory.PiDigits.BoundaryEndpointContraction
open Theory.PiDigits.BoundaryLayerMass
open Theory.PiDigits.BoundaryLayerScalarBounds
open Theory.PiDigits.BoundaryRootGridProjection
open Theory.PiDigits.BoundaryProjectedLayerFloor

private lemma pow_ten_ge_thousand (k : ℕ) (hk : 3 ≤ k) :
    1000 ≤ 10 ^ k := by
  calc
    1000 = 10 ^ 3 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- The exact endpoint gains `52909/200000` over the literal two-sided
endpoint budget.  This is a real-part statement, not a norm estimate. -/
theorem primitiveBoundaryEndpoint_re_gt_neg_two_budget_add
    (k A N : ℕ) (hk : 3 ≤ k) :
    -2 * primitiveBoundaryEndpointBudget (10 ^ k) A + 52909 / 200000 <
      (primitiveBoundaryEndpoint (10 ^ k) A N).re := by
  classical
  let q : ℕ := 10 ^ k
  let S : Finset ℕ := Icc 1 k
  let R : Finset ℕ := (S \ {1}) \ {2}
  let tt : ℕ → ℝ := fun s =>
    (10 : ℝ) ^ N * Real.pi - 10 ^ s * decimalCylinderCenter q A
  let ti : ℕ → ℝ := fun s =>
    Real.pi - 10 ^ s * decimalCylinderCenter q A
  let M : ℕ → ℝ := fun s => boundaryLayerMass q (10 ^ s)
  let P : ℕ → ℂ := fun s => boundaryLayerPolynomial q s (tt s)
  have hq : 1000 ≤ q := by exact pow_ten_ge_thousand k hk
  have h1S : 1 ∈ S := by dsimp [S]; simp; omega
  have h2S : 2 ∈ S := by dsimp [S]; simp; omega
  have h2diff : 2 ∈ S \ {1} := by simp [h2S]
  have h1 :
      -(193 / 20000 : ℝ) - 40 / (q : ℝ) ^ 2 -
          boundaryZeroCoefficient q / 2 < (P 1).re := by
    rw [show P 1 = divisibleBoundaryPolynomial q 10 (tt 1) by
      dsimp [P]
      simpa using boundaryLayerPolynomial_eq_divisible q 1 (tt 1)]
    have h := divisibleBoundaryPolynomial_re_gt q 10 hq (by norm_num) (tt 1)
    norm_num at h ⊢
    convert h using 1 <;> ring
  have h2 :
      -(193 / 200000 : ℝ) - 4400 / (q : ℝ) ^ 2 -
          boundaryZeroCoefficient q / 2 < (P 2).re := by
    rw [show P 2 = divisibleBoundaryPolynomial q 100 (tt 2) by
      dsimp [P]
      simpa using boundaryLayerPolynomial_eq_divisible q 2 (tt 2)]
    have h := divisibleBoundaryPolynomial_re_gt q 100 hq (by norm_num) (tt 2)
    norm_num at h ⊢
    convert h using 1 <;> ring
  have hrest : -(∑ s ∈ R, M s) ≤ (∑ s ∈ R, P s).re := by
    have hreSum : (∑ s ∈ R, P s).re = ∑ s ∈ R, (P s).re := by
      simp
    rw [hreSum]
    change -(∑ s ∈ R, M s) ≤ ∑ s ∈ R, (P s).re
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have hnorm := boundaryLayerPolynomial_norm_le_mass q s hq (tt s)
    have habs := Complex.abs_re_le_norm (P s)
    nlinarith [neg_le_abs (P s).re]
  have hMeq : (∑ s ∈ S, M s) = M 1 + M 2 + ∑ s ∈ R, M s := by
    rw [sum_eq_add_sum_diff_singleton 1 M (fun h => (h h1S).elim)]
    rw [sum_eq_add_sum_diff_singleton 2 M (fun h => (h h2diff).elim)]
    dsimp [R]
    ring
  have hPeq : (∑ s ∈ S, P s).re = (P 1).re + (P 2).re +
      (∑ s ∈ R, P s).re := by
    rw [sum_eq_add_sum_diff_singleton 1 P (fun h => (h h1S).elim)]
    rw [sum_eq_add_sum_diff_singleton 2 P (fun h => (h h2diff).elim)]
    simp only [map_add, Complex.add_re]
    dsimp [R]
    ring
  have hM1 := boundaryLayerMass_ten_gt k hk
  have hM2 := boundaryLayerMass_hundred_gt k hk
  have hzeroRaw := boundaryZeroCoefficient_lt_twelve_div_five_mul q hq
  have hqR : (1000 : ℝ) ≤ q := by exact_mod_cast hq
  have hzero : boundaryZeroCoefficient q < 3 / 1250 := by
    calc
      boundaryZeroCoefficient q < 12 / (5 * (q : ℝ)) := hzeroRaw
      _ ≤ 3 / 1250 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * q)).2
        nlinarith
  have hqSq : (1000000 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hqSqPos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have herrors : 40 / (q : ℝ) ^ 2 + 4400 / (q : ℝ) ^ 2 ≤
      111 / 25000 := by
    rw [← add_div]
    apply (div_le_iff₀ hqSqPos).2
    nlinarith
  change 49 / 200 < M 1 at hM1
  change 23 / 1000 < M 2 at hM2
  have hterminal :
      -(∑ s ∈ S, M s) + 50109 / 200000 < (∑ s ∈ S, P s).re := by
    rw [hMeq, hPeq]
    nlinarith
  have hinitial := initial_layers_strict_saving k A hk
  have hbudget := primitiveBoundaryEndpointBudget_eq_sum_layerMasses k A hk
  have hinitialRe : (∑ s ∈ S,
      boundaryLayerPolynomial q s (ti s)).re <
        (∑ s ∈ S, M s) - 7 / 500 := by
    have hre := Complex.re_le_norm
      (∑ s ∈ S, boundaryLayerPolynomial q s (ti s))
    exact hre.trans_lt (by simpa [q, S, ti, M] using hinitial)
  rw [primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial]
  rw [Complex.sub_re]
  dsimp [q, S, M, P, tt, ti] at hterminal hinitialRe
  rw [hbudget]
  nlinarith

end Theory.PiDigits.BoundaryRootGridEndpoint

#print axioms Theory.PiDigits.BoundaryRootGridEndpoint.primitiveBoundaryEndpoint_re_gt_neg_two_budget_add
