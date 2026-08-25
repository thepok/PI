import TheoryLib.PiQuantitativeBlockHitting.T146T146BoundaryPhaseTorusBounds

/-!
# T147: strict contraction of the actual pi endpoint

The first two decimal valuation layers cannot both have a nearly resonant
initial phase.  Combining that pi-specific separation with the finite Abel
bound gives a fixed saving over the literal two-sided endpoint budget.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.BoundaryEndpointContraction

open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryEndpointLayers
open Theory.PiDigits.BoundaryCoefficientAbel
open Theory.PiDigits.BoundaryLayerMass
open Theory.PiDigits.BoundaryLayerScalarBounds
open Theory.PiDigits.BoundaryPhaseTorusBounds

private lemma pow_ten_ge_thousand (k : ℕ) (hk : 3 ≤ k) :
    1000 ≤ 10 ^ k := by
  calc
    1000 = 10 ^ 3 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk

private lemma sum_range_succ_eq_sum_Icc_one
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, f (i + 1)) = ∑ m ∈ Icc 1 n, f m := by
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [mem_range] at hi
    simp only [mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro m hm
    simp only [mem_Icc] at hm
    refine ⟨m - 1, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro i hi
    rfl

private lemma phase_one_eq_circleExp (t : ℝ) :
    Theory.PiDigits.T27.phase 1 t =
      Theory.Shared.FiniteQuasiconcaveAbel.circleExp t := by
  unfold Theory.PiDigits.T27.phase Theory.Shared.FiniteQuasiconcaveAbel.circleExp
  congr 1
  push_cast
  ring

private lemma boundaryLayerPolynomial_eq_abel
    (q s : ℕ) (t : ℝ) :
    boundaryLayerPolynomial q s t =
      ∑ i ∈ range ((2 * q - 1) / 10 ^ s),
        (positiveBoundaryCoefficient q (10 ^ s * (i + 1)) : ℂ) *
          Theory.Shared.FiniteQuasiconcaveAbel.circleExp t ^ (i + 1) := by
  unfold boundaryLayerPolynomial
  rw [← sum_range_succ_eq_sum_Icc_one]
  apply Finset.sum_congr rfl
  intro i hi
  change (positiveBoundaryCoefficient q (10 ^ s * (i + 1)) : ℂ) *
      Theory.PiDigits.T27.phase ((i + 1 : ℕ) : ℤ) t = _
  rw [Theory.PiDigits.T27.phase_nat_eq_pow, phase_one_eq_circleExp]

private lemma boundaryLayerPolynomial_abel_lt
    (q s : ℕ) (hq : 1000 ≤ q) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖boundaryLayerPolynomial q s t‖ <
      5 / (2 * (q : ℝ) * |Real.sin (Real.pi * t)|) := by
  rw [boundaryLayerPolynomial_eq_abel]
  exact sampled_positiveBoundaryCoefficient_abel_lt q (10 ^ s) hq (by positivity) t hsin

theorem boundaryLayerPolynomial_norm_le_mass
    (q s : ℕ) (hq : 1000 ≤ q) (t : ℝ) :
    ‖boundaryLayerPolynomial q s t‖ ≤ boundaryLayerMass q (10 ^ s) := by
  unfold boundaryLayerPolynomial boundaryLayerMass
  calc
    ‖∑ m ∈ Icc 1 ((2 * q - 1) / 10 ^ s),
        (positiveBoundaryCoefficient q (10 ^ s * m) : ℂ) *
          Theory.PiDigits.T27.phase (m : ℤ) t‖ ≤
        ∑ m ∈ Icc 1 ((2 * q - 1) / 10 ^ s),
          ‖(positiveBoundaryCoefficient q (10 ^ s * m) : ℂ) *
            Theory.PiDigits.T27.phase (m : ℤ) t‖ := norm_sum_le _ _
    _ = ∑ m ∈ Icc 1 ((2 * q - 1) / 10 ^ s),
          positiveBoundaryCoefficient q (10 ^ s * m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm' := mem_Icc.mp hm
      have hfreq : 10 ^ s * m ≤ 2 * q - 1 :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (by positivity : 0 < 10 ^ s)).1 hm'.2
      have hpos := positiveBoundaryCoefficient_pos q (10 ^ s * m) hq
        (Nat.mul_pos (by positivity) (by omega)) hfreq
      rw [norm_mul, Theory.PiDigits.T27.norm_phase, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    _ = ∑ i ∈ range ((2 * q - 1) / 10 ^ s),
          positiveBoundaryCoefficient q (10 ^ s * (i + 1)) :=
      (sum_range_succ_eq_sum_Icc_one
        (fun m => positiveBoundaryCoefficient q (10 ^ s * m))
        ((2 * q - 1) / 10 ^ s)).symm

/-- The literal T139 endpoint budget is exactly the sum of its decimal layer
masses.  In particular it is independent of the cylinder center `A`. -/
theorem primitiveBoundaryEndpointBudget_eq_sum_layerMasses
    (k A : ℕ) (hk : 3 ≤ k) :
    primitiveBoundaryEndpointBudget (10 ^ k) A =
      ∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s) := by
  have hq := pow_ten_ge_thousand k hk
  unfold primitiveBoundaryEndpointBudget
  calc
    (∑ h ∈ positiveBoundarySupport (10 ^ k),
        tenValuation h * ‖centeredBoundaryTerm (10 ^ k) A h‖) =
      ∑ h ∈ positiveBoundarySupport (10 ^ k),
        ∑ _j ∈ range (tenValuation h),
          positiveBoundaryCoefficient (10 ^ k) h := by
      apply Finset.sum_congr rfl
      intro h hh
      have hh' := mem_Icc.mp hh
      have hpos := positiveBoundaryCoefficient_pos (10 ^ k) h hq (by omega) hh'.2
      simp only [centeredBoundaryTerm, norm_mul, Theory.PiDigits.T27.norm_phase,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
        sum_const, card_range, nsmul_eq_mul]
    _ = ∑ s ∈ Icc 1 k,
        ∑ m ∈ Icc 1 ((2 * 10 ^ k - 1) / 10 ^ s),
          positiveBoundaryCoefficient (10 ^ k) (10 ^ s * m) :=
      sum_valuation_eq_sum_decimal_layers k
        (positiveBoundaryCoefficient (10 ^ k))
    _ = ∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s) := by
      apply Finset.sum_congr rfl
      intro s hs
      unfold boundaryLayerMass
      exact (sum_range_succ_eq_sum_Icc_one
        (fun m => positiveBoundaryCoefficient (10 ^ k) (10 ^ s * m))
        ((2 * 10 ^ k - 1) / 10 ^ s)).symm

private lemma sum_layer_norm_lt_budget_sub
    (k r : ℕ) (hk : 3 ≤ k) (hr : r ∈ Icc 1 k) (t : ℕ → ℝ)
    (hspecial : ‖boundaryLayerPolynomial (10 ^ k) r (t r)‖ <
      boundaryLayerMass (10 ^ k) (10 ^ r) - 7 / 500) :
    (∑ s ∈ Icc 1 k, ‖boundaryLayerPolynomial (10 ^ k) s (t s)‖) <
      (∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s)) - 7 / 500 := by
  have hq := pow_ten_ge_thousand k hk
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Icc 1 k)
      (f := fun s => ‖boundaryLayerPolynomial (10 ^ k) s (t s)‖) (i := r)
      (fun hnot => (hnot hr).elim),
    Finset.sum_eq_add_sum_diff_singleton (s := Icc 1 k)
      (f := fun s => boundaryLayerMass (10 ^ k) (10 ^ s)) (i := r)
      (fun hnot => (hnot hr).elim)]
  have hrest :
      (∑ s ∈ Icc 1 k \ {r}, ‖boundaryLayerPolynomial (10 ^ k) s (t s)‖) ≤
        ∑ s ∈ Icc 1 k \ {r}, boundaryLayerMass (10 ^ k) (10 ^ s) := by
    apply Finset.sum_le_sum
    intro s hs
    exact boundaryLayerPolynomial_norm_le_mass (10 ^ k) s hq (t s)
  linarith

theorem initial_layers_strict_saving
    (k A : ℕ) (hk : 3 ≤ k) :
    ‖∑ s ∈ Icc 1 k,
        boundaryLayerPolynomial (10 ^ k) s
          (Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A)‖ <
      (∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s)) - 7 / 500 := by
  let t : ℕ → ℝ := fun s =>
    Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A
  have hq := pow_ten_ge_thousand k hk
  have htriangle :
      ‖∑ s ∈ Icc 1 k, boundaryLayerPolynomial (10 ^ k) s (t s)‖ ≤
        ∑ s ∈ Icc 1 k, ‖boundaryLayerPolynomial (10 ^ k) s (t s)‖ :=
    norm_sum_le _ _
  rcases decimal_center_phase_distance_dichotomy (10 ^ k) A with hfirst | hsecond
  · have hsine := sin_pi_mul_le_abs_sin_of_le_distance
      (7 / 1000) (t 1) (by norm_num) (by simpa [t] using hfirst)
    have hsine' : Real.sin (7 * Real.pi / 1000) ≤
        |Real.sin (Real.pi * t 1)| := by
      convert hsine using 1 <;> ring
    have habs : 219 / 10000 < |Real.sin (Real.pi * t 1)| :=
      sine_seven_pi_div_thousand_gt.trans_le hsine'
    have hsin : Real.sin (Real.pi * t 1) ≠ 0 := by
      exact fun hz => by rw [hz, abs_zero] at habs; norm_num at habs
    have habel := boundaryLayerPolynomial_abel_lt (10 ^ k) 1 hq (t 1) hsin
    have hqR : (1000 : ℝ) ≤ (10 ^ k : ℕ) := by exact_mod_cast hq
    have hden : 0 < 2 * ((10 ^ k : ℕ) : ℝ) * |Real.sin (Real.pi * t 1)| := by
      positivity
    have hdenLower : 219 / 5 <
        2 * ((10 ^ k : ℕ) : ℝ) * |Real.sin (Real.pi * t 1)| := by
      have hmul := mul_le_mul_of_nonneg_right hqR (abs_nonneg (Real.sin (Real.pi * t 1)))
      nlinarith
    have hdiv : 5 / (2 * ((10 ^ k : ℕ) : ℝ) *
        |Real.sin (Real.pi * t 1)|) < 25 / 219 := by
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hmass := boundaryLayerMass_ten_gt k hk
    have hspecial : ‖boundaryLayerPolynomial (10 ^ k) 1 (t 1)‖ <
        boundaryLayerMass (10 ^ k) (10 ^ 1) - 7 / 500 := by
      norm_num
      nlinarith
    exact htriangle.trans_lt (sum_layer_norm_lt_budget_sub k 1 hk
      (by simp; omega) t hspecial)
  · have hsine := sin_pi_mul_le_abs_sin_of_le_distance
      (19 / 100) (t 2) (by norm_num) (by norm_num [t] at hsecond ⊢; exact hsecond)
    have hsine' : Real.sin (19 * Real.pi / 100) ≤
        |Real.sin (Real.pi * t 2)| := by
      convert hsine using 1 <;> ring
    have habs : 561 / 1000 < |Real.sin (Real.pi * t 2)| :=
      sine_nineteen_pi_div_hundred_gt.trans_le hsine'
    have hsin : Real.sin (Real.pi * t 2) ≠ 0 := by
      exact fun hz => by rw [hz, abs_zero] at habs; norm_num at habs
    have habel := boundaryLayerPolynomial_abel_lt (10 ^ k) 2 hq (t 2) hsin
    have hqR : (1000 : ℝ) ≤ (10 ^ k : ℕ) := by exact_mod_cast hq
    have hden : 0 < 2 * ((10 ^ k : ℕ) : ℝ) * |Real.sin (Real.pi * t 2)| := by
      positivity
    have hdenLower : 1000 <
        2 * ((10 ^ k : ℕ) : ℝ) * |Real.sin (Real.pi * t 2)| := by
      have hmul := mul_le_mul_of_nonneg_right hqR (abs_nonneg (Real.sin (Real.pi * t 2)))
      nlinarith
    have hdiv : 5 / (2 * ((10 ^ k : ℕ) : ℝ) *
        |Real.sin (Real.pi * t 2)|) < 1 / 200 := by
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hmass := boundaryLayerMass_hundred_gt k hk
    have hspecial : ‖boundaryLayerPolynomial (10 ^ k) 2 (t 2)‖ <
        boundaryLayerMass (10 ^ k) (10 ^ 2) - 7 / 500 := by
      norm_num
      nlinarith
    exact htriangle.trans_lt (sum_layer_norm_lt_budget_sub k 2 hk
      (by simp; omega) t hspecial)

/-- The actual pi endpoint has a uniform strict saving over the literal
two-sided T139 budget at every decimal scale `10^k`, `k >= 3`. -/
theorem primitiveBoundaryEndpoint_norm_lt_two_budget_sub
    (k A N : ℕ) (hk : 3 ≤ k) :
    ‖primitiveBoundaryEndpoint (10 ^ k) A N‖ <
      2 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 500 := by
  let E : ℝ := ∑ s ∈ Icc 1 k, boundaryLayerMass (10 ^ k) (10 ^ s)
  have hq := pow_ten_ge_thousand k hk
  have hterminal :
      ‖∑ s ∈ Icc 1 k,
          boundaryLayerPolynomial (10 ^ k) s
            ((10 : ℝ) ^ N * Real.pi -
              10 ^ s * decimalCylinderCenter (10 ^ k) A)‖ ≤ E := by
    calc
      _ ≤ ∑ s ∈ Icc 1 k,
          ‖boundaryLayerPolynomial (10 ^ k) s
            ((10 : ℝ) ^ N * Real.pi -
              10 ^ s * decimalCylinderCenter (10 ^ k) A)‖ := norm_sum_le _ _
      _ ≤ E := by
        dsimp [E]
        apply Finset.sum_le_sum
        intro s hs
        exact boundaryLayerPolynomial_norm_le_mass (10 ^ k) s hq _
  have hinitial := initial_layers_strict_saving k A hk
  rw [primitiveBoundaryEndpoint_eq_layer_terminal_sub_initial]
  have hnorm := norm_sub_le
    (∑ s ∈ Icc 1 k,
      boundaryLayerPolynomial (10 ^ k) s
        ((10 : ℝ) ^ N * Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A))
    (∑ s ∈ Icc 1 k,
      boundaryLayerPolynomial (10 ^ k) s
        (Real.pi - 10 ^ s * decimalCylinderCenter (10 ^ k) A))
  have hbudget := primitiveBoundaryEndpointBudget_eq_sum_layerMasses k A hk
  dsimp [E] at hterminal
  rw [hbudget]
  nlinarith

end Theory.PiDigits.BoundaryEndpointContraction

#print axioms Theory.PiDigits.BoundaryEndpointContraction.primitiveBoundaryEndpointBudget_eq_sum_layerMasses
#print axioms Theory.PiDigits.BoundaryEndpointContraction.primitiveBoundaryEndpoint_norm_lt_two_budget_sub
