import TheoryLib.PiQuantitativeBlockHitting.T124T124DirectionalJacksonFrontier

/-!
# T128: boundary-matched finite Fourier kernel

This file replaces the Jackson kernel's inner positive radius by the exact
boundary of an interval of length `1 / q`.  It proves the finite Fourier
closed form and the outside-sign statement needed by the existing generic
directional consumer.  It does not prove cancellation for the decimal orbit
of pi.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.BoundaryMatchedKernel

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.DirectionalJacksonFrontier

/-- Coefficients of the boundary-matched cosine--Fejer-squared kernel, on the
same finite index type and frequencies as the order-`q` Jackson kernel. -/
def boundaryCoefficient (q : ℕ) : JacksonIndex q → ℝ
  | Sum.inl _ => (1 - Real.cos (Real.pi / q)) / (q : ℝ) ^ 2
  | Sum.inr (i, j) => -(edgeSign i * edgeSign j) / (2 * (q : ℝ) ^ 2)

/-- The explicit finite Fourier presentation of the boundary-matched
kernel. -/
def boundaryMinorant (q : ℕ) (t : ℝ) : ℂ :=
  ∑ i : JacksonIndex q,
    boundaryCoefficient q i * Theory.PiDigits.T27.phase (jacksonFrequency i) t

/-- Its signed zero-frequency coefficient after equal frequencies are
collected. -/
def boundaryZeroCoefficient (q : ℕ) : ℝ :=
  aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) 0

private lemma boundaryMainSum_eq (q : ℕ) (hq : 0 < q) (t : ℝ) :
    (∑ x : Fin q × Fin q × Fin q × Fin q,
      boundaryCoefficient q (Sum.inl x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inl x)) t) =
      ((1 - Real.cos (Real.pi / q)) * fejerFactor q t ^ 2 : ℝ) := by
  classical
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [boundaryCoefficient, jacksonFrequency]
  simp_rw [Theory.PiDigits.T27.phase_add]
  have hp := pairPhaseSum_eq q t
  push_cast at hp ⊢
  simp_rw [div_eq_mul_inv]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [hp]
  field_simp

private lemma boundaryEdgeSum_eq (q : ℕ) (hq : 0 < q) (t : ℝ) :
    (∑ x : (Bool × Fin q) × (Bool × Fin q),
      boundaryCoefficient q (Sum.inr x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inr x)) t) =
      -(1 / 2 : ℝ) * Complex.normSq (edgeValue q t) := by
  simpa only [boundaryCoefficient, jacksonCoefficient] using
    jacksonEdgeSum_eq q hq t

private lemma phase_one_re_eq_cos (t : ℝ) :
    (Theory.PiDigits.T27.phase 1 t).re = Real.cos (2 * Real.pi * t) := by
  rw [show Theory.PiDigits.T27.phase 1 t =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
    unfold Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring]
  exact Complex.exp_ofReal_mul_I_re _

private lemma normSq_one_sub_phase_one (t : ℝ) :
    Complex.normSq (1 - Theory.PiDigits.T27.phase 1 t) =
      2 * (1 - Real.cos (2 * Real.pi * t)) := by
  have hnorm : Complex.normSq (Theory.PiDigits.T27.phase 1 t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
    norm_num
  rw [Complex.normSq_sub, Complex.normSq_one, hnorm]
  simp only [one_mul, Complex.conj_re]
  rw [phase_one_re_eq_cos]
  ring

/-- Exact closed form of the finite Fourier presentation. -/
theorem boundaryMinorant_eq (q : ℕ) (hq : 0 < q) (t : ℝ) :
    boundaryMinorant q t =
      ((Real.cos (2 * Real.pi * t) - Real.cos (Real.pi / q)) *
        fejerFactor q t ^ 2 : ℝ) := by
  rw [boundaryMinorant, Fintype.sum_sum_type, boundaryMainSum_eq q hq t,
    boundaryEdgeSum_eq q hq t, edgeValue_eq q hq,
    Complex.normSq_mul, normSq_one_sub_phase_one]
  have hreal : Complex.normSq (fejerFactor q t : ℂ) = fejerFactor q t ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [hreal]
  push_cast
  ring

/-- The boundary-matched main coefficient dominates the Jackson main
coefficient.  The non-strict chord bound suffices for this comparison. -/
lemma two_div_sq_le_one_sub_cos_pi_div (q : ℕ) (hq : 0 < q) :
    2 / (q : ℝ) ^ 2 ≤ 1 - Real.cos (Real.pi / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let y : ℝ := Real.pi / (2 * q)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyhalf : y ≤ Real.pi / 2 := by
    dsimp [y]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    norm_num
    exact_mod_cast hq
  have hs := Real.mul_le_sin hy0 hyhalf
  have hs' : 1 / (q : ℝ) ≤ Real.sin y := by
    calc
      1 / (q : ℝ) = 2 / Real.pi * y := by
        dsimp [y]
        field_simp
      _ ≤ Real.sin y := hs
  have hleft : 0 ≤ 1 / (q : ℝ) := by positivity
  have hsin : 0 ≤ Real.sin y := hleft.trans hs'
  have hsq : (1 / (q : ℝ)) ^ 2 ≤ Real.sin y ^ 2 :=
    (sq_le_sq₀ hleft hsin).2 hs'
  have hcos : Real.cos (Real.pi / q) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / (q : ℝ) = 2 * y by
      dsimp [y]
      field_simp]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  calc
    2 / (q : ℝ) ^ 2 = 2 * (1 / (q : ℝ)) ^ 2 := by field_simp
    _ ≤ 2 * Real.sin y ^ 2 := by gcongr
    _ = 1 - (1 - 2 * Real.sin y ^ 2) := by ring

/-- Every boundary-matched coefficient is at least its coefficient in the
order-`q` Jackson presentation. -/
lemma jacksonCoefficient_le_boundaryCoefficient (q : ℕ) (hq : 0 < q)
    (i : JacksonIndex q) :
    jacksonCoefficient q q i ≤ boundaryCoefficient q i := by
  rcases i with i | i
  · simp only [jacksonCoefficient, boundaryCoefficient]
    exact div_le_div_of_nonneg_right
      (two_div_sq_le_one_sub_cos_pi_div q hq) (sq_nonneg _)
  · rfl

/-- The new signed zero mode retains the existing explicit positive Jackson
lower bound.  Its sharper closed form is deliberately left separate from the
finite hitting consumer. -/
theorem boundaryZeroCoefficient_lower (q : ℕ) (hq : 0 < q) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      boundaryZeroCoefficient q := by
  calc
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
        aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 :=
      Theory.PiDigits.ExactNaturalScaleResonance.jackson_zeroCoefficient_self_lower q hq
    _ ≤ boundaryZeroCoefficient q := by
      unfold aggregatedCoefficient boundaryZeroCoefficient
      exact Finset.sum_le_sum fun i _ =>
        jacksonCoefficient_le_boundaryCoefficient q hq i

private lemma cos_two_pi_le_cos_pi_div_of_far
    {q : ℕ} {u : ℝ} (hq : 0 < q)
    (hlow : (q : ℝ)⁻¹ / 2 ≤ |u|)
    (hhigh : |u| ≤ 1 - (q : ℝ)⁻¹ / 2) :
    Real.cos (2 * Real.pi * u) ≤ Real.cos (Real.pi / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcosAbs : Real.cos (2 * Real.pi * u) =
      Real.cos (2 * Real.pi * |u|) := by
    calc
      Real.cos (2 * Real.pi * u) = Real.cos |2 * Real.pi * u| :=
        (Real.cos_abs _).symm
      _ = Real.cos (2 * Real.pi * |u|) := by
        rw [abs_mul, abs_of_pos Real.two_pi_pos]
  rw [hcosAbs]
  by_cases hhalf : |u| ≤ (1 / 2 : ℝ)
  · have hargLow : Real.pi / q ≤ 2 * Real.pi * |u| := by
      rw [div_eq_mul_inv]
      have hbase : (q : ℝ)⁻¹ ≤ 2 * |u| := by linarith
      nlinarith [Real.pi_pos]
    have hargHigh : 2 * Real.pi * |u| ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hargHigh hargLow
  · have hhalf' : (1 / 2 : ℝ) < |u| := lt_of_not_ge hhalf
    have hargLow : Real.pi / q ≤ 2 * Real.pi * (1 - |u|) := by
      rw [div_eq_mul_inv]
      have hbase : (q : ℝ)⁻¹ ≤ 2 * (1 - |u|) := by linarith
      nlinarith [Real.pi_pos]
    have hargHigh : 2 * Real.pi * (1 - |u|) ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have hperiod : Real.cos (2 * Real.pi * |u|) =
        Real.cos (2 * Real.pi * (1 - |u|)) := by
      calc
        Real.cos (2 * Real.pi * |u|) =
            Real.cos (2 * Real.pi - 2 * Real.pi * |u|) :=
              (Real.cos_two_pi_sub _).symm
        _ = Real.cos (2 * Real.pi * (1 - |u|)) := by ring_nf
    rw [hperiod]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hargHigh hargLow

/-- The boundary-matched polynomial is nonpositive at every point outside
the given interval of length `1 / q`; its sign change occurs at the actual
cylinder boundary rather than at the narrower Jackson radius. -/
theorem boundaryMinorant_re_nonpos_outside
    (q : ℕ) (hq : 0 < q) (x a : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (ha : 0 ≤ a)
    (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hout : x ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    (boundaryMinorant q
      (x - (a + (q : ℝ)⁻¹ / 2))).re ≤ 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let u := x - (a + (q : ℝ)⁻¹ / 2)
  have hfar : (q : ℝ)⁻¹ / 2 ≤ |u| := by
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hout
    rcases hout with hleft | hright
    · exact (show (q : ℝ)⁻¹ / 2 ≤ -u by dsimp [u]; linarith).trans
        (neg_le_abs _)
    · exact (show (q : ℝ)⁻¹ / 2 ≤ u by dsimp [u]; linarith).trans
        (le_abs_self _)
  have hnear : |u| ≤ 1 - (q : ℝ)⁻¹ / 2 := by
    rw [abs_le]
    dsimp [u]
    constructor <;> linarith [hx.1, hx.2.le]
  have hcos := cos_two_pi_le_cos_pi_div_of_far hq hfar hnear
  rw [boundaryMinorant_eq q hq]
  change (Real.cos (2 * Real.pi * u) - Real.cos (Real.pi / q)) *
      fejerFactor q u ^ 2 ≤ 0
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcos) (sq_nonneg _)

/-- The boundary-matched directional defect, with the same centering
convention as T124. -/
def directionalBoundaryDefect (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) : ℝ :=
  normalizedDirectionalFourierDefect
    (boundaryCoefficient q) (@jacksonFrequency q) x N
      (a + (q : ℝ)⁻¹ / 2)

/-- Avoiding a decimal interval forces the boundary directional defect above
the exact signed zero coefficient of the new finite polynomial. -/
theorem finite_empty_decimalInterval_boundary_directional_obstruction
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    boundaryZeroCoefficient q ≤ directionalBoundaryDefect x N q a := by
  unfold directionalBoundaryDefect boundaryZeroCoefficient
  refine finiteFourierPresentation_directional_obstruction
    (boundaryCoefficient q) (@jacksonFrequency q) x N
      (a + (q : ℝ)⁻¹ / 2) _ hN (le_refl _) ?_
  intro j hj
  simpa only [boundaryMinorant] using
    boundaryMinorant_re_nonpos_outside q hq (x j) a (hx j hj) ha haq
      (hempty j hj)

/-- A directional defect strictly below the new kernel's zero coefficient
forces a point in the prescribed interval. -/
theorem finite_decimalInterval_hit_of_boundary_directional_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : directionalBoundaryDefect x N q a < boundaryZeroCoefficient q) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  exact (not_lt_of_ge (finite_empty_decimalInterval_boundary_directional_obstruction
    x N q a hN hq hx ha haq (fun j hj => hno j hj))) hsmall

/-- A fully explicit sufficient threshold, inherited from the verified exact
Jackson zero-mode bound. -/
theorem finite_decimalInterval_hit_of_boundary_explicit_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : directionalBoundaryDefect x N q a <
      1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  apply finite_decimalInterval_hit_of_boundary_directional_smallness
    x N q a hN hq hx ha haq
  exact hsmall.trans_le (boundaryZeroCoefficient_lower q hq)

end Theory.PiDigits.BoundaryMatchedKernel

#print axioms Theory.PiDigits.BoundaryMatchedKernel.boundaryMinorant_eq
#print axioms Theory.PiDigits.BoundaryMatchedKernel.boundaryMinorant_re_nonpos_outside
#print axioms Theory.PiDigits.BoundaryMatchedKernel.finite_decimalInterval_hit_of_boundary_directional_smallness
#print axioms Theory.PiDigits.BoundaryMatchedKernel.finite_decimalInterval_hit_of_boundary_explicit_smallness
