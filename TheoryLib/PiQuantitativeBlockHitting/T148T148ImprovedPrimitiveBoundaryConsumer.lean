import TheoryLib.PiQuantitativeBlockHitting.T147T147BoundaryEndpointContraction

/-!
# T148: improved primitive-boundary consumer

This module only transports T147's unconditional endpoint saving through the
existing exact T139 defect identity and T128 interval-hitting consumer.
-/

noncomputable section

open Set

namespace Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryEndpointContraction

abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- T147 improves the literal endpoint contribution in T139 by `7/250`
before division by the prefix length. -/
theorem directionalBoundaryDefect_lt_primitive_add_improvedEndpointBudget
    (k A N : ℕ) (hk : 3 ≤ k) (hN : 0 < N) :
    directionalBoundaryDefect piOrbit N (10 ^ k)
        ((A : ℝ) / (10 ^ k : ℕ)) <
      -2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re / N +
        (4 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 250) / N := by
  have hq : 0 < 10 ^ k := pow_pos (by norm_num) _
  rw [directionalBoundaryDefect_eq_primitive_add_endpoint (10 ^ k) A N hq]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbre :
      -(primitiveBoundaryEndpoint (10 ^ k) A N).re ≤
        ‖primitiveBoundaryEndpoint (10 ^ k) A N‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hbnorm := primitiveBoundaryEndpoint_norm_lt_two_budget_sub k A N hk
  have hendpoint :
      -2 * (primitiveBoundaryEndpoint (10 ^ k) A N).re <
        4 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 250 := by
    nlinarith
  rw [Complex.add_re]
  calc
    -2 * ((primitiveBoundaryFourierSum (10 ^ k) A N).re +
        (primitiveBoundaryEndpoint (10 ^ k) A N).re) / N <
      (-2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re +
        (4 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 250)) / N := by
          apply (div_lt_div_iff_of_pos_right hNR).2
          linarith
    _ = -2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re / N +
        (4 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 250) / N := by
      ring

/-- Decimal-cylinder hitting with T147's strictly improved endpoint
threshold.  The only remaining premise is the displayed primitive-frequency
arithmetic estimate. -/
theorem piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten
    (k A N : ℕ) (hk : 3 ≤ k) (hA : A < 10 ^ k) (hN : 0 < N)
    (hsmall :
      -2 * (primitiveBoundaryFourierSum (10 ^ k) A N).re / N +
          (4 * primitiveBoundaryEndpointBudget (10 ^ k) A - 7 / 250) / N ≤
        boundaryZeroCoefficient (10 ^ k)) :
    ∃ j : ℕ, j < N ∧ piOrbit j ∈
      Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ)) := by
  have hq : 0 < 10 ^ k := pow_pos (by norm_num) _
  have hdefect :
      directionalBoundaryDefect piOrbit N (10 ^ k)
          ((A : ℝ) / (10 ^ k : ℕ)) < boundaryZeroCoefficient (10 ^ k) :=
    (directionalBoundaryDefect_lt_primitive_add_improvedEndpointBudget
      k A N hk hN).trans_le hsmall
  have haq : (A : ℝ) / (10 ^ k : ℕ) + ((10 ^ k : ℕ) : ℝ)⁻¹ ≤ 1 := by
    have hqR : (0 : ℝ) < (10 ^ k : ℕ) := by exact_mod_cast hq
    have hAle : A + 1 ≤ 10 ^ k := by omega
    have hAleR : ((A + 1 : ℕ) : ℝ) ≤ (10 ^ k : ℕ) := by
      exact_mod_cast hAle
    calc
      (A : ℝ) / (10 ^ k : ℕ) + ((10 ^ k : ℕ) : ℝ)⁻¹ =
          ((A + 1 : ℕ) : ℝ) / (10 ^ k : ℕ) := by
        rw [inv_eq_one_div]
        push_cast
        ring
      _ ≤ ((10 ^ k : ℕ) : ℝ) / (10 ^ k : ℕ) :=
        div_le_div_of_nonneg_right hAleR hqR.le
      _ = 1 := div_self hqR.ne'
  have hhit := finite_decimalInterval_hit_of_boundary_directional_smallness
    piOrbit N (10 ^ k) ((A : ℝ) / (10 ^ k : ℕ)) hN hq
    (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
    (by positivity) haq hdefect
  obtain ⟨j, hjN, hj⟩ := hhit
  refine ⟨j, hjN, ?_⟩
  convert hj using 1 <;> field_simp

end Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer

#print axioms Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer.directionalBoundaryDefect_lt_primitive_add_improvedEndpointBudget
#print axioms Theory.PiDigits.ImprovedPrimitiveBoundaryConsumer.piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten
