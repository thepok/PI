import TheoryLib.PiQuantitativeBlockHitting.T152T152BoundaryRootGridEndpoint

/-!
# T153: exact natural-horizon consumer for the root-grid endpoint

This transports T152 through the existing exact defect identity.  The only
remaining premise is the displayed primitive-frequency real-part bound.
-/

noncomputable section

open Set

namespace Theory.PiDigits.BoundaryRootGridNaturalConsumer

open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.BoundaryRootGridEndpoint

abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- At the natural horizon `N = q`, the exact root-grid threshold is enough
for the corresponding decimal cylinder hit. -/
theorem piOrbit_hit_of_rootGrid_primitiveBoundary_ge
    (k A : ℕ) (hk : 3 ≤ k) (hA : A < 10 ^ k)
    (hprimitive :
      2 * primitiveBoundaryEndpointBudget (10 ^ k) A - 52909 / 200000 -
          ((10 ^ k : ℕ) : ℝ) * boundaryZeroCoefficient (10 ^ k) / 2 ≤
        (primitiveBoundaryFourierSum (10 ^ k) A (10 ^ k)).re) :
    ∃ j : ℕ, j < 10 ^ k ∧ piOrbit j ∈
      Ico ((A : ℝ) / (10 ^ k : ℕ))
        (((A : ℝ) + 1) / (10 ^ k : ℕ)) := by
  let q : ℕ := 10 ^ k
  have hq : 0 < q := pow_pos (by norm_num) _
  have hendpoint := primitiveBoundaryEndpoint_re_gt_neg_two_budget_add k A q hk
  have hsum :
      -(q : ℝ) * boundaryZeroCoefficient q / 2 <
        (primitiveBoundaryFourierSum q A q +
          primitiveBoundaryEndpoint q A q).re := by
    rw [Complex.add_re]
    dsimp [q] at hprimitive hendpoint ⊢
    nlinarith
  have hdefect :
      directionalBoundaryDefect piOrbit q q ((A : ℝ) / q) <
        boundaryZeroCoefficient q := by
    rw [directionalBoundaryDefect_eq_primitive_add_endpoint q A q hq]
    have hqR : (0 : ℝ) < q := by positivity
    apply (div_lt_iff₀ hqR).2
    nlinarith
  have haq : (A : ℝ) / q + (q : ℝ)⁻¹ ≤ 1 := by
    have hqR : (0 : ℝ) < q := by positivity
    have hAle : A + 1 ≤ q := by dsimp [q]; omega
    have hAleR : ((A + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hAle
    calc
      (A : ℝ) / q + (q : ℝ)⁻¹ = ((A + 1 : ℕ) : ℝ) / q := by
        rw [inv_eq_one_div]
        push_cast
        ring
      _ ≤ (q : ℝ) / q := div_le_div_of_nonneg_right hAleR hqR.le
      _ = 1 := div_self hqR.ne'
  have hhit := finite_decimalInterval_hit_of_boundary_directional_smallness
    piOrbit q q ((A : ℝ) / q) hq hq
    (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
    (by positivity) haq hdefect
  obtain ⟨j, hjq, hj⟩ := hhit
  refine ⟨j, by simpa [q] using hjq, ?_⟩
  dsimp [q] at hj ⊢
  convert hj using 1 <;> field_simp

end Theory.PiDigits.BoundaryRootGridNaturalConsumer

#print axioms Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge
