import TheoryLib.PiQuantitativeBlockHitting.T101T101BBPIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# T102: evaluation of the elementary BBP kernel integral

This module evaluates the rational kernel naturally associated with the BBP
series.  It does not yet interchange a series with an integral or identify
the canonical BBP series with this integral.
-/

noncomputable section

namespace Theory.PiDigits.T102BBPKernelIntegral

/-- The upper endpoint used in the BBP kernel representation. -/
def bbpUpper : ℝ := Real.sqrt 2 / 2

/-- The polynomial numerator of the BBP kernel. -/
def bbpKernelNumerator (x : ℝ) : ℝ :=
  4 * Real.sqrt 2 - 8 * x ^ 3 -
    4 * Real.sqrt 2 * x ^ 4 - 8 * x ^ 5

/-- The `k`th polynomial kernel term before geometric summation. -/
def bbpKernelTerm (k : ℕ) (x : ℝ) : ℝ :=
  x ^ (8 * k) * bbpKernelNumerator x

/-- The elementary rational BBP kernel. -/
def bbpKernel (x : ℝ) : ℝ := bbpKernelNumerator x / (1 - x ^ 8)

/-- An antiderivative of the BBP kernel on the interval of interest. -/
def bbpPrimitive (x : ℝ) : ℝ :=
  2 * Real.log (x ^ 2 - 1) -
    2 * Real.log (x ^ 2 - Real.sqrt 2 * x + 1) +
    4 * Real.arctan (Real.sqrt 2 * x - 1)

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num

theorem bbpUpper_nonneg : 0 ≤ bbpUpper := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

theorem bbpUpper_lt_one : bbpUpper < 1 := by
  rw [bbpUpper, div_lt_one (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

theorem bbpQuadratic_pos (x : ℝ) :
    0 < x ^ 2 - Real.sqrt 2 * x + 1 := by
  nlinarith [sq_nonneg (x - Real.sqrt 2 / 2), sqrt_two_sq]

/-- Partial-fraction decomposition of the kernel away from its poles. -/
theorem bbpKernel_eq_partialFractions (x : ℝ) (hx : x ^ 8 ≠ 1) :
    bbpKernel x =
      -4 * (x - Real.sqrt 2) / (x ^ 2 - Real.sqrt 2 * x + 1) +
        2 / (x + 1) + 2 / (x - 1) := by
  have hq : x ^ 2 - Real.sqrt 2 * x + 1 ≠ 0 :=
    ne_of_gt (bbpQuadratic_pos x)
  have hq' : x * (x - Real.sqrt 2) + 1 ≠ 0 := by
    intro h
    apply hq
    nlinarith
  have hx1 : x - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hx
    norm_num at hx
  have hxm1 : x + 1 ≠ 0 := by
    intro h
    have heq : x = -1 := by linarith
    rw [heq] at hx
    norm_num at hx
  have hd : 1 - x ^ 8 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [bbpKernel, bbpKernelNumerator]
  field_simp [hd, hx1, hxm1, hq, hq']
  ring_nf
  rw [sqrt_two_sq]
  ring

/-- The displayed primitive differentiates to the kernel on `[0,1)`. -/
theorem bbpPrimitive_hasDerivAt (x : ℝ) (hx0 : 0 ≤ x) (hxlt : x < 1) :
    HasDerivAt bbpPrimitive (bbpKernel x) x := by
  have hx2lt : x ^ 2 < 1 := by
    simpa [pow_two] using mul_self_lt_mul_self hx0 hxlt
  have hx : x ^ 2 ≠ 1 := ne_of_lt hx2lt
  have hx1 : x ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hq : x ^ 2 - Real.sqrt 2 * x + 1 ≠ 0 :=
    ne_of_gt (bbpQuadratic_pos x)
  have hq' : x * (x - Real.sqrt 2) + 1 ≠ 0 := by
    intro h
    apply hq
    nlinarith
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hlog1 := (hpow.sub_const 1).log hx1
  have hqx : HasDerivAt
      (fun y : ℝ ↦ y ^ 2 - Real.sqrt 2 * y + 1)
      (2 * x - Real.sqrt 2) x := by
    convert (hpow.sub
      ((hasDerivAt_id x).const_mul (Real.sqrt 2))).add_const 1 using 1 <;> ring
  have hlogq := hqx.log hq
  have hatan : HasDerivAt
      (fun y : ℝ ↦ Real.arctan (Real.sqrt 2 * y - 1))
      (1 / (1 + (Real.sqrt 2 * x - 1) ^ 2) * Real.sqrt 2) x := by
    convert (((hasDerivAt_id x).const_mul (Real.sqrt 2)).sub_const 1).arctan
      using 1 <;> simp only [id_eq] <;> ring
  have hprim : HasDerivAt bbpPrimitive
      (2 * (2 * x / (x ^ 2 - 1)) -
        2 * ((2 * x - Real.sqrt 2) /
          (x ^ 2 - Real.sqrt 2 * x + 1)) +
        4 * (1 / (1 + (Real.sqrt 2 * x - 1) ^ 2) * Real.sqrt 2)) x := by
    dsimp [bbpPrimitive]
    convert ((hlog1.const_mul 2).sub (hlogq.const_mul 2)).add
      (hatan.const_mul 4) using 1 <;> ring
  convert hprim using 1
  have hx8 : x ^ 8 < 1 := pow_lt_one₀ hx0 hxlt (by norm_num)
  rw [bbpKernel_eq_partialFractions x (ne_of_lt hx8)]
  have hxm : x - 1 ≠ 0 := by nlinarith
  have hxp : x + 1 ≠ 0 := by nlinarith
  have ha : 1 + (Real.sqrt 2 * x - 1) ^ 2 ≠ 0 := by positivity
  field_simp [hx1, hq, hq', hxm, hxp, ha]
  ring_nf
  rw [sqrt_two_sq, show (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 by
    rw [pow_succ, sqrt_two_sq]]
  ring

theorem bbpPrimitive_upper : bbpPrimitive bbpUpper = 0 := by
  rw [bbpPrimitive, bbpUpper]
  have hzero : Real.sqrt 2 * (Real.sqrt 2 / 2) - 1 = 0 := by
    nlinarith [sqrt_two_sq]
  rw [hzero, Real.arctan_zero]
  have h1 : (Real.sqrt 2 / 2) ^ 2 - 1 = -(1 / 2 : ℝ) := by
    nlinarith [sqrt_two_sq]
  have h2 : (Real.sqrt 2 / 2) ^ 2 -
      Real.sqrt 2 * (Real.sqrt 2 / 2) + 1 = (1 / 2 : ℝ) := by
    nlinarith [sqrt_two_sq]
  rw [h1, h2, Real.log_neg_eq_log]
  ring

theorem bbpPrimitive_zero : bbpPrimitive 0 = -Real.pi := by
  simp [bbpPrimitive, Real.arctan_neg, Real.arctan_one]
  ring

/-- Exact evaluation of the elementary BBP kernel integral. -/
theorem intervalIntegral_bbpKernel :
    (∫ x in (0 : ℝ)..bbpUpper, bbpKernel x) = Real.pi := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) bbpUpper,
      HasDerivAt bbpPrimitive (bbpKernel x) x := by
    intro x hx
    rw [Set.uIcc_of_le bbpUpper_nonneg] at hx
    apply bbpPrimitive_hasDerivAt x hx.1
    exact lt_of_le_of_lt hx.2 bbpUpper_lt_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · rw [bbpPrimitive_upper, bbpPrimitive_zero]
    ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le bbpUpper_nonneg] at hx
    have hxlt : x < 1 := lt_of_le_of_lt hx.2 bbpUpper_lt_one
    have hx8 : x ^ 8 < 1 := pow_lt_one₀ hx.1 hxlt (by norm_num)
    have hd : 1 - x ^ 8 ≠ 0 := by nlinarith
    apply ContinuousAt.continuousWithinAt
    unfold bbpKernel bbpKernelNumerator
    fun_prop

end Theory.PiDigits.T102BBPKernelIntegral
