import TheoryLib.PiQuantitativeBlockHitting.T102T102BBPKernelIntegral

/-!
# T103: termwise and pointwise BBP kernel bridges

This module connects each canonical kernel term to the corresponding BBP
coefficient and records the pointwise geometric sum.  Interchanging the
infinite sum with the interval integral remains a separate obligation.
-/

noncomputable section

namespace Theory.PiDigits.T103BBPIntegralBridge

open T74ThreePrimaryDecimation T98BBPArchimedeanTerm
open T100BBPRealBridge T102BBPKernelIntegral

private theorem integral_pow_nat (n : ℕ) :
    (∫ x in (0 : ℝ)..bbpUpper, x ^ n) =
      bbpUpper ^ (n + 1) / (n + 1 : ℝ) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) bbpUpper,
      HasDerivAt (fun y : ℝ ↦ y ^ (n + 1) / (n + 1 : ℝ)) (x ^ n) x := by
    intro x _
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (n + 1 : ℝ) using 1 <;>
      simp only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp [hn]
  · exact (continuous_pow n).continuousOn.intervalIntegrable

private theorem bbpUpper_pow_eight : bbpUpper ^ 8 = (1 : ℝ) / 16 := by
  rw [bbpUpper, div_pow,
    show (Real.sqrt 2) ^ 8 = ((Real.sqrt 2) ^ 2) ^ 4 by ring,
    sqrt_two_sq]
  norm_num

private theorem bbpUpper_pow_mul (k n : ℕ) :
    bbpUpper ^ (8 * k + n) = ((1 : ℝ) / 16) ^ k * bbpUpper ^ n := by
  rw [pow_add, pow_mul, bbpUpper_pow_eight]

/-- Each polynomial kernel term integrates to its canonical BBP coefficient. -/
theorem intervalIntegral_bbpKernelTerm (k : ℕ) :
    (∫ x in (0 : ℝ)..bbpUpper, bbpKernelTerm k x) = bbpRealTerm k := by
  have hi (n : ℕ) : IntervalIntegrable (fun x : ℝ ↦ x ^ n)
      MeasureTheory.volume 0 bbpUpper :=
    (continuous_pow n).continuousOn.intervalIntegrable
  have heq : (∫ x in (0 : ℝ)..bbpUpper, bbpKernelTerm k x) =
      ∫ x in (0 : ℝ)..bbpUpper,
        (4 * Real.sqrt 2 * x ^ (8 * k) - 8 * x ^ (8 * k + 3) -
          4 * Real.sqrt 2 * x ^ (8 * k + 4) - 8 * x ^ (8 * k + 5)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [bbpKernelTerm, bbpKernelNumerator]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [heq]
  have hA := (hi (8 * k)).const_mul (4 * Real.sqrt 2)
  have hB := (hi (8 * k + 3)).const_mul 8
  have hC := (hi (8 * k + 4)).const_mul (4 * Real.sqrt 2)
  have hD := (hi (8 * k + 5)).const_mul 8
  rw [intervalIntegral.integral_sub ((hA.sub hB).sub hC) hD,
    intervalIntegral.integral_sub (hA.sub hB) hC,
    intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow_nat, integral_pow_nat, integral_pow_nat, integral_pow_nat]
  simp only [bbpRealTerm, bbpCombinedTerm, poleOne, poleTwo, poleThree, poleFour]
  push_cast
  rw [bbpUpper_pow_mul k 1, bbpUpper_pow_mul k 4,
    bbpUpper_pow_mul k 5, bbpUpper_pow_mul k 6]
  have hu2 : bbpUpper ^ 2 = (1 : ℝ) / 2 := by
    rw [bbpUpper]
    field_simp
    nlinarith [sqrt_two_sq]
  have hsu : Real.sqrt 2 * bbpUpper = 1 := by
    rw [bbpUpper]
    nlinarith [sqrt_two_sq]
  have hu4 : bbpUpper ^ 4 = (1 : ℝ) / 4 := by
    rw [show bbpUpper ^ 4 = (bbpUpper ^ 2) ^ 2 by ring, hu2]
    norm_num
  have hu5 : bbpUpper ^ 5 = bbpUpper / 4 := by
    rw [show bbpUpper ^ 5 = bbpUpper ^ 4 * bbpUpper by ring, hu4]
    ring
  have hu6 : bbpUpper ^ 6 = (1 : ℝ) / 8 := by
    rw [show bbpUpper ^ 6 = (bbpUpper ^ 2) ^ 3 by ring, hu2]
    norm_num
  have hsu5 : Real.sqrt 2 * bbpUpper ^ 5 = (1 : ℝ) / 4 := by
    rw [hu5]
    nlinarith
  simp only [pow_one]
  ring_nf
  rw [hsu, hu4, hsu5, hu6]
  norm_num [div_pow]
  field_simp
  ring

/-- Exact factorization exposing positivity of the kernel numerator. -/
theorem bbpKernelNumerator_eq_factor (x : ℝ) :
    bbpKernelNumerator x =
      8 * (bbpUpper - x) * (x ^ 2 + 1) *
        (x ^ 2 + Real.sqrt 2 * x + 1) := by
  rw [bbpKernelNumerator, bbpUpper]
  ring_nf
  rw [sqrt_two_sq]
  ring

/-- Kernel terms are nonnegative throughout the integration interval. -/
theorem bbpKernelTerm_nonneg_on (k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) bbpUpper) : 0 ≤ bbpKernelTerm k x := by
  rw [bbpKernelTerm, bbpKernelNumerator_eq_factor]
  have hx0 : 0 ≤ x := hx.1
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hux : 0 ≤ bbpUpper - x := sub_nonneg.mpr hx.2
  have hq : 0 ≤ x ^ 2 + Real.sqrt 2 * x + 1 := by
    have hsx : 0 ≤ Real.sqrt 2 * x := mul_nonneg hs hx0
    nlinarith [sq_nonneg x]
  positivity

/-- Pointwise, the polynomial kernel terms sum to the rational kernel. -/
theorem bbpKernelTerm_hasSum (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1) :
    HasSum (fun k : ℕ ↦ bbpKernelTerm k x) (bbpKernel x) := by
  have hr0 : 0 ≤ x ^ 8 := pow_nonneg hx0 _
  have hr1 : x ^ 8 < 1 := pow_lt_one₀ hx0 hx (by norm_num)
  have hg := hasSum_geometric_of_lt_one (r := x ^ 8) hr0 hr1
  have hm := hg.mul_right (bbpKernelNumerator x)
  convert hm using 1
  · funext k
    rw [bbpKernelTerm, pow_mul]
  · rw [bbpKernel]
    ring

end Theory.PiDigits.T103BBPIntegralBridge
