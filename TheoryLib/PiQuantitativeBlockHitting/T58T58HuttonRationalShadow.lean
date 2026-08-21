import TheoryLib.PiQuantitativeBlockHitting.T36T36MachinGridStability

/-!
# T58: an exact rational Hutton bracket for pi

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module applies the rational arctangent infrastructure from T36 to
Hutton's identity

`pi / 4 = 2 * arctan (1 / 3) + arctan (1 / 7)`.

Equal adjacent even and odd Taylor truncations give explicit rational lower
and upper bounds for pi.  Their difference is exactly the sum of the two
first omitted terms, so it is a fully computable bracket width.  These
results prove no decimal-cylinder hit, distribution statement, or
every-word statement for pi.
-/

noncomputable section

namespace Theory.PiDigits.HuttonRationalShadow

open Theory.PiDigits.MachinGridStability

/-- The Hutton lower approximant obtained from equal even Taylor
truncations at `1/3` and `1/7`. -/
def huttonLowerRat (K : ℕ) : ℚ :=
  8 * arctanPartialRat 3 (2 * (K + 1)) +
    4 * arctanPartialRat 7 (2 * (K + 1))

/-- The adjacent Hutton upper approximant obtained from equal odd Taylor
truncations at `1/3` and `1/7`. -/
def huttonUpperRat (K : ℕ) : ℚ :=
  8 * arctanPartialRat 3 (2 * (K + 1) + 1) +
    4 * arctanPartialRat 7 (2 * (K + 1) + 1)

/-- Real embedding of the rational Hutton lower approximant. -/
def huttonLower (K : ℕ) : ℝ := (huttonLowerRat K : ℝ)

/-- Real embedding of the rational Hutton upper approximant. -/
def huttonUpper (K : ℕ) : ℝ := (huttonUpperRat K : ℝ)

/-- The real lower approximant is exactly the corresponding pair of finite
Taylor sums. -/
theorem huttonLower_eq (K : ℕ) :
    huttonLower K =
      8 * arctanPartial 3 (2 * (K + 1)) +
        4 * arctanPartial 7 (2 * (K + 1)) := by
  simp [huttonLower, huttonLowerRat, arctanPartial]

/-- The real upper approximant is exactly the corresponding pair of finite
Taylor sums. -/
theorem huttonUpper_eq (K : ℕ) :
    huttonUpper K =
      8 * arctanPartial 3 (2 * (K + 1) + 1) +
        4 * arctanPartial 7 (2 * (K + 1) + 1) := by
  simp [huttonUpper, huttonUpperRat, arctanPartial]

/-- The lower approximant has the displayed exact rational witness. -/
theorem huttonLower_isRat (K : ℕ) :
    ∃ r : ℚ, huttonLower K = (r : ℝ) :=
  ⟨huttonLowerRat K, rfl⟩

/-- The upper approximant has the displayed exact rational witness. -/
theorem huttonUpper_isRat (K : ℕ) :
    ∃ r : ℚ, huttonUpper K = (r : ℝ) :=
  ⟨huttonUpperRat K, rfl⟩

/-- Mathlib's Hutton identity, normalized to solve for `pi`. -/
theorem pi_eq_hutton :
    Real.pi = 8 * Real.arctan (3 : ℝ)⁻¹ +
      4 * Real.arctan (7 : ℝ)⁻¹ := by
  have h := Real.two_mul_arctan_inv_3_add_arctan_inv_7
  linarith

/-- Every rational Hutton lower approximant is below `pi`. -/
theorem huttonLower_le_pi (K : ℕ) : huttonLower K ≤ Real.pi := by
  rw [huttonLower_eq, pi_eq_hutton]
  have h3 := arctanPartial_even_le 3 (K + 1) (by norm_num)
  have h7 := arctanPartial_even_le 7 (K + 1) (by norm_num)
  linarith

/-- Every rational Hutton upper approximant is above `pi`. -/
theorem pi_le_huttonUpper (K : ℕ) : Real.pi ≤ huttonUpper K := by
  rw [huttonUpper_eq, pi_eq_hutton]
  have h3 := arctan_le_arctanPartial_odd 3 (K + 1) (by norm_num)
  have h7 := arctan_le_arctanPartial_odd 7 (K + 1) (by norm_num)
  linarith

/-- Exact one-term recurrence for the real finite Taylor sums. -/
lemma arctanPartial_succ (q terms : ℕ) :
    arctanPartial q (terms + 1) = arctanPartial q terms +
      (-1 : ℝ) ^ terms * arctanMagnitude q terms := by
  rw [arctanPartial_eq_sum, arctanPartial_eq_sum]
  simp [Finset.sum_range_succ]

/-- The explicit real width contributed by the first omitted terms of the
two Hutton series.  Unfolding `arctanMagnitude` gives
`8 / ((4*K+5)*3^(4*K+5)) + 4 / ((4*K+5)*7^(4*K+5))`. -/
def huttonWidth (K : ℕ) : ℝ :=
  8 * arctanMagnitude 3 (2 * (K + 1)) +
    4 * arctanMagnitude 7 (2 * (K + 1))

/-- Closed form of the computable Hutton width. -/
theorem huttonWidth_eq_explicit (K : ℕ) :
    huttonWidth K =
      8 / (((4 * K + 5 : ℕ) : ℝ) * (3 : ℝ) ^ (4 * K + 5)) +
        4 / (((4 * K + 5 : ℕ) : ℝ) * (7 : ℝ) ^ (4 * K + 5)) := by
  unfold huttonWidth arctanMagnitude
  rw [show 2 * (2 * (K + 1)) + 1 = 4 * K + 5 by omega]
  rw [inv_pow, inv_pow]
  have hden :
      (2 : ℝ) * ((2 * (K + 1) : ℕ) : ℝ) + 1 =
        ((4 * K + 5 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hden]
  (field_simp; ring_nf)

/-- The adjacent rational Hutton endpoints differ by exactly their first
omitted Taylor terms. -/
theorem huttonUpperRat_sub_lowerRat (K : ℕ) :
    huttonUpperRat K - huttonLowerRat K =
      8 * arctanTermRat 3 (2 * (K + 1)) +
        4 * arctanTermRat 7 (2 * (K + 1)) := by
  unfold huttonUpperRat huttonLowerRat
  rw [show 2 * (K + 1) + 1 = 2 * (K + 1) + 1 by rfl]
  rw [arctanPartialRat_succ, arctanPartialRat_succ]
  ring

/-- The real bracket width is exactly the explicit omitted-term sum. -/
theorem huttonUpper_sub_lower_eq_width (K : ℕ) :
    huttonUpper K - huttonLower K = huttonWidth K := by
  rw [huttonUpper_eq, huttonLower_eq]
  rw [arctanPartial_succ, arctanPartial_succ]
  simp only [Even.neg_one_pow (even_two_mul (K + 1)), one_mul]
  unfold huttonWidth
  ring

/-- The explicit Hutton width is strictly positive. -/
theorem huttonWidth_pos (K : ℕ) : 0 < huttonWidth K := by
  unfold huttonWidth arctanMagnitude
  positivity

/-- The error of the lower rational shadow is trapped between zero and the
fully computable adjacent-bracket width. -/
theorem pi_sub_huttonLower_mem_width (K : ℕ) :
    0 ≤ Real.pi - huttonLower K ∧
      Real.pi - huttonLower K ≤ huttonWidth K := by
  constructor
  · exact sub_nonneg.mpr (huttonLower_le_pi K)
  · calc
      Real.pi - huttonLower K ≤ huttonUpper K - huttonLower K :=
        sub_le_sub_right (pi_le_huttonUpper K) _
      _ = huttonWidth K := huttonUpper_sub_lower_eq_width K

/-- Complete exact Hutton bracket with its computable width. -/
theorem pi_mem_hutton_bracket (K : ℕ) :
    huttonLower K ≤ Real.pi ∧
      Real.pi ≤ huttonUpper K ∧
      huttonUpper K - huttonLower K = huttonWidth K := by
  exact ⟨huttonLower_le_pi K, pi_le_huttonUpper K,
    huttonUpper_sub_lower_eq_width K⟩

end Theory.PiDigits.HuttonRationalShadow

#print axioms Theory.PiDigits.HuttonRationalShadow.huttonLower_eq
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonUpper_eq
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonLower_isRat
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonUpper_isRat
#print axioms Theory.PiDigits.HuttonRationalShadow.pi_eq_hutton
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonLower_le_pi
#print axioms Theory.PiDigits.HuttonRationalShadow.pi_le_huttonUpper
#print axioms Theory.PiDigits.HuttonRationalShadow.arctanPartial_succ
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonWidth_eq_explicit
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonUpperRat_sub_lowerRat
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonUpper_sub_lower_eq_width
#print axioms Theory.PiDigits.HuttonRationalShadow.huttonWidth_pos
#print axioms Theory.PiDigits.HuttonRationalShadow.pi_sub_huttonLower_mem_width
#print axioms Theory.PiDigits.HuttonRationalShadow.pi_mem_hutton_bracket
