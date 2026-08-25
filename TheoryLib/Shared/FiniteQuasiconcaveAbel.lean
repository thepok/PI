import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite quasiconcave Abel bound

A single reusable finite lemma: a nonnegative quasiconcave real sequence has
total variation controlled by twice its height, and hence its exponential sum
has the sharp elementary Abel bound.
-/

noncomputable section

open Finset

namespace Theory.Shared.FiniteQuasiconcaveAbel

/-- The standard unit-circle exponential `exp(2 * pi * i * t)`. -/
def circleExp (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))

/-- Both endpoints plus the total variation of a finite nonnegative
quasiconcave sequence are at most twice any uniform upper bound. -/
theorem endpoints_add_variation_le_two_mul
    (a : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hnonneg : ∀ i, i ≤ n → 0 ≤ a i)
    (hbound : ∀ i, i ≤ n → a i ≤ B)
    (hquasi : ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (a i) (a k) ≤ a j) :
    a 0 + a n + ∑ i ∈ range n, |a (i + 1) - a i| ≤ 2 * B := by
  induction n generalizing B with
  | zero =>
      simpa using (show a 0 + a 0 ≤ 2 * B by
        nlinarith [hbound 0 le_rfl])
  | succ n ih =>
      rw [sum_range_succ]
      by_cases hdown : a (n + 1) ≤ a n
      · rw [abs_of_nonpos (sub_nonpos.mpr hdown)]
        have hprev := ih B
          (fun i hi => hnonneg i (hi.trans (Nat.le_succ n)))
          (fun i hi => hbound i (hi.trans (Nat.le_succ n)))
          (fun i j k hij hjk hkn => hquasi i j k hij hjk
            (hkn.trans (Nat.le_succ n)))
        nlinarith
      · have hup : a n < a (n + 1) := lt_of_not_ge hdown
        have hprevBound : ∀ i, i ≤ n → a i ≤ a n := by
          intro i hin
          by_contra hnot
          have hai : a n < a i := lt_of_not_ge hnot
          have hmid := hquasi i n (n + 1) hin (Nat.le_succ n) le_rfl
          exact (not_lt_of_ge hmid) (lt_min hai hup)
        have hprev := ih (a n)
          (fun i hi => hnonneg i (hi.trans (Nat.le_succ n)))
          hprevBound
          (fun i j k hij hjk hkn => hquasi i j k hij hjk
            (hkn.trans (Nat.le_succ n)))
        rw [abs_of_pos (sub_pos.mpr hup)]
        nlinarith [hbound (n + 1) le_rfl]

private lemma one_sub_mul_sum_eq
    (a : ℕ → ℝ) (z : ℂ) (n : ℕ) :
    (1 - z) * (∑ i ∈ range (n + 1), (a i : ℂ) * z ^ (i + 1)) =
      (a 0 : ℂ) * z +
        (∑ i ∈ range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)) -
          (a n : ℂ) * z ^ (n + 2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      conv_lhs => rw [sum_range_succ, mul_add, ih]
      conv_rhs => rw [sum_range_succ]
      push_cast
      simp only [pow_succ]
      ring

private lemma norm_one_sub_circleExp (t : ℝ) :
    ‖1 - circleExp t‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [show 1 - circleExp t = -(circleExp t - 1) by ring, norm_neg]
  rw [circleExp, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

/-- Sharp finite Abel estimate for a nonnegative quasiconcave sequence.  The
sum is indexed by `0,...,n`, with its first oscillatory phase equal to
`circleExp t`. -/
theorem norm_sum_mul_circleExp_pow_le
    (a : ℕ → ℝ) (n : ℕ) (B t : ℝ)
    (hnonneg : ∀ i, i ≤ n → 0 ≤ a i)
    (hbound : ∀ i, i ≤ n → a i ≤ B)
    (hquasi : ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (a i) (a k) ≤ a j)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ i ∈ range (n + 1), (a i : ℂ) * circleExp t ^ (i + 1)‖ ≤
      B / |Real.sin (Real.pi * t)| := by
  let z := circleExp t
  let S : ℂ := ∑ i ∈ range (n + 1), (a i : ℂ) * z ^ (i + 1)
  have hz : ‖z‖ = 1 := by
    simp [z, circleExp, Complex.norm_exp]
  have hid := one_sub_mul_sum_eq a z n
  have hvar := endpoints_add_variation_le_two_mul a n B hnonneg hbound hquasi
  have hnormDiff :
      ‖∑ i ∈ range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)‖ ≤
        ∑ i ∈ range n, |a (i + 1) - a i| := by
    calc
      _ ≤ ∑ i ∈ range n,
          ‖((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)‖ := norm_sum_le _ _
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        rw [Complex.norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
  have hright :
      ‖(a 0 : ℂ) * z +
          (∑ i ∈ range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)) -
            (a n : ℂ) * z ^ (n + 2)‖ ≤ 2 * B := by
    calc
      _ ≤ ‖(a 0 : ℂ) * z‖ +
            ‖∑ i ∈ range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)‖ +
              ‖(a n : ℂ) * z ^ (n + 2)‖ := by
                exact (norm_sub_le _ _).trans
                  (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ a 0 + (∑ i ∈ range n, |a (i + 1) - a i|) + a n := by
        have ha0 := hnonneg 0 (Nat.zero_le n)
        have han := hnonneg n le_rfl
        rw [Complex.norm_mul, hz, mul_one, Complex.norm_mul, norm_pow, hz, one_pow, mul_one,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha0, abs_of_nonneg han]
        linarith
      _ ≤ 2 * B := by linarith
  have hproduct : ‖1 - z‖ * ‖S‖ ≤ 2 * B := by
    rw [← Complex.norm_mul, show (1 - z) * S =
        (a 0 : ℂ) * z +
          (∑ i ∈ range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 2)) -
            (a n : ℂ) * z ^ (n + 2) by
      simpa [S] using hid]
    exact hright
  have habs : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  rw [norm_one_sub_circleExp] at hproduct
  change ‖S‖ ≤ B / |Real.sin (Real.pi * t)|
  apply (le_div_iff₀ habs).2
  nlinarith

/-- Strict version for a finite sequence lying strictly below `B`. -/
theorem norm_sum_mul_circleExp_pow_lt
    (a : ℕ → ℝ) (n : ℕ) (B t : ℝ)
    (hnonneg : ∀ i, i ≤ n → 0 ≤ a i)
    (hbound : ∀ i, i ≤ n → a i < B)
    (hquasi : ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (a i) (a k) ≤ a j)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ i ∈ range (n + 1), (a i : ℂ) * circleExp t ^ (i + 1)‖ <
      B / |Real.sin (Real.pi * t)| := by
  obtain ⟨r, hr, hrmax⟩ := exists_max_image (range (n + 1)) a
    ⟨0, mem_range.mpr (Nat.zero_lt_succ n)⟩
  have hrn : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
  have hle : ∀ i, i ≤ n → a i ≤ a r := by
    intro i hi
    exact hrmax i (mem_range.mpr (Nat.lt_succ_of_le hi))
  have hmain := norm_sum_mul_circleExp_pow_le a n (a r) t hnonneg hle hquasi hsin
  have habs : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  exact hmain.trans_lt (div_lt_div_of_pos_right (hbound r hrn) habs)

end Theory.Shared.FiniteQuasiconcaveAbel

#print axioms Theory.Shared.FiniteQuasiconcaveAbel.endpoints_add_variation_le_two_mul
#print axioms Theory.Shared.FiniteQuasiconcaveAbel.norm_sum_mul_circleExp_pow_le
#print axioms Theory.Shared.FiniteQuasiconcaveAbel.norm_sum_mul_circleExp_pow_lt
