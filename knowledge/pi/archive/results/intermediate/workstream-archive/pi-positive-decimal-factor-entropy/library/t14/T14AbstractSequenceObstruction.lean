import TheoryLib.PiPositiveDecimalFactorEntropy.T13T13AutocorrelationAmplification

/-!
# T14: abstract period-three obstruction to fixed-short-lag coherence

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This module concerns only the abstract complex sequence obtained by repeating
`(1, 1, -1)`. It imports T13's exact `ShortLagCoherence` predicate but proves
no theorem about `Real.pi`, decimal digits, or canonical conjecture C1.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity.AbstractSequenceObstruction

open DecimalFactorComplexity.IteratedLagResonance
open DecimalFactorComplexity.AutocorrelationAmplification

/-- The infinite unit-circle sequence formed by repeating `(1, 1, -1)`. -/
abbrev repeatedPattern : ℕ → ℂ := coherenceCounterexample

/-- Every entry of the repeated pattern has norm one. -/
theorem repeatedPattern_norm_one (j : ℕ) : ‖repeatedPattern j‖ = 1 := by
  exact coherenceCounterexample_norm_one j

/-- Exactly `q` remains after summing `q` complete copies of `(1, 1, -1)`. -/
theorem repeatedPattern_sum_three_mul (q : ℕ) :
    (∑ j ∈ range (3 * q), repeatedPattern j) = (q : ℂ) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      simp only [Finset.sum_range_succ]
      rw [ih]
      simp [repeatedPattern, coherenceCounterexample, Nat.add_mod]

/-- The unnormalized seed energy at repetition count `q` is exactly `q^2`. -/
theorem repeatedPattern_energy_three_mul (q : ℕ) :
    ‖∑ j ∈ range (3 * q), repeatedPattern j‖ ^ 2 = (q : ℝ) ^ 2 := by
  rw [repeatedPattern_sum_three_mul]
  simp

/-- The first `R` correlation real parts have the displayed linear bound.
This deliberately uses only unit modulus, so no periodic cancellation is hidden. -/
theorem repeatedPattern_shortLag_sum_le (R q : ℕ) :
    (∑ r ∈ Icc 1 R, (autocorrelation repeatedPattern (3 * q) r).re) ≤
      ((3 * R * q : ℕ) : ℝ) := by
  calc
    (∑ r ∈ Icc 1 R, (autocorrelation repeatedPattern (3 * q) r).re) ≤
        ∑ _r ∈ Icc 1 R, (((3 * q : ℕ) : ℝ)) := by
      apply sum_le_sum
      intro r hr
      calc
        (autocorrelation repeatedPattern (3 * q) r).re ≤
            ‖autocorrelation repeatedPattern (3 * q) r‖ := Complex.re_le_norm _
        _ ≤ ((3 * q - r : ℕ) : ℝ) :=
          norm_autocorrelation_le repeatedPattern (3 * q) r repeatedPattern_norm_one
        _ ≤ ((3 * q : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (3 * q) r
    _ = ((3 * R * q : ℕ) : ℝ) := by
      simp [Nat.card_Icc]
      ring

/-- Explicit finite failure regime. If `R` is a positive fixed cutoff and
`delta * (q - 3) > 6R`, then `q` copies violate T13's exact predicate. -/
theorem repeatedPattern_not_shortLagCoherence_of_large
    (R q : ℕ) (delta : ℝ) (hR : 1 ≤ R) (hboundary : R < 3 * q)
    (hlarge : 6 * (R : ℝ) + 3 * delta < delta * (q : ℝ)) :
    ¬ ShortLagCoherence repeatedPattern (3 * q) R delta := by
  intro hcoh
  have hlower := shortLagCoherence_implies_retained_lower
    repeatedPattern (3 * q) R delta repeatedPattern_norm_one hR hboundary hcoh
  rw [repeatedPattern_energy_three_mul] at hlower
  have hupper := repeatedPattern_shortLag_sum_le R q
  have hqpos : (0 : ℝ) < q := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hscaled := mul_lt_mul_of_pos_right hlarge hqpos
  push_cast at hlower hupper
  nlinarith

/-- The cutoff `R = 0` also fails once the exact energy exceeds the diagonal.
Here the entire positive-lag correlation sum is the predicate's tail. -/
theorem repeatedPattern_not_shortLagCoherence_zero
    (q : ℕ) (delta : ℝ) (hq : 3 < q) (hdelta : 0 < delta) :
    ¬ ShortLagCoherence repeatedPattern (3 * q) 0 delta := by
  intro hcoh
  have hid := norm_sum_sq_eq_autocorrelation repeatedPattern (3 * q)
    repeatedPattern_norm_one
  unfold ShortLagCoherence at hcoh
  simp only [zero_add] at hcoh
  rw [repeatedPattern_energy_three_mul] at hid hcoh
  push_cast at hid hcoh
  have hqReal : (3 : ℝ) < q := by exact_mod_cast hq
  have hpositive : (0 : ℝ) < (q : ℝ) ^ 2 - 3 * q := by
    nlinarith [sq_nonneg ((q : ℝ) - 3)]
  nlinarith

/-- Uniform abstract counterexample family with all quantifiers exposed.
For each fixed natural short-lag cutoff `R`, positive coherence constant
`delta`, and requested energy level `E`, every repetition count beyond one
threshold has length `M = 3q`, lies past the boundary `R < M`, has exact
unnormalized energy `q^2 > E`, and violates T13's exact predicate. -/
theorem repeatedPattern_eventually_not_shortLagCoherence
    (R : ℕ) (delta : ℝ) (hdelta : 0 < delta) (E : ℝ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      R < 3 * q ∧
      ‖∑ j ∈ range (3 * q), repeatedPattern j‖ ^ 2 = (q : ℝ) ^ 2 ∧
      E < ‖∑ j ∈ range (3 * q), repeatedPattern j‖ ^ 2 ∧
      ¬ ShortLagCoherence repeatedPattern (3 * q) R delta := by
  obtain ⟨Q : ℕ, hQ⟩ := exists_nat_gt
    ((6 * (R : ℝ) + 3 * delta) / delta + |E| + (R : ℝ) + 4)
  refine ⟨Q, ?_⟩
  intro q hQq
  have hQqReal : (Q : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQq
  have hratioPos : 0 < (6 * (R : ℝ) + 3 * delta) / delta := by
    apply div_pos
    · positivity
    · exact hdelta
  have hratio : (6 * (R : ℝ) + 3 * delta) / delta < (q : ℝ) := by
    have habs := abs_nonneg E
    have hRnonneg : (0 : ℝ) ≤ R := by positivity
    nlinarith
  have hratioThree :
      (3 : ℝ) ≤ (6 * (R : ℝ) + 3 * delta) / delta := by
    apply (le_div_iff₀ hdelta).2
    have hRnonneg : (0 : ℝ) ≤ R := by positivity
    nlinarith
  have hqThreeReal : (3 : ℝ) < q := hratioThree.trans_lt hratio
  have hqThree : 3 < q := by exact_mod_cast hqThreeReal
  have hRltq : (R : ℝ) < (q : ℝ) := by
    have habs := abs_nonneg E
    nlinarith
  have hboundary : R < 3 * q := by
    exact_mod_cast (show (R : ℝ) < 3 * (q : ℝ) by nlinarith)
  have hlarge : 6 * (R : ℝ) + 3 * delta < delta * (q : ℝ) := by
    have := (div_lt_iff₀ hdelta).mp hratio
    nlinarith
  have henergy := repeatedPattern_energy_three_mul q
  have hE : E < (q : ℝ) ^ 2 := by
    have hEleAbs : E ≤ |E| := le_abs_self E
    have hEltq : E < (q : ℝ) := by
      nlinarith [abs_nonneg E]
    have hqOne : (1 : ℝ) < q := by
      linarith
    nlinarith [sq_nonneg ((q : ℝ) - 1)]
  refine ⟨hboundary, henergy, ?_, ?_⟩
  · rw [henergy]
    exact hE
  · by_cases hRzero : R = 0
    · subst R
      exact repeatedPattern_not_shortLagCoherence_zero q delta hqThree hdelta
    · exact repeatedPattern_not_shortLagCoherence_of_large
        R q delta (Nat.one_le_iff_ne_zero.mpr hRzero) hboundary hlarge

end DecimalFactorComplexity.AbstractSequenceObstruction

#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_norm_one
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_sum_three_mul
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_energy_three_mul
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_shortLag_sum_le
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_not_shortLagCoherence_of_large
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_not_shortLagCoherence_zero
#print axioms DecimalFactorComplexity.AbstractSequenceObstruction.repeatedPattern_eventually_not_shortLagCoherence
