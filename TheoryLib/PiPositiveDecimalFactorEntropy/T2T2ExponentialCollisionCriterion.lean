import TheoryLib.PiDecimalFactorComplexity.T4FinitePrefixCollisionEnergy
import TheoryLib.PiDecimalFactorComplexity.T8PiLacunaryNearReturns

/-!
# T2: exponential collision criterion for the decimal factors of pi

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The canonical target chooses one real `eta > 0`, then one cutoff `N >= 1`,
and requires the same exponential lower bound at every `n >= N`. The
collision criterion has the same outer witnesses and permits a separate
positive finite-prefix size `M` at each such `n`.

All statements are conditional. In particular, this file does not assert
either exponential collision decay or exponential near-return decay for pi.
The names below are deliberately distinct from the older, merely superlinear
`CollisionEnergyC1` and `LacunaryNearReturnC2` predicates.
-/

namespace DecimalFactorComplexity.ExponentialCollisionCriterion

open DecimalFactorComplexity

/-- Canonical C1: positive exponential growth of the full decimal factor
language of pi. Here `canonicalFactorComplexity piDecimalStream n` is exactly
the cardinality `p_pi(n)` from the source statement. -/
def PiPositiveFactorEntropyC1 : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      (10 : ℝ) ^ (eta * (n : ℝ)) ≤
        (canonicalFactorComplexity piDecimalStream n : ℝ)

/-- Agenda C2, with its exact quantifier order: one positive decay exponent,
one positive cutoff, every later length, and then a length-dependent positive
sample size. This is an explicit unproved hypothesis about pi. -/
def PiExponentialCollisionC2 : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
      (E_pi n M : ℝ) ≤
        (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ))

/-- Near-return version of C2. It remains an explicit unproved pi-specific
hypothesis and is stronger than `PiExponentialCollisionC2` via `E_pi <= Q_pi`.
-/
def PiExponentialNearReturnC2 : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
      (Q_pi n M : ℝ) ≤
        (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ))

/-- The finite Cauchy collision bound at explicitly exposed parameters
`eta`, `n`, and `M`. No decay property of pi is asserted: it is exactly the
hypothesis `henergy`. -/
theorem factorComplexity_ge_rpow_of_E_pi_le
    (eta : ℝ) (n M : ℕ) (hM : 1 ≤ M)
    (henergy : (E_pi n M : ℝ) ≤
      (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ))) :
    (10 : ℝ) ^ (eta * (n : ℝ)) ≤
      (canonicalFactorComplexity piDecimalStream n : ℝ) := by
  let decay : ℝ := (10 : ℝ) ^ (-eta * (n : ℝ))
  have hdecay : 0 < decay := by
    dsimp [decay]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hM_sq_pos : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
  have hcsNat :=
    square_le_observedFactorCount_mul_collisionEnergy piDecimalStream n M
  have hcs :
      (M : ℝ) ^ 2 ≤
        (observedFactorCount piDecimalStream n M : ℝ) * (E_pi n M : ℝ) := by
    exact_mod_cast hcsNat
  have hobservedNat :=
    observedFactorCount_le_canonicalFactorComplexity piDecimalStream n M
  have hobserved :
      (observedFactorCount piDecimalStream n M : ℝ) ≤
        (canonicalFactorComplexity piDecimalStream n : ℝ) := by
    exact_mod_cast hobservedNat
  have hupper :
      (observedFactorCount piDecimalStream n M : ℝ) * (E_pi n M : ℝ) ≤
        (canonicalFactorComplexity piDecimalStream n : ℝ) *
          ((M : ℝ) ^ 2 * decay) := by
    calc
      (observedFactorCount piDecimalStream n M : ℝ) * (E_pi n M : ℝ) ≤
          (canonicalFactorComplexity piDecimalStream n : ℝ) * (E_pi n M : ℝ) := by
        gcongr
      _ ≤ (canonicalFactorComplexity piDecimalStream n : ℝ) *
          ((M : ℝ) ^ 2 * decay) := by
        gcongr
  have hscaled :
      (M : ℝ) ^ 2 * 1 ≤
        (M : ℝ) ^ 2 *
          ((canonicalFactorComplexity piDecimalStream n : ℝ) * decay) := by
    simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using hcs.trans hupper
  have hone :
      1 ≤ (canonicalFactorComplexity piDecimalStream n : ℝ) * decay :=
    le_of_mul_le_mul_left hscaled hM_sq_pos
  have hinv :
      decay⁻¹ ≤ (canonicalFactorComplexity piDecimalStream n : ℝ) := by
    exact (inv_le_iff_one_le_mul₀ hdecay).2 hone
  have hten : (0 : ℝ) ≤ 10 := by norm_num
  simpa only [decay, neg_mul, Real.rpow_neg hten, inv_inv] using hinv

/-- Parameterized near-return criterion. The only pi-specific input is the
displayed `Q_pi` bound; the proof imports `E_pi <= Q_pi` and then applies the
finite Cauchy collision bound above. -/
theorem factorComplexity_ge_rpow_of_Q_pi_le
    (eta : ℝ) (n M : ℕ) (hM : 1 ≤ M)
    (hnear : (Q_pi n M : ℝ) ≤
      (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ))) :
    (10 : ℝ) ^ (eta * (n : ℝ)) ≤
      (canonicalFactorComplexity piDecimalStream n : ℝ) := by
  apply factorComplexity_ge_rpow_of_E_pi_le eta n M hM
  have hbridgeNat := pi_collisionEnergy_le_Q_pi n M
  have hbridge : (E_pi n M : ℝ) ≤ (Q_pi n M : ℝ) := by
    exact_mod_cast hbridgeNat
  exact hbridge.trans hnear

/-- The agenda's exponential collision C2 implies canonical C1. This form
deliberately displays the complete quantifier order in the checked theorem
type: `eta`, then the cutoff, then every `n`, and finally its sample size `M`.
The same `eta` and cutoff occur in the conclusion. -/
theorem piExponentialCollisionC2_implies_C1_explicit
    (hC2 : ∃ eta : ℝ, 0 < eta ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
        (E_pi n M : ℝ) ≤
          (M : ℝ) ^ 2 * (10 : ℝ) ^ (-eta * (n : ℝ))) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (eta * (n : ℝ)) ≤
          (canonicalFactorComplexity piDecimalStream n : ℝ) := by
  obtain ⟨eta, heta, n0, hn0, hall⟩ := hC2
  refine ⟨eta, heta, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨M, hM, henergy⟩ := hall n hn
  exact factorComplexity_ge_rpow_of_E_pi_le eta n M hM henergy

/-- The definition-level statement of C2 implies the definition-level
statement of C1. -/
theorem piExponentialCollisionC2_implies_C1
    (hC2 : PiExponentialCollisionC2) : PiPositiveFactorEntropyC1 := by
  exact piExponentialCollisionC2_implies_C1_explicit hC2

/-- Exponential decay of the ordered pi near-return count also implies
canonical C1. Every pi-specific decay assumption remains in `hC2`. -/
theorem piExponentialNearReturnC2_implies_C1
    (hC2 : PiExponentialNearReturnC2) : PiPositiveFactorEntropyC1 := by
  obtain ⟨eta, heta, n0, hn0, hall⟩ := hC2
  refine ⟨eta, heta, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨M, hM, hnear⟩ := hall n hn
  exact factorComplexity_ge_rpow_of_Q_pi_le eta n M hM hnear

end DecimalFactorComplexity.ExponentialCollisionCriterion

#print axioms DecimalFactorComplexity.ExponentialCollisionCriterion.factorComplexity_ge_rpow_of_E_pi_le
#print axioms DecimalFactorComplexity.ExponentialCollisionCriterion.factorComplexity_ge_rpow_of_Q_pi_le
#print axioms DecimalFactorComplexity.ExponentialCollisionCriterion.piExponentialCollisionC2_implies_C1_explicit
#print axioms DecimalFactorComplexity.ExponentialCollisionCriterion.piExponentialCollisionC2_implies_C1
#print axioms DecimalFactorComplexity.ExponentialCollisionCriterion.piExponentialNearReturnC2_implies_C1
