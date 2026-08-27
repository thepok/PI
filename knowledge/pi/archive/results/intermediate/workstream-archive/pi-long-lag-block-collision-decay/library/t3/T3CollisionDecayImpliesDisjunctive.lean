import TheoryLib.PiLongLagBlockCollisionDecay.T1T1LongLagBlockCollisionDecay
import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T23T23FiniteCylinderEnergyCriterion

/-!
# T3: canonical collision decay implies decimal disjunctivity

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file does not assert the open collision estimate. It exposes the accepted
forbidden-language inequalities used by T1 and proves that T1's canonical
predicate, if supplied as a hypothesis, implies occurrence of every finite
word in the fixed floor-based base-10 stream `Theory.PiDigits.piDigit`.
-/

noncomputable section

open Filter

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T3

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T23
open Theory.PiDigits.LongLagBlockCollisionDecay

/-- The immutable decimal convention used in the conclusion: zero-based
digits after the decimal point, obtained from floors in base ten. -/
theorem piDigit_eq_floorDecimalDigit (n : ℕ) :
    Theory.PiDigits.piDigit n =
      ⟨⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ % 10,
        Nat.mod_lt _ (by norm_num)⟩ := by
  rfl

/-- The accepted forbidden-language estimate, displayed as an entropy bound
followed by its strict gap below full base-10 entropy. -/
theorem quantitative_forbidden_word_entropy_bound
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    forbiddenEntropy v ≤
        Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) ∧
      Real.log (forbiddenQ v : ℝ) / ((2 * ell : ℕ) : ℝ) <
        Real.log 10 := by
  exact forbiddenEntropy_le_q_rate_lt_log_ten v hell

/-- The normalized base-10 forbidden-language exponent lies strictly below
T1's explicit midpoint exponent. -/
theorem forbidden_baseTenExponent_lt_decayExponent
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    forbiddenCriticalDimension v < forbiddenDecayExponent v := by
  have hd : (0 : ℝ) < ((2 * ell : ℕ) : ℝ) := by positivity
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hD : (0 : ℝ) < ((2 * ell : ℕ) : ℝ) * Real.log 10 :=
    mul_pos hd hlogTen
  have hrate := forbiddenQ_rate_lt_log_ten v hell
  have hlogQ : Real.log (forbiddenQ v : ℝ) <
      ((2 * ell : ℕ) : ℝ) * Real.log 10 := by
    rw [div_lt_iff₀ hd] at hrate
    simpa [mul_comm] using hrate
  unfold forbiddenCriticalDimension forbiddenDecayExponent
  field_simp [ne_of_gt hD]
  linarith

/-- The actual choice of `s`: it is strictly above the base-10 forbidden-word
exponent and satisfies the canonical hypothesis bounds `0 < s < 1`. -/
theorem explicit_decayExponent_choice
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    let s := forbiddenDecayExponent v
    forbiddenCriticalDimension v < s ∧ 0 < s ∧ s < 1 := by
  dsimp
  exact ⟨forbidden_baseTenExponent_lt_decayExponent hell v,
    (forbiddenDecayExponent_pos_lt_one hell v).1,
    (forbiddenDecayExponent_pos_lt_one hell v).2⟩

/-- At the chosen exponent, the forbidden-language growth divided by decimal
decay has a geometric base in `[0,1)`. -/
theorem explicit_forbidden_decay_base
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    0 ≤ (forbiddenQ v : ℝ) /
          (10 : ℝ) ^
            (forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) ∧
      (forbiddenQ v : ℝ) /
          (10 : ℝ) ^
            (forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) < 1 := by
  exact forbiddenDecayBase_nonneg_lt_one hell v

/-- The finite forbidden language at a two-block multiple obeys the displayed
power bound used in the collision-energy comparison. -/
theorem forbidden_word_count_at_twoBlockScale
    {ell : ℕ} (v : Fin ell → Fin 10) (j : ℕ) :
    forbiddenWordCount v ((2 * ell) * j) ≤ forbiddenQ v ^ j := by
  exact forbiddenWordCount_twoBlock_mul_le_pow v j

/-- Every positive constant is absorbed at a sufficiently large two-block
scale; the exact decimal factor used later is shown in the conclusion. -/
theorem explicit_constant_absorption
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10)
    (C : ℝ) (hC : 0 < C) :
    ∃ j : ℕ, 1 ≤ j ∧
      C * (forbiddenQ v : ℝ) ^ j *
          (10 : ℝ) ^
            (-forbiddenDecayExponent v * (((2 * ell) * j : ℕ) : ℝ)) <
        (1 : ℝ) / 16 := by
  exact exists_twoBlockScale_forbidden_energy_small hell v C hC

/-- An arbitrary nonempty word cannot be missing once the canonical collision
predicate is assumed. The contradiction is explicit: T1 supplies positive
lower block density, which supplies an occurrence forbidden by `hmissing`. -/
theorem arbitrary_missing_word_contradiction
    (hDecay : PiLongLagBlockCollisionDecay)
    (w : List (Fin 10)) (hw : w ≠ [])
    (hmissing : ∀ n : ℕ, ¬ ∀ i : ℕ, ∀ hi : i < w.length,
      Theory.PiDigits.piDigit (n + i) = w.get ⟨i, hi⟩) : False := by
  have hDensity : PiPositiveLowerBlockDensity :=
    piLongLagBlockCollisionDecay_implies_piPositiveLowerBlockDensity hDecay
  have hpositive :
      0 < liminf (blockFrequency Theory.PiDigits.piDigit w) atTop :=
    hDensity w hw
  obtain ⟨n, hn⟩ := exists_block_occurrence_of_pos_liminf
    Theory.PiDigits.piDigit w hpositive
  exact hmissing n hn

/-- End-to-end conditional theorem. The conclusion is canonical `V1`: every
finite list of digits in `Fin 10`, including leading zeroes, occurs
contiguously in the immutable floor-based stream `Theory.PiDigits.piDigit`. -/
theorem piLongLagBlockCollisionDecay_implies_everyFiniteDecimalWordOccurs
    (hDecay : PiLongLagBlockCollisionDecay) :
    ∀ w : List (Fin 10), ∃ n : ℕ,
      ∀ i : ℕ, ∀ hi : i < w.length,
        Theory.PiDigits.piDigit (n + i) = w.get ⟨i, hi⟩ := by
  intro w
  by_cases hw : w = []
  · subst w
    exact ⟨0, by simp⟩
  · by_contra hmissing
    exact arbitrary_missing_word_contradiction hDecay w hw
      (fun n hn => hmissing ⟨n, hn⟩)

end Theory.PiDigits.LongLagBlockCollisionDecay.T3

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.piDigit_eq_floorDecimalDigit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.quantitative_forbidden_word_entropy_bound
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.forbidden_baseTenExponent_lt_decayExponent
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.explicit_decayExponent_choice
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.explicit_forbidden_decay_base
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.forbidden_word_count_at_twoBlockScale
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.explicit_constant_absorption
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.arbitrary_missing_word_contradiction
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T3.piLongLagBlockCollisionDecay_implies_everyFiniteDecimalWordOccurs
