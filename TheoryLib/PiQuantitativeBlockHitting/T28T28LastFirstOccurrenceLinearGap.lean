import TheoryLib.PiQuantitativeBlockHitting.T27T27ManyFrequencyLinearGap

/-!
# T28: last-first-occurrence linear additive gap

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T23's canonical cutoff is one plus the sum of all first-occurrence positions.
The smallest positive prefix containing the same representatives is instead
one plus their finite supremum.  This file constructs that minimal prefix and
transfers T27's many-frequency additive saving to it.

The ratio between this last-first-occurrence cutoff and factor complexity is
still uncontrolled.  Even a hypothetical linear bound on that ratio would
turn the additive saving `P/32` into only a constant relative saving, not the
natural-scale cancellation for every frequency required by T19.  Thus this
sharpening does not imply decimal disjunctivity or V1.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.LastFirstOccurrenceLinearGap

open Theory.PiDigits.DigitChangeFourierDefect
open Theory.PiDigits.MorseHedlundFrequencyDefect
open Theory.PiDigits.ManyFrequencyFirstOccurrenceDefect
open Theory.PiDigits.ManyFrequencyLinearGap
open Theory.PiDigits.FactorComplexity

/-- One plus the last first-occurrence position among the canonical distinct
length-`m` pi factors.  Finite supremum is zero on an empty index type, so this
definition remains the least *positive* covering prefix in that edge case. -/
noncomputable def piLastFirstOccurrencePrefixLength (m : ℕ) : ℕ :=
  1 + (Finset.univ : Finset (Fin (piFactorComplexity m))).sup
    (piFactorFirstOccurrence m)

/-- Every canonical first occurrence is at most the finite supremum used in
the last-first-occurrence cutoff. -/
lemma piFactorFirstOccurrence_le_last_sup (m : ℕ)
    (i : Fin (piFactorComplexity m)) :
    piFactorFirstOccurrence m i ≤
      (Finset.univ : Finset (Fin (piFactorComplexity m))).sup
        (piFactorFirstOccurrence m) := by
  exact Finset.le_sup (f := piFactorFirstOccurrence m) (Finset.mem_univ i)

/-- Every representative position lies strictly inside the minimal covering
prefix. -/
theorem piFactorFirstOccurrence_lt_lastPrefixLength (m : ℕ)
    (i : Fin (piFactorComplexity m)) :
    piFactorFirstOccurrence m i < piLastFirstOccurrencePrefixLength m := by
  have hi := piFactorFirstOccurrence_le_last_sup m i
  unfold piLastFirstOccurrencePrefixLength
  omega

/-- The first occurrences embedded into the last-first-occurrence prefix. -/
noncomputable def piLastFirstOccurrenceEmbedding (m : ℕ) :
    Fin (piFactorComplexity m) ↪ Fin (piLastFirstOccurrencePrefixLength m) where
  toFun i := ⟨piFactorFirstOccurrence m i,
    piFactorFirstOccurrence_lt_lastPrefixLength m i⟩
  inj' := fun _ _ hij ↦
    piFactorFirstOccurrence_injective m (congrArg Fin.val hij)

/-- The minimal-prefix embedding is injective. -/
theorem piLastFirstOccurrenceEmbedding_injective (m : ℕ) :
    Function.Injective (piLastFirstOccurrenceEmbedding m) :=
  (piLastFirstOccurrenceEmbedding m).injective

/-- The last-first-occurrence prefix length is positive. -/
theorem piLastFirstOccurrencePrefixLength_pos (m : ℕ) :
    0 < piLastFirstOccurrencePrefixLength m := by
  unfold piLastFirstOccurrencePrefixLength
  omega

/-- Any positive prefix containing every canonical first occurrence is at
least as long as the last-first-occurrence prefix. -/
theorem piLastFirstOccurrencePrefixLength_le_of_covers
    (m N : ℕ) (hN : 0 < N)
    (hcovers : ∀ i : Fin (piFactorComplexity m),
      piFactorFirstOccurrence m i < N) :
    piLastFirstOccurrencePrefixLength m ≤ N := by
  have hsup :
      (Finset.univ : Finset (Fin (piFactorComplexity m))).sup
          (piFactorFirstOccurrence m) ≤ N - 1 := by
    apply Finset.sup_le
    intro i _hi
    have hi := hcovers i
    omega
  unfold piLastFirstOccurrencePrefixLength
  omega

/-- `piLastFirstOccurrencePrefixLength m` is exactly the least positive prefix
length containing all canonical first-occurrence positions. -/
theorem piLastFirstOccurrencePrefixLength_isLeast (m : ℕ) :
    IsLeast
      {N : ℕ | 0 < N ∧
        ∀ i : Fin (piFactorComplexity m),
          piFactorFirstOccurrence m i < N}
      (piLastFirstOccurrencePrefixLength m) := by
  refine ⟨⟨piLastFirstOccurrencePrefixLength_pos m, ?_⟩, ?_⟩
  · exact piFactorFirstOccurrence_lt_lastPrefixLength m
  · intro N hN
    exact piLastFirstOccurrencePrefixLength_le_of_covers m N hN.1 hN.2

/-- The last-first-occurrence cutoff is no larger than T23's earlier
sum-of-first-occurrences cutoff. -/
theorem piLastFirstOccurrencePrefixLength_le_sumPrefixLength (m : ℕ) :
    piLastFirstOccurrencePrefixLength m ≤
      piFirstOccurrencePrefixLength m := by
  classical
  have hsup :
      (Finset.univ : Finset (Fin (piFactorComplexity m))).sup
          (piFactorFirstOccurrence m) ≤
        ∑ i : Fin (piFactorComplexity m), piFactorFirstOccurrence m i := by
    apply Finset.sup_le
    intro i hi
    apply Finset.single_le_sum
    · intro j _hj
      exact Nat.zero_le _
    · exact hi
  unfold piLastFirstOccurrencePrefixLength piFirstOccurrencePrefixLength
  omega

/-- The orbit point at a minimally embedded first occurrence remains in its
exact length-`m` decimal cell. -/
theorem piLastFirstOccurrenceEmbedding_mem_cell (m : ℕ)
    (i : Fin (piFactorComplexity m)) :
    piOrbit (piLastFirstOccurrenceEmbedding m i).val ∈ Set.Ico
      (((piFirstOccurrenceCylinderCode m i).val : ℝ) / (10 ^ m : ℕ))
      ((((piFirstOccurrenceCylinderCode m i).val + 1 : ℕ) : ℝ) /
        (10 ^ m : ℕ)) := by
  simpa only [piLastFirstOccurrenceEmbedding, piFirstOccurrenceEmbedding]
    using piFirstOccurrenceEmbedding_mem_cell m i

/-- Selected-energy frequencies for the same representatives, now viewed
inside the minimal last-first-occurrence prefix. -/
def piManyLastFirstOccurrenceLinearGapFrequencies (m : ℕ) :
    Finset (Fin (10 ^ m)) :=
  largeEnergyFrequencies (10 ^ m)
    (fun i : Fin (piFactorComplexity m) ↦
      piOrbit (piLastFirstOccurrenceEmbedding m i).val)

/-- Changing the ambient cutoff does not change the selected-support good
set: both embeddings select exactly the same first-occurrence positions. -/
theorem piManyLastFirstOccurrenceLinearGapFrequencies_eq_sumPrefix_set
    (m : ℕ) :
    piManyLastFirstOccurrenceLinearGapFrequencies m =
      piManyFirstOccurrenceLinearGapFrequencies m := by
  rfl

/-- At least one sixteenth of `1,...,10^m` survive in the minimal-prefix
selected-energy set. -/
theorem pi_q_le_sixteen_mul_card_manyLastFirstOccurrenceLinearGapFrequencies
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤
      16 * (piManyLastFirstOccurrenceLinearGapFrequencies m).card := by
  have hP : 4 ≤ piFactorComplexity m := by
    have hp := pi_factorComplexity_lower_bound m (by omega)
    omega
  have hq : 4 ≤ 10 ^ m := by
    calc
      4 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa only [piManyLastFirstOccurrenceLinearGapFrequencies] using
    (q_le_sixteen_mul_card_largeEnergyFrequencies hP hq
      (piFirstOccurrenceCylinderCode m)
      (piFirstOccurrenceCylinderCode_injective m)
      (fun i : Fin (piFactorComplexity m) ↦
        piOrbit (piLastFirstOccurrenceEmbedding m i).val)
      (piLastFirstOccurrenceEmbedding_mem_cell m))

/-- **Minimal-prefix pi specialization.** At least one sixteenth of the
frequencies `1,...,10^m` have additive gap at least `p_pi(m)/32`, hence at
least `(m+1)/32`, at the least positive prefix containing all first
occurrences.  The set of retained frequencies and the cutoff both move with
`m`. -/
theorem pi_manyLastFirstOccurrenceLinearGapFrequencies_spec
    (m : ℕ) (hm : 3 ≤ m) :
    10 ^ m ≤
        16 * (piManyLastFirstOccurrenceLinearGapFrequencies m).card ∧
      ∀ r ∈ piManyLastFirstOccurrenceLinearGapFrequencies m,
        1 ≤ r.val + 1 ∧ r.val + 1 ≤ 10 ^ m ∧
          ((m + 1 : ℕ) : ℝ) / 32 ≤
            (piFactorComplexity m : ℝ) / 32 ∧
          (piFactorComplexity m : ℝ) / 32 ≤
            (piLastFirstOccurrencePrefixLength m : ℝ) -
              ‖exponentialSum piOrbit
                (piLastFirstOccurrencePrefixLength m)
                ((r.val + 1 : ℕ) : ℤ)‖ := by
  refine ⟨
    pi_q_le_sixteen_mul_card_manyLastFirstOccurrenceLinearGapFrequencies m hm,
    ?_⟩
  intro r hr
  have hP : 4 ≤ piFactorComplexity m := by
    have hp := pi_factorComplexity_lower_bound m (by omega)
    omega
  have hgap := largeEnergyFrequency_ambient_additiveGap hP
    (piLastFirstOccurrenceEmbedding m)
    (fun i : Fin (piLastFirstOccurrencePrefixLength m) ↦ piOrbit i.val) hr
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i))
    (piLastFirstOccurrencePrefixLength m)] at hgap
  have hp : m + 1 ≤ piFactorComplexity m :=
    pi_factorComplexity_lower_bound m (by omega)
  have hpR : ((m + 1 : ℕ) : ℝ) ≤ piFactorComplexity m := by
    exact_mod_cast hp
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right hpR (by norm_num)
  · simpa only [exponentialSum] using hgap

end Theory.PiDigits.LastFirstOccurrenceLinearGap
