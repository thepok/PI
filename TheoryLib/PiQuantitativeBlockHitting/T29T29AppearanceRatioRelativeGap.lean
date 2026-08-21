import TheoryLib.PiQuantitativeBlockHitting.T28T28LastFirstOccurrenceLinearGap

/-!
# T29: conditional relative gap from an appearance-ratio bound

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T28 gives an additive saving `P / 32` for at least one sixteenth of the
frequencies `1, ..., 10^m`, where `P` is pi's length-`m` factor complexity and
the ambient length is the least positive prefix `L` containing every
canonical first occurrence.  This file records the exact conditional bridge
from an appearance-ratio estimate `L <= C * P` to the relative bound
`|S| / L <= 1 - 1 / (32 * C)`.

No such appearance-ratio estimate for pi is proved here.  Even a uniform
The constant `C` would control only T28's moving positive-proportion frequency
set and would give a fixed relative saving, not cancellation tending to zero
at every natural-scale frequency.  Therefore this conditional result does
not imply decimal disjunctivity or V1.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.AppearanceRatioRelativeGap

open Theory.PiDigits.DigitChangeFourierDefect
open Theory.PiDigits.FactorComplexity
open Theory.PiDigits.LastFirstOccurrenceLinearGap

/-- An additive gap `P / 32` becomes the relative gap
`1 / (32 * C)` when the positive ambient length `N` is at most `C * P`.
Both positivity hypotheses are explicit because the conclusion divides by
`N` and `C`. -/
theorem normalized_norm_le_one_sub_inv_thirtyTwo_mul_of_appearanceRatio
    {P N C : ℕ} (hN : 0 < N) (hC : 0 < C)
    (happearance : N ≤ C * P) {z : ℂ}
    (hgap : (P : ℝ) / 32 ≤ (N : ℝ) - ‖z‖) :
    ‖z‖ / (N : ℝ) ≤ 1 - 1 / (32 * (C : ℝ)) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hCR : 0 < (C : ℝ) := by exact_mod_cast hC
  have happearanceR : (N : ℝ) ≤ (C : ℝ) * (P : ℝ) := by
    exact_mod_cast happearance
  have hrelativeSaving :
      (N : ℝ) / (32 * (C : ℝ)) ≤ (P : ℝ) / 32 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hCR)]
    nlinarith
  have hraw :
      ‖z‖ ≤ (N : ℝ) - (N : ℝ) / (32 * (C : ℝ)) := by
    linarith
  rw [div_le_iff₀ hNR]
  calc
    ‖z‖ ≤ (N : ℝ) - (N : ℝ) / (32 * (C : ℝ)) := hraw
    _ = (1 - 1 / (32 * (C : ℝ))) * (N : ℝ) := by ring

/-- Under the explicit appearance-ratio hypothesis, every frequency in T28's
retained set has normalized exponential-sum norm at most
`1 - 1 / (32 * C)`. -/
theorem pi_normalized_exponentialSum_le_of_mem_manyLastFirstOccurrence
    (m C : ℕ) (hm : 3 ≤ m) (hC : 0 < C)
    (happearance :
      piLastFirstOccurrencePrefixLength m ≤ C * piFactorComplexity m)
    {r : Fin (10 ^ m)}
    (hr : r ∈ piManyLastFirstOccurrenceLinearGapFrequencies m) :
    ‖exponentialSum piOrbit (piLastFirstOccurrencePrefixLength m)
        ((r.val + 1 : ℕ) : ℤ)‖ /
        (piLastFirstOccurrencePrefixLength m : ℝ) ≤
      1 - 1 / (32 * (C : ℝ)) := by
  have hspec :=
    pi_manyLastFirstOccurrenceLinearGapFrequencies_spec m hm
  exact
    normalized_norm_le_one_sub_inv_thirtyTwo_mul_of_appearanceRatio
      (piLastFirstOccurrencePrefixLength_pos m) hC happearance
      (hspec.2 r hr).2.2.2

/-- **Conditional pi specialization.** If the least first-occurrence covering
prefix has length at most `C` times factor complexity, then at least one
sixteenth of `1, ..., 10^m` lies in the retained set, and every retained
frequency has the displayed relative saving.  This theorem does not provide
the appearance-ratio hypothesis and does not imply V1. -/
theorem pi_manyLastFirstOccurrenceRelativeGapFrequencies_spec
    (m C : ℕ) (hm : 3 ≤ m) (hC : 0 < C)
    (happearance :
      piLastFirstOccurrencePrefixLength m ≤ C * piFactorComplexity m) :
    10 ^ m ≤
        16 * (piManyLastFirstOccurrenceLinearGapFrequencies m).card ∧
      ∀ r ∈ piManyLastFirstOccurrenceLinearGapFrequencies m,
        1 ≤ r.val + 1 ∧ r.val + 1 ≤ 10 ^ m ∧
          ‖exponentialSum piOrbit (piLastFirstOccurrencePrefixLength m)
              ((r.val + 1 : ℕ) : ℤ)‖ /
              (piLastFirstOccurrencePrefixLength m : ℝ) ≤
            1 - 1 / (32 * (C : ℝ)) := by
  have hspec :=
    pi_manyLastFirstOccurrenceLinearGapFrequencies_spec m hm
  refine ⟨hspec.1, ?_⟩
  intro r hr
  exact ⟨(hspec.2 r hr).1, (hspec.2 r hr).2.1,
    pi_normalized_exponentialSum_le_of_mem_manyLastFirstOccurrence
      m C hm hC happearance hr⟩

end Theory.PiDigits.AppearanceRatioRelativeGap
