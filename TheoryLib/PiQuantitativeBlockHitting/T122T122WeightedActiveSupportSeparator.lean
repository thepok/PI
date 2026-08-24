import TheoryLib.PiQuantitativeBlockHitting.T121T121WeightedNaturalScaleCriterion

/-!
# T122: weighted strictness on the actual Jackson support

T121's first separator uses the crude endpoint frequency `2*q`, which is
inside T19's stated pointwise window but outside the active order-`q` Jackson
support when `q = 1`. This file proves a stronger separation: the weighted
premise remains strictly weaker even when the pointwise premise is restricted
to frequencies that actually occur in the Jackson presentation.

The witness is four equally spaced points followed by one extra zero. At
`q = 1`, every active nonzero Jackson frequency is `±1`; the normalized sums
there equal `1/5`. This violates T19's active pointwise threshold `1/8`, while
the complete weighted load is at most `4/5`, below the weighted threshold `1`.

No estimate is proved for the decimal pi orbit, and V1 remains open.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.WeightedNaturalScaleFrontier

namespace T6 = Theory.PiDigits.PiNaturalScaleResonanceObstruction
namespace T18 = Theory.PiDigits.SharperNaturalScaleResonance
namespace T19 = Theory.PiDigits.ExactNaturalScaleResonance
namespace T27 = Theory.PiDigits.T27

/-- A common normalized upper bound on every active Jackson index controls the
weighted load by four times that bound, using T19's exact coefficient mass. -/
theorem jacksonWeightedFourierLoad_le_four_mul_of_active_bound
    (x : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (hactive : ∀ i : T6.JacksonIndex q,
      T6.jacksonFrequency i ≠ 0 →
        ‖T27.exponentialSum x N (T6.jacksonFrequency i)‖ / (N : ℝ) ≤ B) :
    jacksonWeightedFourierLoad x N q ≤ 4 * B := by
  classical
  have hmass :
      (∑ i : T6.JacksonIndex q,
        |T6.jacksonCoefficient q q i|) = 4 := by
    rw [T19.jacksonCoefficient_mass_general q q hq hq]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hqR]
    norm_num
  unfold jacksonWeightedFourierLoad normalizedWeightedFourierLoad
  calc
    (∑ i with T6.jacksonFrequency i ≠ 0,
        |T6.jacksonCoefficient q q i| *
          ‖T27.exponentialSum x N (T6.jacksonFrequency i)‖) / (N : ℝ) =
      ∑ i with T6.jacksonFrequency i ≠ 0,
        |T6.jacksonCoefficient q q i| *
          (‖T27.exponentialSum x N (T6.jacksonFrequency i)‖ /
            (N : ℝ)) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ ∑ i with T6.jacksonFrequency i ≠ 0,
        |T6.jacksonCoefficient q q i| * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hactive i (Finset.mem_filter.mp hi).2) (abs_nonneg _)
    _ = (∑ i with T6.jacksonFrequency i ≠ 0,
        |T6.jacksonCoefficient q q i|) * B := by
      rw [Finset.sum_mul]
    _ ≤ (∑ i : T6.JacksonIndex q,
        |T6.jacksonCoefficient q q i|) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> simp [abs_nonneg]
    _ = 4 * B := by rw [hmass]

/-- The weighted finite premise follows already from T19's pointwise threshold
restricted to active Jackson indices. -/
theorem active_exact_finite_frequency_hypothesis_implies_weighted
    (x : ℕ → ℝ) (N q : ℕ) (hq : 0 < q)
    (hactive : ∀ i : T6.JacksonIndex q,
      T6.jacksonFrequency i ≠ 0 →
        ‖T27.exponentialSum x N (T6.jacksonFrequency i)‖ / (N : ℝ) <
          1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) :
    jacksonWeightedFourierLoad x N q <
      1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) := by
  let t : ℝ :=
    1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hload : jacksonWeightedFourierLoad x N q ≤ 4 * t := by
    exact jacksonWeightedFourierLoad_le_four_mul_of_active_bound
      x N q hq t ht (fun i hi => (hactive i hi).le)
  have hhalf :
      4 * t =
        (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) / 2 := by
    dsimp [t]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hqR]
    ring
  rw [hhalf] at hload
  have hc :
      0 < 1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) := by
    positivity
  linarith

/-- Four equally spaced points followed by one extra zero. -/
def uniformGridFourPlusZero : ℕ → ℝ := fun j =>
  if j < 4 then T18.uniformGrid 4 j else 0

lemma uniformGridFourPlusZero_exponentialSum (h : ℤ) :
    T27.exponentialSum uniformGridFourPlusZero 5 h =
      T27.exponentialSum (T18.uniformGrid 4) 4 h + 1 := by
  simp only [T27.exponentialSum]
  rw [show 5 = 4 + 1 by norm_num, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [uniformGridFourPlusZero, Finset.mem_range.mp hj]
  · simp [uniformGridFourPlusZero, T27.phase]

lemma uniformGridFourPlusZero_norm_div_eq_one_fifth
    (h : ℤ) (hzero : h ≠ 0) (hbound : h.natAbs ≤ 2) :
    ‖T27.exponentialSum uniformGridFourPlusZero 5 h‖ / (5 : ℝ) =
      1 / 5 := by
  have hk : 0 < h.natAbs := Int.natAbs_pos.mpr hzero
  have hk4 : h.natAbs < 4 := by omega
  have hpos := T18.uniformGrid_exponentialSum_nat_eq_zero
    h.natAbs 4 (by norm_num) hk hk4
  have hgrid : T27.exponentialSum (T18.uniformGrid 4) 4 h = 0 := by
    rcases Int.natAbs_eq h with hh | hh
    · rw [hh, hpos]
    · rw [hh, T18.exponentialSum_neg, hpos, map_zero]
  rw [uniformGridFourPlusZero_exponentialSum, hgrid]
  norm_num

lemma uniformGridFourPlusZero_weighted_small :
    jacksonWeightedFourierLoad uniformGridFourPlusZero 5 1 <
      1 / (3 * (1 : ℝ)) + 2 / (3 * (1 : ℝ) ^ 3) := by
  have hload :
      jacksonWeightedFourierLoad uniformGridFourPlusZero 5 1 ≤
        4 * (1 / 5 : ℝ) := by
    refine jacksonWeightedFourierLoad_le_four_mul_of_active_bound
      uniformGridFourPlusZero 5 1 (by norm_num) (1 / 5 : ℝ)
      (by norm_num) ?_
    intro i hi
    have hfreq := jacksonFrequency_one_natAbs_eq_one_of_ne_zero i hi
    exact (uniformGridFourPlusZero_norm_div_eq_one_fifth
      (T6.jacksonFrequency i) hi (by omega)).le
  exact hload.trans_lt (by norm_num)

/-- One active order-one Jackson index carrying frequency `+1`. -/
def qOnePositiveEdgeIndex : T6.JacksonIndex 1 :=
  Sum.inr
    ((false, ⟨0, by norm_num⟩), (true, ⟨0, by norm_num⟩))

lemma qOnePositiveEdgeIndex_frequency :
    T6.jacksonFrequency qOnePositiveEdgeIndex = 1 := by
  simp [qOnePositiveEdgeIndex, T6.jacksonFrequency, T6.edgeFrequency]

/-- Strictness survives restriction to the actual Jackson support. The witness
passes the weighted test but fails T19's pointwise threshold at an active
frequency, not at a dead endpoint frequency. -/
theorem weighted_finite_frequency_hypothesis_strict_vs_active_exact :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      (jacksonWeightedFourierLoad x N q <
        1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) ∧
      ¬ (∀ i : T6.JacksonIndex q,
        T6.jacksonFrequency i ≠ 0 →
          ‖T27.exponentialSum x N (T6.jacksonFrequency i)‖ / (N : ℝ) <
            1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) := by
  refine ⟨uniformGridFourPlusZero, 5, 1, by norm_num, by norm_num,
    uniformGridFourPlusZero_weighted_small, ?_⟩
  intro hactive
  have hone := hactive qOnePositiveEdgeIndex (by
    rw [qOnePositiveEdgeIndex_frequency]
    norm_num)
  rw [qOnePositiveEdgeIndex_frequency] at hone
  rw [uniformGridFourPlusZero_norm_div_eq_one_fifth
    1 (by norm_num) (by norm_num)] at hone
  norm_num at hone

end Theory.PiDigits.WeightedNaturalScaleFrontier

#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.jacksonWeightedFourierLoad_le_four_mul_of_active_bound
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.active_exact_finite_frequency_hypothesis_implies_weighted
#print axioms Theory.PiDigits.WeightedNaturalScaleFrontier.weighted_finite_frequency_hypothesis_strict_vs_active_exact
