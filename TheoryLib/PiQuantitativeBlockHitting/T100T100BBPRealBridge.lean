import TheoryLib.PiQuantitativeBlockHitting.T99T99BBPFiniteTail
import TheoryLib.PiQuantitativeBlockHitting.T35T35OversampledBBPGridStability

/-!
# T100: real and conditional infinite-series bridges for BBP partial sums

The initial declarations in this module only coerce finite rational identities
to the reals. Any later infinite-series conclusion must retain its `HasSum`
hypothesis explicitly; no BBP identity for pi is asserted here.
-/

namespace Theory.PiDigits.T100BBPRealBridge

open scoped BigOperators
open T77SelectedPadicDefectShell T98BBPArchimedeanTerm

/-- The canonical rational BBP coefficient at index `k`, coerced to `ℝ`. -/
noncomputable def bbpRealTerm (k : ℕ) : ℝ :=
  (bbpCombinedTerm k : ℝ)

/-- The canonical rational BBP partial sum through index `M`, coerced to `ℝ`. -/
noncomputable def bbpRealPartial (M : ℕ) : ℝ :=
  (bbpPartial M : ℝ)

/-- The rational successor identity commutes with the real coercion. -/
theorem bbpRealPartial_succ (M : ℕ) :
    bbpRealPartial (M + 1) = bbpRealPartial M + bbpRealTerm (M + 1) := by
  simp only [bbpRealPartial, bbpRealTerm]
  rw [bbpPartial_succ, Rat.cast_add]

private theorem bbpPartial_zero_eq_bbpCombinedTerm_zero :
    bbpPartial 0 = bbpCombinedTerm 0 := by
  simp only [bbpPartial, polePartial, bbpCombinedTerm, Nat.zero_add,
    Finset.sum_range_one]

/-- The inclusive partial sum is the real sum over indices `0` through `M`. -/
theorem bbpRealPartial_eq_sum_range (M : ℕ) :
    bbpRealPartial M = ∑ k ∈ Finset.range (M + 1), bbpRealTerm k := by
  induction M with
  | zero =>
    show ((bbpPartial 0 : ℚ) : ℝ) = _
    simp only [bbpRealTerm, bbpPartial_zero_eq_bbpCombinedTerm_zero]
    rw [Nat.zero_add, Finset.sum_range_one]
  | succ n ih =>
    rw [bbpRealPartial_succ, Finset.sum_range_succ, ih]

/-- Removing the inclusive prefix `0..K` leaves the tail beginning at `K+1`. -/
theorem hasSum_real_bbpCombinedTerm_tail {x : ℝ}
    (hsum : HasSum bbpRealTerm x) (K : ℕ) :
    HasSum (fun j : ℕ ↦ bbpRealTerm (K + j + 1))
      (x - bbpRealPartial K) := by
  have hfun : (fun j : ℕ ↦ bbpRealTerm (K + j + 1)) =
      fun n : ℕ ↦ bbpRealTerm (n + (K + 1)) := by
    funext j
    congr 1
    omega
  rw [hfun, bbpRealPartial_eq_sum_range,
    hasSum_nat_add_iff' (f := bbpRealTerm) (K + 1)]
  exact hsum

private theorem hasSum_geometric_tail (K : ℕ) :
    HasSum (fun j : ℕ ↦ 4 / (16 : ℝ) ^ (K + j + 1))
      (4 / (15 * (16 : ℝ) ^ K)) := by
  have hg := hasSum_geometric_of_lt_one
    (r := (1 : ℝ) / 16) (by positivity) (by norm_num)
  have hm := hg.mul_left (4 / (16 : ℝ) ^ (K + 1))
  convert hm using 1
  · funext j
    rw [show K + j + 1 = (K + 1) + j by omega, pow_add]
    norm_num [div_pow]
    ring
  · field_simp
    ring

/-- An explicit sum hypothesis gives one-sidedness and the geometric error bound. -/
theorem real_bbp_hasSum_tail_bounds {x : ℝ}
    (hsum : HasSum bbpRealTerm x) (K : ℕ) :
    bbpRealPartial K ≤ x ∧
      x - bbpRealPartial K ≤ 4 / (15 * (16 : ℝ) ^ K) ∧
      x - bbpRealPartial K < 1 / (16 : ℝ) ^ K := by
  have ht := hasSum_real_bbpCombinedTerm_tail hsum K
  have hz : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0 := hasSum_zero
  have hnonneg : 0 ≤ x - bbpRealPartial K := by
    apply hasSum_le (hf := hz) (hg := ht)
    intro j
    simp only [bbpRealTerm]
    exact_mod_cast (bbpCombinedTerm_pos (K + j + 1)).le
  have hg := hasSum_geometric_tail K
  have hupper : x - bbpRealPartial K ≤ 4 / (15 * (16 : ℝ) ^ K) := by
    apply hasSum_le (hf := ht) (hg := hg)
    intro j
    have hc : bbpRealTerm (K + j + 1) ≤
        (((4 : ℚ) / (16 : ℚ) ^ (K + j + 1) : ℚ) : ℝ) := by
      simp only [bbpRealTerm]
      exact Rat.cast_le.2 (bbpCombinedTerm_lt_geometric (K + j + 1)).le
    push_cast at hc
    exact hc
  have hstrict : 4 / (15 * (16 : ℝ) ^ K) < 1 / (16 : ℝ) ^ K := by
    have hp : (0 : ℝ) < 16 ^ K := by positivity
    calc
      4 / (15 * (16 : ℝ) ^ K) = (4 / 15) / (16 : ℝ) ^ K := by ring
      _ < 1 / (16 : ℝ) ^ K :=
        (div_lt_div_iff_of_pos_right hp).2 (by norm_num)
  constructor
  · linarith
  exact ⟨hupper, lt_of_le_of_lt hupper hstrict⟩

/-- Conditional T35 specialization for the canonical BBP partial sums.

The BBP series identity and the published irrationality-measure input remain
explicit premises. This theorem does not establish either premise or decimal
orbit density. -/
theorem pi_eventually_decimalBlockCode_bbpPartial_sevenOversampled_eq
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8)
    (hBBP : HasSum bbpRealTerm Real.pi) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      Theory.PiDigits.OversampledBBPGridStability.decimalBlockCode
          (bbpRealPartial (7 * N)) N m =
        Theory.PiDigits.OversampledBBPGridStability.decimalBlockCode
          Real.pi N m := by
  apply
    Theory.PiDigits.OversampledBBPGridStability.pi_eventually_decimalBlockCode_sevenOversampled_eq
      (a := bbpRealPartial) hSource
  · intro K
    exact (real_bbp_hasSum_tail_bounds hBBP K).1
  · intro K
    exact (real_bbp_hasSum_tail_bounds hBBP K).2.2

end Theory.PiDigits.T100BBPRealBridge
