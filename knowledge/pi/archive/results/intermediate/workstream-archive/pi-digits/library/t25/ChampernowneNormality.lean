import Mathlib.Analysis.SpecificLimits.Basic
import TheoryLib.PiDigits.T22ChampernowneDisjunctive
import TheoryLib.PiDigits.T23ChampernowneEpochDiscrepancy
import TheoryLib.PiDigits.T24ChampernownePrefixDiscrepancy

/-!
# T25: full base-10 normality of a fixed artificial real number

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file proves block-frequency normality only for T22's artificial stream
`123456789101112...`. It proves nothing about the decimal digits of pi,
canonical V1 for pi, or sibling V3 for pi.

For a nonempty word `w`, every valid start in the first `N` stream digits is
counted, so occurrences overlap and may cross integer or epoch boundaries.
The denominator is the prefix length `N`; replacing it by the number of valid
starts gives the same limit but is not the statement used here. Words with
leading zeros are ordinary lists and are included without reinterpretation as
decimal representations of natural numbers.
-/

namespace Theory.PiDigits.T25

open Filter Topology
open Theory.PiDigits.T22 Theory.PiDigits.T23 Theory.PiDigits.T24

/-- The first `N` digits of T22's canonical infinite Champernowne stream. -/
def streamPrefix (N : ℕ) : List (Fin 10) :=
  List.ofFn fun i : Fin N => champernowneDigit i

/-- The overlapping occurrence frequency in the first `N` stream digits. -/
noncomputable def blockFrequency (w : List (Fin 10)) (N : ℕ) : ℝ :=
  (finiteContiguousOccurrenceCount w (streamPrefix N) : ℝ) / N

/-- Passing one epoch appends exactly the epoch just completed. -/
theorem completedEpochs_succ_eq (m : ℕ) (hm : 1 ≤ m) :
    completedEpochs (m + 1) = completedEpochs m ++ epoch m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp [completedEpochs, List.range_succ, List.flatMap_append, Nat.add_comm]

/-- The number of digits in completed epochs is monotone in the epoch index. -/
theorem completedEpochs_length_monotone :
    Monotone fun m => (completedEpochs m).length := by
  apply monotone_nat_of_le_succ
  intro m
  by_cases hm : 1 ≤ m
  · rw [completedEpochs_succ_eq m hm, List.length_append]
    omega
  · have : m = 0 := by omega
    subst m
    simp [completedEpochs]

/-- Every finite digit cutoff lies no later than the end of some epoch. -/
theorem exists_epoch_end_after (N : ℕ) :
    ∃ m : ℕ, N ≤ (completedEpochs (m + 1)).length := by
  by_cases hN : N = 0
  · subst N
    exact ⟨0, by simp⟩
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    refine ⟨N, ?_⟩
    rw [completedEpochs_succ_eq N hN1, List.length_append, epoch_length N hN1]
    have hp : 0 < 9 * 10 ^ (N - 1) :=
      Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)
    nlinarith

/-- The first epoch whose endpoint is at or after digit cutoff `N`. -/
noncomputable def epochIndex (N : ℕ) : ℕ :=
  Nat.find (exists_epoch_end_after N)

theorem epochIndex_endpoint (N : ℕ) :
    N ≤ (completedEpochs (epochIndex N + 1)).length := by
  exact Nat.find_spec (exists_epoch_end_after N)

theorem epochIndex_pos {N : ℕ} (hN : 1 ≤ N) : 1 ≤ epochIndex N := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hzero
  have h := epochIndex_endpoint N
  rw [hzero] at h
  simp [completedEpochs] at h
  omega

/-- A positive cutoff is strictly after the epochs preceding its selected epoch. -/
theorem completedEpochs_length_lt_cutoff {N : ℕ} (hN : 1 ≤ N) :
    (completedEpochs (epochIndex N)).length < N := by
  let h := exists_epoch_end_after N
  have hm : 1 ≤ epochIndex N := epochIndex_pos hN
  have hpred : epochIndex N - 1 < epochIndex N :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have hminimal := Nat.find_min h hpred
  have hsucc : epochIndex N - 1 + 1 = epochIndex N := Nat.sub_add_cancel hm
  rw [hsucc] at hminimal
  omega

/-- The selected raw cutoff inside its epoch. -/
noncomputable def epochCutoff (N : ℕ) : ℕ :=
  N - (completedEpochs (epochIndex N)).length

/-- The selected cutoff is no longer than its current epoch. -/
theorem epochCutoff_le_epoch_length {N : ℕ} (hN : 1 ≤ N) :
    epochCutoff N ≤ (epoch (epochIndex N)).length := by
  have hm : 1 ≤ epochIndex N := epochIndex_pos hN
  have hend := epochIndex_endpoint N
  rw [completedEpochs_succ_eq (epochIndex N) hm, List.length_append] at hend
  unfold epochCutoff
  omega

/-- T24's selected arbitrary prefix has exactly the requested digit length. -/
theorem arbitraryPrefix_selected_length {N : ℕ} (hN : 1 ≤ N) :
    (arbitraryPrefix (epochIndex N) (epochCutoff N)).length = N := by
  have hcut := epochCutoff_le_epoch_length hN
  have hstart := (completedEpochs_length_lt_cutoff hN).le
  unfold arbitraryPrefix
  rw [List.length_append, List.length_take_of_le hcut]
  unfold epochCutoff
  omega

/-- T24's selected prefix is the direct length-`N` prefix of T22's stream. -/
theorem arbitraryPrefix_selected_eq_streamPrefix {N : ℕ} (hN : 1 ≤ N) :
    arbitraryPrefix (epochIndex N) (epochCutoff N) = streamPrefix N := by
  have hm : 1 ≤ epochIndex N := epochIndex_pos hN
  have hcut := epochCutoff_le_epoch_length hN
  have hstream := arbitraryPrefix_eq_champernowneDigit_prefix
    (epochIndex N) (epochCutoff N) hm hcut
  have hlen := arbitraryPrefix_selected_length hN
  simpa [streamPrefix, hlen] using hstream

/-- The selected epoch index tends to infinity with the digit cutoff. -/
theorem tendsto_epochIndex_atTop : Tendsto epochIndex atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop ((completedEpochs (b + 1)).length + 1)] with N hN
  by_contra hnot
  have hidx : epochIndex N < b := by omega
  have hmono := completedEpochs_length_monotone (Nat.succ_le_succ hidx.le)
  change (completedEpochs (epochIndex N + 1)).length ≤
    (completedEpochs (b + 1)).length at hmono
  have hend := epochIndex_endpoint N
  omega

/-- Removing one from the selected epoch index still tends to infinity. -/
theorem tendsto_epochIndex_sub_one_atTop :
    Tendsto (fun N => epochIndex N - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have h := tendsto_epochIndex_atTop.eventually (eventually_ge_atTop (b + 1))
  filter_upwards [h] with N hN
  omega

/-- The preceding complete epoch gives the prefix-length lower bound needed
to normalize T24's error term. -/
theorem epoch_prefix_length_lower_bound {N : ℕ} (hN : 1 ≤ N)
    (hm : 2 ≤ epochIndex N) :
    (epochIndex N - 1) * (9 * 10 ^ (epochIndex N - 2)) ≤ N := by
  let m := epochIndex N
  have hm1 : 1 ≤ m - 1 := by omega
  have hsplit := completedEpochs_succ_eq (m - 1) hm1
  have hsplitLen := congrArg List.length hsplit
  have hstart := completedEpochs_length_lt_cutoff hN
  have hsub : m - 1 + 1 = m := by omega
  rw [hsub, List.length_append, epoch_length (m - 1) hm1] at hsplitLen
  have hlen : (m - 1) * (9 * 10 ^ (m - 1 - 1)) ≤
      (completedEpochs m).length := by
    rw [hsplitLen]
    omega
  dsimp [m] at hlen ⊢
  have hexp : epochIndex N - 1 - 1 = epochIndex N - 2 := by omega
  rw [hexp] at hlen
  exact hlen.trans hstart.le

/-- The exponential error scale from T24 is at most reciprocal-linear after
division by the selected prefix length. -/
theorem ten_pow_epochIndex_mul_sub_one_le {N : ℕ} (hN : 1 ≤ N)
    (hm : 2 ≤ epochIndex N) :
    10 ^ (epochIndex N) * (epochIndex N - 1) ≤ 100 * N := by
  have hlower := epoch_prefix_length_lower_bound hN hm
  have hbase : (epochIndex N - 1) * 10 ^ (epochIndex N - 2) ≤ N := by
    calc
      (epochIndex N - 1) * 10 ^ (epochIndex N - 2) ≤
          (epochIndex N - 1) * (9 * 10 ^ (epochIndex N - 2)) := by
        gcongr
        nlinarith [Nat.zero_le (10 ^ (epochIndex N - 2))]
      _ ≤ N := hlower
  have hexponent : epochIndex N = (epochIndex N - 2) + 2 := by omega
  have hpow : 10 ^ epochIndex N = 100 * 10 ^ (epochIndex N - 2) := by
    rw [hexponent, pow_add]
    norm_num
    ring
  calc
    10 ^ epochIndex N * (epochIndex N - 1) =
        100 * ((epochIndex N - 1) * 10 ^ (epochIndex N - 2)) := by
      rw [hpow]
      ring
    _ ≤ 100 * N := Nat.mul_le_mul_left 100 hbase

/-- Real form of the normalized epoch-error estimate. -/
theorem normalized_epoch_error_le (D N : ℕ) (hN : 1 ≤ N)
    (hm : 2 ≤ epochIndex N) :
    ((D : ℝ) * (10 : ℝ) ^ epochIndex N) / N ≤
      (100 * D : ℝ) / ((epochIndex N - 1 : ℕ) : ℝ) := by
  have hcrossNat := Nat.mul_le_mul_left D
    (ten_pow_epochIndex_mul_sub_one_le hN hm)
  have hcrossNat' : D * 10 ^ epochIndex N * (epochIndex N - 1) ≤
      100 * D * N := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcrossNat
  have hcross :
      (D : ℝ) * (10 : ℝ) ^ epochIndex N * ((epochIndex N - 1 : ℕ) : ℝ) ≤
        (100 * D : ℝ) * N := by
    exact_mod_cast hcrossNat'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < ((epochIndex N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ epochIndex N - 1 by omega)
  exact (div_le_div_iff₀ hNpos hmpos).2 hcross

/-- Casting an integer discrepancy measured by `natAbs` to a real absolute
value preserves its bound. -/
theorem natAbs_discrepancy_cast (a b B : ℕ)
    (h : Int.natAbs ((a : ℤ) - (b : ℤ)) ≤ B) :
    abs ((a : ℝ) - (b : ℝ)) ≤ B := by
  rw [← Int.cast_natCast a, ← Int.cast_natCast b, ← Int.cast_sub, ← Int.cast_abs,
    ← Int.natCast_natAbs]
  exact_mod_cast h

/-- T24's finite discrepancy estimate, transferred to the direct length-`N`
prefix and normalized by `N`. -/
theorem scaled_blockFrequency_error_le
    (w : List (Fin 10)) (k N : ℕ) (hwlen : w.length = k) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (hm : max 2 k ≤ epochIndex N) :
    abs ((10 : ℝ) ^ k * blockFrequency w N - 1) ≤
      ((prefixDiscrepancyCoefficient k : ℝ) *
        (10 : ℝ) ^ epochIndex N) / N := by
  have hmT24 : max 1 k ≤ epochIndex N := by omega
  have hcut := epochCutoff_le_epoch_length hN
  have hprefix := arbitraryPrefix_selected_eq_streamPrefix hN
  have hdisc := champernowne_arbitraryPrefix_uniform_discrepancy
    w k (epochIndex N) (epochCutoff N) hwlen hk hmT24 hcut
  have hdisc' :
      Int.natAbs
          ((((10 ^ k * finiteContiguousOccurrenceCount w (streamPrefix N) : ℕ) : ℤ) -
            (N : ℤ))) ≤
        prefixDiscrepancyCoefficient k * 10 ^ epochIndex N := by
    simpa [arbitraryPrefixOccurrenceCount, hprefix, streamPrefix] using hdisc
  have hreal := natAbs_discrepancy_cast
    (10 ^ k * finiteContiguousOccurrenceCount w (streamPrefix N)) N
    (prefixDiscrepancyCoefficient k * 10 ^ epochIndex N) hdisc'
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hreal
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have heq :
      (10 : ℝ) ^ k * blockFrequency w N - 1 =
        ((10 : ℝ) ^ k *
            (finiteContiguousOccurrenceCount w (streamPrefix N) : ℝ) - N) / N := by
    unfold blockFrequency
    field_simp
  rw [heq, abs_div, abs_of_pos hNpos]
  exact div_le_div_of_nonneg_right hreal hNpos.le

/-- The reciprocal-linear majorant for the normalized error tends to zero. -/
theorem tendsto_normalized_epoch_error (D : ℕ) :
    Tendsto
      (fun N => (100 * D : ℝ) / ((epochIndex N - 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hden : Tendsto
      (fun N => ((epochIndex N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_epochIndex_sub_one_atTop
  exact hden.const_div_atTop (100 * D : ℝ)

/-- T24's arbitrary-prefix estimate implies convergence of the frequency
after scaling by the number `10^|w|` of decimal words of that length. -/
theorem tendsto_scaled_blockFrequency
    (w : List (Fin 10)) (hw : w ≠ []) :
    Tendsto
      (fun N => (10 : ℝ) ^ w.length * blockFrequency w N)
      atTop (𝓝 1) := by
  have hk : 1 ≤ w.length := List.length_pos_iff.mpr hw
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero'
  · exact Eventually.of_forall fun N => abs_nonneg _
  · filter_upwards
      [eventually_ge_atTop 1,
        tendsto_epochIndex_atTop.eventually
          (eventually_ge_atTop (max 2 w.length))] with N hN hm
    calc
      abs ((10 : ℝ) ^ w.length * blockFrequency w N - 1) ≤
          ((prefixDiscrepancyCoefficient w.length : ℝ) *
            (10 : ℝ) ^ epochIndex N) / N :=
        scaled_blockFrequency_error_le w w.length N rfl hk hN hm
      _ ≤ (100 * prefixDiscrepancyCoefficient w.length : ℝ) /
          ((epochIndex N - 1 : ℕ) : ℝ) :=
        normalized_epoch_error_le (prefixDiscrepancyCoefficient w.length) N hN
          (le_trans (le_max_left 2 w.length) hm)
  · exact tendsto_normalized_epoch_error (prefixDiscrepancyCoefficient w.length)

/-- The explicit overlapping block-frequency limit for every nonempty decimal
word in T22's stream. The right side is exactly `10^(-|w|)`.

This is full base-10 block-frequency normality of the fixed artificial
Champernowne real number. It includes leading-zero words and proves nothing about pi,
canonical V1 for pi, or sibling V3 for pi.
-/
theorem champernowne_full_baseTen_normality
    (w : List (Fin 10)) (hw : w ≠ []) :
    Tendsto
      (fun N =>
        (finiteContiguousOccurrenceCount w
          (List.ofFn fun i : Fin N => champernowneDigit i) : ℝ) / N)
      atTop
      (𝓝 ((10 : ℝ) ^ (-(w.length : ℤ)))) := by
  have hscaled := tendsto_scaled_blockFrequency w hw
  have hdiv := hscaled.div_const ((10 : ℝ) ^ w.length)
  have hpow : (10 : ℝ) ^ w.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have hreciprocal :
      Tendsto (blockFrequency w) atTop
        (𝓝 ((1 : ℝ) / (10 : ℝ) ^ w.length)) := by
    convert hdiv using 1
    all_goals simp [hpow]
  simpa [zpow_neg, blockFrequency, streamPrefix] using hreciprocal

/-- Explicit specialization showing that every nonempty word beginning with
zero has the same base-10 block-frequency limit. -/
theorem champernowne_leadingZero_blockFrequency
    (d : List (Fin 10)) :
    Tendsto
      (fun N =>
        (finiteContiguousOccurrenceCount ((0 : Fin 10) :: d)
          (List.ofFn fun i : Fin N => champernowneDigit i) : ℝ) / N)
      atTop
      (𝓝 ((10 : ℝ) ^ (-(((0 : Fin 10) :: d).length : ℤ)))) := by
  exact champernowne_full_baseTen_normality ((0 : Fin 10) :: d) (by simp)

#print axioms Theory.PiDigits.T25.epoch_prefix_length_lower_bound
#print axioms Theory.PiDigits.T25.tendsto_normalized_epoch_error
#print axioms Theory.PiDigits.T25.champernowne_full_baseTen_normality
#print axioms Theory.PiDigits.T25.champernowne_leadingZero_blockFrequency

end Theory.PiDigits.T25
