import TheoryLib.PiQuantitativeBlockHitting.T163T163EvenBBPDyadicLift
import TheoryLib.PiQuantitativeBlockHitting.T155T155DelayedBBPPhaseTransfer

/-!
# T164: quadratic BBP tails and sharpened delayed phase transfer

The cancellation inside one four-pole BBP row gives a quadratic, rather than
constant, Archimedean coefficient bound.  This module turns that finite row
estimate into explicit bounds for the actual BBP tail and its sevenfold
decimal scaling, then feeds the upper bound into T155's delayed phase
comparison.  No carrier cancellation or V1 conclusion is asserted.
-/

noncomputable section

open scoped BigOperators

namespace Theory.PiDigits.T164QuadraticBBPTailTransfer

open Finset
open Theory.PiDigits.T98BBPArchimedeanTerm
open Theory.PiDigits.T100BBPRealBridge
open Theory.PiDigits.T104BBPSeriesIdentity
open Theory.PiDigits.T106BBPForcedOrbit
open Theory.PiDigits.T155DelayedBBPPhaseTransfer

/-- The quadratic denominator at the first omitted BBP row. -/
def bbpTailScale (M : ℕ) : ℝ :=
  ((8 * M + 9 : ℕ) : ℝ) * ((8 * M + 10 : ℕ) : ℝ)

/-- The corresponding scale after sevenfold sampling. -/
def sampledBBPTailScale (t : ℕ) : ℝ :=
  ((56 * t + 9 : ℕ) : ℝ) * ((56 * t + 10 : ℕ) : ℝ)

private theorem bbpTailScale_pos (M : ℕ) : 0 < bbpTailScale M := by
  unfold bbpTailScale
  positivity

private theorem sampledBBPTailScale_pos (t : ℕ) :
    0 < sampledBBPTailScale t := by
  unfold sampledBBPTailScale
  positivity

/-- The exact four-pole row lies between the two elementary quadratic
envelopes coming from `4 ≤ Q(x) < 15`. -/
theorem bbpCombinedTerm_quadratic_bounds (j : ℕ) :
    (4 : ℚ) /
          (((8 * j + 1 : ℕ) : ℚ) * ((8 * j + 2 : ℕ) : ℚ) * 16 ^ j) ≤
        bbpCombinedTerm j ∧
      bbpCombinedTerm j <
        (15 : ℚ) /
          (((8 * j + 1 : ℕ) : ℚ) * ((8 * j + 2 : ℕ) : ℚ) * 16 ^ j) := by
  rw [bbpCombinedTerm_eq]
  constructor <;> push_cast
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    have h1 : (0 : ℚ) ≤ j * 16 ^ j := by positivity
    have h2 : (0 : ℚ) ≤ j ^ 2 * 16 ^ j := by positivity
    have h3 : (0 : ℚ) ≤ j ^ 3 * 16 ^ j := by positivity
    have h4 : (0 : ℚ) ≤ j ^ 4 * 16 ^ j := by positivity
    have hp : (0 : ℚ) < 16 ^ j := by positivity
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    have h1 : (0 : ℚ) ≤ j * 16 ^ j := by positivity
    have h2 : (0 : ℚ) ≤ j ^ 2 * 16 ^ j := by positivity
    have h3 : (0 : ℚ) ≤ j ^ 3 * 16 ^ j := by positivity
    have hp : (0 : ℚ) < 16 ^ j := by positivity
    nlinarith

private theorem bbpRealTerm_quadratic_upper (j : ℕ) :
    bbpRealTerm j <
      15 /
        (((8 * j + 1 : ℕ) : ℝ) * ((8 * j + 2 : ℕ) : ℝ) * 16 ^ j) := by
  unfold bbpRealTerm
  have h : ((bbpCombinedTerm j : ℚ) : ℝ) <
      (((15 : ℚ) /
        (((8 * j + 1 : ℕ) : ℚ) * ((8 * j + 2 : ℕ) : ℚ) * 16 ^ j) : ℚ) : ℝ) :=
    Rat.cast_lt.2 (bbpCombinedTerm_quadratic_bounds j).2
  norm_num at h ⊢
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    Rat.cast_div, Rat.cast_pow] using h

private theorem bbpRealTerm_quadratic_lower (j : ℕ) :
    4 /
          (((8 * j + 1 : ℕ) : ℝ) * ((8 * j + 2 : ℕ) : ℝ) * 16 ^ j) ≤
      bbpRealTerm j := by
  unfold bbpRealTerm
  have h :
      ((((4 : ℚ) /
        (((8 * j + 1 : ℕ) : ℚ) * ((8 * j + 2 : ℕ) : ℚ) * 16 ^ j) : ℚ) : ℝ) ≤
        ((bbpCombinedTerm j : ℚ) : ℝ)) :=
    Rat.cast_le.2 (bbpCombinedTerm_quadratic_bounds j).1
  norm_num at h ⊢
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    Rat.cast_div, Rat.cast_pow] using h

private theorem hasSum_quadratic_geometric_majorant (M : ℕ) :
    HasSum
      (fun j : ℕ ↦
        15 / (bbpTailScale M * (16 : ℝ) ^ (M + j + 1)))
      (1 / (bbpTailScale M * (16 : ℝ) ^ M)) := by
  have hg := hasSum_geometric_of_lt_one
    (r := (1 : ℝ) / 16) (by positivity) (by norm_num)
  have hm := hg.mul_left (15 / (bbpTailScale M * (16 : ℝ) ^ (M + 1)))
  convert hm using 1
  · funext j
    rw [show M + j + 1 = (M + 1) + j by omega, pow_add]
    norm_num [div_pow]
    ring
  · have hs := bbpTailScale_pos M
    field_simp
    ring

private theorem bbp_tail_strictly_above_first (M : ℕ) :
    bbpRealTerm (M + 1) < Real.pi - bbpRealPartial M := by
  have htail := real_bbp_hasSum_tail_bounds bbpRealTerm_hasSum_pi (M + 1)
  have hnext : bbpRealPartial (M + 1) < Real.pi := by
    have hs := bbpRealPartial_succ (M + 1)
    have hp : 0 < bbpRealTerm (M + 2) := by
      simpa only [bbpRealTerm, Rat.cast_pos] using bbpCombinedTerm_pos (M + 2)
    have hstep : bbpRealPartial (M + 1) < bbpRealPartial (M + 2) := by
      linarith
    exact hstep.trans_le
      (real_bbp_hasSum_tail_bounds bbpRealTerm_hasSum_pi (M + 2)).1
  rw [bbpRealPartial_succ] at hnext
  linarith

/-- Explicit finite quadratic bounds for the actual infinite BBP tail. -/
theorem real_bbp_tail_quadratic_bounds (M : ℕ) :
    1 / (4 * bbpTailScale M * (16 : ℝ) ^ M) <
        Real.pi - bbpRealPartial M ∧
      Real.pi - bbpRealPartial M <
        1 / (bbpTailScale M * (16 : ℝ) ^ M) := by
  constructor
  · have hfirst := bbp_tail_strictly_above_first M
    have hrow := bbpRealTerm_quadratic_lower (M + 1)
    have hs := bbpTailScale_pos M
    have heq :
        4 /
            (((8 * (M + 1) + 1 : ℕ) : ℝ) *
              ((8 * (M + 1) + 2 : ℕ) : ℝ) * 16 ^ (M + 1)) =
          1 / (4 * bbpTailScale M * (16 : ℝ) ^ M) := by
      unfold bbpTailScale
      push_cast
      field_simp
      ring
    rw [heq] at hrow
    exact hrow.trans_lt hfirst
  · have ht := hasSum_real_bbpCombinedTerm_tail bbpRealTerm_hasSum_pi M
    have hg := hasSum_quadratic_geometric_majorant M
    have hle (j : ℕ) :
        bbpRealTerm (M + j + 1) ≤
          15 / (bbpTailScale M * (16 : ℝ) ^ (M + j + 1)) := by
      have hr := (bbpRealTerm_quadratic_upper (M + j + 1)).le
      have hden : bbpTailScale M ≤
          ((8 * (M + j + 1) + 1 : ℕ) : ℝ) *
            ((8 * (M + j + 1) + 2 : ℕ) : ℝ) := by
        unfold bbpTailScale
        push_cast
        nlinarith
      have hp : (0 : ℝ) < 16 ^ (M + j + 1) := by positivity
      calc
        bbpRealTerm (M + j + 1) ≤
            15 /
              (((8 * (M + j + 1) + 1 : ℕ) : ℝ) *
                ((8 * (M + j + 1) + 2 : ℕ) : ℝ) * 16 ^ (M + j + 1)) := hr
        _ ≤ 15 / (bbpTailScale M * 16 ^ (M + j + 1)) := by
          apply div_le_div_of_nonneg_left (by norm_num)
          · exact mul_pos (bbpTailScale_pos M) hp
          · exact mul_le_mul_of_nonneg_right hden hp.le
    have hzero : bbpRealTerm (M + 1) <
        15 / (bbpTailScale M * (16 : ℝ) ^ (M + 0 + 1)) := by
      have h := bbpRealTerm_quadratic_upper (M + 1)
      unfold bbpTailScale
      convert h using 1
    have hstrict := ht.summable.tsum_lt_tsum (i := 0)
      (fun j ↦ hle j) hzero hg.summable
    rw [ht.tsum_eq, hg.tsum_eq] at hstrict
    exact hstrict

/-- Sevenfold decimal scaling converts the quadratic BBP tail into the exact
`rho^t / Lambda_t` scale. -/
theorem sampledBBPError_quadratic_bounds (t : ℕ) :
    bbpErrorRatio ^ t / (4 * sampledBBPTailScale t) < sampledBBPError t ∧
      sampledBBPError t < bbpErrorRatio ^ t / sampledBBPTailScale t := by
  have ht := real_bbp_tail_quadratic_bounds (7 * t)
  have h10 : (0 : ℝ) < 10 ^ t := by positivity
  have hscale : bbpTailScale (7 * t) = sampledBBPTailScale t := by
    unfold bbpTailScale sampledBBPTailScale
    push_cast
    ring
  have hratio : bbpErrorRatio ^ t =
      (10 : ℝ) ^ t / (16 : ℝ) ^ (7 * t) := by
    rw [bbpErrorRatio, div_pow]
    congr 1
    rw [pow_mul]
  rw [hscale] at ht
  constructor
  · calc
      bbpErrorRatio ^ t / (4 * sampledBBPTailScale t) =
          (10 : ℝ) ^ t *
            (1 / (4 * sampledBBPTailScale t * (16 : ℝ) ^ (7 * t))) := by
        rw [hratio]
        ring
      _ < (10 : ℝ) ^ t * (Real.pi - bbpRealPartial (7 * t)) :=
        mul_lt_mul_of_pos_left ht.1 h10
      _ = sampledBBPError t := by
        unfold sampledBBPError sampledBBPValue
        rfl
  · calc
      sampledBBPError t =
          (10 : ℝ) ^ t * (Real.pi - bbpRealPartial (7 * t)) := by
        unfold sampledBBPError sampledBBPValue
        rfl
      _ < (10 : ℝ) ^ t *
          (1 / (sampledBBPTailScale t * (16 : ℝ) ^ (7 * t))) :=
        mul_lt_mul_of_pos_left ht.2 h10
      _ = bbpErrorRatio ^ t / sampledBBPTailScale t := by
        rw [hratio]
        ring

/-- Pointwise delayed phase transfer with the quadratic BBP-tail saving. -/
theorem norm_phase_pi_sub_delayedBBPValue_quadratic_lt
    (h : ℤ) (k n : ℕ) (hh : h ≠ 0) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ <
      2 * Real.pi * (h.natAbs : ℝ) *
        (bbpErrorRatio ^ (n + k) /
          ((10 : ℝ) ^ k * sampledBBPTailScale (n + k))) := by
  have hbase := norm_phase_pi_sub_delayedBBPValue_le h k n
  have herr := (sampledBBPError_quadratic_bounds (n + k)).2
  have habs : (0 : ℝ) < h.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hh
  have hcoef : 0 < 2 * Real.pi * (h.natAbs : ℝ) := by positivity
  have h10 : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  calc
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) *
        (sampledBBPError (n + k) / (10 : ℝ) ^ k) := hbase
    _ < 2 * Real.pi * (h.natAbs : ℝ) *
        ((bbpErrorRatio ^ (n + k) / sampledBBPTailScale (n + k)) /
          (10 : ℝ) ^ k) := by
      exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right herr h10) hcoef
    _ = 2 * Real.pi * (h.natAbs : ℝ) *
        (bbpErrorRatio ^ (n + k) /
          ((10 : ℝ) ^ k * sampledBBPTailScale (n + k))) := by ring

/-- Natural-window specialization of the sharpened pointwise transfer. -/
theorem norm_phase_pi_sub_delayedBBPValue_quadratic_natural_lt
    (h : ℤ) (k n : ℕ) (hh : h ≠ 0)
    (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) /
        sampledBBPTailScale (n + k) := by
  have hbound := norm_phase_pi_sub_delayedBBPValue_quadratic_lt h k n hh
  have h10 : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hratio : (h.natAbs : ℝ) / (10 : ℝ) ^ k < 2 := by
    rw [div_lt_iff₀ h10]
    exact_mod_cast hfreq
  have hs : 0 < sampledBBPTailScale (n + k) := sampledBBPTailScale_pos _
  have hratioPos : 0 < bbpErrorRatio := by norm_num [bbpErrorRatio]
  have hr : 0 < bbpErrorRatio ^ (n + k) := pow_pos hratioPos _
  have habslt : (h.natAbs : ℝ) < 2 * (10 : ℝ) ^ k := by
    rw [div_lt_iff₀ h10] at hratio
    exact hratio
  calc
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ <
      2 * Real.pi * (h.natAbs : ℝ) *
        (bbpErrorRatio ^ (n + k) /
          ((10 : ℝ) ^ k * sampledBBPTailScale (n + k))) := hbound
    _ < 4 * Real.pi * bbpErrorRatio ^ (n + k) /
        sampledBBPTailScale (n + k) := by
      field_simp
      nlinarith [Real.pi_pos]

private theorem finite_geometric_tail_lt (m N : ℕ) :
    (∑ j ∈ range N, bbpErrorRatio ^ (m + j)) <
      bbpErrorRatio ^ m / (1 - bbpErrorRatio) := by
  have hr0 : 0 ≤ bbpErrorRatio := bbpErrorRatio_nonneg
  have hr1 : bbpErrorRatio < 1 := bbpErrorRatio_lt_one
  have hden : 0 < (1 : ℝ) - bbpErrorRatio := sub_pos.mpr hr1
  have hformula :
      (∑ j ∈ range N, bbpErrorRatio ^ (m + j)) =
        bbpErrorRatio ^ m * (1 - bbpErrorRatio ^ N) /
          (1 - bbpErrorRatio) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [sum_range_succ, ih, pow_add]
        field_simp
        ring
  rw [hformula, div_lt_div_iff_of_pos_right hden]
  have hrpos : 0 < bbpErrorRatio := by norm_num [bbpErrorRatio]
  have hp : 0 < bbpErrorRatio ^ N := pow_pos hrpos _
  have hm : 0 < bbpErrorRatio ^ m := pow_pos hrpos _
  nlinarith

/-- Horizon-uniform natural-window transfer with the quadratic saving frozen
at the initial depth. -/
theorem norm_sum_phase_pi_sub_delayedBBPValue_quadratic_lt
    (h : ℤ) (k n N : ℕ) (hh : h ≠ 0) (hN : 1 ≤ N)
    (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖(∑ j ∈ range N,
          Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi)) -
        ∑ j ∈ range N,
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j))‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (sampledBBPTailScale (n + k) * (1 - bbpErrorRatio)) := by
  rw [← sum_sub_distrib]
  have hscale (j : ℕ) : sampledBBPTailScale (n + k) ≤
      sampledBBPTailScale (n + j + k) := by
    unfold sampledBBPTailScale
    push_cast
    nlinarith
  calc
    ‖∑ j ∈ range N,
        (Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j)))‖ ≤
      ∑ j ∈ range N,
        ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j))‖ :=
        norm_sum_le _ _
    _ < ∑ j ∈ range N,
        4 * Real.pi * bbpErrorRatio ^ ((n + k) + j) /
          sampledBBPTailScale (n + k + j) := by
      apply sum_lt_sum_of_nonempty
      · exact ⟨0, mem_range.mpr (by omega)⟩
      · intro j hj
        simpa [add_assoc, add_left_comm, add_comm] using
          norm_phase_pi_sub_delayedBBPValue_quadratic_natural_lt
            h k (n + j) hh hfreq
    _ ≤ ∑ j ∈ range N,
        4 * Real.pi * bbpErrorRatio ^ ((n + k) + j) /
          sampledBBPTailScale (n + k) := by
      apply sum_le_sum
      intro j hj
      apply div_le_div_of_nonneg_left
      · have hr0 : 0 ≤ bbpErrorRatio := bbpErrorRatio_nonneg
        positivity
      · exact sampledBBPTailScale_pos _
      · simpa [add_assoc, add_left_comm, add_comm] using hscale j
    _ = 4 * Real.pi / sampledBBPTailScale (n + k) *
        (∑ j ∈ range N, bbpErrorRatio ^ ((n + k) + j)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ < 4 * Real.pi / sampledBBPTailScale (n + k) *
        (bbpErrorRatio ^ (n + k) / (1 - bbpErrorRatio)) := by
      exact mul_lt_mul_of_pos_left (finite_geometric_tail_lt (n + k) N)
        (div_pos (by positivity) (sampledBBPTailScale_pos _))
    _ = 4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (sampledBBPTailScale (n + k) * (1 - bbpErrorRatio)) := by
      have hs := ne_of_gt (sampledBBPTailScale_pos (n + k))
      have hr := ne_of_gt (sub_pos.mpr bbpErrorRatio_lt_one)
      field_simp

/-- The same sharpened horizon transfer written with T154's literal reduced
numerator phases. -/
theorem norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_quadratic_lt
    (h : ℤ) (k n N : ℕ) (hh : h ≠ 0) (hN : 1 ≤ N)
    (hfreq : h.natAbs < 2 * 10 ^ k)
    (hburn : ∀ j ∈ range N,
      2 ≤ (n + j) + k ∧
        Nat.log 5 (56 * ((n + j) + k) + 5) ≤ n + j) :
    ‖(∑ j ∈ range N,
          Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi)) -
        ∑ j ∈ range N, delayedBBPNumeratorPhase h k (n + j)‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (sampledBBPTailScale (n + k) * (1 - bbpErrorRatio)) := by
  have hsum :
      (∑ j ∈ range N, delayedBBPNumeratorPhase h k (n + j)) =
        ∑ j ∈ range N,
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j)) := by
    apply sum_congr rfl
    intro j hj
    exact (phase_delayedBBPValue_eq_delayedBBPNumeratorPhase h k (n + j)
      (hburn j hj).1 (hburn j hj).2).symm
  rw [hsum]
  exact norm_sum_phase_pi_sub_delayedBBPValue_quadratic_lt
    h k n N hh hN hfreq

end Theory.PiDigits.T164QuadraticBBPTailTransfer

#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.bbpCombinedTerm_quadratic_bounds
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.real_bbp_tail_quadratic_bounds
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.sampledBBPError_quadratic_bounds
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.norm_phase_pi_sub_delayedBBPValue_quadratic_lt
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.norm_phase_pi_sub_delayedBBPValue_quadratic_natural_lt
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.norm_sum_phase_pi_sub_delayedBBPValue_quadratic_lt
#print axioms Theory.PiDigits.T164QuadraticBBPTailTransfer.norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_quadratic_lt
