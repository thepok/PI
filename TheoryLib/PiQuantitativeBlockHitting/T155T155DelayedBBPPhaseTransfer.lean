import TheoryLib.PiQuantitativeBlockHitting.T154T154DelayedBBPFivePrimary
import TheoryLib.PiQuantitativeBlockHitting.T107T107BBPWeylTransfer

/-!
# T155: horizon-uniform delayed BBP phase transfer

The depth-`n+k` sevenfold BBP truncation approximates the decimal pi point at
index `n` with an extra factor `10^{-k}`.  On the full natural frequency
window `|h| < 2*10^k`, the phase error is therefore bounded by the geometric
T106 error at depth `n+k`.  Summing over any finite horizon costs only the
full geometric tail and hence gives a bound independent of the horizon.

Combined with T154, the comparison point is exactly a phase of the actual
reduced numerator on denominator `2^k D`.  No cancellation or V1 conclusion
is asserted.
-/

noncomputable section

namespace Theory.PiDigits.T155DelayedBBPPhaseTransfer

open scoped BigOperators
open Finset
open Theory.PiDigits.T106BBPForcedOrbit
open Theory.PiDigits.T154DelayedBBPFivePrimary

/-- The nonlocal BBP comparison point: decimal index `n`, truncation depth
`n+k`. -/
def delayedBBPValue (k n : ℕ) : ℝ :=
  (10 : ℝ) ^ n * sampledBBPValue (n + k)

/-- The literal phase of the actual reduced numerator after removing `5^k`. -/
def delayedBBPNumeratorPhase (h : ℤ) (k n : ℕ) : ℂ :=
  Theory.PiDigits.T27.phase h
    ((delayedBBPNumerator k n : ℝ) /
      ((2 ^ k *
        (Theory.PiDigits.T115SampledBBPCellDefectPhase.scaledBBPRat
          (n + k)).den : ℕ) : ℝ))

/-- T154's exact actual-numerator presentation, embedded in the reals. -/
theorem delayedBBPValue_eq_num_div_two_pow_den
    (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n) :
    delayedBBPValue k n =
      (delayedBBPNumerator k n : ℝ) /
        ((2 ^ k *
          (Theory.PiDigits.T115SampledBBPCellDefectPhase.scaledBBPRat
            (n + k)).den : ℕ) : ℝ) := by
  have hrat := delayed_bbpPartial_eq_num_div_two_pow_den k n hm hlog
  unfold delayedBBPValue sampledBBPValue T100BBPRealBridge.bbpRealPartial
  exact_mod_cast hrat

/-- Under the logarithmic burn-in, the delayed BBP comparison phase is
literally the phase of the actual reduced numerator on modulus `2^k D`. -/
theorem phase_delayedBBPValue_eq_delayedBBPNumeratorPhase
    (h : ℤ) (k n : ℕ) (hm : 2 ≤ n + k)
    (hlog : Nat.log 5 (56 * (n + k) + 5) ≤ n) :
    Theory.PiDigits.T27.phase h (delayedBBPValue k n) =
      delayedBBPNumeratorPhase h k n := by
  unfold delayedBBPNumeratorPhase
  rw [delayedBBPValue_eq_num_div_two_pow_den k n hm hlog]

/-- Exact rescaling: the delayed approximation error is the T106 scaled error
at depth `n+k`, divided by `10^k`. -/
theorem abs_piPoint_sub_delayedBBPValue (k n : ℕ) :
    |(10 : ℝ) ^ n * Real.pi - delayedBBPValue k n| =
      sampledBBPError (n + k) / (10 : ℝ) ^ k := by
  have hnonneg : 0 ≤ (10 : ℝ) ^ n * Real.pi - delayedBBPValue k n := by
    unfold delayedBBPValue
    rw [← mul_sub]
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr
        (T100BBPRealBridge.real_bbp_hasSum_tail_bounds
          T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi (7 * (n + k))).1)
  rw [abs_of_nonneg hnonneg]
  unfold delayedBBPValue sampledBBPError
  rw [pow_add]
  field_simp

/-- Pointwise phase transfer before restricting the moving frequency. -/
theorem norm_phase_pi_sub_delayedBBPValue_le (h : ℤ) (k n : ℕ) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) *
        (sampledBBPError (n + k) / (10 : ℝ) ^ k) := by
  have hp :=
    DecimalFactorComplexity.FixedDecimalPeriodicBlocks.norm_phase_sub_phase_le
      h ((10 : ℝ) ^ n * Real.pi) (delayedBBPValue k n)
  simpa [abs_piPoint_sub_delayedBBPValue] using hp

/-- On the complete T139 natural window, each delayed phase error is strictly
below `4*pi*rho^(n+k)`. -/
theorem norm_phase_pi_sub_delayedBBPValue_lt
    (h : ℤ) (k n : ℕ) (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) := by
  have hkpos : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hratio : (h.natAbs : ℝ) / (10 : ℝ) ^ k < 2 := by
    rw [div_lt_iff₀ hkpos]
    exact_mod_cast hfreq
  have herr0 := sampledBBPError_nonneg (n + k)
  have herr := sampledBBPError_lt_geometric (n + k)
  calc
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedBBPValue k n)‖ ≤
        2 * Real.pi * (h.natAbs : ℝ) *
          (sampledBBPError (n + k) / (10 : ℝ) ^ k) :=
      norm_phase_pi_sub_delayedBBPValue_le h k n
    _ = (2 * Real.pi) * ((h.natAbs : ℝ) / (10 : ℝ) ^ k) *
        sampledBBPError (n + k) := by ring
    _ < (2 * Real.pi) * 2 * bbpErrorRatio ^ (n + k) := by
      have hinner :
          ((h.natAbs : ℝ) / (10 : ℝ) ^ k) * sampledBBPError (n + k) <
            2 * bbpErrorRatio ^ (n + k) := by
        calc
        ((h.natAbs : ℝ) / (10 : ℝ) ^ k) * sampledBBPError (n + k) ≤
            2 * sampledBBPError (n + k) :=
          mul_le_mul_of_nonneg_right hratio.le herr0
        _ < 2 * bbpErrorRatio ^ (n + k) :=
          mul_lt_mul_of_pos_left herr (by norm_num)
      have hout := mul_lt_mul_of_pos_left hinner
        (show 0 < 2 * Real.pi by positivity)
      convert hout using 1 <;> ring
    _ = 4 * Real.pi * bbpErrorRatio ^ (n + k) := by ring

private theorem finite_geometric_tail_lt (m N : ℕ) :
    (∑ j ∈ range N, bbpErrorRatio ^ (m + j)) <
      bbpErrorRatio ^ m / (1 - bbpErrorRatio) := by
  have hr0 : 0 ≤ bbpErrorRatio := bbpErrorRatio_nonneg
  have hr1 : bbpErrorRatio < 1 := bbpErrorRatio_lt_one
  have hden : 0 < (1 : ℝ) - bbpErrorRatio := sub_pos.mpr hr1
  have hformula :
      (∑ j ∈ range N, bbpErrorRatio ^ (m + j)) =
        bbpErrorRatio ^ m *
          (1 - bbpErrorRatio ^ N) / (1 - bbpErrorRatio) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [sum_range_succ, ih]
        rw [show m + N = m + N by rfl, pow_add]
        field_simp
        ring
  rw [hformula]
  have hpowpos : 0 < bbpErrorRatio ^ N :=
    pow_pos (by norm_num [bbpErrorRatio]) _
  have hless : 1 - bbpErrorRatio ^ N < 1 := by linarith
  have hbase : 0 < bbpErrorRatio ^ m :=
    pow_pos (by norm_num [bbpErrorRatio]) _
  rw [div_lt_div_iff_of_pos_right hden]
  nlinarith

/-- Uniform-in-horizon natural-window transfer.  The right side does not
depend on `N`; the only restriction on the frequency is the sharp integer
window `|h| < 2*10^k`. -/
theorem norm_sum_phase_pi_sub_delayedBBPValue_lt
    (h : ℤ) (k n N : ℕ) (hN : 1 ≤ N)
    (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖(∑ j ∈ range N,
          Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi)) -
        ∑ j ∈ range N,
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j))‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (1 - bbpErrorRatio) := by
  rw [← sum_sub_distrib]
  calc
    ‖∑ j ∈ range N,
        (Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j)))‖ ≤
        ∑ j ∈ range N,
          ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
            Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j))‖ :=
      norm_sum_le _ _
    _ < ∑ j ∈ range N,
        4 * Real.pi * bbpErrorRatio ^ ((n + k) + j) := by
      apply sum_lt_sum_of_nonempty
      · exact ⟨0, mem_range.mpr (by omega)⟩
      · intro j hj
        simpa [add_assoc, add_left_comm, add_comm] using
          norm_phase_pi_sub_delayedBBPValue_lt h k (n + j) hfreq
    _ = 4 * Real.pi *
        (∑ j ∈ range N, bbpErrorRatio ^ ((n + k) + j)) := by
      rw [mul_sum]
    _ < 4 * Real.pi *
        (bbpErrorRatio ^ (n + k) / (1 - bbpErrorRatio)) := by
      exact mul_lt_mul_of_pos_left (finite_geometric_tail_lt (n + k) N)
        (by positivity)
    _ = 4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (1 - bbpErrorRatio) := by ring

/-- The same horizon-uniform transfer written directly with the actual
reduced numerator phases.  The burn-in hypotheses are required only to
identify each comparison point with `U/(2^k D)`; the analytic error estimate
itself is unconditional. -/
theorem norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt
    (h : ℤ) (k n N : ℕ) (hN : 1 ≤ N)
    (hfreq : h.natAbs < 2 * 10 ^ k)
    (hburn : ∀ j ∈ range N,
      2 ≤ (n + j) + k ∧
        Nat.log 5 (56 * ((n + j) + k) + 5) ≤ n + j) :
    ‖(∑ j ∈ range N,
          Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi)) -
        ∑ j ∈ range N, delayedBBPNumeratorPhase h k (n + j)‖ <
      4 * Real.pi * bbpErrorRatio ^ (n + k) /
        (1 - bbpErrorRatio) := by
  have hsum :
      (∑ j ∈ range N, delayedBBPNumeratorPhase h k (n + j)) =
        ∑ j ∈ range N,
          Theory.PiDigits.T27.phase h (delayedBBPValue k (n + j)) := by
    apply sum_congr rfl
    intro j hj
    exact (phase_delayedBBPValue_eq_delayedBBPNumeratorPhase h k (n + j)
      (hburn j hj).1 (hburn j hj).2).symm
  rw [hsum]
  exact norm_sum_phase_pi_sub_delayedBBPValue_lt h k n N hN hfreq

end Theory.PiDigits.T155DelayedBBPPhaseTransfer

#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.delayedBBPValue_eq_num_div_two_pow_den
#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.phase_delayedBBPValue_eq_delayedBBPNumeratorPhase
#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.abs_piPoint_sub_delayedBBPValue
#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.norm_phase_pi_sub_delayedBBPValue_lt
#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.norm_sum_phase_pi_sub_delayedBBPValue_lt
#print axioms Theory.PiDigits.T155DelayedBBPPhaseTransfer.norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt
