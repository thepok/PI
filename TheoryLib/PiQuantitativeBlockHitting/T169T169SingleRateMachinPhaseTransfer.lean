import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit

/-!
# T169: natural-window transfer to a single-rate rational Machin carrier

T36's rational Machin approximation already converges fast enough to sample it
at index `t`, rather than at the deeper index `3 * t` used by T38.  This file
records the resulting moving-frequency transfer for the actual decimal pi
orbit.  The frequency window is the full natural window `|h| < 2 * 10^k`, and
the accumulated error is uniform in the horizon.

This is an exact transfer to an explicit rational carrier.  It supplies no
cancellation estimate for that carrier and proves no density, normality, or V1
statement.
-/

noncomputable section

open scoped BigOperators

namespace Theory.PiDigits.T169SingleRateMachinPhaseTransfer

open Finset
open Theory.PiDigits.MachinGridStability

/-- The geometric ratio after scaling a depth-`t` Machin error by `10^t`. -/
def singleRateMachinErrorRatio : ℝ := 10 / 625

lemma singleRateMachinErrorRatio_nonneg : 0 ≤ singleRateMachinErrorRatio := by
  norm_num [singleRateMachinErrorRatio]

lemma singleRateMachinErrorRatio_lt_one : singleRateMachinErrorRatio < 1 := by
  norm_num [singleRateMachinErrorRatio]

/-- The explicit rational carrier at decimal delay `n` and word scale `k`.
Its approximation index is exactly the total depth `n + k`. -/
def delayedSingleRateMachinValue (k n : ℕ) : ℝ :=
  (10 : ℝ) ^ n * machinLower (n + k)

/-- The delayed carrier is the real embedding of an explicit rational. -/
theorem delayedSingleRateMachinValue_isRat (k n : ℕ) :
    ∃ r : ℚ, delayedSingleRateMachinValue k n = (r : ℝ) := by
  refine ⟨(10 : ℚ) ^ n * machinLowerRat (n + k), ?_⟩
  simp [delayedSingleRateMachinValue, machinLower]

/-- Scaling the depth-`t` rational Machin error by `10^t` leaves a geometric
error with ratio `10/625`. -/
theorem scaled_machinLower_error_lt (t : ℕ) :
    (10 : ℝ) ^ t * (Real.pi - machinLower t) <
      singleRateMachinErrorRatio ^ t := by
  have h := pi_sub_machinLower_lt_pow625 t
  have h10 : (0 : ℝ) < 10 ^ t := by positivity
  have hm := mul_lt_mul_of_pos_left h h10
  calc
    (10 : ℝ) ^ t * (Real.pi - machinLower t) <
        (10 : ℝ) ^ t * (1 / (625 : ℝ) ^ t) := hm
    _ = singleRateMachinErrorRatio ^ t := by
      rw [singleRateMachinErrorRatio, div_pow]
      ring

/-- Pointwise phase transfer at an arbitrary integer frequency. -/
theorem norm_phase_pi_sub_delayedSingleRateMachinValue_lt
    (h : ℤ) (k n : ℕ) (hh : h ≠ 0) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedSingleRateMachinValue k n)‖ <
      2 * Real.pi * (h.natAbs : ℝ) *
        (singleRateMachinErrorRatio ^ (n + k) / (10 : ℝ) ^ k) := by
  have hphase :=
    DecimalFactorComplexity.FixedDecimalPeriodicBlocks.norm_phase_sub_phase_le
      h ((10 : ℝ) ^ n * Real.pi) (delayedSingleRateMachinValue k n)
  have hnonneg : 0 ≤ Real.pi - machinLower (n + k) :=
    sub_nonneg.mpr (machinLower_le_pi (n + k))
  have habs :
      |(10 : ℝ) ^ n * Real.pi - delayedSingleRateMachinValue k n| =
        (10 : ℝ) ^ n * (Real.pi - machinLower (n + k)) := by
    rw [delayedSingleRateMachinValue]
    rw [show (10 : ℝ) ^ n * Real.pi - 10 ^ n * machinLower (n + k) =
      10 ^ n * (Real.pi - machinLower (n + k)) by ring]
    exact abs_of_nonneg (mul_nonneg (by positivity) hnonneg)
  have hscaled := scaled_machinLower_error_lt (n + k)
  have h10k : (0 : ℝ) < 10 ^ k := by positivity
  have hrewrite :
      (10 : ℝ) ^ n * (Real.pi - machinLower (n + k)) =
        ((10 : ℝ) ^ (n + k) * (Real.pi - machinLower (n + k))) /
          (10 : ℝ) ^ k := by
    rw [pow_add]
    field_simp
  have herr :
      (10 : ℝ) ^ n * (Real.pi - machinLower (n + k)) <
        singleRateMachinErrorRatio ^ (n + k) / (10 : ℝ) ^ k := by
    rw [hrewrite]
    exact div_lt_div_of_pos_right hscaled h10k
  have hcoef : 0 < 2 * Real.pi * (h.natAbs : ℝ) := by
    have habspos : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    positivity
  calc
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedSingleRateMachinValue k n)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) *
        |(10 : ℝ) ^ n * Real.pi - delayedSingleRateMachinValue k n| := hphase
    _ = 2 * Real.pi * (h.natAbs : ℝ) *
        ((10 : ℝ) ^ n * (Real.pi - machinLower (n + k))) := by rw [habs]
    _ < 2 * Real.pi * (h.natAbs : ℝ) *
        (singleRateMachinErrorRatio ^ (n + k) / (10 : ℝ) ^ k) :=
      mul_lt_mul_of_pos_left herr hcoef

/-- Full natural-frequency-window specialization. -/
theorem norm_phase_pi_sub_delayedSingleRateMachinValue_natural_lt
    (h : ℤ) (k n : ℕ) (hh : h ≠ 0)
    (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedSingleRateMachinValue k n)‖ <
      4 * Real.pi * singleRateMachinErrorRatio ^ (n + k) := by
  have hbase := norm_phase_pi_sub_delayedSingleRateMachinValue_lt h k n hh
  have h10 : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have habslt : (h.natAbs : ℝ) < 2 * (10 : ℝ) ^ k := by
    exact_mod_cast hfreq
  have hrpos : 0 < singleRateMachinErrorRatio ^ (n + k) := by
    positivity [show 0 < singleRateMachinErrorRatio by
      norm_num [singleRateMachinErrorRatio]]
  calc
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ n * Real.pi) -
        Theory.PiDigits.T27.phase h (delayedSingleRateMachinValue k n)‖ <
      2 * Real.pi * (h.natAbs : ℝ) *
        (singleRateMachinErrorRatio ^ (n + k) / (10 : ℝ) ^ k) := hbase
    _ < 4 * Real.pi * singleRateMachinErrorRatio ^ (n + k) := by
      field_simp
      nlinarith [Real.pi_pos]

private theorem finite_geometric_tail_lt (m N : ℕ) :
    (∑ j ∈ range N, singleRateMachinErrorRatio ^ (m + j)) <
      singleRateMachinErrorRatio ^ m / (1 - singleRateMachinErrorRatio) := by
  have hr0 : 0 ≤ singleRateMachinErrorRatio := singleRateMachinErrorRatio_nonneg
  have hr1 : singleRateMachinErrorRatio < 1 := singleRateMachinErrorRatio_lt_one
  have hden : 0 < (1 : ℝ) - singleRateMachinErrorRatio := sub_pos.mpr hr1
  have hformula (N : ℕ) :
      (∑ j ∈ range N, singleRateMachinErrorRatio ^ (m + j)) =
        singleRateMachinErrorRatio ^ m *
          (1 - singleRateMachinErrorRatio ^ N) /
            (1 - singleRateMachinErrorRatio) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [sum_range_succ, ih, pow_add]
        field_simp
        ring
  rw [hformula N, div_lt_div_iff_of_pos_right hden]
  have hrpos : 0 < singleRateMachinErrorRatio := by
    norm_num [singleRateMachinErrorRatio]
  have hp : 0 < singleRateMachinErrorRatio ^ N := pow_pos hrpos _
  have hm : 0 < singleRateMachinErrorRatio ^ m := pow_pos hrpos _
  nlinarith

/-- The actual pi phases and the explicit rational carrier phases differ by a
geometric amount uniform in the horizon, throughout the natural window. -/
theorem norm_sum_phase_pi_sub_delayedSingleRateMachinValue_natural_lt
    (h : ℤ) (k n N : ℕ) (hh : h ≠ 0) (hN : 1 ≤ N)
    (hfreq : h.natAbs < 2 * 10 ^ k) :
    ‖(∑ j ∈ range N,
          Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi)) -
        ∑ j ∈ range N,
          Theory.PiDigits.T27.phase h
            (delayedSingleRateMachinValue k (n + j))‖ <
      4 * Real.pi * singleRateMachinErrorRatio ^ (n + k) /
        (1 - singleRateMachinErrorRatio) := by
  rw [← sum_sub_distrib]
  calc
    ‖∑ j ∈ range N,
        (Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
          Theory.PiDigits.T27.phase h
            (delayedSingleRateMachinValue k (n + j)))‖ ≤
      ∑ j ∈ range N,
        ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ (n + j) * Real.pi) -
          Theory.PiDigits.T27.phase h
            (delayedSingleRateMachinValue k (n + j))‖ := norm_sum_le _ _
    _ < ∑ j ∈ range N,
        4 * Real.pi * singleRateMachinErrorRatio ^ ((n + k) + j) := by
      apply sum_lt_sum_of_nonempty
      · exact ⟨0, mem_range.mpr (by omega)⟩
      · intro j hj
        simpa [add_assoc, add_left_comm, add_comm] using
          norm_phase_pi_sub_delayedSingleRateMachinValue_natural_lt
            h k (n + j) hh hfreq
    _ = 4 * Real.pi *
        (∑ j ∈ range N, singleRateMachinErrorRatio ^ ((n + k) + j)) := by
      rw [mul_sum]
    _ < 4 * Real.pi *
        (singleRateMachinErrorRatio ^ (n + k) /
          (1 - singleRateMachinErrorRatio)) := by
      exact mul_lt_mul_of_pos_left
        (finite_geometric_tail_lt (n + k) N) (by positivity)
    _ = 4 * Real.pi * singleRateMachinErrorRatio ^ (n + k) /
        (1 - singleRateMachinErrorRatio) := by ring

end Theory.PiDigits.T169SingleRateMachinPhaseTransfer

#print axioms Theory.PiDigits.T169SingleRateMachinPhaseTransfer.delayedSingleRateMachinValue_isRat
#print axioms Theory.PiDigits.T169SingleRateMachinPhaseTransfer.scaled_machinLower_error_lt
#print axioms
  Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_phase_pi_sub_delayedSingleRateMachinValue_lt
#print axioms
  Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_phase_pi_sub_delayedSingleRateMachinValue_natural_lt
#print axioms
  Theory.PiDigits.T169SingleRateMachinPhaseTransfer.norm_sum_phase_pi_sub_delayedSingleRateMachinValue_natural_lt
