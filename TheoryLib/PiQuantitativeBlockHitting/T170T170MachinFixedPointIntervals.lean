import TheoryLib.PiQuantitativeBlockHitting.T36T36MachinGridStability

/-!
# T170: fixed-point interval certificates for Machin sums

This is a bounded feasibility prototype for certifying long decimal prefixes
without normalizing the full Machin sum to one enormous rational.  Each
rational term is rounded separately at an integer scale, and the rounding
inequalities are proved before finite computation is used.

The final theorem certifies the first 100 fractional decimal digits of `pi`.
It is not a digit-occurrence or distribution result.
-/

noncomputable section

namespace Theory.PiDigits.T170MachinFixedPointIntervals

open Finset
open Theory.PiDigits.MachinGridStability

/-- A rational rounded downward to the grid of mesh `1 / scale`. -/
def fixedFloorRat (scale : ℕ) (x : ℚ) : ℚ :=
  (⌊(scale : ℚ) * x⌋ : ℚ) / scale

/-- A strict rational upper endpoint on the same fixed-point grid. -/
def fixedUpperRat (scale : ℕ) (x : ℚ) : ℚ :=
  ((⌊(scale : ℚ) * x⌋ : ℤ) + 1 : ℚ) / scale

theorem fixedFloorRat_le (scale : ℕ) (x : ℚ) (hscale : 0 < scale) :
    fixedFloorRat scale x ≤ x := by
  have hscaleQ : (0 : ℚ) < scale := by exact_mod_cast hscale
  rw [fixedFloorRat, div_le_iff₀ hscaleQ]
  simpa [mul_comm] using Int.floor_le ((scale : ℚ) * x)

theorem lt_fixedUpperRat (scale : ℕ) (x : ℚ) (hscale : 0 < scale) :
    x < fixedUpperRat scale x := by
  have hscaleQ : (0 : ℚ) < scale := by exact_mod_cast hscale
  rw [fixedUpperRat, lt_div_iff₀ hscaleQ]
  simp [mul_comm, Int.lt_floor_add_one]

/-- Termwise fixed-point lower enclosure of the exact rational Machin sum. -/
def fixedMachinLowerRat (scale K : ℕ) : ℚ :=
  (∑ n ∈ range (2 * (K + 1)),
      fixedFloorRat scale (16 * arctanTermRat 5 n)) +
    ∑ n ∈ range (2 * (K + 1) + 1),
      fixedFloorRat scale (-4 * arctanTermRat 239 n)

/-- Termwise strict upper endpoints for the exact rational Machin sum. -/
def fixedMachinUpperRat (scale K : ℕ) : ℚ :=
  (∑ n ∈ range (2 * (K + 1)),
      fixedUpperRat scale (16 * arctanTermRat 5 n)) +
    ∑ n ∈ range (2 * (K + 1) + 1),
      fixedUpperRat scale (-4 * arctanTermRat 239 n)

private theorem machinLowerRat_eq_term_sums (K : ℕ) :
    machinLowerRat K =
      (∑ n ∈ range (2 * (K + 1)), 16 * arctanTermRat 5 n) +
        ∑ n ∈ range (2 * (K + 1) + 1), -4 * arctanTermRat 239 n := by
  simp [machinLowerRat, arctanPartialRat, Finset.mul_sum]
  ring

theorem fixedMachinLowerRat_le_machinLowerRat
    (scale K : ℕ) (hscale : 0 < scale) :
    fixedMachinLowerRat scale K ≤ machinLowerRat K := by
  rw [machinLowerRat_eq_term_sums]
  unfold fixedMachinLowerRat
  gcongr with n hn
  · exact fixedFloorRat_le scale _ hscale
  · exact fixedFloorRat_le scale _ hscale

theorem machinLowerRat_le_fixedMachinUpperRat
    (scale K : ℕ) (hscale : 0 < scale) :
    machinLowerRat K ≤ fixedMachinUpperRat scale K := by
  rw [machinLowerRat_eq_term_sums]
  unfold fixedMachinUpperRat
  gcongr with n hn
  · exact (lt_fixedUpperRat scale _ hscale).le
  · exact (lt_fixedUpperRat scale _ hscale).le

private def decimalScale100 : ℕ := 10 ^ 100

private def workScale105 : ℕ := 10 ^ 105

private def piPrefix100 : ℕ :=
  31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679

/-- A kernel-checked fixed-point computation places the exact Machin lower
sum above the claimed 100-digit decimal prefix. -/
private theorem piPrefix100_lt_fixedMachinLower :
    (piPrefix100 : ℚ) / decimalScale100 <
      fixedMachinLowerRat workScale105 38 := by
  norm_num [piPrefix100, decimalScale100, workScale105, fixedMachinLowerRat,
    fixedFloorRat, arctanTermRat]

/-- The termwise upper enclosure plus T36's geometric tail remains below the
next 100-digit decimal grid point. -/
private theorem fixedMachinUpper_add_tail_lt_piPrefix100_succ :
    fixedMachinUpperRat workScale105 38 + 1 / (625 : ℚ) ^ 38 <
      (piPrefix100 + 1 : ℚ) / decimalScale100 := by
  norm_num [piPrefix100, decimalScale100, workScale105, fixedMachinUpperRat,
    fixedUpperRat, arctanTermRat]

/-- Honest 100-place decimal-cylinder certificate for `pi`, obtained from
termwise fixed-point rational checks and the already verified T36 tail. -/
theorem pi_mem_decimalCylinder_100 :
    (piPrefix100 : ℝ) / decimalScale100 < Real.pi ∧
      Real.pi < (piPrefix100 + 1 : ℝ) / decimalScale100 := by
  have hlowerRat :
      (piPrefix100 : ℚ) / decimalScale100 < machinLowerRat 38 :=
    piPrefix100_lt_fixedMachinLower.trans_le
      (fixedMachinLowerRat_le_machinLowerRat workScale105 38
        (by norm_num [workScale105]))
  have hlowerReal :
      (piPrefix100 : ℝ) / decimalScale100 < machinLower 38 := by
    unfold machinLower
    have hcast :
        (((piPrefix100 : ℚ) / decimalScale100 : ℚ) : ℝ) <
          (machinLowerRat 38 : ℝ) := Rat.cast_lt.mpr hlowerRat
    simpa using hcast
  constructor
  · exact hlowerReal.trans_le (machinLower_le_pi 38)
  · have htail := pi_sub_machinLower_lt_pow625 38
    have hmUpper :
        machinLowerRat 38 ≤ fixedMachinUpperRat workScale105 38 :=
      machinLowerRat_le_fixedMachinUpperRat workScale105 38
        (by norm_num [workScale105])
    have hmUpperTail :
        machinLowerRat 38 + 1 / (625 : ℚ) ^ 38 ≤
          fixedMachinUpperRat workScale105 38 + 1 / (625 : ℚ) ^ 38 :=
      by
        simpa [add_comm] using
          (add_le_add_right hmUpper (1 / (625 : ℚ) ^ 38))
    have hupperRat :
        machinLowerRat 38 + 1 / (625 : ℚ) ^ 38 <
          (piPrefix100 + 1 : ℚ) / decimalScale100 :=
      hmUpperTail.trans_lt fixedMachinUpper_add_tail_lt_piPrefix100_succ
    have hupperReal :
        machinLower 38 + 1 / (625 : ℝ) ^ 38 <
          (piPrefix100 + 1 : ℝ) / decimalScale100 := by
      unfold machinLower
      have hcast :
          ((machinLowerRat 38 + 1 / (625 : ℚ) ^ 38 : ℚ) : ℝ) <
            (((piPrefix100 + 1 : ℚ) / decimalScale100 : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hupperRat
      simpa using hcast
    linarith

end Theory.PiDigits.T170MachinFixedPointIntervals

#print axioms Theory.PiDigits.T170MachinFixedPointIntervals.pi_mem_decimalCylinder_100
