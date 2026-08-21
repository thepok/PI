import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit
import TheoryLib.PiQuantitativeBlockHitting.T40T40MachinLocalForcing

/-!
# T43: a periodic separator for positive two-adic forcing data

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module gives a small exact separator for a tempting route suggested by
the local two-adic structure of the Machin forcing.  Its forcing is positive,
geometric, summable, and has an exact numerator certificate with two-adic
order `n + 4`.  Nevertheless, the corresponding forced base-ten orbit tends
to the fixed rational orbit at `1 / 3` and eventually avoids the decimal
zero-cell.

This is an artificial separator only.  It is not the Machin forcing and says
nothing about distribution, normality, or the every-word conjecture for pi.
-/

noncomputable section

open Filter Set

namespace Theory.PiDigits.TwoAdicForcingSeparator

open Theory.PiDigits.MachinForcedOrbit

/-- The small geometric ratio used by the separator. -/
def separatorRatio : ℝ := 2 / 5 ^ 11

/-- The moving error, normalized so that its zeroth value is exactly `1 / 2`. -/
def separatorError (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * separatorRatio ^ n

/-- Positive forcing obtained as the exact base-ten coboundary of the error. -/
def separatorForcing (n : ℕ) : ℝ :=
  10 * separatorError n - separatorError (n + 1)

/-- The rational seed is fixed modulo one by multiplication by ten. -/
def separatorSeed : ℝ := 1 / 3

/-- A forced base-ten orbit built by subtracting the moving error from the
periodic rational seed before taking fractional part. -/
def separatorOrbit (n : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ n * separatorSeed - separatorError n)

theorem separatorRatio_nonneg : 0 ≤ separatorRatio := by
  norm_num [separatorRatio]

theorem separatorRatio_lt_one : separatorRatio < 1 := by
  norm_num [separatorRatio]

/-- Exact boundary value of the error at index zero. -/
theorem separatorError_zero : separatorError 0 = 1 / 2 := by
  norm_num [separatorError]

/-- The forcing is a constant multiple of one geometric progression. -/
theorem separatorForcing_eq_geometric (n : ℕ) :
    separatorForcing n =
      (5 - 1 / (5 : ℝ) ^ 11) * separatorRatio ^ n := by
  simp only [separatorForcing, separatorError]
  rw [pow_succ]
  norm_num [separatorRatio]
  ring

/-- Closed rational formula for the forcing, including the exact index in
the denominator. -/
theorem separatorForcing_eq_closed (n : ℕ) :
    separatorForcing n =
      (2 : ℝ) ^ n * ((5 : ℝ) ^ 12 - 1) /
        (5 : ℝ) ^ (11 * (n + 1)) := by
  rw [separatorForcing_eq_geometric, separatorRatio, div_pow]
  rw [show (5 : ℝ) ^ (11 * (n + 1)) = ((5 : ℝ) ^ 11) ^ (n + 1) by
    rw [pow_mul]]
  rw [pow_succ]
  norm_num
  ring

/-- Every forcing term is strictly positive. -/
theorem separatorForcing_pos (n : ℕ) : 0 < separatorForcing n := by
  rw [separatorForcing_eq_geometric]
  have hconstant : (0 : ℝ) < 5 - 1 / (5 : ℝ) ^ 11 := by norm_num
  exact mul_pos hconstant (pow_pos (by norm_num [separatorRatio]) n)

/-- Consecutive forcing terms have the fixed ratio `2 / 5^11`. -/
theorem separatorForcing_succ (n : ℕ) :
    separatorForcing (n + 1) = separatorRatio * separatorForcing n := by
  rw [separatorForcing_eq_geometric, separatorForcing_eq_geometric, pow_succ]
  ring

/-- The positive forcing is summable. -/
theorem summable_separatorForcing : Summable separatorForcing := by
  have hgeo : Summable (fun n : ℕ ↦ separatorRatio ^ n) :=
    summable_geometric_of_lt_one separatorRatio_nonneg separatorRatio_lt_one
  have hmul := hgeo.mul_left (5 - 1 / (5 : ℝ) ^ 11)
  exact hmul.congr (fun n ↦ (separatorForcing_eq_geometric n).symm)

/-- Exact twice-odd presentation: after removing `2^(n+4)`, the numerator is
the fixed odd integer `15258789`, while the displayed denominator is odd. -/
theorem separatorForcing_twoAdic_certificate (n : ℕ) :
    Odd (15258789 : ℕ) ∧
      Odd (5 ^ (11 * (n + 1))) ∧
      separatorForcing n =
        (2 : ℝ) ^ (n + 4) * 15258789 /
          (5 : ℝ) ^ (11 * (n + 1)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact (by norm_num : Odd 5).pow
  · rw [separatorForcing_eq_closed, pow_add]
    norm_num
    ring

/-- Powers of ten are one modulo three, stated as an exact natural identity. -/
lemma pow_ten_eq_three_mul_add_one (n : ℕ) :
    ∃ k : ℕ, 10 ^ n = 3 * k + 1 := by
  induction n with
  | zero => exact ⟨0, by norm_num⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨10 * k + 3, ?_⟩
      rw [pow_succ, hk]
      ring

/-- Modulo one, the periodic seed may be reduced back to `1 / 3` before
subtracting the moving error. -/
theorem separatorOrbit_eq_fract_seed_sub (n : ℕ) :
    separatorOrbit n = Int.fract (separatorSeed - separatorError n) := by
  obtain ⟨k, hk⟩ := pow_ten_eq_three_mul_add_one n
  have hpow : (10 : ℝ) ^ n = 3 * (k : ℝ) + 1 := by
    exact_mod_cast hk
  rw [separatorOrbit, hpow]
  unfold separatorSeed
  rw [show (3 * (k : ℝ) + 1) * (1 / 3 : ℝ) - separatorError n =
      (1 / 3 - separatorError n) + k by ring]
  exact Int.fract_add_natCast _ k

/-- The forced recurrence holds at every index, including `n = 0`. -/
theorem separatorOrbit_succ (n : ℕ) :
    separatorOrbit (n + 1) =
      Int.fract (10 * separatorOrbit n + separatorForcing n) := by
  rw [separatorOrbit, separatorOrbit]
  symm
  calc
    Int.fract
        (10 * Int.fract
          ((10 : ℝ) ^ n * separatorSeed - separatorError n) +
            separatorForcing n) =
        Int.fract
          ((10 : ℝ) *
              ((10 : ℝ) ^ n * separatorSeed - separatorError n) +
            separatorForcing n) := by
      simpa using fract_natCast_mul_fract_add
        ((10 : ℝ) ^ n * separatorSeed - separatorError n)
        (separatorForcing n) 10
    _ = Int.fract
        ((10 : ℝ) ^ (n + 1) * separatorSeed - separatorError (n + 1)) := by
      unfold separatorForcing
      rw [pow_succ]
      congr 1
      ring

/-- At index zero the orbit is `5 / 6`; this records the only large-error
boundary value explicitly. -/
theorem separatorOrbit_zero : separatorOrbit 0 = 5 / 6 := by
  rw [separatorOrbit_eq_fract_seed_sub, separatorError_zero]
  norm_num [separatorSeed, Int.fract]

theorem tendsto_separatorError_zero :
    Tendsto separatorError atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ separatorRatio ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one separatorRatio_nonneg
      separatorRatio_lt_one
  have hconst : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hpow
  change Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * separatorRatio ^ n)
    atTop (nhds 0)
  simpa only [one_div, mul_zero] using hmul

/-- Despite its positive summable forcing and exact two-adic numerator data,
the separator orbit converges to the rational fixed point `1 / 3`. -/
theorem tendsto_separatorOrbit_seed :
    Tendsto separatorOrbit atTop (nhds separatorSeed) := by
  have harg : Tendsto (fun n : ℕ ↦ separatorSeed - separatorError n)
      atTop (nhds (separatorSeed - 0)) :=
    tendsto_const_nhds.sub tendsto_separatorError_zero
  have harg' : Tendsto (fun n : ℕ ↦ separatorSeed - separatorError n)
      atTop (nhds separatorSeed) := by
    simpa using harg
  have hseed_noninteger : separatorSeed ≠ (⌊separatorSeed⌋ : ℝ) := by
    norm_num [separatorSeed]
  have hfract := (continuousAt_fract hseed_noninteger).tendsto.comp harg'
  have hfract_seed : Int.fract separatorSeed = separatorSeed := by
    apply Int.fract_eq_self.mpr
    norm_num [separatorSeed]
  rw [hfract_seed] at hfract
  exact hfract.congr' (Eventually.of_forall fun n ↦
    (separatorOrbit_eq_fract_seed_sub n).symm)

/-- The fixed first-decimal-digit cell `[0, 1/10)` is eventually avoided. -/
theorem eventually_separatorOrbit_avoids_zero_decimal_cell :
    ∀ᶠ n : ℕ in atTop,
      separatorOrbit n ∉ Set.Ico (0 : ℝ) (1 / 10) := by
  have hlower : ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) < separatorOrbit n :=
    (tendsto_order.1 tendsto_separatorOrbit_seed).1 (1 / 4) (by
      norm_num [separatorSeed])
  filter_upwards [hlower] with n hn hcell
  rcases hcell with ⟨_, hupper⟩
  linarith

end Theory.PiDigits.TwoAdicForcingSeparator

#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorRatio_nonneg
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorRatio_lt_one
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorError_zero
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorForcing_eq_geometric
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorForcing_eq_closed
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorForcing_pos
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorForcing_succ
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.summable_separatorForcing
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorForcing_twoAdic_certificate
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.pow_ten_eq_three_mul_add_one
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorOrbit_eq_fract_seed_sub
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorOrbit_succ
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.separatorOrbit_zero
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.tendsto_separatorError_zero
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.tendsto_separatorOrbit_seed
#print axioms
  Theory.PiDigits.TwoAdicForcingSeparator.eventually_separatorOrbit_avoids_zero_decimal_cell
