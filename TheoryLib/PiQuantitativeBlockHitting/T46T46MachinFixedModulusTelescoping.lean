import TheoryLib.PiQuantitativeBlockHitting.T45T45MachinPrimeSurvival

/-!
# T46: fixed-denominator reduction for the sampled Machin orbit

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T38 gives a forced recurrence for the fractional parts of the sampled
rational Machin approximants.  Here we keep the same recurrence unwrapped
and entirely over the rationals.  Iteration writes every later sample as a
power of ten times one fixed initial rational plus an explicit finite sum of
forcing increments.  After embedding in the reals, that whole forcing sum
is exactly the telescoping error

`10^t * sampledMachinError n - sampledMachinError (n + t)`.

Thus, throughout any finite pulse, the main rational term has one fixed
initial denominator and the remaining real translation is geometrically
small.  These are exact identities and bounds.  They do not prove
cancellation, a cylinder hit, recurrence, density, normality, or the
every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinFixedModulusTelescoping

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinForcedOrbit
open Theory.PiDigits.MachinLocalForcing

/-- The sampled rational Machin approximation with its matching unwrapped
decimal scaling. -/
def sampledMachinValueRat (N : ℕ) : ℚ :=
  (10 : ℚ) ^ N * machinLowerRat (3 * N)

/-- The forcing accumulated during `t` steps starting at `n`, with the
power-of-ten weights arising from iteration of the affine recurrence. -/
def sampledMachinForcingAccumulationRat (n t : ℕ) : ℚ :=
  ∑ u ∈ range t,
    (10 : ℚ) ^ (t - 1 - u) * sampledMachinForcingRat (n + u)

/-- The rational sample embeds as the corresponding scaled real sample. -/
theorem sampledMachinValueRat_cast (N : ℕ) :
    (sampledMachinValueRat N : ℝ) =
      (10 : ℝ) ^ N * sampledMachinValue N := by
  simp [sampledMachinValueRat, sampledMachinValue, machinLower]

/-- Exact unwrapped one-step recurrence over the rationals. -/
theorem sampledMachinValueRat_succ (N : ℕ) :
    sampledMachinValueRat (N + 1) =
      10 * sampledMachinValueRat N + sampledMachinForcingRat N := by
  rw [sampledMachinValueRat, sampledMachinValueRat,
    sampledMachinForcingRat, ← machinLowerRat_threeStep_sub_eq]
  rw [pow_succ]
  ring

/-- The finite forcing accumulation obeys the same affine one-step update. -/
theorem sampledMachinForcingAccumulationRat_succ (n t : ℕ) :
    sampledMachinForcingAccumulationRat n (t + 1) =
      10 * sampledMachinForcingAccumulationRat n t +
        sampledMachinForcingRat (n + t) := by
  rw [sampledMachinForcingAccumulationRat,
    sampledMachinForcingAccumulationRat, sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro u hu
  have hut : u < t := mem_range.mp hu
  rw [show t - u = (t - 1 - u) + 1 by omega, pow_succ]
  ring

/-- Iterating the rational recurrence isolates one fixed initial sample and
the explicit weighted finite forcing sum. -/
theorem sampledMachinValueRat_add (n t : ℕ) :
    sampledMachinValueRat (n + t) =
      (10 : ℚ) ^ t * sampledMachinValueRat n +
        sampledMachinForcingAccumulationRat n t := by
  induction t with
  | zero =>
      simp [sampledMachinForcingAccumulationRat]
  | succ t ih =>
      rw [show n + (t + 1) = (n + t) + 1 by omega,
        sampledMachinValueRat_succ, ih,
        sampledMachinForcingAccumulationRat_succ, pow_succ]
      ring

/-- Explicit fixed-denominator form of the iterated recurrence.  The first
term is represented using the single denominator of the initial rational
sample; all later forcing is confined to the additive remainder. -/
theorem sampledMachinValueRat_add_eq_fixed_denominator (n t : ℕ) :
    sampledMachinValueRat (n + t) =
      ((10 : ℚ) ^ t * (sampledMachinValueRat n).num) /
          (sampledMachinValueRat n).den +
        sampledMachinForcingAccumulationRat n t := by
  calc
    sampledMachinValueRat (n + t) =
        (10 : ℚ) ^ t * sampledMachinValueRat n +
          sampledMachinForcingAccumulationRat n t :=
      sampledMachinValueRat_add n t
    _ = ((10 : ℚ) ^ t * (sampledMachinValueRat n).num) /
          (sampledMachinValueRat n).den +
        sampledMachinForcingAccumulationRat n t := by
      congr 1
      have h := congrArg (fun q : ℚ ↦ (10 : ℚ) ^ t * q)
        (Rat.num_div_den (sampledMachinValueRat n)).symm
      exact h.trans (by ring)

/-- Each explicit rational forcing increment is strictly positive. -/
theorem sampledMachinForcingRat_pos (N : ℕ) :
    0 < sampledMachinForcingRat N := by
  have h := sampledMachinForcing_pos N
  rw [sampledMachinForcing_eq_cast_rat] at h
  exact_mod_cast h

/-- The accumulated rational forcing is nonnegative. -/
theorem sampledMachinForcingAccumulationRat_nonneg (n t : ℕ) :
    0 ≤ sampledMachinForcingAccumulationRat n t := by
  rw [sampledMachinForcingAccumulationRat]
  apply sum_nonneg
  intro u hu
  exact mul_nonneg (by positivity)
    (sampledMachinForcingRat_pos (n + u)).le

/-- Exact corrected telescope: after real embedding, the complete weighted
forcing sum is one power-of-ten multiple of the initial sampled error minus
the final sampled error. -/
theorem sampledMachinForcingAccumulationRat_cast_eq_error_telescope
    (n t : ℕ) :
    (sampledMachinForcingAccumulationRat n t : ℝ) =
      (10 : ℝ) ^ t * sampledMachinError n -
        sampledMachinError (n + t) := by
  have h := congrArg (fun q : ℚ ↦ (q : ℝ))
    (sampledMachinValueRat_add n t)
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at h
  rw [sampledMachinValueRat_cast, sampledMachinValueRat_cast] at h
  have hacc :
      (sampledMachinForcingAccumulationRat n t : ℝ) =
        (10 : ℝ) ^ (n + t) * sampledMachinValue (n + t) -
          (10 : ℝ) ^ t *
            ((10 : ℝ) ^ n * sampledMachinValue n) := by
    linarith
  rw [hacc]
  simp only [sampledMachinError]
  rw [pow_add]
  ring

/-- Combined fixed-denominator and error-telescope form.  The rational term
uses the denominator of the single initial sample `n`; the complete effect
of all subsequent forcing increments is the displayed real error
coboundary. -/
theorem sampledMachinValueRat_cast_eq_fixed_denominator_add_error_telescope
    (n t : ℕ) :
    (sampledMachinValueRat (n + t) : ℝ) =
      (((((10 : ℚ) ^ t * (sampledMachinValueRat n).num) /
          (sampledMachinValueRat n).den : ℚ) : ℝ)) +
        ((10 : ℝ) ^ t * sampledMachinError n -
          sampledMachinError (n + t)) := by
  have h := congrArg (fun q : ℚ ↦ (q : ℝ))
    (sampledMachinValueRat_add_eq_fixed_denominator n t)
  simp only [Rat.cast_add] at h
  rw [← sampledMachinForcingAccumulationRat_cast_eq_error_telescope] at ⊢
  exact h

/-- The exact telescoping remainder is nonnegative. -/
theorem error_telescope_nonneg (n t : ℕ) :
    0 ≤ (10 : ℝ) ^ t * sampledMachinError n -
      sampledMachinError (n + t) := by
  rw [← sampledMachinForcingAccumulationRat_cast_eq_error_telescope]
  exact_mod_cast sampledMachinForcingAccumulationRat_nonneg n t

/-- T38's geometric error estimate uniformly bounds the whole accumulated
forcing remainder over a `t`-step segment. -/
theorem sampledMachinForcingAccumulationRat_cast_lt_geometric
    (n t : ℕ) :
    (sampledMachinForcingAccumulationRat n t : ℝ) <
      (10 : ℝ) ^ t * machinErrorRatio ^ n := by
  rw [sampledMachinForcingAccumulationRat_cast_eq_error_telescope]
  calc
    (10 : ℝ) ^ t * sampledMachinError n -
        sampledMachinError (n + t) ≤
        (10 : ℝ) ^ t * sampledMachinError n :=
      sub_le_self _ (sampledMachinError_nonneg (n + t))
    _ < (10 : ℝ) ^ t * machinErrorRatio ^ n :=
      mul_lt_mul_of_pos_left (sampledMachinError_lt_geometric n) (by positivity)

/-- On a segment of length at most `2*N+1` starting at `N+1`, the complete
telescoping translation has the explicit exponentially decaying pulse bound
from the corrected recurrence analysis. -/
theorem sampledMachinForcingAccumulationRat_cast_lt_pulse_bound
    (N t : ℕ) (ht : t ≤ 2 * N + 1) :
    (sampledMachinForcingAccumulationRat (N + 1) t : ℝ) <
      10 * machinErrorRatio * (100 * machinErrorRatio) ^ N := by
  calc
    (sampledMachinForcingAccumulationRat (N + 1) t : ℝ) <
        (10 : ℝ) ^ t * machinErrorRatio ^ (N + 1) :=
      sampledMachinForcingAccumulationRat_cast_lt_geometric (N + 1) t
    _ ≤ (10 : ℝ) ^ (2 * N + 1) * machinErrorRatio ^ (N + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg machinErrorRatio_nonneg _)
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) ht
    _ = 10 * machinErrorRatio * (100 * machinErrorRatio) ^ N := by
      have hten : (10 : ℝ) ^ (2 * N + 1) = 10 * 100 ^ N := by
        rw [pow_add, pow_mul]
        norm_num
        ring
      rw [hten, pow_succ, mul_pow]
      ring

end Theory.PiDigits.MachinFixedModulusTelescoping

namespace Theory.PiDigits.MachinFixedModulusTelescoping

#print axioms sampledMachinValueRat_cast
#print axioms sampledMachinValueRat_succ
#print axioms sampledMachinForcingAccumulationRat_succ
#print axioms sampledMachinValueRat_add
#print axioms sampledMachinValueRat_add_eq_fixed_denominator
#print axioms sampledMachinForcingRat_pos
#print axioms sampledMachinForcingAccumulationRat_nonneg
#print axioms sampledMachinForcingAccumulationRat_cast_eq_error_telescope
#print axioms sampledMachinValueRat_cast_eq_fixed_denominator_add_error_telescope
#print axioms error_telescope_nonneg
#print axioms sampledMachinForcingAccumulationRat_cast_lt_geometric
#print axioms sampledMachinForcingAccumulationRat_cast_lt_pulse_bound

end Theory.PiDigits.MachinFixedModulusTelescoping
