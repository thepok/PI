import TheoryLib.PiQuantitativeBlockHitting.T39T39EventualRecurrentTransfer

/-!
# T40: exact local arithmetic of the sampled Machin forcing

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T38 shows that the triple-sampled rational Machin orbit obeys a forced
base-ten recurrence.  This module expands one forcing increment into the
six newly exposed Taylor terms from each arctangent series.  It also records
the elementary denominator-clearing identity behind each positive pair and
proves that, for both Machin bases, the cleared numerator is exactly twice
an odd integer.

These are exact arithmetic identities.  They do not imply cancellation,
orbit density, normality, or the every-word conjecture.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.MachinLocalForcing

open Theory.PiDigits.MachinGridStability
open Theory.PiDigits.MachinForcedOrbit

/-- Six consecutive rational Taylor terms beginning at `start`. -/
def sixTermArctanWindowRat (q start : ℕ) : ℚ :=
  ∑ j ∈ range 6, arctanTermRat q (start + j)

/-- The exact rational forcing window exposed between sampled indices
`3*N` and `3*(N+1)`. -/
def sampledMachinForcingRat (N : ℕ) : ℚ :=
  (10 : ℚ) ^ (N + 1) *
    (16 * sixTermArctanWindowRat 5 (6 * N + 2) -
      4 * sixTermArctanWindowRat 239 (6 * N + 3))

/-- Advancing the Machin truncation by three exposes exactly six new terms
from each arctangent series. -/
theorem machinLowerRat_threeStep_sub_eq (N : ℕ) :
    machinLowerRat (3 * (N + 1)) - machinLowerRat (3 * N) =
      16 * sixTermArctanWindowRat 5 (6 * N + 2) -
        4 * sixTermArctanWindowRat 239 (6 * N + 3) := by
  have h0 := machinLowerRat_succ (3 * N)
  have h1 := machinLowerRat_succ (3 * N + 1)
  have h2 := machinLowerRat_succ (3 * N + 2)
  simp only [sixTermArctanWindowRat, sum_range_succ, sum_range_zero,
    zero_add] at ⊢
  rw [show 3 * (N + 1) = (3 * N + 2) + 1 by omega, h2,
    show 3 * N + 2 = (3 * N + 1) + 1 by omega, h1,
    show 3 * N + 1 = 3 * N + 1 by rfl, h0]
  ring_nf

/-- The real forcing from T38 is the embedding of the explicit twelve-term
rational window. -/
theorem sampledMachinForcing_eq_cast_rat (N : ℕ) :
    sampledMachinForcing N = (sampledMachinForcingRat N : ℝ) := by
  have h := congrArg (fun r : ℚ ↦ (r : ℝ))
    (machinLowerRat_threeStep_sub_eq N)
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at h
  simp only [sampledMachinForcing, sampledMachinValue, sampledMachinForcingRat,
    machinLower, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_sub,
    h]

/-- One adjacent positive pair of decreasing arctangent magnitudes. -/
def arctanMagnitudePair (q n : ℕ) : ℝ :=
  arctanMagnitude q n - arctanMagnitude q (n + 1)

/-- Every adjacent magnitude pair is strictly positive once the base is at
least two. -/
theorem arctanMagnitudePair_pos (q n : ℕ) (hq : 2 ≤ q) :
    0 < arctanMagnitudePair q n := by
  exact sub_pos.mpr (arctanMagnitude_succ_lt q n hq)

/-- The three adjacent positive pairs exposed by advancing a truncation
index by three. -/
def threeArctanMagnitudePairs (q start : ℕ) : ℝ :=
  ∑ j ∈ range 3, arctanMagnitudePair q (start + 2 * j)

/-- A three-pair window is strictly positive. -/
theorem threeArctanMagnitudePairs_pos
    (q start : ℕ) (hq : 2 ≤ q) :
    0 < threeArctanMagnitudePairs q start := by
  have h0 := arctanMagnitudePair_pos q start hq
  have h1 := arctanMagnitudePair_pos q (start + 2) hq
  have h2 := arctanMagnitudePair_pos q (start + 4) hq
  simp only [threeArctanMagnitudePairs, sum_range_succ, sum_range_zero,
    zero_add]
  positivity

/-- The three-step Machin increment is an exact sum of three positive pairs
from each arctangent series. -/
theorem machinLower_threeStep_sub_eq_positivePairs (N : ℕ) :
    machinLower (3 * (N + 1)) - machinLower (3 * N) =
      16 * threeArctanMagnitudePairs 5 (6 * N + 2) +
        4 * threeArctanMagnitudePairs 239 (6 * N + 3) := by
  have h0 := machinLower_succ_sub_eq (3 * N)
  have h1 := machinLower_succ_sub_eq (3 * N + 1)
  have h2 := machinLower_succ_sub_eq (3 * N + 2)
  rw [show 3 * (N + 1) = (3 * N + 2) + 1 by omega]
  calc
    machinLower (3 * N + 2 + 1) - machinLower (3 * N) =
        (machinLower (3 * N + 2 + 1) - machinLower (3 * N + 2)) +
          (machinLower (3 * N + 1 + 1) - machinLower (3 * N + 1)) +
          (machinLower (3 * N + 1) - machinLower (3 * N)) := by
      ring
    _ = 16 * threeArctanMagnitudePairs 5 (6 * N + 2) +
        4 * threeArctanMagnitudePairs 239 (6 * N + 3) := by
      rw [h2, h1, h0]
      simp only [threeArctanMagnitudePairs, arctanMagnitudePair,
        sum_range_succ, sum_range_zero, zero_add]
      ring_nf

/-- Exact positive-pair presentation of the forcing itself. -/
theorem sampledMachinForcing_eq_positivePairs (N : ℕ) :
    sampledMachinForcing N =
      (10 : ℝ) ^ (N + 1) *
        (16 * threeArctanMagnitudePairs 5 (6 * N + 2) +
          4 * threeArctanMagnitudePairs 239 (6 * N + 3)) := by
  unfold sampledMachinForcing sampledMachinValue
  rw [machinLower_threeStep_sub_eq_positivePairs]

/-- A positive alternating pair written with odd exponents `r` and `r+2`.
The useful applications have odd positive `q` and `r`. -/
def oddPowerPairRat (q r : ℕ) : ℚ :=
  1 / ((r : ℚ) * (q : ℚ) ^ r) -
    1 / (((r + 2 : ℕ) : ℚ) * (q : ℚ) ^ (r + 2))

/-- Integer numerator exposed after clearing the natural common denominator
of one alternating pair. -/
def pairedNumerator (q r : ℕ) : ℤ :=
  (q : ℤ) ^ 2 * (r + 2) - r

/-- Clearing the natural denominator of one alternating pair produces the
small explicit integer `q^2*(r+2)-r`. -/
theorem oddPowerPairRat_denominator_clear
    (q r : ℕ) (hq : q ≠ 0) (hr : r ≠ 0) :
    ((r : ℚ) * (r + 2) * (q : ℚ) ^ (r + 2)) *
        oddPowerPairRat q r =
      (pairedNumerator q r : ℚ) := by
  unfold oddPowerPairRat pairedNumerator
  push_cast
  rw [pow_add]
  field_simp

/-- At base five, every cleared pair numerator is exactly twice an odd
integer. -/
theorem pairedNumerator_five_twice_odd (r : ℕ) :
    ∃ z : ℤ, Odd z ∧ pairedNumerator 5 r = 2 * z := by
  refine ⟨12 * (r : ℤ) + 25, ?_, ?_⟩
  · refine ⟨6 * (r : ℤ) + 12, ?_⟩
    ring
  · simp [pairedNumerator]
    ring

/-- At base 239, every cleared pair numerator is exactly twice an odd
integer. -/
theorem pairedNumerator_twoThirtyNine_twice_odd (r : ℕ) :
    ∃ z : ℤ, Odd z ∧ pairedNumerator 239 r = 2 * z := by
  refine ⟨28560 * (r : ℤ) + 57121, ?_, ?_⟩
  · refine ⟨14280 * (r : ℤ) + 28560, ?_⟩
    ring
  · simp [pairedNumerator]
    ring

end Theory.PiDigits.MachinLocalForcing

#print axioms Theory.PiDigits.MachinLocalForcing.machinLowerRat_threeStep_sub_eq
#print axioms Theory.PiDigits.MachinLocalForcing.sampledMachinForcing_eq_cast_rat
#print axioms Theory.PiDigits.MachinLocalForcing.arctanMagnitudePair_pos
#print axioms Theory.PiDigits.MachinLocalForcing.threeArctanMagnitudePairs_pos
#print axioms Theory.PiDigits.MachinLocalForcing.machinLower_threeStep_sub_eq_positivePairs
#print axioms Theory.PiDigits.MachinLocalForcing.sampledMachinForcing_eq_positivePairs
#print axioms Theory.PiDigits.MachinLocalForcing.oddPowerPairRat_denominator_clear
#print axioms Theory.PiDigits.MachinLocalForcing.pairedNumerator_five_twice_odd
#print axioms Theory.PiDigits.MachinLocalForcing.pairedNumerator_twoThirtyNine_twice_odd
