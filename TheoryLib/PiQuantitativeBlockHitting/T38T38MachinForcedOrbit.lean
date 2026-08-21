import TheoryLib.PiQuantitativeBlockHitting.T37T37FloorSymbolicBridge
import TheoryLib.PiDigits.T26WeylCancellationV1
import TheoryLib.PiDigits.T29FixedFrequencyResonance
import TheoryLib.PiPositiveDecimalFactorEntropy.T33T33FixedDecimalPeriodicBlocks
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# T38: the sampled rational Machin orbit is a summably perturbed pi orbit

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

T36 constructs explicit rational lower Machin approximants to `pi`.  This
module studies the approximants sampled at index `3 * N` and scaled by the
matching decimal power.  Their fractional parts obey an exact forced
base-ten recurrence.  The forcing is rational, while its coboundary is the
positive scaled approximation error.

The error is geometrically summable.  Consequently every fixed-frequency
exponential sum on the sampled rational orbit differs from the corresponding
unwrapped decimal pi sum by a constant independent of the prefix length.
In particular, real Weyl cancellation for the two sequences is equivalent.

This is an obstruction as well as a transfer theorem: the forced rational
recurrence is an exact moving-coordinate presentation of the original pi
orbit.  No result here proves cancellation, density, normality, or the
every-word conjecture.
-/

noncomputable section

open Finset Filter
open scoped ComplexConjugate Real Topology

namespace Theory.PiDigits.MachinForcedOrbit

open Theory.PiDigits.MachinGridStability

/-- The lower Machin approximation sampled three times faster than the
decimal position. -/
def sampledMachinValue (N : ℕ) : ℝ :=
  machinLower (3 * N)

/-- Fractional part of the matching decimal scaling of the sampled rational
Machin approximation. -/
def sampledMachinOrbit (N : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ N * sampledMachinValue N)

/-- The scaled one-sided error between `pi` and the sampled approximant. -/
def sampledMachinError (N : ℕ) : ℝ :=
  (10 : ℝ) ^ N * (Real.pi - sampledMachinValue N)

/-- Rational angular forcing accumulated when the Machin truncation index
advances from `3*N` to `3*(N+1)`. -/
def sampledMachinForcing (N : ℕ) : ℝ :=
  (10 : ℝ) ^ (N + 1) *
    (sampledMachinValue (N + 1) - sampledMachinValue N)

/-- The geometric ratio obtained after decimal scaling and triple sampling.
It is strictly smaller than one. -/
def machinErrorRatio : ℝ :=
  10 / 625 ^ 3

lemma machinErrorRatio_nonneg : 0 ≤ machinErrorRatio := by
  norm_num [machinErrorRatio]

lemma machinErrorRatio_lt_one : machinErrorRatio < 1 := by
  norm_num [machinErrorRatio]

/-- Successive magnitudes in either arctangent series decrease strictly. -/
lemma arctanMagnitude_succ_lt (q n : ℕ) (hq : 2 ≤ q) :
    arctanMagnitude q (n + 1) < arctanMagnitude q n := by
  unfold arctanMagnitude
  have hbase_pos : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  have hbase_one : (q : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)
  have hpow_pos : 0 < ((q : ℝ)⁻¹) ^ (2 * (n + 1) + 1) := by
    positivity
  have hden : 2 * (n : ℝ) + 1 < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by
    norm_num
  calc
    ((q : ℝ)⁻¹) ^ (2 * (n + 1) + 1) /
          (2 * ((n + 1 : ℕ) : ℝ) + 1) <
        ((q : ℝ)⁻¹) ^ (2 * (n + 1) + 1) /
          (2 * (n : ℝ) + 1) := by
      exact (div_lt_div_iff_of_pos_left hpow_pos (by positivity)
        (by positivity)).2 hden
    _ ≤ ((q : ℝ)⁻¹) ^ (2 * n + 1) / (2 * (n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_of_le_one hbase_pos.le hbase_one.le (by omega)

/-- Exact positive-pair presentation of one Machin-approximation step. -/
theorem machinLower_succ_sub_eq (K : ℕ) :
    machinLower (K + 1) - machinLower K =
      16 * (arctanMagnitude 5 (2 * (K + 1)) -
        arctanMagnitude 5 (2 * (K + 1) + 1)) +
      4 * (arctanMagnitude 239 (2 * (K + 1) + 1) -
        arctanMagnitude 239 (2 * (K + 1) + 2)) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (machinLowerRat_succ K)
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] at h
  rw [show (((machinLowerRat (K + 1) : ℚ) : ℝ)) =
        machinLower (K + 1) by rfl,
      show (((machinLowerRat K : ℚ) : ℝ)) = machinLower K by rfl] at h
  unfold arctanMagnitude
  simp [arctanTermRat, pow_succ] at h ⊢
  rw [h]
  ring

/-- The rational lower Machin approximants increase strictly. -/
theorem strictMono_machinLower : StrictMono machinLower := by
  apply strictMono_nat_of_lt_succ
  intro K
  rw [← sub_pos, machinLower_succ_sub_eq]
  have h5 := arctanMagnitude_succ_lt 5 (2 * (K + 1)) (by norm_num)
  have h239 :=
    arctanMagnitude_succ_lt 239 (2 * (K + 1) + 1) (by norm_num)
  positivity

/-- Every sampled value is the real embedding of an explicit rational. -/
theorem sampledMachinValue_isRat (N : ℕ) :
    ∃ r : ℚ, sampledMachinValue N = (r : ℝ) := by
  exact machinLower_isRat (3 * N)

/-- The forcing itself is rational. -/
theorem sampledMachinForcing_isRat (N : ℕ) :
    ∃ r : ℚ, sampledMachinForcing N = (r : ℝ) := by
  refine ⟨(10 : ℚ) ^ (N + 1) *
      (machinLowerRat (3 * (N + 1)) - machinLowerRat (3 * N)), ?_⟩
  simp [sampledMachinForcing, sampledMachinValue, machinLower]

/-- Every forcing increment is strictly positive. -/
theorem sampledMachinForcing_pos (N : ℕ) :
    0 < sampledMachinForcing N := by
  unfold sampledMachinForcing sampledMachinValue
  apply mul_pos (by positivity)
  rw [sub_pos]
  exact strictMono_machinLower (by omega)

/-- The scaled sampled value plus its error is exactly the scaled target. -/
theorem scaled_sampledMachinValue_add_error (N : ℕ) :
    (10 : ℝ) ^ N * sampledMachinValue N + sampledMachinError N =
      (10 : ℝ) ^ N * Real.pi := by
  simp only [sampledMachinError]
  ring

/-- The forcing is the exact base-ten coboundary of the scaled error. -/
theorem sampledMachinForcing_eq_error_coboundary (N : ℕ) :
    sampledMachinForcing N =
      10 * sampledMachinError N - sampledMachinError (N + 1) := by
  simp only [sampledMachinForcing, sampledMachinError, sampledMachinValue]
  rw [show (10 : ℝ) ^ (N + 1) = 10 * 10 ^ N by
    rw [pow_succ]
    ring]
  ring

/-- Taking a fractional part after first taking a fractional part does not
change a further real translation. -/
lemma fract_fract_add (x y : ℝ) :
    Int.fract (Int.fract x + y) = Int.fract (x + y) := by
  calc
    Int.fract (Int.fract x + y) =
        Int.fract ((x + y) - (⌊x⌋ : ℝ)) := by
      congr 1
      rw [Int.fract]
      ring
    _ = Int.fract (x + y) := Int.fract_sub_intCast (x + y) ⌊x⌋

/-- Integer scaling is insensitive, modulo one, to first replacing a real by
its fractional part, even in the presence of an additional translation. -/
lemma fract_natCast_mul_fract_add (x y : ℝ) (n : ℕ) :
    Int.fract ((n : ℝ) * Int.fract x + y) =
      Int.fract ((n : ℝ) * x + y) := by
  let z : ℤ := (n : ℤ) * ⌊x⌋
  calc
    Int.fract ((n : ℝ) * Int.fract x + y) =
        Int.fract (((n : ℝ) * x + y) - (z : ℝ)) := by
      congr 1
      dsimp [z]
      rw [Int.fract]
      push_cast
      ring
    _ = Int.fract ((n : ℝ) * x + y) :=
      Int.fract_sub_intCast ((n : ℝ) * x + y) z

/-- The sampled rational orbit plus its moving error represents the exact
decimal pi orbit on the circle. -/
theorem fract_sampledMachinOrbit_add_error (N : ℕ) :
    Int.fract (sampledMachinOrbit N + sampledMachinError N) =
      Int.fract ((10 : ℝ) ^ N * Real.pi) := by
  rw [sampledMachinOrbit, fract_fract_add]
  congr 1
  exact scaled_sampledMachinValue_add_error N

/-- Exact nonautonomous base-ten recurrence for the sampled rational orbit. -/
theorem sampledMachinOrbit_succ (N : ℕ) :
    sampledMachinOrbit (N + 1) =
      Int.fract (10 * sampledMachinOrbit N + sampledMachinForcing N) := by
  calc
    sampledMachinOrbit (N + 1) =
        Int.fract
          (10 * ((10 : ℝ) ^ N * sampledMachinValue (N + 1))) := by
      simp only [sampledMachinOrbit, pow_succ]
      congr 1
      ring
    _ = Int.fract
        (10 * ((10 : ℝ) ^ N * sampledMachinValue N) +
          sampledMachinForcing N) := by
      congr 1
      simp only [sampledMachinForcing, pow_succ]
      ring
    _ = Int.fract
        (10 * sampledMachinOrbit N + sampledMachinForcing N) := by
      exact (fract_natCast_mul_fract_add
        ((10 : ℝ) ^ N * sampledMachinValue N)
        (sampledMachinForcing N) 10).symm

/-- The sampled error is nonnegative because the rational Machin value lies
below `pi`. -/
theorem sampledMachinError_nonneg (N : ℕ) :
    0 ≤ sampledMachinError N := by
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr (machinLower_le_pi (3 * N)))

/-- Triple sampling turns T36's base-625 tail into a summable geometric
bound after decimal scaling. -/
theorem sampledMachinError_lt_geometric (N : ℕ) :
    sampledMachinError N < machinErrorRatio ^ N := by
  have h := pi_sub_machinLower_lt_pow625 (3 * N)
  have hpow10 : 0 < (10 : ℝ) ^ N := by positivity
  have hm := mul_lt_mul_of_pos_left h hpow10
  rw [sampledMachinError, sampledMachinValue]
  calc
    (10 : ℝ) ^ N * (Real.pi - machinLower (3 * N)) <
        (10 : ℝ) ^ N * (1 / (625 : ℝ) ^ (3 * N)) := hm
    _ = machinErrorRatio ^ N := by
      rw [show (625 : ℝ) ^ (3 * N) = ((625 : ℝ) ^ 3) ^ N by
        rw [pow_mul]]
      simp [machinErrorRatio, inv_pow, div_eq_mul_inv, mul_pow]

/-- The moving-coordinate error is absolutely summable, by comparison with
the geometric ratio supplied by triple sampling. -/
theorem summable_sampledMachinError : Summable sampledMachinError := by
  apply Summable.of_nonneg_of_le sampledMachinError_nonneg
    (fun N => (sampledMachinError_lt_geometric N).le)
  exact summable_geometric_of_lt_one machinErrorRatio_nonneg
    machinErrorRatio_lt_one

/-- A phase at the sampled rational point differs from the corresponding pi
phase by at most `2*pi*|h|` times the scaled Machin error. -/
theorem norm_phase_pi_sub_phase_sampled_le (h : ℤ) (N : ℕ) :
    ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi) -
        Theory.PiDigits.T27.phase h (sampledMachinOrbit N)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) * sampledMachinError N := by
  have hphase :=
    DecimalFactorComplexity.FixedDecimalPeriodicBlocks.norm_phase_sub_phase_le
      h ((10 : ℝ) ^ N * Real.pi)
        ((10 : ℝ) ^ N * sampledMachinValue N)
  have horbit : Theory.PiDigits.T27.phase h (sampledMachinOrbit N) =
      Theory.PiDigits.T27.phase h
        ((10 : ℝ) ^ N * sampledMachinValue N) := by
    exact Theory.PiDigits.T29.phase_fract_eq_phase h
      ((10 : ℝ) ^ N * sampledMachinValue N)
  rw [horbit]
  have habs :
      |(10 : ℝ) ^ N * Real.pi -
          (10 : ℝ) ^ N * sampledMachinValue N| =
        sampledMachinError N := by
    rw [sampledMachinError]
    have hnonneg : 0 ≤ (10 : ℝ) ^ N *
        (Real.pi - sampledMachinValue N) := sampledMachinError_nonneg N
    rw [← abs_of_nonneg hnonneg]
    congr 1
    ring
  simpa only [habs] using hphase

/-- Unnormalized fixed-frequency exponential sum along the sampled rational
Machin orbit. -/
def sampledMachinExponentialSum (M : ℕ) (h : ℤ) : ℂ :=
  ∑ N ∈ range M,
    Theory.PiDigits.T27.phase h (sampledMachinOrbit N)

/-- Unnormalized fixed-frequency exponential sum along the unwrapped decimal
pi orbit. -/
def piDecimalExponentialSum (M : ℕ) (h : ℤ) : ℂ :=
  ∑ N ∈ range M,
    Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi)

/-- The total phase discrepancy over any finite prefix is bounded by the
corresponding finite geometric sum. -/
theorem norm_piDecimalExponentialSum_sub_sampled_le_geometric
    (M : ℕ) (h : ℤ) :
    ‖piDecimalExponentialSum M h - sampledMachinExponentialSum M h‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) *
        ∑ N ∈ range M, machinErrorRatio ^ N := by
  rw [piDecimalExponentialSum, sampledMachinExponentialSum,
    ← sum_sub_distrib]
  calc
    ‖∑ N ∈ range M,
        (Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi) -
          Theory.PiDigits.T27.phase h (sampledMachinOrbit N))‖ ≤
        ∑ N ∈ range M,
          ‖Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N * Real.pi) -
            Theory.PiDigits.T27.phase h (sampledMachinOrbit N)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ N ∈ range M,
        2 * Real.pi * (h.natAbs : ℝ) * machinErrorRatio ^ N := by
      apply sum_le_sum
      intro N hN
      exact (norm_phase_pi_sub_phase_sampled_le h N).trans
        (mul_le_mul_of_nonneg_left
          (sampledMachinError_lt_geometric N).le (by positivity))
    _ = 2 * Real.pi * (h.natAbs : ℝ) *
        ∑ N ∈ range M, machinErrorRatio ^ N := by
      rw [mul_sum]

/-- Uniform-in-prefix Fourier transfer.  The rational sampled orbit and the
pi orbit differ by a constant depending only on the fixed frequency. -/
theorem norm_piDecimalExponentialSum_sub_sampled_le_uniform
    (M : ℕ) (h : ℤ) :
    ‖piDecimalExponentialSum M h - sampledMachinExponentialSum M h‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) / (1 - machinErrorRatio) := by
  refine (norm_piDecimalExponentialSum_sub_sampled_le_geometric M h).trans ?_
  have hgeom : ∑ N ∈ range M, machinErrorRatio ^ N ≤
      (1 - machinErrorRatio)⁻¹ := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := M)
      machinErrorRatio_nonneg machinErrorRatio_lt_one)
  calc
    2 * Real.pi * (h.natAbs : ℝ) *
        ∑ N ∈ range M, machinErrorRatio ^ N ≤
        2 * Real.pi * (h.natAbs : ℝ) *
          (1 - machinErrorRatio)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 * Real.pi * (h.natAbs : ℝ) /
        (1 - machinErrorRatio) := by rw [div_eq_mul_inv]

/-- The normalized difference of the two fixed-frequency sums tends to
zero. -/
theorem tendsto_normalized_sum_difference_zero (h : ℤ) :
    Tendsto
      (fun M : ℕ => (M : ℂ)⁻¹ *
        (piDecimalExponentialSum M h - sampledMachinExponentialSum M h))
      atTop (nhds 0) := by
  let C : ℝ :=
    2 * Real.pi * (h.natAbs : ℝ) / (1 - machinErrorRatio)
  have hbound (M : ℕ) :
      ‖piDecimalExponentialSum M h - sampledMachinExponentialSum M h‖ ≤ C := by
    exact norm_piDecimalExponentialSum_sub_sampled_le_uniform M h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun M => norm_nonneg _) (fun M => ?_)
    (by
      simpa only [zero_mul] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C)
  calc
    ‖(M : ℂ)⁻¹ *
        (piDecimalExponentialSum M h - sampledMachinExponentialSum M h)‖ ≤
        ‖(M : ℂ)⁻¹‖ *
          ‖piDecimalExponentialSum M h - sampledMachinExponentialSum M h‖ :=
      norm_mul_le _ _
    _ ≤ ‖(M : ℂ)⁻¹‖ * C := by
      exact mul_le_mul_of_nonneg_left (hbound M) (norm_nonneg _)
    _ = (M : ℝ)⁻¹ * C := by simp

/-- Weyl cancellation for the sampled rational Machin orbit is equivalent to
Weyl cancellation for the ordinary unwrapped decimal pi orbit. -/
theorem realWeylCancellation_sampled_iff_pi :
    Theory.PiDigits.T26.RealWeylCancellation sampledMachinOrbit ↔
      Theory.PiDigits.T26.RealWeylCancellation
        (fun N => (10 : ℝ) ^ N * Real.pi) := by
  change
    (∀ h : ℤ, h ≠ 0 →
      Tendsto
        (fun M : ℕ => (M : ℂ)⁻¹ * sampledMachinExponentialSum M h)
        atTop (nhds 0)) ↔
    (∀ h : ℤ, h ≠ 0 →
      Tendsto
        (fun M : ℕ => (M : ℂ)⁻¹ * piDecimalExponentialSum M h)
        atTop (nhds 0))
  constructor
  · intro hsampled h hh
    have hdiff := tendsto_normalized_sum_difference_zero h
    have hadd := hdiff.add (hsampled h hh)
    convert hadd using 1
    · funext M
      ring
    · ring
  · intro hpi h hh
    have hdiff := tendsto_normalized_sum_difference_zero h
    have hsub := (hpi h hh).sub hdiff
    convert hsub using 1
    · funext M
      ring
    · ring

end Theory.PiDigits.MachinForcedOrbit

namespace Theory.PiDigits.MachinForcedOrbit

#print axioms sampledMachinValue_isRat
#print axioms sampledMachinForcing_isRat
#print axioms machinErrorRatio_nonneg
#print axioms machinErrorRatio_lt_one
#print axioms arctanMagnitude_succ_lt
#print axioms machinLower_succ_sub_eq
#print axioms strictMono_machinLower
#print axioms sampledMachinForcing_pos
#print axioms scaled_sampledMachinValue_add_error
#print axioms sampledMachinForcing_eq_error_coboundary
#print axioms fract_fract_add
#print axioms fract_natCast_mul_fract_add
#print axioms fract_sampledMachinOrbit_add_error
#print axioms sampledMachinOrbit_succ
#print axioms sampledMachinError_nonneg
#print axioms sampledMachinError_lt_geometric
#print axioms summable_sampledMachinError
#print axioms norm_phase_pi_sub_phase_sampled_le
#print axioms norm_piDecimalExponentialSum_sub_sampled_le_geometric
#print axioms norm_piDecimalExponentialSum_sub_sampled_le_uniform
#print axioms tendsto_normalized_sum_difference_zero
#print axioms realWeylCancellation_sampled_iff_pi

end Theory.PiDigits.MachinForcedOrbit
