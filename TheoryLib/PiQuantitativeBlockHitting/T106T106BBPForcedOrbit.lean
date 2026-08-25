import TheoryLib.PiQuantitativeBlockHitting.T104T104BBPSeriesIdentity
import TheoryLib.PiQuantitativeBlockHitting.T38T38MachinForcedOrbit

/-!
# T106: the seven-step BBP forced orbit

The canonical BBP partial sums sampled at `7 * N` give an exact rational
forcing with seven new terms and an exact nonautonomous base-ten recurrence.
This supplies dynamics, but no mixing, density, digit, or V1 conclusion.
-/

noncomputable section

namespace Theory.PiDigits.T106BBPForcedOrbit

open Theory.PiDigits.OversampledBBPGridStability

def sampledBBPValue (N : ℕ) : ℝ :=
  T100BBPRealBridge.bbpRealPartial (7 * N)

def sampledBBPOrbit (N : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ N * sampledBBPValue N)

def sampledBBPError (N : ℕ) : ℝ :=
  (10 : ℝ) ^ N * (Real.pi - sampledBBPValue N)

def sampledBBPForcing (N : ℕ) : ℝ :=
  (10 : ℝ) ^ (N + 1) *
    (sampledBBPValue (N + 1) - sampledBBPValue N)

def sampledBBPForcingRat (N : ℕ) : ℚ :=
  (10 : ℚ) ^ (N + 1) *
    (T77SelectedPadicDefectShell.bbpPartial (7 * (N + 1)) -
      T77SelectedPadicDefectShell.bbpPartial (7 * N))

def bbpErrorRatio : ℝ := 10 / 16 ^ 7

theorem bbpErrorRatio_nonneg : 0 ≤ bbpErrorRatio := by
  norm_num [bbpErrorRatio]

theorem bbpErrorRatio_lt_one : bbpErrorRatio < 1 := by
  norm_num [bbpErrorRatio]

/-- The real forcing is the real embedding of the explicit rational forcing. -/
theorem sampledBBPForcing_eq_cast_rat (N : ℕ) :
    sampledBBPForcing N = (sampledBBPForcingRat N : ℝ) := by
  have hshift : 7 * (N + 1) = 7 * N + 7 := by omega
  simp only [sampledBBPForcing, sampledBBPForcingRat, sampledBBPValue,
    T100BBPRealBridge.bbpRealPartial, hshift]
  push_cast
  ring

/-- Advancing from `7*N` to `7*(N+1)` adds exactly indices `7*N+1..7*N+7`. -/
theorem sampledBBPForcingRat_eq_sevenTerms (N : ℕ) :
    sampledBBPForcingRat N =
      (10 : ℚ) ^ (N + 1) *
        ∑ j ∈ Finset.range 7,
          T98BBPArchimedeanTerm.bbpCombinedTerm (7 * N + j + 1) := by
  simp only [sampledBBPForcingRat]
  rw [show 7 * (N + 1) = 7 * N + 7 by omega,
    T99BBPFiniteTail.bbpPartial_add_sub_eq_sum]

theorem sampledBBPForcingRat_pos (N : ℕ) : 0 < sampledBBPForcingRat N := by
  rw [sampledBBPForcingRat_eq_sevenTerms]
  refine mul_pos (by positivity) ?_
  exact Finset.sum_pos
    (fun j _ ↦ T98BBPArchimedeanTerm.bbpCombinedTerm_pos (7 * N + j + 1))
    ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem sampledBBPForcing_pos (N : ℕ) : 0 < sampledBBPForcing N := by
  rw [sampledBBPForcing_eq_cast_rat]
  exact Rat.cast_pos.2 (sampledBBPForcingRat_pos N)

/-- Exact nonautonomous base-ten recurrence for the sampled BBP orbit. -/
theorem sampledBBPOrbit_succ (N : ℕ) :
    sampledBBPOrbit (N + 1) =
      Int.fract (10 * sampledBBPOrbit N + sampledBBPForcing N) := by
  calc
    sampledBBPOrbit (N + 1) =
        Int.fract (10 * ((10 : ℝ) ^ N * sampledBBPValue (N + 1))) := by
      simp only [sampledBBPOrbit, pow_succ]
      congr 1
      ring
    _ = Int.fract
        (10 * ((10 : ℝ) ^ N * sampledBBPValue N) +
          sampledBBPForcing N) := by
      congr 1
      simp only [sampledBBPForcing, pow_succ]
      ring
    _ = Int.fract
        (10 * sampledBBPOrbit N + sampledBBPForcing N) := by
      exact (Theory.PiDigits.MachinForcedOrbit.fract_natCast_mul_fract_add
        ((10 : ℝ) ^ N * sampledBBPValue N)
        (sampledBBPForcing N) 10).symm

/-- T104 instantiates T100's strict tail bound at the sampled index. -/
theorem pi_sub_sampledBBPValue_lt_pow16 (N : ℕ) :
    Real.pi - sampledBBPValue N < 1 / (16 : ℝ) ^ (7 * N) := by
  exact
    (T100BBPRealBridge.real_bbp_hasSum_tail_bounds
      T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi (7 * N)).2.2

/-- Conditional on the published exponent-eight irrationality-measure input,
the `m`-digit decimal prefix floor of the sevenfold sampled BBP partial sum
eventually agrees with that of `pi`.  This is only a fixed-grid carry-stability
statement; it supplies no cancellation, density, or word occurrence. -/
theorem eventually_decimalPrefixFloor_sampledBBPValue_eq_pi
    (hSource :
      Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow
        Real.pi 8) :
    ∃ C : ℕ, ∀ m : ℕ, C ≤ m →
      decimalPrefixFloor (sampledBBPValue m) m =
        decimalPrefixFloor Real.pi m := by
  obtain ⟨A, hD⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine
      hSource
  obtain ⟨Cscale, hscale⟩ :=
    eventually_powTenEight_lt_powSixteenSeven 0
  refine ⟨max A Cscale, fun m hm ↦ ?_⟩
  have hmA : A ≤ m := (Nat.le_max_left A Cscale).trans hm
  have hmScale : Cscale ≤ m := (Nat.le_max_right A Cscale).trans hm
  have hscale' :
      (10 : ℝ) ^ (8 * m) < (16 : ℝ) ^ (7 * m) := by
    simpa using hscale m hmScale
  have hbelow : sampledBBPValue m ≤ Real.pi :=
    (T100BBPRealBridge.real_bbp_hasSum_tail_bounds
      T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi (7 * m)).1
  have hclose :
      Real.pi - sampledBBPValue m < 1 / (10 : ℝ) ^ (8 * m) :=
    (pi_sub_sampledBBPValue_lt_pow16 m).trans
      (one_div_lt_one_div_of_lt (by positivity) hscale')
  exact decimalPrefixFloor_eq_of_powerTenDiophantine hD hmA hbelow hclose

theorem sampledBBPError_nonneg (N : ℕ) : 0 ≤ sampledBBPError N := by
  refine mul_nonneg (by positivity) ?_
  exact sub_nonneg.mpr
    (T100BBPRealBridge.real_bbp_hasSum_tail_bounds
      T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi (7 * N)).1

theorem scaled_sampledBBPValue_add_error (N : ℕ) :
    (10 : ℝ) ^ N * sampledBBPValue N + sampledBBPError N =
      (10 : ℝ) ^ N * Real.pi := by
  simp only [sampledBBPError]
  ring

/-- Sevenfold sampling makes the decimal-scaled BBP error geometric. -/
theorem sampledBBPError_lt_geometric (N : ℕ) :
    sampledBBPError N < bbpErrorRatio ^ N := by
  have hpow10 : 0 < (10 : ℝ) ^ N := by positivity
  have hm := mul_lt_mul_of_pos_left (pi_sub_sampledBBPValue_lt_pow16 N)
    hpow10
  rw [sampledBBPError]
  calc
    (10 : ℝ) ^ N * (Real.pi - sampledBBPValue N) <
        (10 : ℝ) ^ N * (1 / (16 : ℝ) ^ (7 * N)) := hm
    _ = bbpErrorRatio ^ N := by
      rw [show (16 : ℝ) ^ (7 * N) = ((16 : ℝ) ^ 7) ^ N by
        rw [pow_mul]]
      simp [bbpErrorRatio, inv_pow, div_eq_mul_inv, mul_pow]

theorem summable_sampledBBPError : Summable sampledBBPError := by
  apply Summable.of_nonneg_of_le sampledBBPError_nonneg
    (fun N ↦ (sampledBBPError_lt_geometric N).le)
  exact summable_geometric_of_lt_one bbpErrorRatio_nonneg
    bbpErrorRatio_lt_one

/-- The forcing is the exact base-ten coboundary of the scaled error. -/
theorem sampledBBPForcing_eq_error_coboundary (N : ℕ) :
    sampledBBPForcing N =
      10 * sampledBBPError N - sampledBBPError (N + 1) := by
  simp only [sampledBBPForcing, sampledBBPError, sampledBBPValue]
  rw [show (10 : ℝ) ^ (N + 1) = 10 * 10 ^ N by
    rw [pow_succ]
    ring]
  ring

/-- The moving coordinate recovers the exact decimal pi orbit modulo one. -/
theorem fract_sampledBBPOrbit_add_error (N : ℕ) :
    Int.fract (sampledBBPOrbit N + sampledBBPError N) =
      Int.fract ((10 : ℝ) ^ N * Real.pi) := by
  rw [sampledBBPOrbit, Theory.PiDigits.MachinForcedOrbit.fract_fract_add]
  congr 1
  exact scaled_sampledBBPValue_add_error N

end Theory.PiDigits.T106BBPForcedOrbit
