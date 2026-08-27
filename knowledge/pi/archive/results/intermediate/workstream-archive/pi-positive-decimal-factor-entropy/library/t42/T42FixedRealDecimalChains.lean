import TheoryLib.PiPositiveDecimalFactorEntropy.T31T31DominantPeriodicTransfer
import TheoryLib.PiPositiveDecimalFactorEntropy.T33T33FixedDecimalPeriodicBlocks
import TheoryLib.PiPositiveDecimalFactorEntropy.T36T36DecimalPeriodicWindowGap
import TheoryLib.PiPositiveDecimalFactorEntropy.T40T40DecimalFrequencyDecimation

/-!
# T42: fixed-real sharpness for decimal-frequency chains

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none recorded; the canonical question was formulated locally.

This is a sibling construction for T33's fixed decimal real, not for pi.  At
T33's scale `s`, the starting frequency is the exact model period `D_s`.
Every decimal multiple remains period-divisible, and `H_s / D_s -> infinity`
makes chains of every prescribed finite length strictly admissible.  The file
retains T40's exact endpoint terms and Fejer weights.  It imports unchanged
T33's vanishing full-band normalized energy-density limit.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace DecimalFactorComplexity.T42FixedRealDecimalChains

open DecimalFactorComplexity.DominantPeriodicTransfer
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.FixedDecimalPeriodicBlocks
open DecimalFactorComplexity.PeriodicWindowGap
open DecimalFactorComplexity.T40DecimalFrequencyDecimation
open Theory.PiDigits.T20

abbrev phase := Theory.PiDigits.T27.phase

/-- Ordinary length-`M` orbit sum of T33's one fixed seed. -/
def fixedOrbitPrefixSum (h : ℤ) (M : ℕ) : ℂ :=
  ∑ j ∈ range M, phase h (baseTenOrbit fixedSeed j)

/-- The first `r` terms removed by the decimal-frequency index shift. -/
def fixedLeftEndpointError (h : ℤ) (r : ℕ) : ℂ :=
  ∑ j ∈ range r, phase h (baseTenOrbit fixedSeed j)

/-- The `r` terms added at the right of a length-`M` shifted window. -/
def fixedRightEndpointError (h : ℤ) (M r : ℕ) : ℂ :=
  ∑ j ∈ Ico M (M + r), phase h (baseTenOrbit fixedSeed j)

/-- T33's period is the starting frequency at scale `s`. -/
def startingFrequency (s : ℕ) : ℤ := period s

/-- The frequency `10^r D_s` in the scale-`s` decimal chain. -/
def chainFrequency (s r : ℕ) : ℤ :=
  decimalFrequency (startingFrequency s) r

/-- T31's explicit lower amplitude at T33's scale. -/
def amplitudeLowerBound (s : ℕ) : ℝ :=
  (sampleSize s : ℝ) - 2 * exceptionBudget s -
    phaseError s * sampleSize s

/-- Exact Fejer contribution of the `r`th fixed-seed chain frequency. -/
def fixedDecimalFejerContribution (s r : ℕ) : ℝ :=
  fejerWeight (bandwidth s) (chainFrequency s r) *
    ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ ^ 2

/-- Sum of all fixed-seed contributions indexed by `0 <= r <= R`. -/
def fixedDecimalChainFejerContribution (s R : ℕ) : ℝ :=
  ∑ r ∈ range (R + 1), fixedDecimalFejerContribution s r

/-- The range sum is exactly T31's `Fin (M_s)` circle-prefix sum. -/
theorem fixedOrbitPrefixSum_eq_circlePrefixSum (s : ℕ) (h : ℤ) :
    fixedOrbitPrefixSum h (sampleSize s) = circlePrefixSum (fixedOrbit s) h := by
  simpa only [fixedOrbitPrefixSum, circlePrefixSum, fixedOrbit] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => phase h (baseTenOrbit fixedSeed j)) (sampleSize s)).symm

/-- Decimal frequency multiplication is an exact orbit-index shift for the
T33 fixed seed; no pi-specific input is used. -/
theorem phase_chainFrequency_eq_shift (s : ℕ) (j r : ℕ) :
    phase (chainFrequency s r) (baseTenOrbit fixedSeed j) =
      phase (startingFrequency s) (baseTenOrbit fixedSeed (j + r)) := by
  simp only [chainFrequency, decimalFrequency, startingFrequency, baseTenOrbit]
  change phase (((10 : ℤ) ^ r) * (period s : ℤ))
      (Int.fract ((10 : ℝ) ^ j * fixedSeed)) =
    phase (period s : ℤ)
      (Int.fract ((10 : ℝ) ^ (j + r) * fixedSeed))
  unfold phase
  rw [FixedDecimalPeriodicBlocks.phase_fract_eq_phase,
    FixedDecimalPeriodicBlocks.phase_fract_eq_phase]
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  rw [pow_add]
  ring

/-- Exact endpoint decomposition for the fixed seed. -/
theorem fixedOrbitPrefixSum_chainFrequency_endpoint_identity
    (s M r : ℕ) (hrM : r ≤ M) :
    fixedOrbitPrefixSum (chainFrequency s r) M =
      fixedOrbitPrefixSum (startingFrequency s) M -
        fixedLeftEndpointError (startingFrequency s) r +
          fixedRightEndpointError (startingFrequency s) M r := by
  unfold fixedOrbitPrefixSum
  simp_rw [phase_chainFrequency_eq_shift]
  rw [sum_range_shift_eq_sum_Ico
    (fun j => phase (startingFrequency s) (baseTenOrbit fixedSeed j)) M r]
  have hsplitLeft := sum_range_add_sum_Ico
    (fun j => phase (startingFrequency s) (baseTenOrbit fixedSeed j)) hrM
  have hsplitMiddle := sum_Ico_consecutive
    (f := fun j => phase (startingFrequency s) (baseTenOrbit fixedSeed j))
    hrM (Nat.le_add_right M r)
  unfold fixedLeftEndpointError fixedRightEndpointError
  rw [← hsplitMiddle]
  congr 1
  apply eq_sub_of_add_eq
  simpa only [add_comm] using hsplitLeft

theorem norm_fixedLeftEndpointError_le (h : ℤ) (r : ℕ) :
    ‖fixedLeftEndpointError h r‖ ≤ r := by
  unfold fixedLeftEndpointError
  calc
    ‖∑ j ∈ range r, phase h (baseTenOrbit fixedSeed j)‖ ≤
        ∑ j ∈ range r, ‖phase h (baseTenOrbit fixedSeed j)‖ := norm_sum_le _ _
    _ = r := by simp [Theory.PiDigits.T27.norm_phase]

theorem norm_fixedRightEndpointError_le (h : ℤ) (M r : ℕ) :
    ‖fixedRightEndpointError h M r‖ ≤ r := by
  unfold fixedRightEndpointError
  calc
    ‖∑ j ∈ Ico M (M + r), phase h (baseTenOrbit fixedSeed j)‖ ≤
        ∑ j ∈ Ico M (M + r), ‖phase h (baseTenOrbit fixedSeed j)‖ :=
      norm_sum_le _ _
    _ = r := by simp [Theory.PiDigits.T27.norm_phase]

/-- Exact endpoint identity and its complete `2r` loss. -/
theorem fixedOrbitPrefixSum_chainFrequency_endpoint_bound
    (s M r : ℕ) (hrM : r ≤ M) :
    fixedOrbitPrefixSum (chainFrequency s r) M =
        fixedOrbitPrefixSum (startingFrequency s) M -
          fixedLeftEndpointError (startingFrequency s) r +
            fixedRightEndpointError (startingFrequency s) M r ∧
      ‖fixedOrbitPrefixSum (chainFrequency s r) M -
          fixedOrbitPrefixSum (startingFrequency s) M‖ ≤ 2 * r := by
  refine ⟨fixedOrbitPrefixSum_chainFrequency_endpoint_identity s M r hrM, ?_⟩
  rw [fixedOrbitPrefixSum_chainFrequency_endpoint_identity s M r hrM]
  have hleft := norm_fixedLeftEndpointError_le (startingFrequency s) r
  have hright := norm_fixedRightEndpointError_le (startingFrequency s) M r
  calc
    ‖fixedOrbitPrefixSum (startingFrequency s) M -
          fixedLeftEndpointError (startingFrequency s) r +
          fixedRightEndpointError (startingFrequency s) M r -
        fixedOrbitPrefixSum (startingFrequency s) M‖ =
        ‖-fixedLeftEndpointError (startingFrequency s) r +
          fixedRightEndpointError (startingFrequency s) M r‖ := by
      congr 1
      abel
    _ ≤ ‖fixedLeftEndpointError (startingFrequency s) r‖ +
        ‖fixedRightEndpointError (startingFrequency s) M r‖ := by
      simpa only [norm_neg] using norm_add_le
        (-fixedLeftEndpointError (startingFrequency s) r)
        (fixedRightEndpointError (startingFrequency s) M r)
    _ ≤ r + r := add_le_add hleft hright
    _ = 2 * r := by ring

/-- Every chain frequency is divisible by T33's scale period. -/
theorem period_dvd_chainFrequency (s r : ℕ) :
    (period s : ℤ) ∣ chainFrequency s r := by
  refine ⟨(10 : ℤ) ^ r, ?_⟩
  simp only [chainFrequency, decimalFrequency, startingFrequency]
  ring

/-- The exact absolute frequency is `10^r D_s`. -/
theorem chainFrequency_natAbs (s r : ℕ) :
    (chainFrequency s r).natAbs = 10 ^ r * period s := by
  rw [chainFrequency, decimalFrequency_natAbs]
  simp [startingFrequency]

/-- T31 gives an explicit large ordinary sum at every strictly admissible
period-divisible frequency. -/
theorem amplitudeLowerBound_le_fixedOrbitPrefixSum
    (s : ℕ) (h : ℤ)
    (hadm : h.natAbs < bandwidth s)
    (hdvd : (period s : ℤ) ∣ h) :
    amplitudeLowerBound s ≤
      ‖fixedOrbitPrefixSum h (sampleSize s)‖ := by
  have hH : 1 ≤ bandwidth s := by
    exact ScaleDependentDecimalOrbit.bandwidth_pos (exponent s) (exponent_pos s)
  have hh : h ∈ fejerFrequencies (bandwidth s) :=
    (mem_fejerFrequencies_iff hH).2 hadm
  rw [fixedOrbitPrefixSum_eq_circlePrefixSum]
  exact norm_circlePrefixSum_lower_of_dvd
    (phaseApproximation s) (periodicModelBounds s) h hh hdvd

/-- The T33 starting frequency has the displayed T31 lower bound. -/
theorem amplitudeLowerBound_le_startingOrbitSum
    (s : ℕ) (hadm : period s < bandwidth s) :
    amplitudeLowerBound s ≤
      ‖fixedOrbitPrefixSum (startingFrequency s) (sampleSize s)‖ := by
  apply amplitudeLowerBound_le_fixedOrbitPrefixSum
  · simpa [startingFrequency] using hadm
  · simp [startingFrequency]

/-- Combining T31 with the exact endpoint decomposition exposes the `2r`
loss inherited by every decimal multiple. -/
theorem amplitudeLowerBound_sub_endpoint_le_chainOrbitSum
    (s r : ℕ) (hrM : r ≤ sampleSize s)
    (hstart : period s < bandwidth s) :
    amplitudeLowerBound s - 2 * (r : ℝ) ≤
      ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ := by
  have hbase := amplitudeLowerBound_le_startingOrbitSum s hstart
  have herr :=
    (fixedOrbitPrefixSum_chainFrequency_endpoint_bound s (sampleSize s) r hrM).2
  have htriangle := norm_le_norm_add_norm_sub'
    (fixedOrbitPrefixSum (startingFrequency s) (sampleSize s))
    (fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s))
  rw [norm_sub_rev] at herr
  linarith

/-- Exact strict-band condition for the scale-`s` chain. -/
theorem chainFrequency_admissible_iff (s r : ℕ) :
    (chainFrequency s r).natAbs < bandwidth s ↔
      10 ^ r * period s < bandwidth s := by
  rw [chainFrequency_natAbs]

/-- For every requested chain endpoint `R`, all sufficiently large explicit
T33 scales support `0 <= r <= R`, and the endpoint shift fits in the sample. -/
theorem arbitrarily_long_strictly_admissible_chains (R : ℕ) :
    ∀ᶠ s in atTop,
      R ≤ sampleSize s ∧
        ∀ r : ℕ, r ≤ R →
          10 ^ r * period s < bandwidth s := by
  have hratio := bandwidth_div_period_tendsto_atTop.eventually_gt_atTop
    ((10 : ℝ) ^ R)
  have hsample := bandwidth_tendsto_atTop.eventually_gt_atTop (R : ℝ)
  filter_upwards [hratio, hsample] with s hsRatio hsSample
  constructor
  · have hRB : R ≤ bandwidth s := by exact_mod_cast hsSample.le
    exact hRB.trans (Nat.div_le_self (sampleSize s) 2)
  · intro r hr
    have hDpos : (0 : ℝ) < period s := by
      exact_mod_cast (show 0 < period s by
        simp [period, ScaleDependentDecimalOrbit.period])
    have htop : (10 : ℝ) ^ R * (period s : ℝ) < bandwidth s :=
      (lt_div_iff₀ hDpos).mp hsRatio
    have hpowNat : 10 ^ r ≤ 10 ^ R :=
      Nat.pow_le_pow_right (by norm_num) hr
    have hpow : (10 : ℝ) ^ r ≤ (10 : ℝ) ^ R := by
      exact_mod_cast hpowNat
    have hstrict : (10 : ℝ) ^ r * (period s : ℝ) < bandwidth s :=
      (mul_le_mul_of_nonneg_right hpow hDpos.le).trans_lt htop
    exact_mod_cast hstrict

/-- The exact Fejer summand displays weight `1 - 10^r D_s/H_s`. -/
theorem fixedDecimalFejerContribution_eq_explicit (s r : ℕ) :
    fixedDecimalFejerContribution s r =
      (1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ)) *
        ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ ^ 2 := by
  unfold fixedDecimalFejerContribution fejerWeight
  rw [chainFrequency_natAbs]

/-- Endpoint loss gives a fully displayed lower bound for one Fejer summand. -/
theorem fixedDecimalFejerContribution_lower
    (s r : ℕ) (hrM : r ≤ sampleSize s)
    (hstart : period s < bandwidth s)
    (hadm : 10 ^ r * period s < bandwidth s)
    (hmargin : 2 * (r : ℝ) ≤ amplitudeLowerBound s) :
    (1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ)) *
        (amplitudeLowerBound s - 2 * (r : ℝ)) ^ 2 ≤
      fixedDecimalFejerContribution s r := by
  have hlower := amplitudeLowerBound_sub_endpoint_le_chainOrbitSum
    s r hrM hstart
  have hbase : 0 ≤ amplitudeLowerBound s - 2 * (r : ℝ) :=
    sub_nonneg.mpr hmargin
  have hsquare :
      (amplitudeLowerBound s - 2 * (r : ℝ)) ^ 2 ≤
        ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ ^ 2 := by
    nlinarith [norm_nonneg
      (fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s))]
  have hHpos : (0 : ℝ) < bandwidth s := by
    exact_mod_cast ScaleDependentDecimalOrbit.bandwidth_pos
      (exponent s) (exponent_pos s)
  have hweight :
      0 ≤ 1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_one hHpos).2
    exact_mod_cast (Nat.le_of_lt hadm)
  rw [fixedDecimalFejerContribution_eq_explicit]
  exact mul_le_mul_of_nonneg_left hsquare hweight

/-- Aggregate fixed-real Fejer lower bound over the complete chain range. -/
theorem fixedDecimalChainFejerContribution_lower
    (s R : ℕ) (hRM : R ≤ sampleSize s)
    (hstart : period s < bandwidth s)
    (hadm : ∀ r : ℕ, r ≤ R → 10 ^ r * period s < bandwidth s)
    (hmargin : 2 * (R : ℝ) ≤ amplitudeLowerBound s) :
    (∑ r ∈ range (R + 1),
        (1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ)) *
          (amplitudeLowerBound s - 2 * (r : ℝ)) ^ 2) ≤
      fixedDecimalChainFejerContribution s R := by
  unfold fixedDecimalChainFejerContribution
  apply sum_le_sum
  intro r hr
  have hrR : r ≤ R := by simp only [mem_range] at hr; omega
  apply fixedDecimalFejerContribution_lower s r (hrR.trans hRM) hstart
    (hadm r hrR)
  have hcast : (r : ℝ) ≤ R := by exact_mod_cast hrR
  linarith

/-- T33's explicit amplitude eventually dominates every fixed endpoint loss. -/
theorem amplitudeLowerBound_eventually_ge_endpoint (R : ℕ) :
    ∀ᶠ s in atTop, 2 * (R : ℝ) ≤ amplitudeLowerBound s := by
  have herrHalf : ∀ᶠ s in atTop,
      2 * (exceptionBudget s : ℝ) / sampleSize s + phaseError s < 1 / 2 :=
    (tendsto_order.1 first_error_tendsto_zero).2 (1 / 2) (by norm_num)
  have hbandLarge := bandwidth_tendsto_atTop.eventually_gt_atTop (2 * (R : ℝ))
  filter_upwards [herrHalf, hbandLarge] with s hsError hsBand
  have hMpos : (0 : ℝ) < sampleSize s := by
    exact_mod_cast (show 0 < sampleSize s by
      simp [sampleSize, ScaleDependentDecimalOrbit.sampleSize])
  have hperturb :
      2 * (exceptionBudget s : ℝ) + phaseError s * sampleSize s <
        (sampleSize s : ℝ) / 2 := by
    calc
      2 * (exceptionBudget s : ℝ) + phaseError s * sampleSize s =
          (2 * (exceptionBudget s : ℝ) / sampleSize s + phaseError s) *
            sampleSize s := by
        field_simp [hMpos.ne']
      _ < (1 / 2 : ℝ) * sampleSize s :=
        mul_lt_mul_of_pos_right hsError hMpos
      _ = (sampleSize s : ℝ) / 2 := by ring
  have hMtwoNat : sampleSize s = 2 * bandwidth s :=
    (recursive_parameters s).2.2.2.1
  have hMtwo : (sampleSize s : ℝ) = 2 * bandwidth s := by
    exact_mod_cast hMtwoNat
  have hendpoint : 2 * (R : ℝ) < (sampleSize s : ℝ) / 2 := by
    rw [hMtwo]
    linarith
  unfold amplitudeLowerBound
  linarith

/-- One named fixed-real sharpness certificate exposing scales, period,
frequency, chain range, endpoint errors, exact weights, and aggregate lower
bound. -/
theorem fixed_real_decimal_chain_sharpness (R : ℕ) :
    ∀ᶠ s in atTop,
      exponent s = 4 * 2 ^ s ∧
      sampleSize s = 10 ^ exponent s ∧
      bandwidth s = sampleSize s / 2 ∧
      period s = 3 ^ exponent s ∧
      startingFrequency s = period s ∧
      R ≤ sampleSize s ∧
      2 * (R : ℝ) ≤ amplitudeLowerBound s ∧
      (∀ r : ℕ, r ≤ R →
        (chainFrequency s r).natAbs = 10 ^ r * period s ∧
        (period s : ℤ) ∣ chainFrequency s r ∧
        10 ^ r * period s < bandwidth s ∧
        fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s) =
          fixedOrbitPrefixSum (startingFrequency s) (sampleSize s) -
            fixedLeftEndpointError (startingFrequency s) r +
              fixedRightEndpointError (startingFrequency s) (sampleSize s) r ∧
        ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s) -
            fixedOrbitPrefixSum (startingFrequency s) (sampleSize s)‖ ≤ 2 * r ∧
        amplitudeLowerBound s - 2 * (r : ℝ) ≤
          ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ ∧
        fixedDecimalFejerContribution s r =
          (1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ)) *
            ‖fixedOrbitPrefixSum (chainFrequency s r) (sampleSize s)‖ ^ 2) ∧
      (∑ r ∈ range (R + 1),
          (1 - ((10 ^ r * period s : ℕ) : ℝ) / (bandwidth s : ℝ)) *
            (amplitudeLowerBound s - 2 * (r : ℝ)) ^ 2) ≤
        fixedDecimalChainFejerContribution s R := by
  filter_upwards [arbitrarily_long_strictly_admissible_chains R,
    amplitudeLowerBound_eventually_ge_endpoint R] with s hsChain hsMargin
  obtain ⟨hRM, hadm⟩ := hsChain
  have hparams := recursive_parameters s
  have hstart : period s < bandwidth s := by
    simpa using hadm 0 (Nat.zero_le R)
  refine ⟨hparams.1, hparams.2.1, hparams.2.2.1,
    hparams.2.2.2.2.1, rfl,
    hRM, hsMargin, ?_, ?_⟩
  · intro r hr
    have hrM : r ≤ sampleSize s := hr.trans hRM
    have hend := fixedOrbitPrefixSum_chainFrequency_endpoint_bound
      s (sampleSize s) r hrM
    exact ⟨chainFrequency_natAbs s r, period_dvd_chainFrequency s r,
      hadm r hr, hend.1, hend.2,
      amplitudeLowerBound_sub_endpoint_le_chainOrbitSum s r hrM hstart,
      fixedDecimalFejerContribution_eq_explicit s r⟩
  · exact fixedDecimalChainFejerContribution_lower
      s R hRM hstart hadm hsMargin

/-- Imported unchanged from T33: despite arbitrarily long large chains, the
complete strict-band Fejer energy has vanishing normalized density. -/
theorem normalized_fullBand_energyDensity_tendsto_zero :
    Tendsto (fun s =>
      energy s / ((bandwidth s : ℝ) * (sampleSize s : ℝ) ^ 2))
      atTop (𝓝 0) := by
  exact energy_div_bandwidth_sampleSize_sq_tendsto_zero

/-- The fixed witness is explicitly not pi. -/
theorem fixed_witness_ne_pi : fixedSeed ≠ Real.pi :=
  fixedSeed_ne_pi

/-- The witness fails every fixed instance of T36's effective-irrationality
property. -/
theorem fixed_witness_not_effectiveIrrationality (μ : ℝ) (Q0 : ℕ) :
    ¬ EffectiveIrrationality fixedSeed μ Q0 :=
  t33_fixedSeed_not_effectiveIrrationality μ Q0

structure ScopeStatus where
  fixedWitnessIsPi : Bool
  satisfiesT36EffectiveIrrationality : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  positiveNormalizedEnergyDensity : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  fixedWitnessIsPi := false
  satisfiesT36EffectiveIrrationality := false
  provesC1 := false
  disprovesC1 := false
  positiveNormalizedEnergyDensity := false

/-- Explicit non-pi, T36-failure, C1, and normalized-density nonclaims. -/
theorem explicit_non_pi_C1_scope :
    fixedSeed ≠ Real.pi ∧
      (∀ μ : ℝ, ∀ Q0 : ℕ, ¬ EffectiveIrrationality fixedSeed μ Q0) ∧
      scopeStatus.fixedWitnessIsPi = false ∧
      scopeStatus.satisfiesT36EffectiveIrrationality = false ∧
      scopeStatus.provesC1 = false ∧
      scopeStatus.disprovesC1 = false ∧
      scopeStatus.positiveNormalizedEnergyDensity = false := by
  exact ⟨fixed_witness_ne_pi,
    fun μ Q0 => fixed_witness_not_effectiveIrrationality μ Q0,
    by norm_num [scopeStatus], by norm_num [scopeStatus],
    by norm_num [scopeStatus], by norm_num [scopeStatus],
    by norm_num [scopeStatus]⟩

end DecimalFactorComplexity.T42FixedRealDecimalChains

#print axioms DecimalFactorComplexity.T42FixedRealDecimalChains.fixed_real_decimal_chain_sharpness
#print axioms DecimalFactorComplexity.T42FixedRealDecimalChains.normalized_fullBand_energyDensity_tendsto_zero
#print axioms DecimalFactorComplexity.T42FixedRealDecimalChains.explicit_non_pi_C1_scope
