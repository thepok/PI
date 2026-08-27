import TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier
import TheoryLib.PiPositiveDecimalFactorEntropy.T13T13AutocorrelationAmplification

/-!
# T40: decimal frequency decimation

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file proves finite endpoint-shift and Fejer-chain statements.  Its only
pi-specific amplification theorem assumes the literal failure of canonical
C1.  It makes no unconditional assertion about pi or C1.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T40DecimalFrequencyDecimation

open DecimalFactorComplexity
open DecimalFactorComplexity.AutocorrelationAmplification
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.ScaleAdaptiveOrbitFourier

abbrev phase := Theory.PiDigits.T27.phase

/-- The first `r` terms removed when a length-`M` window is shifted by `r`. -/
def leftEndpointError (h : ℤ) (r : ℕ) : ℂ :=
  ∑ j ∈ range r, phase h (piDecimalShiftOrbit j)

/-- The `r` terms added at the right when a length-`M` window is shifted by `r`. -/
def rightEndpointError (h : ℤ) (M r : ℕ) : ℂ :=
  ∑ j ∈ Ico M (M + r), phase h (piDecimalShiftOrbit j)

/-- Multiplication of the frequency by `10^r` is exactly an index shift by `r`. -/
theorem phase_decimalFrequency_eq_shift (h : ℤ) (j r : ℕ) :
    phase (((10 : ℤ) ^ r) * h) (piDecimalShiftOrbit j) =
      phase h (piDecimalShiftOrbit (j + r)) := by
  simp only [piDecimalShiftOrbit, Theory.PiDigits.T20.baseTenOrbit]
  change Theory.PiDigits.T27.phase (((10 : ℤ) ^ r) * h)
      (Int.fract ((10 : ℝ) ^ j * Real.pi)) =
    Theory.PiDigits.T27.phase h
      (Int.fract ((10 : ℝ) ^ (j + r) * Real.pi))
  rw [phase_fract_eq_phase, phase_fract_eq_phase]
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  rw [pow_add]
  ring

/-- A shifted range is the corresponding natural-number interval. -/
theorem sum_range_shift_eq_sum_Ico
    (a : ℕ → ℂ) (M r : ℕ) :
    (∑ j ∈ range M, a (j + r)) = ∑ j ∈ Ico r (M + r), a j := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  apply sum_congr rfl
  intro j hj
  congr 1
  omega

/-- Exact endpoint decomposition, valid when the shift does not exceed the window. -/
theorem piOrbitSum_decimalFrequency_endpoint_identity
    (h : ℤ) (M r : ℕ) (hrM : r ≤ M) :
    piOrbitSum (((10 : ℤ) ^ r) * h) M =
      piOrbitSum h M - leftEndpointError h r + rightEndpointError h M r := by
  rw [piOrbitSum_eq_circleOrbitPhase_sum, piOrbitSum_eq_circleOrbitPhase_sum]
  simp_rw [circleOrbitPhase, phase_decimalFrequency_eq_shift]
  rw [sum_range_shift_eq_sum_Ico
    (fun j => phase h (piDecimalShiftOrbit j)) M r]
  have hsplitLeft := sum_range_add_sum_Ico
    (fun j => phase h (piDecimalShiftOrbit j)) hrM
  have hsplitMiddle := sum_Ico_consecutive
    (f := fun j => phase h (piDecimalShiftOrbit j)) hrM (Nat.le_add_right M r)
  unfold leftEndpointError rightEndpointError
  rw [← hsplitMiddle]
  congr 1
  apply eq_sub_of_add_eq
  simpa only [add_comm] using hsplitLeft

/-- The left endpoint error has exactly `r` unit-modulus summands. -/
theorem norm_leftEndpointError_le (h : ℤ) (r : ℕ) :
    ‖leftEndpointError h r‖ ≤ r := by
  unfold leftEndpointError
  calc
    ‖∑ j ∈ range r, phase h (piDecimalShiftOrbit j)‖ ≤
        ∑ j ∈ range r, ‖phase h (piDecimalShiftOrbit j)‖ := norm_sum_le _ _
    _ = r := by simp [Theory.PiDigits.T27.norm_phase]

/-- The right endpoint error has exactly `r` unit-modulus summands. -/
theorem norm_rightEndpointError_le (h : ℤ) (M r : ℕ) :
    ‖rightEndpointError h M r‖ ≤ r := by
  unfold rightEndpointError
  calc
    ‖∑ j ∈ Ico M (M + r), phase h (piDecimalShiftOrbit j)‖ ≤
        ∑ j ∈ Ico M (M + r), ‖phase h (piDecimalShiftOrbit j)‖ := norm_sum_le _ _
    _ = r := by simp [Theory.PiDigits.T27.norm_phase]

/-- Exact endpoint identity together with its explicit `2r` norm loss. -/
theorem piOrbitSum_decimalFrequency_endpoint_bound
    (h : ℤ) (M r : ℕ) (hrM : r ≤ M) :
    piOrbitSum (((10 : ℤ) ^ r) * h) M =
        piOrbitSum h M - leftEndpointError h r + rightEndpointError h M r ∧
      ‖piOrbitSum (((10 : ℤ) ^ r) * h) M - piOrbitSum h M‖ ≤ 2 * r := by
  refine ⟨piOrbitSum_decimalFrequency_endpoint_identity h M r hrM, ?_⟩
  rw [piOrbitSum_decimalFrequency_endpoint_identity h M r hrM]
  have hleft := norm_leftEndpointError_le h r
  have hright := norm_rightEndpointError_le h M r
  calc
    ‖piOrbitSum h M - leftEndpointError h r + rightEndpointError h M r -
        piOrbitSum h M‖ = ‖-leftEndpointError h r + rightEndpointError h M r‖ := by
          congr 1
          abel
    _ ≤ ‖leftEndpointError h r‖ + ‖rightEndpointError h M r‖ := by
      simpa only [norm_neg] using norm_add_le (-leftEndpointError h r) (rightEndpointError h M r)
    _ ≤ r + r := add_le_add hleft hright
    _ = 2 * r := by ring

/-- The `r`th frequency in the decimal chain `h, 10h, 10^2h, ...`. -/
def decimalFrequency (h : ℤ) (r : ℕ) : ℤ := ((10 : ℤ) ^ r) * h

/-- Membership of the `r`th decimal frequency in the strict Fejer band. -/
def DecimalFrequencyAdmissible (H : ℕ) (h : ℤ) (r : ℕ) : Prop :=
  (decimalFrequency h r).natAbs < H

/-- The absolute frequency is exactly `10^r * |h|`. -/
theorem decimalFrequency_natAbs (h : ℤ) (r : ℕ) :
    (decimalFrequency h r).natAbs = 10 ^ r * h.natAbs := by
  simp [decimalFrequency, Int.natAbs_mul, Int.natAbs_pow]

/-- The exact strict frequency range at every chain index. -/
theorem decimalFrequencyAdmissible_iff (H : ℕ) (h : ℤ) (r : ℕ) :
    DecimalFrequencyAdmissible H h r ↔ 10 ^ r * h.natAbs < H := by
  rw [DecimalFrequencyAdmissible, decimalFrequency_natAbs]

/-- The reverse triangle inequality loses at most the two endpoint blocks. -/
theorem norm_piOrbitSum_decimalFrequency_lower
    (h : ℤ) (M r : ℕ) (hrM : r ≤ M) :
    ‖piOrbitSum h M‖ - 2 * (r : ℝ) ≤
      ‖piOrbitSum (decimalFrequency h r) M‖ := by
  have herr := (piOrbitSum_decimalFrequency_endpoint_bound h M r hrM).2
  change ‖piOrbitSum (decimalFrequency h r) M - piOrbitSum h M‖ ≤
    2 * (r : ℝ) at herr
  have htriangle := norm_le_norm_add_norm_sub'
    (piOrbitSum h M) (piOrbitSum (decimalFrequency h r) M)
  rw [norm_sub_rev] at herr
  linarith

/-- The exact Fejer summand belonging to the `r`th decimal frequency. -/
def decimalFejerContribution (M H : ℕ) (h : ℤ) (r : ℕ) : ℝ :=
  fejerWeight H (decimalFrequency h r) *
    ‖piOrbitSum (decimalFrequency h r) M‖ ^ 2

/-- The contribution displays the exact weight `1 - 10^r|h|/H`. -/
theorem decimalFejerContribution_eq_explicit
    (M H : ℕ) (h : ℤ) (r : ℕ) :
    decimalFejerContribution M H h r =
      (1 - ((10 ^ r * h.natAbs : ℕ) : ℝ) / (H : ℝ)) *
        ‖piOrbitSum (decimalFrequency h r) M‖ ^ 2 := by
  unfold decimalFejerContribution fejerWeight
  rw [decimalFrequency_natAbs]

/-- Every admissible chain frequency has a nonnegative exact Fejer weight. -/
theorem decimalFejerWeight_nonneg
    (H : ℕ) (h : ℤ) (r : ℕ)
    (hadm : DecimalFrequencyAdmissible H h r) :
    0 ≤ fejerWeight H (decimalFrequency h r) := by
  have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le _) hadm
  unfold fejerWeight
  apply sub_nonneg.mpr
  apply (div_le_one (by exact_mod_cast hH)).2
  exact_mod_cast (Nat.le_of_lt hadm)

/-- Endpoint loss gives the displayed lower bound for one exact Fejer summand. -/
theorem decimalFejerContribution_lower
    (M H : ℕ) (h : ℤ) (r : ℕ)
    (hrM : r ≤ M) (hadm : DecimalFrequencyAdmissible H h r)
    (hmargin : 2 * (r : ℝ) ≤ ‖piOrbitSum h M‖) :
    fejerWeight H (decimalFrequency h r) *
        (‖piOrbitSum h M‖ - 2 * (r : ℝ)) ^ 2 ≤
      decimalFejerContribution M H h r := by
  have hlower := norm_piOrbitSum_decimalFrequency_lower h M r hrM
  have hbase : 0 ≤ ‖piOrbitSum h M‖ - 2 * (r : ℝ) := sub_nonneg.mpr hmargin
  have hsquare :
      (‖piOrbitSum h M‖ - 2 * (r : ℝ)) ^ 2 ≤
        ‖piOrbitSum (decimalFrequency h r) M‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖piOrbitSum (decimalFrequency h r) M‖ -
        (‖piOrbitSum h M‖ - 2 * (r : ℝ)))]
  unfold decimalFejerContribution
  exact mul_le_mul_of_nonneg_left hsquare
    (decimalFejerWeight_nonneg H h r hadm)

/-- Sum of every exact Fejer contribution in `h,10h,...,10^R h`. -/
def decimalChainFejerContribution (M H : ℕ) (h : ℤ) (R : ℕ) : ℝ :=
  ∑ r ∈ range (R + 1), decimalFejerContribution M H h r

/-- Aggregate amplification along a wholly admissible decimal chain. -/
theorem decimalChainFejerContribution_lower
    (M H : ℕ) (h : ℤ) (R : ℕ)
    (hRM : R ≤ M)
    (hadm : ∀ r : ℕ, r ≤ R → DecimalFrequencyAdmissible H h r)
    (hmargin : 2 * (R : ℝ) ≤ ‖piOrbitSum h M‖) :
    (∑ r ∈ range (R + 1),
        fejerWeight H (decimalFrequency h r) *
          (‖piOrbitSum h M‖ - 2 * (r : ℝ)) ^ 2) ≤
      decimalChainFejerContribution M H h R := by
  unfold decimalChainFejerContribution
  apply sum_le_sum
  intro r hr
  have hrR : r ≤ R := by simp only [mem_range] at hr; omega
  apply decimalFejerContribution_lower M H h r (hrR.trans hRM) (hadm r hrR)
  have hcast : (r : ℝ) ≤ R := by exact_mod_cast hrR
  linarith

/-- A finite decimal chain either stays strictly inside the Fejer band or has
an adjacent crossing of its boundary. -/
theorem admissibleChain_or_adjacentBoundary
    (H : ℕ) (h : ℤ) (R : ℕ)
    (hzero : DecimalFrequencyAdmissible H h 0) :
    (∀ r : ℕ, r ≤ R → DecimalFrequencyAdmissible H h r) ∨
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧
        (decimalFrequency h (r - 1)).natAbs < H ∧
        H ≤ (decimalFrequency h r).natAbs := by
  induction R with
  | zero =>
      left
      intro r hr
      have : r = 0 := by omega
      simpa [this] using hzero
  | succ R ih =>
      rcases ih with hall | ⟨r, hr1, hrR, hprev, hcross⟩
      · by_cases hnext : DecimalFrequencyAdmissible H h (R + 1)
        · left
          intro r hr
          by_cases hre : r = R + 1
          · simpa [hre] using hnext
          · exact hall r (by omega)
        · right
          refine ⟨R + 1, by omega, by omega, ?_, ?_⟩
          · simpa only [Nat.add_sub_cancel] using hall R (by omega)
          · exact Nat.le_of_not_gt hnext
      · right
        exact ⟨r, hr1, hrR.trans (Nat.le_succ R), hprev, hcross⟩

/-- The exponent `n` is no larger than the decimal sample size `10^n`. -/
lemma self_le_ten_pow (n : ℕ) : n ≤ 10 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
      omega

/-- Literal failure of C1 gives, for `B` then `N` then `R`, one T10 witness
with either the complete explicit Fejer amplification chain or an adjacent
boundary-frequency obstruction.  The normalization and lower scale precede
all witnesses exactly as in T10. -/
theorem piFailureC1_implies_decimalChain_amplification_or_boundary
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N → ∀ R : ℕ,
      ∃ n k M H : ℕ, ∃ h : ℤ,
        N ≤ n ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧ h ≠ 0 ∧ h.natAbs < H ∧
          B * (M : ℝ) < ‖piOrbitSum h M‖ ^ 2 ∧ R ≤ M ∧
          (((∀ r : ℕ, r ≤ R → 10 ^ r * h.natAbs < H) ∧
              (∀ r : ℕ, r ≤ R →
                piOrbitSum (decimalFrequency h r) M =
                    piOrbitSum h M - leftEndpointError h r +
                      rightEndpointError h M r ∧
                ‖piOrbitSum (decimalFrequency h r) M - piOrbitSum h M‖ ≤
                    2 * (r : ℝ) ∧
                decimalFejerContribution M H h r =
                  (1 - ((10 ^ r * h.natAbs : ℕ) : ℝ) / (H : ℝ)) *
                    ‖piOrbitSum (decimalFrequency h r) M‖ ^ 2) ∧
              (∑ r ∈ range (R + 1),
                  fejerWeight H (decimalFrequency h r) *
                    (‖piOrbitSum h M‖ - 2 * (r : ℝ)) ^ 2) ≤
                decimalChainFejerContribution M H h R) ∨
            ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧
              10 ^ (r - 1) * h.natAbs < H ∧
              H ≤ 10 ^ r * h.natAbs) := by
  intro B hB N hN R
  let Bstar : ℝ := max B (4 * (R : ℝ) ^ 2)
  have hBstar : 0 ≤ Bstar := le_trans hB (le_max_left _ _)
  have hNstar : 1 ≤ max N R := hN.trans (le_max_left _ _)
  obtain ⟨n, k, M, H, h, hn, hM, hk, hH, hh0, hhH, hlarge⟩ :=
    piFailureC1_implies_arbitrarily_large_scale_resonance
      hfailure Bstar hBstar (max N R) hNstar
  have hNn : N ≤ n := (le_max_left N R).trans hn
  have hRn : R ≤ n := (le_max_right N R).trans hn
  have hRM : R ≤ M := by
    rw [hM]
    exact hRn.trans (self_le_ten_pow n)
  have hMnat : 1 ≤ M := by
    rw [hM]
    exact one_le_pow₀ (by norm_num)
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hMnat
  have hBlarge : B * (M : ℝ) < ‖piOrbitSum h M‖ ^ 2 := by
    calc
      B * (M : ℝ) ≤ Bstar * (M : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ < ‖piOrbitSum h M‖ ^ 2 := hlarge
  have hthreshold : 4 * (R : ℝ) ^ 2 ≤ Bstar := le_max_right _ _
  have hscaledThreshold : 4 * (R : ℝ) ^ 2 ≤ Bstar * (M : ℝ) := by
    calc
      4 * (R : ℝ) ^ 2 ≤ Bstar := hthreshold
      _ ≤ Bstar * (M : ℝ) := by nlinarith
  have hmargin : 2 * (R : ℝ) ≤ ‖piOrbitSum h M‖ := by
    nlinarith [hscaledThreshold, hlarge, norm_nonneg (piOrbitSum h M)]
  have hzero : DecimalFrequencyAdmissible H h 0 := by
    simpa [DecimalFrequencyAdmissible, decimalFrequency] using hhH
  refine ⟨n, k, M, H, h, hNn, hM, hk, hH, hh0, hhH, hBlarge, hRM, ?_⟩
  rcases admissibleChain_or_adjacentBoundary H h R hzero with hall | hboundary
  · left
    have hallExplicit : ∀ r : ℕ, r ≤ R → 10 ^ r * h.natAbs < H := by
      intro r hr
      exact (decimalFrequencyAdmissible_iff H h r).mp (hall r hr)
    refine ⟨hallExplicit, ?_,
      decimalChainFejerContribution_lower M H h R hRM hall hmargin⟩
    intro r hr
    have hend := piOrbitSum_decimalFrequency_endpoint_bound h M r (hr.trans hRM)
    exact ⟨hend.1, hend.2, decimalFejerContribution_eq_explicit M H h r⟩
  · right
    obtain ⟨r, hr1, hrR, hprev, hcross⟩ := hboundary
    rw [decimalFrequency_natAbs] at hprev hcross
    exact ⟨r, hr1, hrR, hprev, hcross⟩

/-- Machine-readable scope record.  `false` means T40 makes no such claim. -/
structure ScopeStatus where
  unconditionalPiClaim : Bool
  provesC1 : Bool
  fullChainWithoutBoundaryAlternative : Bool
  fixedNormalizedThreshold : Bool
  positiveDensityCommonSpectrum : Bool
  retainsBoundaryObstruction : Bool
  deriving DecidableEq, Repr

/-! Comparison source: `knowledge_library/t15/T15_INVERSE_STRUCTURE_AUDIT.md`,
SHA-256: `d68e9b853a4628a01252834178c2b1dc8a9dc2c113135491543579569796cb01`.
The audit is `literature-checked` for its bounded corpus, not a theorem about
all possible inverse methods. -/

/-- T40 supplies finite witness-dependent mass only.  It does not supply the
fixed normalized threshold or positive-density common spectrum identified as
missing by the bounded T15 audit. -/
def scopeStatus : ScopeStatus where
  unconditionalPiClaim := false
  provesC1 := false
  fullChainWithoutBoundaryAlternative := false
  fixedNormalizedThreshold := false
  positiveDensityCommonSpectrum := false
  retainsBoundaryObstruction := true

/-- Explicit nonclaims and the retained boundary alternative. -/
theorem explicit_scope_and_T15_nonclaims :
    scopeStatus.unconditionalPiClaim = false ∧
      scopeStatus.provesC1 = false ∧
      scopeStatus.fullChainWithoutBoundaryAlternative = false ∧
      scopeStatus.fixedNormalizedThreshold = false ∧
      scopeStatus.positiveDensityCommonSpectrum = false ∧
      scopeStatus.retainsBoundaryObstruction = true := by
  norm_num [scopeStatus]

end DecimalFactorComplexity.T40DecimalFrequencyDecimation

#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.phase_decimalFrequency_eq_shift
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.piOrbitSum_decimalFrequency_endpoint_identity
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.norm_leftEndpointError_le
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.norm_rightEndpointError_le
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.piOrbitSum_decimalFrequency_endpoint_bound
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalFrequency_natAbs
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalFrequencyAdmissible_iff
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.norm_piOrbitSum_decimalFrequency_lower
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalFejerContribution_eq_explicit
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalFejerWeight_nonneg
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalFejerContribution_lower
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.decimalChainFejerContribution_lower
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.admissibleChain_or_adjacentBoundary
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.piFailureC1_implies_decimalChain_amplification_or_boundary
#print axioms DecimalFactorComplexity.T40DecimalFrequencyDecimation.explicit_scope_and_T15_nonclaims
