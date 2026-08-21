import TheoryLib.PiPositiveDecimalFactorEntropy.T2T2ExponentialCollisionCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T6T6PairCorrelationConditional
import TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy

/-!
# T7: a conditional finite Fejer criterion for the decimal orbit of pi

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

For `n >= 1`, this file fixes `M = 10^n` and `H = M / 2`.  The kernel used
below is the normalized Fejer kernel of order `H - 1`, so its signed Fourier
weights are exactly `1 - |h| / H` for `|h| < H`.  The zero frequency is
included.  All claims about cancellation in the fixed pi orbit are confined
to the explicit unproved hypothesis `PiFejerSpectralHypothesis`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace DecimalFactorComplexity.FejerSpectralCriterion

open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.WeightedFourierReduction
open Theory.PiDigits.BoundaryRobustFejerDichotomy

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- The ordinary exponential sum of the fractional decimal orbit
`x_j = fract (10^j * pi)`. -/
def piOrbitSum (h : ℤ) (M : ℕ) : ℂ :=
  ∑ j : Fin M, phase h (piDecimalShiftOrbit j)

/-- Signed Fejer frequencies `|h| < H`, including zero. -/
def fejerFrequencies (H : ℕ) : Finset ℤ :=
  Theory.PiDigits.BoundaryRobustFejerDichotomy.signedFrequenciesZero (H - 1)

/-- For positive `H`, membership is exactly the strict cutoff `|h| < H`. -/
@[simp] theorem mem_fejerFrequencies_iff {H : ℕ} {h : ℤ} (hH : 1 ≤ H) :
    h ∈ fejerFrequencies H ↔ h.natAbs < H := by
  rw [fejerFrequencies, mem_signedFrequenciesZero]
  omega

/-- The exact triangular Fejer weight `1 - |h| / H`. -/
def fejerWeight (H : ℕ) (h : ℤ) : ℝ :=
  1 - (h.natAbs : ℝ) / (H : ℝ)

/-- The finite weighted energy of the ordinary orbit sums.  The frequency
set, every weight, and the zero mode are visible in this definition. -/
def piFejerEnergy (H M : ℕ) : ℝ :=
  ∑ h ∈ fejerFrequencies H,
    fejerWeight H h * ‖piOrbitSum h M‖ ^ 2

/-- For positive `H`, the imported order-`H-1` triangular coefficient is
exactly the weight used in `piFejerEnergy`. -/
theorem triangularCoefficient_pred_eq_fejerWeight
    (H : ℕ) (h : ℤ) (hH : 1 ≤ H) :
    Theory.PiDigits.BoundaryRobustFejerDichotomy.triangularCoefficient
        (H - 1) h = fejerWeight H h := by
  unfold Theory.PiDigits.BoundaryRobustFejerDichotomy.triangularCoefficient
    fejerWeight
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hH
  rw [hcast]

/-- The natural-number identity making the agenda's `H = M/2` explicit. -/
theorem two_mul_half_ten_pow (n : ℕ) (hn : 1 ≤ n) :
    2 * (10 ^ n / 2) = 10 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k, pow_succ]
  omega

/-- A strict circular cutoff at radius `1/(2H)` lies in the central interval
where the order-`H-1` Fejer kernel is at least `4H/pi^2`. -/
theorem fejerKernel_pred_lower_of_circleDistance_lt
    (H : ℕ) (hH : 1 ≤ H) (x : ℝ)
    (hx : circleDistance x < (2 * (H : ℝ))⁻¹) :
    4 * (H : ℝ) / Real.pi ^ 2 ≤ fejerKernel (H - 1) x := by
  obtain ⟨z, hz⟩ := exists_int_abs_sub_lt_of_circleDistance_lt hx
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hH
  have hradius :
      fejerRadius (H - 1) =
        (2 * (H : ℝ))⁻¹ := by
    unfold fejerRadius
    rw [hcast]
  have hcentral :
      |x - (z : ℝ)| ≤
        fejerRadius (H - 1) := by
    rw [hradius]
    exact hz.le
  have hk := fejerKernel_lower_on_centralInterval
    (H - 1) (x - (z : ℝ)) hcentral
  have hshift : fejerKernel (H - 1) (x - (z : ℝ)) =
      fejerKernel (H - 1) x := by
    have hp := fejerKernel_int_shift (H - 1) z (x - (z : ℝ))
    simpa only [sub_add_cancel] using hp.symm
  rw [hcast] at hk
  exact hk.trans_eq hshift

/-- Exact finite Fejer expansion after summing over all ordered orbit pairs. -/
theorem orderedPair_fejerKernel_eq_piFejerEnergy
    (H M : ℕ) (hH : 1 ≤ H) :
    (∑ ij : Fin M × Fin M,
        fejerKernel (H - 1)
          (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1)) =
      piFejerEnergy H M := by
  classical
  have hexpand (x : ℝ) :
      (fejerKernel (H - 1) x : ℂ) =
        ∑ h ∈ fejerFrequencies H,
          (fejerWeight H h : ℂ) * phase h x := by
    rw [fejerKernel_eq_aggregated]
    apply sum_congr rfl
    intro h hh
    rw [triangularCoefficient_pred_eq_fejerWeight H h hH]
  have hcomplex :
      ((∑ ij : Fin M × Fin M,
          fejerKernel (H - 1)
            (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) : ℝ) : ℂ) =
        (piFejerEnergy H M : ℂ) := by
    push_cast
    simp_rw [hexpand]
    rw [sum_comm]
    simp_rw [← Finset.mul_sum]
    unfold piFejerEnergy
    push_cast
    apply sum_congr rfl
    intro h hh
    rw [orderedPair_phase_identity
      (fun i : Fin M => piDecimalShiftOrbit i) h]
    unfold piOrbitSum
    push_cast
    rfl
  exact_mod_cast hcomplex

/-- Pointwise lower bound for every pair in T2's strict near-return set at
the agenda's exact parameters `M = 10^n` and `H = M/2`. -/
theorem piNearReturn_fejerKernel_lower
    (n : ℕ) (hn : 1 ≤ n) (ij : Fin (10 ^ n) × Fin (10 ^ n))
    (hnear : circleDistance
        (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
          ((10 : ℝ) ^ n)⁻¹) :
    2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2 ≤
      fejerKernel (10 ^ n / 2 - 1)
        (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) := by
  have hdouble : 2 * (10 ^ n / 2) = 10 ^ n :=
    two_mul_half_ten_pow n hn
  have hpowpos : 0 < 10 ^ n := pow_pos (by norm_num) n
  have hH : 1 ≤ 10 ^ n / 2 := by omega
  have hdoubleCast :
      2 * ((10 ^ n / 2 : ℕ) : ℝ) = ((10 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hdouble
  have hdoubleReal :
      2 * ((10 ^ n / 2 : ℕ) : ℝ) = (10 : ℝ) ^ n := by
    simpa using hdoubleCast
  have horbit :
      circleDistance
          (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
        (2 * ((10 ^ n / 2 : ℕ) : ℝ))⁻¹ := by
    rw [hdoubleReal, circleDistance_piShift_sub_eq_powerDifference]
    exact hnear
  have hk := fejerKernel_pred_lower_of_circleDistance_lt
    (10 ^ n / 2) hH
    (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) horbit
  calc
    2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2 =
        4 * ((10 ^ n / 2 : ℕ) : ℝ) / Real.pi ^ 2 := by
      rw [← hdoubleCast]
      ring
    _ ≤ fejerKernel (10 ^ n / 2 - 1)
        (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) := hk

/-- The explicit finite Fourier transfer requested in T7.  It exposes
`M = 10^n`, `H = M/2`, the strict cutoff through `Q_pi`, and
`C_0 = pi^2/2`. -/
theorem Q_pi_pow_ten_le_fejerEnergy
    (n : ℕ) (hn : 1 ≤ n) :
    (Q_pi n (10 ^ n) : ℝ) ≤
      (Real.pi ^ 2 / 2) * (((10 ^ n : ℕ) : ℝ)⁻¹) *
        piFejerEnergy (10 ^ n / 2) (10 ^ n) := by
  classical
  have hdouble := two_mul_half_ten_pow n hn
  have hpowpos : 0 < 10 ^ n := pow_pos (by norm_num) n
  have hH : 1 ≤ 10 ^ n / 2 := by omega
  have hcard :
      (Q_pi n (10 ^ n) : ℝ) =
        ∑ ij : Fin (10 ^ n) × Fin (10 ^ n),
          if circleDistance
              (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
                ((10 : ℝ) ^ n)⁻¹ then 1 else 0 := by
    unfold Q_pi piNearReturnPairs
    norm_cast
    simp
  have hsum :
      (2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2) *
          (Q_pi n (10 ^ n) : ℝ) ≤
        ∑ ij : Fin (10 ^ n) × Fin (10 ^ n),
          fejerKernel (10 ^ n / 2 - 1)
            (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) := by
    rw [hcard, Finset.mul_sum]
    apply sum_le_sum
    intro ij hij
    split_ifs with hnear
    · simpa only [mul_one] using
        piNearReturn_fejerKernel_lower n hn ij hnear
    · simp only [mul_zero]
      exact Theory.PiDigits.T27.fejerKernel_nonneg _ _
  rw [orderedPair_fejerKernel_eq_piFejerEnergy
    (10 ^ n / 2) (10 ^ n) hH] at hsum
  have hMpos : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by
    exact_mod_cast hpowpos
  have hscale : 0 < 2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2 := by
    positivity
  have hdiv :
      (Q_pi n (10 ^ n) : ℝ) ≤
        piFejerEnergy (10 ^ n / 2) (10 ^ n) /
          (2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2) := by
    apply (le_div_iff₀ hscale).2
    simpa [mul_comm] using hsum
  calc
    (Q_pi n (10 ^ n) : ℝ) ≤
        piFejerEnergy (10 ^ n / 2) (10 ^ n) /
          (2 * ((10 ^ n : ℕ) : ℝ) / Real.pi ^ 2) := hdiv
    _ = (Real.pi ^ 2 / 2) * (((10 ^ n : ℕ) : ℝ)⁻¹) *
        piFejerEnergy (10 ^ n / 2) (10 ^ n) := by
      field_simp [hMpos.ne', Real.pi_ne_zero]

/-- The spectral statement left unproved for pi: one fixed positive constant
controls the complete weighted energy at `M = 10^n`, `H = M/2`, for every
sufficiently large `n`. -/
def PiFejerSpectralHypothesis : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n →
      piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
        C * ((10 ^ n : ℕ) : ℝ) ^ 2

/-- The named statement exposes every quantifier in the unproved spectral
hypothesis. -/
theorem piFejerSpectralHypothesis_iff_quantifiers :
    PiFejerSpectralHypothesis ↔
      ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n →
          piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
            C * ((10 ^ n : ℕ) : ℝ) ^ 2 :=
  Iff.rfl

/-- A finite energy estimate gives the corresponding explicit linear bound
for the ordered near-return count. -/
theorem Q_pi_pow_ten_le_linear_of_energy_bound
    (C : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (henergy : piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
      C * ((10 ^ n : ℕ) : ℝ) ^ 2) :
    (Q_pi n (10 ^ n) : ℝ) ≤
      (Real.pi ^ 2 / 2 * C) * ((10 ^ n : ℕ) : ℝ) := by
  have hfourier := Q_pi_pow_ten_le_fejerEnergy n hn
  have hMpos : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by positivity
  calc
    (Q_pi n (10 ^ n) : ℝ) ≤
        (Real.pi ^ 2 / 2) * (((10 ^ n : ℕ) : ℝ)⁻¹) *
          piFejerEnergy (10 ^ n / 2) (10 ^ n) := hfourier
    _ ≤ (Real.pi ^ 2 / 2) * (((10 ^ n : ℕ) : ℝ)⁻¹) *
          (C * ((10 ^ n : ℕ) : ℝ) ^ 2) := by
      gcongr
    _ = (Real.pi ^ 2 / 2 * C) * ((10 ^ n : ℕ) : ℝ) := by
      field_simp [hMpos.ne']

/-- Any fixed real constant is eventually bounded by `10^(n/2)`. -/
theorem eventually_constant_le_ten_rpow_half (K : ℝ) :
    ∃ n1 : ℕ, 1 ≤ n1 ∧ ∀ n : ℕ, n1 ≤ n →
      K ≤ (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
  let b : ℝ := (10 : ℝ) ^ (1 / 2 : ℝ)
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have ht : Filter.Tendsto (fun n : ℕ => b ^ n)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hev : ∀ᶠ n : ℕ in Filter.atTop, K < b ^ n :=
    ht.eventually_gt_atTop K
  rw [Filter.eventually_atTop] at hev
  obtain ⟨m, hm⟩ := hev
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hmn : m ≤ n := (le_max_right 1 m).trans hn
  calc
    K ≤ b ^ n := (hm n hmn).le
    _ = (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
      dsimp [b]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]

/-- The full quantitative conditional transfer.  The theorem displays the
fixed exponent `eta = 1/2`, the sample size `M = 10^n`, and all eventual
quantifiers before packaging the result as C2. -/
theorem piFejerSpectralHypothesis_implies_explicit_collision_bound
    (hspectral : PiFejerSpectralHypothesis) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ ∀ n : ℕ, nstar ≤ n →
      (E_pi n (10 ^ n) : ℝ) ≤
        ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  obtain ⟨C, hC, n0, hn0, henergy⟩ := hspectral
  obtain ⟨n1, hn1, hgrowth⟩ :=
    eventually_constant_le_ten_rpow_half (Real.pi ^ 2 / 2 * C)
  refine ⟨max n0 n1, hn0.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn0' : n0 ≤ n := (le_max_left n0 n1).trans hn
  have hn1' : n1 ≤ n := (le_max_right n0 n1).trans hn
  have hnpos : 1 ≤ n := hn0.trans hn0'
  have hQ := Q_pi_pow_ten_le_linear_of_energy_bound
    C n hnpos (henergy n hn0')
  have hcollisionNat := pi_collisionEnergy_le_Q_pi n (10 ^ n)
  have hcollision :
      (E_pi n (10 ^ n) : ℝ) ≤ (Q_pi n (10 ^ n) : ℝ) := by
    exact_mod_cast hcollisionNat
  have hconstant := hgrowth n hn1'
  have hMnonneg : (0 : ℝ) ≤ ((10 ^ n : ℕ) : ℝ) := by positivity
  have hlinear :
      (Real.pi ^ 2 / 2 * C) * ((10 ^ n : ℕ) : ℝ) ≤
        ((10 ^ n : ℕ) : ℝ) *
          (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hconstant hMnonneg
  have hpowCast :
      ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have htarget :
      ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) =
        ((10 ^ n : ℕ) : ℝ) *
          (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
    calc
      ((10 ^ n : ℕ) : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) =
          (((10 : ℝ) ^ (n : ℝ)) * (10 : ℝ) ^ (n : ℝ)) *
            (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
              rw [hpowCast, pow_two]
      _ = (10 : ℝ) ^ ((n : ℝ) + (n : ℝ)) *
            (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
      _ = (10 : ℝ) ^
            (((n : ℝ) + (n : ℝ)) + (-(1 / 2 : ℝ) * (n : ℝ))) := by
              rw [← Real.rpow_add (by norm_num)]
      _ = (10 : ℝ) ^ ((n : ℝ) + (1 / 2 : ℝ) * (n : ℝ)) := by
              congr 1
              ring
      _ = (10 : ℝ) ^ (n : ℝ) *
            (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
      _ = ((10 ^ n : ℕ) : ℝ) *
            (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
              rw [hpowCast]
  calc
    (E_pi n (10 ^ n) : ℝ) ≤ (Q_pi n (10 ^ n) : ℝ) := hcollision
    _ ≤ (Real.pi ^ 2 / 2 * C) * ((10 ^ n : ℕ) : ℝ) := hQ
    _ ≤ ((10 ^ n : ℕ) : ℝ) *
        (10 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)) := hlinear
    _ = ((10 ^ n : ℕ) : ℝ) ^ 2 *
        (10 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := htarget.symm

/-- The explicit unproved spectral hypothesis supplies T2's collision C2
with exponent `eta = 1/2` and witness `M = 10^n`. -/
theorem piFejerSpectralHypothesis_implies_C2
    (hspectral : PiFejerSpectralHypothesis) :
    PiExponentialCollisionC2 := by
  obtain ⟨nstar, hnstar, hbound⟩ :=
    piFejerSpectralHypothesis_implies_explicit_collision_bound hspectral
  refine ⟨(1 / 2 : ℝ), by norm_num, nstar, hnstar, ?_⟩
  intro n hn
  exact ⟨10 ^ n, one_le_pow₀ (by norm_num), hbound n hn⟩

/-- Canonical C1 follows only from the displayed spectral hypothesis, via the
accepted T2 implication `PiExponentialCollisionC2 -> C1`. -/
theorem piFejerSpectralHypothesis_implies_C1
    (hspectral : PiFejerSpectralHypothesis) :
    PiPositiveFactorEntropyC1 := by
  exact piExponentialCollisionC2_implies_C1
    (piFejerSpectralHypothesis_implies_C2 hspectral)

end DecimalFactorComplexity.FejerSpectralCriterion

#print axioms DecimalFactorComplexity.FejerSpectralCriterion.mem_fejerFrequencies_iff
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.triangularCoefficient_pred_eq_fejerWeight
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.two_mul_half_ten_pow
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.fejerKernel_pred_lower_of_circleDistance_lt
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.orderedPair_fejerKernel_eq_piFejerEnergy
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.piNearReturn_fejerKernel_lower
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.Q_pi_pow_ten_le_fejerEnergy
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.piFejerSpectralHypothesis_iff_quantifiers
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.Q_pi_pow_ten_le_linear_of_energy_bound
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.eventually_constant_le_ten_rpow_half
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.piFejerSpectralHypothesis_implies_explicit_collision_bound
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.piFejerSpectralHypothesis_implies_C2
#print axioms DecimalFactorComplexity.FejerSpectralCriterion.piFejerSpectralHypothesis_implies_C1
