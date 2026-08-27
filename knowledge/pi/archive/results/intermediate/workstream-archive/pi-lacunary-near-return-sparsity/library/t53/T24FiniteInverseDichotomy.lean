import TheoryLib.PiLacunaryNearReturnSparsity.T13IteratedLagResonance

/-!
# T24: finite inverse dichotomy for base-ten resonances

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves a finite cycle-or-positive-preperiod inverse theorem and
applies it separately to every depth supplied by T13.  The final theorem is
only a necessary consequence of the literal negation of canonical A1.  It
asserts no compatibility between witnesses at different depths, no uniform
preperiod bound, no proof of A1, and no irrationality contradiction.
-/

noncomputable section

open Finset
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity
namespace FiniteInverseDichotomy

open IteratedLagResonance

/-- The phase error obtained from a correlation whose real part exceeds
`tau`. -/
def inverseError (tau : ℝ) : ℝ := Real.arccos tau / (2 * Real.pi)

/-- The literal denominator of a base-ten eventually periodic approximation.
The case `j = 0` is a pure cycle; `j > 0` has positive preperiod. -/
def decimalEventuallyPeriodicDenominator (j s : ℕ) : ℝ :=
  (10 : ℝ) ^ j * ((10 : ℝ) ^ s - 1)

/-- Approximation at explicit preperiod `j`, period `s`, and error `tau`. -/
def EventuallyPeriodicApproximation
    (beta tau : ℝ) (j s : ℕ) : Prop :=
  ∃ a : ℤ,
    |beta - (a : ℝ) / decimalEventuallyPeriodicDenominator j s| <
      inverseError tau / decimalEventuallyPeriodicDenominator j s

/-- A pure-cycle approximation with period strictly below `M`. -/
def CycleApproximation (beta tau : ℝ) (M : ℕ) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ s < M ∧ EventuallyPeriodicApproximation beta tau 0 s

/-- A positive-preperiod approximation whose preperiod plus period is below
`M`. -/
def PositivePreperiodApproximation (beta tau : ℝ) (M : ℕ) : Prop :=
  ∃ j s : ℕ, 1 ≤ j ∧ 1 ≤ s ∧ j + s < M ∧
    EventuallyPeriodicApproximation beta tau j s

/-- Nearest-integer inversion of a cosine inequality, with every constant
displayed. -/
lemma cosine_gt_implies_near_integer (x tau : ℝ)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hcos : Real.cos (2 * Real.pi * x) > tau) :
    ∃ a : ℤ, |x - a| < inverseError tau := by
  let a : ℤ := round x
  refine ⟨a, ?_⟩
  have hdist : |x - (a : ℝ)| ≤ 1 / 2 := by
    simpa [a] using (abs_sub_round x)
  have htheta_le_pi :
      (2 * Real.pi) * |x - (a : ℝ)| ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcos_eq :
      Real.cos ((2 * Real.pi) * |x - (a : ℝ)|) =
        Real.cos (2 * Real.pi * x) := by
    calc
      Real.cos ((2 * Real.pi) * |x - (a : ℝ)|) =
          Real.cos |(2 * Real.pi) * (x - (a : ℝ))| := by
            rw [abs_mul, abs_of_pos Real.two_pi_pos]
      _ = Real.cos ((2 * Real.pi) * (x - (a : ℝ))) := Real.cos_abs _
      _ = Real.cos (2 * Real.pi * x - (a : ℝ) * (2 * Real.pi)) := by
        congr 1
        ring
      _ = Real.cos (2 * Real.pi * x) :=
        Real.cos_sub_int_mul_two_pi _ a
  have htheta_lt :
      (2 * Real.pi) * |x - (a : ℝ)| < Real.arccos tau := by
    by_contra hnot
    have harc_le_theta :
        Real.arccos tau ≤ (2 * Real.pi) * |x - (a : ℝ)| :=
      le_of_not_gt hnot
    have hle :
        Real.cos ((2 * Real.pi) * |x - (a : ℝ)|) ≤
          Real.cos (Real.arccos tau) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (Real.arccos_nonneg tau) htheta_le_pi harc_le_theta
    rw [Real.cos_arccos (by linarith) htau1.le, hcos_eq] at hle
    exact (not_lt_of_ge hle) hcos
  exact (lt_div_iff₀ Real.two_pi_pos).2
    (by simpa [inverseError, mul_comm] using htheta_lt)

/-- A large unit-modulus sum satisfying the displayed energy inequality has
two positively separated terms with correlation real part greater than
`tau`. -/
theorem large_sum_has_correlated_pair
    (z : ℕ → ℂ) (M : ℕ) (delta tau : ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hdelta : 0 < delta) (htau : 0 ≤ tau)
    (henergy : (M : ℝ) + 2 * tau * (M : ℝ) ^ 2 ≤
      (delta * (M : ℝ)) ^ 2)
    (hlarge : delta * (M : ℝ) < ‖∑ j ∈ range M, z j‖) :
    ∃ j s : ℕ, 1 ≤ s ∧ j + s < M ∧
      tau < (z (j + s) * conj (z j)).re := by
  classical
  by_contra hnone
  push Not at hnone
  have hcorr (s : ℕ) (hs : s ∈ Icc 1 (M - 1)) :
      (autocorrelation z M s).re ≤ ((M - s : ℕ) : ℝ) * tau := by
    rw [autocorrelation]
    calc
      (∑ j ∈ range (M - s), z (j + s) * conj (z j)).re =
          ∑ j ∈ range (M - s), (z (j + s) * conj (z j)).re := by
        simp
      _ ≤ ∑ _j ∈ range (M - s), tau := by
        apply sum_le_sum
        intro j hj
        apply hnone j s (mem_Icc.mp hs).1
        simp only [mem_range] at hj
        have hsle : s ≤ M - 1 := (mem_Icc.mp hs).2
        omega
      _ = ((M - s : ℕ) : ℝ) * tau := by simp
  have hsum :
      ∑ s ∈ Icc 1 (M - 1), (autocorrelation z M s).re ≤
        tau * (M : ℝ) ^ 2 := by
    calc
      ∑ s ∈ Icc 1 (M - 1), (autocorrelation z M s).re ≤
          ∑ s ∈ Icc 1 (M - 1), ((M - s : ℕ) : ℝ) * tau := by
        exact sum_le_sum fun s hs => hcorr s hs
      _ = tau * ∑ s ∈ Icc 1 (M - 1), ((M - s : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro s _hs
        ring
      _ ≤ tau * (M : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (LagDiscrepancy.lagLengthSum_le_sq M) htau
  have hupper :
      ‖∑ j ∈ range M, z j‖ ^ 2 ≤
        (M : ℝ) + 2 * tau * (M : ℝ) ^ 2 := by
    rw [norm_sum_sq_eq_autocorrelation z M hz]
    nlinarith
  have hlower :
      (delta * (M : ℝ)) ^ 2 < ‖∑ j ∈ range M, z j‖ ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg hdelta.le (Nat.cast_nonneg M))
      (norm_nonneg _)).2 hlarge
  exact (not_lt_of_ge (hupper.trans henergy)) hlower

/-- Correlation of two base-ten geometric phases is the cosine at their
eventually periodic denominator. -/
lemma geometricPhase_correlation_re (beta : ℝ) (j s : ℕ) :
    (geometricPhase beta (j + s) * conj (geometricPhase beta j)).re =
      Real.cos
        (2 * Real.pi *
          (decimalEventuallyPeriodicDenominator j s * beta)) := by
  rw [geometricPhase_difference]
  unfold geometricPhase decimalEventuallyPeriodicDenominator
  rw [show
      2 * (Real.pi : ℂ) * Complex.I *
          ((((10 : ℝ) ^ j *
            (beta * ((10 : ℝ) ^ s - 1)) : ℝ) : ℂ)) =
        (((2 * Real.pi *
          ((10 : ℝ) ^ j * ((10 : ℝ) ^ s - 1) * beta) : ℝ) : ℂ) *
            Complex.I) by
      push_cast
      ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- A correlated phase pair gives the stated rational approximation. -/
lemma correlated_pair_implies_approximation
    (beta tau : ℝ) (j s : ℕ)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1) (hs : 1 ≤ s)
    (hcorr : tau <
      (geometricPhase beta (j + s) * conj (geometricPhase beta j)).re) :
    EventuallyPeriodicApproximation beta tau j s := by
  have hcos :
      tau < Real.cos
        (2 * Real.pi *
          (decimalEventuallyPeriodicDenominator j s * beta)) := by
    rwa [geometricPhase_correlation_re] at hcorr
  obtain ⟨a, ha⟩ := cosine_gt_implies_near_integer
    (decimalEventuallyPeriodicDenominator j s * beta) tau
      htau0 htau1 hcos
  refine ⟨a, ?_⟩
  have hspos : 0 < s := by omega
  have hpow : (1 : ℝ) < (10 : ℝ) ^ s :=
    one_lt_pow₀ (by norm_num) hspos.ne'
  have hdenom : 0 < decimalEventuallyPeriodicDenominator j s := by
    unfold decimalEventuallyPeriodicDenominator
    positivity
  have hrearrange :
      beta - (a : ℝ) / decimalEventuallyPeriodicDenominator j s =
        (decimalEventuallyPeriodicDenominator j s * beta - (a : ℝ)) /
          decimalEventuallyPeriodicDenominator j s := by
    field_simp
  rw [hrearrange, abs_div, abs_of_pos hdenom]
  exact (div_lt_div_iff_of_pos_right hdenom).2 ha

/-- Self-contained finite inverse dichotomy.  The second alternative includes
the negation of the first, so the two branches are disjoint. -/
theorem finite_cycle_or_positivePreperiod_inverse
    (beta delta tau : ℝ) (M : ℕ)
    (htauPos : 0 < tau) (htauDelta : tau < delta)
    (hdeltaOne : delta ≤ 1)
    (henergy : (M : ℝ) + 2 * tau * (M : ℝ) ^ 2 ≤
      (delta * (M : ℝ)) ^ 2)
    (hlarge : delta * (M : ℝ) <
      ‖∑ j ∈ range M, geometricPhase beta j‖) :
    CycleApproximation beta tau M ∨
      (¬ CycleApproximation beta tau M ∧
        PositivePreperiodApproximation beta tau M) := by
  have hdelta : 0 < delta := htauPos.trans htauDelta
  have htau0 : 0 ≤ tau := htauPos.le
  have htau1 : tau < 1 := htauDelta.trans_le hdeltaOne
  have hz : ∀ j, ‖geometricPhase beta j‖ = 1 := by
    intro j
    simpa [geometricPhase, Theory.PiDigits.T27.phase] using
      Theory.PiDigits.T27.norm_phase (1 : ℤ) ((10 : ℝ) ^ j * beta)
  obtain ⟨j, s, hs, hjs, hcorr⟩ :=
    large_sum_has_correlated_pair (geometricPhase beta) M delta tau
      hz hdelta htau0 henergy hlarge
  have happ : EventuallyPeriodicApproximation beta tau j s :=
    correlated_pair_implies_approximation beta tau j s
      htau0 htau1 hs hcorr
  by_cases hcycle : CycleApproximation beta tau M
  · exact Or.inl hcycle
  · refine Or.inr ⟨hcycle, ?_⟩
    have hj : 1 ≤ j := by
      by_contra hjnot
      have hjzero : j = 0 := by omega
      apply hcycle
      refine ⟨s, hs, ?_, ?_⟩
      · simpa [hjzero] using hjs
      · simpa [hjzero] using happ
    exact ⟨j, s, hj, hs, hjs, happ⟩

/-- T13's density denominator at one specified depth. -/
def stageDensityDenominator (A n d : ℕ) : ℕ :=
  densityDenominator (131072 * A ^ 2 * n ^ 2) d

/-- The normalized resonance density supplied by T13 at one depth. -/
def stageDelta (A n d : ℕ) : ℝ :=
  (stageDensityDenominator A n d : ℝ)⁻¹

/-- Correlation threshold used by the finite inverse theorem. -/
def stageTau (A n d : ℕ) : ℝ :=
  1 / (8 * (stageDensityDenominator A n d : ℝ) ^ 2)

/-- Explicit residual length requested from T13 at one depth. -/
def stageLengthRequest (A n d : ℕ) : ℕ :=
  2 * stageDensityDenominator A n d ^ 2

/-- The real coefficient of the geometric phase at one T13 depth. -/
def stageCoefficient {d : ℕ} (h r : ℕ) (shifts : Fin d → ℕ) : ℝ :=
  (h : ℝ) * ((10 : ℝ) ^ r - 1) *
    (∏ t, ((10 : ℝ) ^ shifts t - 1)) * Real.pi

lemma densityDenominator_pos (D d : ℕ) (hD : 1 ≤ D) :
    1 ≤ densityDenominator D d := by
  induction d generalizing D with
  | zero => simpa [densityDenominator] using hD
  | succ d ih =>
      simpa [densityDenominator] using
        ih (nextDensityDenominator D) (nextDensityDenominator_pos D hD)

lemma stageDensityDenominator_pos (A n d : ℕ)
    (hA : 1 ≤ A) (hn : 1 ≤ n) :
    1 ≤ stageDensityDenominator A n d := by
  apply densityDenominator_pos
  have hpos : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
  omega

/-- The choice `M ≥ 2D²`, `delta = 1/D`, and `tau = 1/(8D²)`
satisfies the explicit energy hypothesis of the finite inverse theorem. -/
lemma stage_energy_inequality (D M : ℕ)
    (hD : 1 ≤ D) (hM : 2 * D ^ 2 ≤ M) :
    (M : ℝ) + 2 * (1 / (8 * (D : ℝ) ^ 2)) * (M : ℝ) ^ 2 ≤
      (((D : ℝ)⁻¹) * (M : ℝ)) ^ 2 := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hMreal : 2 * (D : ℝ) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hM
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  field_simp
  nlinarith

/-- Necessary-only, stagewise T13 specialization.  For each depth `d`, all
witnesses are selected anew.  In particular this statement provides no
compatibility between depths and no depth-independent preperiod bound. -/
theorem literal_not_A1_implies_stagewise_inverse_necessaryOnly
    (hnotA1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ d : ℕ,
        ∃ N r h : ℕ, ∃ shifts : Fin d → ℕ,
          let D := stageDensityDenominator A n d
          let K := stageLengthRequest A n d
          let M := N - r - ∑ t, shifts t
          let beta := stageCoefficient h r shifts
          N = 16 * A * n *
              iterationLengthThresholdAux
                (131072 * A ^ 2 * n ^ 2) 1 K 1 d ∧
          r ∈ Icc 1 (N - 1) ∧
          h ∈ Icc 1 (256 * A * n) ∧
          Function.Injective shifts ∧
          (∀ t, 1 ≤ shifts t) ∧
          (∀ t, shifts t ≠ r) ∧
          1 ≤ D ∧
          K ≤ M ∧
          2 ≤ M ∧
          0 < stageDelta A n d ∧
          0 < stageTau A n d ∧
          stageTau A n d < stageDelta A n d ∧
          stageDelta A n d ≤ 1 ∧
          stageTau A n d < 1 ∧
          stageDelta A n d * (M : ℝ) <
            ‖∑ j ∈ range M, geometricPhase beta j‖ ∧
          (CycleApproximation beta (stageTau A n d) M ∨
            (¬ CycleApproximation beta (stageTau A n d) M ∧
              PositivePreperiodApproximation
                beta (stageTau A n d) M)) := by
  obtain ⟨A, hA, hmain⟩ :=
    literal_not_A1_implies_arbitrary_depth_resonance hnotA1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hmainn⟩ := hmain n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro d
  let D : ℕ := stageDensityDenominator A n d
  have hD : 1 ≤ D := stageDensityDenominator_pos A n d hA hn
  let K : ℕ := stageLengthRequest A n d
  have hK : 1 ≤ K := by
    have hKpos : 0 < K := by
      dsimp [K, stageLengthRequest]
      positivity
    omega
  obtain ⟨N, r, h, shifts, hN, hr, hh, hinjective, hpositive,
      havoids, hresidual, hresonance⟩ := hmainn d K hK
  let M : ℕ := N - r - ∑ t, shifts t
  let beta : ℝ := stageCoefficient h r shifts
  have hKM : K ≤ M := by simpa [M] using hresidual
  have hDreal : 0 < (D : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hdelta : 0 < stageDelta A n d := by
    simpa [stageDelta, D] using inv_pos.mpr hDreal
  have htauPos : 0 < stageTau A n d := by
    unfold stageTau
    positivity
  have hDsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hdenomLarge : (1 : ℝ) < 8 * (D : ℝ) ^ 2 := by nlinarith
  have htau1 : stageTau A n d < 1 := by
    rw [stageTau]
    exact (div_lt_one (by positivity)).2 hdenomLarge
  have htauDelta : stageTau A n d < stageDelta A n d := by
    have hlocal : 1 / (8 * (D : ℝ) ^ 2) < 1 / (D : ℝ) := by
      apply one_div_lt_one_div_of_lt hDreal
      nlinarith
    simpa [stageTau, stageDelta, D, one_div] using hlocal
  have hdeltaOne : stageDelta A n d ≤ 1 := by
    rw [stageDelta]
    simpa [D, one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hDone)
  have hMrequest : 2 * D ^ 2 ≤ M := by
    simpa [K, stageLengthRequest, D] using hKM
  have hMtwo : 2 ≤ M := by
    have hDsqNat : 1 ≤ D ^ 2 := by nlinarith
    omega
  have henergy :
      (M : ℝ) + 2 * stageTau A n d * (M : ℝ) ^ 2 ≤
        (stageDelta A n d * (M : ℝ)) ^ 2 := by
    simpa [stageTau, stageDelta, D] using
      stage_energy_inequality D M hD hMrequest
  have hlarge :
      stageDelta A n d * (M : ℝ) <
        ‖∑ j ∈ range M, geometricPhase beta j‖ := by
    have hresonance' :
        (M : ℝ) / (D : ℝ) <
          ‖∑ j ∈ range M, geometricPhase beta j‖ := by
      simpa only [iteratedResonanceSum, M, D, stageDensityDenominator,
        beta, stageCoefficient] using hresonance
    simpa [stageDelta, D, div_eq_mul_inv, mul_comm] using hresonance'
  have hdichotomy :=
    finite_cycle_or_positivePreperiod_inverse
      beta (stageDelta A n d) (stageTau A n d) M
      htauPos htauDelta hdeltaOne henergy hlarge
  refine ⟨N, r, h, shifts, ?_⟩
  dsimp only
  refine ⟨?_, hr, hh, hinjective, hpositive, havoids, hD, ?_,
    hMtwo, hdelta, htauPos, htauDelta, hdeltaOne, htau1, ?_, hdichotomy⟩
  · simpa [K, stageLengthRequest] using hN
  · simpa [K, M] using hKM
  · simpa [M, beta] using hlarge

end FiniteInverseDichotomy
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.cosine_gt_implies_near_integer
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.large_sum_has_correlated_pair
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.geometricPhase_correlation_re
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.correlated_pair_implies_approximation
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.finite_cycle_or_positivePreperiod_inverse
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.stage_energy_inequality
#print axioms DecimalFactorComplexity.FiniteInverseDichotomy.literal_not_A1_implies_stagewise_inverse_necessaryOnly
