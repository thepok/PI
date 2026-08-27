import TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier
import TheoryLib.PiLacunaryNearReturnSparsity.T13IteratedLagResonance
import TheoryLib.PiDigits.T29FixedFrequencyResonance

/-!
# T13: finite autocorrelation amplification limits

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This module proves deterministic finite identities and consequences conditional
on the literal failure of canonical C1. It proves no unconditional assertion
about `Real.pi`, C1, or any additional coherence premise.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity.AutocorrelationAmplification

open DecimalFactorComplexity
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.IteratedLagResonance
open DecimalFactorComplexity.ScaleAdaptiveOrbitFourier

abbrev phase := Theory.PiDigits.T27.phase

/-- The phase sequence attached to an arbitrary real circle orbit. -/
def circleOrbitPhase (x : ℕ → ℝ) (h : ℤ) (j : ℕ) : ℂ := phase h (x j)

/-- Positive-lag correlation, with exactly `M-r` terms. -/
def circleOrbitCorrelation (x : ℕ → ℝ) (h : ℤ) (M r : ℕ) : ℂ :=
  autocorrelation (circleOrbitPhase x h) M r

/-- The integer frequency created by a base-ten lag `r`. -/
def decimalLagFrequency (h : ℤ) (r : ℕ) : ℤ := h * ((10 : ℤ) ^ r - 1)

/-- The `Fin M` sum in T10 is the same zero-based sum over `range M`. -/
theorem piOrbitSum_eq_circleOrbitPhase_sum (h : ℤ) (M : ℕ) :
    piOrbitSum h M =
      ∑ j ∈ range M, circleOrbitPhase
        DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h j := by
  simpa only [DecimalFactorComplexity.FejerSpectralCriterion.piOrbitSum,
    DecimalFactorComplexity.FejerSpectralCriterion.phase,
    circleOrbitPhase, AutocorrelationAmplification.phase] using
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => Theory.PiDigits.T27.phase h
          (DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit j)) M)

theorem phase_fract_eq_phase (h : ℤ) (x : ℝ) :
    Theory.PiDigits.T27.phase h (Int.fract x) =
      Theory.PiDigits.T27.phase h x := by
  simpa only [Theory.PiDigits.T27.phase] using
    (Theory.PiDigits.T29.phase_fract_eq_phase h x)

/-- Base-ten differencing multiplies the integer frequency by `10^r-1`. -/
theorem piOrbitPhase_mul_conj_eq_lagFrequency
    (h : ℤ) (j r : ℕ) :
    circleOrbitPhase
        DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h (j + r) *
        conj (circleOrbitPhase
          DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h j) =
      circleOrbitPhase
        DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit
          (decimalLagFrequency h r) j := by
  simp only [circleOrbitPhase,
    AutocorrelationAmplification.phase,
    DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit,
    Theory.PiDigits.T20.baseTenOrbit]
  rw [phase_fract_eq_phase, phase_fract_eq_phase, phase_fract_eq_phase]
  rw [← DecimalFactorComplexity.WeightedFourierReduction.phase_real_sub]
  unfold decimalLagFrequency
  change Theory.PiDigits.T27.phase h
      ((10 : ℝ) ^ (j + r) * Real.pi - (10 : ℝ) ^ j * Real.pi) =
    Theory.PiDigits.T27.phase (h * ((10 : ℤ) ^ r - 1))
      ((10 : ℝ) ^ j * Real.pi)
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  rw [pow_add]
  ring

/-- The lag correlation is exactly the ordinary orbit sum at the displayed
descendant frequency and displayed remaining length. -/
theorem pi_circleOrbitCorrelation_eq_piOrbitSum_lagFrequency
    (h : ℤ) (M r : ℕ) :
    circleOrbitCorrelation
        DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h M r =
      piOrbitSum (decimalLagFrequency h r) (M - r) := by
  rw [piOrbitSum_eq_circleOrbitPhase_sum]
  unfold circleOrbitCorrelation autocorrelation
  apply sum_congr rfl
  intro j hj
  exact piOrbitPhase_mul_conj_eq_lagFrequency h j r

/-- Exact autocorrelation identity for an arbitrary finite real circle orbit.
The `M` diagonal terms are explicit, and lag `r` has remaining length `M-r`. -/
theorem circleOrbit_autocorrelation_identity
    (x : ℕ → ℝ) (h : ℤ) (M : ℕ) :
    ‖∑ j ∈ range M, circleOrbitPhase x h j‖ ^ 2 =
      M + 2 * ∑ r ∈ Icc 1 (M - 1),
        (circleOrbitCorrelation x h M r).re := by
  apply norm_sum_sq_eq_autocorrelation
  intro j
  exact Theory.PiDigits.T27.norm_phase h (x j)

/-- Fully expanded identity: `M` diagonal terms, lags `1 ≤ r ≤ M-1`, and
the exact inner range `0 ≤ j < M-r` are all visible in the theorem type. -/
theorem circleOrbit_autocorrelation_identity_explicit
    (x : ℕ → ℝ) (h : ℤ) (M : ℕ) :
    ‖∑ j ∈ range M, phase h (x j)‖ ^ 2 =
      M + 2 * ∑ r ∈ Icc 1 (M - 1),
        (∑ j ∈ range (M - r),
          phase h (x (j + r)) * conj (phase h (x j))).re := by
  simpa only [circleOrbitPhase, circleOrbitCorrelation, autocorrelation] using
    circleOrbit_autocorrelation_identity x h M

/-- Every lag correlation is bounded by its displayed remaining length. -/
theorem norm_circleOrbitCorrelation_le_remainingLength
    (x : ℕ → ℝ) (h : ℤ) (M r : ℕ) :
    ‖circleOrbitCorrelation x h M r‖ ≤ (M - r : ℕ) := by
  apply norm_autocorrelation_le
  intro j
  exact Theory.PiDigits.T27.norm_phase h (x j)

/-- The discarded remaining lengths are exactly `1,...,L-1`. -/
theorem tail_remainingLength_sum (M L : ℕ) (hL : L ≤ M) :
    ∑ r ∈ Icc (M - L + 1) (M - 1), (M - r) = L * (L - 1) / 2 := by
  classical
  calc
    (∑ r ∈ Icc (M - L + 1) (M - 1), (M - r)) =
        ∑ r ∈ Icc (M - L + 1) M, (M - r) := by
      apply Finset.sum_subset
      · intro r hr
        simp only [mem_Icc] at hr ⊢
        omega
      · intro r hr hrold
        simp only [mem_Icc] at hr
        simp only [mem_Icc, not_and_or, not_le] at hrold
        have : r = M := by omega
        subst r
        simp
    _ = ∑ j ∈ range L, j := by
      apply Finset.sum_bij (fun r _ => M - r)
      · intro r hr
        simp only [mem_range, mem_Icc] at hr ⊢
        omega
      · intro a ha b hb hab
        simp only [mem_Icc] at ha hb
        omega
      · intro j hj
        simp only [mem_range] at hj
        refine ⟨M - j, ?_, ?_⟩
        · simp only [mem_Icc]
          omega
        · omega
      · intro r hr
        rfl
    _ = L * (L - 1) / 2 := Finset.sum_range_id L

/-- The tail consisting of correlations with remaining length below `L` has
the exact triangular trivial upper bound `L*(L-1)/2`. -/
theorem tail_circleOrbitCorrelation_re_le
    (x : ℕ → ℝ) (h : ℤ) (M L : ℕ) (hL : L ≤ M) :
    ∑ r ∈ Icc (M - L + 1) (M - 1),
        (circleOrbitCorrelation x h M r).re ≤
      (L * (L - 1) / 2 : ℕ) := by
  calc
    (∑ r ∈ Icc (M - L + 1) (M - 1),
        (circleOrbitCorrelation x h M r).re) ≤
        ∑ r ∈ Icc (M - L + 1) (M - 1), ((M - r : ℕ) : ℝ) := by
      apply sum_le_sum
      intro r hr
      exact (Complex.re_le_norm _).trans
        (norm_circleOrbitCorrelation_le_remainingLength x h M r)
    _ = ((∑ r ∈ Icc (M - L + 1) (M - 1), (M - r)) : ℕ) := by
      simp
    _ = (L * (L - 1) / 2 : ℕ) := by rw [tail_remainingLength_sum M L hL]

/-- Split all positive lags according to whether at least `L` terms remain. -/
theorem full_lag_sum_eq_retained_add_tail
    (x : ℕ → ℝ) (h : ℤ) (M L : ℕ) (hL : 1 ≤ L) (hLM : L < M) :
    (∑ r ∈ Icc 1 (M - 1), (circleOrbitCorrelation x h M r).re) =
      (∑ r ∈ Icc 1 (M - L), (circleOrbitCorrelation x h M r).re) +
      ∑ r ∈ Icc (M - L + 1) (M - 1),
        (circleOrbitCorrelation x h M r).re := by
  let A : Finset ℕ := Icc 1 (M - L)
  let T : Finset ℕ := Icc (M - L + 1) (M - 1)
  have hdis : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro r hrA hrT
    simp only [A, T, mem_Icc] at hrA hrT
    omega
  have hunion : A ∪ T = Icc 1 (M - 1) := by
    ext r
    simp only [A, T, mem_union, mem_Icc]
    omega
  rw [← hunion, sum_union hdis]

/-- Pareto lower bound before averaging: retaining only lags whose descendant
sum has length at least `L` costs exactly the triangular tail `L*(L-1)/2`. -/
theorem retained_circleOrbitCorrelation_sum_lower
    (x : ℕ → ℝ) (h : ℤ) (M L : ℕ) (hL : 1 ≤ L) (hLM : L < M) :
    (‖∑ j ∈ range M, circleOrbitPhase x h j‖ ^ 2 - (M : ℝ) -
          (L : ℝ) * ((L - 1 : ℕ) : ℝ)) / 2 ≤
      ∑ r ∈ Icc 1 (M - L), (circleOrbitCorrelation x h M r).re := by
  have hid := circleOrbit_autocorrelation_identity x h M
  rw [full_lag_sum_eq_retained_add_tail x h M L hL hLM] at hid
  have htail := tail_circleOrbitCorrelation_re_le x h M L hLM.le
  have htriNat : 2 * (L * (L - 1) / 2) = L * (L - 1) := by
    rw [mul_comm, ← Finset.sum_range_id]
    exact Finset.sum_range_id_mul_two L
  have htri :
      (2 : ℝ) * (L * (L - 1) / 2 : ℕ) =
        (L : ℝ) * ((L - 1 : ℕ) : ℝ) := by
    exact_mod_cast htriNat
  nlinarith

/-- Explicit cutoff Pareto bound. Some lag `1 ≤ r ≤ M-L` retains at least
`L` terms and reaches the displayed average lower bound. -/
theorem exists_lag_with_remainingLength_and_pareto_bound
    (x : ℕ → ℝ) (h : ℤ) (M L : ℕ) (hL : 1 ≤ L) (hLM : L < M) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ M - L ∧ L ≤ M - r ∧
      (‖∑ j ∈ range M, circleOrbitPhase x h j‖ ^ 2 - (M : ℝ) -
          (L : ℝ) * ((L - 1 : ℕ) : ℝ)) /
            (2 * ((M - L : ℕ) : ℝ)) ≤
        (circleOrbitCorrelation x h M r).re := by
  let S : Finset ℕ := Icc 1 (M - L)
  let A : ℝ :=
    (‖∑ j ∈ range M, circleOrbitPhase x h j‖ ^ 2 - (M : ℝ) -
      (L : ℝ) * ((L - 1 : ℕ) : ℝ)) / (2 * ((M - L : ℕ) : ℝ))
  have hML : 0 < M - L := Nat.sub_pos_of_lt hLM
  have hSnonempty : S.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [S, mem_Icc]
    omega
  have hScard : S.card = M - L := by
    simp only [S, Nat.card_Icc]
    omega
  have hlower := retained_circleOrbitCorrelation_sum_lower x h M L hL hLM
  have hsum :
      (∑ r ∈ S, A) ≤
        ∑ r ∈ S, (circleOrbitCorrelation x h M r).re := by
    calc
      (∑ r ∈ S, A) = ((M - L : ℕ) : ℝ) * A := by
        simp [hScard]
      _ = (‖∑ j ∈ range M, circleOrbitPhase x h j‖ ^ 2 - (M : ℝ) -
            (L : ℝ) * ((L - 1 : ℕ) : ℝ)) / 2 := by
        dsimp [A]
        field_simp
      _ ≤ ∑ r ∈ S, (circleOrbitCorrelation x h M r).re := by
        simpa only [S] using hlower
  obtain ⟨r, hrS, hr⟩ := Finset.exists_le_of_sum_le hSnonempty hsum
  simp only [S, mem_Icc] at hrS
  refine ⟨r, hrS.1, hrS.2, ?_, ?_⟩
  · omega
  · simpa only [A] using hr

/-- The same Pareto theorem with the lag correlation fully expanded. -/
theorem exists_lag_with_remainingLength_and_pareto_bound_explicit
    (x : ℕ → ℝ) (h : ℤ) (M L : ℕ) (hL : 1 ≤ L) (hLM : L < M) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ M - L ∧ L ≤ M - r ∧
      (‖∑ j ∈ range M, phase h (x j)‖ ^ 2 - (M : ℝ) -
          (L : ℝ) * ((L - 1 : ℕ) : ℝ)) /
            (2 * ((M - L : ℕ) : ℝ)) ≤
        (∑ j ∈ range (M - r),
          phase h (x (j + r)) * conj (phase h (x j))).re := by
  simpa only [circleOrbitPhase, circleOrbitCorrelation, autocorrelation] using
    exists_lag_with_remainingLength_and_pareto_bound x h M L hL hLM

/-- T10's literal `B`-before-witness order, followed by the growing cutoff
`L=2^n` and the strongest direct Pareto descendant bound. -/
theorem piFailureC1_implies_growing_cutoff_pareto_quantifiers
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H L r : ℕ, ∃ h : ℤ,
        N ≤ n ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧ h ≠ 0 ∧ h.natAbs < H ∧
          B * (M : ℝ) < ‖piOrbitSum h M‖ ^ 2 ∧
          L = 2 ^ n ∧ 1 ≤ r ∧ r ≤ M - L ∧ L ≤ M - r ∧
          (B * (M : ℝ) - (M : ℝ) -
              (L : ℝ) * ((L - 1 : ℕ) : ℝ)) /
                (2 * ((M - L : ℕ) : ℝ)) <
            (piOrbitSum (h * ((10 : ℤ) ^ r - 1)) (M - r)).re := by
  intro B hB N hN
  obtain ⟨n, k, M, H, h, hn, hM, hk, hH, hh0, hhH, hlarge⟩ :=
    piFailureC1_implies_arbitrarily_large_scale_resonance
      hfailure B hB N hN
  have hn1 : 1 ≤ n := hN.trans hn
  have hpowpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hLpos : 1 ≤ 2 ^ n := hpowpos
  have hLMpow : 2 ^ n < 10 ^ n := by
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hLM : 2 ^ n < M := by simpa only [hM] using hLMpow
  obtain ⟨r, hr1, hrupper, hremain, hpareto⟩ :=
    exists_lag_with_remainingLength_and_pareto_bound
      (x := DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit)
      h M (2 ^ n) hLpos hLM
  have hfour :
      ‖∑ j ∈ range M, circleOrbitPhase
          DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h j‖ ^ 2 =
        ‖piOrbitSum h M‖ ^ 2 := by
    rw [← piOrbitSum_eq_circleOrbitPhase_sum]
  have hdenom : (0 : ℝ) < 2 * ((M - 2 ^ n : ℕ) : ℝ) := by
    have : 0 < M - 2 ^ n := Nat.sub_pos_of_lt hLM
    positivity
  have hstrict :
      (B * (M : ℝ) - (M : ℝ) -
          ((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) - 1 : ℕ) : ℝ)) /
            (2 * ((M - 2 ^ n : ℕ) : ℝ)) <
        (circleOrbitCorrelation
          DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit
            h M r).re := by
    apply lt_of_lt_of_le _ hpareto
    apply (div_lt_div_iff_of_pos_right hdenom).2
    rw [hfour]
    linarith
  rw [pi_circleOrbitCorrelation_eq_piOrbitSum_lagFrequency] at hstrict
  exact ⟨n, k, M, H, 2 ^ n, r, h, hn, hM, hk, hH, hh0, hhH,
    hlarge, rfl, hr1, hrupper, hremain, by
      simpa only [decimalLagFrequency] using hstrict⟩

/-- Literal failure of C1 conditionally yields a descendant resonance whose
remaining length grows at least as `2^n`. The requested level `C`, hence
`B=2*C+2`, is fixed before T10 supplies `n,k,M,H,h`; no child bandwidth claim
or unconditional assertion about pi is made. -/
theorem piFailureC1_implies_growing_remainingLength_resonance
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ C : ℝ, 0 ≤ C → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H L r : ℕ, ∃ h : ℤ,
        N ≤ n ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧ h ≠ 0 ∧ h.natAbs < H ∧
          (2 * C + 2) * (M : ℝ) < ‖piOrbitSum h M‖ ^ 2 ∧
          L = 2 ^ n ∧ 1 ≤ r ∧ r ≤ M - L ∧ L ≤ M - r ∧
          C < (piOrbitSum (h * ((10 : ℤ) ^ r - 1)) (M - r)).re := by
  intro C hC N hN
  have hB : 0 ≤ 2 * C + 2 := by positivity
  obtain ⟨n, k, M, H, h, hn, hM, hk, hH, hh0, hhH, hlarge⟩ :=
    piFailureC1_implies_arbitrarily_large_scale_resonance
      hfailure (2 * C + 2) hB N hN
  have hn1 : 1 ≤ n := hN.trans hn
  have hpowpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hLpos : 1 ≤ 2 ^ n := hpowpos
  have hLMpow : 2 ^ n < 10 ^ n := by
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hLM : 2 ^ n < M := by simpa only [hM] using hLMpow
  obtain ⟨r, hr1, hrupper, hremain, hpareto⟩ :=
    exists_lag_with_remainingLength_and_pareto_bound
      (x := DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit)
      h M (2 ^ n) hLpos hLM
  have hfour :
      ‖∑ j ∈ range M, circleOrbitPhase
          DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h j‖ ^ 2 =
        ‖piOrbitSum h M‖ ^ 2 := by
    rw [← piOrbitSum_eq_circleOrbitPhase_sum]
  have htailNat : (2 ^ n) * (2 ^ n - 1) < M := by
    calc
      (2 ^ n) * (2 ^ n - 1) < (2 ^ n) * (2 ^ n) := by
        gcongr
        omega
      _ = 4 ^ n := by rw [← mul_pow]; norm_num
      _ ≤ 10 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      _ = M := hM.symm
  have htail :
      ((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) - 1 : ℕ) : ℝ) < (M : ℝ) := by
    exact_mod_cast htailNat
  have hdenom : (0 : ℝ) < 2 * ((M - 2 ^ n : ℕ) : ℝ) := by
    have : 0 < M - 2 ^ n := Nat.sub_pos_of_lt hLM
    positivity
  have hMreal : (0 : ℝ) < M := by
    exact_mod_cast (lt_trans hpowpos hLM)
  have hcutoff : (((M - 2 ^ n : ℕ) : ℕ) : ℝ) < (M : ℝ) := by
    exact_mod_cast Nat.sub_lt (lt_trans hpowpos hLM) hpowpos
  have hlower :
      C <
        (‖∑ j ∈ range M, circleOrbitPhase
              DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit h j‖ ^ 2 -
            (M : ℝ) - ((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) - 1 : ℕ) : ℝ)) /
          (2 * ((M - 2 ^ n : ℕ) : ℝ)) := by
    rw [hfour]
    apply (lt_div_iff₀ hdenom).2
    nlinarith
  have hchild :
      C < (circleOrbitCorrelation
        DecimalFactorComplexity.PairCorrelationConditional.piDecimalShiftOrbit
          h M r).re := lt_of_lt_of_le hlower hpareto
  rw [pi_circleOrbitCorrelation_eq_piOrbitSum_lagFrequency] at hchild
  exact ⟨n, k, M, H, 2 ^ n, r, h, hn, hM, hk, hH, hh0, hhH,
    hlarge, rfl, hr1, hrupper, hremain, by
      simpa only [decimalLagFrequency] using hchild⟩

/-- An explicit, unproved short-lag coherence premise. No theorem below
asserts this premise for the decimal orbit of pi. -/
def ShortLagCoherence (z : ℕ → ℂ) (M R : ℕ) (delta : ℝ) : Prop :=
  ∑ r ∈ Icc (R + 1) (M - 1), (autocorrelation z M r).re ≤
    (1 - delta) * (‖∑ j ∈ range M, z j‖ ^ 2 - (M : ℝ)) / 2

/-- Exact split into fixed short lags and the discarded long-lag tail. -/
theorem full_autocorrelation_sum_eq_short_add_tail
    (z : ℕ → ℂ) (M R : ℕ) (hR : 1 ≤ R) (hRM : R < M) :
    (∑ r ∈ Icc 1 (M - 1), (autocorrelation z M r).re) =
      (∑ r ∈ Icc 1 R, (autocorrelation z M r).re) +
      ∑ r ∈ Icc (R + 1) (M - 1), (autocorrelation z M r).re := by
  let A : Finset ℕ := Icc 1 R
  let T : Finset ℕ := Icc (R + 1) (M - 1)
  have hdis : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro r hrA hrT
    simp only [A, T, mem_Icc] at hrA hrT
    omega
  have hunion : A ∪ T = Icc 1 (M - 1) := by
    ext r
    simp only [A, T, mem_union, mem_Icc]
    omega
  rw [← hunion, sum_union hdis]

/-- The exact consequence of the additional coherence premise. -/
theorem shortLagCoherence_implies_retained_lower
    (z : ℕ → ℂ) (M R : ℕ) (delta : ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hR : 1 ≤ R) (hRM : R < M)
    (hcoh : ShortLagCoherence z M R delta) :
    delta * (‖∑ j ∈ range M, z j‖ ^ 2 - (M : ℝ)) / 2 ≤
      ∑ r ∈ Icc 1 R, (autocorrelation z M r).re := by
  have hid := norm_sum_sq_eq_autocorrelation z M hz
  rw [full_autocorrelation_sum_eq_short_add_tail z M R hR hRM] at hid
  unfold ShortLagCoherence at hcoh
  nlinarith

/-- The concrete period-three unit sequence `(1,1,-1)^4`. -/
def coherenceCounterexample (j : ℕ) : ℂ :=
  if j % 3 = 2 then -1 else 1

theorem coherenceCounterexample_norm_one (j : ℕ) :
    ‖coherenceCounterexample j‖ = 1 := by
  unfold coherenceCounterexample
  split <;> simp

/-- Checked finite values: length `12`, total sum `4`, squared norm `16`,
and the only lag at cutoff `R=1` is the negative value `-3`. -/
theorem coherenceCounterexample_checked_values :
    (∑ j ∈ range 12, coherenceCounterexample j) = 4 ∧
      ‖∑ j ∈ range 12, coherenceCounterexample j‖ ^ 2 = 16 ∧
      autocorrelation coherenceCounterexample 12 1 = -3 := by
  norm_num [coherenceCounterexample, autocorrelation, Finset.sum_range_succ]

/-- Expanded lag-one computation for the finite counterexample. -/
theorem coherenceCounterexample_lag_one_explicit :
    (∑ j ∈ range 11,
      coherenceCounterexample (j + 1) * conj (coherenceCounterexample j)) = -3 := by
  simpa only [autocorrelation] using coherenceCounterexample_checked_values.2.2

/-- For every positive coherence constant, the checked length-12 sequence
violates the explicit `R=1` coherence premise despite energy `16 > 12`. -/
theorem coherenceCounterexample_not_shortLagCoherence
    (delta : ℝ) (hdelta : 0 < delta) :
    ‖∑ j ∈ range 12, coherenceCounterexample j‖ ^ 2 > 12 ∧
      ¬ ShortLagCoherence coherenceCounterexample 12 1 delta := by
  constructor
  · rw [coherenceCounterexample_checked_values.2.1]
    norm_num
  · unfold ShortLagCoherence
    have hid := norm_sum_sq_eq_autocorrelation coherenceCounterexample 12
      coherenceCounterexample_norm_one
    rw [full_autocorrelation_sum_eq_short_add_tail
      coherenceCounterexample 12 1 (by norm_num) (by norm_num)] at hid
    have hshort :
        (∑ r ∈ Icc 1 1, (autocorrelation coherenceCounterexample 12 r).re) = -3 := by
      simp [coherenceCounterexample_checked_values.2.2]
    have htail :
        (∑ r ∈ Icc 2 11, (autocorrelation coherenceCounterexample 12 r).re) = 5 := by
      rw [coherenceCounterexample_checked_values.2.1, hshort] at hid
      norm_num at hid ⊢
      linarith
    rw [htail, coherenceCounterexample_checked_values.2.1]
    norm_num
    linarith

end DecimalFactorComplexity.AutocorrelationAmplification

#print axioms DecimalFactorComplexity.AutocorrelationAmplification.circleOrbit_autocorrelation_identity_explicit
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.norm_circleOrbitCorrelation_le_remainingLength
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.tail_remainingLength_sum
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.tail_circleOrbitCorrelation_re_le
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.full_lag_sum_eq_retained_add_tail
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.retained_circleOrbitCorrelation_sum_lower
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.exists_lag_with_remainingLength_and_pareto_bound_explicit
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.piOrbitPhase_mul_conj_eq_lagFrequency
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.pi_circleOrbitCorrelation_eq_piOrbitSum_lagFrequency
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.piFailureC1_implies_growing_cutoff_pareto_quantifiers
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.piFailureC1_implies_growing_remainingLength_resonance
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.full_autocorrelation_sum_eq_short_add_tail
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.shortLagCoherence_implies_retained_lower
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.coherenceCounterexample_norm_one
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.coherenceCounterexample_checked_values
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.coherenceCounterexample_lag_one_explicit
#print axioms DecimalFactorComplexity.AutocorrelationAmplification.coherenceCounterexample_not_shortLagCoherence
