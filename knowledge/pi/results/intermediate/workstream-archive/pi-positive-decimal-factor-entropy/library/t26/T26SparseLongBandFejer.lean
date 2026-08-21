import TheoryLib.PiPositiveDecimalFactorEntropy.T2T2ExponentialCollisionCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion

/-!
# T26: sparse-sample, long-band Fejer criterion

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file keeps the sample length and Fourier bandwidth independent.  It then
specializes to `L_n = 10^(n/2)` (natural-number division) and
`H_n = 10^n/2`.  Every conclusion about positive decimal factor entropy is
conditional on the explicit, unproved predicate `PiSparseLongBandC7`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace DecimalFactorComplexity.SparseLongBandFejer

open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.WeightedFourierReduction

/-- The sparse sample length `L_n = 10^(n/2)`, where `/` is natural-number
division. -/
def sparseSampleLength (n : ℕ) : ℕ := 10 ^ (n / 2)

/-- The independently chosen long bandwidth `H_n = 10^n/2`. -/
def longBandwidth (n : ℕ) : ℕ := 10 ^ n / 2

/-- T7's complete signed Fejer energy, presented in sample-first order so the
sample length `L` is visibly independent of the bandwidth `H`. -/
def completePiFejerEnergy (L H : ℕ) : ℝ :=
  piFejerEnergy H L

/-- The exact sparse parameters, including natural-number division in the
exponent defining `L_n`. -/
theorem sparse_parameters (n : ℕ) :
    sparseSampleLength n = 10 ^ (n / 2) ∧
      longBandwidth n = 10 ^ n / 2 := by
  exact ⟨rfl, rfl⟩

/-- The complete band, strict cutoff, triangular weight, zero mode, and every
orbit sum are visible in this expansion. -/
theorem completePiFejerEnergy_eq_complete_band (L H : ℕ) :
    completePiFejerEnergy L H =
      ∑ h ∈ fejerFrequencies H,
        (1 - (h.natAbs : ℝ) / (H : ℝ)) *
          ‖∑ j : Fin L,
            DecimalFactorComplexity.FejerSpectralCriterion.phase h
              (piDecimalShiftOrbit j)‖ ^ 2 := by
  rfl

/-- The strict frequency cutoff in the sample-first energy is `|h| < H`. -/
theorem mem_completePiFejerEnergy_frequencies_iff
    {H : ℕ} {h : ℤ} (hH : 1 ≤ H) :
    h ∈ fejerFrequencies H ↔ h.natAbs < H := by
  exact mem_fejerFrequencies_iff hH

/-- At every positive decimal length, twice the long bandwidth is exactly the
decimal resolution. -/
theorem two_mul_longBandwidth (n : ℕ) (hn : 1 ≤ n) :
    2 * longBandwidth n = 10 ^ n := by
  exact two_mul_half_ten_pow n hn

/-- The sparse sample contains at least one orbit point. -/
theorem sparseSampleLength_pos (n : ℕ) : 0 < sparseSampleLength n := by
  unfold sparseSampleLength
  positivity

/-- Every pair counted by `Q_pi(n,L_n)` lies in the central interval of the
order-`H_n-1` Fejer kernel.  The decimal cutoff is strictly `10^(-n)` and is
not replaced by a non-strict inequality. -/
theorem piSparseNearReturn_fejerKernel_lower
    (n : ℕ) (hn : 1 ≤ n)
    (ij : Fin (sparseSampleLength n) × Fin (sparseSampleLength n))
    (hnear : circleDistance
        (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
          ((10 : ℝ) ^ n)⁻¹) :
    4 * (longBandwidth n : ℝ) / Real.pi ^ 2 ≤
      DecimalFactorComplexity.FejerSpectralCriterion.fejerKernel
        (longBandwidth n - 1)
        (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) := by
  have hdouble : 2 * longBandwidth n = 10 ^ n :=
    two_mul_longBandwidth n hn
  have hpowpos : 0 < 10 ^ n := by positivity
  have hH : 1 ≤ longBandwidth n := by
    omega
  have hdoubleReal :
      2 * (longBandwidth n : ℝ) = (10 : ℝ) ^ n := by
    exact_mod_cast hdouble
  have horbit :
      circleDistance
          (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
        (2 * (longBandwidth n : ℝ))⁻¹ := by
    rw [hdoubleReal, circleDistance_piShift_sub_eq_powerDifference]
    exact hnear
  exact fejerKernel_pred_lower_of_circleDistance_lt
    (longBandwidth n) hH
    (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) horbit

/-- Exact sparse-sample finite Fourier transfer.  It exposes `n`, `L_n`,
`H_n`, the strict decimal cutoff inside `Q_pi`, and the constant
`pi^2/(4 H_n)`. -/
theorem Q_pi_sparseSampleLength_le_completePiFejerEnergy
    (n : ℕ) (hn : 1 ≤ n) :
    (Q_pi n (sparseSampleLength n) : ℝ) ≤
      (Real.pi ^ 2 / (4 * (longBandwidth n : ℝ))) *
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) := by
  classical
  have hH : 1 ≤ longBandwidth n := by
    have hdouble : 2 * longBandwidth n = 10 ^ n :=
      two_mul_longBandwidth n hn
    have hpowpos : 0 < 10 ^ n := by positivity
    omega
  have hcard :
      (Q_pi n (sparseSampleLength n) : ℝ) =
        ∑ ij : Fin (sparseSampleLength n) × Fin (sparseSampleLength n),
          if circleDistance
              (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) <
                ((10 : ℝ) ^ n)⁻¹ then 1 else 0 := by
    unfold Q_pi piNearReturnPairs
    norm_cast
    simp
  have hsum :
      (4 * (longBandwidth n : ℝ) / Real.pi ^ 2) *
          (Q_pi n (sparseSampleLength n) : ℝ) ≤
        ∑ ij : Fin (sparseSampleLength n) × Fin (sparseSampleLength n),
          DecimalFactorComplexity.FejerSpectralCriterion.fejerKernel
            (longBandwidth n - 1)
            (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) := by
    rw [hcard, Finset.mul_sum]
    apply sum_le_sum
    intro ij hij
    split_ifs with hnear
    · simpa only [mul_one] using
        piSparseNearReturn_fejerKernel_lower n hn ij hnear
    · simp only [mul_zero]
      exact Theory.PiDigits.T27.fejerKernel_nonneg _ _
  rw [orderedPair_fejerKernel_eq_piFejerEnergy
    (longBandwidth n) (sparseSampleLength n) hH] at hsum
  change (4 * (longBandwidth n : ℝ) / Real.pi ^ 2) *
      (Q_pi n (sparseSampleLength n) : ℝ) ≤
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) at hsum
  have hHreal : (0 : ℝ) < longBandwidth n := by exact_mod_cast hH
  have hscale : 0 < 4 * (longBandwidth n : ℝ) / Real.pi ^ 2 := by
    positivity
  have hdiv :
      (Q_pi n (sparseSampleLength n) : ℝ) ≤
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) /
          (4 * (longBandwidth n : ℝ) / Real.pi ^ 2) := by
    apply (le_div_iff₀ hscale).2
    simpa [mul_comm] using hsum
  calc
    (Q_pi n (sparseSampleLength n) : ℝ) ≤
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) /
          (4 * (longBandwidth n : ℝ) / Real.pi ^ 2) := hdiv
    _ = (Real.pi ^ 2 / (4 * (longBandwidth n : ℝ))) *
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) := by
      field_simp [hHreal.ne', Real.pi_ne_zero]

/-- C7 is the explicit unproved fixed-pi input.  One positive constant controls
the sparse complete energy at every sufficiently late decimal length. -/
def PiSparseLongBandC7 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) ≤
        C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)

/-- C7 with every quantifier, scale, and normalization exposed. -/
theorem piSparseLongBandC7_iff_quantifiers :
    PiSparseLongBandC7 ↔
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) ≤
            C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) :=
  Iff.rfl

/-- A single C7 energy estimate gives the explicit linear near-return bound. -/
theorem Q_pi_sparseSampleLength_le_linear_of_energy_bound
    (C : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (henergy :
      completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) ≤
        C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)) :
    (Q_pi n (sparseSampleLength n) : ℝ) ≤
      (Real.pi ^ 2 / 4 * C) * (sparseSampleLength n : ℝ) := by
  have hfourier :=
    Q_pi_sparseSampleLength_le_completePiFejerEnergy n hn
  have hH : 1 ≤ longBandwidth n := by
    have hdouble : 2 * longBandwidth n = 10 ^ n :=
      two_mul_longBandwidth n hn
    have hpowpos : 0 < 10 ^ n := by positivity
    omega
  have hHreal : (0 : ℝ) < longBandwidth n := by exact_mod_cast hH
  calc
    (Q_pi n (sparseSampleLength n) : ℝ) ≤
        (Real.pi ^ 2 / (4 * (longBandwidth n : ℝ))) *
          completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) :=
      hfourier
    _ ≤ (Real.pi ^ 2 / (4 * (longBandwidth n : ℝ))) *
          (C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)) := by
      gcongr
    _ = (Real.pi ^ 2 / 4 * C) * (sparseSampleLength n : ℝ) := by
      field_simp [hHreal.ne']

/-- The explicit unproved C7 hypothesis conditionally gives
`Q_pi(n,L_n) = O(L_n)`, with the inherited constant `pi^2 C / 4`. -/
theorem piSparseLongBandC7_implies_explicit_Q_linear
    (hC7 : PiSparseLongBandC7) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (Q_pi n (sparseSampleLength n) : ℝ) ≤
          (Real.pi ^ 2 / 4 * C) * (sparseSampleLength n : ℝ) := by
  obtain ⟨C, hC, N, hN, henergy⟩ := hC7
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn
  have hnpos : 1 ≤ n := hN.trans hn
  exact Q_pi_sparseSampleLength_le_linear_of_energy_bound
    C n hnpos (henergy n hn)

/-- Any fixed constant is eventually absorbed by the sparse sample length
times the exact quarter-exponential decay needed for C2. -/
theorem eventually_constant_le_sparseSampleLength_mul_quarter_decay (K : ℝ) :
    ∃ n1 : ℕ, 1 ≤ n1 ∧ ∀ n : ℕ, n1 ≤ n →
      K ≤ (sparseSampleLength n : ℝ) *
        (10 : ℝ) ^ (-(1 / 4 : ℝ) * (n : ℝ)) := by
  let b : ℝ := (10 : ℝ) ^ (1 / 4 : ℝ)
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have ht : Filter.Tendsto (fun n : ℕ => b ^ n)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      K * (10 : ℝ) ^ (1 / 2 : ℝ) < b ^ n :=
    ht.eventually_gt_atTop (K * (10 : ℝ) ^ (1 / 2 : ℝ))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨m, hm⟩ := hev
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hmn : m ≤ n := (le_max_right 1 m).trans hn
  have hgrowth :
      K * (10 : ℝ) ^ (1 / 2 : ℝ) ≤
        (10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) := by
    calc
      K * (10 : ℝ) ^ (1 / 2 : ℝ) ≤ b ^ n := (hm n hmn).le
      _ = (10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) := by
        dsimp [b]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hsqrt : 0 < (10 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hK :
      K ≤ (10 : ℝ) ^
        ((1 / 4 : ℝ) * (n : ℝ) - (1 / 2 : ℝ)) := by
    calc
      K = (K * (10 : ℝ) ^ (1 / 2 : ℝ)) *
          ((10 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
        field_simp [hsqrt.ne']
      _ ≤ (10 : ℝ) ^ ((1 / 4 : ℝ) * (n : ℝ)) *
          ((10 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = (10 : ℝ) ^
          ((1 / 4 : ℝ) * (n : ℝ) - (1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
        congr 1
  have hnDiv : n ≤ 2 * (n / 2) + 1 := by omega
  have hnDivReal :
      (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnDiv
  have hexponent :
      (1 / 4 : ℝ) * (n : ℝ) - (1 / 2 : ℝ) ≤
        ((n / 2 : ℕ) : ℝ) - (1 / 4 : ℝ) * (n : ℝ) := by
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 10) hexponent
  have hLcast :
      (sparseSampleLength n : ℝ) =
        (10 : ℝ) ^ ((n / 2 : ℕ) : ℝ) := by
    unfold sparseSampleLength
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  calc
    K ≤ (10 : ℝ) ^
        ((1 / 4 : ℝ) * (n : ℝ) - (1 / 2 : ℝ)) := hK
    _ ≤ (10 : ℝ) ^
        (((n / 2 : ℕ) : ℝ) - (1 / 4 : ℝ) * (n : ℝ)) := hpow
    _ = (sparseSampleLength n : ℝ) *
        (10 : ℝ) ^ (-(1 / 4 : ℝ) * (n : ℝ)) := by
      rw [hLcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
      congr 1
      ring

/-- C7 conditionally gives the exact C2 collision estimate with
`eta = 1/4` and the exposed witness `M = L_n`. -/
theorem piSparseLongBandC7_implies_explicit_collision_bound
    (hC7 : PiSparseLongBandC7) :
    ∃ nstar : ℕ, 1 ≤ nstar ∧ ∀ n : ℕ, nstar ≤ n →
      (E_pi n (sparseSampleLength n) : ℝ) ≤
        (sparseSampleLength n : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 4 : ℝ) * (n : ℝ)) := by
  obtain ⟨C, hC, N, hN, henergy⟩ := hC7
  obtain ⟨n1, hn1, hgrowth⟩ :=
    eventually_constant_le_sparseSampleLength_mul_quarter_decay
      (Real.pi ^ 2 / 4 * C)
  refine ⟨max N n1, hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hNn : N ≤ n := (le_max_left N n1).trans hn
  have hn1n : n1 ≤ n := (le_max_right N n1).trans hn
  have hnpos : 1 ≤ n := hN.trans hNn
  have hQ := Q_pi_sparseSampleLength_le_linear_of_energy_bound
    C n hnpos (henergy n hNn)
  have hcollisionNat :=
    pi_collisionEnergy_le_Q_pi n (sparseSampleLength n)
  have hcollision :
      (E_pi n (sparseSampleLength n) : ℝ) ≤
        (Q_pi n (sparseSampleLength n) : ℝ) := by
    exact_mod_cast hcollisionNat
  have hconstant := hgrowth n hn1n
  have hLnonneg : (0 : ℝ) ≤ sparseSampleLength n := by positivity
  calc
    (E_pi n (sparseSampleLength n) : ℝ) ≤
        (Q_pi n (sparseSampleLength n) : ℝ) := hcollision
    _ ≤ (Real.pi ^ 2 / 4 * C) * (sparseSampleLength n : ℝ) := hQ
    _ ≤ ((sparseSampleLength n : ℝ) *
          (10 : ℝ) ^ (-(1 / 4 : ℝ) * (n : ℝ))) *
          (sparseSampleLength n : ℝ) := by
      exact mul_le_mul_of_nonneg_right hconstant hLnonneg
    _ = (sparseSampleLength n : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(1 / 4 : ℝ) * (n : ℝ)) := by
      ring

/-- The explicit unproved C7 hypothesis supplies T2's C2 with the fixed
exponent `eta = 1/4`. -/
theorem piSparseLongBandC7_implies_C2
    (hC7 : PiSparseLongBandC7) :
    PiExponentialCollisionC2 := by
  obtain ⟨nstar, hnstar, hbound⟩ :=
    piSparseLongBandC7_implies_explicit_collision_bound hC7
  refine ⟨(1 / 4 : ℝ), by norm_num, nstar, hnstar, ?_⟩
  intro n hn
  exact ⟨sparseSampleLength n,
    Nat.zero_lt_of_lt (sparseSampleLength_pos n), hbound n hn⟩

/-- Canonical C1 follows through T2 only under the explicit unproved C7
hypothesis. -/
theorem piSparseLongBandC7_implies_C1
    (hC7 : PiSparseLongBandC7) :
    PiPositiveFactorEntropyC1 := by
  exact piExponentialCollisionC2_implies_C1
    (piSparseLongBandC7_implies_C2 hC7)

/-- Direct contrapositive in the required order: literal failure of C1, then
arbitrary `B`, then arbitrary cutoff `N`, forces a later sparse scale whose
complete energy is larger than `B H_n L_n`.  No C1 failure is asserted. -/
theorem piFailureC1_implies_arbitrarily_large_sparseLongBandEnergy
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      B * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) <
        completePiFejerEnergy (sparseSampleLength n) (longBandwidth n) := by
  have hnotC7 : ¬ PiSparseLongBandC7 := by
    intro hC7
    apply hfailure
    exact piSparseLongBandC7_implies_C1 hC7
  unfold PiSparseLongBandC7 at hnotC7
  push Not at hnotC7
  intro B N
  let C : ℝ := max B 1
  have hC : 0 < C := by
    exact lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  let N' : ℕ := max 1 N
  have hN' : 1 ≤ N' := le_max_left 1 N
  obtain ⟨n, hn, hlarge⟩ := hnotC7 C hC N' hN'
  refine ⟨n, (le_max_right 1 N).trans hn, ?_⟩
  have hBC : B ≤ C := le_max_left B 1
  have hHL :
      (0 : ℝ) ≤
        (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) := by
    positivity
  have hnormalize :
      B * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) ≤
        C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) := by
    calc
      B * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) =
          B * ((longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)) := by ring
      _ ≤ C * ((longBandwidth n : ℝ) * (sparseSampleLength n : ℝ)) :=
        mul_le_mul_of_nonneg_right hBC hHL
      _ = C * (longBandwidth n : ℝ) * (sparseSampleLength n : ℝ) := by ring
  exact hnormalize.trans_lt hlarge

end DecimalFactorComplexity.SparseLongBandFejer

#print axioms DecimalFactorComplexity.SparseLongBandFejer.completePiFejerEnergy_eq_complete_band
#print axioms DecimalFactorComplexity.SparseLongBandFejer.sparse_parameters
#print axioms DecimalFactorComplexity.SparseLongBandFejer.mem_completePiFejerEnergy_frequencies_iff
#print axioms DecimalFactorComplexity.SparseLongBandFejer.two_mul_longBandwidth
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseNearReturn_fejerKernel_lower
#print axioms DecimalFactorComplexity.SparseLongBandFejer.Q_pi_sparseSampleLength_le_completePiFejerEnergy
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseLongBandC7_iff_quantifiers
#print axioms DecimalFactorComplexity.SparseLongBandFejer.Q_pi_sparseSampleLength_le_linear_of_energy_bound
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseLongBandC7_implies_explicit_Q_linear
#print axioms DecimalFactorComplexity.SparseLongBandFejer.eventually_constant_le_sparseSampleLength_mul_quarter_decay
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseLongBandC7_implies_explicit_collision_bound
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseLongBandC7_implies_C2
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piSparseLongBandC7_implies_C1
#print axioms DecimalFactorComplexity.SparseLongBandFejer.piFailureC1_implies_arbitrarily_large_sparseLongBandEnergy
