import TheoryLib.PiLacunaryNearReturnSparsity.T5LagDiscrepancy
import TheoryLib.PiDecimalFactorComplexity.T10PiWeightedFourierReduction

/-!
# Long lag resonance obstruction for pi near returns

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves only a necessary consequence of literal failure of the
canonical statement.  In particular, it proves no exponential-sum estimate
for `Real.pi` and does not assert that the canonical statement fails.
-/

noncomputable section

open Filter Finset Set
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity
namespace LongLagResonance

open LagDiscrepancy
open WeightedFourierReduction

/-- The length of the positive-lag orbit indexed by `r`. -/
def lagOrbitLength (N r : ℕ) : ℕ := N - r

/-- The base-ten lag orbit whose near-zero visits count the `r`-lag pairs. -/
def lagOrbitPoint (r j : ℕ) : ℝ :=
  (10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi

/-- The literal low-harmonic exponential sum on one lag orbit. -/
def lagExponentialSum (N r h : ℕ) : ℂ :=
  ∑ j ∈ range (N - r),
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
        ((lagOrbitPoint r j : ℝ) : ℂ))

lemma lagExponentialSum_eq_phase_sum (N r h : ℕ) :
    lagExponentialSum N r h =
      ∑ j ∈ range (N - r), phase (h : ℤ) (lagOrbitPoint r j) := by
  rfl

/-- Signed-frequency form used internally by the Fejer expansion. -/
def lagPhaseSum (N r : ℕ) (h : ℤ) : ℂ :=
  ∑ j ∈ range (N - r), phase h (lagOrbitPoint r j)

lemma lagPhaseSum_nat (N r h : ℕ) :
    lagPhaseSum N r (h : ℤ) = lagExponentialSum N r h := by
  rfl

lemma norm_lagPhaseSum_natAbs (N r : ℕ) (h : ℤ) :
    ‖lagPhaseSum N r h‖ = ‖lagExponentialSum N r h.natAbs‖ := by
  by_cases hh : 0 ≤ h
  · have hcast : ((h.natAbs : ℕ) : ℤ) = h := Int.natAbs_of_nonneg hh
    calc
      ‖lagPhaseSum N r h‖ = ‖lagPhaseSum N r (h.natAbs : ℤ)‖ := by rw [hcast]
      _ = ‖lagExponentialSum N r h.natAbs‖ :=
        congrArg norm (lagPhaseSum_nat N r h.natAbs)
  · have hneg : h < 0 := lt_of_not_ge hh
    have heq : h = -((h.natAbs : ℕ) : ℤ) :=
      Int.eq_neg_natAbs_of_nonpos hneg.le
    have hconj : lagPhaseSum N r h =
        conj (lagPhaseSum N r (h.natAbs : ℤ)) := by
      calc
        lagPhaseSum N r h = lagPhaseSum N r (-((h.natAbs : ℕ) : ℤ)) := by
          exact congrArg (lagPhaseSum N r) heq
        _ = conj (lagPhaseSum N r (h.natAbs : ℤ)) := by
          unfold lagPhaseSum
          simp_rw [Theory.PiDigits.T27.phase_neg]
          rw [map_sum]
    calc
      ‖lagPhaseSum N r h‖ = ‖conj (lagPhaseSum N r (h.natAbs : ℤ))‖ :=
        congrArg norm hconj
      _ = ‖lagPhaseSum N r (h.natAbs : ℤ)‖ := Complex.norm_conj _
      _ = ‖lagExponentialSum N r h.natAbs‖ :=
        congrArg norm (lagPhaseSum_nat N r h.natAbs)

/-- At canonical radii, no circular interval discrepancy can exceed the
number of points in its lag orbit. -/
theorem lagCircularIntervalDiscrepancy_le_length (N r : ℕ) (radius : ℝ)
    (hradius0 : 0 ≤ radius) (hradiusHalf : radius ≤ 1 / 2) :
    lagCircularIntervalDiscrepancy N r radius ≤ ((N - r : ℕ) : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro d ⟨center, rfl⟩
  have hcount : (lagCircularIntervalCount N r radius center : ℝ) ≤
      ((N - r : ℕ) : ℝ) := by
    exact_mod_cast lagCircularIntervalCount_le_length N r radius center
  have hexpected0 : 0 ≤ 2 * radius * ((N - r : ℕ) : ℝ) := by positivity
  have hexpected : 2 * radius * ((N - r : ℕ) : ℝ) ≤
      ((N - r : ℕ) : ℝ) := by
    have hlength : 0 ≤ ((N - r : ℕ) : ℝ) := by positivity
    nlinarith
  rw [abs_le]
  constructor <;> linarith [show 0 ≤ (lagCircularIntervalCount N r radius center : ℝ) by positivity]

lemma lagCircularIntervalDiscrepancy_decimalRadius_le_length
    (n N r : ℕ) (hn : 1 ≤ n) :
    lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
      ((N - r : ℕ) : ℝ) := by
  exact lagCircularIntervalDiscrepancy_le_length N r (decimalRadius n)
    (decimalRadius_pos n).le (decimalRadius_le_half n hn)

/-- Lags whose orbit has less than a `1/(16*A*n)` fraction of the full
prefix. -/
def shortLagSet (A n N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter fun r => 16 * A * n * (N - r) < N

/-- The total discrepancy carried by short lag orbits is at most the stated
`N²/(16*A*n)` budget. -/
theorem shortLagDiscrepancy_sum_le
    (A n N : ℕ) (hA : 1 ≤ A) (hn : 1 ≤ n) :
    (∑ r ∈ shortLagSet A n N,
        lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
      (N : ℝ) ^ 2 / (16 * (A : ℝ) * (n : ℝ)) := by
  have hAN : 0 < (A : ℝ) * (n : ℝ) := by positivity
  have hterm : ∀ r ∈ shortLagSet A n N,
      lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
        (N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hshort := hr'.2
    have hshortReal :
        16 * ((A : ℝ) * (n : ℝ)) * ((N - r : ℕ) : ℝ) < (N : ℝ) := by
      have hcast : ((16 * A * n * (N - r) : ℕ) : ℝ) < (N : ℝ) := by
        exact_mod_cast hshort
      norm_num only [Nat.cast_mul, Nat.cast_sub, Nat.cast_ofNat] at hcast
      simpa [mul_assoc] using hcast
    have hdisc := lagCircularIntervalDiscrepancy_decimalRadius_le_length n N r hn
    have hlength : ((N - r : ℕ) : ℝ) <
        (N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) := by
      apply (lt_div_iff₀ (by positivity :
        0 < 16 * ((A : ℝ) * (n : ℝ)))).2
      nlinarith
    exact hdisc.trans hlength.le
  have hcard : (shortLagSet A n N).card ≤ N := by
    calc
      (shortLagSet A n N).card ≤ (Finset.Icc 1 (N - 1)).card := by
        apply Finset.card_le_card
        intro r hr
        exact (Finset.mem_filter.mp hr).1
      _ ≤ N := by
        simp only [Nat.card_Icc]
        omega
  have hcardReal : ((shortLagSet A n N).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard
  calc
    (∑ r ∈ shortLagSet A n N,
        lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
      ∑ _r ∈ shortLagSet A n N,
        (N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) := by
          exact Finset.sum_le_sum fun r hr => hterm r hr
    _ = ((shortLagSet A n N).card : ℝ) *
        ((N : ℝ) / (16 * ((A : ℝ) * (n : ℝ)))) := by simp
    _ ≤ (N : ℝ) * ((N : ℝ) / (16 * ((A : ℝ) * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcardReal (by positivity)
    _ = (N : ℝ) ^ 2 / (16 * (A : ℝ) * (n : ℝ)) := by ring

/-- A bad finite canonical scale has a lag orbit occupying at least a
`1/(16*A*n)` fraction of the prefix and carrying normalized discrepancy at
least `1/(8*A*n)`.  The other branch is exactly the desired finite bound. -/
theorem finite_nearReturn_or_longLag_dichotomy
    (A n N : ℕ) (hA : 1 ≤ A) (hn : 1 ≤ n)
    (hNlarge : 8 * A * n ≤ N)
    (hradius : 8 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1) :
    A * n * Q_pi n N ≤ N ^ 2 ∨
      ∃ r ∈ Finset.Icc 1 (N - 1),
        N ≤ 16 * A * n * (N - r) ∧
        1 / (8 * (A : ℝ) * (n : ℝ)) ≤
          lagCircularIntervalDiscrepancy N r (decimalRadius n) /
            ((N - r : ℕ) : ℝ) := by
  by_cases hgood : A * n * Q_pi n N ≤ N ^ 2
  · exact Or.inl hgood
  right
  have hbad : N ^ 2 < A * n * Q_pi n N := Nat.lt_of_not_ge hgood
  have hAN : 0 < (A : ℝ) * (n : ℝ) := by positivity
  have hN : 1 ≤ N := by
    have hpos : 0 < 8 * A * n := by
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have : 1 ≤ 8 * A * n := hpos
    exact this.trans hNlarge
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hQ := Q_pi_le_lagDiscrepancy_sum n N hn hN
  have hbadReal : (N : ℝ) ^ 2 <
      (A : ℝ) * (n : ℝ) * (Q_pi n N : ℝ) := by
    exact_mod_cast hbad
  have hNlargeReal : 8 * ((A : ℝ) * (n : ℝ)) ≤ (N : ℝ) := by
    have hcast : ((8 * A * n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNlarge
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    simpa [mul_assoc] using hcast
  have hdiag :
      (A : ℝ) * (n : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 2 / 8 := by
    have hm := mul_le_mul_of_nonneg_right hNlargeReal hNreal.le
    nlinarith
  have hradiusTerm :
      4 * ((A : ℝ) * (n : ℝ)) * decimalRadius n * (N : ℝ) ^ 2 ≤
        (N : ℝ) ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hradius (sq_nonneg (N : ℝ))
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hQ hAN.le
  have hsumLower :
      3 * (N : ℝ) ^ 2 / (16 * ((A : ℝ) * (n : ℝ))) <
        ∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
    have hraw :
        3 * (N : ℝ) ^ 2 / 8 <
          2 * ((A : ℝ) * (n : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (N - 1),
              lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
      nlinarith
    apply (div_lt_iff₀ (by positivity :
      0 < 16 * ((A : ℝ) * (n : ℝ)))).2
    nlinarith
  by_contra hnone
  push Not at hnone
  have hterm : ∀ r ∈ Finset.Icc 1 (N - 1),
      lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
        (N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) +
          ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) := by
    intro r hr
    have hrBounds := Finset.mem_Icc.mp hr
    have hlengthNat : 0 < N - r := by omega
    have hlength : 0 < ((N - r : ℕ) : ℝ) := by exact_mod_cast hlengthNat
    by_cases hshort : 16 * A * n * (N - r) < N
    · have hshortReal :
          16 * ((A : ℝ) * (n : ℝ)) * ((N - r : ℕ) : ℝ) < (N : ℝ) := by
        have hcast : ((16 * A * n * (N - r) : ℕ) : ℝ) < (N : ℝ) := by
          exact_mod_cast hshort
        norm_num only [Nat.cast_mul, Nat.cast_sub, Nat.cast_ofNat] at hcast
        simpa [mul_assoc] using hcast
      have hdiscLength :=
        lagCircularIntervalDiscrepancy_decimalRadius_le_length n N r hn
      have hfirst : ((N - r : ℕ) : ℝ) <
          (N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) := by
        apply (lt_div_iff₀ (by positivity :
          0 < 16 * ((A : ℝ) * (n : ℝ)))).2
        nlinarith
      exact (hdiscLength.trans hfirst.le).trans
        (le_add_of_nonneg_right (by positivity))
    · have hlong : N ≤ 16 * A * n * (N - r) := Nat.le_of_not_gt hshort
      have hsmall := hnone r hr hlong
      have hdiscSmall :
          lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
            ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) := by
        have hmul := (div_lt_iff₀ hlength).mp hsmall
        exact hmul.le.trans_eq (by ring)
      exact hdiscSmall.trans (le_add_of_nonneg_left (by positivity))
  have hcard : (Finset.Icc 1 (N - 1)).card ≤ N := by
    simp only [Nat.card_Icc]
    omega
  have hcardReal : ((Finset.Icc 1 (N - 1)).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard
  have hsumUpper :
      (∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
        3 * (N : ℝ) ^ 2 / (16 * ((A : ℝ) * (n : ℝ))) := by
    calc
      (∑ r ∈ Finset.Icc 1 (N - 1),
          lagCircularIntervalDiscrepancy N r (decimalRadius n)) ≤
          ∑ r ∈ Finset.Icc 1 (N - 1),
            ((N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) +
              ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) ) := by
            exact Finset.sum_le_sum fun r hr => hterm r hr
      _ = ((Finset.Icc 1 (N - 1)).card : ℝ) *
            ((N : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) ) +
          (∑ r ∈ Finset.Icc 1 (N - 1), ((N - r : ℕ) : ℝ)) /
            (8 * ((A : ℝ) * (n : ℝ))) := by
          rw [Finset.sum_add_distrib]
          simp only [sum_const, nsmul_eq_mul, Finset.sum_div]
      _ ≤ (N : ℝ) * ((N : ℝ) / (16 * ((A : ℝ) * (n : ℝ)))) +
          (N : ℝ) ^ 2 / (8 * ((A : ℝ) * (n : ℝ))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
          · exact div_le_div_of_nonneg_right (lagLengthSum_le_sq N) (by positivity)
      _ = 3 * (N : ℝ) ^ 2 / (16 * ((A : ℝ) * (n : ℝ))) := by
          field_simp
          ring
  exact (not_lt_of_ge hsumUpper hsumLower)

/-- The long-lag branch extracted directly from a bad finite canonical scale. -/
theorem badFinite_nearReturn_implies_longLag
    (A n N : ℕ) (hA : 1 ≤ A) (hn : 1 ≤ n)
    (hNlarge : 8 * A * n ≤ N)
    (hradius : 8 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1)
    (hbad : N ^ 2 < A * n * Q_pi n N) :
    ∃ r ∈ Finset.Icc 1 (N - 1),
      N ≤ 16 * A * n * (N - r) ∧
      1 / (8 * (A : ℝ) * (n : ℝ)) ≤
        lagCircularIntervalDiscrepancy N r (decimalRadius n) /
          ((N - r : ℕ) : ℝ) := by
  rcases finite_nearReturn_or_longLag_dichotomy A n N hA hn hNlarge hradius with
    hgood | hlong
  · exact False.elim ((not_lt_of_ge hgood) hbad)
  · exact hlong

lemma lag_centered_integral_phase_identity
    (N r : ℕ) (h : ℤ) (center a : ℝ) :
    (∑ j ∈ range (N - r),
        ∫ y in -a..a,
          (phase h ((lagOrbitPoint r j - center) - y)).re) =
      ((phase h (-center) * lagPhaseSum N r h) *
        (∫ y in -a..a, phase (-h) y)).re := by
  have hintegrable : ∀ j ∈ range (N - r),
      IntervalIntegrable
        (fun y : ℝ => (phase h ((lagOrbitPoint r j - center) - y)).re)
        MeasureTheory.volume (-a) a := by
    intro j hj
    apply Continuous.intervalIntegrable
    unfold phase Theory.PiDigits.T27.phase lagOrbitPoint
    fun_prop
  rw [← intervalIntegral.integral_finsetSum hintegrable]
  have hpoint (y : ℝ) :
      (∑ j ∈ range (N - r),
          (phase h ((lagOrbitPoint r j - center) - y)).re) =
        ((phase h (-center) * lagPhaseSum N r h) * phase (-h) y).re := by
    have hcomplex :
        (∑ j ∈ range (N - r),
            phase h ((lagOrbitPoint r j - center) - y)) =
          (phase h (-center) * lagPhaseSum N r h) * phase (-h) y := by
      have hcenter : phase (-h) center = phase h (-center) := by
        calc
          phase (-h) center = conj (phase h center) :=
            Theory.PiDigits.T27.phase_neg h center
          _ = phase h (-center) := (phase_neg_real h center).symm
      simp_rw [phase_real_sub, ← Theory.PiDigits.T27.phase_neg, hcenter]
      unfold lagPhaseSum
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    calc
      (∑ j ∈ range (N - r),
          (phase h ((lagOrbitPoint r j - center) - y)).re) =
          (∑ j ∈ range (N - r),
            phase h ((lagOrbitPoint r j - center) - y)).re := by
              simpa only [Complex.reCLM_apply] using
                (map_sum Complex.reCLM _ (range (N - r))).symm
      _ = _ := congrArg Complex.re hcomplex
  rw [intervalIntegral.integral_congr (fun y _ => hpoint y)]
  let c : ℂ := phase h (-center) * lagPhaseSum N r h
  have hcomplexIntegrable : IntervalIntegrable (fun y : ℝ => c * phase (-h) y)
      MeasureTheory.volume (-a) a := by
    apply Continuous.intervalIntegrable
    dsimp [c]
    unfold phase Theory.PiDigits.T27.phase
    fun_prop
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hcomplexIntegrable
  simp only [Complex.reCLM_apply] at hmap
  rw [hmap]
  rw [intervalIntegral.integral_const_mul]

lemma lag_intervalMajorant_sum_eq_doubleFrequencySum
    (n N r H : ℕ) (center : ℝ) :
    (∑ j ∈ range (N - r),
        intervalMajorant n H (lagOrbitPoint r j - center)) =
      (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ u ∈ range (H + 1), ∑ v ∈ range (H + 1),
          ((phase ((v : ℤ) - u) (-center) *
              lagPhaseSum N r ((v : ℤ) - u)) *
            (∫ y in -(majorantRadius n H)..majorantRadius n H,
              phase (-((v : ℤ) - u)) y)).re := by
  have hkernel (x : ℝ) :
      (∫ y in -(majorantRadius n H)..majorantRadius n H,
          fejerKernel H (x - y)) =
        (∑ u ∈ range (H + 1), ∑ v ∈ range (H + 1),
          ∫ y in -(majorantRadius n H)..majorantRadius n H,
            (phase ((v : ℤ) - u) (x - y)).re) / (H + 1 : ℝ) := by
    simp_rw [Theory.PiDigits.T27.fejerKernel_eq_doubleSum]
    simp only [← Complex.reCLM_apply, map_sum]
    rw [intervalIntegral.integral_div]
    congr 1
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro u hu
      rw [intervalIntegral.integral_finsetSum]
      intro v hv
      apply Continuous.intervalIntegrable
      unfold Theory.PiDigits.T27.phase
      fun_prop
    · intro u hu
      apply Continuous.intervalIntegrable
      unfold Theory.PiDigits.T27.phase
      fun_prop
  simp_rw [intervalMajorant, hkernel]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_div]
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply congrArg (· / (H + 1 : ℝ))
  apply congrArg ((fejerMass H)⁻¹ * ·)
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  exact lag_centered_integral_phase_identity N r ((v : ℤ) - u) center
    (majorantRadius n H)

/-- A centered strict circular interval count is bounded by a finite
Fejer/Erdos-Turan expression for the same lag orbit.  This is deterministic:
the exponential sums on the right are displayed, not assumed bounded. -/
theorem lagCircularIntervalCount_le_fourier
    (n N r H : ℕ) (center : ℝ) :
    (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) ≤
      (Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * ((N - r : ℕ) : ℝ) +
        Real.pi ^ 2 / 2 *
          ∑ h ∈ Finset.Icc 1 H,
            energyWeight n H h * ‖lagExponentialSum N r h‖ := by
  let g : ℕ → ℝ := fun h =>
    if h = 0 then 2 * majorantRadius n H * ((N - r : ℕ) : ℝ)
    else energyWeight n H h * ‖lagExponentialSum N r h‖
  have hg : ∀ h, 0 ≤ g h := by
    intro h
    simp only [g]
    split_ifs with hh
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (majorantRadius_pos n H).le) (by positivity)
    · have hhpos : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hh
      apply mul_nonneg
      · apply le_min
        · exact add_nonneg
            (mul_nonneg (by norm_num) (nearReturnRadius_pos n).le)
            (div_nonneg (by norm_num) (by positivity))
        · exact div_nonneg (by norm_num)
            (mul_nonneg Real.pi_pos.le hhpos.le)
      · positivity
  have hfrequency (u v : ℕ) (hu : u ∈ range (H + 1))
      (hv : v ∈ range (H + 1)) :
      (((phase ((v : ℤ) - u) (-center) *
          lagPhaseSum N r ((v : ℤ) - u)) *
        (∫ y in -(majorantRadius n H)..majorantRadius n H,
          phase (-((v : ℤ) - u)) y)).re) ≤
        g (Int.natAbs ((v : ℤ) - u)) := by
    by_cases huv : v = u
    · subst v
      simp [g, lagPhaseSum, phase, Theory.PiDigits.T27.phase,
        intervalIntegral.integral_const]
      ring_nf
      exact le_rfl
    · have hk0 : (v : ℤ) - u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast huv)
      have hkH : Int.natAbs ((v : ℤ) - u) ≤ H := by
        have hu' : u ≤ H := by simpa [Finset.mem_range] using hu
        have hv' : v ≤ H := by simpa [Finset.mem_range] using hv
        omega
      have hlength := norm_integral_phase_le_length (-((v : ℤ) - u))
        (majorantRadius_pos n H).le
      have hfreq := norm_integral_phase_neg_le_frequency hk0 (majorantRadius n H)
      have hintegral :
          ‖∫ y in -(majorantRadius n H)..majorantRadius n H,
              phase (-((v : ℤ) - u)) y‖ ≤
            energyWeight n H (Int.natAbs ((v : ℤ) - u)) := by
        apply le_min
        · rw [two_mul_majorantRadius] at hlength
          exact hlength
        · exact hfreq
      have hnormsum := norm_lagPhaseSum_natAbs N r ((v : ℤ) - u)
      simp only [g, if_neg (Int.natAbs_ne_zero.mpr hk0)]
      calc
        ((phase ((v : ℤ) - u) (-center) *
            lagPhaseSum N r ((v : ℤ) - u)) *
          (∫ y in -(majorantRadius n H)..majorantRadius n H,
            phase (-((v : ℤ) - u)) y)).re ≤
            ‖(phase ((v : ℤ) - u) (-center) *
              lagPhaseSum N r ((v : ℤ) - u)) *
              (∫ y in -(majorantRadius n H)..majorantRadius n H,
                phase (-((v : ℤ) - u)) y)‖ := Complex.re_le_norm _
        _ = ‖lagExponentialSum N r (Int.natAbs ((v : ℤ) - u))‖ *
              ‖∫ y in -(majorantRadius n H)..majorantRadius n H,
                phase (-((v : ℤ) - u)) y‖ := by
              rw [norm_mul, norm_mul, Theory.PiDigits.T27.norm_phase,
                one_mul, hnormsum]
        _ ≤ ‖lagExponentialSum N r (Int.natAbs ((v : ℤ) - u))‖ *
              energyWeight n H (Int.natAbs ((v : ℤ) - u)) :=
            mul_le_mul_of_nonneg_left hintegral (norm_nonneg _)
        _ = _ := by ring
  have hcount : (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) ≤
      ∑ j ∈ range (N - r),
        intervalMajorant n H (lagOrbitPoint r j - center) := by
    have hcard : (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) =
        ∑ j ∈ range (N - r),
          (if circleDistance (lagOrbitPoint r j - center) < decimalRadius n
            then 1 else 0 : ℝ) := by
      let p : ℕ → Prop := fun j =>
        circleDistance (lagOrbitPoint r j - center) < decimalRadius n
      have hcardNat (s : Finset ℕ) : (s.filter p).card =
          ∑ j ∈ s, if p j then 1 else 0 := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih =>
            by_cases hp : p j <;> simp_all
      have hnat := hcardNat (range (N - r))
      change (((range (N - r)).filter p).card : ℝ) = _
      exact_mod_cast hnat
    rw [hcard]
    apply Finset.sum_le_sum
    intro j hj
    simpa [decimalRadius, nearReturnRadius] using
      nearReturnIndicator_le_intervalMajorant n H (lagOrbitPoint r j - center)
  calc
    (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) ≤
        ∑ j ∈ range (N - r),
          intervalMajorant n H (lagOrbitPoint r j - center) := hcount
    _ = (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ u ∈ range (H + 1), ∑ v ∈ range (H + 1),
          ((phase ((v : ℤ) - u) (-center) *
              lagPhaseSum N r ((v : ℤ) - u)) *
            (∫ y in -(majorantRadius n H)..majorantRadius n H,
              phase (-((v : ℤ) - u)) y)).re :=
      lag_intervalMajorant_sum_eq_doubleFrequencySum n N r H center
    _ ≤ (fejerMass H)⁻¹ / (H + 1 : ℝ) *
        ∑ u ∈ range (H + 1), ∑ v ∈ range (H + 1),
          g (Int.natAbs ((v : ℤ) - u)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact hfrequency u v hu hv
      · exact div_nonneg (inv_nonneg.mpr (fejerMass_pos H).le) (by positivity)
    _ ≤ (fejerMass H)⁻¹ *
        (g 0 + 2 * ∑ h ∈ Finset.Icc 1 H, g h) := by
      have hpairs := pairDifference_sum_le H g hg
      calc
        (fejerMass H)⁻¹ / (H + 1 : ℝ) *
            ∑ u ∈ range (H + 1), ∑ v ∈ range (H + 1),
              g (Int.natAbs ((v : ℤ) - u)) ≤
          (fejerMass H)⁻¹ / (H + 1 : ℝ) *
            ((H + 1 : ℝ) *
              (g 0 + 2 * ∑ h ∈ Finset.Icc 1 H, g h)) := by
            exact mul_le_mul_of_nonneg_left hpairs
              (div_nonneg (inv_nonneg.mpr (fejerMass_pos H).le) (by positivity))
        _ = _ := by field_simp
    _ ≤ (Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * ((N - r : ℕ) : ℝ) +
        Real.pi ^ 2 / 2 *
          ∑ h ∈ Finset.Icc 1 H,
            energyWeight n H h * ‖lagExponentialSum N r h‖ := by
      have hzero : g 0 = 2 * majorantRadius n H * ((N - r : ℕ) : ℝ) := by
        simp [g]
      have hpositive : (∑ h ∈ Finset.Icc 1 H, g h) =
          ∑ h ∈ Finset.Icc 1 H,
            energyWeight n H h * ‖lagExponentialSum N r h‖ := by
        apply sum_congr rfl
        intro h hh
        have hh0 : h ≠ 0 := by
          simp only [Finset.mem_Icc] at hh
          omega
        simp [g, hh0]
      rw [hzero, hpositive, mul_add]
      have hzeroBound := majorantCoefficient_zero_le n H
      rw [majorantCoefficient_zero, div_eq_mul_inv, mul_comm] at hzeroBound
      have hsumNonneg : 0 ≤ ∑ h ∈ Finset.Icc 1 H,
          energyWeight n H h * ‖lagExponentialSum N r h‖ := by
        apply sum_nonneg
        intro h hh
        have hhpos : 0 < (h : ℝ) := by
          simp only [Finset.mem_Icc] at hh
          exact_mod_cast hh.1
        exact mul_nonneg (by
          apply le_min
          · exact add_nonneg
              (mul_nonneg (by norm_num) (nearReturnRadius_pos n).le)
              (div_nonneg (by norm_num) (by positivity))
          · exact div_nonneg (by norm_num)
              (mul_nonneg Real.pi_pos.le hhpos.le)) (norm_nonneg _)
      calc
        (fejerMass H)⁻¹ *
            (2 * majorantRadius n H * ((N - r : ℕ) : ℝ)) +
          (fejerMass H)⁻¹ *
            (2 * ∑ h ∈ Finset.Icc 1 H,
              energyWeight n H h * ‖lagExponentialSum N r h‖) ≤
          (Real.pi ^ 2 / 2 * nearReturnRadius n +
              Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * ((N - r : ℕ) : ℝ) +
            (Real.pi ^ 2 / 4) *
              (2 * ∑ h ∈ Finset.Icc 1 H,
                energyWeight n H h * ‖lagExponentialSum N r h‖) := by
          apply add_le_add
          · calc
              (fejerMass H)⁻¹ *
                  (2 * majorantRadius n H * ((N - r : ℕ) : ℝ)) =
                ((fejerMass H)⁻¹ * (2 * majorantRadius n H)) *
                  ((N - r : ℕ) : ℝ) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hzeroBound (by positivity)
          · exact mul_le_mul_of_nonneg_right (inv_fejerMass_le H)
              (mul_nonneg (by norm_num) hsumNonneg)
        _ = _ := by
          rw [show nearReturnRadius n = decimalRadius n by rfl]
          ring

/-- Supremum-level circular Erdos-Turan specialization for the lag orbit.
The right side consists only of explicit deterministic terms and the displayed
finite exponential sums. -/
theorem lagCircularIntervalDiscrepancy_le_fourier
    (n N r H : ℕ) :
    lagCircularIntervalDiscrepancy N r (decimalRadius n) ≤
      (2 * decimalRadius n + Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * ((N - r : ℕ) : ℝ) +
        Real.pi ^ 2 / 2 *
          ∑ h ∈ Finset.Icc 1 H,
            energyWeight n H h * ‖lagExponentialSum N r h‖ := by
  apply csSup_le (Set.range_nonempty _)
  rintro d ⟨center, rfl⟩
  have hcount := lagCircularIntervalCount_le_fourier n N r H center
  have hcount0 : 0 ≤ (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) :=
    by positivity
  have hexpected0 : 0 ≤ 2 * decimalRadius n * ((N - r : ℕ) : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (decimalRadius_pos n).le) (by positivity)
  calc
    |(lagCircularIntervalCount N r (decimalRadius n) center : ℝ) -
        2 * decimalRadius n * ((N - r : ℕ) : ℝ)| ≤
      (lagCircularIntervalCount N r (decimalRadius n) center : ℝ) +
        2 * decimalRadius n * ((N - r : ℕ) : ℝ) := by
          simpa [abs_of_nonneg hcount0, abs_of_nonneg hexpected0] using
            abs_sub (lagCircularIntervalCount N r (decimalRadius n) center : ℝ)
              (2 * decimalRadius n * ((N - r : ℕ) : ℝ))
    _ ≤ (2 * decimalRadius n + Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * ((N - r : ℕ) : ℝ) +
        Real.pi ^ 2 / 2 *
          ∑ h ∈ Finset.Icc 1 H,
            energyWeight n H h * ‖lagExponentialSum N r h‖ := by
      nlinarith

/-- Large normalized circular discrepancy on a lag orbit forces one explicit
low harmonic to resonate.  The stronger radius hypothesis separates an
upper excess from the trivial possible lower deficit. -/
theorem longLagDiscrepancy_implies_resonance
    (A n N r : ℕ) (hA : 1 ≤ A) (hn : 1 ≤ n)
    (hr : r ∈ Finset.Icc 1 (N - 1))
    (hradius : 256 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1)
    (hdisc : 1 / (8 * (A : ℝ) * (n : ℝ)) ≤
      lagCircularIntervalDiscrepancy N r (decimalRadius n) /
        ((N - r : ℕ) : ℝ)) :
    ∃ h ∈ Finset.Icc 1 (256 * A * n),
      ((N - r : ℕ) : ℝ) /
          (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) <
        ‖lagExponentialSum N r h‖ := by
  have hrBounds := Finset.mem_Icc.mp hr
  have hlengthNat : 0 < N - r := by omega
  have hlength : 0 < ((N - r : ℕ) : ℝ) := by exact_mod_cast hlengthNat
  have hAN : 0 < (A : ℝ) * (n : ℝ) := by positivity
  have hdiscMul :
      ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) ≤
        lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
    have hm := (le_div_iff₀ hlength).mp hdisc
    calc
      ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) =
          (1 / (8 * (A : ℝ) * (n : ℝ))) * ((N - r : ℕ) : ℝ) := by ring
      _ ≤ _ := hm
  have htarget :
      ((N - r : ℕ) : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) <
        lagCircularIntervalDiscrepancy N r (decimalRadius n) := by
    have hhalf :
        ((N - r : ℕ) : ℝ) / (16 * ((A : ℝ) * (n : ℝ))) <
          ((N - r : ℕ) : ℝ) / (8 * ((A : ℝ) * (n : ℝ))) := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 16 * ((A : ℝ) * (n : ℝ)))
        (by positivity : 0 < 8 * ((A : ℝ) * (n : ℝ)))]
      nlinarith
    exact hhalf.trans_le hdiscMul
  obtain ⟨d, ⟨center, rfl⟩, hcenter⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) htarget
  let M : ℝ := ((N - r : ℕ) : ℝ)
  let C : ℝ := (lagCircularIntervalCount N r (decimalRadius n) center : ℝ)
  have hM : 0 < M := hlength
  have hC : 0 ≤ C := by positivity
  have hexpected0 : 0 ≤ 2 * decimalRadius n * M :=
    mul_nonneg (mul_nonneg (by norm_num) (decimalRadius_pos n).le) hM.le
  have hexpectedSmall :
      2 * decimalRadius n * M ≤ M / (128 * ((A : ℝ) * (n : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_right hradius hM.le
    dsimp [M]
    apply (le_div_iff₀ (by positivity :
      0 < 128 * ((A : ℝ) * (n : ℝ)))).2
    nlinarith
  have htargetCenter : M / (16 * ((A : ℝ) * (n : ℝ))) <
      |C - 2 * decimalRadius n * M| := by
    simpa only [M, C] using hcenter
  have hupperExcess : 0 < C - 2 * decimalRadius n * M := by
    by_contra hnonpos
    have habs : |C - 2 * decimalRadius n * M| =
        2 * decimalRadius n * M - C := by
      simpa only [neg_sub] using abs_of_nonpos (le_of_not_gt hnonpos)
    rw [habs] at htargetCenter
    have htargetExpected :
        M / (16 * ((A : ℝ) * (n : ℝ))) <
          2 * decimalRadius n * M := htargetCenter.trans_le (sub_le_self _ hC)
    have hsmallTarget : M / (128 * ((A : ℝ) * (n : ℝ))) <
        M / (16 * ((A : ℝ) * (n : ℝ))) := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 128 * ((A : ℝ) * (n : ℝ)))
        (by positivity : 0 < 16 * ((A : ℝ) * (n : ℝ)))]
      nlinarith
    exact (not_lt_of_ge hexpectedSmall) (hsmallTarget.trans htargetExpected)
  have hcountLower :
      M / (16 * ((A : ℝ) * (n : ℝ))) < C := by
    rw [abs_of_pos hupperExcess] at htargetCenter
    exact htargetCenter.trans (sub_lt_self _
      (mul_pos (mul_pos (by norm_num) (decimalRadius_pos n)) hM))
  let H : ℕ := 256 * A * n
  let S : ℝ := ∑ h ∈ Finset.Icc 1 H,
    energyWeight n H h * ‖lagExponentialSum N r h‖
  have hfourier : C ≤
      (Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * M +
        Real.pi ^ 2 / 2 * S := by
    simpa only [C, M, S] using
      lagCircularIntervalCount_le_fourier n N r H center
  have hpiSq : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfirstCoeff :
      Real.pi ^ 2 / 2 * decimalRadius n ≤
        1 / (32 * ((A : ℝ) * (n : ℝ))) := by
    have hpiHalf : Real.pi ^ 2 / 2 < 8 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hradius
      (show 0 ≤ (1 : ℝ) / (256 * ((A : ℝ) * (n : ℝ))) by positivity)
    have hrho : decimalRadius n ≤
        1 / (256 * ((A : ℝ) * (n : ℝ))) := by
      apply (le_div_iff₀ (by positivity :
        0 < 256 * ((A : ℝ) * (n : ℝ)))).2
      nlinarith
    calc
      Real.pi ^ 2 / 2 * decimalRadius n ≤
          8 * decimalRadius n :=
        mul_le_mul_of_nonneg_right hpiHalf.le (decimalRadius_pos n).le
      _ ≤ 8 * (1 / (256 * ((A : ℝ) * (n : ℝ)))) := by gcongr
      _ = 1 / (32 * ((A : ℝ) * (n : ℝ))) := by field_simp; ring
  have hHreal : (256 : ℝ) * ((A : ℝ) * (n : ℝ)) = (H : ℝ) := by
    dsimp [H]
    push_cast
    ring
  have hsecondCoeff :
      Real.pi ^ 2 / (4 * (H + 1 : ℝ)) <
        1 / (64 * ((A : ℝ) * (n : ℝ))) := by
    have hdenLeft : 0 < 4 * (H + 1 : ℝ) := by positivity
    have hdenRight : 0 < 64 * ((A : ℝ) * (n : ℝ)) := by positivity
    rw [div_lt_div_iff₀ hdenLeft hdenRight]
    rw [← hHreal]
    nlinarith
  have hbaseline :
      (Real.pi ^ 2 / 2 * decimalRadius n +
          Real.pi ^ 2 / (4 * (H + 1 : ℝ))) * M <
        3 * M / (64 * ((A : ℝ) * (n : ℝ))) := by
    have hcoeff :
        Real.pi ^ 2 / 2 * decimalRadius n +
            Real.pi ^ 2 / (4 * (H + 1 : ℝ)) <
          3 / (64 * ((A : ℝ) * (n : ℝ))) := by
      calc
        _ < 1 / (32 * ((A : ℝ) * (n : ℝ))) +
            1 / (64 * ((A : ℝ) * (n : ℝ))) :=
          add_lt_add_of_le_of_lt hfirstCoeff hsecondCoeff
        _ = 3 / (64 * ((A : ℝ) * (n : ℝ))) := by field_simp; ring
    have := mul_lt_mul_of_pos_right hcoeff hM
    convert this using 1 <;> ring
  have henergy : M / (64 * ((A : ℝ) * (n : ℝ))) <
      Real.pi ^ 2 / 2 * S := by
    have hsplit : M / (16 * ((A : ℝ) * (n : ℝ))) =
        3 * M / (64 * ((A : ℝ) * (n : ℝ))) +
          M / (64 * ((A : ℝ) * (n : ℝ))) := by
      field_simp
      ring
    nlinarith
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    apply sum_nonneg
    intro h hh
    have hhpos : 0 < (h : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).1
    exact mul_nonneg (by
      apply le_min
      · exact add_nonneg
          (mul_nonneg (by norm_num) (nearReturnRadius_pos n).le)
          (div_nonneg (by norm_num) (by positivity))
      · exact div_nonneg (by norm_num)
          (mul_nonneg Real.pi_pos.le hhpos.le)) (norm_nonneg _)
  have hsumLower : M / (512 * ((A : ℝ) * (n : ℝ))) < S := by
    have hSpos : 0 < S := by
      by_contra hnotpos
      have hSle : S ≤ 0 := le_of_not_gt hnotpos
      have hcoefPos : 0 < Real.pi ^ 2 / 2 := by positivity
      have : Real.pi ^ 2 / 2 * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoefPos.le hSle
      exact (not_lt_of_ge this) (henergy.trans' (by positivity))
    have henergyUpper : Real.pi ^ 2 / 2 * S < 8 * S :=
      mul_lt_mul_of_pos_right (by nlinarith : Real.pi ^ 2 / 2 < 8)
        hSpos
    have hscale : M / (64 * ((A : ℝ) * (n : ℝ))) / 8 =
        M / (512 * ((A : ℝ) * (n : ℝ))) := by field_simp; ring
    rw [← hscale]
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)).2
      (by simpa [mul_comm] using henergy.trans henergyUpper)
  by_contra hnone
  push Not at hnone
  have hweight_le_one : ∀ h ∈ Finset.Icc 1 H, energyWeight n H h ≤ 1 := by
    intro h hh
    have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
    have hhreal : (1 : ℝ) ≤ h := by exact_mod_cast hh1
    calc
      energyWeight n H h ≤ 1 / (Real.pi * (h : ℝ)) := min_le_right _ _
      _ ≤ 1 := by
        have hden : 1 ≤ Real.pi * (h : ℝ) := by
          calc
            (1 : ℝ) ≤ 1 * (h : ℝ) := by simpa using hhreal
            _ ≤ Real.pi * (h : ℝ) :=
              mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (by positivity)
        exact (div_le_one (by positivity)).2 hden
  have hterm : ∀ h ∈ Finset.Icc 1 H,
      energyWeight n H h * ‖lagExponentialSum N r h‖ ≤
        M / (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
    intro h hh
    calc
      energyWeight n H h * ‖lagExponentialSum N r h‖ ≤
          1 * ‖lagExponentialSum N r h‖ :=
        mul_le_mul_of_nonneg_right (hweight_le_one h hh) (norm_nonneg _)
      _ ≤ M / (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        simpa using hnone h hh
  have hcard : (Finset.Icc 1 H).card = H := by
    simp [Nat.card_Icc]
  have hsumUpper : S ≤ M / (512 * ((A : ℝ) * (n : ℝ))) := by
    calc
      S ≤ ∑ _h ∈ Finset.Icc 1 H,
          M / (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        exact Finset.sum_le_sum fun h hh => hterm h hh
      _ = (H : ℝ) *
          (M / (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2)) := by
        simp [hcard]
      _ = M / (512 * ((A : ℝ) * (n : ℝ))) := by
        rw [← hHreal]
        field_simp
        ring
  exact (not_lt_of_ge hsumUpper hsumLower)

/-- Literal failure of canonical C1 forces arbitrarily long lag orbits with
an explicit low-harmonic resonance.  The requested orbit length `K` is chosen
before `N`; all constants and positivity conditions occur in the type. -/
theorem not_canonical_C1_implies_arbitrarily_long_lag_resonance
    (hnot : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ ∀ K : ℕ, 1 ≤ K →
        ∃ N r h : ℕ,
          N = 16 * A * n * K ∧
          r ∈ Finset.Icc 1 (N - 1) ∧
          K ≤ N - r ∧
          h ∈ Finset.Icc 1 (256 * A * n) ∧
          ((N - r : ℕ) : ℝ) /
              (131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2) <
            ‖∑ j ∈ range (N - r),
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
                  ((((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi) : ℝ) : ℂ))‖ := by
  push Not at hnot
  obtain ⟨A, hA, hbad⟩ := hnot
  have h32A : 1 ≤ 32 * A := by
    have hpos : 0 < 32 * A := Nat.mul_pos (by norm_num) (by omega)
    exact hpos
  obtain ⟨nRadius, hnRadius, hRadius⟩ :=
    eventually_eight_mul_scaled_decimalRadius_le_one (32 * A) h32A
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  have hmax : 1 ≤ max n0 nRadius := hn0.trans (le_max_left _ _)
  obtain ⟨n, hnmax, hbadN⟩ := hbad (max n0 nRadius) hmax
  have hn0n : n0 ≤ n := (le_max_left n0 nRadius).trans hnmax
  have hnRadiusN : nRadius ≤ n := (le_max_right n0 nRadius).trans hnmax
  have hn : 1 ≤ n := hn0.trans hn0n
  have hRadiusRaw := hRadius n hnRadiusN
  have hRadius256 :
      256 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1 := by
    convert hRadiusRaw using 1 <;> push_cast <;> ring
  refine ⟨n, hn0n, hn, ?_⟩
  intro K hK
  let N : ℕ := 16 * A * n * K
  have hANpos : 0 < A * n := Nat.mul_pos (by omega) (by omega)
  have hN : 1 ≤ N := by
    dsimp [N]
    have : 0 < 16 * A * n * K := by
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))
        (by omega)
    exact this
  have hNlarge : 8 * A * n ≤ N := by
    dsimp [N]
    have hKpos : 0 < K := by omega
    nlinarith
  have hRadius8 :
      8 * (A : ℝ) * (n : ℝ) * decimalRadius n ≤ 1 := by
    have hrho := (decimalRadius_pos n).le
    nlinarith
  obtain ⟨r, hr, hlong, hdisc⟩ := badFinite_nearReturn_implies_longLag
    A n N hA hn hNlarge hRadius8 (hbadN N hN)
  obtain ⟨h, hh, hres⟩ :=
    longLagDiscrepancy_implies_resonance A n N r hA hn hr hRadius256 hdisc
  have hKlength : K ≤ N - r := by
    have hmul : (16 * A * n) * K ≤ (16 * A * n) * (N - r) := by
      simpa [N, mul_assoc] using hlong
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  refine ⟨N, r, h, rfl, hr, hKlength, hh, ?_⟩
  simpa only [lagExponentialSum, lagOrbitPoint] using hres

end LongLagResonance
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.LongLagResonance.lagCircularIntervalDiscrepancy_le_length
#print axioms DecimalFactorComplexity.LongLagResonance.shortLagDiscrepancy_sum_le
#print axioms DecimalFactorComplexity.LongLagResonance.finite_nearReturn_or_longLag_dichotomy
#print axioms DecimalFactorComplexity.LongLagResonance.badFinite_nearReturn_implies_longLag
#print axioms DecimalFactorComplexity.LongLagResonance.lagCircularIntervalCount_le_fourier
#print axioms DecimalFactorComplexity.LongLagResonance.lagCircularIntervalDiscrepancy_le_fourier
#print axioms DecimalFactorComplexity.LongLagResonance.longLagDiscrepancy_implies_resonance
#print axioms DecimalFactorComplexity.LongLagResonance.not_canonical_C1_implies_arbitrarily_long_lag_resonance
