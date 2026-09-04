import TheoryLib.PiQuantitativeBlockHitting.T202T202RamanujanTwoAdicRamp
import Mathlib

/-!
# T216: reciprocal coefficient valuation

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t216; each task compiled and
axiom-checked; assembled by Claude Opus 5

Tasks 04 and 05 of the pack are not included: they were not proved.
-/

noncomputable section

namespace Theory.PiDigits.T216ReciprocalCoefficientValuation

open scoped BigOperators

abbrev RawComposition (n : ℕ) :=
  Σ k : Fin (n + 1), Fin k.1 → Fin (n + 1)

def IsComposition (n : ℕ) (c : RawComposition n) : Prop :=
  (∑ i, (c.2 i).1) = n ∧ ∀ i, 0 < (c.2 i).1

abbrev CompositionOf (n : ℕ) :=
  {c : RawComposition n // IsComposition n c}

noncomputable instance compositionFintype (n : ℕ) :
    Fintype (CompositionOf n) := Fintype.ofFinite _

def compLength {n : ℕ} (c : CompositionOf n) : ℕ := c.1.1.1

def compPart {n : ℕ} (c : CompositionOf n)
    (i : Fin (compLength c)) : ℕ := (c.1.2 i).1

def compWeight {n : ℕ} (v : ℕ → ℕ) (c : CompositionOf n) : ℕ :=
  ∑ i, v (compPart c i)

def compTerm {n : ℕ} (a : ℕ → ℤ) (c : CompositionOf n) : ℤ :=
  (-1 : ℤ) ^ compLength c * ∏ i, a (compPart c i)

noncomputable def reciprocalCoeff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ c : CompositionOf n, compTerm a c

def IsMinCompWeight (v : ℕ → ℕ) (n q : ℕ) : Prop :=
  (∃ c : CompositionOf n, compWeight v c = q) ∧
    ∀ c : CompositionOf n, q ≤ compWeight v c

noncomputable def minimumNormalizedSum
    (a : ℕ → ℤ) (v : ℕ → ℕ) (n q : ℕ) : ℤ :=
  ∑ c : CompositionOf n,
    if compWeight v c = q then compTerm a c / (2 : ℤ) ^ q else 0

def ramanujanCoeff (n : ℕ) : ℤ :=
  ((((6 * n + 1) *
    Theory.PiDigits.T202RamanujanDyadicRamp.centralCube n : ℕ)) : ℤ)

def ramanujanWeight (n : ℕ) : ℕ :=
  3 * Theory.PiDigits.T202RamanujanDyadicRamp.binaryDigitSum n

noncomputable def ramanujanReciprocalCoeff (n : ℕ) : ℤ :=
  reciprocalCoeff ramanujanCoeff n

def decimalValInt (z : ℤ) : ℕ :=
  min (padicValInt 2 z) (padicValInt 5 z)

lemma reciprocalCoeff_composition_sum (a : ℕ → ℤ) (n : ℕ) :
    reciprocalCoeff a n =
      ∑ c : CompositionOf n,
        (-1 : ℤ) ^ compLength c * ∏ i, a (compPart c i) := by
  rfl

lemma two_pow_v_dvd {a : ℕ → ℤ} {v : ℕ → ℕ}
    (ha : ∀ k, 0 < k → v k ≤ padicValInt 2 (a k)) {k : ℕ} (hk : 0 < k) :
    (2 : ℤ) ^ v k ∣ a k := by
  have h1 : ((2 : ℕ) : ℤ) ^ v k ∣ a k := by
    rw [padicValInt_dvd_iff_of_ne_one (by norm_num)]
    exact Or.inr (ha k hk)
  simpa using h1

lemma two_pow_weight_dvd_compTerm {a : ℕ → ℤ} {v : ℕ → ℕ} {n : ℕ}
    (ha : ∀ k, 0 < k → v k ≤ padicValInt 2 (a k)) (c : CompositionOf n) :
    (2 : ℤ) ^ compWeight v c ∣ compTerm a c := by
  have hprod : (2 : ℤ) ^ compWeight v c
      = ∏ i : Fin (compLength c), (2 : ℤ) ^ v (compPart c i) := by
    rw [compWeight, Finset.prod_pow_eq_pow_sum]
  rw [compTerm, hprod]
  refine Dvd.dvd.mul_left ?_ _
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro i _
  exact two_pow_v_dvd ha (c.2.2 i)

lemma valuation_ge_minCompWeight
    {a : ℕ → ℤ} {v : ℕ → ℕ} {n q : ℕ}
    (hmin : IsMinCompWeight v n q)
    (ha : ∀ k, 0 < k → v k ≤ padicValInt 2 (a k))
    (hne : reciprocalCoeff a n ≠ 0) :
    q ≤ padicValInt 2 (reciprocalCoeff a n) := by
  have hdvd : ((2 : ℕ) : ℤ) ^ q ∣ reciprocalCoeff a n := by
    have : (2 : ℤ) ^ q ∣ reciprocalCoeff a n := by
      rw [reciprocalCoeff]
      refine Finset.dvd_sum ?_
      intro c _
      exact dvd_trans (pow_dvd_pow 2 (hmin.2 c)) (two_pow_weight_dvd_compTerm ha c)
    simpa using this
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) q
    (reciprocalCoeff a n)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

lemma minimum_layer_odd_no_cancel
    {a : ℕ → ℤ} {v : ℕ → ℕ} {n q : ℕ}
    (hmin : IsMinCompWeight v n q)
    (hdiv : ∀ c : CompositionOf n,
      (2 : ℤ) ^ compWeight v c ∣ compTerm a c)
    (hodd : Odd (minimumNormalizedSum a v n q)) :
    ∃ z : ℤ, reciprocalCoeff a n = (2 : ℤ) ^ q * z ∧ Odd z := by
  have hne0 : ((2 : ℤ) ^ q) ≠ 0 := by positivity
  have hq_dvd : ∀ c : CompositionOf n, (2 : ℤ) ^ q ∣ compTerm a c := fun c =>
    dvd_trans (pow_dvd_pow 2 (hmin.2 c)) (hdiv c)
  refine ⟨∑ c : CompositionOf n, compTerm a c / (2 : ℤ) ^ q, ?_, ?_⟩
  · rw [reciprocalCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    exact (Int.mul_ediv_cancel' (hq_dvd c)).symm
  · have hsplit : (∑ c : CompositionOf n, compTerm a c / (2 : ℤ) ^ q)
        = minimumNormalizedSum a v n q
          + ∑ c : CompositionOf n,
              (if compWeight v c = q then 0 else compTerm a c / (2 : ℤ) ^ q) := by
      simp only [minimumNormalizedSum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro c _
      by_cases h : compWeight v c = q <;> simp [h]
    have h2 : (2 : ℤ) ∣ ∑ c : CompositionOf n,
        (if compWeight v c = q then 0 else compTerm a c / (2 : ℤ) ^ q) := by
      refine Finset.dvd_sum ?_
      intro c _
      by_cases h : compWeight v c = q
      · simp [h]
      · simp only [h, if_false]
        have hlt : q < compWeight v c :=
          lt_of_le_of_ne (hmin.2 c) (fun hh => h hh.symm)
        obtain ⟨t, ht⟩ := hdiv c
        have hpow : (2 : ℤ) ^ compWeight v c
            = (2 : ℤ) ^ q * (2 : ℤ) ^ (compWeight v c - q) := by
          rw [← pow_add]
          congr 1
          omega
        have hdiveq : compTerm a c / (2 : ℤ) ^ q
            = (2 : ℤ) ^ (compWeight v c - q) * t := by
          rw [ht, hpow, mul_assoc, Int.mul_ediv_cancel_left _ hne0]
        rw [hdiveq]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) t
    rw [hsplit]
    exact hodd.add_even ((even_iff_two_dvd).mpr h2)

theorem reciprocal_coefficients_cauchy_bound
    {F : ℂ → ℂ} {c ρ : ℕ → ℂ}
    (hF : HasFPowerSeriesOnBall F
      (FormalMultilinearSeries.ofScalars ℂ c) 0
      (ENNReal.ofReal ((1 : ℝ) / 64)))
    (hclose : ∀ z : ℂ, ‖z‖ ≤ (1 : ℝ) / 256 →
      ‖F z - 1‖ ≤ 4 / Real.pi - 1)
    (hrho : HasFPowerSeriesAt (fun z : ℂ => (F z)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ ρ) 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ Λ : ℝ, 0 < Λ ∧ Λ < 256 ∧
      ∀ n : ℕ, ‖ρ n‖ ≤ C * Λ ^ n := by
  -- the strict numerical bound `4/π - 1 < 1`
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi0 : (0 : ℝ) < Real.pi := by linarith
  have hbound : 4 / Real.pi - 1 < 1 := by
    have h4 : 4 / Real.pi < 2 := by
      rw [div_lt_iff₀ hpi0]; linarith
    linarith
  -- `F` is analytic, hence continuous, on the open ball of radius `1/64`
  have hFan : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) (1 / 64)) := by
    have h := hF.analyticOnNhd
    rwa [Metric.eball_ofReal] at h
  have hFcont : ContinuousOn F (Metric.ball (0 : ℂ) (1 / 64)) := hFan.continuousOn
  -- the open zero-free neighbourhood of the closed `1/256` disk
  set U : Set ℂ :=
    Metric.ball (0 : ℂ) (1 / 64) ∩ (fun z : ℂ => ‖F z - 1‖) ⁻¹' (Set.Iio 1) with hUdef
  have hUopen : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ Metric.isOpen_ball isOpen_Iio
    exact (hFcont.sub continuousOn_const).norm
  have hsub : Metric.closedBall (0 : ℂ) (1 / 256) ⊆ U := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]; linarith
    · simp only [Set.mem_preimage, Set.mem_Iio]
      exact lt_of_le_of_lt (hclose z hz) hbound
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall (0 : ℂ) (1 / 256)).exists_thickening_subset_open hUopen hsub
  rw [thickening_closedBall hδ (by norm_num)] at hδsub
  -- a slightly larger zero-free closed disk
  set R : ℝ := min (δ / 2 + 1 / 256) (1 / 128) with hRdef
  have hR1 : (1 : ℝ) / 256 < R := by
    rw [hRdef]; refine lt_min ?_ ?_ <;> linarith
  have hR2 : R < δ + 1 / 256 := by
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    linarith
  have hRle : R ≤ 1 / 128 := min_le_right _ _
  have hR0 : (0 : ℝ) < R := by linarith
  set Rn : NNReal := ⟨R, hR0.le⟩ with hRndef
  have hRcoe : (Rn : ℝ) = R := rfl
  have hclosedsub : Metric.closedBall (0 : ℂ) (Rn : ℝ) ⊆ U := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, hRcoe] at hz
    refine hδsub ?_
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hFne : ∀ z ∈ Metric.closedBall (0 : ℂ) (Rn : ℝ), F z ≠ 0 := by
    intro z hz hFz
    have h := (hclosedsub hz).2
    simp only [Set.mem_preimage, Set.mem_Iio, hFz] at h
    norm_num at h
  have hGdiff : DifferentiableOn ℂ (fun z : ℂ => (F z)⁻¹)
      (Metric.closedBall (0 : ℂ) (Rn : ℝ)) := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) (1 / 64) := (hclosedsub hz).1
    have hFd : DifferentiableAt ℂ F z := (hFan z hzb).differentiableAt
    exact (hFd.inv (hFne z hz)).differentiableWithinAt
  have hRnpos : 0 < Rn := hR0
  have hG := hGdiff.hasFPowerSeriesOnBall hRnpos
  have heq : cauchyPowerSeries (fun z : ℂ => (F z)⁻¹) 0 Rn
      = FormalMultilinearSeries.ofScalars ℂ ρ :=
    hG.hasFPowerSeriesAt.eq_formalMultilinearSeries hrho
  rw [heq] at hG
  have hrad : (Rn : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ ρ).radius := hG.r_le
  -- a Cauchy estimate on an intermediate radius
  set rr : ℝ := (1 / 256 + R) / 2 with hrrdef
  have hrr1 : (1 : ℝ) / 256 < rr := by rw [hrrdef]; linarith
  have hrr2 : rr < R := by rw [hrrdef]; linarith
  have hrr0 : (0 : ℝ) < rr := by linarith
  set rn : NNReal := ⟨rr, hrr0.le⟩ with hrndef
  have hrcoe : (rn : ℝ) = rr := rfl
  have hltnn : rn < Rn := hrr2
  have hlt : (rn : ENNReal)
      < (FormalMultilinearSeries.ofScalars ℂ ρ).radius :=
    lt_of_lt_of_le (by exact_mod_cast hltnn) hrad
  obtain ⟨C, hC, hCb⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ ρ).norm_mul_pow_le_of_lt_radius hlt
  refine ⟨C, hC, 1 / rr, by positivity, ?_, ?_⟩
  · rw [div_lt_iff₀ hrr0]; linarith
  · intro n
    have h1 := hCb n
    rw [FormalMultilinearSeries.ofScalars_norm, hrcoe] at h1
    have hp : (0 : ℝ) < rr ^ n := by positivity
    rw [div_pow, one_pow, mul_one_div, le_div_iff₀ hp]
    exact h1

end Theory.PiDigits.T216ReciprocalCoefficientValuation
