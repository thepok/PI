import TheoryLib.PiQuantitativeBlockHitting.T104T104BBPSeriesIdentity

/-!
# T200: Bailey–Crandall coefficient and analytic coboundary

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 (wave E2, one task per lemma, four parallel), against the contracted
signatures of AllMath task pack t200; gate-checked per task; assembled by Codex
-/

noncomputable section
open scoped BigOperators
namespace Theory.PiDigits.T200BaileyCrandallCoboundary

def g (x : ℝ) : ℝ :=
  (1 - x) * (x ^ 2 + 2) * (x ^ 2 + 2 * x + 2)

def R (n : ℕ) : ℝ :=
  4 / (8 * n + 1) - 2 / (8 * n + 4) -
    1 / (8 * n + 5) - 1 / (8 * n + 6)

def tau (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x / (16 - x ^ 8)

def Y (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (16 : ℝ) ^ (n - 1 - k) * R k


namespace CoefficientIntegralProof

theorem g_expand (x : ℝ) : g x = 4 - 2 * x ^ 3 - x ^ 4 - x ^ 5 := by
  unfold g
  ring

theorem integrand_expand (n : ℕ) (x : ℝ) :
    x ^ (8 * n) * g x =
      4 * x ^ (8 * n) - 2 * x ^ (8 * n + 3) - x ^ (8 * n + 4) - x ^ (8 * n + 5) := by
  have e3 : x ^ (8 * n + 3) = x ^ (8 * n) * x ^ 3 := by rw [pow_add]
  have e4 : x ^ (8 * n + 4) = x ^ (8 * n) * x ^ 4 := by rw [pow_add]
  have e5 : x ^ (8 * n + 5) = x ^ (8 * n) * x ^ 5 := by rw [pow_add]
  rw [e3, e4, e5, g_expand]
  ring

theorem integral_pow_zero_one (m : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m) = 1 / ((m : ℝ) + 1) := by
  have hn : (m + 1 : ℝ) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (1 : ℝ),
      HasDerivAt (fun y : ℝ ↦ y ^ (m + 1) / (m + 1 : ℝ)) (x ^ m) x := by
    intro x _
    convert ((hasDerivAt_id x).pow (m + 1)).div_const (m + 1 : ℝ) using 1;
      simp only [id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
    field_simp
  have hval : (∫ x in (0 : ℝ)..1, x ^ m) =
      (1 : ℝ) ^ (m + 1) / (m + 1 : ℝ) - (0 : ℝ) ^ (m + 1) / (m + 1 : ℝ) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_pow m).continuousOn.intervalIntegrable (a := (0 : ℝ)) (b := 1))
    simpa only [] using this
  rw [hval, one_pow]
  have hm1 : m + 1 ≠ 0 := by omega
  rw [zero_pow hm1, zero_div, sub_zero]

end CoefficientIntegralProof

open CoefficientIntegralProof

theorem R_eq_intervalIntegral (n : ℕ) :
    R n = ∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x := by
  have h0 : IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * n)) MeasureTheory.volume 0 1 :=
    (continuous_pow (8 * n)).continuousOn.intervalIntegrable
  have h3 : IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * n + 3)) MeasureTheory.volume 0 1 :=
    (continuous_pow (8 * n + 3)).continuousOn.intervalIntegrable
  have h4 : IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * n + 4)) MeasureTheory.volume 0 1 :=
    (continuous_pow (8 * n + 4)).continuousOn.intervalIntegrable
  have h5 : IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * n + 5)) MeasureTheory.volume 0 1 :=
    (continuous_pow (8 * n + 5)).continuousOn.intervalIntegrable
  have hcongr : (∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x) =
      ∫ x in (0 : ℝ)..1,
        (4 * x ^ (8 * n) - 2 * x ^ (8 * n + 3) - x ^ (8 * n + 4) - x ^ (8 * n + 5)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact integrand_expand n x
  have hA : IntervalIntegrable (fun x : ℝ ↦ 4 * x ^ (8 * n)) MeasureTheory.volume 0 1 :=
    h0.const_mul 4
  have hB : IntervalIntegrable (fun x : ℝ ↦ 2 * x ^ (8 * n + 3)) MeasureTheory.volume 0 1 :=
    h3.const_mul 2
  have hC : IntervalIntegrable (fun x : ℝ ↦ (4 * x ^ (8 * n) - 2 * x ^ (8 * n + 3))) MeasureTheory.volume 0 1 :=
    hA.sub hB
  have hD : IntervalIntegrable (fun x : ℝ ↦ (4 * x ^ (8 * n) - 2 * x ^ (8 * n + 3) - x ^ (8 * n + 4))) MeasureTheory.volume 0 1 :=
    hC.sub h4
  rw [hcongr,
    intervalIntegral.integral_sub hD h5,
    intervalIntegral.integral_sub hC h4,
    intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow_zero_one, integral_pow_zero_one,
    integral_pow_zero_one, integral_pow_zero_one]
  unfold R
  push_cast
  have h1 : ((8 : ℝ) * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((8 : ℝ) * (n : ℝ) + 4) ≠ 0 := by positivity
  have h3' : ((8 : ℝ) * (n : ℝ) + 5) ≠ 0 := by positivity
  have h4' : ((8 : ℝ) * (n : ℝ) + 6) ≠ 0 := by positivity
  field_simp
  ring

theorem R_div_pow_eq_bbpRealTerm (n : ℕ) :
    R n / (16 : ℝ) ^ n =
      Theory.PiDigits.T100BBPRealBridge.bbpRealTerm n := by
  simp only [R, Theory.PiDigits.T100BBPRealBridge.bbpRealTerm,
    Theory.PiDigits.T98BBPArchimedeanTerm.bbpCombinedTerm,
    Theory.PiDigits.T74ThreePrimaryDecimation.poleOne,
    Theory.PiDigits.T74ThreePrimaryDecimation.poleTwo,
    Theory.PiDigits.T74ThreePrimaryDecimation.poleThree,
    Theory.PiDigits.T74ThreePrimaryDecimation.poleFour]
  push_cast
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (8 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (8 * (n : ℝ) + 4) ≠ 0 := by positivity
  have h3 : (8 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h4 : (8 * (n : ℝ) + 6) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h6 : (4 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem g_expand (x : ℝ) : g x = 4 - x ^ 5 - x ^ 4 - 2 * x ^ 3 := by
  unfold g
  ring

theorem g_pos_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < g x := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have h3 : x ^ 3 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have h4 : x ^ 4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have h5 : x ^ 5 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  rw [g_expand]
  linarith

theorem denom_pos_on_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < (16 : ℝ) - x ^ 8 := by
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have h8 : x ^ 8 ≤ 1 := pow_le_one₀ hx0 hx1
  linarith

theorem denom_ne_on_uIcc {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
    (16 : ℝ) - x ^ 8 ≠ 0 := by
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  exact ne_of_gt (denom_pos_on_Icc hx)

theorem tau_integrand_continuousOn (n : ℕ) :
    ContinuousOn (fun x : ℝ ↦ x ^ (8 * n) * g x / (16 - x ^ 8))
      (Set.uIcc (0 : ℝ) 1) := by
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hnum : ContinuousOn (fun x : ℝ ↦ x ^ (8 * n) * g x) (Set.uIcc (0 : ℝ) 1) :=
    ((continuous_pow (8 * n)).mul hg).continuousOn
  have hden : ContinuousOn (fun x : ℝ ↦ (16 : ℝ) - x ^ 8) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_const.sub (continuous_pow 8)).continuousOn
  exact hnum.div hden (fun x hx => denom_ne_on_uIcc hx)

theorem tau_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ x ^ (8 * n) * g x / (16 - x ^ 8))
      MeasureTheory.volume 0 1 :=
  (tau_integrand_continuousOn n).intervalIntegrable

theorem majorant_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (4 : ℝ) / 15 * x ^ (8 * n))
      MeasureTheory.volume 0 1 :=
  ((continuous_const.mul (continuous_pow (8 * n))).continuousOn).intervalIntegrable

theorem key_ineq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    15 * g x ≤ 4 * (16 - x ^ 8) := by
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have h3 : (0 : ℝ) ≤ x ^ 3 := pow_nonneg hx0 3
  have h4 : (0 : ℝ) ≤ x ^ 4 := pow_nonneg hx0 4
  have h5 : (0 : ℝ) ≤ x ^ 5 := pow_nonneg hx0 5
  have h8 : x ^ 8 ≤ (1 : ℝ) := pow_le_one₀ hx0 hx1
  rw [g_expand]
  linarith

theorem integrand_le_majorant (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ^ (8 * n) * g x / (16 - x ^ 8) ≤ (4 : ℝ) / 15 * x ^ (8 * n) := by
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hxp : (0 : ℝ) ≤ x ^ (8 * n) := pow_nonneg hx0 _
  have hden : (0 : ℝ) < 16 - x ^ 8 := denom_pos_on_Icc hx
  have hkey := key_ineq hx
  have hGD : g x / (16 - x ^ 8) ≤ (4 : ℝ) / 15 := by
    rw [div_le_iff₀ hden]
    linarith
  calc x ^ (8 * n) * g x / (16 - x ^ 8)
      = x ^ (8 * n) * (g x / (16 - x ^ 8)) := by ring
    _ ≤ x ^ (8 * n) * (4 / 15) :=
        mul_le_mul_of_nonneg_left hGD hxp
    _ = 4 / 15 * x ^ (8 * n) := by ring

theorem pow_intervalIntegrable (m : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ x ^ m) MeasureTheory.volume 0 1 :=
  ((continuous_pow m).continuousOn).intervalIntegrable

theorem integral_pow_8n (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (8 * n)) = 1 / (((8 * n + 1 : ℕ) : ℝ)) := by
  have hc : (((8 * n + 1 : ℕ) : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (((8 * n + 1 : ℕ) : ℝ)) := by positivity
    exact ne_of_gt this
  have hsub : 8 * n + 1 - 1 = 8 * n := by omega
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ ↦ y ^ (8 * n + 1) / (((8 * n + 1 : ℕ) : ℝ)))
        (x ^ (8 * n)) x := by
    intro x _
    have h := (hasDerivAt_pow (8 * n + 1) x).div_const (((8 * n + 1 : ℕ) : ℝ))
    rw [hsub] at h
    convert h using 1
    push_cast
    field_simp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (pow_intervalIntegrable (8 * n))
  rw [hftc]
  simp only [one_pow, zero_pow (by omega : 8 * n + 1 ≠ 0), zero_div, sub_zero]

theorem tau_pos (n : ℕ) : 0 < tau n := by
  unfold tau
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (tau_intervalIntegrable n)
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    have hxp : (0 : ℝ) < x ^ (8 * n) := pow_pos hx0 _
    have hg : 0 < g x := g_pos_on_Ioo ⟨hx0, hx1⟩
    have h8 : x ^ 8 < (1 : ℝ) := pow_lt_one₀ hx0.le hx1 (by norm_num)
    have hden : (0 : ℝ) < 16 - x ^ 8 := by linarith
    positivity
  · norm_num

theorem tau_le (n : ℕ) : tau n ≤ 4 / (15 * ((8 * n + 1 : ℕ) : ℝ)) := by
  unfold tau
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) ≤ 1) (tau_intervalIntegrable n)
    (majorant_intervalIntegrable n)
    (fun x hx => integrand_le_majorant n hx)
  have hval := integral_pow_8n n
  have hconst : (∫ x in (0 : ℝ)..1, (4 : ℝ) / 15 * x ^ (8 * n))
      = (4 / 15) * (1 / (((8 * n + 1 : ℕ) : ℝ))) := by
    rw [intervalIntegral.integral_const_mul, hval]
  rw [hconst] at hmono
  have heq : (4 : ℝ) / 15 * (1 / (((8 * n + 1 : ℕ) : ℝ)))
      = 4 / (15 * ((8 * n + 1 : ℕ) : ℝ)) := by
    ring
  rw [heq] at hmono
  exact hmono

theorem tau_pos_and_le (n : ℕ) :
    0 < tau n ∧
      tau n ≤ 4 / (15 * ((8 * n + 1 : ℕ) : ℝ)) :=
  ⟨tau_pos n, tau_le n⟩

namespace HypothesisForms

theorem R_eq_sixteen_mul_tau_sub_tau_succ
    (hR_eq_intervalIntegral :
      ∀ m : ℕ, R m = ∫ x in (0 : ℝ)..1, x ^ (8 * m) * g x)
    (n : ℕ) :
    R n = 16 * tau n - tau (n + 1) := by
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hnum_n : Continuous (fun x : ℝ => x ^ (8 * n) * g x) :=
    (continuous_pow _).mul hg
  have hnum_n1 : Continuous (fun x : ℝ => x ^ (8 * (n + 1)) * g x) :=
    (continuous_pow _).mul hg
  have hden : Continuous (fun x : ℝ => (16 : ℝ) - x ^ 8) := by
    fun_prop
  have hden_ne : ∀ x : ℝ, x ∈ Set.uIcc (0 : ℝ) 1 → (16 : ℝ) - x ^ 8 ≠ 0 := by
    intro x hx
    have h01 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 :=
      Set.uIcc_of_le (by norm_num)
    rw [h01] at hx
    obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
    have hx8 : x ^ 8 ≤ 1 := pow_le_one₀ hx0 hx1
    have hpos : (0 : ℝ) < 16 - x ^ 8 := by linarith
    exact ne_of_gt hpos
  have hF_n_on : ContinuousOn
      (fun x : ℝ => x ^ (8 * n) * g x / (16 - x ^ 8)) (Set.uIcc 0 1) :=
    hnum_n.continuousOn.div hden.continuousOn (fun x hx => hden_ne x hx)
  have hF_n1_on : ContinuousOn
      (fun x : ℝ => x ^ (8 * (n + 1)) * g x / (16 - x ^ 8)) (Set.uIcc 0 1) :=
    hnum_n1.continuousOn.div hden.continuousOn (fun x hx => hden_ne x hx)
  have hF_n_int : IntervalIntegrable
      (fun x : ℝ => x ^ (8 * n) * g x / (16 - x ^ 8))
      MeasureTheory.volume 0 1 :=
    hF_n_on.intervalIntegrable
  have hF_n1_int : IntervalIntegrable
      (fun x : ℝ => x ^ (8 * (n + 1)) * g x / (16 - x ^ 8))
      MeasureTheory.volume 0 1 :=
    hF_n1_on.intervalIntegrable
  have h16F_n_int : IntervalIntegrable
      (fun x : ℝ => 16 * (x ^ (8 * n) * g x / (16 - x ^ 8)))
      MeasureTheory.volume 0 1 :=
    hF_n_int.const_mul 16
  have hexp : ∀ x : ℝ, x ^ (8 * (n + 1)) = x ^ (8 * n) * x ^ 8 := by
    intro x
    have h : 8 * (n + 1) = 8 * n + 8 := by ring
    rw [h, pow_add]
  have hpoint : ∀ x : ℝ, x ∈ Set.uIcc (0 : ℝ) 1 →
      16 * (x ^ (8 * n) * g x / (16 - x ^ 8)) -
        x ^ (8 * (n + 1)) * g x / (16 - x ^ 8) =
      x ^ (8 * n) * g x := by
    intro x hx
    have hD : (16 : ℝ) - x ^ 8 ≠ 0 := hden_ne x hx
    rw [hexp x]
    field_simp
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIoc (0 : ℝ) 1 →
        (16 * (x ^ (8 * n) * g x / (16 - x ^ 8)) -
          x ^ (8 * (n + 1)) * g x / (16 - x ^ 8)) =
        x ^ (8 * n) * g x := by
    filter_upwards with x
    intro hx
    have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hx
    exact hpoint x hxIcc
  have hcongr : (∫ x in (0 : ℝ)..1,
        (16 * (x ^ (8 * n) * g x / (16 - x ^ 8)) -
          x ^ (8 * (n + 1)) * g x / (16 - x ^ 8))) =
      ∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x :=
    intervalIntegral.integral_congr_ae hae
  calc R n = ∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x := hR_eq_intervalIntegral n
    _ = (∫ x in (0 : ℝ)..1,
          (16 * (x ^ (8 * n) * g x / (16 - x ^ 8)) -
            x ^ (8 * (n + 1)) * g x / (16 - x ^ 8))) := hcongr.symm
    _ = (∫ x in (0 : ℝ)..1, 16 * (x ^ (8 * n) * g x / (16 - x ^ 8))) -
          ∫ x in (0 : ℝ)..1, x ^ (8 * (n + 1)) * g x / (16 - x ^ 8) :=
        intervalIntegral.integral_sub h16F_n_int hF_n1_int
    _ = 16 * (∫ x in (0 : ℝ)..1, x ^ (8 * n) * g x / (16 - x ^ 8)) -
          ∫ x in (0 : ℝ)..1, x ^ (8 * (n + 1)) * g x / (16 - x ^ 8) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 16 * tau n - tau (n + 1) := rfl

lemma bound_tendsto :
    Filter.Tendsto (fun m : ℕ => 4 / (15 * ((8 * m + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have hid : Filter.Tendsto (fun m : ℕ => m) Filter.atTop Filter.atTop :=
    Filter.tendsto_id
  have htop : Filter.Tendsto (fun m : ℕ => 8 * m + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun m => by omega) hid
  have h0 : Filter.Tendsto (fun n : ℕ => ((4 / 15 : ℝ) / ((n : ℝ))))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (4 / 15 : ℝ)
  have hcomp : Filter.Tendsto
      (fun m : ℕ => ((4 / 15 : ℝ) / (((8 * m + 1 : ℕ) : ℝ))))
      Filter.atTop (nhds 0) :=
    h0.comp htop
  have heq : (fun m : ℕ => 4 / (15 * ((8 * m + 1 : ℕ) : ℝ))) =
      (fun m : ℕ => ((4 / 15 : ℝ) / (((8 * m + 1 : ℕ) : ℝ)))) := by
    funext m
    rw [div_mul_eq_div_div]
  rw [heq]
  exact hcomp

theorem tendsto_tau_zero
    (hTau_pos_and_le :
      ∀ m : ℕ, 0 < tau m ∧
        tau m ≤ 4 / (15 * ((8 * m + 1 : ℕ) : ℝ))) :
    Filter.Tendsto tau Filter.atTop (nhds 0) :=
  squeeze_zero (fun m => le_of_lt (hTau_pos_and_le m).1)
    (fun m => (hTau_pos_and_le m).2) bound_tendsto

theorem Y_add_tau_eq_pow_mul_pi
    (hR_div_pow_eq_bbpRealTerm :
      ∀ m : ℕ, R m / (16 : ℝ) ^ m =
        Theory.PiDigits.T100BBPRealBridge.bbpRealTerm m)
    (hCoboundary : ∀ m : ℕ, R m = 16 * tau m - tau (m + 1))
    (hTauZero : Filter.Tendsto tau Filter.atTop (nhds 0))
    {n : ℕ} (hn : 1 ≤ n) :
    Y n + tau n = (16 : ℝ) ^ (n - 1) * Real.pi := by
  have h16ne : (16 : ℝ) ≠ 0 := by norm_num
  -- Each BBP term telescopes through the coboundary.
  have hterm : ∀ k : ℕ,
      Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k =
        16 * (tau k / (16 : ℝ) ^ k) - 16 * (tau (k + 1) / (16 : ℝ) ^ (k + 1)) := by
    intro k
    have hbk := (hR_div_pow_eq_bbpRealTerm k).symm
    rw [hbk, hCoboundary k]
    have hne : (16 : ℝ) ^ k ≠ 0 := pow_ne_zero k h16ne
    have hsucc : (16 : ℝ) ^ (k + 1) = (16 : ℝ) ^ k * 16 := pow_succ _ _
    rw [hsucc]
    have hne2 : (16 : ℝ) ^ k * 16 ≠ 0 := mul_ne_zero hne h16ne
    field_simp
  -- Finite partial sums telescope.
  have hsum : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k) =
        16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) - 16 * (tau N / (16 : ℝ) ^ N) := by
    intro N
    have hcongr : (∑ k ∈ Finset.range N, Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k) =
        ∑ k ∈ Finset.range N,
          (16 * (tau k / (16 : ℝ) ^ k) - 16 * (tau (k + 1) / (16 : ℝ) ^ (k + 1))) :=
      Finset.sum_congr rfl (fun k _ => hterm k)
    rw [hcongr, Finset.sum_range_sub']
  -- The coboundary remainder vanishes at infinity.
  have hInv : Filter.Tendsto (fun N : ℕ => ((16 : ℝ) ^ N)⁻¹) Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun N : ℕ => ((1 / 16 : ℝ)) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have heq : (fun N : ℕ => ((16 : ℝ) ^ N)⁻¹) = (fun N : ℕ => ((1 / 16 : ℝ)) ^ N) := by
      funext N
      simp only [one_div, inv_pow]
    rw [heq]
    exact hpow
  have hf_tendsto : Filter.Tendsto (fun N : ℕ => 16 * (tau N / (16 : ℝ) ^ N)) Filter.atTop (nhds 0) := by
    have hmul : Filter.Tendsto (fun N : ℕ => tau N * (((16 : ℝ) ^ N)⁻¹)) Filter.atTop (nhds (0 * 0)) :=
      hTauZero.mul hInv
    rw [zero_mul] at hmul
    have h16 : Filter.Tendsto (fun _ : ℕ => (16 : ℝ)) Filter.atTop (nhds 16) :=
      tendsto_const_nhds
    have hcomb := h16.mul hmul
    rw [mul_zero] at hcomb
    simpa [div_eq_mul_inv] using hcomb
  have hpartial : Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k)
      Filter.atTop (nhds Real.pi) :=
    Theory.PiDigits.T104BBPSeriesIdentity.bbpRealTerm_hasSum_pi.tendsto_sum_nat
  have hlim : Filter.Tendsto
      (fun N : ℕ => 16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) - 16 * (tau N / (16 : ℝ) ^ N))
      Filter.atTop (nhds (16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) - 0)) :=
    tendsto_const_nhds.sub hf_tendsto
  have hF_pi : Filter.Tendsto
      (fun N : ℕ => 16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) - 16 * (tau N / (16 : ℝ) ^ N))
      Filter.atTop (nhds Real.pi) :=
    Filter.Tendsto.congr (fun N => hsum N) hpartial
  have hf0 : 16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) - 0 = Real.pi :=
    tendsto_nhds_unique hlim hF_pi
  have hf0val : 16 * (tau 0 / (16 : ℝ) ^ (0 : ℕ)) = Real.pi := by simpa using hf0
  -- Reduce to n = m + 1 to handle the natural subtraction in Y.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hexpn : m + 1 - 1 = m := Nat.add_sub_cancel m 1
  rw [hexpn]
  have hS : (∑ k ∈ Finset.range (m + 1), Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k) =
      Real.pi - 16 * (tau (m + 1) / (16 : ℝ) ^ (m + 1)) := by
    rw [hsum (m + 1), hf0val]
  have hY : Y (m + 1) =
      (16 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k := by
    unfold Y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkm : k ≤ m := by omega
    have hpow : (16 : ℝ) ^ m = (16 : ℝ) ^ (m - k) * (16 : ℝ) ^ k := by
      conv_lhs => rw [← Nat.sub_add_cancel hkm, pow_add]
    have hne : (16 : ℝ) ^ k ≠ 0 := pow_ne_zero k h16ne
    have hbbp : Theory.PiDigits.T100BBPRealBridge.bbpRealTerm k = R k / (16 : ℝ) ^ k :=
      (hR_div_pow_eq_bbpRealTerm k).symm
    have hexp : m + 1 - 1 - k = m - k := by omega
    rw [hexp, hbbp, hpow]
    field_simp
  rw [hY, hS]
  have hpow_succ : (16 : ℝ) ^ (m + 1) = (16 : ℝ) ^ m * 16 := pow_succ _ _
  have hftau : (16 : ℝ) ^ m * (16 * (tau (m + 1) / (16 : ℝ) ^ (m + 1))) = tau (m + 1) := by
    rw [hpow_succ]
    have hne : (16 : ℝ) ^ m ≠ 0 := pow_ne_zero m h16ne
    have hne2 : (16 : ℝ) ^ m * 16 ≠ 0 := mul_ne_zero hne h16ne
    field_simp
  calc (16 : ℝ) ^ m * (Real.pi - 16 * (tau (m + 1) / (16 : ℝ) ^ (m + 1))) + tau (m + 1)
      = (16 : ℝ) ^ m * Real.pi - (16 : ℝ) ^ m * (16 * (tau (m + 1) / (16 : ℝ) ^ (m + 1))) +
        tau (m + 1) := by ring
    _ = (16 : ℝ) ^ m * Real.pi - tau (m + 1) + tau (m + 1) := by rw [hftau]
    _ = (16 : ℝ) ^ m * Real.pi := by ring

end HypothesisForms

theorem R_eq_sixteen_mul_tau_sub_tau_succ (n : ℕ) :
    R n = 16 * tau n - tau (n + 1) :=
  HypothesisForms.R_eq_sixteen_mul_tau_sub_tau_succ R_eq_intervalIntegral n

theorem tendsto_tau_zero :
    Filter.Tendsto tau Filter.atTop (nhds 0) :=
  HypothesisForms.tendsto_tau_zero tau_pos_and_le

theorem Y_add_tau_eq_pow_mul_pi {n : ℕ} (hn : 1 ≤ n) :
    Y n + tau n = (16 : ℝ) ^ (n - 1) * Real.pi :=
  HypothesisForms.Y_add_tau_eq_pow_mul_pi
    R_div_pow_eq_bbpRealTerm R_eq_sixteen_mul_tau_sub_tau_succ
    tendsto_tau_zero hn

end Theory.PiDigits.T200BaileyCrandallCoboundary
