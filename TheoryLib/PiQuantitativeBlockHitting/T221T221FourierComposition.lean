import Mathlib

/-!
# T221: Fourier composition

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t221; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section

namespace Theory.PiDigits.T221FourierComposition

open MeasureTheory
open scoped BigOperators

noncomputable def coeff (f : ℝ → ℂ) (m : ℤ) : ℂ :=
  ∫ x in Set.Ico (0 : ℝ) 1,
    f x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)

noncomputable def Tb (b : ℕ) (x : ℝ) : ℝ := x - ⌊x⌋

lemma coeff_eq_interval (f : ℝ → ℂ) (m : ℤ) :
    coeff f m = ∫ x in (0:ℝ)..1,
      f x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I) := by
  rw [coeff, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ico_eq_integral_Ioc]

lemma intervalIntegrable_of_Ico {g : ℝ → ℂ} (hg : IntegrableOn g (Set.Ico (0:ℝ) 1)) :
    IntervalIntegrable g volume 0 1 := by
  have hset : Set.Ico (0:ℝ) 1 =ᵐ[volume] Set.Ioc (0:ℝ) 1 :=
    (MeasureTheory.Ioo_ae_eq_Ico).symm.trans MeasureTheory.Ioo_ae_eq_Ioc
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact hg.congr_set_ae hset.symm

lemma floor_on_piece {b : ℕ} (hbpos : (0:ℝ) < (b:ℝ)) (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo ((j : ℝ) / (b:ℝ)) (((j : ℝ) + 1) / (b:ℝ))) :
    Tb b ((b:ℝ) * x) = (b:ℝ) * x - (j : ℝ) := by
  have h1 : (j : ℝ) ≤ (b:ℝ) * x := by
    have := hx.1
    rw [div_lt_iff₀ hbpos] at this
    nlinarith [this]
  have h2 : (b:ℝ) * x < (j : ℝ) + 1 := by
    have := hx.2
    rw [lt_div_iff₀ hbpos] at this
    nlinarith [this]
  have hfloor : ⌊(b:ℝ) * x⌋ = (j : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      exact h1
    · push_cast
      exact h2
  rw [Tb, hfloor]
  push_cast
  ring

lemma base_intervalIntegrable {b : ℕ} {g : ℝ → ℂ} {m : ℤ}
    (hg : IntegrableOn g (Set.Ico (0:ℝ) 1)) :
    IntervalIntegrable
      (fun u => g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I))
      volume 0 1 := by
  refine (intervalIntegrable_of_Ico hg).mul_continuousOn ?_
  fun_prop

lemma nice_eq {b : ℕ} {g : ℝ → ℂ} {m : ℤ} (hb0 : (b:ℝ) ≠ 0) (j : ℕ) :
    (fun x => g ((b:ℝ) * x - (j:ℝ)) *
        Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      = fun x => (g ((b:ℝ) * x + -(j:ℝ)) *
          Complex.exp (-(2 * Real.pi * m * ((b:ℝ) * x + -(j:ℝ)) / b : ℝ) * Complex.I)) *
          Complex.exp (-(2 * Real.pi * m * j / b : ℝ) * Complex.I) := by
  funext x
  have hxj : (b:ℝ) * x + -(j:ℝ) = (b:ℝ) * x - (j:ℝ) := by ring
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast hb0
  rw [hxj, mul_assoc (g ((b:ℝ) * x - (j:ℝ))), ← Complex.exp_add]
  congr 1
  rw [← add_mul]
  congr 1
  push_cast
  field_simp
  ring

lemma nice_integrable {b : ℕ} {g : ℝ → ℂ} {m : ℤ} (hbpos : (0:ℝ) < (b:ℝ))
    (hg : IntegrableOn g (Set.Ico (0:ℝ) 1)) (j : ℕ) :
    IntervalIntegrable
      (fun x => g ((b:ℝ) * x - (j:ℝ)) *
        Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      volume ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)) := by
  have hb0 : (b:ℝ) ≠ 0 := ne_of_gt hbpos
  have h1 := base_intervalIntegrable (b := b) (m := m) hg
  have h2 := h1.comp_add_right (-(j:ℝ))
  have h2' : IntervalIntegrable
      (fun x => g (x + -(j:ℝ)) *
        Complex.exp (-(2 * Real.pi * m * (x + -(j:ℝ)) / b : ℝ) * Complex.I))
      volume (j:ℝ) ((j:ℝ)+1) := by
    have e1 : (0:ℝ) - -(j:ℝ) = (j:ℝ) := by ring
    have e2 : (1:ℝ) - -(j:ℝ) = (j:ℝ)+1 := by ring
    rw [e1, e2] at h2
    exact h2
  have h3 := h2'.comp_mul_left (c := (b:ℝ))
  have h4 : IntervalIntegrable
      (fun x => g ((b:ℝ) * x + -(j:ℝ)) *
        Complex.exp (-(2 * Real.pi * m * ((b:ℝ) * x + -(j:ℝ)) / b : ℝ) * Complex.I))
      volume ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)) := h3
  rw [nice_eq hb0 j]
  exact h4.mul_const _

lemma nice_value {b : ℕ} {g : ℝ → ℂ} {m : ℤ} (hbpos : (0:ℝ) < (b:ℝ)) (j : ℕ) :
    (∫ x in ((j:ℝ)/(b:ℝ))..(((j:ℝ)+1)/(b:ℝ)),
        g ((b:ℝ) * x - (j:ℝ)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      = Complex.exp (-(2 * Real.pi * m * j / b : ℝ) * Complex.I) *
        ((b:ℝ)⁻¹ • ∫ u in (0:ℝ)..1,
          g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I)) := by
  have hb0 : (b:ℝ) ≠ 0 := ne_of_gt hbpos
  have hsub :
      (∫ x in ((j:ℝ)/(b:ℝ))..(((j:ℝ)+1)/(b:ℝ)),
        g ((b:ℝ) * x + -(j:ℝ)) *
          Complex.exp (-(2 * Real.pi * m * ((b:ℝ) * x + -(j:ℝ)) / b : ℝ) * Complex.I))
      = (b:ℝ)⁻¹ • ∫ u in ((b:ℝ) * ((j:ℝ)/(b:ℝ)) + -(j:ℝ))..((b:ℝ) * (((j:ℝ)+1)/(b:ℝ)) + -(j:ℝ)),
          g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I) :=
    intervalIntegral.integral_comp_mul_add
      (fun u => g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I)) hb0 (-(j:ℝ))
  have e1 : (b:ℝ) * ((j:ℝ)/(b:ℝ)) + -(j:ℝ) = 0 := by field_simp; ring
  have e2 : (b:ℝ) * (((j:ℝ)+1)/(b:ℝ)) + -(j:ℝ) = 1 := by field_simp; ring
  rw [e1, e2] at hsub
  rw [nice_eq hb0 j, intervalIntegral.integral_mul_const, hsub, mul_comm]

lemma piece_transfer {b : ℕ} {g : ℝ → ℂ} {m : ℤ} (hbpos : (0:ℝ) < (b:ℝ))
    (hg : IntegrableOn g (Set.Ico (0:ℝ) 1)) (j : ℕ) :
    IntervalIntegrable
        (fun x => g (Tb b ((b:ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
        volume ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ))
      ∧ (∫ x in ((j:ℝ)/(b:ℝ))..(((j:ℝ)+1)/(b:ℝ)),
            g (Tb b ((b:ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
        = ∫ x in ((j:ℝ)/(b:ℝ))..(((j:ℝ)+1)/(b:ℝ)),
            g ((b:ℝ) * x - (j:ℝ)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I) := by
  have hle : ((j:ℝ))/(b:ℝ) ≤ (((j:ℝ)+1))/(b:ℝ) := by
    gcongr; linarith
  have hEq : Set.EqOn
      (fun x => g (Tb b ((b:ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      (fun x => g ((b:ℝ) * x - (j:ℝ)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      (Set.Ioo ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ))) := by
    intro x hx
    simp only
    rw [floor_on_piece hbpos j hx]
  have hres : volume.restrict (Set.Ioc ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)))
      = volume.restrict (Set.Ioo ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ))) :=
    (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm
  have hni := nice_integrable (b := b) (g := g) (m := m) hbpos hg j
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hni
  have hae : (fun x => g (Tb b ((b:ℝ) * x)) *
        Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      =ᵐ[volume.restrict (Set.Ioo ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)))]
      (fun x => g ((b:ℝ) * x - (j:ℝ)) *
        Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)) :=
    Filter.eventuallyEq_of_mem (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) hEq
  have e1 : ∀ F : ℝ → ℂ, (∫ x in Set.Ioc ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)), F x)
      = ∫ x in Set.Ioo ((j:ℝ)/(b:ℝ)) (((j:ℝ)+1)/(b:ℝ)), F x := by
    intro F
    exact (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle, MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.congr ?_ hae.symm
    rw [MeasureTheory.IntegrableOn, hres] at hni
    exact hni
  · rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle, e1, e1]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hEq

lemma coeff_comp_Tb {b : ℕ} {g : ℝ → ℂ} {m : ℤ}
    (hb : 2 ≤ b) (hg : IntegrableOn g (Set.Ico 0 1)) :
    coeff (fun x => g (Tb b (b * x))) m =
      if (b : ℤ) ∣ m then coeff g (m / (b : ℤ)) else 0 := by
  have hbnat : 0 < b := by omega
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbnat
  have hb0 : (b:ℝ) ≠ 0 := ne_of_gt hbpos
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast hb0
  have hint : ∀ k, k < b → IntervalIntegrable
      (fun x => g (Tb b ((b:ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      volume (((k:ℕ):ℝ)/(b:ℝ)) (((k+1 : ℕ):ℝ)/(b:ℝ)) := by
    intro k _
    have hc : ((k+1 : ℕ):ℝ)/(b:ℝ) = ((k:ℝ)+1)/(b:ℝ) := by push_cast; ring
    rw [hc]
    exact (piece_transfer hbpos hg k).1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => ((k:ℝ)/(b:ℝ))) (n := b)
    (f := fun x => g (Tb b ((b:ℝ) * x)) *
      Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
    (μ := volume) hint
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at hsum
  rw [div_self hb0] at hsum
  rw [coeff_eq_interval, ← hsum]
  have hkey : ∀ k ∈ Finset.range b,
      (∫ x in ((k:ℝ)/(b:ℝ))..(((k:ℝ)+1)/(b:ℝ)),
        g (Tb b ((b:ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      = (Complex.exp (-(2 * Real.pi * m / b : ℝ) * Complex.I))^k *
        ((b:ℝ)⁻¹ • ∫ u in (0:ℝ)..1,
          g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I)) := by
    intro k _
    rw [(piece_transfer hbpos hg k).2, nice_value hbpos k]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.sum_mul]
  by_cases hd : (b : ℤ) ∣ m
  · obtain ⟨t, ht⟩ := id hd
    have hmr : (m:ℝ) = (b:ℝ) * (t:ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) ht
    have hbz : (b : ℤ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hq : m / (b : ℤ) = t := by
      rw [ht]; exact Int.mul_ediv_cancel_left t hbz
    have hzeta : Complex.exp (-(2 * Real.pi * m / b : ℝ) * Complex.I) = 1 := by
      have hre : (2 * Real.pi * (m:ℝ) / (b:ℝ) : ℝ) = ((t : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hmr]; field_simp
      rw [hre, ← Complex.exp_int_mul_two_pi_mul_I (-t)]
      congr 1
      push_cast
      ring
    rw [hzeta, if_pos hd]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hJ : (∫ u in (0:ℝ)..1,
        g u * Complex.exp (-(2 * Real.pi * m * u / b : ℝ) * Complex.I))
        = coeff g (m / (b : ℤ)) := by
      rw [coeff_eq_interval]
      have harg : ∀ u : ℝ, (2 * Real.pi * (m:ℝ) * u / (b:ℝ) : ℝ)
          = (2 * Real.pi * ((m / (b:ℤ) : ℤ) : ℝ) * u : ℝ) := by
        intro u
        rw [hq, hmr]
        field_simp
      simp only [harg]
    rw [hJ, Complex.real_smul]
    push_cast
    field_simp
    try ring
  · have hzb : (Complex.exp (-(2 * Real.pi * m / b : ℝ) * Complex.I))^b = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I (-m)]
      congr 1
      push_cast
      field_simp
      try ring
    have hzne : Complex.exp (-(2 * Real.pi * m / b : ℝ) * Complex.I) ≠ 1 := by
      intro hcon
      rw [Complex.exp_eq_one_iff] at hcon
      obtain ⟨n, hn⟩ := hcon
      refine hd ⟨-n, ?_⟩
      have hcancel : -((2 * Real.pi * (m:ℝ) / (b:ℝ) : ℝ) : ℂ)
          = (n:ℂ) * (2 * (Real.pi : ℂ)) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        rw [hn]
        ring
      have hreal : -(2 * Real.pi * (m:ℝ) / (b:ℝ)) = (n:ℝ) * (2 * Real.pi) := by
        exact_mod_cast hcancel
      have h2 : 2 * Real.pi * (m:ℝ) / (b:ℝ) = -((n:ℝ) * (2 * Real.pi)) := by linarith
      rw [div_eq_iff hb0] at h2
      have h2pi : (2 * Real.pi) ≠ 0 := by
        have := Real.pi_pos
        positivity
      have hm : (m:ℝ) = (b:ℝ) * (-(n:ℝ)) := by
        apply mul_left_cancel₀ h2pi
        linear_combination h2
      exact_mod_cast hm
    have hgeom : ∑ k ∈ Finset.range b,
        (Complex.exp (-(2 * Real.pi * m / b : ℝ) * Complex.I))^k = 0 := by
      rw [geom_sum_eq hzne, hzb, sub_self, zero_div]
    rw [hgeom, zero_mul, if_neg hd]

lemma integrableOn_char {g : ℝ → ℂ} {m : ℤ} (hg : IntegrableOn g (Set.Ico (0:ℝ) 1)) :
    IntegrableOn (fun x => g x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      (Set.Ico (0:ℝ) 1) volume := by
  have hset : Set.Ico (0:ℝ) 1 =ᵐ[volume] Set.Ioc (0:ℝ) 1 :=
    (MeasureTheory.Ioo_ae_eq_Ico).symm.trans MeasureTheory.Ioo_ae_eq_Ioc
  have h1 : IntervalIntegrable g volume 0 1 := intervalIntegrable_of_Ico hg
  have h2 : IntervalIntegrable
      (fun x => g x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)) volume 0 1 := by
    refine h1.mul_continuousOn ?_
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h2
  exact h2.congr_set_ae hset

lemma coboundary_coeff
    {b : ℕ} {f g : ℝ → ℂ} {m : ℤ}
    (hb : 2 ≤ b)
    (hf : IntegrableOn f (Set.Ico 0 1))
    (hg : IntegrableOn g (Set.Ico 0 1))
    (hcob : ∀ᵐ x ∂Measure.restrict volume (Set.Ico 0 1),
      f x = g x - g (Tb b ((b : ℝ) * x))) :
    coeff f m = coeff g m -
      (if (b : ℤ) ∣ m then coeff g (m / (b : ℤ)) else 0) := by
  have hfE := integrableOn_char (m := m) hf
  have hgE := integrableOn_char (m := m) hg
  have hae1 : (fun x => f x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      =ᵐ[volume.restrict (Set.Ico (0:ℝ) 1)]
      (fun x => g x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)
        - g (Tb b ((b : ℝ) * x)) * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)) := by
    filter_upwards [hcob] with x hx
    rw [hx]
    ring
  have hae2 : (fun x => g (Tb b ((b : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I))
      =ᵐ[volume.restrict (Set.Ico (0:ℝ) 1)]
      (fun x => g x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)
        - f x * Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)) := by
    filter_upwards [hcob] with x hx
    rw [hx]
    ring
  have hTE : IntegrableOn (fun x => g (Tb b ((b : ℝ) * x)) *
      Complex.exp (-(2 * Real.pi * m * x : ℝ) * Complex.I)) (Set.Ico (0:ℝ) 1) volume :=
    (hgE.sub hfE).congr hae2.symm
  have step1 : coeff f m = coeff g m - coeff (fun x => g (Tb b ((b : ℝ) * x))) m := by
    rw [coeff, coeff, coeff, MeasureTheory.integral_congr_ae hae1]
    exact MeasureTheory.integral_sub hgE hTE
  rw [step1, coeff_comp_Tb hb hg]

lemma ray_telescope
    {b : ℕ} {f g : ℝ → ℂ} {h : ℤ} {k : ℕ}
    (hb : 2 ≤ b) (hh : h ≠ 0) (hprim : ¬ (b : ℤ) ∣ h)
    (hrec : ∀ m : ℤ,
      coeff f m = coeff g m -
        (if (b : ℤ) ∣ m then coeff g (m / (b : ℤ)) else 0)) :
    coeff g ((b : ℤ) ^ k * h) =
      ∑ j ∈ Finset.range (k + 1), coeff f ((b : ℤ) ^ j * h) := by
  have _hh : h ≠ 0 := hh
  have hb0 : (b : ℤ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 by omega)
  induction k with
  | zero =>
      have hnd : ¬ (b : ℤ) ∣ (b : ℤ) ^ 0 * h := by simpa using hprim
      have hz := hrec ((b : ℤ) ^ 0 * h)
      rw [if_neg hnd, sub_zero] at hz
      simp only [pow_zero, one_mul] at hz
      simp [hz]
  | succ k ih =>
      have hdvd : (b : ℤ) ∣ (b : ℤ) ^ (k + 1) * h := ⟨(b : ℤ) ^ k * h, by ring⟩
      have hq : ((b : ℤ) ^ (k + 1) * h) / (b : ℤ) = (b : ℤ) ^ k * h := by
        have : (b : ℤ) ^ (k + 1) * h = (b : ℤ) * ((b : ℤ) ^ k * h) := by ring
        rw [this, Int.mul_ediv_cancel_left _ hb0]
      have hstep := hrec ((b : ℤ) ^ (k + 1) * h)
      rw [if_pos hdvd, hq] at hstep
      rw [Finset.sum_range_succ, ← ih]
      linear_combination -hstep

end Theory.PiDigits.T221FourierComposition
