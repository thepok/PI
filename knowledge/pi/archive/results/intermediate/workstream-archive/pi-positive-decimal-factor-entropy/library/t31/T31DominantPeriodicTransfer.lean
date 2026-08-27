import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T28T28ScaleDependentDecimalOrbit

/-!
# T31: finite dominant-periodic-block transfer

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This is a conditional sibling theorem about arbitrary finite circle prefixes.
It neither constructs one fixed real satisfying the hypotheses nor specializes
them to the decimal orbit of pi, and it proves no assertion about C1.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology ComplexConjugate

namespace DecimalFactorComplexity.DominantPeriodicTransfer

open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.ScaleDependentDecimalOrbit

abbrev phase := Theory.PiDigits.T27.phase

/-- Ordinary exponential sum of an arbitrary circle prefix. -/
def circlePrefixSum {M : ℕ} (x : Fin M → ℝ) (h : ℤ) : ℂ :=
  ∑ j : Fin M, phase h (x j)

/-- Complete signed strict-band energy, including zero, with every triangular
weight displayed by `fejerWeight`. -/
def completeFejerEnergy {M : ℕ} (x : Fin M → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ fejerFrequencies H,
    fejerWeight H h * ‖circlePrefixSum x h‖ ^ 2

/-- Total triangular weight on frequencies divisible by `D`. -/
def annihilatorWeight (D H : ℕ) : ℝ :=
  ∑ h ∈ fejerFrequencies H,
    if (D : ℤ) ∣ h then fejerWeight H h else 0

/-- A prefix differs from its model at at most `P` exceptional indices and by
at most `eps` in phase at every other index, uniformly on `|h| < H`. -/
structure PhaseApproximation {M : ℕ} (x y : Fin M → ℝ)
    (H P : ℕ) (eps : ℝ) where
  exceptions : Finset (Fin M)
  card_exceptions : exceptions.card ≤ P
  eps_nonneg : 0 ≤ eps
  close_phase : ∀ h ∈ fejerFrequencies H, ∀ j, j ∉ exceptions →
    ‖phase h (x j) - phase h (y j)‖ ≤ eps

/-- The exact Fourier properties required of the period-`D` model. Periodicity
alone does not imply these bounds, so both are explicit hypotheses. -/
structure PeriodicModelBounds {M : ℕ} (y : Fin M → ℝ)
    (H D : ℕ) : Prop where
  periodic : ∀ (j : ℕ) (hj : j + D < M),
    y ⟨j + D, hj⟩ = y ⟨j, by omega⟩
  annihilator : ∀ h ∈ fejerFrequencies H, (D : ℤ) ∣ h →
    ‖circlePrefixSum y h‖ = M
  offAnnihilator : ∀ h ∈ fejerFrequencies H, ¬(D : ℤ) ∣ h →
    ‖circlePrefixSum y h‖ ≤ D

/-- The complete triangular energy is definitionally the displayed sum. -/
theorem completeFejerEnergy_eq_displayed {M : ℕ} (x : Fin M → ℝ) (H : ℕ) :
    completeFejerEnergy x H =
      ∑ h ∈ fejerFrequencies H,
        (1 - (h.natAbs : ℝ) / (H : ℝ)) *
          ‖∑ j : Fin M, phase h (x j)‖ ^ 2 := by
  rfl

/-- Uniform finite perturbation of every Fourier sum. The exceptional terms
cost exactly the displayed coarse constant `2*P`; all `M` terms are charged
the uniform phase error `eps`. -/
theorem norm_circlePrefixSum_sub_model_le {M H P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (ha : PhaseApproximation x y H P eps)
    (h : ℤ) (hh : h ∈ fejerFrequencies H) :
    ‖circlePrefixSum x h - circlePrefixSum y h‖ ≤
      2 * (P : ℝ) + eps * M := by
  rw [circlePrefixSum, circlePrefixSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin M, (phase h (x j) - phase h (y j))‖ ≤
        ∑ j : Fin M, ‖phase h (x j) - phase h (y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin M,
        (2 * (if j ∈ ha.exceptions then (1 : ℝ) else 0) + eps) := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hj : j ∈ ha.exceptions
      · rw [if_pos hj]
        calc
          ‖phase h (x j) - phase h (y j)‖ ≤
              ‖phase h (x j)‖ + ‖phase h (y j)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [Theory.PiDigits.T27.norm_phase,
              Theory.PiDigits.T27.norm_phase]
            norm_num
          _ ≤ 2 * 1 + eps := by linarith [ha.eps_nonneg]
      · rw [if_neg hj]
        simpa using ha.close_phase h hh j hj
    _ = 2 * (ha.exceptions.card : ℝ) + eps * M := by
      simp [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * (P : ℝ) + eps * M := by
      have hcard : (ha.exceptions.card : ℝ) ≤ P := by
        exact_mod_cast ha.card_exceptions
      linarith

/-- The model annihilator survives finite perturbation. -/
theorem norm_circlePrefixSum_lower_of_dvd {M H D P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D) (h : ℤ)
    (hh : h ∈ fejerFrequencies H) (hd : (D : ℤ) ∣ h) :
    (M : ℝ) - 2 * P - eps * M ≤ ‖circlePrefixSum x h‖ := by
  have hpert := norm_circlePrefixSum_sub_model_le ha h hh
  have hmodel := hm.annihilator h hh hd
  have hrev := norm_sub_norm_le (circlePrefixSum y h) (circlePrefixSum x h)
  rw [norm_sub_rev] at hrev
  rw [hmodel] at hrev
  linarith

/-- Away from the annihilator, only the model remainder and perturbation
remain. -/
theorem norm_circlePrefixSum_upper_of_not_dvd {M H D P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D) (h : ℤ)
    (hh : h ∈ fejerFrequencies H) (hd : ¬(D : ℤ) ∣ h) :
    ‖circlePrefixSum x h‖ ≤ (D : ℝ) + 2 * P + eps * M := by
  have hpert := norm_circlePrefixSum_sub_model_le ha h hh
  have hmodel := hm.offAnnihilator h hh hd
  have hrev := norm_sub_norm_le (circlePrefixSum x h) (circlePrefixSum y h)
  linarith

/-- Generic exact annihilator weight, imported from T28's checked summation. -/
theorem annihilatorWeight_exact (D H : ℕ) (hD : 0 < D) (hH : 0 < H) :
    annihilatorWeight D H =
      let L := (H - 1) / D
      (2 * L + 1 : ℕ) - (D : ℝ) * L * (L + 1) / H := by
  unfold annihilatorWeight
  exact ScaleDependentDecimalOrbit.annihilator_fejerWeight_sum_general
    D H hD hH

/-- Bounds on the exact triangular annihilator weight. -/
theorem annihilatorWeight_bounds (D H : ℕ) (hD : 0 < D) (hH : 0 < H) :
    let L := (H - 1) / D
    (L : ℝ) ≤ annihilatorWeight D H ∧
      annihilatorWeight D H ≤ 2 * L + 1 := by
  let L := (H - 1) / D
  have hDL : D * L ≤ H - 1 := Nat.mul_div_le (H - 1) D
  have hfrac : (D : ℝ) * L * (L + 1) / H ≤ L + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hH)]
    have hDLr : (D : ℝ) * L ≤ H := by
      exact_mod_cast hDL.trans (Nat.sub_le H 1)
    nlinarith
  have hfrac0 : 0 ≤ (D : ℝ) * L * (L + 1) / H := by positivity
  rw [annihilatorWeight_exact D H hD hH]
  dsimp only
  constructor <;> push_cast <;> nlinarith

/-- Nonnegativity of the complete energy at every positive bandwidth. -/
theorem completeFejerEnergy_nonneg {M H : ℕ} (x : Fin M → ℝ) (hH : 0 < H) :
    0 ≤ completeFejerEnergy x H := by
  have hHnat : 1 ≤ H := hH
  unfold completeFejerEnergy
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg
    (ScaleDependentDecimalOrbit.fejerWeight_nonneg_of_mem H hHnat h hh)
    (sq_nonneg _)

/-- Explicit finite lower perturbation bound for the complete energy. -/
theorem energy_lower_bound {M H D P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (hH : 0 < H)
    (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D)
    (hsmall : 2 * (P : ℝ) + eps * M ≤ M) :
    ((M : ℝ) - 2 * P - eps * M) ^ 2 * annihilatorWeight D H ≤
      completeFejerEnergy x H := by
  have hHnat : 1 ≤ H := hH
  have hamp : 0 ≤ (M : ℝ) - 2 * P - eps * M := by linarith
  unfold annihilatorWeight completeFejerEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hw := ScaleDependentDecimalOrbit.fejerWeight_nonneg_of_mem H hHnat h hh
  by_cases hd : (D : ℤ) ∣ h
  · rw [if_pos hd]
    have hn := norm_circlePrefixSum_lower_of_dvd ha hm h hh hd
    have hsq : ((M : ℝ) - 2 * P - eps * M) ^ 2 ≤
        ‖circlePrefixSum x h‖ ^ 2 := by
      nlinarith [norm_nonneg (circlePrefixSum x h)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hsq hw
  · rw [if_neg hd, mul_zero]
    exact mul_nonneg hw (sq_nonneg _)

/-- Explicit finite upper perturbation bound for the complete energy. -/
theorem energy_upper_bound {M H D P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (hH : 0 < H)
    (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D) :
    completeFejerEnergy x H ≤
      (M : ℝ) ^ 2 * annihilatorWeight D H +
        (H : ℝ) * ((D : ℝ) + 2 * P + eps * M) ^ 2 := by
  have hHnat : 1 ≤ H := hH
  have hoff : 0 ≤ (D : ℝ) + 2 * P + eps * M := by
    nlinarith [ha.eps_nonneg]
  have htrivial (h : ℤ) : ‖circlePrefixSum x h‖ ≤ M := by
    unfold circlePrefixSum
    calc
      ‖∑ j : Fin M, phase h (x j)‖ ≤
          ∑ j : Fin M, ‖phase h (x j)‖ := norm_sum_le _ _
      _ = M := by simp [Theory.PiDigits.T27.norm_phase]
  unfold completeFejerEnergy annihilatorWeight
  calc
    (∑ h ∈ fejerFrequencies H,
        fejerWeight H h * ‖circlePrefixSum x h‖ ^ 2) ≤
      ∑ h ∈ fejerFrequencies H,
        ((M : ℝ) ^ 2 *
            (if (D : ℤ) ∣ h then fejerWeight H h else 0) +
          ((D : ℝ) + 2 * P + eps * M) ^ 2 * fejerWeight H h) := by
      apply Finset.sum_le_sum
      intro h hh
      have hw := ScaleDependentDecimalOrbit.fejerWeight_nonneg_of_mem H hHnat h hh
      by_cases hd : (D : ℤ) ∣ h
      · rw [if_pos hd]
        have hsquare : ‖circlePrefixSum x h‖ ^ 2 ≤ (M : ℝ) ^ 2 := by
          nlinarith [htrivial h, norm_nonneg (circlePrefixSum x h)]
        have hmain := mul_le_mul_of_nonneg_left hsquare hw
        have hextra : 0 ≤
            ((D : ℝ) + 2 * P + eps * M) ^ 2 * fejerWeight H h :=
          mul_nonneg (sq_nonneg _) hw
        nlinarith
      · rw [if_neg hd]
        have hn := norm_circlePrefixSum_upper_of_not_dvd ha hm h hh hd
        have hsquare : ‖circlePrefixSum x h‖ ^ 2 ≤
            ((D : ℝ) + 2 * P + eps * M) ^ 2 := by
          nlinarith [norm_nonneg (circlePrefixSum x h)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hsquare hw
    _ = (M : ℝ) ^ 2 *
          (∑ h ∈ fejerFrequencies H,
            if (D : ℤ) ∣ h then fejerWeight H h else 0) +
        ((D : ℝ) + 2 * P + eps * M) ^ 2 *
          (∑ h ∈ fejerFrequencies H, fejerWeight H h) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (M : ℝ) ^ 2 *
          (∑ h ∈ fejerFrequencies H,
            if (D : ℤ) ∣ h then fejerWeight H h else 0) +
        (H : ℝ) * ((D : ℝ) + 2 * P + eps * M) ^ 2 := by
      rw [DecimalFactorComplexity.AbstractSubgroupSeparation.sum_fejerWeight
        H hHnat]
      ring

/-- The finite upper bound after division by `H*M^2`, with every constant
visible. -/
theorem normalized_energy_upper_bound {M H D P : ℕ} {eps : ℝ}
    {x y : Fin M → ℝ} (hM : 0 < M) (hH : 0 < H) (hD : 0 < D)
    (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D) :
    completeFejerEnergy x H / ((H : ℝ) * (M : ℝ) ^ 2) ≤
      2 / (D : ℝ) + 1 / H +
        ((D : ℝ) / M + 2 * (P : ℝ) / M + eps) ^ 2 := by
  let L := (H - 1) / D
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDL : D * L ≤ H - 1 := Nat.mul_div_le (H - 1) D
  have hLratio : (L : ℝ) ≤ (H : ℝ) / D := by
    rw [le_div_iff₀ hDr]
    have hcast : (D : ℝ) * L ≤ H := by
      exact_mod_cast hDL.trans (Nat.sub_le H 1)
    simpa [mul_comm] using hcast
  have hA := (annihilatorWeight_bounds D H hD hH).2
  change annihilatorWeight D H ≤ 2 * (L : ℝ) + 1 at hA
  have hAcontrol : annihilatorWeight D H / H ≤
      2 / (D : ℝ) + 1 / H := by
    calc
      annihilatorWeight D H / H ≤ (2 * (L : ℝ) + 1) / H :=
        div_le_div_of_nonneg_right hA hHr.le
      _ ≤ (2 * ((H : ℝ) / D) + 1) / H := by gcongr
      _ = 2 / (D : ℝ) + 1 / H := by field_simp [hDr.ne', hHr.ne']
  have henergy := energy_upper_bound hH ha hm
  calc
    completeFejerEnergy x H / ((H : ℝ) * (M : ℝ) ^ 2) ≤
        ((M : ℝ) ^ 2 * annihilatorWeight D H +
          (H : ℝ) * ((D : ℝ) + 2 * P + eps * M) ^ 2) /
            ((H : ℝ) * (M : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right henergy
        (mul_nonneg hHr.le (sq_nonneg _))
    _ = annihilatorWeight D H / H +
        (((D : ℝ) + 2 * P + eps * M) / M) ^ 2 := by
      field_simp [hHr.ne', hMr.ne']
    _ = annihilatorWeight D H / H +
        ((D : ℝ) / M + 2 * (P : ℝ) / M + eps) ^ 2 := by
      congr 2
      field_simp [hMr.ne']
    _ ≤ _ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hAcontrol
          (((D : ℝ) / M + 2 * (P : ℝ) / M + eps) ^ 2)

/-- Combined finite transfer certificate with `M,H,D,P,eps`, both energies,
all constants, and the strict triangular band visible in its dependencies. -/
theorem finite_dominant_periodic_transfer
    (M H D P : ℕ) (eps : ℝ) (x y : Fin M → ℝ)
    (hM : 0 < M) (hH : 0 < H) (hD : 0 < D)
    (ha : PhaseApproximation x y H P eps)
    (hm : PeriodicModelBounds y H D)
    (hsmall : 2 * (P : ℝ) + eps * M ≤ M) :
    (((M : ℝ) - 2 * P - eps * M) ^ 2 * annihilatorWeight D H ≤
        completeFejerEnergy x H) ∧
      (completeFejerEnergy x H ≤
        (M : ℝ) ^ 2 * annihilatorWeight D H +
          (H : ℝ) * ((D : ℝ) + 2 * P + eps * M) ^ 2) ∧
      (completeFejerEnergy x H / ((H : ℝ) * (M : ℝ) ^ 2) ≤
        2 / (D : ℝ) + 1 / H +
          ((D : ℝ) / M + 2 * (P : ℝ) / M + eps) ^ 2) := by
  exact ⟨energy_lower_bound hH ha hm hsmall,
    energy_upper_bound hH ha hm,
    normalized_energy_upper_bound hM hH hD ha hm⟩

/-- If `H/D` diverges, the exact triangular weight on multiples of `D`
diverges. This is the sequence-level form of T28's finite weight formula. -/
theorem annihilatorWeight_tendsto_atTop (H D : ℕ → ℕ)
    (hpos : ∀ᶠ n in atTop, 0 < H n ∧ 0 < D n)
    (hHD : Tendsto (fun n => (H n : ℝ) / D n) atTop atTop) :
    Tendsto (fun n => annihilatorWeight (D n) (H n)) atTop atTop := by
  rw [tendsto_atTop] at hHD ⊢
  intro B
  filter_upwards [hHD (B + 2), hpos] with n hnratio hnpos
  let L := (H n - 1) / D n
  have hbound := (annihilatorWeight_bounds (D n) (H n) hnpos.2 hnpos.1).1
  change (L : ℝ) ≤ annihilatorWeight (D n) (H n) at hbound
  have hmod : (H n - 1) % D n < D n := Nat.mod_lt _ hnpos.2
  have hdecomp := Nat.div_add_mod' (H n - 1) (D n)
  have hnat : H n ≤ L * D n + D n := by
    dsimp only [L]
    omega
  have hratio : (H n : ℝ) / D n ≤ L + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hnpos.2)]
    have hcast : (H n : ℝ) ≤ (L : ℝ) * D n + D n := by
      exact_mod_cast hnat
    nlinarith
  linarith

/-- First asymptotic regime. Growing `H/D` and vanishing exceptional/phase
fraction force energy divided by `M^2` to diverge. -/
theorem normalized_energy_tendsto_atTop
    (M H D P : ℕ → ℕ) (eps : ℕ → ℝ)
    (x y : ∀ n, Fin (M n) → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < M n ∧ 0 < H n ∧ 0 < D n)
    (ha : ∀ n, PhaseApproximation (x n) (y n) (H n) (P n) (eps n))
    (hm : ∀ n, PeriodicModelBounds (y n) (H n) (D n))
    (hHD : Tendsto (fun n => (H n : ℝ) / D n) atTop atTop)
    (herr : Tendsto (fun n => 2 * (P n : ℝ) / M n + eps n)
      atTop (𝓝 0)) :
    Tendsto (fun n => completeFejerEnergy (x n) (H n) / (M n : ℝ) ^ 2)
      atTop atTop := by
  have hAW : Tendsto (fun n => annihilatorWeight (D n) (H n)) atTop atTop :=
    annihilatorWeight_tendsto_atTop H D (hpos.mono fun _ hn => ⟨hn.2.1, hn.2.2⟩) hHD
  have herrHalf : ∀ᶠ n in atTop,
      2 * (P n : ℝ) / M n + eps n < 1 / 2 :=
    (tendsto_order.1 herr).2 (1 / 2) (by norm_num)
  rw [tendsto_atTop]
  intro B
  filter_upwards [hpos, herrHalf,
    hAW.eventually_gt_atTop (4 * max B 0)] with n hnpos hnerr hnAW
  have hMr : (0 : ℝ) < M n := by exact_mod_cast hnpos.1
  have hperturb : 2 * (P n : ℝ) + eps n * M n < (M n : ℝ) / 2 := by
    calc
      2 * (P n : ℝ) + eps n * M n =
          (2 * (P n : ℝ) / M n + eps n) * M n := by
        field_simp [hMr.ne']
      _ < (1 / 2 : ℝ) * M n := mul_lt_mul_of_pos_right hnerr hMr
      _ = (M n : ℝ) / 2 := by ring
  have hsmall : 2 * (P n : ℝ) + eps n * M n ≤ M n := by linarith
  have hlower := energy_lower_bound hnpos.2.1 (ha n) (hm n) hsmall
  have hamp : (M n : ℝ) / 2 ≤
      (M n : ℝ) - 2 * P n - eps n * M n := by linarith
  have hsquare : ((M n : ℝ) / 2) ^ 2 ≤
      ((M n : ℝ) - 2 * P n - eps n * M n) ^ 2 := by
    nlinarith
  have hAWnonneg : 0 ≤ annihilatorWeight (D n) (H n) := by
    have hmax : 0 ≤ max B 0 := le_max_right B 0
    linarith
  have hprod : ((M n : ℝ) / 2) ^ 2 * annihilatorWeight (D n) (H n) ≤
      ((M n : ℝ) - 2 * P n - eps n * M n) ^ 2 *
        annihilatorWeight (D n) (H n) :=
    mul_le_mul_of_nonneg_right hsquare hAWnonneg
  have hB : B ≤ max B 0 := le_max_left B 0
  have hBprod : B * (M n : ℝ) ^ 2 ≤
      ((M n : ℝ) / 2) ^ 2 * annihilatorWeight (D n) (H n) := by
    have hscale : 4 * B ≤ annihilatorWeight (D n) (H n) := by linarith
    nlinarith [sq_nonneg ((M n : ℝ))]
  rw [le_div_iff₀ (sq_pos_of_pos hMr)]
  exact hBprod.trans (hprod.trans hlower)

/-- Second asymptotic regime. Growing `D,H` and a vanishing normalized
boundary/exception/phase error force density-normalized energy to zero. -/
theorem normalized_energy_density_tendsto_zero
    (M H D P : ℕ → ℕ) (eps : ℕ → ℝ)
    (x y : ∀ n, Fin (M n) → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < M n ∧ 0 < H n ∧ 0 < D n)
    (ha : ∀ n, PhaseApproximation (x n) (y n) (H n) (P n) (eps n))
    (hm : ∀ n, PeriodicModelBounds (y n) (H n) (D n))
    (hDtop : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    (hHtop : Tendsto (fun n => (H n : ℝ)) atTop atTop)
    (herr : Tendsto (fun n =>
      (D n : ℝ) / M n + 2 * (P n : ℝ) / M n + eps n) atTop (𝓝 0)) :
    Tendsto (fun n => completeFejerEnergy (x n) (H n) /
      ((H n : ℝ) * (M n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hDinv : Tendsto (fun n => 2 / (D n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hDtop
  have hHinv : Tendsto (fun n => 1 / (H n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hHtop
  have hcontrol : Tendsto (fun n =>
      2 / (D n : ℝ) + 1 / (H n : ℝ) +
        ((D n : ℝ) / M n + 2 * (P n : ℝ) / M n + eps n) ^ 2)
      atTop (𝓝 0) := by
    simpa using (hDinv.add hHinv).add (herr.pow 2)
  apply squeeze_zero' (g := fun n =>
    2 / (D n : ℝ) + 1 / (H n : ℝ) +
      ((D n : ℝ) / M n + 2 * (P n : ℝ) / M n + eps n) ^ 2)
  · filter_upwards [hpos] with n hn
    exact div_nonneg (completeFejerEnergy_nonneg (x n) hn.2.1)
      (mul_nonneg (by positivity) (sq_nonneg _))
  · filter_upwards [hpos] with n hn
    exact normalized_energy_upper_bound hn.1 hn.2.1 hn.2.2 (ha n) (hm n)
  · exact hcontrol

/-- Machine-readable scope record: all fields are false because T31 is only a
conditional finite and sequential transfer theorem. -/
structure ScopeStatus where
  constructsFixedReal : Bool
  specializesToPi : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  constructsFixedReal := false
  specializesToPi := false
  provesC1 := false
  disprovesC1 := false

/-- Explicit fixed-real, pi, and C1 nonclaims. -/
theorem explicit_scope_nonclaims :
    scopeStatus.constructsFixedReal = false ∧
      scopeStatus.specializesToPi = false ∧
      scopeStatus.provesC1 = false ∧ scopeStatus.disprovesC1 = false := by
  norm_num [scopeStatus]

end DecimalFactorComplexity.DominantPeriodicTransfer

#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.completeFejerEnergy_eq_displayed
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.norm_circlePrefixSum_sub_model_le
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.norm_circlePrefixSum_lower_of_dvd
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.norm_circlePrefixSum_upper_of_not_dvd
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.annihilatorWeight_exact
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.annihilatorWeight_bounds
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.energy_lower_bound
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.energy_upper_bound
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.normalized_energy_upper_bound
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.finite_dominant_periodic_transfer
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.normalized_energy_tendsto_atTop
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.normalized_energy_density_tendsto_zero
#print axioms DecimalFactorComplexity.DominantPeriodicTransfer.explicit_scope_nonclaims
