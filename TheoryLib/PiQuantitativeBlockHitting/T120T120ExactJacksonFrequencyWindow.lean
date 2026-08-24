import TheoryLib.PiQuantitativeBlockHitting.T19T19ExactNaturalScaleResonance

/-!
# T120: tighter Jackson resonance window and denominator

T19 uses the order-`q` Jackson minorant to turn a missing interval of length
`1/q` into a finite Fourier resonance.  Two losses in that consumer can be
removed without adding any hypothesis:

* the generic triangle-inequality argument gives the threshold
  `c₀ / (A + c₀)`, rather than `c₀ / (2*A)`;
* the order-`q` Jackson presentation has no frequency of magnitude `2*q`, so
  the exact window is `2*q - 1`.

For T19, `A = 4` and

`c₀ = 1/(3*q) + 2/(3*q^3)`.

Thus a missing interval forces a nonzero frequency `|h| ≤ 2*q - 1` with
normalized sum at least

`c₀ / (4 + c₀) = (q^2 + 2) / (12*q^3 + q^2 + 2)`,

asymptotic to `1/(12*q)`.  T19's threshold is asymptotic to `1/(24*q)`.
The new finite hypothesis is proved strictly weaker than T19's by an explicit
uniform two-point grid.

The final theorem remains conditional: it does not prove the required
cancellation for pi and does not prove V1 unconditionally.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.T120ExactJacksonFrequencyWindow

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.SharperNaturalScaleResonance
open Theory.PiDigits.ExactNaturalScaleResonance

/-- A strengthened finite Fourier principle.  The old `c₀ / (2*A)` loss is
replaced by `c₀ / (A + c₀)`.  The extra `c₀` in the denominator avoids any
need to extract a strict term from a finite weighted sum. -/
theorem finiteFourierPresentation_resonance_improved
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ)
    (x : ℕ → ℝ) (N H : ℕ) (center c0 A : ℝ)
    (hN : 0 < N) (hc0 : 0 < c0) (hA : 0 < A)
    (hfrequency : ∀ i, (frequency i).natAbs ≤ H)
    (hzero : c0 ≤ ∑ i with frequency i = 0, coefficient i)
    (hmass : (∑ i, |coefficient i|) ≤ A)
    (hnonpos : ∀ j < N,
      (∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ H ∧
      c0 / (A + c0) ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < A + c0 := add_pos hA hc0
  let z : ℂ := ∑ i with frequency i ≠ 0,
    coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
      Theory.PiDigits.T27.exponentialSum x N (frequency i)
  have htotal :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)).re ≤ 0 := by
    simp_rw [← Complex.reCLM_apply]
    rw [map_sum]
    exact Finset.sum_nonpos fun j hj => hnonpos j (Finset.mem_range.mp hj)
  have hfourier :
      (∑ j ∈ Finset.range N, ∑ i, coefficient i *
        Theory.PiDigits.T27.phase (frequency i) (x j - center)) =
      ∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Theory.PiDigits.T27.exponentialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show x j - center = -center + x j by ring,
      Theory.PiDigits.T27.phase_add_real]
    ring
  rw [hfourier] at htotal
  have hsplit :
      (∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
        Theory.PiDigits.T27.exponentialSum x N (frequency i)) =
      (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
    calc
      (∑ i, coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
          Theory.PiDigits.T27.exponentialSum x N (frequency i)) =
        (∑ i with frequency i = 0, coefficient i *
          Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i)) +
        ∑ i with frequency i ≠ 0, coefficient i *
          Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i) :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => frequency i = 0) _).symm
      _ = (N : ℝ) * (∑ i with frequency i = 0, coefficient i) + z := by
        congr 1
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hz := (Finset.mem_filter.mp hi).2
        simp [hz, Theory.PiDigits.T27.phase_zero,
          Theory.PiDigits.T27.exponentialSum_zero]
        ring
  rw [hsplit] at htotal
  have htotal' : (N : ℝ) * (∑ i with frequency i = 0, coefficient i) +
      z.re ≤ 0 := by simpa using htotal
  have hzlarge : c0 * (N : ℝ) ≤ ‖z‖ := by
    calc
      c0 * (N : ℝ) ≤ (N : ℝ) *
          (∑ i with frequency i = 0, coefficient i) := by
            nlinarith
      _ ≤ -z.re := by linarith
      _ ≤ |z.re| := neg_le_abs _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  by_contra hnone
  push Not at hnone
  have hterm (i : ι) (hi : frequency i ≠ 0) :
      ‖Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ ≤
        (N : ℝ) * (c0 / (A + c0)) := by
    have hi' := hnone (frequency i) hi (hfrequency i)
    simpa [mul_comm] using (div_le_iff₀ hNR).mp hi'.le
  have hzupper :
      ‖z‖ ≤ A * ((N : ℝ) * (c0 / (A + c0))) := by
    calc
      ‖z‖ ≤ ∑ i with frequency i ≠ 0,
          ‖coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i with frequency i ≠ 0,
          |coefficient i| * ((N : ℝ) * (c0 / (A + c0))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
        exact mul_le_mul_of_nonneg_left (hterm i (Finset.mem_filter.mp hi).2)
          (abs_nonneg _)
      _ = (∑ i with frequency i ≠ 0, |coefficient i|) *
          ((N : ℝ) * (c0 / (A + c0))) := by rw [Finset.sum_mul]
      _ ≤ A * ((N : ℝ) * (c0 / (A + c0))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          (∑ i with frequency i ≠ 0, |coefficient i|) ≤
              ∑ i, |coefficient i| := by
            rw [Finset.sum_filter]
            apply Finset.sum_le_sum
            intro i hi
            split <;> simp [abs_nonneg]
          _ ≤ A := hmass
  have hfrac : A / (A + c0) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hstrict :
      A * ((N : ℝ) * (c0 / (A + c0))) < c0 * (N : ℝ) := by
    calc
      A * ((N : ℝ) * (c0 / (A + c0))) =
          (A / (A + c0)) * (c0 * (N : ℝ)) := by ring
      _ < 1 * (c0 * (N : ℝ)) :=
        mul_lt_mul_of_pos_right hfrac (mul_pos hc0 hNR)
      _ = c0 * (N : ℝ) := by ring
  exact (not_lt_of_ge hzlarge) (lt_of_le_of_lt hzupper hstrict)

/-- Every frequency that actually occurs in the order-`n` Jackson
presentation has magnitude at most `2*n - 1`.  The former `2*n` endpoint is
not attained. -/
lemma jacksonFrequency_natAbs_le_pred {n : ℕ} (hn : 0 < n)
    (i : JacksonIndex n) :
    (jacksonFrequency i).natAbs ≤ 2 * n - 1 := by
  let B : ℕ := 2 * n - 1
  have hB : (B : ℤ) = 2 * (n : ℤ) - 1 := by
    dsimp [B]
    omega
  have bounded (z : ℤ) (hlo : -(B : ℤ) ≤ z) (hhi : z ≤ (B : ℤ)) :
      z.natAbs ≤ B := by
    have habs : z.natAbs ≤ ((B : ℤ)).natAbs :=
      Int.natAbs_le_iff_sq_le.mpr (by nlinarith)
    simpa using habs
  rcases i with ⟨⟨r, s, u, v⟩⟩ | ⟨⟨br, r⟩, ⟨bs, s⟩⟩
  · change Int.natAbs
      (((s : ℤ) - (r : ℤ)) + ((v : ℤ) - (u : ℤ))) ≤ B
    apply bounded
    · rw [hB]
      have hr := r.isLt
      have hs := s.isLt
      have hu := u.isLt
      have hv := v.isLt
      omega
    · rw [hB]
      have hr := r.isLt
      have hs := s.isLt
      have hu := u.isLt
      have hv := v.isLt
      omega
  · cases br <;> cases bs
    · change Int.natAbs ((-(s : ℤ)) - (-(r : ℤ))) ≤ B
      apply bounded
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
    · change Int.natAbs
        (((n : ℤ) - (s : ℤ)) - (-(r : ℤ))) ≤ B
      apply bounded
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
    · change Int.natAbs
        ((-(s : ℤ)) - ((n : ℤ) - (r : ℤ))) ≤ B
      apply bounded
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
    · change Int.natAbs
        (((n : ℤ) - (s : ℤ)) - ((n : ℤ) - (r : ℤ))) ≤ B
      apply bounded
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega
      · rw [hB]
        have hr := r.isLt
        have hs := s.isLt
        omega

/-- The exact lower bound for the zero mode used by T19. -/
def exactJacksonZeroMass (q : ℕ) : ℝ :=
  1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)

/-- The improved normalized resonance threshold. -/
def exactJacksonImprovedThreshold (q : ℕ) : ℝ :=
  exactJacksonZeroMass q / (4 + exactJacksonZeroMass q)

lemma exactJacksonZeroMass_pos (q : ℕ) (hq : 0 < q) :
    0 < exactJacksonZeroMass q := by
  unfold exactJacksonZeroMass
  positivity

/-- The zero-mode lower bound cannot exceed the total coefficient mass `4`.
This is proved from the Fourier presentation itself rather than from a loose
arithmetic estimate. -/
lemma exactJacksonZeroMass_le_four (q : ℕ) (hq : 0 < q) :
    exactJacksonZeroMass q ≤ 4 := by
  calc
    exactJacksonZeroMass q ≤
        ∑ i : JacksonIndex q with jacksonFrequency i = 0,
          jacksonCoefficient q q i := by
      simpa only [exactJacksonZeroMass] using
        jackson_zeroCoefficient_self_lower q hq
    _ ≤ ∑ i : JacksonIndex q with jacksonFrequency i = 0,
          |jacksonCoefficient q q i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_abs_self _
    _ ≤ ∑ i : JacksonIndex q, |jacksonCoefficient q q i| := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      split <;> simp [abs_nonneg]
    _ = 4 := by
      rw [jacksonCoefficient_mass_general q q hq hq]
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp
      norm_num

lemma exactJacksonOldThreshold_eq_div_eight (q : ℕ) (hq : 0 < q) :
    1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3) =
      exactJacksonZeroMass q / 8 := by
  unfold exactJacksonZeroMass
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

/-- T19's threshold is no larger than the improved threshold. -/
lemma exactJacksonOldThreshold_le_improved (q : ℕ) (hq : 0 < q) :
    1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3) ≤
      exactJacksonImprovedThreshold q := by
  rw [exactJacksonOldThreshold_eq_div_eight q hq]
  unfold exactJacksonImprovedThreshold
  have hcpos := exactJacksonZeroMass_pos q hq
  have hc4 := exactJacksonZeroMass_le_four q hq
  have hinv :
      1 / (8 : ℝ) ≤ 1 / (4 + exactJacksonZeroMass q) := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  calc
    exactJacksonZeroMass q / 8 =
        exactJacksonZeroMass q * (1 / (8 : ℝ)) := by ring
    _ ≤ exactJacksonZeroMass q *
        (1 / (4 + exactJacksonZeroMass q)) :=
      mul_le_mul_of_nonneg_left hinv hcpos.le
    _ = exactJacksonZeroMass q /
        (4 + exactJacksonZeroMass q) := by ring

/-- An empty interval of length `1/q` forces a resonance in the exact support
window and at the improved denominator. -/
theorem finite_empty_decimalInterval_resonance_improved
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * q - 1 ∧
      exactJacksonImprovedThreshold q ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  let center := a + (q : ℝ)⁻¹ / 2
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finiteFourierPresentation_resonance_improved
      (jacksonCoefficient q q) (@jacksonFrequency q)
      x N (2 * q - 1) center (exactJacksonZeroMass q) 4 hN
      (exactJacksonZeroMass_pos q hq) (by norm_num)
      (jacksonFrequency_natAbs_le_pred hq)
      (by
        simpa only [exactJacksonZeroMass] using
          jackson_zeroCoefficient_self_lower q hq)
      (by
        rw [jacksonCoefficient_mass_general q q hq hq]
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        field_simp
        norm_num)
      (by
        intro j hj
        simpa only [jacksonMinorant, center] using
          jacksonMinorant_re_nonpos_outside q q hq hq (x j) a
            (hx j hj) ha haq (hempty j hj))
  exact ⟨h, hzero, hbound, by
    simpa only [exactJacksonImprovedThreshold] using hlarge⟩

/-- Direct contrapositive of the improved empty-interval theorem. -/
theorem finite_decimalInterval_hit_of_improved_frequency_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q - 1 →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        exactJacksonImprovedThreshold q) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finite_empty_decimalInterval_resonance_improved
      x N q a hN hq hx ha haq (fun j hj => hno j hj)
  exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

/-- A missing decimal word in the finite pi orbit forces the improved exact
Jackson resonance. -/
theorem piOrbit_naturalScale_resonance_improved_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ s.length - 1 ∧
      exactJacksonImprovedThreshold (10 ^ s.length) ≤
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) := by
  let q := 10 ^ s.length
  let a := Theory.PiDigits.T27.decimalCylinderLeft s
  have hq : 0 < q := by positivity
  have hempty : ∀ j < N,
      Theory.PiDigits.T27.piFractionalOrbit j ∉
        Set.Ico a (a + (q : ℝ)⁻¹) := by
    intro j hj hmem
    apply hmissing j hj
    have hinterval : Theory.PiDigits.T27.piFractionalOrbit j ∈
        Set.Ico
          ((Theory.PiDigits.T20.wordValue s : ℝ) / (10 : ℝ) ^ s.length)
          (((Theory.PiDigits.T20.wordValue s + 1 : ℕ) : ℝ) /
            (10 : ℝ) ^ s.length) := by
      have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
      rw [hpow] at hmem
      have hmem' : Theory.PiDigits.T27.piFractionalOrbit j ∈
          Set.Ico (Theory.PiDigits.T27.decimalCylinderLeft s)
            (Theory.PiDigits.T27.decimalCylinderLeft s +
              Theory.PiDigits.T27.decimalCylinderLength s.length) := by
        simpa only [a, q, Theory.PiDigits.T27.decimalCylinderLength] using hmem
      rw [Theory.PiDigits.T27.decimalCylinder_interval] at hmem'
      exact hmem'
    have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
      s (Theory.PiDigits.T27.piFractionalOrbit j) hinterval
    intro i hi
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
      Real.pi Real.pi_pos.le j i
    exact (Theory.PiDigits.T20.decimalDigit_pi (j + i)).symm.trans
      (hshift.symm.trans (hdigits i hi))
  simpa only [q, a, Nat.cast_pow, Nat.cast_ofNat,
    Theory.PiDigits.T27.decimalCylinderLength] using
    finite_empty_decimalInterval_resonance_improved
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- The improved simultaneous finite-orbit cancellation target.  It has both
a shorter frequency window and a larger admissible threshold than T19's
`PiNaturalScaleCancellationExact`. -/
def PiNaturalScaleCancellationImproved : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * 10 ^ k - 1 →
      ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) <
        exactJacksonImprovedThreshold (10 ^ k)

/-- At fixed finite data, T19's frequency condition implies the improved
condition. -/
theorem exact_finite_frequency_hypothesis_implies_improved
    (x : ℕ → ℝ) (N q : ℕ) (hq : 0 < q)
    (hexact : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) :
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q - 1 →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        exactJacksonImprovedThreshold q := by
  intro h hzero hbound
  have hboundOld : h.natAbs ≤ 2 * q := hbound.trans (by omega)
  exact lt_of_lt_of_le (hexact h hzero hboundOld)
    (exactJacksonOldThreshold_le_improved q hq)

/-- T19's global premise implies the improved premise. -/
theorem piNaturalScaleCancellationExact_implies_improved
    (hexact : PiNaturalScaleCancellationExact) :
    PiNaturalScaleCancellationImproved := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := hexact k hk
  refine ⟨N, hN, ?_⟩
  exact exact_finite_frequency_hypothesis_implies_improved
    Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) (by positivity) hsmall

/-- The improved cancellation target still reaches canonical V1.  The premise
is not proved for pi. -/
theorem piNaturalScaleCancellationImproved_implies_canonicalV1
    (himproved : PiNaturalScaleCancellationImproved) : Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ := himproved (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) = (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      obtain ⟨h, hzero, hbound, hlarge⟩ :=
        piOrbit_naturalScale_resonance_improved_of_missingBefore
          (d :: s) N hN hmissingBefore
      exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

lemma uniformGridTwo_small_first_one :
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 1 →
      ‖Theory.PiDigits.T27.exponentialSum (uniformGrid 2) 2 h‖ / (2 : ℝ) <
        exactJacksonImprovedThreshold 1 := by
  intro h hzero hbound
  have hk : 0 < h.natAbs := Int.natAbs_pos.mpr hzero
  have hk2 : h.natAbs < 2 := by omega
  have hpos := uniformGrid_exponentialSum_nat_eq_zero
    h.natAbs 2 (by norm_num) hk hk2
  rcases Int.natAbs_eq h with hh | hh
  · rw [hh, hpos]
    norm_num [exactJacksonImprovedThreshold, exactJacksonZeroMass]
  · rw [hh, exponentialSum_neg, hpos, map_zero]
    norm_num [exactJacksonImprovedThreshold, exactJacksonZeroMass]

/-- The new finite spectral premise is strictly weaker than T19's premise.
The uniform two-point grid cancels the entire new window at `q = 1`, while it
is fully resonant at the old endpoint frequency `h = 2`. -/
theorem improved_finite_frequency_hypothesis_strict_vs_exact :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q - 1 →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          exactJacksonImprovedThreshold q) ∧
      ¬ (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) := by
  refine ⟨uniformGrid 2, 2, 1, by norm_num, by norm_num, ?_, ?_⟩
  · simpa using uniformGridTwo_small_first_one
  · intro hexact
    have htwo := hexact 2 (by norm_num) (by norm_num)
    have hsum :
        Theory.PiDigits.T27.exponentialSum (uniformGrid 2) 2 (2 : ℤ) =
          (2 : ℂ) := by
      simpa using uniformGrid_exponentialSum_self 2 (by norm_num)
    rw [hsum] at htwo
    norm_num at htwo

end Theory.PiDigits.T120ExactJacksonFrequencyWindow

#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.finiteFourierPresentation_resonance_improved
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.jacksonFrequency_natAbs_le_pred
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.exactJacksonZeroMass_le_four
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.exactJacksonOldThreshold_le_improved
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.finite_empty_decimalInterval_resonance_improved
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.finite_decimalInterval_hit_of_improved_frequency_smallness
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.piOrbit_naturalScale_resonance_improved_of_missingBefore
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.exact_finite_frequency_hypothesis_implies_improved
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.piNaturalScaleCancellationExact_implies_improved
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.piNaturalScaleCancellationImproved_implies_canonicalV1
#print axioms Theory.PiDigits.T120ExactJacksonFrequencyWindow.improved_finite_frequency_hypothesis_strict_vs_exact
