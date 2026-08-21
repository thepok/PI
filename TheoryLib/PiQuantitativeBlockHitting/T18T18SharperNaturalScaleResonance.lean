import TheoryLib.PiQuantitativeBlockHitting.T6PiNaturalScaleResonanceObstruction

/-!
# T18: sharper natural-scale resonance obstruction

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T6 evaluates its explicit Jackson minorant at order `64*q`.  The same
minorant is already effective at order `2*q`.  Two disjoint explicit
`q^3`-families of zero-frequency quadruples give constant coefficient at
least `1/(2*q)`, while the coefficient `L1` mass is exactly `10`.
Consequently, an empty interval of length `1/q` forces a nonzero frequency at
most `4*q` whose normalized exponential sum is at least `1/(40*q)`.

The result is a sharper conditional reduction, not a proof that the decimal
orbit of pi satisfies the required cancellation estimate and not a proof of
canonical V1.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.SharperNaturalScaleResonance

open Theory.PiDigits.PiNaturalScaleResonanceObstruction

/-- Two disjoint translated `q^3` families of zero-frequency quadruples at
Jackson order `2*q`. The Boolean coordinate records whether the first two
entries lie in the lower or upper half of `Fin (2*q)`. -/
def zeroQuadEmbeddingTwo (q : ℕ) :
    (Bool × Fin q × Fin q × Fin q) ↪
      (Fin (2 * q) × Fin (2 * q) × Fin (2 * q) × Fin (2 * q)) where
  toFun x :=
    let r : Fin (2 * q) :=
      ⟨if x.1 then q + x.2.1 else x.2.1, by split <;> omega⟩
    let s : Fin (2 * q) :=
      ⟨if x.1 then q + x.2.2.1 else x.2.2.1, by split <;> omega⟩
    let u : Fin (2 * q) := ⟨x.2.2.1 + x.2.2.2, by omega⟩
    let v : Fin (2 * q) := ⟨x.2.1 + x.2.2.2, by omega⟩
    (r, s, u, v)
  inj' := by
    rintro ⟨b, r, s, t⟩ ⟨b', r', s', t'⟩ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    rcases h with ⟨hr, hs, hu, _hv⟩
    cases b <;> cases b'
    · simp at hr hs
      have hrr : r = r' := Fin.ext hr
      have hss : s = s' := Fin.ext hs
      have htt : t = t' := Fin.ext (by omega)
      subst r'
      subst s'
      subst t'
      rfl
    · simp at hr hs
      have hrlt := r.isLt
      omega
    · simp at hr hs
      have hr'lt := r'.isLt
      omega
    · simp at hr hs
      have hrr : r = r' := Fin.ext (by omega)
      have hss : s = s' := Fin.ext (by omega)
      have htt : t = t' := Fin.ext (by omega)
      subst r'
      subst s'
      subst t'
      rfl

lemma zeroQuadEmbeddingTwo_frequency (q : ℕ)
    (x : Bool × Fin q × Fin q × Fin q) :
    jacksonFrequency (Sum.inl (zeroQuadEmbeddingTwo q x)) = 0 := by
  rcases x with ⟨b, r, s, t⟩
  cases b <;> simp [zeroQuadEmbeddingTwo, jacksonFrequency]

lemma zeroQuadTwo_count_lower (q : ℕ) :
    2 * q * q * q ≤
      ((Finset.univ : Finset (Fin (2 * q) × Fin (2 * q) ×
        Fin (2 * q) × Fin (2 * q))).filter fun x =>
          jacksonFrequency (Sum.inl x) = 0).card := by
  let s : Finset (Bool × Fin q × Fin q × Fin q) := Finset.univ
  let t := (Finset.univ : Finset (Fin (2 * q) × Fin (2 * q) ×
    Fin (2 * q) × Fin (2 * q))).filter fun x =>
      jacksonFrequency (Sum.inl x) = 0
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn
    (zeroQuadEmbeddingTwo q)
    (by
      intro x hx
      simpa [t] using zeroQuadEmbeddingTwo_frequency q x)
    (zeroQuadEmbeddingTwo q).injective.injOn
  simpa only [s, t, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_assoc] using hcard

/-- At order `2*q`, the unaggregated coefficient `L1` mass is exactly `10`. -/
lemma jacksonCoefficient_mass_two (q : ℕ) (hq : 0 < q) :
    (∑ i : JacksonIndex (2 * q),
      |jacksonCoefficient q (2 * q) i|) = 10 := by
  classical
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [jacksonCoefficient]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmain :
      |(2 / (q : ℝ) ^ 2) / ((2 * q : ℕ) : ℝ) ^ 2| =
        (2 / (q : ℝ) ^ 2) / ((2 * q : ℕ) : ℝ) ^ 2 :=
    abs_of_nonneg (by positivity)
  rw [hmain]
  simp_rw [abs_div, abs_neg, abs_mul, edgeSign_abs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp
  rw [abs_of_nonneg (by positivity)]
  ring

/-- The two explicit zero-mode families give constant coefficient at least
`1/(2*q)` at Jackson order `2*q`. -/
lemma jackson_zeroCoefficient_lower_two (q : ℕ) (hq : 0 < q) :
    (1 : ℝ) / (2 * (q : ℝ)) ≤
      ∑ i : JacksonIndex (2 * q) with jacksonFrequency i = 0,
        jacksonCoefficient q (2 * q) i := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ x : (Bool × Fin (2 * q)) × (Bool × Fin (2 * q)),
      if jacksonFrequency (Sum.inr x) = 0 then
        jacksonCoefficient q (2 * q) (Sum.inr x) else 0) =
      -(1 / ((2 * q : ℕ) : ℝ)) by
    simpa only [Finset.sum_filter] using
      jacksonEdge_zeroCoefficient (2 * q) (by omega)]
  have hcount := zeroQuadTwo_count_lower q
  have hcoeff : 0 ≤
      (2 / (q : ℝ) ^ 2) / (((2 * q : ℕ) : ℝ) ^ 2) := by positivity
  have hmain :
      ((2 * q * q * q : ℕ) : ℝ) *
          ((2 / (q : ℝ) ^ 2) / (((2 * q : ℕ) : ℝ) ^ 2)) ≤
        ∑ x : Fin (2 * q) × Fin (2 * q) × Fin (2 * q) × Fin (2 * q),
          if jacksonFrequency (Sum.inl x) = 0 then
            jacksonCoefficient q (2 * q) (Sum.inl x) else 0 := by
    rw [← Finset.sum_filter]
    simp only [jacksonCoefficient, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hcoeff
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (1 : ℝ) / (2 * (q : ℝ)) =
        ((2 * q * q * q : ℕ) : ℝ) *
          ((2 / (q : ℝ) ^ 2) / (((2 * q : ℕ) : ℝ) ^ 2)) -
            1 / ((2 * q : ℕ) : ℝ) := by
          push_cast
          field_simp
          ring
    _ ≤ _ := by linarith

/-- Sharpened generic empty-interval theorem. Compared with T6, the frequency
window is `4*q` instead of `128*q`, and the forced normalized resonance is
`1/(40*q)` instead of `1/(16388*q)`. -/
theorem finite_empty_decimalInterval_resonance_sharp
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 4 * q ∧
      1 / (40 * (q : ℝ)) ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  let center := a + (q : ℝ)⁻¹ / 2
  have hn : 0 < 2 * q := by omega
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finiteFourierPresentation_resonance
      (jacksonCoefficient q (2 * q)) (@jacksonFrequency (2 * q))
      x N (4 * q) center (1 / (2 * (q : ℝ))) 10 hN
      (by positivity) (by norm_num)
      (fun i => (jacksonFrequency_bound i).trans_eq (by omega))
      (jackson_zeroCoefficient_lower_two q hq)
      (by rw [jacksonCoefficient_mass_two q hq])
      (by
        intro j hj
        simpa only [jacksonMinorant, center] using
          jacksonMinorant_re_nonpos_outside q (2 * q) hq hn (x j) a
            (hx j hj) ha haq (hempty j hj))
  refine ⟨h, hzero, hbound, ?_⟩
  convert hlarge using 1
  field_simp
  ring

/-- Direct contrapositive: strict smallness for the shorter frequency window
forces a hit in the prescribed interval. -/
theorem finite_decimalInterval_hit_of_sharp_frequency_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (40 * (q : ℝ))) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finite_empty_decimalInterval_resonance_sharp
      x N q a hN hq hx ha haq (fun j hj => hno j hj)
  exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

/-- Equally spaced sample used to show that the new finite spectral
hypothesis is genuinely weaker than T6's finite spectral hypothesis. -/
def uniformGrid (L : ℕ) : ℕ → ℝ := fun j => (j : ℝ) / L

lemma phase_uniformGrid_eq_pow (h : ℤ) (L j : ℕ) :
    Theory.PiDigits.T27.phase h (uniformGrid L j) =
      Theory.PiDigits.T27.phase h (1 / (L : ℝ)) ^ j := by
  induction j with
  | zero => simp [uniformGrid, Theory.PiDigits.T27.phase]
  | succ j ih =>
      rw [show uniformGrid L (j + 1) =
          uniformGrid L j + 1 / (L : ℝ) by
        simp only [uniformGrid]
        push_cast
        ring]
      rw [Theory.PiDigits.T27.phase_add_real, ih, pow_succ]

lemma phase_integer_at_one (h : ℤ) :
    Theory.PiDigits.T27.phase h 1 = 1 := by
  rw [Theory.PiDigits.T27.phase]
  convert Complex.exp_int_mul_two_pi_mul_I h using 1
  push_cast
  ring_nf

lemma phase_uniformGrid_root_pow (h : ℤ) (L : ℕ) (hL : 0 < L) :
    Theory.PiDigits.T27.phase h (1 / (L : ℝ)) ^ L = 1 := by
  rw [← phase_uniformGrid_eq_pow]
  have hcast : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simpa [uniformGrid, hcast] using phase_integer_at_one h

lemma phase_uniformGrid_root_ne_one (k L : ℕ)
    (hL : 0 < L) (hk : 0 < k) (hkL : k < L) :
    Theory.PiDigits.T27.phase (k : ℤ) (1 / (L : ℝ)) ≠ 1 := by
  intro heq
  have hcast : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hexp :
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) = 1 := by
    rw [Theory.PiDigits.T27.phase] at heq
    convert heq using 1
    push_cast
    field_simp
  have hdvd : L ∣ k :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hL.ne').mp hexp
  exact (not_le_of_gt hkL) (Nat.le_of_dvd hk hdvd)

lemma uniformGrid_exponentialSum_nat_eq_zero (k L : ℕ)
    (hL : 0 < L) (hk : 0 < k) (hkL : k < L) :
    Theory.PiDigits.T27.exponentialSum (uniformGrid L) L (k : ℤ) = 0 := by
  rw [Theory.PiDigits.T27.exponentialSum]
  simp_rw [phase_uniformGrid_eq_pow]
  let r := Theory.PiDigits.T27.phase (k : ℤ) (1 / (L : ℝ))
  have hrpow : r ^ L = 1 := phase_uniformGrid_root_pow (k : ℤ) L hL
  have hrne : r ≠ 1 := phase_uniformGrid_root_ne_one k L hL hk hkL
  have hgeom := geom_sum_mul_neg r L
  rw [hrpow, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right
    (sub_ne_zero.mpr hrne.symm)

lemma exponentialSum_neg (x : ℕ → ℝ) (N : ℕ) (h : ℤ) :
    Theory.PiDigits.T27.exponentialSum x N (-h) =
      conj (Theory.PiDigits.T27.exponentialSum x N h) := by
  simp only [Theory.PiDigits.T27.exponentialSum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact Theory.PiDigits.T27.phase_neg h (x j)

lemma uniformGridFive_small_first_four :
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 →
      ‖Theory.PiDigits.T27.exponentialSum (uniformGrid 5) 5 h‖ / (5 : ℝ) <
        1 / (40 : ℝ) := by
  intro h hzero hbound
  have hk : 0 < h.natAbs := Int.natAbs_pos.mpr hzero
  have hk5 : h.natAbs < 5 := by omega
  have hpos := uniformGrid_exponentialSum_nat_eq_zero
    h.natAbs 5 (by norm_num) hk hk5
  rcases Int.natAbs_eq h with hh | hh
  · rw [hh, hpos]
    norm_num
  · rw [hh, exponentialSum_neg, hpos, map_zero]
    norm_num

lemma uniformGrid_exponentialSum_self (L : ℕ) (hL : 0 < L) :
    Theory.PiDigits.T27.exponentialSum (uniformGrid L) L (L : ℤ) = L := by
  rw [Theory.PiDigits.T27.exponentialSum]
  have hphase : Theory.PiDigits.T27.phase (L : ℤ) (1 / (L : ℝ)) = 1 := by
    rw [Theory.PiDigits.T27.phase]
    have hcast : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    convert Complex.exp_two_pi_mul_I using 1
    push_cast
    field_simp
  simp_rw [phase_uniformGrid_eq_pow, hphase, one_pow]
  simp

/-- The finite family of inequalities used by the new theorem is strictly
weaker, not merely differently normalized. The five-point uniform grid
cancels every nonzero frequency through `4`, but frequency `5` is fully
resonant and therefore violates T6's requirement through `128`. -/
theorem sharp_finite_frequency_hypothesis_strict :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (40 * (q : ℝ))) ∧
      ¬ (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 128 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (16388 * (q : ℝ))) := by
  refine ⟨uniformGrid 5, 5, 1, by norm_num, by norm_num, ?_, ?_⟩
  · simpa using uniformGridFive_small_first_four
  · intro hlegacy
    have hfive := hlegacy 5 (by norm_num) (by norm_num)
    have hsum :
        Theory.PiDigits.T27.exponentialSum (uniformGrid 5) 5 (5 : ℤ) =
          (5 : ℂ) := by
      simpa using uniformGrid_exponentialSum_self 5 (by norm_num)
    rw [hsum] at hfive
    norm_num at hfive

/-- A missing decimal word among the first `N` starts of the base-ten pi orbit
forces the sharper natural-scale resonance. -/
theorem piOrbit_naturalScale_resonance_sharp_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 4 * 10 ^ s.length ∧
      1 / (40 * (10 : ℝ) ^ s.length) ≤
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
    finite_empty_decimalInterval_resonance_sharp
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- The new finite cancellation target. For each positive word length, one
finite pi-orbit sample has small sums only in the shorter frequency window
`4*10^k`, and the allowed upper bound is the larger constant `1/(40*10^k)`.

This is an open hypothesis about pi. -/
def PiNaturalScaleCancellationSharp : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 * 10 ^ k →
      ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) <
        1 / (40 * (10 : ℝ) ^ k)

/-- The T6-parameter finite cancellation target, named only so the strict
parameter improvement can be audited in one theorem. This too is open for
pi. -/
def PiNaturalScaleCancellationT6 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 128 * 10 ^ k →
      ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) <
        1 / (16388 * (10 : ℝ) ^ k)

/-- T6's stronger parameter target implies the sharper target: the frequency
window shrinks from `128*10^k` to `4*10^k`, while the permitted bound grows
strictly from `1/(16388*10^k)` to `1/(40*10^k)`. -/
theorem piNaturalScaleCancellationT6_implies_sharp
    (hT6 : PiNaturalScaleCancellationT6) :
    PiNaturalScaleCancellationSharp := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := hT6 k hk
  refine ⟨N, hN, ?_⟩
  intro h hzero hbound
  have hboundT6 : h.natAbs ≤ 128 * 10 ^ k := by
    exact hbound.trans (by omega)
  have hlegacy := hsmall h hzero hboundT6
  have hpow : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hconstants :
      1 / (16388 * (10 : ℝ) ^ k) <
        1 / (40 * (10 : ℝ) ^ k) := by
    field_simp
    nlinarith
  exact hlegacy.trans hconstants

/-- The sharper finite cancellation target is sufficient for canonical V1.
No assertion is made that pi satisfies the target. -/
theorem piNaturalScaleCancellationSharp_implies_canonicalV1
    (hsharp : PiNaturalScaleCancellationSharp) : Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ := hsharp (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) = (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      obtain ⟨h, hzero, hbound, hlarge⟩ :=
        piOrbit_naturalScale_resonance_sharp_of_missingBefore
          (d :: s) N hN hmissingBefore
      exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

end Theory.PiDigits.SharperNaturalScaleResonance

#print axioms Theory.PiDigits.SharperNaturalScaleResonance.zeroQuadEmbeddingTwo_frequency
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.zeroQuadTwo_count_lower
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.jacksonCoefficient_mass_two
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.jackson_zeroCoefficient_lower_two
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.finite_empty_decimalInterval_resonance_sharp
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.finite_decimalInterval_hit_of_sharp_frequency_smallness
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.sharp_finite_frequency_hypothesis_strict
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.piOrbit_naturalScale_resonance_sharp_of_missingBefore
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.piNaturalScaleCancellationT6_implies_sharp
#print axioms Theory.PiDigits.SharperNaturalScaleResonance.piNaturalScaleCancellationSharp_implies_canonicalV1
