import TheoryLib.PiQuantitativeBlockHitting.T18T18SharperNaturalScaleResonance

/-!
# T19: exact zero-mode natural-scale resonance

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T18 already improves T6's Jackson order from `64*q` to `2*q`.  Here a
triangular zero-frequency embedding counts `(2*q^3+q)/3` main terms at order
`q`.  Together with the exact coefficient mass `4`, this shows that an empty
interval of length `1/q` forces a nonzero frequency at most `2*q` with
normalized exponential sum at least

`1/(24*q) + 1/(12*q^3)`.

The finite smallness condition is proved strictly weaker than T18's by an
explicit equally spaced sample.  The final pi theorem is conditional: it
does not assert the required cancellation for pi and does not prove V1
unconditionally.  The Jackson/Fejer localization method is classical; no
novelty claim is made for the method or constants.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.ExactNaturalScaleResonance

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.SharperNaturalScaleResonance

/-- A triangular index set containing exactly the zero-frequency terms needed
for the sharp order-`q` lower bound. -/
abbrev TriZeroIndex (n : ℕ) :=
  (Σ j : Fin n, Fin (j + 1) × Fin (j + 1)) ⊕
  (Σ j : Fin n, Fin j × Fin j)

/-- The two triangular branches map injectively to zero-frequency Jackson
quadruples.  The first branch has first coordinate at most the second; every
populated point of the second branch has the strict reverse inequality. -/
def triZeroEmbedding (n : ℕ) :
    TriZeroIndex n ↪ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := by
    rcases x with x | x
    · let j : ℕ := x.1
      let d : ℕ := n - (j + 1)
      let r : Fin n := ⟨x.2.1, by omega⟩
      let s : Fin n := ⟨x.2.1 + d, by
        have hj := x.1.isLt
        have hr := x.2.1.isLt
        dsimp [j, d]
        omega⟩
      let u : Fin n := ⟨x.2.2 + d, by
        have hj := x.1.isLt
        have hu := x.2.2.isLt
        dsimp [j, d]
        omega⟩
      let v : Fin n := ⟨x.2.2, by omega⟩
      exact (r, s, u, v)
    · let j : ℕ := x.1
      let d : ℕ := n - j
      let r : Fin n := ⟨x.2.1 + d, by
        have hj := x.1.isLt
        have hr := x.2.1.isLt
        dsimp [j, d]
        omega⟩
      let s : Fin n := ⟨x.2.1, by omega⟩
      let u : Fin n := ⟨x.2.2, by omega⟩
      let v : Fin n := ⟨x.2.2 + d, by
        have hj := x.1.isLt
        have hv := x.2.2.isLt
        dsimp [j, d]
        omega⟩
      exact (r, s, u, v)
  inj' := by
    rintro (x | x) (y | y) h
    · rcases x with ⟨jx, rx, vx⟩
      rcases y with ⟨jy, ry, vy⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      rcases h with ⟨hr, hs, hu, hv⟩
      have hj : jx = jy := by
        apply Fin.ext
        have hxj := jx.isLt
        have hyj := jy.isLt
        omega
      subst jy
      congr
      · exact Fin.ext hr
      · exact Fin.ext hv
    · rcases x with ⟨jx, rx, vx⟩
      rcases y with ⟨jy, sy, uy⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      rcases h with ⟨hr, hs, hu, hv⟩
      have hxj := jx.isLt
      have hyj := jy.isLt
      have hxd : n - (jx.val + 1) < n - jy.val := by omega
      omega
    · rcases x with ⟨jx, sx, ux⟩
      rcases y with ⟨jy, ry, vy⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      rcases h with ⟨hr, hs, hu, hv⟩
      have hxj := jx.isLt
      have hyj := jy.isLt
      have hyd : n - (jy.val + 1) < n - jx.val := by omega
      omega
    · rcases x with ⟨jx, sx, ux⟩
      rcases y with ⟨jy, sy, uy⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      rcases h with ⟨hr, hs, hu, hv⟩
      have hj : jx = jy := by
        apply Fin.ext
        have hxj := jx.isLt
        have hyj := jy.isLt
        omega
      subst jy
      congr
      · exact Fin.ext hs
      · exact Fin.ext hu

lemma triZeroEmbedding_frequency (n : ℕ) (x : TriZeroIndex n) :
    jacksonFrequency (Sum.inl (triZeroEmbedding n x)) = 0 := by
  rcases x with x | x
  · simp only [triZeroEmbedding, jacksonFrequency]
    push_cast
    omega
  · simp only [triZeroEmbedding, jacksonFrequency]
    push_cast
    omega

lemma sum_shift_sq (n : ℕ) :
    (∑ j ∈ Finset.range n, (j + 1) ^ 2) =
      n ^ 2 + ∑ j ∈ Finset.range n, j ^ 2 := by
  calc
    (∑ j ∈ Finset.range n, (j + 1) ^ 2) =
        ∑ j ∈ Finset.range (n + 1), j ^ 2 := by
      rw [Finset.sum_range_succ']
      simp
    _ = n ^ 2 + ∑ j ∈ Finset.range n, j ^ 2 := by
      rw [Finset.sum_range_succ]
      omega

lemma sum_sq_combined (n : ℕ) :
    3 * (n ^ 2 + 2 * ∑ j ∈ Finset.range n, j ^ 2) =
      2 * n ^ 3 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        3 * ((n + 1) ^ 2 + 2 *
            ((∑ j ∈ Finset.range n, j ^ 2) + n ^ 2)) =
            3 * (n ^ 2 + 2 * ∑ j ∈ Finset.range n, j ^ 2) +
              (6 * n ^ 2 + 6 * n + 3) := by ring
        _ = 2 * (n + 1) ^ 3 + (n + 1) := by rw [ih]; ring

/-- Exact cardinality identity for the triangular zero-mode family. -/
lemma triZeroIndex_card_formula (n : ℕ) :
    3 * Fintype.card (TriZeroIndex n) = 2 * n ^ 3 + n := by
  rw [Fintype.card_sum]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j + 1) * (j + 1)) n]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j * j) n]
  simp only [← pow_two]
  rw [sum_shift_sq]
  rw [add_assoc, ← two_mul]
  exact sum_sq_combined n

lemma zeroQuad_count_triangular_lower (n : ℕ) :
    Fintype.card (TriZeroIndex n) ≤
      ((Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun x =>
        jacksonFrequency (Sum.inl x) = 0).card := by
  let s : Finset (TriZeroIndex n) := Finset.univ
  let t := (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun x =>
    jacksonFrequency (Sum.inl x) = 0
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn
    (triZeroEmbedding n)
    (by
      intro x hx
      simpa [t] using triZeroEmbedding_frequency n x)
    (triZeroEmbedding n).injective.injOn
  simpa only [s, t, Finset.card_univ] using hcard

/-- Exact `L1` mass of the unaggregated Jackson presentation at arbitrary
positive order. -/
lemma jacksonCoefficient_mass_general (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    (∑ i : JacksonIndex n, |jacksonCoefficient q n i|) =
      2 * (n : ℝ) ^ 2 / (q : ℝ) ^ 2 + 2 := by
  classical
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [jacksonCoefficient]
  have hmain :
      |(2 / (q : ℝ) ^ 2) / (n : ℝ) ^ 2| =
        (2 / (q : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
    abs_of_nonneg (by positivity)
  rw [hmain]
  simp_rw [abs_div, abs_neg, abs_mul, edgeSign_abs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  field_simp

/-- At Jackson order `q`, the constant coefficient has the displayed exact
triangular lower bound. -/
lemma jackson_zeroCoefficient_self_lower (q : ℕ) (hq : 0 < q) :
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) ≤
      ∑ i : JacksonIndex q with jacksonFrequency i = 0,
        jacksonCoefficient q q i := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ x : (Bool × Fin q) × (Bool × Fin q),
      if jacksonFrequency (Sum.inr x) = 0 then
        jacksonCoefficient q q (Sum.inr x) else 0) =
      -(1 / (q : ℝ)) by
    simpa only [Finset.sum_filter] using
      jacksonEdge_zeroCoefficient q hq]
  let z := (Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter
    fun x => jacksonFrequency (Sum.inl x) = 0
  have hcount := zeroQuad_count_triangular_lower q
  have hcountR : (Fintype.card (TriZeroIndex q) : ℝ) ≤ (z.card : ℝ) := by
    exact_mod_cast hcount
  have hformulaNat := triZeroIndex_card_formula q
  have hformulaR : (Fintype.card (TriZeroIndex q) : ℝ) =
      (2 * (q : ℝ) ^ 3 + q) / 3 := by
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hformulaNat
    push_cast at hcast
    linarith
  have hcoeff : 0 ≤ (2 / (q : ℝ) ^ 2) / (q : ℝ) ^ 2 := by positivity
  have hmain :
      (Fintype.card (TriZeroIndex q) : ℝ) *
          ((2 / (q : ℝ) ^ 2) / (q : ℝ) ^ 2) ≤
        ∑ x : Fin q × Fin q × Fin q × Fin q,
          if jacksonFrequency (Sum.inl x) = 0 then
            jacksonCoefficient q q (Sum.inl x) else 0 := by
    rw [← Finset.sum_filter]
    simp only [jacksonCoefficient, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcountR hcoeff
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3) =
        (Fintype.card (TriZeroIndex q) : ℝ) *
            ((2 / (q : ℝ) ^ 2) / (q : ℝ) ^ 2) -
          1 / (q : ℝ) := by
      rw [hformulaR]
      field_simp
      ring
    _ ≤ _ := by linarith

/-- Exact order-`q` empty-interval theorem. -/
theorem finite_empty_decimalInterval_resonance_exact
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * q ∧
      1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3) ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  let center := a + (q : ℝ)⁻¹ / 2
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finiteFourierPresentation_resonance
      (jacksonCoefficient q q) (@jacksonFrequency q)
      x N (2 * q) center
      (1 / (3 * (q : ℝ)) + 2 / (3 * (q : ℝ) ^ 3)) 4 hN
      (by positivity) (by norm_num)
      jacksonFrequency_bound
      (jackson_zeroCoefficient_self_lower q hq)
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
  refine ⟨h, hzero, hbound, ?_⟩
  convert hlarge using 1
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

/-- Direct contrapositive of the exact empty-interval theorem. -/
theorem finite_decimalInterval_hit_of_exact_frequency_smallness
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hsmall : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) :
    ∃ j : ℕ, j < N ∧ x j ∈ Set.Ico a (a + (q : ℝ)⁻¹) := by
  by_contra hno
  push Not at hno
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finite_empty_decimalInterval_resonance_exact
      x N q a hN hq hx ha haq (fun j hj => hno j hj)
  exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

/-- A missing decimal word in the finite pi orbit forces the exact
order-`q` resonance. -/
theorem piOrbit_naturalScale_resonance_exact_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 2 * 10 ^ s.length ∧
      1 / (24 * (10 : ℝ) ^ s.length) +
          1 / (12 * ((10 : ℝ) ^ s.length) ^ 3) ≤
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
    finite_empty_decimalInterval_resonance_exact
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- The exact finite pi-orbit cancellation target. This remains an open
hypothesis about pi. -/
def PiNaturalScaleCancellationExact : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 0 < N ∧
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * 10 ^ k →
      ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ / (N : ℝ) <
        1 / (24 * (10 : ℝ) ^ k) +
          1 / (12 * ((10 : ℝ) ^ k) ^ 3)

/-- At fixed finite data, T18's smallness hypothesis implies T19's. Together
with `exact_finite_frequency_hypothesis_strict_vs_sharp`, this makes the
finite T19 premise strictly weaker in the literal implication-plus-separator
sense. -/
theorem sharp_finite_frequency_hypothesis_implies_exact
    (x : ℕ → ℝ) (N q : ℕ) (hq : 0 < q)
    (hsharp : ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (40 * (q : ℝ))) :
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
      ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
        1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3) := by
  intro h hzero hbound
  have hboundSharp : h.natAbs ≤ 4 * q :=
    hbound.trans (by omega)
  have hold := hsharp h hzero hboundSharp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hconstants :
      1 / (40 * (q : ℝ)) <
        1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3) := by
    have hfirst :
        1 / (40 * (q : ℝ)) < 1 / (24 * (q : ℝ)) := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · nlinarith
    have hextra : 0 < 1 / (12 * (q : ℝ) ^ 3) := by positivity
    linarith
  exact hold.trans hconstants

/-- T18's stronger finite spectral target implies the exact order-`q`
target. -/
theorem piNaturalScaleCancellationSharp_implies_exact
    (hsharp : PiNaturalScaleCancellationSharp) :
    PiNaturalScaleCancellationExact := by
  intro k hk
  obtain ⟨N, hN, hsmall⟩ := hsharp k hk
  refine ⟨N, hN, ?_⟩
  intro h hzero hbound
  have hboundSharp : h.natAbs ≤ 4 * 10 ^ k :=
    hbound.trans (by omega)
  have hold := hsmall h hzero hboundSharp
  have hpow : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hconstants :
      1 / (40 * (10 : ℝ) ^ k) <
        1 / (24 * (10 : ℝ) ^ k) +
          1 / (12 * ((10 : ℝ) ^ k) ^ 3) := by
    have hfirst :
        1 / (40 * (10 : ℝ) ^ k) <
          1 / (24 * (10 : ℝ) ^ k) := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · nlinarith
    have hextra : 0 < 1 / (12 * ((10 : ℝ) ^ k) ^ 3) := by positivity
    linarith
  exact hold.trans hconstants

/-- The exact finite cancellation target implies canonical V1. The premise
is not proved for pi. -/
theorem piNaturalScaleCancellationExact_implies_canonicalV1
    (hexact : PiNaturalScaleCancellationExact) : Theory.PiDigits.V1 := by
  intro s
  cases s with
  | nil => exact ⟨0, by simp⟩
  | cons d s =>
      obtain ⟨N, hN, hsmall⟩ := hexact (d :: s).length (by simp)
      by_contra hmissing
      have hmissingBefore : ∀ n : ℕ, n < N →
          ¬ ∀ i : ℕ, ∀ hi : i < (d :: s).length,
            Theory.PiDigits.piDigit (n + i) = (d :: s).get ⟨i, hi⟩ := by
        intro n hn hocc
        exact hmissing ⟨n, hocc⟩
      obtain ⟨h, hzero, hbound, hlarge⟩ :=
        piOrbit_naturalScale_resonance_exact_of_missingBefore
          (d :: s) N hN hmissingBefore
      exact (not_lt_of_ge hlarge) (hsmall h hzero hbound)

lemma uniformGridThree_small_first_two :
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 →
      ‖Theory.PiDigits.T27.exponentialSum (uniformGrid 3) 3 h‖ / (3 : ℝ) <
        1 / (24 : ℝ) + 1 / (12 : ℝ) := by
  intro h hzero hbound
  have hk : 0 < h.natAbs := Int.natAbs_pos.mpr hzero
  have hk3 : h.natAbs < 3 := by omega
  have hpos := uniformGrid_exponentialSum_nat_eq_zero
    h.natAbs 3 (by norm_num) hk hk3
  rcases Int.natAbs_eq h with hh | hh
  · rw [hh, hpos]
    norm_num
  · rw [hh, exponentialSum_neg, hpos, map_zero]
    norm_num

/-- The exact finite spectral premise is strictly weaker than T18's premise.
The uniform three-point grid cancels frequencies `1` and `2`, but is fully
resonant at frequency `3`, which T18 still controls. -/
theorem exact_finite_frequency_hypothesis_strict_vs_sharp :
    ∃ x : ℕ → ℝ, ∃ N q : ℕ, 0 < N ∧ 0 < q ∧
      (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 2 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (24 * (q : ℝ)) + 1 / (12 * (q : ℝ) ^ 3)) ∧
      ¬ (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ 4 * q →
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) <
          1 / (40 * (q : ℝ))) := by
  refine ⟨uniformGrid 3, 3, 1, by norm_num, by norm_num, ?_, ?_⟩
  · simpa using uniformGridThree_small_first_two
  · intro hsharp
    have hthree := hsharp 3 (by norm_num) (by norm_num)
    have hsum :
        Theory.PiDigits.T27.exponentialSum (uniformGrid 3) 3 (3 : ℤ) =
          (3 : ℂ) := by
      simpa using uniformGrid_exponentialSum_self 3 (by norm_num)
    rw [hsum] at hthree
    norm_num at hthree

end Theory.PiDigits.ExactNaturalScaleResonance

#print axioms Theory.PiDigits.ExactNaturalScaleResonance.triZeroEmbedding_frequency
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.triZeroIndex_card_formula
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.zeroQuad_count_triangular_lower
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.jacksonCoefficient_mass_general
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.jackson_zeroCoefficient_self_lower
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.finite_empty_decimalInterval_resonance_exact
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.finite_decimalInterval_hit_of_exact_frequency_smallness
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.piOrbit_naturalScale_resonance_exact_of_missingBefore
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.sharp_finite_frequency_hypothesis_implies_exact
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.piNaturalScaleCancellationSharp_implies_exact
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.piNaturalScaleCancellationExact_implies_canonicalV1
#print axioms Theory.PiDigits.ExactNaturalScaleResonance.exact_finite_frequency_hypothesis_strict_vs_sharp
