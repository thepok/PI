import TheoryLib.PiQuantitativeBlockHitting.T1PiQuantitativeBlockHitting
import TheoryLib.PiQuantitativeBlockHitting.T3UniformPiAnalyticCover
import TheoryLib.PiQuantitativeBlockHitting.T5PiQuantitativeResonanceObstruction
import TheoryLib.PiDigits.T27FiniteExponentialCylinderCoverage

/-!
# Natural-scale resonance forced by an empty decimal interval

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

The results below are necessary conditions only.  No converse is proved, and
the final theorem neither proves nor refutes C1.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.PiNaturalScaleResonanceObstruction

/-- Indices for the two pieces of the finite Jackson minorant. -/
abbrev JacksonIndex (n : ℕ) :=
  (Fin n × Fin n × Fin n × Fin n) ⊕ ((Bool × Fin n) × (Bool × Fin n))

/-- The signed frequencies in `(1-X)F`, where `F` is the normalized Fejer
kernel of order `n-1`. -/
def edgeFrequency {n : ℕ} (i : Bool × Fin n) : ℤ :=
  if i.1 then (n : ℤ) - i.2 else -(i.2 : ℤ)

/-- The signs of the coefficients in `(1-X)F`. -/
def edgeSign {n : ℕ} (i : Bool × Fin n) : ℝ :=
  if i.1 then -1 else 1

/-- Frequency attached to one term of the finite Jackson presentation. -/
def jacksonFrequency {n : ℕ} : JacksonIndex n → ℤ
  | Sum.inl (r, s, u, v) =>
      ((s : ℤ) - (r : ℤ)) + ((v : ℤ) - (u : ℤ))
  | Sum.inr (i, j) => edgeFrequency j - edgeFrequency i

/-- Coefficient attached to one term of the finite Jackson presentation. -/
def jacksonCoefficient (q n : ℕ) : JacksonIndex n → ℝ
  | Sum.inl _ => (2 / (q : ℝ) ^ 2) / (n : ℝ) ^ 2
  | Sum.inr (i, j) =>
      -(edgeSign i * edgeSign j) / (2 * (n : ℝ) ^ 2)

/-- The explicit finite trigonometric polynomial used below. -/
def jacksonMinorant (q n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : JacksonIndex n,
    jacksonCoefficient q n i * Theory.PiDigits.T27.phase (jacksonFrequency i) t

/-- An explicit family of zero-frequency terms giving the lower bound on the
constant coefficient of the Jackson minorant. -/
def zeroQuadEmbedding (q : ℕ) :
    (Fin (16 * q) × Fin (16 * q) × Fin (32 * q)) ↪
      (Fin (64 * q) × Fin (64 * q) × Fin (64 * q) × Fin (64 * q)) where
  toFun x :=
    let r : Fin (64 * q) := ⟨x.1, by omega⟩
    let s : Fin (64 * q) := ⟨x.2.1, by omega⟩
    let u : Fin (64 * q) := ⟨16 * q + x.2.2, by omega⟩
    let v : Fin (64 * q) := ⟨16 * q + x.2.2 + x.1 - x.2.1, by omega⟩
    (r, s, u, v)
  inj' := by
    rintro ⟨r, s, t⟩ ⟨r', s', t'⟩ h
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    rcases h with ⟨hr, hs, hu, _⟩
    have hrr : r = r' := Fin.ext hr
    have hss : s = s' := Fin.ext hs
    have htt : t = t' := Fin.ext (by omega)
    simp [hrr, hss, htt]

lemma zeroQuadEmbedding_frequency (q : ℕ)
    (x : Fin (16 * q) × Fin (16 * q) × Fin (32 * q)) :
    jacksonFrequency (Sum.inl (zeroQuadEmbedding q x)) = 0 := by
  rcases x with ⟨r, s, t⟩
  simp only [zeroQuadEmbedding, jacksonFrequency]
  push_cast
  omega

lemma zeroQuad_count_lower (q : ℕ) :
    (16 * q) * (16 * q) * (32 * q) ≤
      ((Finset.univ : Finset (Fin (64 * q) × Fin (64 * q) ×
        Fin (64 * q) × Fin (64 * q))).filter fun x =>
          jacksonFrequency (Sum.inl x) = 0).card := by
  let s : Finset (Fin (16 * q) × Fin (16 * q) × Fin (32 * q)) := Finset.univ
  let t := (Finset.univ : Finset (Fin (64 * q) × Fin (64 * q) ×
    Fin (64 * q) × Fin (64 * q))).filter fun x =>
      jacksonFrequency (Sum.inl x) = 0
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn
    (zeroQuadEmbedding q)
    (by
      intro x hx
      simpa [t] using zeroQuadEmbedding_frequency q x)
    (zeroQuadEmbedding q).injective.injOn
  simpa only [s, t, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_assoc] using hcard

lemma edgeFrequency_injective {n : ℕ} : Function.Injective (@edgeFrequency n) := by
  rintro ⟨b, r⟩ ⟨c, s⟩ h
  cases b with
  | false =>
      cases c with
      | false =>
          change -(r : ℤ) = -(s : ℤ) at h
          simp only [Prod.mk.injEq, true_and]
          exact Fin.ext (by omega)
      | true =>
          change -(r : ℤ) = (n : ℤ) - (s : ℤ) at h
          have hr0 : 0 ≤ (r : ℤ) := by omega
          have hslt : (s : ℤ) < n := by exact_mod_cast s.isLt
          exfalso
          omega
  | true =>
      cases c with
      | false =>
          change (n : ℤ) - (r : ℤ) = -(s : ℤ) at h
          have hs0 : 0 ≤ (s : ℤ) := by omega
          have hrlt : (r : ℤ) < n := by exact_mod_cast r.isLt
          exfalso
          omega
      | true =>
          change (n : ℤ) - (r : ℤ) = (n : ℤ) - (s : ℤ) at h
          simp only [Prod.mk.injEq, true_and]
          exact Fin.ext (by omega)

lemma edgeFrequency_natAbs_le {n : ℕ} (i : Bool × Fin n) :
    (edgeFrequency i).natAbs ≤ n := by
  rcases i with ⟨b, r⟩
  cases b with
  | false => simp [edgeFrequency]
  | true =>
      simp only [edgeFrequency, if_true]
      rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt r.isLt)]
      omega

lemma jacksonFrequency_bound {n : ℕ} (i : JacksonIndex n) :
    (jacksonFrequency i).natAbs ≤ 2 * n := by
  rcases i with ⟨⟨r, s, u, v⟩⟩ | ⟨i, j⟩
  · simp only [jacksonFrequency]
    have hlo : -(2 * (n : ℤ)) ≤
        ((s : ℤ) - (r : ℤ)) + ((v : ℤ) - (u : ℤ)) := by
      have hr := r.isLt
      have hs := s.isLt
      have hu := u.isLt
      have hv := v.isLt
      omega
    have hhi : ((s : ℤ) - (r : ℤ)) + ((v : ℤ) - (u : ℤ)) ≤
        2 * (n : ℤ) := by
      have hr := r.isLt
      have hs := s.isLt
      have hu := u.isLt
      have hv := v.isLt
      omega
    have habs : Int.natAbs (((s : ℤ) - (r : ℤ)) + ((v : ℤ) - (u : ℤ))) ≤
        Int.natAbs (2 * (n : ℤ)) :=
      Int.natAbs_le_iff_sq_le.mpr (by nlinarith)
    simpa using habs
  · simp only [jacksonFrequency, edgeFrequency]
    calc
      (edgeFrequency j - edgeFrequency i).natAbs ≤
          (edgeFrequency j).natAbs + (edgeFrequency i).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ n + n := Nat.add_le_add (edgeFrequency_natAbs_le j)
        (edgeFrequency_natAbs_le i)
      _ = 2 * n := by omega

/-- The unnormalized geometric sum used to define the Fejer factor. -/
def geometricSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range n, Theory.PiDigits.T27.phase (r : ℤ) t

/-- The normalized Fejer factor occurring in the Jackson minorant. -/
def fejerFactor (n : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq (geometricSum n t) / n

lemma pairPhaseSum_eq (n : ℕ) (t : ℝ) :
    ∑ r : Fin n, ∑ s : Fin n,
        Theory.PiDigits.T27.phase ((s : ℤ) - (r : ℤ)) t =
      (fejerFactor n t : ℂ) * n := by
  classical
  have hnC : (n : ℂ) = 0 ∨ (n : ℂ) ≠ 0 := eq_or_ne _ _
  rcases hnC with hnC | hnC
  · have hn : n = 0 := by exact_mod_cast hnC
    subst n
    simp [fejerFactor, geometricSum]
  · rw [fejerFactor, Complex.ofReal_div]
    push_cast
    rw [div_mul_cancel₀ _ hnC]
    change (∑ r : Fin n, ∑ s : Fin n,
      Theory.PiDigits.T27.phase ((s : ℤ) - (r : ℤ)) t) =
        (Complex.normSq (geometricSum n t) : ℂ)
    rw [Complex.normSq_eq_conj_mul_self]
    have hgeom : geometricSum n t =
        ∑ r : Fin n, Theory.PiDigits.T27.phase (r : ℤ) t := by
      exact (Fin.sum_univ_eq_sum_range
        (fun r : ℕ => Theory.PiDigits.T27.phase (r : ℤ) t) n).symm
    rw [hgeom, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    exact (Theory.PiDigits.T27.phase_sub (r : ℤ) (s : ℤ) t).symm

lemma geometricSum_mul_one_sub_phase (n : ℕ) (t : ℝ) :
    geometricSum n t * (1 - Theory.PiDigits.T27.phase 1 t) =
      1 - Theory.PiDigits.T27.phase (n : ℤ) t := by
  simp_rw [geometricSum, Theory.PiDigits.T27.phase_nat_eq_pow]
  exact geom_sum_mul_neg (Theory.PiDigits.T27.phase 1 t) n

/-- The Fourier presentation of `(1-X)F`. -/
def edgeValue (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i : Bool × Fin n,
    (edgeSign i / n) * Theory.PiDigits.T27.phase (edgeFrequency i) t

lemma edgeValue_eq (n : ℕ) (hn : 0 < n) (t : ℝ) :
    edgeValue n t =
      (1 - Theory.PiDigits.T27.phase 1 t) * (fejerFactor n t : ℂ) := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgeom : geometricSum n t =
      ∑ r : Fin n, Theory.PiDigits.T27.phase (r : ℤ) t := by
    exact (Fin.sum_univ_eq_sum_range
      (fun r : ℕ => Theory.PiDigits.T27.phase (r : ℤ) t) n).symm
  have hneg : (∑ r : Fin n, Theory.PiDigits.T27.phase (-(r : ℤ)) t) =
      conj (geometricSum n t) := by
    rw [hgeom, map_sum]
    simp only [Theory.PiDigits.T27.phase_neg]
  have hphase (r : Fin n) :
      Theory.PiDigits.T27.phase ((n : ℤ) - (r : ℤ)) t =
        Theory.PiDigits.T27.phase (n : ℤ) t *
          Theory.PiDigits.T27.phase (-(r : ℤ)) t := by
    rw [show (n : ℤ) - (r : ℤ) = (n : ℤ) + -(r : ℤ) by ring,
      Theory.PiDigits.T27.phase_add]
  have hedge : edgeValue n t =
      (1 - Theory.PiDigits.T27.phase (n : ℤ) t) *
        conj (geometricSum n t) / n := by
    rw [edgeValue, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [edgeSign, edgeFrequency]
    simp_rw [hphase]
    rw [← hneg]
    simp_rw [div_eq_mul_inv]
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hedge, fejerFactor, Complex.ofReal_div]
  change (1 - Theory.PiDigits.T27.phase (n : ℤ) t) *
      conj (geometricSum n t) / n =
    (1 - Theory.PiDigits.T27.phase 1 t) *
      ((Complex.normSq (geometricSum n t) : ℂ) / n)
  rw [Complex.normSq_eq_conj_mul_self]
  rw [← geometricSum_mul_one_sub_phase]
  field_simp

lemma jacksonMainSum_eq (q n : ℕ) (hn : 0 < n) (t : ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n,
      jacksonCoefficient q n (Sum.inl x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inl x)) t) =
      (2 / (q : ℝ) ^ 2) * (fejerFactor n t : ℂ) ^ 2 := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [jacksonCoefficient, jacksonFrequency]
  simp_rw [Theory.PiDigits.T27.phase_add]
  have hp := pairPhaseSum_eq n t
  push_cast at hp ⊢
  simp_rw [div_eq_mul_inv]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [hp]
  field_simp

lemma jacksonEdgeSum_eq (n : ℕ) (_hn : 0 < n) (t : ℝ) :
    (∑ x : (Bool × Fin n) × (Bool × Fin n),
      jacksonCoefficient 1 n (Sum.inr x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inr x)) t) =
      -(1 / 2 : ℝ) * Complex.normSq (edgeValue n t) := by
  classical
  have hcoeff (i : Bool × Fin n) :
      conj ((edgeSign i : ℂ) / (n : ℂ)) =
        (edgeSign i : ℂ) / (n : ℂ) := by
    simp
  rw [Fintype.sum_prod_type]
  simp only [jacksonCoefficient, jacksonFrequency]
  simp_rw [← Theory.PiDigits.T27.phase_sub]
  rw [Complex.normSq_eq_conj_mul_self, edgeValue, map_sum, Finset.sum_mul]
  simp only [map_mul]
  simp_rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoeff i]
  ring

/-- Closed form of the explicit finite Fourier presentation. -/
lemma jacksonMinorant_eq (q n : ℕ) (_hq : 0 < q) (hn : 0 < n) (t : ℝ) :
    jacksonMinorant q n t =
      ((2 / (q : ℝ) ^ 2) * fejerFactor n t ^ 2 -
        (1 / 2 : ℝ) * Complex.normSq (edgeValue n t) : ℝ) := by
  rw [jacksonMinorant, Fintype.sum_sum_type]
  rw [jacksonMainSum_eq q n hn t]
  have hedge := jacksonEdgeSum_eq n hn t
  have hqedge : (∑ x : (Bool × Fin n) × (Bool × Fin n),
      jacksonCoefficient q n (Sum.inr x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inr x)) t) =
      ∑ x : (Bool × Fin n) × (Bool × Fin n),
      jacksonCoefficient 1 n (Sum.inr x) *
        Theory.PiDigits.T27.phase (jacksonFrequency (Sum.inr x)) t := by
    apply Finset.sum_congr rfl
    intro x hx
    rfl
  rw [hqedge, hedge]
  push_cast
  ring

lemma edgeSign_abs (i : Bool × Fin n) : |edgeSign i| = 1 := by
  rcases i with ⟨b, r⟩
  cases b <;> simp [edgeSign]

lemma jacksonCoefficient_mass (q : ℕ) (hq : 0 < q) :
    (∑ i : JacksonIndex (64 * q),
      |jacksonCoefficient q (64 * q) i|) = 8194 := by
  classical
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [jacksonCoefficient]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmain :
      |(2 / (q : ℝ) ^ 2) / ((64 * q : ℕ) : ℝ) ^ 2| =
        (2 / (q : ℝ) ^ 2) / ((64 * q : ℕ) : ℝ) ^ 2 :=
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

lemma jacksonEdge_zeroCoefficient (n : ℕ) (hn : 0 < n) :
    (∑ x : (Bool × Fin n) × (Bool × Fin n) with
        jacksonFrequency (Sum.inr x) = 0,
      jacksonCoefficient 1 n (Sum.inr x)) = -(1 / (n : ℝ)) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [jacksonFrequency, sub_eq_zero]
  simp_rw [edgeFrequency_injective.eq_iff]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsign (i : Bool × Fin n) : edgeSign i ^ 2 = 1 := by
    rcases i with ⟨b, r⟩
    cases b <;> simp [edgeSign]
  have hsum : (∑ i : Bool × Fin n, edgeSign i ^ 2) = 2 * n := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [edgeSign]
    ring
  simp [jacksonCoefficient]
  calc
    (∑ i : Bool × Fin n, -(edgeSign i * edgeSign i) /
        (2 * (n : ℝ) ^ 2)) =
        (∑ i : Bool × Fin n, edgeSign i ^ 2) *
          ((n : ℝ)⁻¹ ^ 2 * (-1 / 2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ = -(n : ℝ)⁻¹ := by
      rw [hsum]
      field_simp

lemma jackson_zeroCoefficient_lower (q : ℕ) (hq : 0 < q) :
    (1 / (q : ℝ)) ≤
      ∑ i : JacksonIndex (64 * q) with jacksonFrequency i = 0,
        jacksonCoefficient q (64 * q) i := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ x : (Bool × Fin (64 * q)) × (Bool × Fin (64 * q)),
      if jacksonFrequency (Sum.inr x) = 0 then
        jacksonCoefficient q (64 * q) (Sum.inr x) else 0) =
      -(1 / ((64 * q : ℕ) : ℝ)) by
    simpa only [Finset.sum_filter] using
      jacksonEdge_zeroCoefficient (64 * q) (by omega)]
  have hcount := zeroQuad_count_lower q
  have hcoeff : 0 ≤
      (2 / (q : ℝ) ^ 2) / (((64 * q : ℕ) : ℝ) ^ 2) := by positivity
  have hmain :
      (((16 * q) * (16 * q) * (32 * q) : ℕ) : ℝ) *
          ((2 / (q : ℝ) ^ 2) / (((64 * q : ℕ) : ℝ) ^ 2)) ≤
        ∑ x : Fin (64 * q) × Fin (64 * q) × Fin (64 * q) × Fin (64 * q),
          if jacksonFrequency (Sum.inl x) = 0 then
            jacksonCoefficient q (64 * q) (Sum.inl x) else 0 := by
    rw [← Finset.sum_filter]
    simp only [jacksonCoefficient, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hcoeff
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    1 / (q : ℝ) ≤
        (((16 * q) * (16 * q) * (32 * q) : ℕ) : ℝ) *
          ((2 / (q : ℝ) ^ 2) / (((64 * q : ℕ) : ℝ) ^ 2)) -
            1 / ((64 * q : ℕ) : ℝ) := by
          push_cast
          field_simp
          nlinarith
    _ ≤ _ := by linarith

lemma fejerFactor_nonneg (n : ℕ) (t : ℝ) : 0 ≤ fejerFactor n t := by
  unfold fejerFactor
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

/-- The explicit Jackson polynomial is nonpositive at every point outside the
given interval of length `1/q`. -/
theorem jacksonMinorant_re_nonpos_outside
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (x a : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (ha : 0 ≤ a)
    (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hout : x ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    (jacksonMinorant q n
      (x - (a + (q : ℝ)⁻¹ / 2))).re ≤ 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hL : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  have hsep := Theory.PiDigits.T27.phase_separation_of_outside_interval
    hx ha hL haq hout
  have hnormsq : 4 / (q : ℝ) ^ 2 ≤
      Complex.normSq
        (1 - Theory.PiDigits.T27.phase 1
          (x - (a + (q : ℝ)⁻¹ / 2))) := by
    rw [Complex.normSq_eq_norm_sq]
    have hnonneg : 0 ≤ ‖1 - Theory.PiDigits.T27.phase 1
        (x - (a + (q : ℝ)⁻¹ / 2))‖ := norm_nonneg _
    have hqne : (q : ℝ) ≠ 0 := hqR.ne'
    field_simp at hsep ⊢
    nlinarith
  rw [jacksonMinorant_eq q n hq hn,
    edgeValue_eq n hn, Complex.normSq_mul]
  have hreal : Complex.normSq
      (fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) : ℂ) =
      fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [hreal]
  change 2 / (q : ℝ) ^ 2 *
      fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2 -
        1 / 2 * (Complex.normSq
          (1 - Theory.PiDigits.T27.phase 1
            (x - (a + (q : ℝ)⁻¹ / 2))) *
              fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2) ≤ 0
  have hsq : 0 ≤ fejerFactor n
      (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hnormsq hsq
  calc
    2 / (q : ℝ) ^ 2 * fejerFactor n
          (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2 -
        1 / 2 * (Complex.normSq
          (1 - Theory.PiDigits.T27.phase 1
            (x - (a + (q : ℝ)⁻¹ / 2))) *
              fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2) ≤
      2 / (q : ℝ) ^ 2 * fejerFactor n
          (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2 -
        1 / 2 * (4 / (q : ℝ) ^ 2 *
          fejerFactor n (x - (a + (q : ℝ)⁻¹ / 2)) ^ 2) := by
            exact sub_le_sub_left
              (mul_le_mul_of_nonneg_left hmul (by norm_num)) _
    _ = 0 := by ring

/-- A reusable finite Fourier principle: a positive zero coefficient and a
nonpositive empirical sum force a nonzero resonant frequency. -/
theorem finiteFourierPresentation_resonance
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
      c0 / (2 * A) ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
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
        (N : ℝ) * (c0 / (2 * A)) := by
    have hi' := hnone (frequency i) hi (hfrequency i)
    simpa [mul_comm] using (div_le_iff₀ hNR).mp hi'.le
  have hzupper : ‖z‖ ≤ c0 * (N : ℝ) / 2 := by
    calc
      ‖z‖ ≤ ∑ i with frequency i ≠ 0,
          ‖coefficient i * Theory.PiDigits.T27.phase (frequency i) (-center) *
            Theory.PiDigits.T27.exponentialSum x N (frequency i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i with frequency i ≠ 0,
          |coefficient i| * ((N : ℝ) * (c0 / (2 * A))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Theory.PiDigits.T27.norm_phase, mul_one]
        exact mul_le_mul_of_nonneg_left (hterm i (Finset.mem_filter.mp hi).2)
          (abs_nonneg _)
      _ = (∑ i with frequency i ≠ 0, |coefficient i|) *
          ((N : ℝ) * (c0 / (2 * A))) := by rw [Finset.sum_mul]
      _ ≤ A * ((N : ℝ) * (c0 / (2 * A))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          (∑ i with frequency i ≠ 0, |coefficient i|) ≤
              ∑ i, |coefficient i| := by
            rw [Finset.sum_filter]
            apply Finset.sum_le_sum
            intro i hi
            split <;> simp [abs_nonneg]
          _ ≤ A := hmass
      _ = c0 * (N : ℝ) / 2 := by field_simp
  nlinarith

/-- Public generic empty-interval theorem at the natural frequency scale. -/
theorem finite_empty_decimalInterval_resonance
    (x : ℕ → ℝ) (N q : ℕ) (a : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hx : ∀ j < N, x j ∈ Set.Ico (0 : ℝ) 1)
    (ha : 0 ≤ a) (haq : a + (q : ℝ)⁻¹ ≤ 1)
    (hempty : ∀ j < N, x j ∉ Set.Ico a (a + (q : ℝ)⁻¹)) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 128 * q ∧
      1 / (16388 * (q : ℝ)) ≤
        ‖Theory.PiDigits.T27.exponentialSum x N h‖ / (N : ℝ) := by
  let center := a + (q : ℝ)⁻¹ / 2
  have hn : 0 < 64 * q := by omega
  obtain ⟨h, hzero, hbound, hlarge⟩ :=
    finiteFourierPresentation_resonance
      (jacksonCoefficient q (64 * q)) (@jacksonFrequency (64 * q))
      x N (128 * q) center (1 / (q : ℝ)) 8194 hN
      (by positivity) (by norm_num)
      (fun i => (jacksonFrequency_bound i).trans_eq (by omega))
      (jackson_zeroCoefficient_lower q hq)
      (by rw [jacksonCoefficient_mass q hq])
      (by
        intro j hj
        simpa only [jacksonMinorant, center] using
          jacksonMinorant_re_nonpos_outside q (64 * q) hq hn (x j) a
            (hx j hj) ha haq (hempty j hj))
  refine ⟨h, hzero, hbound, ?_⟩
  convert hlarge using 1
  · have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    norm_num

/-- A missing decimal word among the first `N` starts gives a natural-scale
resonance for the base-ten orbit of pi. -/
theorem piOrbit_naturalScale_resonance_of_missingBefore
    (s : List (Fin 10)) (N : ℕ) (hN : 0 < N)
    (hmissing : ∀ n : ℕ, n < N → ¬ ∀ i : ℕ, ∀ hi : i < s.length,
      Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 128 * 10 ^ s.length ∧
      1 / (16388 * (10 : ℝ) ^ s.length) ≤
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
    finite_empty_decimalInterval_resonance
      Theory.PiDigits.T27.piFractionalOrbit N q a hN hq
      (fun j _ => Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j)
      (Theory.PiDigits.T27.decimalCylinderLeft_nonneg s)
      (by
        have hpow : (q : ℝ) = (10 : ℝ) ^ s.length := by simp [q]
        rw [hpow]
        simpa only [a, Theory.PiDigits.T27.decimalCylinderLength] using
          Theory.PiDigits.T27.decimalCylinderRight_le_one s)
      hempty

/-- Full-containment form of the pi specialization, with the exact number of
admissible starts. -/
theorem normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment
    (C k : ℕ) (hC : 1 ≤ C)
    (w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k)
    (hmissing : ¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
      ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) :
    ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 128 * 10 ^ k ∧
      1 / (16388 * (10 : ℝ) ^ k) ≤
        ‖Theory.PiDigits.T27.exponentialSum Theory.PiDigits.T27.piFractionalOrbit
          (C * k * 10 ^ k - k + 1) h‖ /
            ((C * k * 10 ^ k - k + 1 : ℕ) : ℝ) := by
  let D := C * k * 10 ^ k
  let N := D - k + 1
  let s : List (Fin 10) := List.ofFn w
  have hkD : k ≤ D := by
    dsimp [D]
    calc
      k = 1 * k * 1 := by omega
      _ ≤ C * k * 10 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul hC le_rfl)
          (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))
  have hN : 0 < N := by dsimp [N]; omega
  have hmissingBefore : ∀ n : ℕ, n < N →
      ¬ ∀ i : ℕ, ∀ hi : i < s.length,
        Theory.PiDigits.piDigit (n + i) = s.get ⟨i, hi⟩ := by
    intro n hn hocc
    apply hmissing
    refine ⟨n, ?_, ?_⟩
    · dsimp [N]
      omega
    · intro j
      have hj : j.val < s.length := by simp only [s, List.length_ofFn, j.isLt]
      simpa only [s, List.get_ofFn] using hocc j.val hj
  simpa only [s, List.length_ofFn, N, D] using
    piOrbit_naturalScale_resonance_of_missingBefore s N hN hmissingBefore

/-- Literal failure of C1 forces either failure of V1 or unbounded bad lengths
with a natural-scale pi-orbit resonance.  This is necessary-only. -/
theorem not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance
    (hnotC1 : ¬ Theory.PiDigits.QuantitativeBlockHitting.C1) :
    (¬ Theory.PiDigits.V1) ∨
      (Theory.PiDigits.V1 ∧
        ∀ C K : ℕ, 1 ≤ C → 1 ≤ K →
          ∃ k : ℕ, K ≤ k ∧
            ∃ w : Theory.PiDigits.QuantitativeBlockHitting.DecimalWord k,
            (¬ ∃ n : ℕ, n + k ≤ C * k * 10 ^ k ∧
              ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
            ∃ h : ℤ, h ≠ 0 ∧ h.natAbs ≤ 128 * 10 ^ k ∧
              1 / (16388 * (k + 1 : ℝ) * (10 : ℝ) ^ k) ≤
                ‖Theory.PiDigits.T27.exponentialSum
                  Theory.PiDigits.T27.piFractionalOrbit
                  (C * k * 10 ^ k - k + 1) h‖ /
                    ((C * k * 10 ^ k - k + 1 : ℕ) : ℝ)) := by
  rcases Theory.PiDigits.QuantitativeResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_resonance
      hnotC1 with hV1 | hright
  · exact Or.inl hV1
  · right
    refine ⟨hright.1, ?_⟩
    intro C K hC hK
    obtain ⟨k, hk, w, hmissing, hold⟩ := hright.2 C K hC hK
    obtain ⟨h, hzero, hbound, hlarge⟩ :=
      normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment
        C k hC w hmissing
    refine ⟨k, hk, w, hmissing, h, hzero, hbound, ?_⟩
    exact (by
      have hkR : (1 : ℝ) ≤ k + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      calc
        1 / (16388 * (k + 1 : ℝ) * (10 : ℝ) ^ k) ≤
            1 / (16388 * (10 : ℝ) ^ k) := by
              apply one_div_le_one_div_of_le
              · positivity
              · nlinarith [mul_le_mul_of_nonneg_right hkR
                  (show (0 : ℝ) ≤ 16388 * (10 : ℝ) ^ k by positivity)]
        _ ≤ _ := hlarge)

#print axioms finite_empty_decimalInterval_resonance
#print axioms piOrbit_naturalScale_resonance_of_missingBefore
#print axioms normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment
#print axioms not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance

end Theory.PiDigits.PiNaturalScaleResonanceObstruction
