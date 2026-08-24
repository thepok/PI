import TheoryLib.PiQuantitativeBlockHitting.T127T127BoundaryKernelRatioAlgebra
import TheoryLib.PiQuantitativeBlockHitting.T128T128BoundaryMatchedKernel

/-!
# T129: exact boundary zero mode

This file computes the zero Fourier coefficient of the boundary-matched
cosine--Fejer-squared kernel exactly.  It does not assert cancellation for the
decimal orbit of pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.BoundaryKernelNormalizedComparison

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.ExactNaturalScaleResonance
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel

private abbrev ZeroQuad (q : ℕ) :=
  {x : Fin q × Fin q × Fin q × Fin q // jacksonFrequency (Sum.inl x) = 0}

private def triZeroEquivFun (q : ℕ) : TriZeroIndex q → ZeroQuad q :=
  fun x => ⟨triZeroEmbedding q x, triZeroEmbedding_frequency q x⟩

private lemma triZeroEquivFun_injective (q : ℕ) :
    Function.Injective (triZeroEquivFun q) := by
  intro x y h
  exact (triZeroEmbedding q).injective (congrArg Subtype.val h)

private lemma triZeroEquivFun_surjective (q : ℕ) :
    Function.Surjective (triZeroEquivFun q) := by
  rintro ⟨⟨r, s, u, v⟩, hfreq⟩
  simp only [jacksonFrequency] at hfreq
  by_cases hrs : r.val ≤ s.val
  · have hvu : v.val ≤ u.val := by
      omega
    let d := s.val - r.val
    have hdlt : d < q := by
      dsimp [d]
      omega
    let j : Fin q := ⟨q - (d + 1), by omega⟩
    have hjval : j.val + 1 = q - d := by
      dsimp [j]
      omega
    let r' : Fin (j + 1) := ⟨r.val, by
      rw [hjval]
      omega⟩
    let v' : Fin (j + 1) := ⟨v.val, by
      rw [hjval]
      omega⟩
    let y : TriZeroIndex q := Sum.inl ⟨j, (r', v')⟩
    refine ⟨y, Subtype.ext ?_⟩
    apply Prod.ext
    · exact Fin.ext (by simp [triZeroEquivFun, y, triZeroEmbedding, r'])
    apply Prod.ext
    · exact Fin.ext (by
        simp [triZeroEquivFun, y, triZeroEmbedding, r', j, d]
        omega)
    apply Prod.ext
    · exact Fin.ext (by
        simp [triZeroEquivFun, y, triZeroEmbedding, v', j, d]
        omega)
    · exact Fin.ext (by simp [triZeroEquivFun, y, triZeroEmbedding, v'])
  · have hsr : s.val < r.val := Nat.lt_of_not_ge hrs
    have huv : u.val ≤ v.val := by
      omega
    let d := r.val - s.val
    have hdpos : 0 < d := by dsimp [d]; omega
    have hdle : d ≤ q := by dsimp [d]; omega
    let j : Fin q := ⟨q - d, by omega⟩
    have hjval : j.val = q - d := rfl
    let s' : Fin j := ⟨s.val, by
      rw [hjval]
      omega⟩
    let u' : Fin j := ⟨u.val, by
      rw [hjval]
      omega⟩
    let y : TriZeroIndex q := Sum.inr ⟨j, (s', u')⟩
    refine ⟨y, Subtype.ext ?_⟩
    apply Prod.ext
    · exact Fin.ext (by
        simp [triZeroEquivFun, y, triZeroEmbedding, s', j, d]
        omega)
    apply Prod.ext
    · exact Fin.ext (by simp [triZeroEquivFun, y, triZeroEmbedding, s'])
    apply Prod.ext
    · exact Fin.ext (by simp [triZeroEquivFun, y, triZeroEmbedding, u'])
    · exact Fin.ext (by
        simp [triZeroEquivFun, y, triZeroEmbedding, u', j, d]
        omega)

/-- The triangular zero-frequency parametrization from T19 is exact, not just
an injection. -/
lemma zeroQuad_card_exact (q : ℕ) :
    ((Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter fun x =>
        jacksonFrequency (Sum.inl x) = 0).card =
      Fintype.card (TriZeroIndex q) := by
  classical
  let s := (Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter fun x =>
    jacksonFrequency (Sum.inl x) = 0
  let ep : ZeroQuad q ≃ {x // x ∈ s} :=
    { toFun := fun x => ⟨x.val, by
        dsimp [s]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun x => ⟨x.val, by
        have hx : x.val ∈
            (Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter
              (fun y => jacksonFrequency (Sum.inl y) = 0) := by
          simpa only [s] using x.property
        exact (Finset.mem_filter.mp hx).2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  have hs : s.card = Fintype.card (ZeroQuad q) := by
    rw [← Fintype.card_coe s]
    exact Fintype.card_congr ep.symm
  let e : TriZeroIndex q ≃ ZeroQuad q := Equiv.ofBijective
    (triZeroEquivFun q) ⟨triZeroEquivFun_injective q, triZeroEquivFun_surjective q⟩
  change s.card = Fintype.card (TriZeroIndex q)
  rw [hs]
  exact (Fintype.card_congr e).symm

private lemma boundaryMain_zeroCoefficient_exact (q : ℕ) (hq : 0 < q) :
    (∑ x : Fin q × Fin q × Fin q × Fin q with
        jacksonFrequency (Sum.inl x) = 0,
      boundaryCoefficient q (Sum.inl x)) =
      (2 * (q : ℝ) ^ 2 + 1) * (1 - Real.cos (Real.pi / q)) /
        (3 * (q : ℝ)) := by
  classical
  rw [Finset.sum_filter]
  simp only [boundaryCoefficient]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, zeroQuad_card_exact q]
  have hcard := triZeroIndex_card_formula q
  have hcardR : (Fintype.card (TriZeroIndex q) : ℝ) =
      (2 * (q : ℝ) ^ 3 + q) / 3 := by
    have hcast := congrArg (fun x : ℕ => (x : ℝ)) hcard
    push_cast at hcast
    linarith
  rw [hcardR]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- The lower bound used by the existing Jackson consumer is its exact signed
zero Fourier coefficient. -/
theorem jacksonZeroCoefficient_eq (q : ℕ) (hq : 0 < q) :
    aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 =
      ((q : ℝ) ^ 2 + 2) / (3 * (q : ℝ) ^ 3) := by
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ x : Fin q × Fin q × Fin q × Fin q,
      if jacksonFrequency (Sum.inl x) = 0 then
        jacksonCoefficient q q (Sum.inl x) else 0) =
      (2 * (q : ℝ) ^ 2 + 1) * 2 / (3 * (q : ℝ) ^ 3) by
    rw [← Finset.sum_filter]
    simp only [jacksonCoefficient, Finset.sum_const, nsmul_eq_mul,
      zeroQuad_card_exact q]
    have hcard := triZeroIndex_card_formula q
    have hcardR : (Fintype.card (TriZeroIndex q) : ℝ) =
        (2 * (q : ℝ) ^ 3 + q) / 3 := by
      have hcast := congrArg (fun x : ℕ => (x : ℝ)) hcard
      push_cast at hcast
      linarith
    rw [hcardR]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp]
  rw [show (∑ x : (Bool × Fin q) × (Bool × Fin q),
      if jacksonFrequency (Sum.inr x) = 0 then
        jacksonCoefficient q q (Sum.inr x) else 0) = -(1 / (q : ℝ)) by
    simpa only [Finset.sum_filter] using jacksonEdge_zeroCoefficient q hq]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

/-- Exact signed zero Fourier coefficient of the boundary-matched kernel. -/
theorem boundaryZeroCoefficient_eq (q : ℕ) (hq : 0 < q) :
    boundaryZeroCoefficient q =
      (2 * ((q : ℝ) ^ 2 - 1) -
          (2 * (q : ℝ) ^ 2 + 1) * Real.cos (Real.pi / q)) /
        (3 * (q : ℝ)) := by
  unfold boundaryZeroCoefficient aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ x : Fin q × Fin q × Fin q × Fin q,
      if jacksonFrequency (Sum.inl x) = 0 then
        boundaryCoefficient q (Sum.inl x) else 0) =
      (2 * (q : ℝ) ^ 2 + 1) * (1 - Real.cos (Real.pi / q)) /
        (3 * (q : ℝ)) by
    simpa only [Finset.sum_filter] using boundaryMain_zeroCoefficient_exact q hq]
  rw [show (∑ x : (Bool × Fin q) × (Bool × Fin q),
      if jacksonFrequency (Sum.inr x) = 0 then
        boundaryCoefficient q (Sum.inr x) else 0) = -(1 / (q : ℝ)) by
    simpa only [Finset.sum_filter, boundaryCoefficient, jacksonCoefficient] using
      jacksonEdge_zeroCoefficient q hq]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

/-- Exact gain in the signed zero mode relative to the order-`q` Jackson
kernel. -/
theorem boundaryZeroCoefficient_sub_jackson (q : ℕ) (hq : 0 < q) :
    boundaryZeroCoefficient q -
        aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 =
      (2 * (q : ℝ) ^ 2 + 1) / (3 * (q : ℝ)) *
        (1 - Real.cos (Real.pi / q) - 2 / (q : ℝ) ^ 2) := by
  rw [boundaryZeroCoefficient_eq q hq, jacksonZeroCoefficient_eq q hq]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp
  ring

private lemma two_div_sq_lt_one_sub_cos_pi_div (q : ℕ) (hq : 1 < q) :
    2 / (q : ℝ) ^ 2 < 1 - Real.cos (Real.pi / q) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  let y : ℝ := Real.pi / (2 * q)
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hyhalf : y < Real.pi / 2 := by
    dsimp [y]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  have hs0 : 1 / (q : ℝ) < Real.sin y := by
    calc
      1 / (q : ℝ) = 2 / Real.pi * y := by
        dsimp [y]
        field_simp
      _ < Real.sin y := Real.mul_lt_sin hy0 hyhalf
  have hleft : 0 ≤ 1 / (q : ℝ) := by positivity
  have hsin : 0 ≤ Real.sin y := (le_trans hleft hs0.le)
  have hsq : (1 / (q : ℝ)) ^ 2 < Real.sin y ^ 2 :=
    (sq_lt_sq₀ hleft hsin).2 hs0
  have hcos : Real.cos (Real.pi / q) = 1 - 2 * Real.sin y ^ 2 := by
    rw [show Real.pi / (q : ℝ) = 2 * y by
      dsimp [y]
      field_simp]
    exact Real.cos_two_mul_eq_one_sub y
  rw [hcos]
  calc
    2 / (q : ℝ) ^ 2 = 2 * (1 / (q : ℝ)) ^ 2 := by field_simp
    _ < 2 * Real.sin y ^ 2 := by nlinarith
    _ = 1 - (1 - 2 * Real.sin y ^ 2) := by ring

/-- For every nontrivial order, matching the actual interval boundary gives a
strictly larger signed zero mode than the old Jackson kernel. -/
theorem jacksonZeroCoefficient_lt_boundaryZeroCoefficient
    (q : ℕ) (hq : 1 < q) :
    aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 <
      boundaryZeroCoefficient q := by
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  rw [← sub_pos]
  rw [boundaryZeroCoefficient_sub_jackson q hq0]
  exact mul_pos (by positivity)
    (sub_pos.mpr (two_div_sq_lt_one_sub_cos_pi_div q hq))

end Theory.PiDigits.BoundaryKernelNormalizedComparison

#print axioms Theory.PiDigits.BoundaryKernelNormalizedComparison.boundaryZeroCoefficient_eq
#print axioms Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_eq
#print axioms Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_lt_boundaryZeroCoefficient
