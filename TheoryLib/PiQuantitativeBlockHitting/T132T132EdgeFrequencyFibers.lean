import TheoryLib.PiQuantitativeBlockHitting.T131T131MainFrequencyFibers

/-!
# T132: signed edge-frequency fibers

This file computes the signed edge-pair contribution at every positive
frequency in the finite Jackson support.  Combined with T131, it identifies
the actual aggregated Jackson and boundary-matched coefficients with the
closed affine formulas from T130 and transfers the normalized strict
comparison to the actual finite presentations.

No cancellation estimate for the decimal orbit of pi is asserted.
-/

noncomputable section

namespace Theory.PiDigits.EdgeFrequencyFibers

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra
open Theory.PiDigits.MainFrequencyFibers

/-- The signed contribution of the edge-pair branch at positive frequency
`h`. -/
def signedEdgeCoefficient (q h : ℕ) : ℝ :=
  ∑ x : (Bool × Fin q) × (Bool × Fin q),
    if jacksonFrequency (Sum.inr x) = (h : ℤ) then
      jacksonCoefficient q q (Sum.inr x) else 0

private abbrev DiffFiber (q h : ℕ) :=
  {x : Fin q × Fin q // (x.1.val : ℤ) - x.2.val = h}

private abbrev ForwardFiber (q h : ℕ) :=
  {x : Fin q × Fin q // (q : ℤ) + x.1.val - x.2.val = h}

private lemma filter_card_eq_subtype_card
    {X : Type*} [Fintype X] [DecidableEq X] (p : X → Prop) [DecidablePred p] :
    ((Finset.univ : Finset X).filter p).card = Fintype.card {x // p x} := by
  let e : {x // p x} ≃ {x // x ∈ (Finset.univ : Finset X).filter p} :=
    { toFun := fun x => ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun x => ⟨x.val, (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr e.symm

private def diffFiberMap (q h : ℕ) (hhq : h ≤ q) :
    Fin (q - h) → DiffFiber q h := fun k =>
  ⟨(⟨k.val + h, by omega⟩, ⟨k.val, by omega⟩), by
    simp only
    push_cast
    omega⟩

private lemma diffFiberMap_bijective (q h : ℕ) (hhq : h ≤ q) :
    Function.Bijective (diffFiberMap q h hhq) := by
  constructor
  · intro k l heq
    apply Fin.ext
    simpa [diffFiberMap] using congrArg (fun x => x.val.2.val) heq
  · rintro ⟨⟨a, b⟩, hab⟩
    have hb : b.val < q - h := by
      have ha := a.isLt
      push_cast at hab
      omega
    refine ⟨⟨b.val, hb⟩, Subtype.ext ?_⟩
    ext <;> simp [diffFiberMap] <;> push_cast at hab <;> omega

private lemma diffFiber_card (q h : ℕ) (hhq : h ≤ q) :
    Fintype.card (DiffFiber q h) = q - h := by
  rw [← Fintype.card_fin (q - h)]
  exact (Fintype.card_congr
    (Equiv.ofBijective (diffFiberMap q h hhq)
      (diffFiberMap_bijective q h hhq))).symm

private def forwardLowMap (q h : ℕ) (hhq : h ≤ q) :
    Fin h → ForwardFiber q h := fun k =>
  ⟨(⟨k.val, by omega⟩, ⟨q + k.val - h, by omega⟩), by
    simp only
    rw [Nat.cast_sub (by omega : h ≤ q + k.val)]
    omega⟩

private lemma forwardLowMap_bijective
    (q h : ℕ) (hhq : h ≤ q) :
    Function.Bijective (forwardLowMap q h hhq) := by
  constructor
  · intro k l heq
    apply Fin.ext
    simpa [forwardLowMap] using congrArg (fun x => x.val.1.val) heq
  · rintro ⟨⟨a, b⟩, hab⟩
    have halt : a.val < h := by
      have hb := b.isLt
      push_cast at hab
      omega
    refine ⟨⟨a.val, halt⟩, Subtype.ext ?_⟩
    ext <;> simp [forwardLowMap] <;> push_cast at hab <;> omega

private lemma forwardFiber_card_low
    (q h : ℕ) (hhq : h ≤ q) :
    Fintype.card (ForwardFiber q h) = h := by
  simpa using (Fintype.card_congr
    (Equiv.ofBijective (forwardLowMap q h hhq)
      (forwardLowMap_bijective q h hhq))).symm

private def forwardHighMap (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q) :
    Fin (2 * q - h) → ForwardFiber q h := fun k =>
  ⟨(⟨k.val + (h - q), by omega⟩, ⟨k.val, by omega⟩), by
    simp only
    push_cast
    rw [Nat.cast_sub (by omega : q ≤ h)]
    omega⟩

private lemma forwardHighMap_bijective
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q) :
    Function.Bijective (forwardHighMap q h hhq hhsupp) := by
  constructor
  · intro k l heq
    apply Fin.ext
    simpa [forwardHighMap] using congrArg (fun x => x.val.2.val) heq
  · rintro ⟨⟨a, b⟩, hab⟩
    have hb : b.val < 2 * q - h := by
      have ha := a.isLt
      push_cast at hab
      omega
    refine ⟨⟨b.val, hb⟩, Subtype.ext ?_⟩
    ext <;> simp [forwardHighMap] <;> push_cast at hab <;> omega

private lemma forwardFiber_card_high
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q) :
    Fintype.card (ForwardFiber q h) = 2 * q - h := by
  rw [← Fintype.card_fin (2 * q - h)]
  exact (Fintype.card_congr
    (Equiv.ofBijective (forwardHighMap q h hhq hhsupp)
      (forwardHighMap_bijective q h hhq hhsupp))).symm

private lemma sum_diff_eq (q h : ℕ) (hhq : h ≤ q) (c : ℝ) :
    (∑ a : Fin q, ∑ b : Fin q,
      if (a.val : ℤ) - b.val = h then c else 0) = (q - h : ℕ) * c := by
  calc
    _ = ∑ x : Fin q × Fin q,
        if (x.1.val : ℤ) - x.2.val = h then c else 0 := by
          rw [Fintype.sum_prod_type]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [filter_card_eq_subtype_card, diffFiber_card q h hhq]

private lemma sum_diff_eq_zero (q h : ℕ) (hhq : q < h) (c : ℝ) :
    (∑ a : Fin q, ∑ b : Fin q,
      if (a.val : ℤ) - b.val = h then c else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  split_ifs with hab
  · have ha' := a.isLt
    have hb' := b.isLt
    push_cast at hab
    omega
  · rfl

private lemma sum_forward_eq_low
    (q h : ℕ) (hhq : h ≤ q) (c : ℝ) :
    (∑ a : Fin q, ∑ b : Fin q,
      if (q : ℤ) + a.val - b.val = h then c else 0) = h * c := by
  calc
    _ = ∑ x : Fin q × Fin q,
        if (q : ℤ) + x.1.val - x.2.val = h then c else 0 := by
          rw [Fintype.sum_prod_type]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [filter_card_eq_subtype_card, forwardFiber_card_low q h hhq]

private lemma sum_forward_eq_high
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q) (c : ℝ) :
    (∑ a : Fin q, ∑ b : Fin q,
      if (q : ℤ) + a.val - b.val = h then c else 0) = (2 * q - h : ℕ) * c := by
  calc
    _ = ∑ x : Fin q × Fin q,
        if (q : ℤ) + x.1.val - x.2.val = h then c else 0 := by
          rw [Fintype.sum_prod_type]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [filter_card_eq_subtype_card, forwardFiber_card_high q h hhq hhsupp]

private lemma sum_reverse_eq_zero (q h : ℕ) (hh0 : 0 < h) (c : ℝ) :
    (∑ a : Fin q, ∑ b : Fin q,
      if (a.val : ℤ) - q - b.val = h then c else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  split_ifs with hab
  · have ha' := a.isLt
    have hb' := b.isLt
    push_cast at hab
    omega
  · rfl

theorem signedEdgeCoefficient_eq_piecewise
    (q h : ℕ) (hq : 0 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    signedEdgeCoefficient q h = if h ≤ q then
      (3 * (h : ℝ) - 2 * q) / (2 * (q : ℝ) ^ 2)
    else (2 * q - h : ℝ) / (2 * (q : ℝ) ^ 2) := by
  classical
  unfold signedEdgeCoefficient
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [jacksonFrequency, edgeFrequency, jacksonCoefficient, edgeSign,
    Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul, neg_neg]
  simp_rw [Finset.sum_add_distrib]
  have hreverse :
      (∑ a : Fin q, ∑ b : Fin q,
        if -(b.val : ℤ) - ((q : ℤ) - a.val) = h then
          1 / (2 * (q : ℝ) ^ 2) else 0) = 0 := by
    simpa only [show ∀ a b : Fin q,
        -(b.val : ℤ) - ((q : ℤ) - a.val) = a.val - q - b.val by
          intro a b; ring] using
      sum_reverse_eq_zero q h hh0 (1 / (2 * (q : ℝ) ^ 2))
  by_cases hhq : h ≤ q
  · have htt :
        (∑ a : Fin q, ∑ b : Fin q,
          if (q : ℤ) - b.val - ((q : ℤ) - a.val) = h then
            -1 / (2 * (q : ℝ) ^ 2) else 0) =
          (q - h : ℕ) * (-1 / (2 * (q : ℝ) ^ 2)) := by
      simpa only [show ∀ a b : Fin q,
          (q : ℤ) - b.val - ((q : ℤ) - a.val) = a.val - b.val by
            intro a b; ring] using
        sum_diff_eq q h hhq (-1 / (2 * (q : ℝ) ^ 2))
    have hff :
        (∑ a : Fin q, ∑ b : Fin q,
          if -(b.val : ℤ) - -(a.val : ℤ) = h then
            -1 / (2 * (q : ℝ) ^ 2) else 0) =
          (q - h : ℕ) * (-1 / (2 * (q : ℝ) ^ 2)) := by
      simpa only [show ∀ a b : Fin q,
          -(b.val : ℤ) - -(a.val : ℤ) = a.val - b.val by
            intro a b; ring] using
        sum_diff_eq q h hhq (-1 / (2 * (q : ℝ) ^ 2))
    have hforward :
        (∑ a : Fin q, ∑ b : Fin q,
          if (q : ℤ) - b.val - -(a.val : ℤ) = h then
            1 / (2 * (q : ℝ) ^ 2) else 0) =
          h * (1 / (2 * (q : ℝ) ^ 2)) := by
      simpa only [show ∀ a b : Fin q,
          (q : ℤ) - b.val - -(a.val : ℤ) = q + a.val - b.val by
            intro a b; ring] using
        sum_forward_eq_low q h hhq (1 / (2 * (q : ℝ) ^ 2))
    rw [htt, hreverse, hforward, hff]
    rw [if_pos hhq]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Nat.cast_sub hhq]
    field_simp
    ring
  · have hhq' : q < h := by omega
    have htt :
        (∑ a : Fin q, ∑ b : Fin q,
          if (q : ℤ) - b.val - ((q : ℤ) - a.val) = h then
            -1 / (2 * (q : ℝ) ^ 2) else 0) = 0 := by
      simpa only [show ∀ a b : Fin q,
          (q : ℤ) - b.val - ((q : ℤ) - a.val) = a.val - b.val by
            intro a b; ring] using
        sum_diff_eq_zero q h hhq' (-1 / (2 * (q : ℝ) ^ 2))
    have hff :
        (∑ a : Fin q, ∑ b : Fin q,
          if -(b.val : ℤ) - -(a.val : ℤ) = h then
            -1 / (2 * (q : ℝ) ^ 2) else 0) = 0 := by
      simpa only [show ∀ a b : Fin q,
          -(b.val : ℤ) - -(a.val : ℤ) = a.val - b.val by
            intro a b; ring] using
        sum_diff_eq_zero q h hhq' (-1 / (2 * (q : ℝ) ^ 2))
    have hforward :
        (∑ a : Fin q, ∑ b : Fin q,
          if (q : ℤ) - b.val - -(a.val : ℤ) = h then
            1 / (2 * (q : ℝ) ^ 2) else 0) =
          (2 * q - h : ℕ) * (1 / (2 * (q : ℝ) ^ 2)) := by
      simpa only [show ∀ a b : Fin q,
          (q : ℤ) - b.val - -(a.val : ℤ) = q + a.val - b.val by
            intro a b; ring] using
        sum_forward_eq_high q h hhq' (by omega)
          (1 / (2 * (q : ℝ) ^ 2))
    rw [htt, hreverse, hforward, hff]
    rw [if_neg hhq]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Nat.cast_sub (by omega : h ≤ 2 * q)]
    push_cast
    field_simp
    ring

/-- The signed edge fiber is exactly the discrete neighboring correction
`M_q(h) - B_q(h)` in the affine cosine--Fejer coefficient. -/
theorem signedEdgeCoefficient_eq_neighboring_sub
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    signedEdgeCoefficient q h =
      neighboringCoefficient q h - fejerSquareCoefficient q h := by
  rw [signedEdgeCoefficient_eq_piecewise q h (by omega) hh0 hhsupp]
  by_cases hhq : h ≤ q
  · rw [if_pos hhq]
    by_cases heq : h = q
    · subst h
      simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
        if_pos (le_refl q), if_pos (by omega : q - 1 ≤ q),
        if_neg (by omega : ¬ q + 1 ≤ q)]
      have hqR : (q : ℝ) ≠ 0 := by positivity
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      field_simp
      ring
    · have hhp1 : h + 1 ≤ q := by omega
      simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
        if_pos hhq, if_pos (by omega : h - 1 ≤ q), if_pos hhp1]
      have hqR : (q : ℝ) ≠ 0 := by positivity
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ h)]
      field_simp
      ring
  · rw [if_neg hhq]
    have hhq' : q < h := by omega
    by_cases hnear : h = q + 1
    · subst h
      simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
        if_neg (by omega : ¬ q + 1 ≤ q),
        if_pos (by omega : q + 1 - 1 ≤ q),
        if_neg (by omega : ¬ q + 1 + 1 ≤ q)]
      have hqR : (q : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
        if_neg hhq, if_neg (by omega : ¬ h - 1 ≤ q),
        if_neg (by omega : ¬ h + 1 ≤ q)]
      have hqR : (q : ℝ) ≠ 0 := by positivity
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ h)]
      field_simp
      ring
/-- Every actual positive-support Jackson coefficient agrees with the closed
affine coefficient at the Jackson parameter. -/
theorem aggregatedJacksonCoefficient_eq_affine
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) (h : ℤ) =
      affineCoefficient q h (jacksonBeta q) := by
  classical
  have hmain :
      (∑ x : Fin q × Fin q × Fin q × Fin q,
        if jacksonFrequency (Sum.inl x) = (h : ℤ) then
          jacksonCoefficient q q (Sum.inl x) else 0) =
        2 / (q : ℝ) ^ 2 * fejerSquareCoefficient q h := by
    rw [← Finset.sum_filter]
    simp only [jacksonCoefficient, Finset.sum_const, nsmul_eq_mul]
    change (mainFrequencyMultiplicity q (h : ℤ) : ℝ) *
        ((2 / (q : ℝ) ^ 2) / (q : ℝ) ^ 2) = _
    rw [mainFrequencyMultiplicity_eq_cubic q h hh0 hhsupp]
    unfold fejerSquareCoefficient
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  unfold aggregatedCoefficient
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  change _ + signedEdgeCoefficient q h = _
  rw [hmain, signedEdgeCoefficient_eq_neighboring_sub q h hq hh0 hhsupp]
  unfold affineCoefficient jacksonBeta
  ring

/-- The same actual-coefficient identification for the boundary-matched
parameter. -/
theorem aggregatedBoundaryCoefficient_eq_affine
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) (h : ℤ) =
      affineCoefficient q h (Real.cos (Real.pi / q)) := by
  rw [aggregatedBoundaryCoefficient_eq_jackson_add,
    aggregatedJacksonCoefficient_eq_affine q h hq hh0 hhsupp,
    aggregatedFejerSquareCoefficient_eq q h (by omega) hh0 hhsupp]
  unfold affineCoefficient jacksonBeta
  ring

/-- Full normalized strict domination for the actual frequency-aggregated
finite presentations, at every positive frequency in their exact support. -/
theorem normalized_aggregatedBoundary_lt_jackson
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) (h : ℤ) /
        boundaryZeroCoefficient q <
      aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) (h : ℤ) /
        aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 := by
  rw [aggregatedBoundaryCoefficient_eq_affine q h hq hh0 hhsupp,
    aggregatedJacksonCoefficient_eq_affine q h hq hh0 hhsupp,
    ← affineZeroCoefficient_boundary q hq,
    jacksonZeroCoefficient_eq q (by omega),
    ← affineZeroCoefficient_jackson q hq]
  exact normalized_boundary_lt_jackson q h hq hh0 hhsupp

end Theory.PiDigits.EdgeFrequencyFibers

#print axioms Theory.PiDigits.EdgeFrequencyFibers.signedEdgeCoefficient_eq_piecewise
#print axioms Theory.PiDigits.EdgeFrequencyFibers.aggregatedJacksonCoefficient_eq_affine
#print axioms Theory.PiDigits.EdgeFrequencyFibers.aggregatedBoundaryCoefficient_eq_affine
#print axioms Theory.PiDigits.EdgeFrequencyFibers.normalized_aggregatedBoundary_lt_jackson
