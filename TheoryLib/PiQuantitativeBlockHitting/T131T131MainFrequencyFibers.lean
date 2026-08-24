import TheoryLib.PiQuantitativeBlockHitting.T130T130BoundaryNonzeroCoefficientAlgebra

/-!
# T131: exact positive main-frequency fibers

This file identifies the positive-frequency fibers of the main Jackson
quadruples with explicit finite parameter spaces and computes their exact
cardinality.  It closes the finite combinatorial gap left in T130; it does not
assert any cancellation for the decimal orbit of pi.
-/

noncomputable section

namespace Theory.PiDigits.MainFrequencyFibers

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel
open Theory.PiDigits.BoundaryKernelNormalizedComparison
open Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra

private abbrev MainFiber (q h : ℕ) :=
  {x : Fin q × Fin q × Fin q × Fin q //
    jacksonFrequency (Sum.inl x) = (h : ℤ)}

private abbrev PositivePart (q h : ℕ) :=
  Σ a : Fin (h + 1), Fin (q - a.val) × Fin (q - (h - a.val))

private abbrev MixedPart (q h : ℕ) :=
  Σ d : Fin (q - h - 1),
    Fin (q - (d.val + 1)) × Fin (q - h - (d.val + 1))

private abbrev FirstFiberModel (q h : ℕ) :=
  PositivePart q h ⊕ (MixedPart q h ⊕ MixedPart q h)

private abbrev LateFiberModel (q h : ℕ) :=
  Σ k : Fin (2 * q - h - 1),
    Fin (2 * q - h - 1 - k.val) × Fin (k.val + 1)

private def firstFiberMap (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    FirstFiberModel q h → MainFiber q h
  | Sum.inl ⟨a, r, u⟩ => by
      let b := h - a.val
      exact ⟨(⟨r.val, by omega⟩, ⟨r.val + a.val, by omega⟩,
          ⟨u.val, by omega⟩, ⟨u.val + b, by omega⟩), by
        simp only [jacksonFrequency]
        push_cast
        dsimp [b]
        omega⟩
  | Sum.inr (Sum.inl ⟨d, s, u⟩) => by
      let k := d.val + 1
      exact ⟨(⟨s.val + k, by omega⟩, ⟨s.val, by omega⟩,
          ⟨u.val, by omega⟩, ⟨u.val + h + k, by omega⟩), by
        simp only [jacksonFrequency]
        push_cast
        dsimp [k]
        omega⟩
  | Sum.inr (Sum.inr ⟨d, v, r⟩) => by
      let k := d.val + 1
      exact ⟨(⟨r.val, by omega⟩, ⟨r.val + h + k, by omega⟩,
          ⟨v.val + k, by omega⟩, ⟨v.val, by omega⟩), by
        simp only [jacksonFrequency]
        push_cast
        dsimp [k]
        omega⟩

private lemma firstFiberMap_injective (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    Function.Injective (firstFiberMap q h hh0 hhq) := by
  intro x y heq
  rcases x with x | x
  · rcases y with y | y
    · rcases x with ⟨a, r, u⟩
      rcases y with ⟨b, s, v⟩
      simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
        Fin.mk.injEq] at heq
      rcases heq with ⟨hr, hrs, hu, huv⟩
      have hab : a = b := Fin.ext (by omega)
      subst b
      congr
      · exact Fin.ext hr
      · exact Fin.ext hu
    · rcases x with ⟨a, r, u⟩
      rcases y with y | y
      · rcases y with ⟨d, s, v⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
      · rcases y with ⟨d, v, s⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
  · rcases y with y | y
    · rcases x with x | x
      · rcases x with ⟨d, s, v⟩
        rcases y with ⟨a, r, u⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
      · rcases x with ⟨d, v, s⟩
        rcases y with ⟨a, r, u⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
    · rcases x with x | x <;> rcases y with y | y
      · rcases x with ⟨d, s, u⟩
        rcases y with ⟨e, t, v⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        rcases heq with ⟨hrs, hs, hu, huv⟩
        have hde : d = e := Fin.ext (by omega)
        subst e
        congr
        · exact Fin.ext hs
        · exact Fin.ext hu
      · rcases x with ⟨d, s, u⟩
        rcases y with ⟨e, v, r⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
      · rcases x with ⟨d, v, r⟩
        rcases y with ⟨e, s, u⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        omega
      · rcases x with ⟨d, v, r⟩
        rcases y with ⟨e, w, s⟩
        simp only [firstFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
          Fin.mk.injEq] at heq
        rcases heq with ⟨hr, hrs, huv, hv⟩
        have hde : d = e := Fin.ext (by omega)
        subst e
        congr
        · exact Fin.ext hv
        · exact Fin.ext hr

private lemma firstFiberMap_surjective (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    Function.Surjective (firstFiberMap q h hh0 hhq) := by
  rintro ⟨⟨r, s, u, v⟩, hfreq⟩
  simp only [jacksonFrequency] at hfreq
  by_cases hrs : r.val ≤ s.val
  · by_cases huv : u.val ≤ v.val
    · let a : Fin (h + 1) := ⟨s.val - r.val, by
        push_cast at hfreq
        omega⟩
      let rr : Fin (q - a.val) := ⟨r.val, by dsimp [a]; omega⟩
      let uu : Fin (q - (h - a.val)) := ⟨u.val, by
        dsimp [a]
        push_cast at hfreq
        omega⟩
      refine ⟨Sum.inl ⟨a, rr, uu⟩, Subtype.ext ?_⟩
      ext <;> simp [firstFiberMap, a, rr, uu] <;>
        push_cast at hfreq <;> omega
    · have hvu : v.val < u.val := Nat.lt_of_not_ge huv
      let k := u.val - v.val
      have hk0 : 0 < k := by dsimp [k]; omega
      have hkbound : k - 1 < q - h - 1 := by
        dsimp [k]
        push_cast at hfreq
        omega
      let d : Fin (q - h - 1) := ⟨k - 1, hkbound⟩
      let vv : Fin (q - (d.val + 1)) := ⟨v.val, by dsimp [d, k]; omega⟩
      let rr : Fin (q - h - (d.val + 1)) := ⟨r.val, by
        dsimp [d, k]
        push_cast at hfreq
        omega⟩
      refine ⟨Sum.inr (Sum.inr ⟨d, vv, rr⟩), Subtype.ext ?_⟩
      ext <;> simp [firstFiberMap, d, k, vv, rr] <;>
        push_cast at hfreq <;> omega
  · have hsr : s.val < r.val := Nat.lt_of_not_ge hrs
    let k := r.val - s.val
    have hk0 : 0 < k := by dsimp [k]; omega
    have hkbound : k - 1 < q - h - 1 := by
      dsimp [k]
      push_cast at hfreq
      omega
    let d : Fin (q - h - 1) := ⟨k - 1, hkbound⟩
    let ss : Fin (q - (d.val + 1)) := ⟨s.val, by dsimp [d, k]; omega⟩
    let uu : Fin (q - h - (d.val + 1)) := ⟨u.val, by
      dsimp [d, k]
      push_cast at hfreq
      omega⟩
    refine ⟨Sum.inr (Sum.inl ⟨d, ss, uu⟩), Subtype.ext ?_⟩
    ext <;> simp [firstFiberMap, d, k, ss, uu] <;>
      push_cast at hfreq <;> omega

private def firstFiberEquiv (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    FirstFiberModel q h ≃ MainFiber q h :=
  Equiv.ofBijective (firstFiberMap q h hh0 hhq)
    ⟨firstFiberMap_injective q h hh0 hhq, firstFiberMap_surjective q h hh0 hhq⟩

private def lateFiberMap (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    LateFiberModel q h → MainFiber q h
  | ⟨k, r, u⟩ => by
      let a := h - q + 1 + k.val
      let b := q - 1 - k.val
      exact ⟨(⟨r.val, by omega⟩, ⟨r.val + a, by omega⟩,
          ⟨u.val, by omega⟩, ⟨u.val + b, by omega⟩), by
        simp only [jacksonFrequency]
        push_cast
        dsimp [a, b]
        omega⟩

private lemma lateFiberMap_injective
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    Function.Injective (lateFiberMap q h hhq hhsupp) := by
  rintro ⟨k, r, u⟩ ⟨l, s, v⟩ heq
  simp only [lateFiberMap, Subtype.mk.injEq, Prod.mk.injEq,
    Fin.mk.injEq] at heq
  rcases heq with ⟨hr, hrs, hu, huv⟩
  have hkl : k = l := Fin.ext (by omega)
  subst l
  congr
  · exact Fin.ext hr
  · exact Fin.ext hu

private lemma lateFiberMap_surjective
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    Function.Surjective (lateFiberMap q h hhq hhsupp) := by
  rintro ⟨⟨r, s, u, v⟩, hfreq⟩
  simp only [jacksonFrequency] at hfreq
  have hrs : r.val ≤ s.val := by
    by_contra hn
    have hsr : s.val < r.val := Nat.lt_of_not_ge hn
    have hu := u.isLt
    have hv := v.isLt
    push_cast at hfreq
    omega
  have huv : u.val ≤ v.val := by
    by_contra hn
    have hvu : v.val < u.val := Nat.lt_of_not_ge hn
    have hr := r.isLt
    have hs := s.isLt
    push_cast at hfreq
    omega
  let a := s.val - r.val
  let kNat := a - (h - q + 1)
  have hklt : kNat < 2 * q - h - 1 := by
    dsimp [kNat, a]
    push_cast at hfreq
    omega
  let k : Fin (2 * q - h - 1) := ⟨kNat, hklt⟩
  let rr : Fin (2 * q - h - 1 - k.val) := ⟨r.val, by
    dsimp [k, kNat, a]
    push_cast at hfreq
    omega⟩
  let uu : Fin (k.val + 1) := ⟨u.val, by
    dsimp [k, kNat, a]
    push_cast at hfreq
    omega⟩
  refine ⟨⟨k, rr, uu⟩, Subtype.ext ?_⟩
  ext <;> simp [lateFiberMap, k, kNat, a, rr, uu] <;>
    push_cast at hfreq <;> omega

private def lateFiberEquiv
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    LateFiberModel q h ≃ MainFiber q h :=
  Equiv.ofBijective (lateFiberMap q h hhq hhsupp)
    ⟨lateFiberMap_injective q h hhq hhsupp,
      lateFiberMap_surjective q h hhq hhsupp⟩

private lemma sum_range_succ_real (n : ℕ) :
    (∑ k ∈ Finset.range n, (k + 1 : ℝ)) =
      (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      push_cast
      ring

private lemma sum_desc_asc (n : ℕ) :
    (∑ k ∈ Finset.range n, ((n - k : ℕ) : ℝ) * (k + 1)) =
      (n : ℝ) * (n + 1) * (n + 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show (∑ k ∈ Finset.range n,
          (((n + 1 - k : ℕ) : ℝ) * (k + 1))) =
          (∑ k ∈ Finset.range n,
            (((n - k : ℕ) : ℝ) * (k + 1))) +
            ∑ k ∈ Finset.range n, (k + 1 : ℝ) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        push_cast
        rw [Nat.cast_sub (by omega : k ≤ n), Nat.cast_sub (by omega : k ≤ n + 1)]
        norm_num
        push_cast
        ring]
      rw [ih]
      rw [sum_range_succ_real]
      norm_num
      push_cast
      ring

private lemma sum_affine_opposed (A B : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (A - k) * (B + k)) =
      (n : ℝ) * A * B + (A - B) * n * (n - 1) / 2 -
        (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      push_cast
      ring

private lemma sum_affine_descending (A B : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (A - k) * (B - k)) =
      (n : ℝ) * A * B - (A + B) * n * (n - 1) / 2 +
        (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      push_cast
      ring

private lemma mainFrequencyMultiplicity_eq_fiber_card (q h : ℕ) :
    mainFrequencyMultiplicity q (h : ℤ) = Fintype.card (MainFiber q h) := by
  classical
  let s := (Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter
    fun x => jacksonFrequency (Sum.inl x) = (h : ℤ)
  let e : MainFiber q h ≃ {x // x ∈ s} :=
    { toFun := fun x => ⟨x.val, by
        dsimp [s]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun x => ⟨x.val, by
        have hx : x.val ∈
            (Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter
              (fun y => jacksonFrequency (Sum.inl y) = (h : ℤ)) := by
          simpa only [s] using x.property
        exact (Finset.mem_filter.mp hx).2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  unfold mainFrequencyMultiplicity
  change s.card = Fintype.card (MainFiber q h)
  rw [← Fintype.card_coe s]
  exact Fintype.card_congr e.symm

private lemma positivePart_card (q h : ℕ) (hhq : h ≤ q) :
    (Fintype.card (PositivePart q h) : ℝ) =
      ((h + 1 : ℕ) : ℝ) * q * (q - h) +
        ((q : ℝ) - (q - h)) * ((h + 1 : ℕ) : ℝ) *
          (((h + 1 : ℕ) : ℝ) - 1) / 2 -
        ((h + 1 : ℕ) : ℝ) * (((h + 1 : ℕ) : ℝ) - 1) *
          (2 * ((h + 1 : ℕ) : ℝ) - 1) / 6 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.cast_sum]
  let n := h + 1
  have hfin : (∑ x : Fin n,
      (((q - x.val) * (q - (h - x.val)) : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range n,
        (((q - k) * (q - (h - k)) : ℕ) : ℝ) :=
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (((q - k) * (q - (h - k)) : ℕ) : ℝ)) n
  change (∑ x : Fin n,
    (((q - x.val) * (q - (h - x.val)) : ℕ) : ℝ)) = _
  rw [hfin]
  dsimp [n]
  rw [show (∑ k ∈ Finset.range (h + 1),
      (((q - k) * (q - (h - k)) : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range (h + 1),
        ((q : ℝ) - k) * (((q : ℝ) - h) + k) by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hkh : k ≤ h := by omega
    push_cast
    rw [Nat.cast_sub (hkh.trans hhq),
      Nat.cast_sub ((Nat.sub_le h k).trans hhq), Nat.cast_sub hkh]
    ring]
  exact sum_affine_opposed (q : ℝ) ((q : ℝ) - h) (h + 1)

private lemma mixedPart_card (q h : ℕ) (hhq : h ≤ q) :
    (Fintype.card (MixedPart q h) : ℝ) =
      ((q - h - 1 : ℕ) : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) - h - 1) -
        (((q : ℝ) - 1) + ((q : ℝ) - h - 1)) *
          ((q - h - 1 : ℕ) : ℝ) *
          (((q - h - 1 : ℕ) : ℝ) - 1) / 2 +
        ((q - h - 1 : ℕ) : ℝ) *
          (((q - h - 1 : ℕ) : ℝ) - 1) *
          (2 * ((q - h - 1 : ℕ) : ℝ) - 1) / 6 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.cast_sum]
  let n := q - h - 1
  have hfin : (∑ x : Fin n,
      (((q - (x.val + 1)) * (q - h - (x.val + 1)) : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range n,
        (((q - (k + 1)) * (q - h - (k + 1)) : ℕ) : ℝ) :=
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        (((q - (k + 1)) * (q - h - (k + 1)) : ℕ) : ℝ)) n
  change (∑ x : Fin n,
    (((q - (x.val + 1)) * (q - h - (x.val + 1)) : ℕ) : ℝ)) = _
  rw [hfin]
  dsimp [n]
  rw [show (∑ k ∈ Finset.range (q - h - 1),
      (((q - (k + 1)) * (q - h - (k + 1)) : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range (q - h - 1),
        (((q : ℝ) - 1) - k) * (((q : ℝ) - h - 1) - k) by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    push_cast
    rw [Nat.cast_sub (by omega : k + 1 ≤ q),
      Nat.cast_sub (by omega : k + 1 ≤ q - h), Nat.cast_sub hhq]
    simp only [Nat.cast_add, Nat.cast_one]
    ring]
  exact sum_affine_descending
    ((q : ℝ) - 1) ((q : ℝ) - h - 1) (q - h - 1)

private lemma firstFiberModel_card (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    (Fintype.card (FirstFiberModel q h) : ℝ) = cubicMultiplicity q h := by
  simp only [Fintype.card_sum, Nat.cast_add]
  rw [positivePart_card q h hhq, mixedPart_card q h hhq]
  simp only [cubicMultiplicity, if_pos hhq]
  by_cases hlt : h < q
  · have hcast : (((q - h - 1 : ℕ) : ℝ)) =
        (q : ℝ) - h - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q - h), Nat.cast_sub hhq]
      norm_num
    rw [hcast]
    push_cast
    ring
  · have heq : h = q := by omega
    subst h
    norm_num
    ring

/-- Exact main-quadruple multiplicity on the first positive support. -/
theorem mainFrequencyMultiplicity_eq_cubic_first
    (q h : ℕ) (hh0 : 0 < h) (hhq : h ≤ q) :
    (mainFrequencyMultiplicity q (h : ℤ) : ℝ) = cubicMultiplicity q h := by
  rw [mainFrequencyMultiplicity_eq_fiber_card]
  rw [show Fintype.card (MainFiber q h) = Fintype.card (FirstFiberModel q h) by
    exact (Fintype.card_congr (firstFiberEquiv q h hh0 hhq)).symm]
  exact firstFiberModel_card q h hh0 hhq

private lemma lateFiberModel_card (q h : ℕ)
    (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    (Fintype.card (LateFiberModel q h) : ℝ) =
      ((2 * q - h - 1 : ℕ) : ℝ) * (2 * q - h : ℕ) *
        (2 * q - h + 1 : ℕ) / 6 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.cast_sum]
  let n := 2 * q - h - 1
  have hfin : (∑ x : Fin n, (((n - x.val) * (x.val + 1) : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range n, (((n - k) * (k + 1) : ℕ) : ℝ) :=
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (((n - k) * (k + 1) : ℕ) : ℝ)) n
  change (∑ x : Fin n, (((n - x.val) * (x.val + 1) : ℕ) : ℝ)) = _
  rw [hfin]
  dsimp [n]
  simp_rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [sum_desc_asc]
  have hn1 : 2 * q - h - 1 + 1 = 2 * q - h := by omega
  have hn2 : 2 * q - h - 1 + 2 = 2 * q - h + 1 := by omega
  have hn1R := congrArg (fun x : ℕ => (x : ℝ)) hn1
  have hn2R := congrArg (fun x : ℕ => (x : ℝ)) hn2
  push_cast at hn1R hn2R
  rw [hn1R, hn2R]

/-- Exact main-quadruple multiplicity on the late positive support. -/
theorem mainFrequencyMultiplicity_eq_cubic_late
    (q h : ℕ) (hhq : q < h) (hhsupp : h ≤ 2 * q - 2) :
    (mainFrequencyMultiplicity q (h : ℤ) : ℝ) = cubicMultiplicity q h := by
  rw [mainFrequencyMultiplicity_eq_fiber_card]
  rw [show Fintype.card (MainFiber q h) = Fintype.card (LateFiberModel q h) by
    exact (Fintype.card_congr (lateFiberEquiv q h hhq hhsupp)).symm]
  rw [lateFiberModel_card q h hhq hhsupp]
  simp only [cubicMultiplicity, if_neg (by omega : ¬ h ≤ q)]
  have hc0 : (((2 * q - h : ℕ) : ℝ)) = 2 * q - h := by
    rw [Nat.cast_sub (by omega : h ≤ 2 * q)]
    push_cast
    ring
  have hc1 : (((2 * q - h - 1 : ℕ) : ℝ)) = 2 * q - h - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * q - h), hc0]
    norm_num
  have hc2 : (((2 * q - h + 1 : ℕ) : ℝ)) = 2 * q - h + 1 := by
    rw [Nat.cast_add, hc0, Nat.cast_one]
  rw [hc0, hc1, hc2]

private lemma mainFrequencyMultiplicity_top (q : ℕ) (hq : 0 < q) :
    mainFrequencyMultiplicity q (2 * (q : ℤ) - 1) = 0 := by
  classical
  unfold mainFrequencyMultiplicity
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro x hx
  rcases x with ⟨r, s, u, v⟩
  simp only [jacksonFrequency]
  have hr := r.isLt
  have hs := s.isLt
  have hu := u.isLt
  have hv := v.isLt
  push_cast
  omega

private lemma cubicMultiplicity_top (q : ℕ) (hq : 0 < q) :
    cubicMultiplicity q (2 * q - 1) = 0 := by
  by_cases hq1 : q = 1
  · subst q
    norm_num [cubicMultiplicity]
  have hnot : ¬ 2 * q - 1 ≤ q := by omega
  simp only [cubicMultiplicity, if_neg hnot]
  push_cast
  rw [show ((2 * q - 1 : ℕ) : ℝ) = 2 * (q : ℝ) - 1 by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * q)]
    push_cast
    ring]
  ring

/-- Exact main-quadruple multiplicity at every positive frequency in its full
support, including the empty outer endpoint. -/
theorem mainFrequencyMultiplicity_eq_cubic
    (q h : ℕ) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    (mainFrequencyMultiplicity q (h : ℤ) : ℝ) = cubicMultiplicity q h := by
  by_cases hhq : h ≤ q
  · exact mainFrequencyMultiplicity_eq_cubic_first q h hh0 hhq
  · by_cases htop : h = 2 * q - 1
    · subst h
      have hz : (((2 * q - 1 : ℕ) : ℤ)) = 2 * (q : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * q)]
        push_cast
        ring
      rw [hz, mainFrequencyMultiplicity_top q (by omega), Nat.cast_zero,
        cubicMultiplicity_top q (by omega)]
    · exact mainFrequencyMultiplicity_eq_cubic_late q h (by omega) (by omega)

/-- The finite presentation of `F_q^2` has exactly the closed coefficient
from T130 throughout the positive support. -/
theorem aggregatedFejerSquareCoefficient_eq
    (q h : ℕ) (hq : 0 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    aggregatedCoefficient (fejerSquarePresentationCoefficient q)
        (@jacksonFrequency q) (h : ℤ) = fejerSquareCoefficient q h := by
  rw [aggregatedFejerSquareCoefficient_eq_card,
    mainFrequencyMultiplicity_eq_cubic q h hh0 hhsupp]
  rfl

end Theory.PiDigits.MainFrequencyFibers

#print axioms Theory.PiDigits.MainFrequencyFibers.mainFrequencyMultiplicity_eq_cubic
#print axioms Theory.PiDigits.MainFrequencyFibers.aggregatedFejerSquareCoefficient_eq
