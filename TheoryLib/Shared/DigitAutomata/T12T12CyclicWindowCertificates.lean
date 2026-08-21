import TheoryLib.Shared.DigitAutomata.T9T9CyclicSparseForbidden

/-!
# T12: geometric certificates for cyclic window events

Canonical source: `problems/local/multiplicative-avoidance-gap.txt`
SHA-256: `05d09b6edb60fa060cc952fc5b2fad9dea75c20d84ac628d86f1b6dd6b0ab7c8`
Original source URL: none; the canonical file records a local formulation on 2026-07-26.

This module proves only finite cyclic-word counting certificates and applies the
kernel-checked T9 local-lemma interface. It contains no arithmetic carry model,
endpoint convention, `Y`, `Gamma`, entropy-gap bound, or claim about C1.
-/

open Finset

namespace Theory.Shared.DigitAutomata.T12

open Theory.Shared.DigitAutomata.T9

section FiniteCoordinates

variable {X A C : Type*} [Fintype X] [Fintype A] [Fintype C]

/-- Exact cardinality factorization for predicates on the two components of a
finite product decomposition. -/
theorem split_predicate_cardinality (e : X ≃ A × C)
    (P : A → Prop) (Q : C → Prop) [DecidablePred P] [DecidablePred Q] :
    ((Finset.univ.filter fun x ↦ P (e x).1 ∧ Q (e x).2).card * Fintype.card X =
      (Finset.univ.filter fun x ↦ P (e x).1).card *
        (Finset.univ.filter fun x ↦ Q (e x).2).card) := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype,
    ← Fintype.card_subtype, Fintype.card_congr e]
  let ePQ : {x : X // P (e x).1 ∧ Q (e x).2} ≃ {a : A // P a} × {c : C // Q c} :=
    (e.subtypeEquiv fun _ ↦ Iff.rfl).trans Equiv.subtypeProdEquivProd
  let eP : {x : X // P (e x).1} ≃ {a : A // P a} × C :=
    (e.subtypeEquiv fun _ ↦ Iff.rfl).trans Equiv.prodSubtypeFstEquivSubtypeProd
  let eQ : {x : X // Q (e x).2} ≃ A × {c : C // Q c} :=
    (e.subtypeEquiv fun _ ↦ Iff.rfl).trans <|
      (((Equiv.prodComm A C).subtypeEquiv fun _ ↦ Iff.rfl).trans
        Equiv.prodSubtypeFstEquivSubtypeProd).trans
          (Equiv.prodComm {c : C // Q c} A)
  rw [Fintype.card_congr ePQ, Fintype.card_congr eP, Fintype.card_congr eQ]
  simp only [Fintype.card_prod]
  ring

/-- Counting a predicate on the first component leaves every second component
free. -/
theorem split_first_cardinality (e : X ≃ A × C)
    (P : A → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x ↦ P (e x).1).card =
      (Finset.univ.filter P).card * Fintype.card C := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  let eP : {x : X // P (e x).1} ≃ {a : A // P a} × C :=
    (e.subtypeEquiv fun _ ↦ Iff.rfl).trans Equiv.prodSubtypeFstEquivSubtypeProd
  rw [Fintype.card_congr eP, Fintype.card_prod]

end FiniteCoordinates

section CyclicGeometry

/-- The coordinate embedding of the length-`m` cyclic window beginning at `i`. -/
def cyclicEmbedding (n m : ℕ) (hmn : m ≤ n) (i : Fin n) : Fin m ↪ Fin n where
  toFun j := i + Fin.castLE hmn j
  inj' := by
    intro j k hjk
    exact Fin.castLE_injective hmn (add_left_cancel hjk)

/-- The set of coordinates read by one cyclic window. -/
def cyclicSupport (n m : ℕ) (hmn : m ≤ n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.map (cyclicEmbedding n m hmn i)

/-- Two distinct starts are neighbors exactly when their cyclic windows overlap. -/
def overlapNeighbor (n m : ℕ) (hmn : m ≤ n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ ¬Disjoint (cyclicSupport n m hmn i)
    (cyclicSupport n m hmn j)

/-- A positive offset strictly smaller than the window length, viewed modulo
the cyclic period. -/
def positiveOffset (n m : ℕ) (hmn : m ≤ n) (r : Fin (m - 1)) : Fin n :=
  ⟨r.val + 1, by omega⟩

/-- The at most `2*(m-1)` possible nonzero forward and backward offsets from
one cyclic start. -/
def overlapCandidates (n m : ℕ) (hmn : m ≤ n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.image fun r : Fin (m - 1) ⊕ Fin (m - 1) ↦
    Sum.elim (fun d ↦ i + positiveOffset n m hmn d)
      (fun d ↦ i - positiveOffset n m hmn d) r

@[simp] theorem mem_cyclicSupport (n m : ℕ) (hmn : m ≤ n)
    (i r : Fin n) :
    r ∈ cyclicSupport n m hmn i ↔
      r ∈ Set.range (cyclicEmbedding n m hmn i) := by
  simp [cyclicSupport]

@[simp] theorem cyclicEmbedding_apply (n m : ℕ) (hmn : m ≤ n)
    (i : Fin n) (j : Fin m) :
    (cyclicEmbedding n m hmn i j).val = (i.val + j.val) % n := by
  simp [cyclicEmbedding, Fin.add_def]

theorem cyclicWindow_eq_restrict (b n m : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (x : Fin n → Fin b) (i : Fin n) :
    cyclicWindow b n m hn x i = fun j ↦ x (cyclicEmbedding n m hmn i j) := by
  funext j
  apply congrArg x
  apply Fin.ext
  exact cyclicEmbedding_apply n m hmn i j |>.symm

/-- A cyclic window is unchanged when two words agree away from a disjoint
window support. -/
theorem cyclicWindow_eq_of_eq_off_support (b n m : ℕ) (hn : 0 < n)
    (hmn : m ≤ n) {i j : Fin n} {x y : Fin n → Fin b}
    (hdisj : Disjoint (cyclicSupport n m hmn i) (cyclicSupport n m hmn j))
    (hxy : ∀ r, r ∉ cyclicSupport n m hmn i → x r = y r) :
    cyclicWindow b n m hn x j = cyclicWindow b n m hn y j := by
  rw [cyclicWindow_eq_restrict b n m hn hmn,
    cyclicWindow_eq_restrict b n m hn hmn]
  funext a
  apply hxy
  intro ha
  exact Finset.disjoint_left.mp hdisj ha (by simp [cyclicSupport])

/-- A full cyclic word splits into its coordinates on one window and all
remaining coordinates. -/
def cyclicSplitEquiv (b n m : ℕ) (hmn : m ≤ n) (i : Fin n) :
    (Fin n → Fin b) ≃
      (Fin m → Fin b) × ({r : Fin n // r ∉ Set.range (cyclicEmbedding n m hmn i)} → Fin b) :=
  (Equiv.piEquivPiSubtypeProd
      (fun r ↦ r ∈ Set.range (cyclicEmbedding n m hmn i)) (fun _ ↦ Fin b)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun _ : Set.range (cyclicEmbedding n m hmn i) ↦ Fin b)
        (cyclicEmbedding n m hmn i).toEquivRange).symm
      (Equiv.refl _))

@[simp] theorem cyclicSplitEquiv_fst (b n m : ℕ) (hn : 0 < n) (hmn : m ≤ n)
    (i : Fin n) (x : Fin n → Fin b) :
    (cyclicSplitEquiv b n m hmn i x).1 = cyclicWindow b n m hn x i := by
  funext j
  rw [cyclicWindow_eq_restrict]
  rfl

/-- Equality of the outside components means equality at every coordinate
outside the selected window. -/
theorem eq_off_support_of_cyclicSplitEquiv_snd_eq (b n m : ℕ) (hmn : m ≤ n)
    (i : Fin n) {x y : Fin n → Fin b}
    (hxy : (cyclicSplitEquiv b n m hmn i x).2 =
      (cyclicSplitEquiv b n m hmn i y).2) :
    ∀ r, r ∉ cyclicSupport n m hmn i → x r = y r := by
  intro r hr
  have hrange : r ∉ Set.range (cyclicEmbedding n m hmn i) := by
    simpa using hr
  exact congrFun hxy ⟨r, hrange⟩

/-- The exact cardinality of a single cyclic forbidden-window event. -/
theorem cyclicBadAt_card_exact (b n m : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hm : 0 < m) (hlarge : 2 * m - 1 ≤ n)
    (F : Finset (Fin m → Fin b)) (i : Fin n) :
    (cyclicBadAt b n m hn F i).card = F.card * b ^ (n - m) := by
  have hmn : m ≤ n := by omega
  have hcount := split_first_cardinality (cyclicSplitEquiv b n m hmn i)
    (fun w : Fin m → Fin b ↦ w ∈ F)
  rw [show cyclicBadAt b n m hn F i =
      Finset.univ.filter (fun x ↦ (cyclicSplitEquiv b n m hmn i x).1 ∈ F) by
        ext x
        simp [cyclicBadAt, cyclicSplitEquiv_fst b n m hn hmn i x]]
  rw [hcount]
  congr 1
  · simp
  · have hsupport :
        Fintype.card {x // x ∈ Set.range (cyclicEmbedding n m hmn i)} = m := by
      rw [← Fintype.card_congr (cyclicEmbedding n m hmn i).toEquivRange]
      simp
    have hcompl :
        Fintype.card {x // x ∉ Set.range (cyclicEmbedding n m hmn i)} = n - m := by
      rw [Fintype.card_subtype_compl, hsupport]
      simp
    rw [Fintype.card_fun, hcompl]
    simp

/-- Cleared-denominator form of the exact single-window count required by T9. -/
theorem cyclicBadAt_mass_identity (b n m : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hm : 0 < m) (hlarge : 2 * m - 1 ≤ n)
    (F : Finset (Fin m → Fin b)) (i : Fin n) :
    mass (cyclicBadAt b n m hn F i) * (b : ℝ) ^ m =
      F.card * mass (Finset.univ : Finset (Fin n → Fin b)) := by
  rw [mass_univ_cyclicWords]
  unfold mass
  rw [cyclicBadAt_card_exact b n m hb hn hm hlarge F i]
  norm_cast
  have hpow : b ^ n = b ^ (n - m) * b ^ m := by
    conv_lhs => rw [show n = (n - m) + m by omega, pow_add]
  rw [hpow]
  ac_rfl

/-- Nonneighbors have disjoint cyclic coordinate supports. -/
theorem support_disjoint_of_not_neighbor (n m : ℕ) (hmn : m ≤ n)
    {i j : Fin n} (hji : j ≠ i) (hjn : j ∉ overlapNeighbor n m hmn i) :
    Disjoint (cyclicSupport n m hmn i) (cyclicSupport n m hmn j) := by
  simpa [overlapNeighbor, hji] using hjn

/-- Every distinct overlapping start is one of the forward or backward
offset candidates. -/
theorem overlapNeighbor_subset_candidates (n m : ℕ) (hmn : m ≤ n)
    (hm : 0 < m) (i : Fin n) :
    overlapNeighbor n m hmn i ⊆ overlapCandidates n m hmn i := by
  letI : NeZero n := ⟨by omega⟩
  intro j hj
  have hj' := (mem_filter.mp hj).2
  rcases hj' with ⟨hji, hoverlap⟩
  rcases Finset.not_disjoint_iff.mp hoverlap with ⟨r, hri, hrj⟩
  rw [mem_cyclicSupport] at hri hrj
  rcases hri with ⟨a, ha⟩
  rcases hrj with ⟨c, hc⟩
  have hac : a ≠ c := by
    intro hac
    subst c
    apply hji
    apply add_right_cancel (b := Fin.castLE hmn a)
    simpa [cyclicEmbedding] using (ha.trans hc.symm).symm
  by_cases hca : c.val < a.val
  · let d : Fin (m - 1) := ⟨a.val - c.val - 1, by omega⟩
    have hoffset : Fin.castLE hmn a = Fin.castLE hmn c + positiveOffset n m hmn d := by
      apply Fin.ext
      change a.val = (c.val + (d.val + 1)) % n
      rw [Nat.mod_eq_of_lt (by dsimp [d]; omega)]
      dsimp [d]
      omega
    have hj : j = i + positiveOffset n m hmn d := by
      apply add_right_cancel (b := Fin.castLE hmn c)
      calc
        j + Fin.castLE hmn c = i + Fin.castLE hmn a := by
          simpa [cyclicEmbedding] using hc.trans ha.symm
        _ = (i + positiveOffset n m hmn d) + Fin.castLE hmn c := by
          rw [hoffset]
          ac_rfl
    rw [overlapCandidates, mem_image]
    exact ⟨Sum.inl d, mem_univ _, by simpa [hj]⟩
  · have haclt : a.val < c.val := by omega
    let d : Fin (m - 1) := ⟨c.val - a.val - 1, by omega⟩
    have hoffset : Fin.castLE hmn c = Fin.castLE hmn a + positiveOffset n m hmn d := by
      apply Fin.ext
      change c.val = (a.val + (d.val + 1)) % n
      rw [Nat.mod_eq_of_lt (by dsimp [d]; omega)]
      dsimp [d]
      omega
    have hsum : j + positiveOffset n m hmn d = i := by
      apply add_right_cancel (b := Fin.castLE hmn a)
      calc
        (j + positiveOffset n m hmn d) + Fin.castLE hmn a =
            j + Fin.castLE hmn c := by rw [hoffset]; ac_rfl
        _ = i + Fin.castLE hmn a := by
          simpa [cyclicEmbedding] using hc.trans ha.symm
    have hj : j = i - positiveOffset n m hmn d :=
      eq_sub_iff_add_eq.mpr hsum
    rw [overlapCandidates, mem_image]
    exact ⟨Sum.inr d, mem_univ _, by simpa [hj]⟩

/-- Avoidance of nonneighbor events depends only on coordinates outside the
selected window. -/
theorem avoids_eq_of_cyclicSplitEquiv_snd_eq (b n m : ℕ) (hn : 0 < n)
    (hmn : m ≤ n) (F : Finset (Fin m → Fin b)) (i : Fin n)
    (T : Finset (Fin n)) (hiT : i ∉ T)
    (hTnon : ∀ j ∈ T, j ∉ overlapNeighbor n m hmn i)
    {x y : Fin n → Fin b}
    (hxy : (cyclicSplitEquiv b n m hmn i x).2 =
      (cyclicSplitEquiv b n m hmn i y).2) :
    x ∈ avoids (cyclicBadAt b n m hn F) T ↔
      y ∈ avoids (cyclicBadAt b n m hn F) T := by
  have hoff := eq_off_support_of_cyclicSplitEquiv_snd_eq b n m hmn i hxy
  have hwindow (j : Fin n) (hjT : j ∈ T) :
      cyclicWindow b n m hn x j = cyclicWindow b n m hn y j := by
    apply cyclicWindow_eq_of_eq_off_support b n m hn hmn
      (support_disjoint_of_not_neighbor n m hmn (fun hji ↦ hiT (by simpa [hji] using hjT))
        (hTnon j hjT))
    exact hoff
  simp only [avoids, mem_filter, mem_univ, true_and, cyclicBadAt]
  constructor
  · intro hx j hjT hy
    apply hx j hjT
    simpa [hwindow j hjT] using hy
  · intro hy j hjT hx
    apply hy j hjT
    simpa [hwindow j hjT] using hx

/-- Exact factorization of one bad event from avoidance of any set of
nonneighboring events. -/
theorem cyclic_nonneighbor_factorization (b n m : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hm : 0 < m) (hlarge : 2 * m - 1 ≤ n)
    (F : Finset (Fin m → Fin b)) (i : Fin n) (T : Finset (Fin n))
    (hiT : i ∉ T) (hTnon : ∀ j ∈ T, j ∉ overlapNeighbor n m (by omega) i) :
    mass (badAndAvoids (cyclicBadAt b n m hn F) i T) *
        mass (Finset.univ : Finset (Fin n → Fin b)) =
      mass (cyclicBadAt b n m hn F i) *
        mass (avoids (cyclicBadAt b n m hn F) T) := by
  let hmn : m ≤ n := by omega
  let E := cyclicSplitEquiv b n m hmn i
  let zeroInside : Fin m → Fin b := fun _ ↦ ⟨0, hb⟩
  let Q : ({r : Fin n // r ∉ Set.range (cyclicEmbedding n m hmn i)} → Fin b) → Prop :=
    fun outside ↦ E.symm (zeroInside, outside) ∈
      avoids (cyclicBadAt b n m hn F) T
  have hbad (x : Fin n → Fin b) :
      x ∈ cyclicBadAt b n m hn F i ↔ (E x).1 ∈ F := by
    simp [E, cyclicBadAt, cyclicSplitEquiv_fst b n m hn hmn i x]
  have havoids (x : Fin n → Fin b) :
      x ∈ avoids (cyclicBadAt b n m hn F) T ↔ Q (E x).2 := by
    apply avoids_eq_of_cyclicSplitEquiv_snd_eq b n m hn hmn F i T hiT hTnon
    simp [E, Q]
  have hfactor := split_predicate_cardinality E
    (fun w : Fin m → Fin b ↦ w ∈ F) Q
  unfold mass badAndAvoids
  norm_cast
  rw [show cyclicBadAt b n m hn F i =
      Finset.univ.filter (fun x ↦ (E x).1 ∈ F) by
        ext x
        simp [hbad],
    show avoids (cyclicBadAt b n m hn F) T =
      Finset.univ.filter (fun x ↦ Q (E x).2) by
        ext x
        simp [havoids]]
  simpa [Finset.filter_and, and_comm] using hfactor

/-- The overlap graph has at most `2*(m-1)` neighbors at every start. -/
theorem overlapNeighbor_card_le (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hlarge : 2 * m - 1 ≤ n) (i : Fin n) :
    (overlapNeighbor n m (by omega) i).card ≤ 2 * (m - 1) := by
  let hmn : m ≤ n := by omega
  calc
    (overlapNeighbor n m hmn i).card ≤ (overlapCandidates n m hmn i).card :=
      card_le_card (overlapNeighbor_subset_candidates n m hmn hm i)
    _ ≤ Fintype.card (Fin (m - 1) ⊕ Fin (m - 1)) := by
      exact card_image_le.trans_eq (by simp)
    _ = 2 * (m - 1) := by simp [two_mul]

/-- The geometric overlap graph satisfies T9's exact dependency interface. -/
theorem cyclic_strongDependency (b n m : ℕ) (hb : 0 < b) (hn : 0 < n)
    (hm : 0 < m) (hlarge : 2 * m - 1 ≤ n)
    (F : Finset (Fin m → Fin b)) :
    StrongDependency (cyclicBadAt b n m hn F)
      (overlapNeighbor n m (by omega)) := by
  intro i T hiT hTnon
  exact cyclic_nonneighbor_factorization b n m hb hn hm hlarge F i T hiT hTnon

/-- T6's cyclic growth estimate with all three geometric certificates discharged. -/
theorem t6_cyclic_list_growth_of_large_period
    (b q e k n : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hqe : q ≤ b ^ e)
    (hk : 2 * e + 12 ≤ k) (hn : 0 < n)
    (hperiod : 2 * (k + e) - 1 ≤ n)
    (F : Finset (Fin (k + e) → Fin b))
    (hFcard : F.card ≤ 4 * b ^ e)
    (hquarter : 4 / (b : ℝ) ^ k ≤ 1 / 4)
    (hdependencySmall :
      ((2 * (2 * (k + e - 1)) : ℕ) : ℝ) *
        (4 / (b : ℝ) ^ k) ≤ 1 / 2) :
    ((b : ℝ) * (1 - 8 / (b : ℝ) ^ k)) ^ n ≤
      (cyclicAvoiders b n (k + e) hn F).card := by
  apply Theory.Shared.DigitAutomata.T9.t6_cyclic_list_growth b q e k n hb hq hqe hk hn F
    (overlapNeighbor n (k + e) (by omega)) hFcard
  · exact fun i ↦ overlapNeighbor_card_le n (k + e) hn (by omega) hperiod i
  · exact cyclic_strongDependency b n (k + e) (by omega) hn (by omega) hperiod F
  · exact fun i ↦ cyclicBadAt_mass_identity b n (k + e) (by omega) hn
      (by omega) hperiod F i
  · exact hquarter
  · exact hdependencySmall

end CyclicGeometry

#print axioms Theory.Shared.DigitAutomata.T12.split_predicate_cardinality
#print axioms Theory.Shared.DigitAutomata.T12.cyclicBadAt_card_exact
#print axioms Theory.Shared.DigitAutomata.T12.cyclicBadAt_mass_identity
#print axioms Theory.Shared.DigitAutomata.T12.cyclic_nonneighbor_factorization
#print axioms Theory.Shared.DigitAutomata.T12.overlapNeighbor_card_le
#print axioms Theory.Shared.DigitAutomata.T12.cyclic_strongDependency
#print axioms Theory.Shared.DigitAutomata.T12.t6_cyclic_list_growth_of_large_period

end Theory.Shared.DigitAutomata.T12

