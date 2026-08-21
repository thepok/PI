import TheoryLib.PiQuantitativeBlockHitting.T32T32RecurrentRightSpecial

/-!
# T33: sharpness of recurrent right-special growth

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file gives an exact finite-alphabet separator for T31 and T32.  The
decimal stream with digit `1` exactly at zero-based powers of two, and digit
`0` elsewhere, is aperiodic but has exactly `n + 1` recurrent length-`n`
factors for every positive `n`.  At every length its all-zero factor is the
unique recurrent right-special factor.

The represented decimal is a leading-zero shift of the classical Kempner
number `sum k, 10 ^ (-(2 ^ k))`.  Shallit's bounded-continued-fraction result
for that number is a literature statement recorded in `ultrapi.md`; it is not
used as a Lean premise here.  This module proves only the combinatorial
sharpness result and makes no digit-distribution claim about pi.
-/

noncomputable section

namespace Theory.PiDigits.RecurrentFactorComplexity.KempnerSharpness

open DecimalFactorComplexity
open Theory.PiDigits.RecurrentFactorComplexity

/-- A decimal stream whose digit is `1` exactly at zero-based powers of two. -/
noncomputable def spikeStream (m : ℕ) : Fin 10 := by
  classical
  exact if ∃ k : ℕ, m = 2 ^ k then 1 else 0

@[simp] lemma spikeStream_pow (k : ℕ) : spikeStream (2 ^ k) = 1 := by
  simp [spikeStream]

lemma spikeStream_eq_zero_of_between_powers {m k : ℕ}
    (hlow : 2 ^ k < m) (hhigh : m < 2 ^ (k + 1)) :
    spikeStream m = 0 := by
  rw [spikeStream, if_neg]
  rintro ⟨j, rfl⟩
  have hkj : k < j :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlow
  have hjk : j < k + 1 :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hhigh
  omega

lemma spikeStream_eq_zero_or_one (m : ℕ) :
    spikeStream m = 0 ∨ spikeStream m = 1 := by
  classical
  simp only [spikeStream]
  split <;> simp

lemma spikeStream_ne_zero_iff (m : ℕ) :
    spikeStream m ≠ 0 ↔ ∃ k : ℕ, m = 2 ^ k := by
  classical
  simp [spikeStream]

/-- The powers-of-two spike stream is not eventually periodic. -/
theorem spikeStream_not_eventuallyPeriodic :
    ¬ EventuallyPeriodic spikeStream := by
  rintro ⟨N, p, hp, hperiod⟩
  let k := max N p
  have hk : max N p < 2 ^ k := by
    simpa [k] using (max N p).lt_two_pow_self
  let m := 2 ^ k
  have hN : N ≤ m := by dsimp [m]; omega
  have hpm : p < m := by dsimp [m]; omega
  have hlow : 2 ^ k < m + p := by dsimp [m]; omega
  have hhigh : m + p < 2 ^ (k + 1) := by
    rw [pow_succ]
    dsimp [m]
    omega
  have h := hperiod (m - N)
  rw [Nat.add_sub_of_le hN] at h
  rw [spikeStream_pow k] at h
  have hzero := spikeStream_eq_zero_of_between_powers hlow hhigh
  rw [hzero] at h
  norm_num at h

/-- Far enough out, a length-`n` window contains at most one spike. -/
lemma blockAt_spikeStream_atMostOne (n i : ℕ) (hi : 2 ^ n ≤ i)
    {j k : Fin n}
    (hj : blockAt spikeStream n i j ≠ 0)
    (hk : blockAt spikeStream n i k ≠ 0) :
    j = k := by
  have hj' : spikeStream (i + j) ≠ 0 := hj
  have hk' : spikeStream (i + k) ≠ 0 := hk
  obtain ⟨a, ha⟩ := (spikeStream_ne_zero_iff (i + j)).mp hj'
  obtain ⟨b, hb⟩ := (spikeStream_ne_zero_iff (i + k)).mp hk'
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hpq : 2 ^ a < 2 ^ b := by omega
    have hab : a < b :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpq
    have hgap : 2 ^ a ≤ 2 ^ b - 2 ^ a := by
      have hdouble : 2 * 2 ^ a ≤ 2 ^ b := by
        calc
          2 * 2 ^ a = 2 ^ (a + 1) := by rw [pow_succ]; omega
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hlarge : 2 ^ n ≤ 2 ^ a := by omega
    have hsmall : 2 ^ b - 2 ^ a < n := by
      have hjval : (j : ℕ) < n := j.isLt
      have hkval : (k : ℕ) < n := k.isLt
      omega
    have hn : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  · have hpq : 2 ^ b < 2 ^ a := by omega
    have hba : b < a :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpq
    have hgap : 2 ^ b ≤ 2 ^ a - 2 ^ b := by
      have hdouble : 2 * 2 ^ b ≤ 2 ^ a := by
        calc
          2 * 2 ^ b = 2 ^ (b + 1) := by rw [pow_succ]; omega
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hlarge : 2 ^ n ≤ 2 ^ b := by omega
    have hsmall : 2 ^ a - 2 ^ b < n := by
      have hjval : (j : ℕ) < n := j.isLt
      have hkval : (k : ℕ) < n := k.isLt
      omega
    have hn : n < 2 ^ n := Nat.lt_two_pow_self
    omega

/-- A block has at most one nonzero coordinate. -/
def AtMostOneNonzero {n : ℕ} (w : Block (Fin 10) n) : Prop :=
  ∀ ⦃j k : Fin n⦄, w j ≠ 0 → w k ≠ 0 → j = k

/-- Every coordinate of a block is zero or one. -/
def ZeroOneValued {n : ℕ} (w : Block (Fin 10) n) : Prop :=
  ∀ j, w j = 0 ∨ w j = 1

lemma recurrentFactor_atMostOne {n : ℕ}
    (w : RecurrentFactor spikeStream n) :
    AtMostOneNonzero w.1 := by
  obtain ⟨i, hi, hiw⟩ := w.2 (2 ^ n)
  intro j k hj hk
  apply blockAt_spikeStream_atMostOne n i hi
  · simpa [hiw] using hj
  · simpa [hiw] using hk

lemma recurrentFactor_zeroOneValued {n : ℕ}
    (w : RecurrentFactor spikeStream n) :
    ZeroOneValued w.1 := by
  obtain ⟨i, _hi, hiw⟩ := w.2 0
  intro j
  rw [← hiw]
  exact spikeStream_eq_zero_or_one (i + j)

/-- The unique nonzero coordinate of a block, if it has one. -/
noncomputable def supportIndex {n : ℕ} (w : Block (Fin 10) n) :
    Option (Fin n) := by
  classical
  exact if h : ∃ j, w j ≠ 0 then some h.choose else none

lemma supportIndex_eq_some_iff {n : ℕ} {w : Block (Fin 10) n}
    (hone : AtMostOneNonzero w) (j : Fin n) :
    supportIndex w = some j ↔ w j ≠ 0 := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ j, w j ≠ 0
    · rw [supportIndex, dif_pos hex] at h
      have hc : hex.choose = j := Option.some.inj h
      simpa [hc] using hex.choose_spec
    · rw [supportIndex, dif_neg hex] at h
      simp at h
  · intro hj
    have hex : ∃ j, w j ≠ 0 := ⟨j, hj⟩
    rw [supportIndex, dif_pos hex]
    congr 1
    exact hone hex.choose_spec hj

noncomputable def recurrentSupportIndex {n : ℕ} :
    RecurrentFactor spikeStream n → Option (Fin n) :=
  fun w => supportIndex w.1

lemma recurrentSupportIndex_injective (n : ℕ) :
    Function.Injective (@recurrentSupportIndex n) := by
  intro w v hmap
  apply Subtype.ext
  funext j
  have hnz : w.1 j ≠ 0 ↔ v.1 j ≠ 0 := by
    rw [← supportIndex_eq_some_iff (recurrentFactor_atMostOne w) j]
    rw [← supportIndex_eq_some_iff (recurrentFactor_atMostOne v) j]
    change supportIndex w.1 = supportIndex v.1 at hmap
    rw [hmap]
  rcases recurrentFactor_zeroOneValued w j with hw | hw
  · have hv : v.1 j = 0 := by
      by_contra hv
      exact (hnz.mpr hv) (by simp [hw])
    rw [hw, hv]
  · have hvnz : v.1 j ≠ 0 := hnz.mp (by simp [hw])
    rcases recurrentFactor_zeroOneValued v j with hv | hv
    · exact (hvnz hv).elim
    · rw [hw, hv]

/-- The canonical zero or singleton-one block associated to a support. -/
def supportBlock {n : ℕ} : Option (Fin n) → Block (Fin 10) n
  | none => fun _ => 0
  | some j => fun k => if k = j then 1 else 0

lemma recurrentFactor_eq_supportBlock {n : ℕ}
    (w : RecurrentFactor spikeStream n) :
    w.1 = supportBlock (recurrentSupportIndex w) := by
  funext k
  rcases hsupport : recurrentSupportIndex w with _ | j
  · have hk : w.1 k = 0 := by
      by_contra hnz
      have hsome :=
        (supportIndex_eq_some_iff (recurrentFactor_atMostOne w) k).2 hnz
      change recurrentSupportIndex w = some k at hsome
      rw [hsupport] at hsome
      simp at hsome
    simpa [supportBlock, hsupport] using hk
  · by_cases hkj : k = j
    · subst k
      have hnz : w.1 j ≠ 0 := by
        apply (supportIndex_eq_some_iff (recurrentFactor_atMostOne w) j).1
        exact hsupport
      rcases recurrentFactor_zeroOneValued w j with hz | hone
      · exact (hnz hz).elim
      · simpa [supportBlock, hsupport] using hone
    · have hk : w.1 k = 0 := by
        by_contra hnz
        have hsome :=
          (supportIndex_eq_some_iff (recurrentFactor_atMostOne w) k).2 hnz
        change recurrentSupportIndex w = some k at hsome
        rw [hsupport] at hsome
        exact hkj (Option.some.inj hsome.symm)
      simpa [supportBlock, hsupport, hkj] using hk

/-- The T31 recurrent-complexity lower bound is attained exactly at every
positive length by the powers-of-two spike stream. -/
theorem recurrentFactorComplexity_spikeStream (n : ℕ) (hn : 0 < n) :
    recurrentFactorComplexity spikeStream n = n + 1 := by
  apply Nat.le_antisymm
  · rw [recurrentFactorComplexity]
    calc
      Nat.card (RecurrentFactor spikeStream n) ≤ Nat.card (Option (Fin n)) :=
        Nat.card_le_card_of_injective recurrentSupportIndex
          (recurrentSupportIndex_injective n)
      _ = n + 1 := by simp
  · exact recurrentFactorComplexity_lower_bound spikeStream
      spikeStream_not_eventuallyPeriodic n hn

/-- The support coordinate completely and exactly classifies recurrent
length-`n` factors. `none` is the zero block; `some j` is the block whose
unique one lies at `j`. -/
theorem recurrentSupportIndex_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (@recurrentSupportIndex n) := by
  apply (Nat.bijective_iff_injective_and_card recurrentSupportIndex).2
  refine ⟨recurrentSupportIndex_injective n, ?_⟩
  calc
    Nat.card (RecurrentFactor spikeStream n) =
        recurrentFactorComplexity spikeStream n := rfl
    _ = n + 1 := recurrentFactorComplexity_spikeStream n hn
    _ = Nat.card (Option (Fin n)) := by simp

theorem recurrentSupportIndex_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (@recurrentSupportIndex n) :=
  (recurrentSupportIndex_bijective n hn).2

/-- Every one of the `n + 1` possible supports is realized by exactly one
recurrent factor. -/
theorem existsUnique_recurrentFactor_with_support
    (n : ℕ) (hn : 0 < n) (o : Option (Fin n)) :
    ∃! w : RecurrentFactor spikeStream n, recurrentSupportIndex w = o := by
  obtain ⟨w, hw⟩ := recurrentSupportIndex_surjective n hn o
  refine ⟨w, hw, ?_⟩
  intro v hv
  exact recurrentSupportIndex_injective n (hv.trans hw.symm)

/-- Exact shape classification: for positive length, the zero block and each
singleton-one block occur recurrently, and each shape gives one recurrent
factor. -/
theorem existsUnique_recurrentFactor_eq_supportBlock
    (n : ℕ) (hn : 0 < n) (o : Option (Fin n)) :
    ∃! w : RecurrentFactor spikeStream n, w.1 = supportBlock o := by
  obtain ⟨w, hw⟩ := recurrentSupportIndex_surjective n hn o
  have hshape : w.1 = supportBlock o := by
    simpa [hw] using recurrentFactor_eq_supportBlock w
  refine ⟨w, hshape, ?_⟩
  intro v hv
  apply Subtype.ext
  exact hv.trans hshape.symm

/-- A recurrent factor is right-special when it has two recurrent extensions
with different final digits. -/
def IsRecurrentRightSpecial {n : ℕ}
    (w : RecurrentFactor spikeStream n) : Prop :=
  ∃ v₁ v₂ : RecurrentFactor spikeStream (n + 1),
    recurrentInitial spikeStream n v₁ = w ∧
    recurrentInitial spikeStream n v₂ = w ∧
    v₁.1 (Fin.last n) ≠ v₂.1 (Fin.last n)

/-- Every recurrent right-special factor of the spike stream is the all-zero
block. -/
lemma recurrentRightSpecial_eq_zero {n : ℕ}
    {w : RecurrentFactor spikeStream n}
    (hw : IsRecurrentRightSpecial w) :
    w.1 = fun _ => 0 := by
  obtain ⟨v₁, v₂, hv₁, hv₂, hlast⟩ := hw
  have hinit₁ := congrArg Subtype.val hv₁
  have hinit₂ := congrArg Subtype.val hv₂
  change initial v₁.1 = w.1 at hinit₁
  change initial v₂.1 = w.1 at hinit₂
  funext j
  by_contra hj
  have hj₁ : v₁.1 j.castSucc ≠ 0 := by
    have heq := congrFun hinit₁ j
    change v₁.1 j.castSucc = w.1 j at heq
    exact fun hzero => hj (heq.symm.trans hzero)
  have hj₂ : v₂.1 j.castSucc ≠ 0 := by
    have heq := congrFun hinit₂ j
    change v₂.1 j.castSucc = w.1 j at heq
    exact fun hzero => hj (heq.symm.trans hzero)
  have hlast₁ : v₁.1 (Fin.last n) = 0 := by
    by_contra hnz
    have heq := recurrentFactor_atMostOne v₁ hj₁ hnz
    exact Fin.castSucc_ne_last j heq
  have hlast₂ : v₂.1 (Fin.last n) = 0 := by
    by_contra hnz
    have heq := recurrentFactor_atMostOne v₂ hj₂ hnz
    exact Fin.castSucc_ne_last j heq
  exact hlast (hlast₁.trans hlast₂.symm)

/-- At each length, including zero, the all-zero recurrent factor is the
unique recurrent right-special factor. -/
theorem existsUnique_recurrentRightSpecial (n : ℕ) :
    ∃! w : RecurrentFactor spikeStream n, IsRecurrentRightSpecial w := by
  obtain ⟨w, v₁, v₂, hv₁, hv₂, hlast⟩ :=
    exists_recurrent_block_two_recurrent_right_extensions
      spikeStream spikeStream_not_eventuallyPeriodic n
  have hw : IsRecurrentRightSpecial w := ⟨v₁, v₂, hv₁, hv₂, hlast⟩
  refine ⟨w, hw, ?_⟩
  intro v hv
  apply Subtype.ext
  exact (recurrentRightSpecial_eq_zero hv).trans
    (recurrentRightSpecial_eq_zero hw).symm

end Theory.PiDigits.RecurrentFactorComplexity.KempnerSharpness

namespace Theory.PiDigits.RecurrentFactorComplexity.KempnerSharpness

#print axioms spikeStream_not_eventuallyPeriodic
#print axioms recurrentFactorComplexity_spikeStream
#print axioms recurrentSupportIndex_bijective
#print axioms existsUnique_recurrentFactor_eq_supportBlock
#print axioms existsUnique_recurrentRightSpecial

end Theory.PiDigits.RecurrentFactorComplexity.KempnerSharpness
