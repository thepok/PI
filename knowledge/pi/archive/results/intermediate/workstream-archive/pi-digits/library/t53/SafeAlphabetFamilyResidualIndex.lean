import TheoryLib.PiDigits.T50BackgroundMarkerZero
import TheoryLib.PiDigits.T51ArbitraryWordResidualIndex
import TheoryLib.PiDigits.T52SimultaneousFamilyResidualIndex
import Mathlib.Data.Fintype.Pigeonhole

/-!
# T53: fixed-safe-alphabet finite-family residual index

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

This file treats exactly finite nonempty families of nonempty decimal words
such that every word contains a digit outside the fixed alphabet `{1, 2}`.
The outside digit may depend on the word, so a common digit is not required.

This does not treat arbitrary forbidden families or arbitrary safe alphabets.
The external level and future schedule remain shared language parameters, not
fields available to a persistent-state code, so schedule-aware controllers are
excluded. Nothing here concerns the decimal digits of `Real.pi`,
`T37.JMix Real.pi`, canonical V1, or sibling V3.
-/

namespace Theory.PiDigits.T53

open Theory.PiDigits

noncomputable section

abbrev DecimalWord := T52.DecimalWord

/-- Every digit lies in the fixed safe alphabet `{1, 2}`. -/
def Safe12Digits (digits : DecimalWord) : Prop :=
  ∀ d ∈ digits, d = (1 : Fin 10) ∨ d = (2 : Fin 10)

/-- The exact T53 family class: finite and nonempty, with nonempty words, each
of which contains some digit outside the fixed safe alphabet `{1, 2}`. -/
def Safe12Family (F : Finset DecimalWord) : Prop :=
  F.Nonempty ∧ (∀ w ∈ F, w ≠ []) ∧
    ∀ w ∈ F, ∃ d ∈ w, d ≠ (1 : Fin 10) ∧ d ≠ (2 : Fin 10)

theorem safe12Digits_append {u v : DecimalWord}
    (hu : Safe12Digits u) (hv : Safe12Digits v) :
    Safe12Digits (u ++ v) := by
  intro d hd
  rw [List.mem_append] at hd
  exact hd.elim (hu d) (hv d)

/-- T50's complete background-marker source is `{1,2}`-valued. -/
theorem backgroundMarkerWord_safe12 (length k : ℕ) :
    Safe12Digits (T50.backgroundMarkerWord length k) := by
  intro d hd
  simp only [T50.backgroundMarkerWord, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hd
  rcases hd with hfront | hright
  · rcases hfront with hone | htwo
    · exact Or.inl hone.2
    · exact Or.inr htwo
  · exact Or.inl hright.2

/-- Every T50 source prefix used at a common level is `{1,2}`-valued. -/
theorem familySource_safe12 (K : ℕ) (j : Fin (K + 1)) :
    Safe12Digits (T50.familyState K j).decimalPrefix := by
  rw [T50.family_decimalPrefix_eq]
  exact backgroundMarkerWord_safe12 _ _

theorem packetDigits_safe12_of_allOnes {packets : List T41.Packet}
    (h : T50.AllOnesContinuation packets) :
    Safe12Digits (T51.packetDigits packets) := by
  intro d hd
  simp only [T51.packetDigits, List.mem_flatMap] at hd
  obtain ⟨p, hp, hdp⟩ := hd
  exact Or.inl (h p hp d hdp)

/-- Every decimal digit in T50's all-one continuation lies in `{1,2}`. -/
theorem familySeparator_safe12 (K : ℕ) (j : Fin (K + 1)) :
    Safe12Digits (T51.packetDigits (T50.familySeparator K j)) :=
  packetDigits_safe12_of_allOnes (T50.familySeparator_allOnes K j)

/-- The full T50 source followed by its separator remains `{1,2}`-valued. -/
theorem family_fullSourceContinuation_safe12 (K : ℕ) (j : Fin (K + 1)) :
    Safe12Digits ((T50.familyState K j).decimalPrefix ++
      T51.packetDigits (T50.familySeparator K j)) :=
  safe12Digits_append (familySource_safe12 K j) (familySeparator_safe12 K j)

/-- A `{1,2}`-valued list avoids any word containing a digit outside `{1,2}`. -/
theorem avoidsWord_of_safe12 {w digits : DecimalWord}
    (hw : ∃ d ∈ w, d ≠ (1 : Fin 10) ∧ d ≠ (2 : Fin 10))
    (hdigits : Safe12Digits digits) : T51.AvoidsWord w digits := by
  obtain ⟨d, hdw, hd1, hd2⟩ := hw
  apply T51.avoidsWord_of_avoidsDigit hdw
  intro hd
  rcases hdigits d hd with h1 | h2
  · exact hd1 h1
  · exact hd2 h2

theorem avoidsFamily_of_safe12 {F : Finset DecimalWord}
    (hwords : ∀ w ∈ F,
      ∃ d ∈ w, d ≠ (1 : Fin 10) ∧ d ≠ (2 : Fin 10))
    {digits : DecimalWord} (hdigits : Safe12Digits digits) :
    T52.AvoidsFamily F digits := by
  intro w hw
  exact avoidsWord_of_safe12 (hwords w hw) hdigits

/-- The complete source-continuation path avoids every safe-family word. This
full-list statement includes occurrences crossing the retained source boundary. -/
theorem family_fullSourceContinuation_avoidsFamily
    {F : Finset DecimalWord} (hF : Safe12Family F)
    (K : ℕ) (j : Fin (K + 1)) :
    T52.AvoidsFamily F ((T50.familyState K j).decimalPrefix ++
      T51.packetDigits (T50.familySeparator K j)) :=
  avoidsFamily_of_safe12 hF.2.2
    (family_fullSourceContinuation_safe12 K j)

theorem familySource_avoidsFamily
    {F : Finset DecimalWord} (hF : Safe12Family F)
    (K : ℕ) (j : Fin (K + 1)) :
    T52.AvoidsFamily F (T50.familyState K j).decimalPrefix :=
  avoidsFamily_of_safe12 hF.2.2 (familySource_safe12 K j)

/-- T52's exact carry-plus-boundary residual induced by a T50 source. -/
def familyResidual (F : Finset DecimalWord) (K : ℕ)
    (j : Fin (K + 1)) : T52.FamilyResidualState F :=
  T52.familyResidualOf F (T50.familyState K j)

theorem familyResidual_injective (F : Finset DecimalWord) (K : ℕ) :
    Function.Injective (familyResidual F K) := by
  intro u v huv
  apply T50.familyResidual_injective K
  have hcarry := congrArg T52.FamilyResidualState.carry huv
  simpa [familyResidual, T52.familyResidualOf, T50.familyResidual] using hcarry

theorem family_persistentReachableAt
    {F : Finset DecimalWord} (hF : Safe12Family F)
    (K : ℕ) (j : Fin (K + 1)) :
    T52.PersistentReachableAt F (T50.familyLevel K) (familyResidual F K j) := by
  refine ⟨T50.familyState K j, ⟨?_, (T50.family_reachableAt K j).2,
    familySource_avoidsFamily hF K j⟩, rfl⟩
  exact T51.carryReachable_of_reachableFor (T50.family_reachableAt K j).1

/-- Boundary-sensitive acceptance: the retained boundaries accept exactly
because the complete source-plus-separator avoids every family word. -/
theorem familySeparator_acceptedForFamily
    {F : Finset DecimalWord} (hF : Safe12Family F)
    (K : ℕ) (j : Fin (K + 1)) :
    T52.AcceptedForFamily F (T41.balancedContext (T50.familyLevel K))
      (familyResidual F K j) (T50.familySeparator K j) := by
  apply (T52.acceptedForFamily_sourceBoundary_iff hF.2.1
    (familySource_avoidsFamily hF K j)
    (T41.balancedContext (T50.familyLevel K))
    (T50.familySeparator K j)).2
  constructor
  · simpa [T50.familyResidual] using
      T51.acceptedFor_implies_carryAccepted (T50.familySeparator_accepted K j)
  · exact family_fullSourceContinuation_avoidsFamily hF K j

/-- One-sided rejection is carry-only: no family-avoidance test is used. -/
theorem familySeparator_rejectedByCarry
    (F : Finset DecimalWord) (K : ℕ) {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T51.CarryAccepted (T41.balancedContext (T50.familyLevel K))
      (familyResidual F K v).carry (T50.familySeparator K u) := by
  simpa [familyResidual, T52.familyResidualOf, T50.familyResidual,
    T51.zeroPackage] using
    (T51.package_separator_rejectedByCarry T51.zeroPackage K huv)

theorem familySeparator_rejectedForFamily
    (F : Finset DecimalWord) (K : ℕ) {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T52.AcceptedForFamily F (T41.balancedContext (T50.familyLevel K))
      (familyResidual F K v) (T50.familySeparator K u) := by
  intro haccepted
  exact familySeparator_rejectedByCarry F K huv haccepted.1

/-- Explicit carry-only oriented separators for all distinct witness pairs. -/
theorem safe12Family_carryOnly_oneSidedSeparators
    (F : Finset DecimalWord) (hF : Safe12Family F) (K : ℕ) :
    Function.Injective (familyResidual F K) ∧
      (∀ j, T52.PersistentReachableAt F (T50.familyLevel K)
        (familyResidual F K j)) ∧
      ∀ u v, u ≠ v →
        T46.TailLegal (T50.familyLevel K) (T50.familySeparator K u) ∧
        T52.AcceptedForFamily F (T41.balancedContext (T50.familyLevel K))
          (familyResidual F K u) (T50.familySeparator K u) ∧
        ¬ T51.CarryAccepted (T41.balancedContext (T50.familyLevel K))
          (familyResidual F K v).carry (T50.familySeparator K u) := by
  refine ⟨familyResidual_injective F K, family_persistentReachableAt hF K, ?_⟩
  intro u v huv
  exact ⟨T50.familySeparator_tailLegal K u,
    familySeparator_acceptedForFamily hF K u,
    familySeparator_rejectedByCarry F K huv⟩

theorem family_pairwise_rightLanguage_inequivalent
    {F : Finset DecimalWord} (hF : Safe12Family F)
    (K : ℕ) {u v : Fin (K + 1)} (huv : u ≠ v) :
    ¬ T52.RightLanguageEquivalentAt F (T50.familyLevel K)
      (familyResidual F K u) (familyResidual F K v) := by
  intro hequiv
  have hu : T50.familySeparator K u ∈
      T52.ContinuationLanguageAt F (T50.familyLevel K)
        (familyResidual F K u) :=
    ⟨T50.familySeparator_tailLegal K u,
      familySeparator_acceptedForFamily hF K u⟩
  have hv : T50.familySeparator K u ∈
      T52.ContinuationLanguageAt F (T50.familyLevel K)
        (familyResidual F K v) := by
    rw [← hequiv]
    exact hu
  exact familySeparator_rejectedForFamily F K huv hv.2

/-- Every `K` has `K+1` pairwise language-distinct reachable residuals at one
common external level. -/
theorem safe12Family_commonLevel_moreThan_pairwise_inequivalent
    (F : Finset DecimalWord) (hF : Safe12Family F) (K : ℕ) :
    ∃ N : ℕ, ∃ f : Fin (K + 1) → T52.FamilyResidualState F,
      K < Fintype.card (Fin (K + 1)) ∧ Function.Injective f ∧
      (∀ j, T52.PersistentReachableAt F N (f j)) ∧
      ∀ u v, u ≠ v → ¬ T52.RightLanguageEquivalentAt F N (f u) (f v) := by
  exact ⟨T50.familyLevel K, familyResidual F K, by simp,
    familyResidual_injective F K, family_persistentReachableAt hF K,
    fun _ _ huv => family_pairwise_rightLanguage_inequivalent hF K huv⟩

/-- Every finite nonempty safe-12 family has infinite externally clocked
continuation-language index. -/
theorem safe12Family_infiniteContinuationLanguageIndex
    (F : Finset DecimalWord) (hF : Safe12Family F) :
    T52.InfiniteContinuationLanguageIndex F := by
  intro K
  exact safe12Family_commonLevel_moreThan_pairwise_inequivalent F hF K

/-- No finite persistent-state code preserves all exact family languages in
the fixed-safe-alphabet class. -/
theorem safe12Family_no_finite_languagePreserving_persistentStateCode
    (F : Finset DecimalWord) (hF : Safe12Family F)
    {Q : Type*} [Finite Q] (code : T52.FamilyResidualState F → Q) :
    ¬ T52.LanguagePreservingPersistentStateCode F code := by
  classical
  letI := Fintype.ofFinite Q
  let K := Fintype.card Q
  obtain ⟨N, f, hcard, _hinjective, hreachable, hinequivalent⟩ :=
    safe12Family_infiniteContinuationLanguageIndex F hF K
  let coded : Fin (K + 1) → Q := fun j => code (f j)
  obtain ⟨u, v, huv, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt coded hcard
  intro hpreserves
  have hequiv := hpreserves N (f u) (f v) (hreachable u) (hreachable v) (by
    simpa [coded] using hcode)
  exact hinequivalent u v huv hequiv

/-- The concrete family requested by T53. -/
def zeroThreeFamily : Finset DecimalWord :=
  {[(0 : Fin 10)], [(3 : Fin 10)]}

theorem zeroThreeFamily_safe12 : Safe12Family zeroThreeFamily := by
  constructor
  · simp [zeroThreeFamily]
  constructor
  · intro w hw
    simp only [zeroThreeFamily, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp
  · intro w hw
    simp only [zeroThreeFamily, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp, by decide, by decide⟩
    · exact ⟨3, by simp, by decide, by decide⟩

/-- The words `[0]` and `[3]` have no digit common to both, so this corollary
is genuinely outside T52's common-digit hypothesis. -/
theorem zeroThreeFamily_hasNoCommonDigit :
    ¬ T52.HasCommonDigit zeroThreeFamily := by
  rintro ⟨d, hd⟩
  have h0 : d = (0 : Fin 10) := by
    simpa using hd [(0 : Fin 10)] (by simp [zeroThreeFamily])
  have h3 : d = (3 : Fin 10) := by
    simpa using hd [(3 : Fin 10)] (by simp [zeroThreeFamily])
  rw [h0] at h3
  have hval := congrArg Fin.val h3
  norm_num at hval

theorem zeroThreeFamily_infiniteContinuationLanguageIndex :
    T52.InfiniteContinuationLanguageIndex zeroThreeFamily :=
  safe12Family_infiniteContinuationLanguageIndex zeroThreeFamily
    zeroThreeFamily_safe12

/-- The concrete extension beyond common-digit families, with the absence of
a common digit included in the corollary itself. -/
theorem zeroThreeFamily_noCommonDigit_infiniteIndex :
    Safe12Family zeroThreeFamily ∧
      ¬ T52.HasCommonDigit zeroThreeFamily ∧
      T52.InfiniteContinuationLanguageIndex zeroThreeFamily :=
  ⟨zeroThreeFamily_safe12, zeroThreeFamily_hasNoCommonDigit,
    zeroThreeFamily_infiniteContinuationLanguageIndex⟩

theorem zeroThreeFamily_no_finite_languagePreserving_persistentStateCode
    {Q : Type*} [Finite Q]
    (code : T52.FamilyResidualState zeroThreeFamily → Q) :
    ¬ T52.LanguagePreservingPersistentStateCode zeroThreeFamily code :=
  safe12Family_no_finite_languagePreserving_persistentStateCode
    zeroThreeFamily zeroThreeFamily_safe12 code

end

end Theory.PiDigits.T53

#print axioms Theory.PiDigits.T53.backgroundMarkerWord_safe12
#print axioms Theory.PiDigits.T53.familySource_safe12
#print axioms Theory.PiDigits.T53.familySeparator_safe12
#print axioms Theory.PiDigits.T53.family_fullSourceContinuation_avoidsFamily
#print axioms Theory.PiDigits.T53.familySeparator_acceptedForFamily
#print axioms Theory.PiDigits.T53.familySeparator_rejectedByCarry
#print axioms Theory.PiDigits.T53.safe12Family_carryOnly_oneSidedSeparators
#print axioms Theory.PiDigits.T53.safe12Family_commonLevel_moreThan_pairwise_inequivalent
#print axioms Theory.PiDigits.T53.safe12Family_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T53.safe12Family_no_finite_languagePreserving_persistentStateCode
#print axioms Theory.PiDigits.T53.zeroThreeFamily_safe12
#print axioms Theory.PiDigits.T53.zeroThreeFamily_hasNoCommonDigit
#print axioms Theory.PiDigits.T53.zeroThreeFamily_infiniteContinuationLanguageIndex
#print axioms Theory.PiDigits.T53.zeroThreeFamily_noCommonDigit_infiniteIndex
#print axioms Theory.PiDigits.T53.zeroThreeFamily_no_finite_languagePreserving_persistentStateCode
