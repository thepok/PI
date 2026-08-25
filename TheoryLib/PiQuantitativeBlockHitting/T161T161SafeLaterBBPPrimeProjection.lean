import TheoryLib.PiQuantitativeBlockHitting.T159T159ExactBBPTopPrimeProjection

/-!
# T161: terminal-prime projection across the safe later-depth block

For a prime entering through the terminal first or third pole at index `7*m`,
the same pole remains the unique pole divisible by that prime throughout the
maximal elementary safe block of later sevenfold BBP truncations.  The generic
T159 projection machinery then gives the exact local residue and valuation of
the actual scaled sampled BBP rational at every safe depth.

This is four-pole BBP arithmetic with sevenfold sampling.  It supplies no
primitive-frequency cancellation, distribution statement, or V1 conclusion.
-/

noncomputable section

namespace Theory.PiDigits.T161SafeLaterBBPPrimeProjection

open Theory.PiDigits.T159ExactBBPTopPrimeProjection
open Theory.PiDigits.T115SampledBBPCellDefectPhase

private lemma caseOne_poleOne_dvd_iff
    (m t p j : ℕ) (hm : 1 ≤ m) (ht : t ≤ 4 * m - 1)
    (hpdef : p = 56 * m + 1) (hj : j ≤ 7 * t) :
    p ∣ 8 * j + 1 ↔ j = 7 * m := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hp0 : 0 < p := by omega
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hdlt : 8 * j + 1 < 4 * p := by omega
    have hclt : c < 4 := by nlinarith
    interval_cases c <;> omega
  · rintro rfl
    rw [show 8 * (7 * m) + 1 = p by omega]

private lemma caseOne_poleThree_not_dvd
    (m t p j : ℕ) (hm : 1 ≤ m) (ht : t ≤ 4 * m - 1)
    (hpdef : p = 56 * m + 1) (hj : j ≤ 7 * t) :
    ¬ p ∣ 8 * j + 5 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hp0 : 0 < p := by omega
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hdlt : 8 * j + 5 < 4 * p := by omega
  have hclt : c < 4 := by nlinarith
  interval_cases c
  all_goals omega

private lemma caseOne_poleTwo_not_dvd
    (m t p j : ℕ) (hm : 1 ≤ m) (ht : t ≤ 4 * m - 1)
    (hpdef : p = 56 * m + 1) (hj : j ≤ 7 * t) :
    ¬ p ∣ 2 * j + 1 := by
  intro hd
  have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) hd
  omega

private lemma caseOne_poleFour_not_dvd
    (m t p j : ℕ) (hm : 1 ≤ m) (ht : t ≤ 4 * m - 1)
    (hpdef : p = 56 * m + 1) (hj : j ≤ 7 * t) :
    ¬ p ∣ 4 * j + 3 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hp0 : 0 < p := by omega
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hdlt : 4 * j + 3 < 2 * p := by omega
  have hclt : c < 2 := by nlinarith
  interval_cases c
  omega

private lemma caseThree_poleThree_dvd_iff
    (m t p j : ℕ) (ht : t ≤ 4 * m)
    (hpdef : p = 56 * m + 5) (hj : j ≤ 7 * t) :
    p ∣ 8 * j + 5 ↔ j = 7 * m := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have hp0 : 0 < p := by omega
    have hc0 : 0 < c := by
      by_contra h
      have : c = 0 := by omega
      subst c
      simp at hc
    have hdlt : 8 * j + 5 < 4 * p := by omega
    have hclt : c < 4 := by nlinarith
    interval_cases c <;> omega
  · rintro rfl
    rw [show 8 * (7 * m) + 5 = p by omega]

private lemma caseThree_poleOne_not_dvd
    (m t p j : ℕ) (ht : t ≤ 4 * m)
    (hpdef : p = 56 * m + 5) (hj : j ≤ 7 * t) :
    ¬ p ∣ 8 * j + 1 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hp0 : 0 < p := by omega
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hdlt : 8 * j + 1 < 4 * p := by omega
  have hclt : c < 4 := by nlinarith
  interval_cases c <;> omega

private lemma caseThree_poleTwo_not_dvd
    (m t p j : ℕ) (ht : t ≤ 4 * m)
    (hpdef : p = 56 * m + 5) (hj : j ≤ 7 * t) :
    ¬ p ∣ 2 * j + 1 := by
  intro hd
  have hle := Nat.le_of_dvd (by omega : 0 < 2 * j + 1) hd
  omega

private lemma caseThree_poleFour_not_dvd
    (m t p j : ℕ) (ht : t ≤ 4 * m)
    (hpdef : p = 56 * m + 5) (hj : j ≤ 7 * t) :
    ¬ p ∣ 4 * j + 3 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hp0 : 0 < p := by omega
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := by omega
    subst c
    simp at hc
  have hdlt : 4 * j + 3 < 2 * p := by omega
  have hclt : c < 2 := by nlinarith
  interval_cases c
  omega

/-- In case I, throughout `m ≤ t ≤ 4*m-1`, the terminal denominator
`8*(7*m)+1 = p` is the only `p`-divisible denominator among all four BBP pole
families at indices at most `7*t`. -/
theorem caseOne_unique_terminal_pole
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m - 1)
    (hpdef : p = 56 * m + 1) :
    5 < p ∧ 7 * m ≤ 7 * t ∧
    (∀ j ≤ 7 * t, p ∣ 8 * j + 1 ↔ j = 7 * m) ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 5) ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) := by
  exact ⟨by omega, by omega,
    fun j hj ↦ caseOne_poleOne_dvd_iff m t p j hm ht hpdef hj,
    fun j hj ↦ caseOne_poleTwo_not_dvd m t p j hm ht hpdef hj,
    fun j hj ↦ caseOne_poleThree_not_dvd m t p j hm ht hpdef hj,
    fun j hj ↦ caseOne_poleFour_not_dvd m t p j hm ht hpdef hj⟩

/-- In case III, throughout `m ≤ t ≤ 4*m`, the terminal denominator
`8*(7*m)+5 = p` is the only `p`-divisible denominator among all four BBP pole
families at indices at most `7*t`. -/
theorem caseThree_unique_terminal_pole
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m)
    (hpdef : p = 56 * m + 5) :
    5 < p ∧ 7 * m ≤ 7 * t ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 8 * j + 1) ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 2 * j + 1) ∧
    (∀ j ≤ 7 * t, p ∣ 8 * j + 5 ↔ j = 7 * m) ∧
    (∀ j ≤ 7 * t, ¬ p ∣ 4 * j + 3) := by
  exact ⟨by omega, by omega,
    fun j hj ↦ caseThree_poleOne_not_dvd m t p j ht hpdef hj,
    fun j hj ↦ caseThree_poleTwo_not_dvd m t p j ht hpdef hj,
    fun j hj ↦ caseThree_poleThree_dvd_iff m t p j ht hpdef hj,
    fun j hj ↦ caseThree_poleFour_not_dvd m t p j ht hpdef hj⟩

/-- Exact case-I projection of the actual scaled sampled BBP rational at every
safe later depth. -/
theorem scaledBBPRat_safeLaterProjection_one
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m - 1)
    (hp : p.Prime) (hpdef : p = 56 * m + 1) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat t) (4 * (10 : ℚ) ^ t) := by
  rcases caseOne_unique_terminal_pole m t p hm hmt ht hpdef with
    ⟨hpgt, hi, hone, htwo, hthree, hfour⟩
  apply scaledBBPRat_primeProjection_one_of_unique
      t (7 * m) p hp hpgt hi (by omega)
  · intro j hj hne
    exact (hone j hj).not.mpr hne
  · exact htwo
  · exact hthree
  · exact hfour

/-- Exact case-III projection of the actual scaled sampled BBP rational at
every safe later depth. -/
theorem scaledBBPRat_safeLaterProjection_three
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m)
    (hp : p.Prime) (hpdef : p = 56 * m + 5) :
    PrimeCongruent p ((p : ℚ) * scaledBBPRat t) (4 * (10 : ℚ) ^ t) := by
  rcases caseThree_unique_terminal_pole m t p hm hmt ht hpdef with
    ⟨hpgt, hi, hone, htwo, hthree, hfour⟩
  apply scaledBBPRat_primeProjection_three_of_unique
      t (7 * m) p hp hpgt hi (by omega)
  · exact hone
  · exact htwo
  · intro j hj hne
    exact (hthree j hj).not.mpr hne
  · exact hfour

/-- The case-I terminal prime has exact valuation `-1` throughout its safe
later-depth block. -/
theorem scaledBBPRat_safeLaterVal_one
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m - 1)
    (hp : p.Prime) (hpdef : p = 56 * m + 1) :
    padicValRat p (scaledBBPRat t) = -1 := by
  exact scaledBBPRat_val_eq_neg_one_of_projection t p hp (by omega)
    (scaledBBPRat_safeLaterProjection_one m t p hm hmt ht hp hpdef)

/-- The case-III terminal prime has exact valuation `-1` throughout its safe
later-depth block. -/
theorem scaledBBPRat_safeLaterVal_three
    (m t p : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (ht : t ≤ 4 * m)
    (hp : p.Prime) (hpdef : p = 56 * m + 5) :
    padicValRat p (scaledBBPRat t) = -1 := by
  exact scaledBBPRat_val_eq_neg_one_of_projection t p hp (by omega)
    (scaledBBPRat_safeLaterProjection_three m t p hm hmt ht hp hpdef)

end Theory.PiDigits.T161SafeLaterBBPPrimeProjection

#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.caseOne_unique_terminal_pole
#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.caseThree_unique_terminal_pole
#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.scaledBBPRat_safeLaterProjection_one
#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.scaledBBPRat_safeLaterProjection_three
#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.scaledBBPRat_safeLaterVal_one
#print axioms Theory.PiDigits.T161SafeLaterBBPPrimeProjection.scaledBBPRat_safeLaterVal_three
