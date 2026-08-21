import TheoryLib.PiDigits.T7Statements

/-
This file concerns sibling V3, not canonical V1.

Source: problems/local/pi-digits.txt
SHA-256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
-/

namespace Theory.PiDigits.V3Reduction

/-- Every infinite decimal stream embeds at strictly increasing positions in `x`. -/
def EveryStreamIsSubsequence (x : ℕ → Fin 10) : Prop :=
  ∀ s : ℕ → Fin 10, ∃ positions : ℕ → ℕ,
    StrictMono positions ∧ ∀ i : ℕ, x (positions i) = s i

/-- Every decimal digit occurs in `x` at or after every requested position. -/
def EveryDigitOccursArbitrarilyLate (x : ℕ → Fin 10) : Prop :=
  ∀ d : Fin 10, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ x n = d

noncomputable def selectedPositions
    (x : ℕ → Fin 10) (h : EveryDigitOccursArbitrarilyLate x)
    (s : ℕ → Fin 10) : ℕ → ℕ
  | 0 => Classical.choose (h (s 0) 0)
  | n + 1 =>
      Classical.choose (h (s (n + 1)) (selectedPositions x h s n + 1))

theorem selectedPositions_matches
    (x : ℕ → Fin 10) (h : EveryDigitOccursArbitrarilyLate x)
    (s : ℕ → Fin 10) (n : ℕ) :
    x (selectedPositions x h s n) = s n := by
  cases n with
  | zero =>
      exact (Classical.choose_spec (h (s 0) 0)).2
  | succ n =>
      exact
        (Classical.choose_spec
          (h (s (n + 1)) (selectedPositions x h s n + 1))).2

theorem selectedPositions_strictMono
    (x : ℕ → Fin 10) (h : EveryDigitOccursArbitrarilyLate x)
    (s : ℕ → Fin 10) :
    StrictMono (selectedPositions x h s) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hnext :=
    (Classical.choose_spec
      (h (s (n + 1)) (selectedPositions x h s n + 1))).1
  exact Nat.lt_of_succ_le hnext

theorem everyDigitOccursArbitrarilyLate_of_everyStreamIsSubsequence
    (x : ℕ → Fin 10) (h : EveryStreamIsSubsequence x) :
    EveryDigitOccursArbitrarilyLate x := by
  intro d N
  obtain ⟨positions, hpositions, hmatches⟩ := h (fun _ => d)
  refine ⟨positions N, StrictMono.id_le hpositions N, ?_⟩
  simpa using hmatches N

theorem everyStreamIsSubsequence_of_everyDigitOccursArbitrarilyLate
    (x : ℕ → Fin 10) (h : EveryDigitOccursArbitrarilyLate x) :
    EveryStreamIsSubsequence x := by
  intro s
  exact
    ⟨selectedPositions x h s, selectedPositions_strictMono x h s,
      selectedPositions_matches x h s⟩

theorem everyStreamIsSubsequence_iff_everyDigitOccursArbitrarilyLate
    (x : ℕ → Fin 10) :
    EveryStreamIsSubsequence x ↔ EveryDigitOccursArbitrarilyLate x := by
  constructor
  · exact everyDigitOccursArbitrarilyLate_of_everyStreamIsSubsequence x
  · exact everyStreamIsSubsequence_of_everyDigitOccursArbitrarilyLate x

/-- Sibling V3 implies arbitrarily late occurrences of every decimal digit. -/
theorem siblingV3_implies_everyDigitOccursArbitrarilyLate
    (h : Theory.PiDigits.V3) :
    ∀ d : Fin 10, ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ Theory.PiDigits.piDigit n = d := by
  apply everyDigitOccursArbitrarilyLate_of_everyStreamIsSubsequence
  exact h

/-- Arbitrarily late occurrences of every digit imply sibling V3. -/
theorem everyDigitOccursArbitrarilyLate_implies_siblingV3
    (h : ∀ d : Fin 10, ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ Theory.PiDigits.piDigit n = d) :
    Theory.PiDigits.V3 := by
  apply everyStreamIsSubsequence_of_everyDigitOccursArbitrarilyLate
  exact h

/--
Exact reduction of T7's sibling V3 proposition, not canonical V1, to an
explicit arbitrarily-late-occurrence statement for all decimal digits.
-/
theorem siblingV3_iff_everyDigitOccursArbitrarilyLate :
    Theory.PiDigits.V3 ↔
      ∀ d : Fin 10, ∀ N : ℕ, ∃ n : ℕ,
        N ≤ n ∧ Theory.PiDigits.piDigit n = d := by
  constructor
  · exact siblingV3_implies_everyDigitOccursArbitrarilyLate
  · exact everyDigitOccursArbitrarilyLate_implies_siblingV3

end Theory.PiDigits.V3Reduction
