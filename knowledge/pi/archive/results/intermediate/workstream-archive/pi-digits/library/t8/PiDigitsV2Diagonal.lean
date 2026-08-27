import TheoryLib.PiDigits.T7Statements

/-
This file resolves only V2, the non-canonical infinite-tail sibling from
`problems/local/pi-digits.txt`. It gives no progress on V1, the canonical open
question about finite contiguous digit strings.

Source SHA-256:
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
-/

namespace Theory.PiDigits

/-- At index `k`, choose `1` if the `k`th digit of the tail beginning at `k`
is zero, and choose zero otherwise. -/
noncomputable def diagonalSequence (k : ℕ) : Fin 10 :=
  if piDigit (k + k) = 0 then 1 else 0

/-- The diagonal sequence differs at index `k` from the tail beginning at
`k`. -/
theorem diagonalSequence_ne_diagonal (k : ℕ) :
    diagonalSequence k ≠ piDigit (k + k) := by
  unfold diagonalSequence
  by_cases h : piDigit (k + k) = 0
  · simp [h]
  · simpa [h] using (Ne.symm h)

/-- The explicit diagonal sequence is unequal to every tail of the decimal
digit stream of pi. -/
theorem diagonalSequence_avoids_every_tail :
    ∀ n : ℕ, diagonalSequence ≠ fun i => piDigit (n + i) := by
  intro n h
  exact diagonalSequence_ne_diagonal n (congrFun h n)

/-- Exact negation of T7's V2. V2 is a non-canonical sibling statement, so
this theorem does not resolve or advance canonical V1. -/
theorem not_v2 : ¬ V2 := by
  intro hV2
  obtain ⟨n, hn⟩ := hV2 diagonalSequence
  apply diagonalSequence_avoids_every_tail n
  funext i
  exact (hn i).symm

end Theory.PiDigits
