import Mathlib

/-
Source: problems/local/pi-digits.txt
SHA-256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825

Line correspondence:
* V1 is source line 25: every finite digit string occurs contiguously.
* V2 is source lines 27-28: every infinite digit stream is a tail.
* V3 is source lines 34-35: every infinite digit stream is a subsequence.
-/
namespace Theory.PiDigits

/-- The `n`th digit after the decimal point of `Real.pi`, indexed from zero. -/
noncomputable def piDigit (n : ℕ) : Fin 10 :=
  ⟨⌊Real.pi * (10 : ℝ) ^ (n + 1)⌋₊ % 10, Nat.mod_lt _ (by norm_num)⟩

/-- V1 (canonical): every finite decimal digit string occurs contiguously in pi. -/
def V1 : Prop :=
  ∀ s : List (Fin 10), ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
    piDigit (n + i) = s.get ⟨i, hi⟩

/-- V2 (sibling): every infinite decimal digit stream is a tail of pi. -/
def V2 : Prop :=
  ∀ s : ℕ → Fin 10, ∃ n : ℕ, ∀ i : ℕ, piDigit (n + i) = s i

/-- V3 (sibling): every infinite decimal digit stream is a subsequence of pi. -/
def V3 : Prop :=
  ∀ s : ℕ → Fin 10, ∃ positions : ℕ → ℕ,
    StrictMono positions ∧ ∀ i : ℕ, piDigit (positions i) = s i

#check V1
#check V2
#check V3

end Theory.PiDigits
