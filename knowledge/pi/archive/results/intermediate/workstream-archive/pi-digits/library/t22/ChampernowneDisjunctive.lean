import Mathlib.Data.Nat.Digits.Lemmas
import TheoryLib.PiDigits.T21PiDigitsV1V3Relationship

/-!
# T22: a constructive solved analogue using the Champernowne stream

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file concerns only the artificial stream obtained by concatenating the
ordinary decimal representations of the positive natural numbers:
`123456789101112...`. It proves nothing about the decimal digits of pi,
canonical V1 for pi, or sibling V3.

The universal theorem below quantifies over all finite lists of `Fin 10`,
including the empty list. A separate corollary makes leading-zero coverage
explicit: such a word is embedded after the initial `1` in a positive
integer's decimal representation.
-/

namespace Theory.PiDigits.T22

open Theory.PiDigits.T21

/-- The concatenation of the first `k` blocks. -/
def finiteConcat {α : Type*} (blocks : ℕ → List α) : ℕ → List α
  | 0 => []
  | k + 1 => finiteConcat blocks k ++ blocks k

@[simp]
theorem finiteConcat_zero {α : Type*} (blocks : ℕ → List α) :
    finiteConcat blocks 0 = [] := rfl

@[simp]
theorem finiteConcat_succ {α : Type*} (blocks : ℕ → List α) (k : ℕ) :
    finiteConcat blocks (k + 1) = finiteConcat blocks k ++ blocks k := rfl

/-- Splitting a finite concatenation after its first `m` blocks. -/
theorem finiteConcat_add {α : Type*} (blocks : ℕ → List α) (m n : ℕ) :
    finiteConcat blocks (m + n) =
      finiteConcat blocks m ++ finiteConcat (fun k => blocks (m + k)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, finiteConcat_succ, finiteConcat_succ, ih]
      simp only [List.append_assoc]

/-- Nonempty blocks make the first `k` blocks contain at least `k` entries. -/
theorem index_le_finiteConcat_length {α : Type*} (blocks : ℕ → List α)
    (hne : ∀ k, blocks k ≠ []) (k : ℕ) :
    k ≤ (finiteConcat blocks k).length := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteConcat_succ, List.length_append]
      cases hblock : blocks k with
      | nil => exact (hne k hblock).elim
      | cons a l =>
          rw [List.length_cons]
          omega

/--
The infinite concatenation of nonempty finite blocks. At index `n`, the first
`n + 1` blocks are already long enough, so `getI` never uses its default.
-/
def concatStream {α : Type*} [Inhabited α] (blocks : ℕ → List α) (n : ℕ) : α :=
  (finiteConcat blocks (n + 1)).getI n

/-- Reusable coverage: every enumerated block occurs at its cumulative offset. -/
theorem enumeratedBlock_occursAt_concatStream {α : Type*} [Inhabited α]
    (blocks : ℕ → List α) (hne : ∀ k, blocks k ≠ []) (k : ℕ) :
    ∀ i : ℕ, ∀ hi : i < (blocks k).length,
      concatStream blocks ((finiteConcat blocks k).length + i) = (blocks k)[i] := by
  intro i hi
  let offset := (finiteConcat blocks k).length
  have hkoffset : k ≤ offset := index_le_finiteConcat_length blocks hne k
  have hcount : offset + i + 1 =
      (k + 1) + ((offset + i + 1) - (k + 1)) := by
    omega
  have hinside : offset + i < (finiteConcat blocks (k + 1)).length := by
    rw [finiteConcat_succ, List.length_append]
    exact Nat.add_lt_add_left hi offset
  unfold concatStream
  change (finiteConcat blocks (offset + i + 1)).getI (offset + i) = _
  rw [hcount, finiteConcat_add]
  rw [List.getI_append _ _ _ hinside]
  rw [finiteConcat_succ]
  rw [List.getI_append_right]
  · rw [Nat.add_sub_cancel_left, List.getI_eq_getElem _ hi]
  · exact Nat.le_add_right offset i

/-- Coerce a natural number to its residue decimal digit. -/
def digitOfNat (n : ℕ) : Fin 10 :=
  ⟨n % 10, Nat.mod_lt _ (by norm_num)⟩

@[simp]
theorem digitOfNat_val (d : Fin 10) : digitOfNat d.val = d := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt d.isLt

/-- The usual most-significant-first base-10 representation of `n`. -/
def decimalDigits (n : ℕ) : List (Fin 10) :=
  (Nat.digits 10 n).reverse.map digitOfNat

/-- The `k`th Champernowne block is the representation of `k + 1`. -/
def champernowneBlocks (k : ℕ) : List (Fin 10) :=
  decimalDigits (k + 1)

theorem champernowneBlocks_ne_nil (k : ℕ) : champernowneBlocks k ≠ [] := by
  simp [champernowneBlocks, decimalDigits]

/-- The decimal Champernowne digit stream `123456789101112...`. -/
def champernowneDigit : ℕ → Fin 10 :=
  concatStream champernowneBlocks

/-- Encode a digit word after a leading `1`, preventing loss of leading zeros. -/
def prefixedValue (w : List (Fin 10)) : ℕ :=
  Nat.ofDigits 10 ((1 :: w).map Fin.val).reverse

/-- The standard decimal representation of `prefixedValue w` is exactly `1 :: w`. -/
theorem decimalDigits_prefixedValue (w : List (Fin 10)) :
    decimalDigits (prefixedValue w) = 1 :: w := by
  have hdigits : Nat.digits 10 (prefixedValue w) =
      ((1 :: w).map Fin.val).reverse := by
    unfold prefixedValue
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro d hd
      rw [List.mem_reverse] at hd
      simp only [List.mem_map] at hd
      obtain ⟨d, _, rfl⟩ := hd
      exact d.isLt
    · intro hne
      simp
  unfold decimalDigits
  rw [hdigits]
  rw [List.reverse_reverse, List.map_map, List.map_cons]
  congr 1
  calc
    List.map (digitOfNat ∘ Fin.val) w = List.map id w := by
      apply List.map_congr_left
      intro d hd
      exact digitOfNat_val d
    _ = w := List.map_id w

/-- The encoding used for an arbitrary word is a positive natural number. -/
theorem prefixedValue_pos (w : List (Fin 10)) : 0 < prefixedValue w := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hrepr := decimalDigits_prefixedValue w
  rw [hzero] at hrepr
  simp [decimalDigits] at hrepr

/-- Every finite decimal word occurs contiguously in the Champernowne stream. -/
theorem champernowne_everyFiniteDecimalWord :
    ∀ w : List (Fin 10), ∃ n : ℕ, WordOccursAt champernowneDigit w n := by
  intro w
  let v := prefixedValue w
  let k := v - 1
  have hvpos : 0 < v := prefixedValue_pos w
  have hk : k + 1 = v := by
    dsimp [k]
    omega
  have hblock : champernowneBlocks k = 1 :: w := by
    unfold champernowneBlocks
    rw [hk]
    exact decimalDigits_prefixedValue w
  let offset := (finiteConcat champernowneBlocks k).length
  refine ⟨offset + 1, ?_⟩
  intro i hi
  have hj : i + 1 < (champernowneBlocks k).length := by
    rw [hblock, List.length_cons]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    champernowneBlocks champernowneBlocks_ne_nil k (i + 1) hj
  change concatStream champernowneBlocks ((offset + 1) + i) = w[i]
  rw [show (offset + 1) + i = offset + (i + 1) by omega]
  rw [hcoverage]
  have hget := congrArg (fun l : List (Fin 10) => l[i + 1]?) hblock
  simp [hi] at hget
  rw [List.getElem?_eq_getElem hj] at hget
  exact Option.some.inj hget

/-- Leading-zero words are covered explicitly, not treated as numeral representations. -/
theorem champernowne_everyLeadingZeroWord (w : List (Fin 10)) :
    ∃ n : ℕ, WordOccursAt champernowneDigit ((0 : Fin 10) :: w) n := by
  exact champernowne_everyFiniteDecimalWord ((0 : Fin 10) :: w)

end Theory.PiDigits.T22

#print axioms Theory.PiDigits.T22.enumeratedBlock_occursAt_concatStream
#print axioms Theory.PiDigits.T22.decimalDigits_prefixedValue
#print axioms Theory.PiDigits.T22.champernowne_everyFiniteDecimalWord
#print axioms Theory.PiDigits.T22.champernowne_everyLeadingZeroWord
