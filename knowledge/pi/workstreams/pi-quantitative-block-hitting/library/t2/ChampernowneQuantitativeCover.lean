import TheoryLib.PiDigits.T22ChampernowneDisjunctive
import TheoryLib.PiDigits.T23ChampernowneEpochDiscrepancy
import TheoryLib.PiDigits.T24ChampernownePrefixDiscrepancy
import TheoryLib.PiDigits.T25ChampernowneNormality

/-!
# Explicit quantitative word coverage for the Champernowne stream

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file proves the requested solved analogue for T22's artificial
Champernowne stream. It proves nothing about the decimal digits of pi.

The proof is finite and constructive. For a word `w`, T22 encodes `1 :: w` as
one positive integer. We bound the total length of all preceding integer
blocks directly; no normality theorem, limit, or asymptotic premise is used.
-/

namespace Theory.PiDigits.QuantitativeChampernowneCover

open Theory.PiDigits.T21 Theory.PiDigits.T22

/-- The explicit uniform Champernowne cover constant. -/
def C_Ch : ℕ := 22

theorem C_Ch_ge_one : 1 ≤ C_Ch := by
  norm_num [C_Ch]

/-- If each of the first `n` blocks has length at most `M`, their finite
concatenation has length at most `n * M`. -/
theorem finiteConcat_length_le_mul {α : Type*} (blocks : ℕ → List α)
    (n M : ℕ) (hblocks : ∀ j < n, (blocks j).length ≤ M) :
    (finiteConcat blocks n).length ≤ n * M := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finiteConcat_succ, List.length_append]
      have hprev := ih (fun j hj => hblocks j (by omega))
      have hlast := hblocks n (by omega)
      simpa [Nat.add_mul] using Nat.add_le_add hprev hlast

/-- The leading-`1` encoding of a length-`k` word is below `10^(k+1)`. -/
theorem prefixedValue_lt_ten_pow_length_succ (w : List (Fin 10)) :
    prefixedValue w < 10 ^ (w.length + 1) := by
  have h := Nat.ofDigits_lt_base_pow_length
    (b := 10) (l := ((1 :: w).map Fin.val).reverse) (by norm_num)
    (by
      intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt)
  simpa [prefixedValue] using h

/-- A number below `10^m` has at most `m` ordinary decimal digits. -/
theorem decimalDigits_length_le_of_lt_ten_pow {n m : ℕ}
    (hn : n < 10 ^ m) :
    (decimalDigits n).length ≤ m := by
  simpa [decimalDigits] using
    (Nat.digits_length_le_iff (by norm_num : 1 < (10 : ℕ)) n).mpr hn

/-- T22's leading-`1` construction, with its exact start exposed publicly. -/
theorem prefixedWord_occursAt_exactStart (w : List (Fin 10)) :
    WordOccursAt champernowneDigit w
      ((finiteConcat champernowneBlocks (prefixedValue w - 1)).length + 1) := by
  let v := prefixedValue w
  let b := v - 1
  have hvpos : 0 < v := by
    exact prefixedValue_pos w
  have hb : b + 1 = v := by
    dsimp [b]
    omega
  have hblock : champernowneBlocks b = 1 :: w := by
    unfold champernowneBlocks
    rw [hb]
    exact decimalDigits_prefixedValue w
  let offset := (finiteConcat champernowneBlocks b).length
  intro i hi
  have hj : i + 1 < (champernowneBlocks b).length := by
    rw [hblock, List.length_cons]
    omega
  have hcoverage := enumeratedBlock_occursAt_concatStream
    champernowneBlocks champernowneBlocks_ne_nil b (i + 1) hj
  change concatStream champernowneBlocks ((offset + 1) + i) = w[i]
  rw [show (offset + 1) + i = offset + (i + 1) by omega]
  rw [hcoverage]
  have hget := congrArg (fun l : List (Fin 10) => l[i + 1]?) hblock
  simp [hi] at hget
  rw [List.getElem?_eq_getElem hj] at hget
  exact Option.some.inj hget

/-- Every positive-length decimal word, including every leading-zero word, is
fully contained in the first `C_Ch * k * 10^k` Champernowne digits. -/
theorem champernowne_uniform_full_containment
    (k : ℕ) (hk : 1 ≤ k) (w : List (Fin 10)) (hw : w.length = k) :
    ∃ n : ℕ, n + k ≤ C_Ch * k * 10 ^ k ∧
      WordOccursAt champernowneDigit w n := by
  let v := prefixedValue w
  let b := v - 1
  let offset := (finiteConcat champernowneBlocks b).length
  let n := offset + 1
  have hvpos : 0 < v := by
    exact prefixedValue_pos w
  have hb_lt_v : b < v := by
    dsimp [b]
    omega
  have hvpow : v < 10 ^ (k + 1) := by
    dsimp [v]
    simpa [hw] using prefixedValue_lt_ten_pow_length_succ w
  have hblockLengths :
      ∀ j < b, (champernowneBlocks j).length ≤ k + 1 := by
    intro j hj
    apply decimalDigits_length_le_of_lt_ten_pow
    exact (show j + 1 < v by omega).trans hvpow
  have hoffset : offset ≤ b * (k + 1) := by
    exact finiteConcat_length_le_mul champernowneBlocks b (k + 1) hblockLengths
  have hbpow : b ≤ 10 ^ (k + 1) := by
    omega
  have hoffsetScale : offset ≤ 20 * k * 10 ^ k := by
    calc
      offset ≤ b * (k + 1) := hoffset
      _ ≤ 10 ^ (k + 1) * (k + 1) := Nat.mul_le_mul_right (k + 1) hbpow
      _ = (10 ^ k * 10) * (k + 1) := by rw [pow_succ]
      _ ≤ (10 ^ k * 10) * (2 * k) := by
        gcongr
        omega
      _ = 20 * k * 10 ^ k := by ring
  have hextra : 1 + k ≤ 2 * k * 10 ^ k := by
    calc
      1 + k ≤ 2 * k := by omega
      _ ≤ 2 * k * 10 ^ k :=
        Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  have hoccurs : WordOccursAt champernowneDigit w n := by
    dsimp [n, offset, b, v]
    exact prefixedWord_occursAt_exactStart w
  refine ⟨n, ?_, hoccurs⟩
  calc
    n + k = offset + (1 + k) := by simp [n]; omega
    _ ≤ 20 * k * 10 ^ k + 2 * k * 10 ^ k :=
      Nat.add_le_add hoffsetScale hextra
    _ = C_Ch * k * 10 ^ k := by norm_num [C_Ch]; ring

/-- Hostile-review surface: the numeral, all quantifiers, list-length
condition, full-containment deadline, and contiguous occurrence are explicit.
No restriction excludes a list whose first digit is zero. -/
theorem champernowne_explicit_22_cover :
    (1 : ℕ) ≤ 22 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ w : List (Fin 10), w.length = k →
        ∃ n : ℕ, n + k ≤ 22 * k * 10 ^ k ∧
          WordOccursAt champernowneDigit w n := by
  constructor
  · norm_num
  · intro k hk w hw
    simpa [C_Ch] using champernowne_uniform_full_containment k hk w hw

end Theory.PiDigits.QuantitativeChampernowneCover

#print axioms Theory.PiDigits.QuantitativeChampernowneCover.finiteConcat_length_le_mul
#print axioms Theory.PiDigits.QuantitativeChampernowneCover.prefixedValue_lt_ten_pow_length_succ
#print axioms Theory.PiDigits.QuantitativeChampernowneCover.decimalDigits_length_le_of_lt_ten_pow
#print axioms Theory.PiDigits.QuantitativeChampernowneCover.prefixedWord_occursAt_exactStart
#print axioms Theory.PiDigits.QuantitativeChampernowneCover.champernowne_uniform_full_containment
#print axioms Theory.PiDigits.QuantitativeChampernowneCover.champernowne_explicit_22_cover
