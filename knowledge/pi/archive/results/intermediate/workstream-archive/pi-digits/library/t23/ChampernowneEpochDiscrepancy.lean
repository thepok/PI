import TheoryLib.PiDigits.T22ChampernowneDisjunctive

/-!
# T23: finite discrepancy at complete Champernowne epochs

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file concerns only the artificial decimal word obtained by concatenating
the positive integers having a fixed decimal length.  It proves an endpoint
estimate, not full Champernowne normality.  It proves nothing about pi,
canonical V1, or sibling variants V2 and V3.

The intended epoch parameter satisfies `1 ≤ m`, as it does in the main
theorem. Definitions are total on naturals; their value at `m = 0` is outside
the statement and is not asserted to enumerate zero-digit positive integers.
-/

namespace Theory.PiDigits.T23

open Theory.PiDigits.T22

/-- The possible nonzero leading decimal digits. -/
def leadingDigits : Finset ℕ := Finset.Icc 1 9

/-- A leading digit paired with an arbitrary fixed-length decimal tail. -/
noncomputable def mDigitDescriptors (m : ℕ) : Finset (ℕ × List ℕ) :=
  leadingDigits ×ˢ List.fixedLengthDigits (b := 10) (by norm_num) (m - 1)

/-- The decimal word represented by a descriptor. -/
def descriptorDigits (x : ℕ × List ℕ) : List (Fin 10) :=
  digitOfNat x.1 :: x.2.map digitOfNat

/-- The positive integer represented by a descriptor. -/
def descriptorValue (x : ℕ × List ℕ) : ℕ :=
  Nat.ofDigits 10 (x.1 :: x.2).reverse

private def descriptorLE (x y : ℕ × List ℕ) : Prop :=
  descriptorValue x < descriptorValue y ∨
    (descriptorValue x = descriptorValue y ∧ Encodable.encode x ≤ Encodable.encode y)

private instance : DecidableRel descriptorLE := by
  intro x y
  unfold descriptorLE
  infer_instance

private instance : IsTrans (ℕ × List ℕ) descriptorLE where
  trans a b c hab hbc := by
    rcases hab with hab | ⟨habv, habe⟩
    · rcases hbc with hbc | ⟨hbcv, hbce⟩
      · left; omega
      · left; omega
    · rcases hbc with hbc | ⟨hbcv, hbce⟩
      · left; omega
      · right
        exact ⟨habv.trans hbcv, le_trans habe hbce⟩

private instance : Std.Total descriptorLE where
  total a b := by
    rcases lt_trichotomy (descriptorValue a) (descriptorValue b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (Encodable.encode a) (Encodable.encode b) with he | he
      · exact Or.inl (Or.inr ⟨h, he⟩)
      · exact Or.inr (Or.inr ⟨h.symm, he⟩)
    · exact Or.inr (Or.inl h)

private instance : Std.Antisymm descriptorLE where
  antisymm a b hab hba := by
    rcases hab with hab | ⟨habv, habe⟩
    · rcases hba with hba | ⟨hbav, hbae⟩ <;> omega
    · rcases hba with hba | ⟨hbav, hbae⟩
      · omega
      · exact Encodable.encode_injective (Nat.le_antisymm habe hbae)

/-- For `1 ≤ m`, every positive integer having exactly `m` digits, represented once. -/
noncomputable def mDigitPositiveIntegers (m : ℕ) : List ℕ :=
  ((mDigitDescriptors m).sort descriptorLE).map descriptorValue

/-- The corresponding decimal blocks in lexicographic, hence numerical, order. -/
noncomputable def mDigitBlocks (m : ℕ) : List (List (Fin 10)) :=
  ((mDigitDescriptors m).sort descriptorLE).map descriptorDigits

/-- For `1 ≤ m`, the complete length-`m` Champernowne epoch. -/
noncomputable def epoch (m : ℕ) : List (Fin 10) :=
  (mDigitPositiveIntegers m).flatMap decimalDigits

/-- All overlapping contiguous occurrences in a finite word.

Every valid starting index is tested, so overlaps and starts crossing a block
boundary are included automatically.
-/
def finiteContiguousOccurrenceCount (w E : List (Fin 10)) : ℕ :=
  ((Finset.range (E.length + 1 - w.length)).filter fun i =>
    (E.drop i).take w.length = w).card

private def blockInternalOccurrenceCount
    (w a : List (Fin 10)) (m : ℕ) : ℕ :=
  ((Finset.range (m + 1 - w.length)).filter fun i =>
    (a.drop i).take w.length = w).card

private def boundaryOccurrenceCount
    (w a b : List (Fin 10)) (m : ℕ) : ℕ :=
  ((Finset.Icc 1 (w.length - 1)).filter fun r =>
    a.drop (m - r) ++ b.take (w.length - r) = w).card

private def recursiveInternalOccurrenceCount
    (w : List (Fin 10)) (B : List (List (Fin 10))) (m : ℕ) : ℕ :=
  (B.map fun a => blockInternalOccurrenceCount w a m).sum

private def recursiveBoundaryOccurrenceCount
    (w : List (Fin 10)) (B : List (List (Fin 10))) (m : ℕ) : ℕ :=
  match B with
  | a :: b :: B => boundaryOccurrenceCount w a b m +
      recursiveBoundaryOccurrenceCount w (b :: B) m
  | _ => 0

private theorem slice_append_internal (w a E : List (Fin 10)) (m i : ℕ)
    (ha : a.length = m) (hi : i < m + 1 - w.length) :
    ((a ++ E).drop i).take w.length = (a.drop i).take w.length := by
  rw [List.drop_append, List.take_append]
  have him : i ≤ m := by omega
  have hki : w.length ≤ m - i := by omega
  have hdrop : (a.drop i).length = m - i := by simp [ha]
  have hsub : i - a.length = 0 := by omega
  have hzero : w.length - (a.drop i).length = 0 := by omega
  rw [hsub, hzero, List.take_zero, List.append_nil]

private theorem slice_append_crossing (w a E : List (Fin 10)) (m t : ℕ)
    (ha : a.length = m) (hk : 1 ≤ w.length) (hkm : w.length ≤ m)
    (ht : t < w.length - 1) :
    ((a ++ E).drop (m + 1 - w.length + t)).take w.length =
      a.drop (m - (w.length - 1 - t)) ++
        E.take (w.length - (w.length - 1 - t)) := by
  let r := w.length - 1 - t
  have hr1 : 1 ≤ r := by omega
  have hrk : r < w.length := by omega
  have hi : m + 1 - w.length + t = m - r := by omega
  rw [hi, List.drop_append, List.take_append]
  have hsub : m - r - a.length = 0 := by omega
  have hdrop : (a.drop (m - r)).length = r := by simp [ha]; omega
  have htake : (a.drop (m - r)).take w.length = a.drop (m - r) :=
    List.take_of_length_le (by omega)
  rw [htake, hdrop]
  simp [hsub, r]

private theorem slice_append_tail (w a E : List (Fin 10)) (m j : ℕ)
    (ha : a.length = m) :
    ((a ++ E).drop (m + j)).take w.length = (E.drop j).take w.length := by
  rw [List.drop_append]
  have hsub : m + j - a.length = j := by omega
  have hdrop : a.drop (m + j) = [] := List.drop_eq_nil_iff.mpr (by omega)
  rw [hsub, hdrop, List.nil_append]

private theorem finiteContiguousOccurrenceCount_append
    (w a E : List (Fin 10)) (m : ℕ)
    (ha : a.length = m) (hk : 1 ≤ w.length) (hkm : w.length ≤ m)
    (hkE : w.length ≤ E.length) :
    finiteContiguousOccurrenceCount w (a ++ E) =
      blockInternalOccurrenceCount w a m + boundaryOccurrenceCount w a E m +
        finiteContiguousOccurrenceCount w E := by
  classical
  unfold finiteContiguousOccurrenceCount blockInternalOccurrenceCount
    boundaryOccurrenceCount
  rw [List.length_append, ha]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have htotal : m + E.length + 1 - w.length =
      (m + 1 - w.length) + ((w.length - 1) + (E.length + 1 - w.length)) := by
    omega
  rw [htotal, Finset.sum_range_add]
  rw [Finset.sum_range_add]
  rw [← Nat.add_assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      rw [slice_append_internal w a E m i ha (Finset.mem_range.mp hi)]
    · apply Finset.sum_bij (fun t _ => w.length - 1 - t)
      · intro t ht
        simp only [Finset.mem_Icc]
        have := Finset.mem_range.mp ht
        omega
      · intro t₁ ht₁ t₂ ht₂ heq
        have h₁ := Finset.mem_range.mp ht₁
        have h₂ := Finset.mem_range.mp ht₂
        omega
      · intro r hr
        simp only [Finset.mem_Icc] at hr
        refine ⟨w.length - 1 - r, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro t ht
        have htt := Finset.mem_range.mp ht
        rw [slice_append_crossing w a E m t ha hk hkm htt]
  · apply Finset.sum_congr rfl
    intro j hj
    have hi : m + 1 - w.length + (w.length - 1 + j) = m + j := by omega
    rw [hi, slice_append_tail w a E m j ha]

private theorem take_flatten_cons_of_le
    (b : List (Fin 10)) (B : List (List (Fin 10))) (n : ℕ)
    (hn : n ≤ b.length) : (b :: B).flatten.take n = b.take n := by
  simp only [List.flatten_cons, List.take_append]
  have hz : n - b.length = 0 := by omega
  simp [hz]

private theorem boundaryOccurrenceCount_flatten_cons
    (w a b : List (Fin 10)) (B : List (List (Fin 10))) (m : ℕ)
    (hb : b.length = m) (hkm : w.length ≤ m) :
    boundaryOccurrenceCount w a (b :: B).flatten m =
      boundaryOccurrenceCount w a b m := by
  unfold boundaryOccurrenceCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  simp only [Finset.mem_Icc] at hr
  rw [take_flatten_cons_of_le b B (w.length - r)]
  omega

private theorem finiteContiguousOccurrenceCount_flatten
    (w : List (Fin 10)) (B : List (List (Fin 10))) (m : ℕ)
    (hB : ∀ b ∈ B, b.length = m) (hk : 1 ≤ w.length) (hkm : w.length ≤ m) :
    finiteContiguousOccurrenceCount w B.flatten =
      recursiveInternalOccurrenceCount w B m +
        recursiveBoundaryOccurrenceCount w B m := by
  induction B with
  | nil =>
      simp [finiteContiguousOccurrenceCount, recursiveInternalOccurrenceCount,
        recursiveBoundaryOccurrenceCount, hk]
  | cons a B ih =>
      have ha : a.length = m := hB a (by simp)
      cases B with
      | nil =>
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
            recursiveInternalOccurrenceCount, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, Nat.add_zero, recursiveBoundaryOccurrenceCount]
          unfold finiteContiguousOccurrenceCount blockInternalOccurrenceCount
          rw [ha]
      | cons b B =>
          have hb : b.length = m := hB b (by simp)
          have htail : ∀ c ∈ b :: B, c.length = m := by
            intro c hc
            exact hB c (by simp [hc])
          have hElen : w.length ≤ (b :: B).flatten.length := by
            rw [List.flatten_cons, List.length_append, hb]
            omega
          rw [List.flatten_cons,
            finiteContiguousOccurrenceCount_append w a (b :: B).flatten m ha hk hkm hElen]
          rw [ih htail]
          rw [boundaryOccurrenceCount_flatten_cons w a b B m hb hkm]
          simp only [recursiveInternalOccurrenceCount, List.map_cons, List.sum_cons,
            recursiveBoundaryOccurrenceCount]
          omega

/-- A concrete coefficient independent of the epoch length `m`. -/
def discrepancyCoefficient (k : ℕ) : ℕ :=
  9 * k * (10 ^ (k - 1) + 1)

private theorem fixedLengthDigits_slice_card
    (p k s : ℕ) (w : List ℕ)
    (hwlen : w.length = k) (hwdigits : ∀ d ∈ w, d < 10) :
    ((List.fixedLengthDigits (b := 10) (by norm_num) (p + k + s)).filter fun L =>
      (L.drop p).take k = w).card = 10 ^ (p + s) := by
  classical
  let P := List.fixedLengthDigits (b := 10) (by norm_num) p ×ˢ
    List.fixedLengthDigits (b := 10) (by norm_num) s
  let S := (List.fixedLengthDigits (b := 10) (by norm_num) (p + k + s)).filter fun L =>
    (L.drop p).take k = w
  have hcard : P.card = S.card := by
    apply Finset.card_bij'
      (fun x _ => x.1 ++ w ++ x.2)
      (fun L _ => (L.take p, L.drop (p + k)))
    · intro x hx
      rw [Finset.mem_product] at hx
      rw [Finset.mem_filter]
      constructor
      · rw [List.mem_fixedLengthDigits_iff]
        constructor
        · simp only [List.length_append]
          rw [(List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.1 |>.1,
            (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.2 |>.1, hwlen]
        · intro d hd
          simp only [List.mem_append] at hd
          rcases hd with (hd | hd) | hd
          · exact (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.1 |>.2 d hd
          · exact hwdigits d hd
          · exact (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.2 |>.2 d hd
      · simp [(List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.1 |>.1, hwlen]
    · intro L hL
      rw [Finset.mem_product]
      rw [Finset.mem_filter] at hL
      have hLmem := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hL.1
      constructor
      · rw [List.mem_fixedLengthDigits_iff]
        constructor
        · simp [hLmem.1]
          omega
        · intro d hd
          exact hLmem.2 d (List.mem_of_mem_take hd)
      · rw [List.mem_fixedLengthDigits_iff]
        constructor
        · simp [hLmem.1]
        · intro d hd
          exact hLmem.2 d (List.mem_of_mem_drop hd)
    · intro x hx
      rw [Finset.mem_product] at hx
      apply Prod.ext
      · simp [(List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.1 |>.1]
      · have hp := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.1 |>.1
        have : p + k = x.1.length + w.length := by omega
        rw [this]
        simp
    · intro L hL
      rw [Finset.mem_filter] at hL
      have hLlen := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hL.1 |>.1
      rw [Prod.fst, Prod.snd]
      calc
        L.take p ++ w ++ L.drop (p + k) =
            L.take p ++ (L.drop p).take k ++ L.drop (p + k) := by rw [hL.2]
        _ = L := by
          rw [← List.drop_drop]
          simp
  change S.card = _
  rw [← hcard]
  simp [P, List.card_fixedLengthDigits, Nat.pow_add]

private theorem map_digitOfNat_eq_iff (L : List ℕ) (w : List (Fin 10))
    (hL : ∀ d ∈ L, d < 10) :
    L.map digitOfNat = w ↔ L = w.map Fin.val := by
  constructor
  · intro h
    have h' := congrArg (List.map Fin.val) h
    rw [List.map_map] at h'
    calc
      L = L.map (Fin.val ∘ digitOfNat) := by
        symm
        calc
          L.map (Fin.val ∘ digitOfNat) = L.map id := by
            apply List.map_congr_left
            intro d hd
            exact Nat.mod_eq_of_lt (hL d hd)
          _ = L := List.map_id L
      _ = w.map Fin.val := h'
  · intro h
    calc
      L.map digitOfNat = (w.map Fin.val).map digitOfNat := congrArg _ h
      _ = w.map (digitOfNat ∘ Fin.val) := List.map_map
      _ = w.map id := by
        apply List.map_congr_left
        intro d hd
        exact digitOfNat_val d
      _ = w := List.map_id w

theorem descriptorDigits_length {m : ℕ} (hm : 1 ≤ m) {x : ℕ × List ℕ}
    (hx : x ∈ mDigitDescriptors m) : (descriptorDigits x).length = m := by
  rw [mDigitDescriptors, Finset.mem_product] at hx
  simp only [descriptorDigits, List.length_cons, List.length_map]
  rw [(List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.2 |>.1]
  omega

theorem decimalDigits_descriptorValue {m : ℕ} {x : ℕ × List ℕ}
    (hx : x ∈ mDigitDescriptors m) :
    decimalDigits (descriptorValue x) = descriptorDigits x := by
  rw [mDigitDescriptors, Finset.mem_product] at hx
  have hlead : x.1 ≠ 0 := by
    have hmem : x.1 ∈ Finset.Icc 1 9 := by simpa [leadingDigits] using hx.1
    have := (Finset.mem_Icc.mp hmem).1
    omega
  have htail := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.2 |>.2
  have hdigits : Nat.digits 10 (descriptorValue x) = (x.1 :: x.2).reverse := by
    unfold descriptorValue
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro d hd
      rw [List.mem_reverse] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · have hmem : x.1 ∈ Finset.Icc 1 9 := by simpa [leadingDigits] using hx.1
        have hupper := (Finset.mem_Icc.mp hmem).2
        omega
      · exact htail d hd
    · intro h
      simpa only [List.getLast_reverse, List.head_cons] using hlead
  unfold decimalDigits descriptorDigits
  rw [hdigits, List.reverse_reverse, List.map_cons]

theorem epoch_eq_blocks_flatten (m : ℕ) :
    epoch m = (mDigitBlocks m).flatten := by
  classical
  unfold epoch mDigitPositiveIntegers mDigitBlocks
  rw [List.flatMap_map, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro x hx
  apply decimalDigits_descriptorValue
  simpa using hx

private theorem descriptor_nonleading_slice_card
    {m j k : ℕ} (w : List (Fin 10))
    (hm : 1 ≤ m) (hj : 1 ≤ j) (hjk : j + k ≤ m) (hwlen : w.length = k) :
    ((mDigitDescriptors m).filter fun x =>
      ((descriptorDigits x).drop j).take k = w).card =
      9 * 10 ^ (m - k - 1) := by
  classical
  let T := List.fixedLengthDigits (b := 10) (by norm_num) (m - 1)
  let U := T.filter fun L => (L.drop (j - 1)).take k = w.map Fin.val
  have hpred (d : ℕ) (L : List ℕ) (hL : L ∈ T) :
      ((descriptorDigits (d, L)).drop j).take k = w ↔
        (L.drop (j - 1)).take k = w.map Fin.val := by
    have hLd := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hL |>.2
    rw [show j = (j - 1) + 1 by omega]
    simp only [descriptorDigits, List.drop_succ_cons]
    rw [← List.map_drop, ← List.map_take]
    rw [show j - 1 + 1 - 1 = j - 1 by omega]
    apply map_digitOfNat_eq_iff
    intro x hx
    exact hLd x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hfilter :
      (mDigitDescriptors m).filter (fun x =>
        ((descriptorDigits x).drop j).take k = w) = leadingDigits ×ˢ U := by
    ext x
    simp only [Finset.mem_filter, mDigitDescriptors, Finset.mem_product, U]
    constructor
    · rintro ⟨⟨hd, hL⟩, hx⟩
      exact ⟨hd, hL, (hpred x.1 x.2 hL).mp hx⟩
    · rintro ⟨hd, hL, hx⟩
      exact ⟨⟨hd, hL⟩, (hpred x.1 x.2 hL).mpr hx⟩
  have hleadcard : leadingDigits.card = 9 := by
    simp [leadingDigits, Nat.card_Icc]
  have htail_length : m - 1 = (j - 1) + k + (m - j - k) := by omega
  have hwordlen : (w.map Fin.val).length = k := by simp [hwlen]
  have hworddigits : ∀ d ∈ w.map Fin.val, d < 10 := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    exact x.isLt
  have htailcard : U.card = 10 ^ ((j - 1) + (m - j - k)) := by
    have h := fixedLengthDigits_slice_card (j - 1) k (m - j - k)
      (w.map Fin.val) hwordlen hworddigits
    simpa only [U, T, htail_length] using h
  have hexponent : (j - 1) + (m - j - k) = m - k - 1 := by omega
  rw [hfilter, Finset.card_product, hleadcard, htailcard, hexponent]

/-- Occurrences wholly inside one integer and starting after its leading digit. -/
noncomputable def nonleadingInternalCount (w : List (Fin 10)) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (m - w.length),
    ((mDigitDescriptors m).filter fun x =>
      ((descriptorDigits x).drop j).take w.length = w).card

/-- Occurrences beginning at the leading digit of one integer. -/
noncomputable def leadingInternalCount (w : List (Fin 10)) (m : ℕ) : ℕ :=
  ((mDigitDescriptors m).filter fun x =>
    (descriptorDigits x).take w.length = w).card

/-- Occurrences crossing each adjacent-integer boundary.

For every boundary and every `r = 1, ..., |w|-1`, this tests the word made
from the last `r` digits on the left and the first `|w|-r` digits on the
right. Thus all overlapping cross-boundary starts are present.

This one-boundary representation applies when `|w| ≤ m` and is defined as
zero outside that regime.
-/
noncomputable def crossBoundaryCount (w : List (Fin 10)) (m : ℕ) : ℕ :=
  if w.length ≤ m then
    let B := mDigitBlocks m
    ∑ q ∈ Finset.range (B.length - 1),
      ((Finset.Icc 1 (w.length - 1)).filter fun r =>
        ((B.getD q []).drop (m - r) ++
          (B.getD (q + 1) []).take (w.length - r)) = w).card
  else 0

/-- The complete blockwise occurrence count at an epoch endpoint.

When `0 < |w| ≤ m`, the three summands are exactly all contiguous starts in
the flattened epoch: non-leading internal starts, leading starts, and starts
crossing one adjacent-integer boundary. Starts at different offsets are kept
distinct, so overlapping occurrences are counted separately.
-/
noncomputable def epochOccurrenceCount (w : List (Fin 10)) (m : ℕ) : ℕ :=
  nonleadingInternalCount w m + leadingInternalCount w m + crossBoundaryCount w m

private theorem blockInternalOccurrenceCount_split
    (w a : List (Fin 10)) (m : ℕ) (hkm : w.length ≤ m) :
    blockInternalOccurrenceCount w a m =
      (∑ j ∈ Finset.Icc 1 (m - w.length),
        if (a.drop j).take w.length = w then 1 else 0) +
      (if a.take w.length = w then 1 else 0) := by
  unfold blockInternalOccurrenceCount
  rw [Finset.card_filter]
  rw [show m + 1 - w.length = (m - w.length) + 1 by omega]
  rw [Finset.sum_range_succ']
  apply congrArg₂ (· + ·)
  · apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      simp only [Finset.mem_Icc]
      have := Finset.mem_range.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ heq
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨j - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro i hi
      rfl
  · simp

private theorem recursiveInternalOccurrenceCount_mDigitBlocks
    (w : List (Fin 10)) (m : ℕ) (hkm : w.length ≤ m) :
    recursiveInternalOccurrenceCount w (mDigitBlocks m) m =
      nonleadingInternalCount w m + leadingInternalCount w m := by
  classical
  have hsorted :
      recursiveInternalOccurrenceCount w (mDigitBlocks m) m =
        ∑ x ∈ mDigitDescriptors m,
          blockInternalOccurrenceCount w (descriptorDigits x) m := by
    unfold recursiveInternalOccurrenceCount mDigitBlocks
    rw [List.map_map]
    change
      (↑(((mDigitDescriptors m).sort descriptorLE).map
        (fun x => blockInternalOccurrenceCount w (descriptorDigits x) m)) :
          Multiset ℕ).sum =
        ((mDigitDescriptors m).val.map
          (fun x => blockInternalOccurrenceCount w (descriptorDigits x) m)).sum
    congr 1
    calc
      (↑(((mDigitDescriptors m).sort descriptorLE).map
          (fun x => blockInternalOccurrenceCount w (descriptorDigits x) m)) : Multiset ℕ) =
          Multiset.map (fun x => blockInternalOccurrenceCount w (descriptorDigits x) m)
            (↑((mDigitDescriptors m).sort descriptorLE) : Multiset (ℕ × List ℕ)) := rfl
      _ = Multiset.map (fun x => blockInternalOccurrenceCount w (descriptorDigits x) m)
          (mDigitDescriptors m).val :=
        congrArg _ (Finset.sort_eq (mDigitDescriptors m) descriptorLE)
  rw [hsorted]
  unfold nonleadingInternalCount leadingInternalCount
  simp_rw [Finset.card_filter]
  calc
    (∑ x ∈ mDigitDescriptors m,
        blockInternalOccurrenceCount w (descriptorDigits x) m) =
        ∑ x ∈ mDigitDescriptors m,
          ((∑ j ∈ Finset.Icc 1 (m - w.length),
              if ((descriptorDigits x).drop j).take w.length = w then 1 else 0) +
            (if (descriptorDigits x).take w.length = w then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact blockInternalOccurrenceCount_split w (descriptorDigits x) m hkm
    _ = (∑ j ∈ Finset.Icc 1 (m - w.length),
            ∑ x ∈ mDigitDescriptors m,
              if ((descriptorDigits x).drop j).take w.length = w then 1 else 0) +
          ∑ x ∈ mDigitDescriptors m,
            if (descriptorDigits x).take w.length = w then 1 else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]

private theorem indexedBoundaryOccurrenceCount_eq_recursive
    (w : List (Fin 10)) (B : List (List (Fin 10))) (m : ℕ) :
    (∑ q ∈ Finset.range (B.length - 1),
      boundaryOccurrenceCount w (B.getD q []) (B.getD (q + 1) []) m) =
      recursiveBoundaryOccurrenceCount w B m := by
  induction B with
  | nil => simp [recursiveBoundaryOccurrenceCount]
  | cons a B ih =>
      cases B with
      | nil => simp [recursiveBoundaryOccurrenceCount]
      | cons b B =>
          simp only [List.length_cons]
          rw [show B.length + 1 + 1 - 1 = B.length + 1 by omega]
          rw [Finset.sum_range_succ']
          change (∑ q ∈ Finset.range B.length,
              boundaryOccurrenceCount w ((a :: b :: B).getD (q + 1) [])
                ((a :: b :: B).getD (q + 1 + 1) []) m) +
              boundaryOccurrenceCount w a b m =
            recursiveBoundaryOccurrenceCount w (a :: b :: B) m
          simp only [List.getD_cons_succ]
          have hsum : (∑ q ∈ Finset.range B.length,
              boundaryOccurrenceCount w ((b :: B).getD q []) (B.getD q []) m) =
              ∑ q ∈ Finset.range ((b :: B).length - 1),
                boundaryOccurrenceCount w ((b :: B).getD q [])
                  ((b :: B).getD (q + 1) []) m := by
            simp only [List.length_cons, List.getD_cons_succ]
            congr 2
          rw [hsum, ih]
          simp [recursiveBoundaryOccurrenceCount, Nat.add_comm]

private theorem crossBoundaryCount_eq_recursive
    (w : List (Fin 10)) (m : ℕ) (hwm : w.length ≤ m) :
    crossBoundaryCount w m =
      recursiveBoundaryOccurrenceCount w (mDigitBlocks m) m := by
  simpa [crossBoundaryCount, boundaryOccurrenceCount, hwm] using
    indexedBoundaryOccurrenceCount_eq_recursive w (mDigitBlocks m) m

/-- The blockwise partition counts exactly the filtered starts in the flattened epoch. -/
theorem epochOccurrenceCount_eq_finiteContiguousOccurrenceCount
    (w : List (Fin 10)) (m : ℕ) (hw : 1 ≤ w.length) (hwm : w.length ≤ m) :
    epochOccurrenceCount w m = finiteContiguousOccurrenceCount w (epoch m) := by
  classical
  have hblocks : ∀ b ∈ mDigitBlocks m, b.length = m := by
    intro b hb
    rw [mDigitBlocks] at hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact descriptorDigits_length (le_trans hw hwm) (by simpa using hx)
  rw [epoch_eq_blocks_flatten]
  rw [finiteContiguousOccurrenceCount_flatten w (mDigitBlocks m) m hblocks hw hwm]
  rw [recursiveInternalOccurrenceCount_mDigitBlocks w m hwm]
  rw [← crossBoundaryCount_eq_recursive w m hwm]
  unfold epochOccurrenceCount
  omega

/-- Public occurrence count: all filtered contiguous starts in the flattened epoch. -/
noncomputable def occurrenceCount (w : List (Fin 10)) (m : ℕ) : ℕ :=
  finiteContiguousOccurrenceCount w (epoch m)

/-- Cross-boundary occurrences are an explicit summand of the public count. -/
theorem crossBoundaryCount_le_occurrenceCount (w : List (Fin 10)) (m : ℕ) :
    crossBoundaryCount w m ≤ occurrenceCount w m := by
  by_cases hwm : w.length ≤ m
  · by_cases hw : 1 ≤ w.length
    · rw [occurrenceCount,
        ← epochOccurrenceCount_eq_finiteContiguousOccurrenceCount w m hw hwm]
      unfold epochOccurrenceCount
      omega
    · have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst w
      simp [crossBoundaryCount]
  · simp [crossBoundaryCount, hwm]

theorem mDigitDescriptors_card (m : ℕ) :
    (mDigitDescriptors m).card = 9 * 10 ^ (m - 1) := by
  classical
  rw [mDigitDescriptors, Finset.card_product, List.card_fixedLengthDigits]
  simp [leadingDigits, Nat.card_Icc]

/-- Distinct length-`m` descriptors have distinct numerical values. -/
theorem descriptorValue_injectiveOn_mDigitDescriptors (m : ℕ) :
    Set.InjOn descriptorValue (mDigitDescriptors m) := by
  intro x hx y hy hvalue
  change x ∈ mDigitDescriptors m at hx
  change y ∈ mDigitDescriptors m at hy
  rw [mDigitDescriptors, Finset.mem_product] at hx hy
  have hxtail := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hx.2
  have hytail := (List.mem_fixedLengthDigits_iff (by norm_num)).mp hy.2
  have hxlead : x.1 < 10 := by
    have hxIcc : x.1 ∈ Finset.Icc 1 9 := by simpa [leadingDigits] using hx.1
    have hxupper := (Finset.mem_Icc.mp hxIcc).2
    omega
  have hylead : y.1 < 10 := by
    have hyIcc : y.1 ∈ Finset.Icc 1 9 := by simpa [leadingDigits] using hy.1
    have hyupper := (Finset.mem_Icc.mp hyIcc).2
    omega
  have hlength : (x.1 :: x.2).reverse.length = (y.1 :: y.2).reverse.length := by
    simp [hxtail.1, hytail.1]
  have hxdigits : ∀ d ∈ (x.1 :: x.2).reverse, d < 10 := by
    intro d hd
    rw [List.mem_reverse] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hxlead
    · exact hxtail.2 d hd
  have hydigits : ∀ d ∈ (y.1 :: y.2).reverse, d < 10 := by
    intro d hd
    rw [List.mem_reverse] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hylead
    · exact hytail.2 d hd
  have hlists : (x.1 :: x.2).reverse = (y.1 :: y.2).reverse := by
    apply Nat.ofDigits_inj_of_len_eq (by norm_num) hlength hxdigits hydigits
    exact hvalue
  have hcons : x.1 :: x.2 = y.1 :: y.2 := by
    simpa using congrArg List.reverse hlists
  exact Prod.ext (List.cons.inj hcons).1 (List.cons.inj hcons).2

/-- Every descriptor value has exactly `m` decimal digits. -/
theorem descriptorValue_decimalLength {m : ℕ} (hm : 1 ≤ m)
    {x : ℕ × List ℕ} (hx : x ∈ mDigitDescriptors m) :
    (Nat.digits 10 (descriptorValue x)).length = m := by
  calc
    (Nat.digits 10 (descriptorValue x)).length =
        (decimalDigits (descriptorValue x)).length := by simp [decimalDigits]
    _ = (descriptorDigits x).length :=
      congrArg List.length (decimalDigits_descriptorValue hx)
    _ = m := descriptorDigits_length hm hx

/-- Descriptor values lie in the complete interval of `m`-digit naturals. -/
theorem descriptorValue_mem_mDigitInterval {m : ℕ} (hm : 1 ≤ m)
    {x : ℕ × List ℕ} (hx : x ∈ mDigitDescriptors m) :
    10 ^ (m - 1) ≤ descriptorValue x ∧ descriptorValue x < 10 ^ m := by
  have hlength := descriptorValue_decimalLength hm hx
  constructor
  · exact (Nat.lt_digits_length_iff (by norm_num) (descriptorValue x)).mp (by omega)
  · exact (Nat.digits_length_le_iff (by norm_num) (descriptorValue x)).mp (by omega)

private theorem descriptorValue_image_eq_mDigitInterval (m : ℕ) (hm : 1 ≤ m) :
    (mDigitDescriptors m).image descriptorValue =
      Finset.Ico (10 ^ (m - 1)) (10 ^ m) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    exact Finset.mem_Ico.mpr (descriptorValue_mem_mDigitInterval hm hx)
  · rw [Finset.card_image_of_injOn (descriptorValue_injectiveOn_mDigitDescriptors m)]
    rw [mDigitDescriptors_card, Nat.card_Ico]
    have hpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    rw [hpow]
    omega

/-- Membership specification: the list contains precisely all `m`-digit naturals. -/
theorem mem_mDigitPositiveIntegers_iff
    (m n : ℕ) (hm : 1 ≤ m) :
    n ∈ mDigitPositiveIntegers m ↔ 10 ^ (m - 1) ≤ n ∧ n < 10 ^ m := by
  classical
  rw [← Finset.mem_Ico]
  rw [← descriptorValue_image_eq_mDigitInterval m hm]
  simp [mDigitPositiveIntegers]

/-- No natural number occurs twice in the length-`m` epoch descriptor list. -/
theorem mDigitPositiveIntegers_nodup (m : ℕ) :
    (mDigitPositiveIntegers m).Nodup := by
  classical
  unfold mDigitPositiveIntegers
  apply List.Nodup.map_on
  · intro x hx y hy hvalue
    apply descriptorValue_injectiveOn_mDigitDescriptors m
    · simpa using hx
    · simpa using hy
    · exact hvalue
  · exact Finset.sort_nodup _ _

/-- Descriptor sorting induces nondecreasing numerical order. -/
theorem mDigitPositiveIntegers_sortedLE (m : ℕ) :
    (mDigitPositiveIntegers m).SortedLE := by
  classical
  rw [List.sortedLE_iff_pairwise]
  unfold mDigitPositiveIntegers
  rw [List.pairwise_map]
  apply (Finset.pairwise_sort (mDigitDescriptors m) descriptorLE).imp
  intro x y hxy
  unfold descriptorLE at hxy
  omega

/-- The length-`m` positive integers occur in strictly increasing numerical order. -/
theorem mDigitPositiveIntegers_sortedLT (m : ℕ) :
    (mDigitPositiveIntegers m).SortedLT :=
  (mDigitPositiveIntegers_sortedLE m).sortedLT_of_nodup
    (mDigitPositiveIntegers_nodup m)

/-- Exact enumeration of every `m`-digit natural, once and in numerical order. -/
theorem mDigitPositiveIntegers_eq_range (m : ℕ) (hm : 1 ≤ m) :
    mDigitPositiveIntegers m =
      List.range' (10 ^ (m - 1)) (9 * 10 ^ (m - 1)) := by
  apply (mDigitPositiveIntegers_sortedLT m).eq_of_mem_iff
    (List.sortedLT_range' (10 ^ (m - 1)) (9 * 10 ^ (m - 1)) (by omega))
  intro n
  rw [mem_mDigitPositiveIntegers_iff m n hm, List.mem_range']
  have hpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  rw [hpow]
  constructor
  · rintro ⟨hlower, hupper⟩
    refine ⟨n - 10 ^ (m - 1), ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨i, hi, rfl⟩
    omega

theorem mDigitBlocks_length (m : ℕ) :
    (mDigitBlocks m).length = 9 * 10 ^ (m - 1) := by
  classical
  simp [mDigitBlocks, mDigitDescriptors_card]

theorem epoch_length (m : ℕ) (hm : 1 ≤ m) :
    (epoch m).length = m * (9 * 10 ^ (m - 1)) := by
  classical
  rw [epoch_eq_blocks_flatten m, List.length_flatten]
  unfold mDigitBlocks
  rw [List.map_map]
  have hlengths :
      ((mDigitDescriptors m).sort descriptorLE).map (fun x => (descriptorDigits x).length) =
        ((mDigitDescriptors m).sort descriptorLE).map (fun _ => m) := by
    apply List.map_congr_left
    intro x hx
    exact descriptorDigits_length hm (by simpa using hx)
  change (((mDigitDescriptors m).sort descriptorLE).map
    (fun x => (descriptorDigits x).length)).sum = _
  rw [hlengths]
  simp [mDigitDescriptors_card]
  ring

theorem nonleadingInternalCount_eq (w : List (Fin 10)) (m k : ℕ)
    (hm : 1 ≤ m) (hwlen : w.length = k) :
    nonleadingInternalCount w m =
      (m - k) * (9 * 10 ^ (m - k - 1)) := by
  classical
  unfold nonleadingInternalCount
  rw [hwlen]
  calc
    (∑ j ∈ Finset.Icc 1 (m - k),
        ((mDigitDescriptors m).filter fun x =>
          ((descriptorDigits x).drop j).take k = w).card) =
        ∑ _j ∈ Finset.Icc 1 (m - k), 9 * 10 ^ (m - k - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjone := (Finset.mem_Icc.mp hj).1
      have hjle := (Finset.mem_Icc.mp hj).2
      apply descriptor_nonleading_slice_card w hm hjone
      · have hjle := (Finset.mem_Icc.mp hj).2
        omega
      · exact hwlen
    _ = (m - k) * (9 * 10 ^ (m - k - 1)) := by
      simp [Nat.card_Icc]

theorem leadingInternalCount_le (w : List (Fin 10)) (m : ℕ) :
    leadingInternalCount w m ≤ 9 * 10 ^ (m - 1) := by
  unfold leadingInternalCount
  exact (Finset.card_filter_le _ _).trans_eq (mDigitDescriptors_card m)

theorem crossBoundaryCount_le (w : List (Fin 10)) (m : ℕ) :
    crossBoundaryCount w m ≤
      (9 * 10 ^ (m - 1) - 1) * (w.length - 1) := by
  classical
  by_cases hwm : w.length ≤ m
  · rw [crossBoundaryCount, if_pos hwm]
    let B := mDigitBlocks m
    calc
      (∑ q ∈ Finset.range (B.length - 1),
          ((Finset.Icc 1 (w.length - 1)).filter fun r =>
            ((B.getD q []).drop (m - r) ++
              (B.getD (q + 1) []).take (w.length - r)) = w).card) ≤
          ∑ _q ∈ Finset.range (B.length - 1), (w.length - 1) := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_filter_le _ _).trans_eq (by simp [Nat.card_Icc])
      _ = (9 * 10 ^ (m - 1) - 1) * (w.length - 1) := by
        simp [B, mDigitBlocks_length]
  · simp [crossBoundaryCount, hwm]

theorem exceptionalCount_le (w : List (Fin 10)) (m k : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) :
    leadingInternalCount w m + crossBoundaryCount w m ≤
      k * (9 * 10 ^ (m - 1)) := by
  have hlead := leadingInternalCount_le w m
  have hcross := crossBoundaryCount_le w m
  rw [hwlen] at hcross
  calc
    leadingInternalCount w m + crossBoundaryCount w m ≤
        9 * 10 ^ (m - 1) +
          (9 * 10 ^ (m - 1) - 1) * (k - 1) := Nat.add_le_add hlead hcross
    _ ≤ 9 * 10 ^ (m - 1) + (9 * 10 ^ (m - 1)) * (k - 1) := by
      gcongr
      exact Nat.sub_le _ _
    _ = k * (9 * 10 ^ (m - 1)) := by
      calc
        9 * 10 ^ (m - 1) + (9 * 10 ^ (m - 1)) * (k - 1) =
            (9 * 10 ^ (m - 1)) * ((k - 1) + 1) := by ring
        _ = (9 * 10 ^ (m - 1)) * k := by rw [Nat.sub_add_cancel hk]
        _ = k * (9 * 10 ^ (m - 1)) := Nat.mul_comm _ _

private theorem scaled_nonleading_term (m k : ℕ) (hkm : k ≤ m) :
    10 ^ k * ((m - k) * (9 * 10 ^ (m - k - 1))) =
      (m - k) * (9 * 10 ^ (m - 1)) := by
  by_cases hmk : m = k
  · subst m
    simp
  · have hlt : k < m := lt_of_le_of_ne hkm (Ne.symm hmk)
    have hexponent : k + (m - k - 1) = m - 1 := by omega
    calc
      10 ^ k * ((m - k) * (9 * 10 ^ (m - k - 1))) =
          (m - k) * 9 * (10 ^ k * 10 ^ (m - k - 1)) := by ring
      _ = (m - k) * 9 * 10 ^ (m - 1) := by rw [← pow_add, hexponent]
      _ = (m - k) * (9 * 10 ^ (m - 1)) := by ring

private theorem final_arithmetic_bound (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    k * (9 * 10 ^ (m - 1)) + 10 ^ k * (k * (9 * 10 ^ (m - 1))) ≤
      discrepancyCoefficient k * 10 ^ m := by
  have hmpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  have hkpow : 10 ^ k = 10 ^ (k - 1) * 10 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  unfold discrepancyCoefficient
  rw [hmpow, hkpow]
  nlinarith [Nat.zero_le (10 ^ (m - 1)), Nat.zero_le (10 ^ (k - 1))]

/--
Explicit uniform discrepancy bound for every nonempty decimal word, including
words with leading zeros, at every complete epoch with `m ≥ max 1 |w|`.

`occurrenceCount` counts all overlapping internal occurrences and all
overlapping occurrences crossing adjacent-integer boundaries. The coefficient
`9*k*(10^(k-1)+1)` depends only on the word length, never on `m`.

This finite endpoint estimate proves neither full Champernowne normality nor
any statement about pi, canonical V1, sibling V2, or sibling V3.
-/
theorem champernowne_epoch_uniform_discrepancy
    (w : List (Fin 10)) (k m : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : max 1 k ≤ m) :
    Int.natAbs
        (((10 ^ k * occurrenceCount w m : ℕ) : ℤ) - ((epoch m).length : ℤ)) ≤
      discrepancyCoefficient k * 10 ^ m := by
  have hm1 : 1 ≤ m := le_trans (le_max_left 1 k) hm
  have hkm : k ≤ m := le_trans (le_max_right 1 k) hm
  let N := 9 * 10 ^ (m - 1)
  let G := nonleadingInternalCount w m
  let R := leadingInternalCount w m + crossBoundaryCount w m
  have hG : G = (m - k) * (9 * 10 ^ (m - k - 1)) := by
    exact nonleadingInternalCount_eq w m k hm1 hwlen
  have hR : R ≤ k * N := by
    exact exceptionalCount_le w m k hwlen hk
  have hlength : (epoch m).length = m * N := by
    exact epoch_length m hm1
  have hscaledG : 10 ^ k * G = (m - k) * N := by
    rw [hG]
    exact scaled_nonleading_term m k hkm
  have hmdecomp : m = (m - k) + k := by omega
  have hlength' : (epoch m).length = ((m - k) + k) * N := by
    rw [← hmdecomp]
    exact hlength
  have hscaled_le : 10 ^ k * G ≤ (epoch m).length := by
    rw [hlength', hscaledG, Nat.add_mul]
    exact Nat.le_add_right _ _
  have hdeficit : (epoch m).length - 10 ^ k * G = k * N := by
    rw [hlength', hscaledG, Nat.add_mul]
    exact Nat.add_sub_cancel_left _ _
  have hbaseAbs :
      Int.natAbs (((10 ^ k * G : ℕ) : ℤ) - ((epoch m).length : ℤ)) = k * N := by
    rw [Int.natAbs_natCast_sub_natCast_of_le hscaled_le, hdeficit]
  have hcount : occurrenceCount w m = G + R := by
    rw [occurrenceCount,
      ← epochOccurrenceCount_eq_finiteContiguousOccurrenceCount w m (by omega) (by omega)]
    unfold epochOccurrenceCount G R
    omega
  calc
    Int.natAbs
        (((10 ^ k * occurrenceCount w m : ℕ) : ℤ) - ((epoch m).length : ℤ)) =
        Int.natAbs
          ((((10 ^ k * G : ℕ) : ℤ) - ((epoch m).length : ℤ)) +
            ((10 ^ k * R : ℕ) : ℤ)) := by
      rw [hcount]
      congr 1
      push_cast
      ring
    _ ≤ Int.natAbs (((10 ^ k * G : ℕ) : ℤ) - ((epoch m).length : ℤ)) +
        Int.natAbs ((10 ^ k * R : ℕ) : ℤ) := Int.natAbs_add_le _ _
    _ = k * N + 10 ^ k * R := by
      rw [hbaseAbs]
      congr 1
    _ ≤ k * N + 10 ^ k * (k * N) := by gcongr
    _ ≤ discrepancyCoefficient k * 10 ^ m := final_arithmetic_bound m k hm1 hk

theorem champernowne_epoch_leadingZero_discrepancy
    (d : List (Fin 10)) (m : ℕ) (hm : max 1 (d.length + 1) ≤ m) :
    Int.natAbs
        (((10 ^ (d.length + 1) *
          occurrenceCount ((0 : Fin 10) :: d) m : ℕ) : ℤ) -
          ((epoch m).length : ℤ)) ≤
      discrepancyCoefficient (d.length + 1) * 10 ^ m := by
  apply champernowne_epoch_uniform_discrepancy ((0 : Fin 10) :: d) (d.length + 1) m
  · simp
  · omega
  · exact hm

#print axioms Theory.PiDigits.T23.champernowne_epoch_uniform_discrepancy
#print axioms Theory.PiDigits.T23.champernowne_epoch_leadingZero_discrepancy
#print axioms Theory.PiDigits.T23.epochOccurrenceCount_eq_finiteContiguousOccurrenceCount
#print axioms Theory.PiDigits.T23.mem_mDigitPositiveIntegers_iff
#print axioms Theory.PiDigits.T23.mDigitPositiveIntegers_nodup
#print axioms Theory.PiDigits.T23.mDigitPositiveIntegers_sortedLT
#print axioms Theory.PiDigits.T23.mDigitPositiveIntegers_eq_range
#print axioms Theory.PiDigits.T23.crossBoundaryCount_le_occurrenceCount

end Theory.PiDigits.T23
