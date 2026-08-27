import TheoryLib.PiLacunaryNearReturnSparsity.T83T83LiteralStatisticAudit

/-!
# T92: constant-run Review-B discriminator

This file analyzes the exact-word sibling isolated by T83 and T87. It proves
no statement about `Real.pi`, C1, C2, or the carry-thickened T56 statistic.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T92ConstantRunDiscriminator

open DecimalFactorComplexity
open DecimalFactorComplexity.T83LiteralStatisticAudit

/-- Review B's binary sample length, using natural-number division. -/
def binarySampleLength (n : ℕ) : ℕ := 2 ^ (n / 2)

/-- The ordered, off-diagonal, exact-equality short count of the constant
binary family. T83 proves that this is the count on its legal constant stream. -/
def constantShortCount (n : ℕ) : ℕ :=
  constantRunExactShortPairCount n (binarySampleLength n)

/-- The ordered exact-equality long count of the constant family. Since every
length-`n` block is equal, this is the complement of the short count among all
ordered off-diagonal pairs of the `L_n` starts. -/
def constantLongCount (n : ℕ) : ℕ :=
  binarySampleLength n * (binarySampleLength n - 1) - constantShortCount n

/-- One infinite legal binary word supplies every finite prefix in the family. -/
def constantBinaryStream : Stream (Fin 2) := fun _ => 0

/-- T87's ordered, off-diagonal exact-equality short statistic for a binary
stream: positive lags are doubled to include both orientations. -/
def binaryExactShortPairCount (x : Stream (Fin 2)) (n L : ℕ) : ℕ :=
  by
    classical
    exact 2 * ∑ r ∈ (Finset.Icc 1 (L - 1)).filter (fun r => r < n),
      ((Finset.range (L - r)).filter fun i =>
        factorAt x n i = factorAt x n (i + r)).card

/-- T87's ordered, off-diagonal exact-equality long statistic, with the
boundary lag `n` included. -/
def binaryExactLongPairCount (x : Stream (Fin 2)) (n L : ℕ) : ℕ :=
  by
    classical
    exact 2 * ∑ r ∈ Finset.Icc n (L - 1),
      ((Finset.range (L - r)).filter fun i =>
        factorAt x n i = factorAt x n (i + r)).card

/-- Every short comparison succeeds on the constant binary stream. -/
theorem binaryExactShortPairCount_constantBinaryStream (n L : ℕ) :
    binaryExactShortPairCount constantBinaryStream n L =
      constantRunExactShortPairCount n L := by
  classical
  unfold binaryExactShortPairCount constantRunExactShortPairCount
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.card_filter_eq_iff.mpr]
  · simp
  · intro i _hi
    apply Subtype.ext
    funext j
    rfl

/-- Every long comparison also succeeds on the same constant binary stream. -/
theorem binaryExactLongPairCount_constantBinaryStream (n L : ℕ) :
    binaryExactLongPairCount constantBinaryStream n L =
      2 * ∑ r ∈ Finset.Icc n (L - 1), (L - r) := by
  classical
  unfold binaryExactLongPairCount
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.card_filter_eq_iff.mpr]
  · simp
  · intro i _hi
    apply Subtype.ext
    funext j
    rfl

/-- The short count is realized by one legal infinite stream, not by unrelated
finite words selected separately at each scale. -/
theorem constantShortCount_eq_legal_stream_count (n : ℕ) :
    constantShortCount n =
      exactShortPairCount constantDecimalStream n (binarySampleLength n) := by
  rw [exactShortPairCount_constantDecimalStream]
  rfl

/-- Both orientations of all positive lags enumerate every ordered
off-diagonal pair. -/
theorem total_constant_lag_sum (L : ℕ) :
    2 * ∑ r ∈ Finset.Icc 1 (L - 1), (L - r) = L * (L - 1) := by
  cases L with
  | zero => simp
  | succ L =>
      have hreflect := Finset.sum_Ico_reflect (fun j : ℕ => j) 1
        (m := L + 1) (n := L + 1) (by omega)
      rw [show Nat.succ L - 1 = L by omega,
        show Finset.Icc 1 L = Finset.Ico 1 (L + 1) by
          ext x
          simp]
      have hreflect' :
          (∑ j ∈ Finset.Ico 1 (L + 1), (L + 1 - j)) =
            ∑ j ∈ Finset.Ico 1 (L + 1), j := by
        simpa using hreflect
      rw [hreflect']
      rw [show Finset.Ico 1 (L + 1) = Finset.range (L + 1) \ {0} by
        ext x
        simp
        omega]
      have hzero : ({0} : Finset ℕ) ⊆ Finset.range (L + 1) := by simp
      have hsum : (∑ j ∈ Finset.range (L + 1) \ {0}, j) +
          (∑ j ∈ ({0} : Finset ℕ), j) =
            ∑ j ∈ Finset.range (L + 1), j :=
        Finset.sum_sdiff hzero
      have heq : (∑ j ∈ Finset.range (L + 1) \ {0}, j) =
          ∑ j ∈ Finset.range (L + 1), j := by
        simpa using hsum
      rw [heq]
      rw [Nat.mul_comm 2, Finset.sum_range_id_mul_two]
      simp

/-- The short and long positive-lag ranges are disjoint and exhaustive. -/
theorem constantRun_short_add_long (n L : ℕ) (hn : 1 ≤ n) :
    constantRunExactShortPairCount n L +
        2 * ∑ r ∈ Finset.Icc n (L - 1), (L - r) =
      L * (L - 1) := by
  let A := (Finset.Icc 1 (L - 1)).filter (fun r => r < n)
  let B := Finset.Icc n (L - 1)
  have hcover : A ∪ B = Finset.Icc 1 (L - 1) := by
    ext r
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisjoint : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrA hrB
    have hra := (Finset.mem_filter.mp hrA).2
    have hrb := (Finset.mem_Icc.mp hrB).1
    omega
  have hsum :
      (∑ r ∈ A, (L - r)) + ∑ r ∈ B, (L - r) =
        ∑ r ∈ Finset.Icc 1 (L - 1), (L - r) := by
    rw [← Finset.sum_union hdisjoint, hcover]
  have htotal := total_constant_lag_sum L
  unfold constantRunExactShortPairCount
  change 2 * ∑ r ∈ A, (L - r) + 2 * ∑ r ∈ B, (L - r) =
    L * (L - 1)
  omega

/-- The numerical long count is exactly T87's long statistic on the one legal
binary stream, including lag `n`. -/
theorem constantLongCount_eq_legal_binary_stream_count
    (n : ℕ) (hn : 1 ≤ n) :
    constantLongCount n =
      binaryExactLongPairCount constantBinaryStream n (binarySampleLength n) := by
  rw [binaryExactLongPairCount_constantBinaryStream]
  have hpartition := constantRun_short_add_long n (binarySampleLength n) hn
  unfold constantLongCount constantShortCount
  omega

/-- Likewise, the numerical short count is exactly T87's short statistic on
the same legal binary stream. -/
theorem constantShortCount_eq_legal_binary_stream_count (n : ℕ) :
    constantShortCount n =
      binaryExactShortPairCount constantBinaryStream n (binarySampleLength n) := by
  rw [binaryExactShortPairCount_constantBinaryStream]
  rfl

/-- The short and long classes partition all ordered off-diagonal pairs in the
constant family. -/
theorem constantShortCount_add_constantLongCount (n : ℕ) :
    constantShortCount n + constantLongCount n =
      binarySampleLength n * (binarySampleLength n - 1) := by
  unfold constantLongCount
  have hsubset :
      (Finset.Icc 1 (binarySampleLength n - 1)).filter (fun r => r < n) ⊆
        Finset.Icc 1 (binarySampleLength n - 1) :=
    Finset.filter_subset _ _
  have hsum :
      (∑ r ∈ (Finset.Icc 1 (binarySampleLength n - 1)).filter (fun r => r < n),
          (binarySampleLength n - r)) ≤
        ∑ r ∈ Finset.Icc 1 (binarySampleLength n - 1),
          (binarySampleLength n - r) :=
    Finset.sum_le_sum_of_subset hsubset
  have hshort : constantShortCount n ≤
      binarySampleLength n * (binarySampleLength n - 1) := by
    unfold constantShortCount constantRunExactShortPairCount
    have htotal := total_constant_lag_sum (binarySampleLength n)
    omega
  omega

/-- There are fewer than `n` positive short lags, at most `L_n` starts per
lag, and two orientations. -/
theorem constantShortCount_le_two_mul (n : ℕ) :
    constantShortCount n ≤ 2 * n * binarySampleLength n := by
  let A := (Finset.Icc 1 (binarySampleLength n - 1)).filter (fun r => r < n)
  have hcard : A.card ≤ n := by
    calc
      A.card ≤ (Finset.range n).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_range]
        exact (Finset.mem_filter.mp hr).2
      _ = n := Finset.card_range _
  have hsum :
      (∑ r ∈ A, (binarySampleLength n - r)) ≤
        ∑ _r ∈ A, binarySampleLength n := by
    apply Finset.sum_le_sum
    intro r _hr
    omega
  unfold constantShortCount constantRunExactShortPairCount
  change 2 * ∑ r ∈ A, (binarySampleLength n - r) ≤
    2 * n * binarySampleLength n
  calc
    2 * ∑ r ∈ A, (binarySampleLength n - r) ≤
        2 * ∑ _r ∈ A, binarySampleLength n := Nat.mul_le_mul_left 2 hsum
    _ = 2 * A.card * binarySampleLength n := by simp [mul_assoc]
    _ ≤ 2 * n * binarySampleLength n := by gcongr

/-- Explicit exponential domination used after the finite exceptional range. -/
theorem twenty_mul_add_ten_le_three_mul_two_pow_sub_one
    {k : ℕ} (hk : 6 ≤ k) :
    20 * k + 10 ≤ 3 * (2 ^ k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hpow : 20 ≤ 3 * 2 ^ k := by
        have hmono : 2 ^ 6 ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by norm_num) hk
        norm_num at hmono ⊢
        omega
      rw [pow_succ]
      omega

/-- From `n=12` onward, the quadratic long-pair load already pays the entire
short count with Review B's coefficient `3/2`; no additive constant is needed. -/
theorem late_constantShortCount_charged_by_long
    {n : ℕ} (hn : 12 ≤ n) :
    2 * constantShortCount n ≤ 3 * constantLongCount n := by
  let k := n / 2
  let L := binarySampleLength n
  have hk : 6 ≤ k := by
    dsimp [k]
    omega
  have hnupper : n ≤ 2 * k + 1 := by
    dsimp [k]
    omega
  have hdom := twenty_mul_add_ten_le_three_mul_two_pow_sub_one hk
  have hL : L = 2 ^ k := by rfl
  have hscale : 10 * n ≤ 3 * (L - 1) := by
    calc
      10 * n ≤ 10 * (2 * k + 1) := Nat.mul_le_mul_left 10 hnupper
      _ = 20 * k + 10 := by ring
      _ ≤ 3 * (2 ^ k - 1) := hdom
      _ = 3 * (L - 1) := by rw [hL]
  have hshort := constantShortCount_le_two_mul n
  have hshort' : constantShortCount n ≤ 2 * n * L := by
    simpa [L] using hshort
  have hfive : 5 * constantShortCount n ≤ 3 * (L * (L - 1)) := by
    calc
      5 * constantShortCount n ≤ 5 * (2 * n * L) :=
        Nat.mul_le_mul_left 5 hshort'
      _ = (10 * n) * L := by ring
      _ ≤ (3 * (L - 1)) * L := Nat.mul_le_mul_right L hscale
      _ = 3 * (L * (L - 1)) := by ring
  have hpartition := constantShortCount_add_constantLongCount n
  have hpartition' : constantShortCount n + constantLongCount n =
      L * (L - 1) := by
    simpa [L] using hpartition
  omega

/-- The T87-inspired constant family has discriminator at most `51/8` at every
scale. This denominator-free form is exactly
`S ≤ (51/8)L + (3/2)R`. -/
theorem constant_family_uniform_reviewB_bound (n : ℕ) :
    8 * constantShortCount n ≤
      51 * binarySampleLength n + 12 * constantLongCount n := by
  by_cases hn : 12 ≤ n
  · have hlate := late_constantShortCount_charged_by_long hn
    omega
  · have hnle : n ≤ 11 := by omega
    interval_cases n <;>
      norm_num [binarySampleLength, constantShortCount, constantLongCount,
        constantRunExactShortPairCount] <;>
      decide

/-- Directly on the legal infinite binary stream, T87's exact statistic has
the uniform Review-B constant `51/8` for every allowed `n ≥ 1`. -/
theorem legal_constantBinaryStream_uniform_reviewB_bound
    {n : ℕ} (hn : 1 ≤ n) :
    8 * binaryExactShortPairCount constantBinaryStream n (binarySampleLength n) ≤
      51 * binarySampleLength n +
        12 * binaryExactLongPairCount constantBinaryStream n
          (binarySampleLength n) := by
  rw [← constantShortCount_eq_legal_binary_stream_count,
    ← constantLongCount_eq_legal_binary_stream_count n hn]
  exact constant_family_uniform_reviewB_bound n

/-- The uniform constant is sharp for this family: equality occurs at `n=7`,
where `L=8`, `S=54`, and `R=2`. -/
theorem constant_family_equality_at_seven :
    binarySampleLength 7 = 8 ∧
      constantShortCount 7 = 54 ∧
      constantLongCount 7 = 2 ∧
      8 * constantShortCount 7 =
        51 * binarySampleLength 7 + 12 * constantLongCount 7 := by
  norm_num [binarySampleLength, constantShortCount, constantLongCount,
    constantRunExactShortPairCount]
  decide

end DecimalFactorComplexity.T92ConstantRunDiscriminator

#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constantShortCount_eq_legal_stream_count
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.binaryExactShortPairCount_constantBinaryStream
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.binaryExactLongPairCount_constantBinaryStream
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constantLongCount_eq_legal_binary_stream_count
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constantShortCount_add_constantLongCount
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constantShortCount_le_two_mul
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.twenty_mul_add_ten_le_three_mul_two_pow_sub_one
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.late_constantShortCount_charged_by_long
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constant_family_uniform_reviewB_bound
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.legal_constantBinaryStream_uniform_reviewB_bound
#print axioms DecimalFactorComplexity.T92ConstantRunDiscriminator.constant_family_equality_at_seven
