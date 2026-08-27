import TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction
import TheoryLib.PiLongLagBlockCollisionDecay.T49T49PrimitiveIncidenceAssembly

/-!
# T56: signed primitive residue pairing at `m = 1`

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module independently formalizes the finite residue-1/residue-9 core
suggested by the unverified T54 note. It imports only kernel-checked T29 and
T49 interfaces. A bounded base-ten uniqueness argument proves that the four
displayed rows exhaust each full ambient T49 primitive value fiber. The module
also proves the exact quartic record count and identifies the parameter sum
with the deduplicated selected Finset sums.
The analytic transfer is conditional on an explicit `EBoxBound`; no instance
of that bound, all-scale primitive estimate, C2, C1, or canonical collision
estimate is asserted.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T56

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T34
open Theory.PiDigits.LongLagBlockCollisionDecay.T49

/-- The dyadic side length used throughout T56. -/
def boxLength (t : ℕ) : ℕ := 2 ^ t

/-- The sole scale in T56 is `m=1`, `N=4*L+1`. -/
def boxEndpoint (t : ℕ) : ℕ := 4 * boxLength t + 1

/-- The literal canonical block at `N=4*2^t+1`. -/
def boxBlock (t : ℕ) : DyadicBlock := ⟨1, t + 2⟩

/-- Four ordered coordinates, stored as `(((x1,x2),x3),x4)`. -/
abbrev BoxQuartet := ((ℕ × ℕ) × ℕ) × ℕ

def boxX1 (x : BoxQuartet) : ℕ := x.1.1.1
def boxX2 (x : BoxQuartet) : ℕ := x.1.1.2
def boxX3 (x : BoxQuartet) : ℕ := x.1.2
def boxX4 (x : BoxQuartet) : ℕ := x.2

def boxInterval1 (t : ℕ) : Finset ℕ :=
  Finset.Icc 1 (boxLength t)

def boxInterval2 (t : ℕ) : Finset ℕ :=
  Finset.Icc (boxLength t + 1) (2 * boxLength t)

def boxInterval3 (t : ℕ) : Finset ℕ :=
  Finset.Icc (2 * boxLength t + 1) (3 * boxLength t)

def boxInterval4 (t : ℕ) : Finset ℕ :=
  Finset.Icc (3 * boxLength t + 1) (4 * boxLength t)

/-- The exact Cartesian quartet box `I1 x I2 x I3 x I4`. -/
def boxQuartetDomain (t : ℕ) : Finset BoxQuartet :=
  ((boxInterval1 t ×ˢ boxInterval2 t) ×ˢ boxInterval3 t) ×ˢ boxInterval4 t

/-- The four label permutations in one positive primitive value fiber. -/
inductive FiberRow
  | row00
  | row01
  | row10
  | row11
  deriving DecidableEq, Fintype

/-- The unique T12 record whose ordered coordinates are `(x,y)` when `x≠y`. -/
def coordinateRecord (x y : ℕ) : OrderedLongPair :=
  if y < x then (true, ⟨x - y, y⟩) else (false, ⟨y - x, x⟩)

/-- In an eight-token base-ten relation with coefficients of absolute value at
most one, the coefficient sum at every fixed exponent vanishes.  The strict
inequality `8 < 10` is the no-carry input. -/
theorem eightToken_coefficient_balance
    (a : Fin 8 → ℕ) (c : Fin 8 → ℤ)
    (hc : ∀ i, (c i).natAbs ≤ 1)
    (hsum : ∑ i, c i * (10 : ℤ) ^ a i = 0) (e : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i => a i = e), c i = 0 := by
  have upper (q : ℕ) :
      ∑ i ∈ Finset.univ.filter (fun i => q ≤ a i),
        c i * (10 : ℤ) ^ a i = 0 := by
    exact decimal_upper_sum_eq_zero (K := 1) (J := 1) a c hc
      (by norm_num) hsum (by omega)
  let E := Finset.univ.filter (fun i => a i = e)
  let H := Finset.univ.filter (fun i => e + 1 ≤ a i)
  have hsplit : Finset.univ.filter (fun i => e ≤ a i) = E ∪ H := by
    ext i
    simp only [E, H, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hdisj : Disjoint E H := by
    apply Finset.disjoint_left.mpr
    intro i hiE hiH
    have hiEq := (Finset.mem_filter.mp hiE).2
    have hiHigh := (Finset.mem_filter.mp hiH).2
    omega
  have hslice : ∑ i ∈ E, c i * (10 : ℤ) ^ a i = 0 := by
    have h := upper e
    rw [hsplit, Finset.sum_union hdisj] at h
    have hH := upper (e + 1)
    change (∑ i ∈ H, c i * (10 : ℤ) ^ a i) = 0 at hH
    simpa [hH] using h
  have hfactor :
      (∑ i ∈ E, c i * (10 : ℤ) ^ a i) =
        (∑ i ∈ E, c i) * (10 : ℤ) ^ e := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hfactor] at hslice
  have hcoeff := (mul_eq_zero.mp hslice).resolve_right
    (pow_ne_zero _ (by norm_num))
  simpa [E] using hcoeff

/-- A four-token signed decimal value with fixed signs `(+,+,-,-)` determines
the two positive and two negative exponent multisets whenever the target has
four distinct exponents.  This is the bounded base-ten uniqueness lemma needed
for ambient primitive fibers. -/
theorem fourTokenSign_value_unique_of_target_injective
    (u v : Fin 4 → ℕ) (hv : Function.Injective v)
    (hval : signedDecimalValue fourTokenSign u =
      signedDecimalValue fourTokenSign v) :
    ((u 0 = v 0 ∧ u 1 = v 1) ∨ (u 0 = v 1 ∧ u 1 = v 0)) ∧
      ((u 2 = v 2 ∧ u 3 = v 3) ∨ (u 2 = v 3 ∧ u 3 = v 2)) := by
  let a : Fin 8 → ℕ := ![u 0, u 1, u 2, u 3, v 0, v 1, v 2, v 3]
  let c : Fin 8 → ℤ := ![1, 1, -1, -1, -1, -1, 1, 1]
  have hc : ∀ i, (c i).natAbs ≤ 1 := by
    intro i
    fin_cases i <;> simp [c]
  have hsum : ∑ i, c i * (10 : ℤ) ^ a i = 0 := by
    simp [a, c, signedDecimalValue, Fin.sum_univ_eight,
      Fin.sum_univ_four, fourTokenSign] at hval ⊢
    linarith
  have hv_ne {i j : Fin 4} (hij : i ≠ j) : v i ≠ v j := by
    exact fun h => hij (hv h)
  have balance (e : ℕ) :
      ∑ i ∈ Finset.univ.filter (fun i => a i = e), c i = 0 :=
    eightToken_coefficient_balance a c hc hsum e
  have h0 := balance (v 0)
  have h1 := balance (v 1)
  have h2 := balance (v 2)
  have h3 := balance (v 3)
  simp only [Finset.sum_filter] at h0 h1 h2 h3
  simp [a, c, Fin.sum_univ_eight, hv_ne] at h0 h1 h2 h3
  have hp0 : u 0 = v 0 ∨ u 1 = v 0 := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at h0
    split_ifs at h0 <;> omega
  have hp1 : u 0 = v 1 ∨ u 1 = v 1 := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at h1
    split_ifs at h1 <;> omega
  have hn2 : u 2 = v 2 ∨ u 3 = v 2 := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at h2
    split_ifs at h2 <;> omega
  have hn3 : u 2 = v 3 ∨ u 3 = v 3 := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at h3
    split_ifs at h3 <;> omega
  constructor
  · rcases hp0 with h00 | h10 <;> rcases hp1 with h01 | h11
    · exact (hv_ne (by decide) (h00.symm.trans h01)).elim
    · exact Or.inl ⟨h00, h11⟩
    · exact Or.inr ⟨h01, h10⟩
    · exact (hv_ne (by decide) (h10.symm.trans h11)).elim
  · rcases hn2 with h22 | h32 <;> rcases hn3 with h23 | h33
    · exact (hv_ne (by decide) (h22.symm.trans h23)).elim
    · exact Or.inl ⟨h22, h33⟩
    · exact Or.inr ⟨h23, h32⟩
    · exact (hv_ne (by decide) (h32.symm.trans h33)).elim

/-- Residue-1 positive value `10^x4+10^x1-10^x2-10^x3`. -/
def residueOneValue (x : BoxQuartet) : ℕ :=
  (10 ^ boxX4 x - 10 ^ boxX3 x) -
    (10 ^ boxX2 x - 10 ^ boxX1 x)

/-- Residue-9 positive value `10^x4+10^x2-10^x1-10^x3`. -/
def residueNineValue (x : BoxQuartet) : ℕ :=
  (10 ^ boxX4 x - 10 ^ boxX3 x) +
    (10 ^ boxX2 x - 10 ^ boxX1 x)

/-- Explicit reduced tails witnessing primitive residues one and nine. -/
def residueOneTail (x : BoxQuartet) : ℕ :=
  (10 ^ (boxX4 x - boxX1 x - 1) -
      10 ^ (boxX3 x - boxX1 x - 1)) -
    10 ^ (boxX2 x - boxX1 x - 1)

def residueNineTail (x : BoxQuartet) : ℕ :=
  (10 ^ (boxX4 x - boxX1 x - 1) -
      10 ^ (boxX3 x - boxX1 x - 1)) +
    (10 ^ (boxX2 x - boxX1 x - 1) - 1)

/-- The four exact positive record pairs over a residue-1 value. -/
def residueOnePair (x : BoxQuartet) : FiberRow → PrimitiveRecordPair
  | .row00 => (coordinateRecord (boxX4 x) (boxX2 x),
      coordinateRecord (boxX3 x) (boxX1 x))
  | .row01 => (coordinateRecord (boxX4 x) (boxX3 x),
      coordinateRecord (boxX2 x) (boxX1 x))
  | .row10 => (coordinateRecord (boxX1 x) (boxX2 x),
      coordinateRecord (boxX3 x) (boxX4 x))
  | .row11 => (coordinateRecord (boxX1 x) (boxX3 x),
      coordinateRecord (boxX2 x) (boxX4 x))

/-- The four exact positive record pairs over a residue-9 value. -/
def residueNinePair (x : BoxQuartet) : FiberRow → PrimitiveRecordPair
  | .row00 => (coordinateRecord (boxX4 x) (boxX1 x),
      coordinateRecord (boxX3 x) (boxX2 x))
  | .row01 => (coordinateRecord (boxX4 x) (boxX3 x),
      coordinateRecord (boxX1 x) (boxX2 x))
  | .row10 => (coordinateRecord (boxX2 x) (boxX1 x),
      coordinateRecord (boxX3 x) (boxX4 x))
  | .row11 => (coordinateRecord (boxX2 x) (boxX3 x),
      coordinateRecord (boxX1 x) (boxX4 x))

/-- Exact residue-1 selected primitive record subdomain. -/
def residueOneRecordDomain (t : ℕ) : Finset PrimitiveRecordPair :=
  (boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow)).image
    (fun xr => residueOnePair xr.1 xr.2)

/-- Exact residue-9 selected primitive record subdomain. -/
def residueNineRecordDomain (t : ℕ) : Finset PrimitiveRecordPair :=
  (boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow)).image
    (fun xr => residueNinePair xr.1 xr.2)

/-- The selected four-row residue-1 image over one fixed quartet. -/
def residueOneFiber (x : BoxQuartet) : Finset PrimitiveRecordPair :=
  (Finset.univ : Finset FiberRow).image (residueOnePair x)

/-- The selected four-row residue-9 image over one fixed quartet. -/
def residueNineFiber (x : BoxQuartet) : Finset PrimitiveRecordPair :=
  (Finset.univ : Finset FiberRow).image (residueNinePair x)

/-- The full T49 primitive value fiber over one residue-one box value. -/
def residueOneAmbientFiber (Q0 t : ℕ) (x : BoxQuartet) :
    Finset PrimitiveRecordPair :=
  (primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t)).filter
    (fun p => blockDifferenceValue p = residueOneValue x)

/-- The full T49 primitive value fiber over one residue-nine box value. -/
def residueNineAmbientFiber (Q0 t : ℕ) (x : BoxQuartet) :
    Finset PrimitiveRecordPair :=
  (primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t)).filter
    (fun p => blockDifferenceValue p = residueNineValue x)

/-- The high-coordinate and low-coordinate positive lacunary gaps. -/
def upperGap (x : BoxQuartet) : ℕ := 10 ^ boxX4 x - 10 ^ boxX3 x
def lowerGap (x : BoxQuartet) : ℕ := 10 ^ boxX2 x - 10 ^ boxX1 x

/-- One real correlation across the upper two coordinate intervals. -/
def upperCorrelation (t h : ℕ) : ℝ :=
  ∑ x3 ∈ boxInterval3 t, ∑ x4 ∈ boxInterval4 t,
    Real.cos (2 * Real.pi ^ 2 * h * (10 ^ x4 - 10 ^ x3))

/-- One real correlation across the lower two coordinate intervals. -/
def lowerCorrelation (t h : ℕ) : ℝ :=
  ∑ x1 ∈ boxInterval1 t, ∑ x2 ∈ boxInterval2 t,
    Real.cos (2 * Real.pi ^ 2 * h * (10 ^ x2 - 10 ^ x1))

/-- The exact ten-frequency lower-dimensional cross sum over the literal
quartet box. The theorem `EBox_eq_crossCorrelations` gives its product form. -/
def EBox (t : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10, ∑ x ∈ boxQuartetDomain t,
    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
      Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (lowerGap x : ℝ))

/-- The explicit hypothesis left unproved by T56. The constant is uniform in
the dyadic exponent `t`. -/
def EBoxBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ t : ℕ, |EBox t| ≤ C * (boxLength t : ℝ) ^ 3

/-- The selected fiber-parameter contribution, with four rows per quartet and
T49's single swapped-off-diagonal factor `2` retained literally. -/
def boxSignedContribution (Q0 t : ℕ) : ℝ :=
  2 * (∑ xr ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow),
    (inclusiveRealKernel 1 (blockDifferenceValue (residueOnePair xr.1 xr.2))
        Real.pi +
      inclusiveRealKernel 1 (blockDifferenceValue (residueNinePair xr.1 xr.2))
        Real.pi) / widthWeight (boxBlock t))

/-- The same selected contribution summed over the deduplicated record images. -/
def boxDeduplicatedSignedContribution (Q0 t : ℕ) : ℝ :=
  2 * ((∑ p ∈ residueOneRecordDomain t,
      inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
        widthWeight (boxBlock t)) +
    ∑ p ∈ residueNineRecordDomain t,
      inclusiveRealKernel 1 (blockDifferenceValue p) Real.pi /
        widthWeight (boxBlock t))

theorem boxLength_pos (t : ℕ) : 0 < boxLength t := by
  simp [boxLength]

theorem boxEndpoint_pos (t : ℕ) : 1 ≤ boxEndpoint t := by
  simp [boxEndpoint]

theorem translatedCanonicalBlocks_boxEndpoint (t : ℕ) :
    translatedCanonicalBlocks (boxEndpoint t) = [boxBlock t] := by
  show canonicalDyadicPartition (boxEndpoint t) = [boxBlock t]
  unfold canonicalDyadicPartition boxEndpoint boxLength boxBlock
  rw [Nat.add_sub_cancel]
  rw [show (4 * 2 ^ t : ℕ) = 2 ^ (t + 2) from by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, Nat.add_comm]]
  rw [Nat.bitIndices_two_pow, List.reverse_singleton]
  simp only [dyadicPartitionFrom, Nat.zero_add]

theorem boxBlock_mem_translatedCanonicalBlocks (t : ℕ) :
    boxBlock t ∈ translatedCanonicalBlocks (boxEndpoint t) := by
  rw [translatedCanonicalBlocks_boxEndpoint]
  simp

theorem boxBlock_endpoints (t : ℕ) :
    (boxBlock t).start = 1 ∧ (boxBlock t).finish = boxEndpoint t := by
  constructor
  · rfl
  · simp [boxBlock, boxEndpoint, boxLength, DyadicBlock.finish,
      DyadicBlock.blockLength]
    ring

theorem boxWidth_literal (t : ℕ) :
    widthWeight (boxBlock t) =
      Real.sqrt ((boxEndpoint t : ℝ) ^ 2 - 1) := by
  rw [widthWeight_eq_endpoints]
  rw [(boxBlock_endpoints t).1, (boxBlock_endpoints t).2]
  norm_num

theorem boxInclusiveFrequencies :
    inclusiveFrequencies 1 = Finset.Icc 1 10 := by
  simp [inclusiveFrequencies, decimalFrequency]

theorem mem_boxQuartetDomain_iff {t : ℕ} {x : BoxQuartet} :
    x ∈ boxQuartetDomain t ↔
      1 ≤ boxX1 x ∧ boxX1 x ≤ boxLength t ∧
      boxLength t + 1 ≤ boxX2 x ∧ boxX2 x ≤ 2 * boxLength t ∧
      2 * boxLength t + 1 ≤ boxX3 x ∧ boxX3 x ≤ 3 * boxLength t ∧
      3 * boxLength t + 1 ≤ boxX4 x ∧ boxX4 x ≤ 4 * boxLength t := by
  simp [boxQuartetDomain, boxInterval1, boxInterval2, boxInterval3,
    boxInterval4, boxX1, boxX2, boxX3, boxX4, and_assoc]

theorem boxQuartet_ordered {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) :
    1 ≤ boxX1 x ∧ boxX1 x < boxX2 x ∧ boxX2 x < boxX3 x ∧
      boxX3 x < boxX4 x ∧ boxX4 x < boxEndpoint t := by
  have h := mem_boxQuartetDomain_iff.mp hx
  have hL := boxLength_pos t
  simp only [boxEndpoint]
  omega

theorem coordinateRecord_audit {x y : ℕ} (hxy : x ≠ y) :
    orderedFirst (coordinateRecord x y) = x ∧
      orderedSecond (coordinateRecord x y) = y ∧
      signedDecimalFrequency (coordinateRecord x y) =
        (10 : ℤ) ^ x - (10 : ℤ) ^ y := by
  by_cases hyx : y < x
  · simp [coordinateRecord, hyx, orderedFirst, orderedSecond,
      signedDecimalFrequency, positiveDecimalFrequency_int_eq]
    omega
  · have hxy' : x < y := by omega
    simp [coordinateRecord, hyx, orderedFirst, orderedSecond,
      signedDecimalFrequency, positiveDecimalFrequency_int_eq]
    omega

theorem coordinateRecord_coordinates (x y : ℕ) :
    orderedFirst (coordinateRecord x y) = x ∧
      orderedSecond (coordinateRecord x y) = y := by
  by_cases hyx : y < x
  · simp [coordinateRecord, hyx, orderedFirst, orderedSecond]
    omega
  · simp [coordinateRecord, hyx, orderedFirst, orderedSecond]
    omega

theorem coordinateRecord_eq_iff {x y u v : ℕ} :
    coordinateRecord x y = coordinateRecord u v ↔ x = u ∧ y = v := by
  constructor
  · intro h
    have hfirst := congrArg orderedFirst h
    have hsecond := congrArg orderedSecond h
    rw [(coordinateRecord_coordinates x y).1,
      (coordinateRecord_coordinates u v).1] at hfirst
    rw [(coordinateRecord_coordinates x y).2,
      (coordinateRecord_coordinates u v).2] at hsecond
    exact ⟨hfirst, hsecond⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The four residue-one rows are exactly the two positive-label and two
negative-label permutations of one labeled exponent support. -/
theorem residueOne_exponent_rows (x : BoxQuartet) :
    blockDifferenceExponent (residueOnePair x .row00) =
        ![boxX4 x, boxX1 x, boxX2 x, boxX3 x] ∧
      blockDifferenceExponent (residueOnePair x .row01) =
        ![boxX4 x, boxX1 x, boxX3 x, boxX2 x] ∧
      blockDifferenceExponent (residueOnePair x .row10) =
        ![boxX1 x, boxX4 x, boxX2 x, boxX3 x] ∧
      blockDifferenceExponent (residueOnePair x .row11) =
        ![boxX1 x, boxX4 x, boxX3 x, boxX2 x] := by
  repeat' apply And.intro
  all_goals
    funext i
    fin_cases i <;>
      simp [blockDifferenceExponent, residueOnePair,
        coordinateRecord_coordinates]

/-- The four residue-nine rows are exactly the corresponding two-by-two
label permutations of their exponent support. -/
theorem residueNine_exponent_rows (x : BoxQuartet) :
    blockDifferenceExponent (residueNinePair x .row00) =
        ![boxX4 x, boxX2 x, boxX1 x, boxX3 x] ∧
      blockDifferenceExponent (residueNinePair x .row01) =
        ![boxX4 x, boxX2 x, boxX3 x, boxX1 x] ∧
      blockDifferenceExponent (residueNinePair x .row10) =
        ![boxX2 x, boxX4 x, boxX1 x, boxX3 x] ∧
      blockDifferenceExponent (residueNinePair x .row11) =
        ![boxX2 x, boxX4 x, boxX3 x, boxX1 x] := by
  repeat' apply And.intro
  all_goals
    funext i
    fin_cases i <;>
      simp [blockDifferenceExponent, residueNinePair,
        coordinateRecord_coordinates]

/-- T31's record difference is exactly T16's labeled signed four-token value. -/
theorem signedDecimalValue_blockDifferenceExponent (p : PrimitiveRecordPair) :
    signedDecimalValue fourTokenSign (blockDifferenceExponent p) =
      signedDecimalFrequency p.1 - signedDecimalFrequency p.2 := by
  rw [signedDecimalFrequency_eq_orderedPhaseFrequency,
    signedDecimalFrequency_eq_orderedPhaseFrequency]
  simp [signedDecimalValue, fourTokenSign, blockDifferenceExponent,
    orderedPhaseFrequency, Fin.sum_univ_four]
  ring

/-- Positive record pairs are determined by their four labeled exponents. -/
theorem blockPositiveRecordPair_eq_of_exponent_eq
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    {p q : PrimitiveRecordPair}
    (hp : p ∈ blockPositiveDifferenceDomain μ c Q0 m N B)
    (hq : q ∈ blockPositiveDifferenceDomain μ c Q0 m N B)
    (h : blockDifferenceExponent p = blockDifferenceExponent q) : p = q := by
  let pp : ↥(blockPositiveDifferenceDomain μ c Q0 m N B) := ⟨p, hp⟩
  let qq : ↥(blockPositiveDifferenceDomain μ c Q0 m N B) := ⟨q, hq⟩
  have hvec : blockDifferenceVector pp = blockDifferenceVector qq := by
    funext i
    apply Fin.ext
    have hi := congrFun h i
    have hpExp := congrFun (exponentNat_blockDifferenceVector pp) i
    have hqExp := congrFun (exponentNat_blockDifferenceVector qq) i
    simpa [exponentNat] using hpExp.trans (hi.trans hqExp.symm)
  exact congrArg Subtype.val (blockDifferenceVector_injective hvec)

theorem coordinateRecord_orientation {x y : ℕ} (hxy : x ≠ y) :
    (coordinateRecord x y).1 = decide (y < x) := by
  by_cases hyx : y < x
  · simp [coordinateRecord, hyx]
  · simp [coordinateRecord, hyx]

theorem coordinateRecord_endpoint {x y : ℕ} (hxy : x ≠ y) :
    frequencyEndpoint (coordinateRecord x y).2 = max x y := by
  by_cases hyx : y < x
  · simp [coordinateRecord, hyx, frequencyEndpoint]
    omega
  · have hxy' : x < y := by omega
    simp [coordinateRecord, hyx, frequencyEndpoint]
    omega

theorem coordinateRecord_mem_boxBlock
    (Q0 t x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxN : x < boxEndpoint t) (hyN : y < boxEndpoint t) (hxy : x ≠ y) :
    coordinateRecord x y ∈ blockRecordDomain 8 1 Q0 1 (boxBlock t) := by
  rw [mem_blockRecordDomain_iff]
  have hq : coordinateRecord x y ∈
      orderedLongPairDomain 8 1 Q0 1 (boxEndpoint t) := by
    rw [mem_orderedLongPairDomain_eight_one_one_iff]
    rw [(coordinateRecord_audit hxy).1,
      (coordinateRecord_audit hxy).2.1]
    exact ⟨hxN, hyN, hxy⟩
  have hqspec := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq
  have hadm := hqspec.1
  refine ⟨hadm, ?_, ?_⟩
  · rw [(boxBlock_endpoints t).1, coordinateRecord_endpoint hxy]
    omega
  · rw [(boxBlock_endpoints t).2]
    exact hqspec.2

theorem tenPow_gap_dominates {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    10 ^ b - 10 ^ a < 10 ^ d - 10 ^ c := by
  have hca : 10 ^ a < 10 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hbcPow : 10 ^ b < 10 ^ c := Nat.pow_lt_pow_right (by omega) hbc
  have hstep : 10 ^ (c + 1) ≤ 10 ^ d :=
    pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) (by omega)
  rw [pow_succ] at hstep
  have hcpos : 0 < 10 ^ c := pow_pos (by norm_num) _
  have hleft : 10 ^ b - 10 ^ a < 10 ^ c :=
    (Nat.sub_le (10 ^ b) (10 ^ a)).trans_lt hbcPow
  have hright : 10 ^ c ≤ 10 ^ d - 10 ^ c := by omega
  exact hleft.trans_le hright

theorem tenPow_lt_laterGap {b c d : ℕ} (hbc : b < c) (hcd : c < d) :
    10 ^ b < 10 ^ d - 10 ^ c := by
  have hbcPow : 10 ^ b < 10 ^ c := Nat.pow_lt_pow_right (by omega) hbc
  have hstep : 10 ^ (c + 1) ≤ 10 ^ d :=
    pow_le_pow_right' (by norm_num : 0 < (10 : ℕ)) (by omega)
  rw [pow_succ] at hstep
  have hcpos : 0 < 10 ^ c := pow_pos (by norm_num) _
  have hright : 10 ^ c ≤ 10 ^ d - 10 ^ c := by omega
  exact hbcPow.trans_le hright

theorem tenPow_shift_factor {a b : ℕ} (hab : a < b) :
    10 ^ b = 10 ^ a * (10 * 10 ^ (b - a - 1)) := by
  have he : b = a + (b - a - 1) + 1 := by omega
  calc
    10 ^ b = 10 ^ (a + (b - a - 1) + 1) :=
      congrArg (fun n : ℕ => 10 ^ n) he
    _ = 10 ^ a * (10 * 10 ^ (b - a - 1)) := by
      rw [pow_add, pow_succ]
      ring

theorem residue_factorizations {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) :
    residueOneValue x = 10 ^ boxX1 x * (1 + 10 * residueOneTail x) ∧
      residueNineValue x = 10 ^ boxX1 x * (9 + 10 * residueNineTail x) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h14 : boxX1 x < boxX4 x := h13.trans h34
  let bp := 10 ^ (boxX2 x - boxX1 x - 1)
  let cp := 10 ^ (boxX3 x - boxX1 x - 1)
  let dp := 10 ^ (boxX4 x - boxX1 x - 1)
  have hebc : boxX2 x - boxX1 x - 1 < boxX3 x - boxX1 x - 1 := by omega
  have hecd : boxX3 x - boxX1 x - 1 < boxX4 x - boxX1 x - 1 := by omega
  have htail : bp < dp - cp := by
    exact tenPow_lt_laterGap hebc hecd
  have hbp : 1 ≤ bp := one_le_pow₀ (by norm_num)
  have hcpdp : cp ≤ dp := by
    exact pow_le_pow_right' (by norm_num) hecd.le
  have hpow2 := tenPow_shift_factor h12
  have hpow3 := tenPow_shift_factor h13
  have hpow4 := tenPow_shift_factor h14
  dsimp [bp, cp, dp] at htail hbp hcpdp hpow2 hpow3 hpow4
  constructor
  · unfold residueOneValue residueOneTail
    rw [hpow2, hpow3, hpow4]
    have hAC : 10 ^ boxX1 x * (10 * 10 ^ (boxX3 x - boxX1 x - 1)) ≤
        10 ^ boxX1 x * (10 * 10 ^ (boxX4 x - boxX1 x - 1)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcpdp)
    have hAB : 10 ^ boxX1 x ≤
        10 ^ boxX1 x * (10 * 10 ^ (boxX2 x - boxX1 x - 1)) := by
      calc
        10 ^ boxX1 x = 10 ^ boxX1 x * 1 := by ring
        _ ≤ 10 ^ boxX1 x *
            (10 * 10 ^ (boxX2 x - boxX1 x - 1)) := by
          apply Nat.mul_le_mul_left
          omega
    have hsmall :
        10 ^ boxX1 x * (10 * 10 ^ (boxX2 x - boxX1 x - 1)) -
            10 ^ boxX1 x ≤
          10 ^ boxX1 x * (10 * 10 ^ (boxX4 x - boxX1 x - 1)) -
            10 ^ boxX1 x * (10 * 10 ^ (boxX3 x - boxX1 x - 1)) := by
      calc
        10 ^ boxX1 x * (10 * 10 ^ (boxX2 x - boxX1 x - 1)) -
            10 ^ boxX1 x =
            10 ^ boxX1 x *
              (10 * 10 ^ (boxX2 x - boxX1 x - 1) - 1) := by
          rw [Nat.mul_sub_left_distrib]
          simp
        _ ≤ 10 ^ boxX1 x *
            (10 * (10 ^ (boxX4 x - boxX1 x - 1) -
              10 ^ (boxX3 x - boxX1 x - 1))) := by
          apply Nat.mul_le_mul_left
          omega
        _ = 10 ^ boxX1 x *
              (10 * 10 ^ (boxX4 x - boxX1 x - 1)) -
            10 ^ boxX1 x *
              (10 * 10 ^ (boxX3 x - boxX1 x - 1)) := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    apply Nat.cast_injective (R := ℤ)
    push_cast [hAC, hAB, hsmall, hcpdp, htail.le]
    ring
  · unfold residueNineValue residueNineTail
    rw [hpow2, hpow3, hpow4]
    have hAC : 10 ^ boxX1 x * (10 * 10 ^ (boxX3 x - boxX1 x - 1)) ≤
        10 ^ boxX1 x * (10 * 10 ^ (boxX4 x - boxX1 x - 1)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcpdp)
    have hAB : 10 ^ boxX1 x ≤
        10 ^ boxX1 x * (10 * 10 ^ (boxX2 x - boxX1 x - 1)) := by
      calc
        10 ^ boxX1 x = 10 ^ boxX1 x * 1 := by ring
        _ ≤ 10 ^ boxX1 x *
            (10 * 10 ^ (boxX2 x - boxX1 x - 1)) := by
          apply Nat.mul_le_mul_left
          omega
    apply Nat.cast_injective (R := ℤ)
    push_cast [hAC, hAB, hcpdp, hbp]
    ring

/-- Exact decimal valuation and primitive residues after removing the full
power `10^x1`; the witnesses are the explicit tails above. -/
theorem residue_valuation_primitive_audit
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    tenValuation (residueOneValue x) = boxX1 x ∧
      tenPrimitivePart (residueOneValue x) = 1 + 10 * residueOneTail x ∧
      tenPrimitivePart (residueOneValue x) % 10 = 1 ∧
    tenValuation (residueNineValue x) = boxX1 x ∧
      tenPrimitivePart (residueNineValue x) = 9 + 10 * residueNineTail x ∧
      tenPrimitivePart (residueNineValue x) % 10 = 9 := by
  have hfactor := residue_factorizations hx
  have hv1 : tenValuation (residueOneValue x) = boxX1 x := by
    rw [hfactor.1]
    exact tenValuation_lowDecimalCoefficient (boxX1 x) (residueOneTail x) 1
      (Or.inl rfl)
  have hv9 : tenValuation (residueNineValue x) = boxX1 x := by
    rw [hfactor.2]
    exact tenValuation_lowDecimalCoefficient (boxX1 x) (residueNineTail x) 9
      (Or.inr (Or.inr (Or.inr rfl)))
  have hp1 : tenPrimitivePart (residueOneValue x) =
      1 + 10 * residueOneTail x := by
    have hred := ten_reduction (residueOneValue x)
    rw [hv1] at hred
    have hmul : 10 ^ boxX1 x * tenPrimitivePart (residueOneValue x) =
        10 ^ boxX1 x * (1 + 10 * residueOneTail x) :=
      hred.trans hfactor.1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul
  have hp9 : tenPrimitivePart (residueNineValue x) =
      9 + 10 * residueNineTail x := by
    have hred := ten_reduction (residueNineValue x)
    rw [hv9] at hred
    have hmul : 10 ^ boxX1 x * tenPrimitivePart (residueNineValue x) =
        10 ^ boxX1 x * (9 + 10 * residueNineTail x) :=
      hred.trans hfactor.2
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul
  refine ⟨hv1, hp1, ?_, hv9, hp9, ?_⟩
  · rw [hp1]
    omega
  · rw [hp9]
    omega

theorem residueValues_positive {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) :
    0 < residueOneValue x ∧ 0 < residueNineValue x := by
  have h := boxQuartet_ordered hx
  have hdom := tenPow_gap_dominates h.2.1 h.2.2.1 h.2.2.2.1
  unfold residueOneValue residueNineValue
  constructor <;> omega

theorem residueOnePair_records_mem
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    (residueOnePair x row).1 ∈ blockRecordDomain 8 1 Q0 1 (boxBlock t) ∧
      (residueOnePair x row).2 ∈ blockRecordDomain 8 1 Q0 1 (boxBlock t) := by
  have h := boxQuartet_ordered hx
  cases row <;> simp only [residueOnePair] <;> constructor <;>
    apply coordinateRecord_mem_boxBlock <;> omega

theorem residueNinePair_records_mem
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    (residueNinePair x row).1 ∈ blockRecordDomain 8 1 Q0 1 (boxBlock t) ∧
      (residueNinePair x row).2 ∈ blockRecordDomain 8 1 Q0 1 (boxBlock t) := by
  have h := boxQuartet_ordered hx
  cases row <;> simp only [residueNinePair] <;> constructor <;>
    apply coordinateRecord_mem_boxBlock <;> omega

theorem residueOne_signedDifference
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    signedDecimalFrequency (residueOnePair x row).1 -
        signedDecimalFrequency (residueOnePair x row).2 =
      (residueOneValue x : ℤ) := by
  have h := boxQuartet_ordered hx
  have hdom := tenPow_gap_dominates h.2.1 h.2.2.1 h.2.2.2.1
  have hba : 10 ^ boxX1 x ≤ 10 ^ boxX2 x := by
    exact pow_le_pow_right' (by norm_num) h.2.1.le
  have hcd : 10 ^ boxX3 x ≤ 10 ^ boxX4 x := by
    exact pow_le_pow_right' (by norm_num) h.2.2.2.1.le
  have hsub : 10 ^ boxX2 x - 10 ^ boxX1 x ≤
      10 ^ boxX4 x - 10 ^ boxX3 x := hdom.le
  cases row <;> simp only [residueOnePair] <;>
    rw [(coordinateRecord_audit (by omega)).2.2,
      (coordinateRecord_audit (by omega)).2.2] <;>
    unfold residueOneValue <;> push_cast [hba, hcd, hsub] <;> ring

theorem residueNine_signedDifference
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    signedDecimalFrequency (residueNinePair x row).1 -
        signedDecimalFrequency (residueNinePair x row).2 =
      (residueNineValue x : ℤ) := by
  have h := boxQuartet_ordered hx
  have hba : 10 ^ boxX1 x ≤ 10 ^ boxX2 x := by
    exact pow_le_pow_right' (by norm_num) h.2.1.le
  have hcd : 10 ^ boxX3 x ≤ 10 ^ boxX4 x := by
    exact pow_le_pow_right' (by norm_num) h.2.2.2.1.le
  cases row <;> simp only [residueNinePair] <;>
    rw [(coordinateRecord_audit (by omega)).2.2,
      (coordinateRecord_audit (by omega)).2.2] <;>
    unfold residueNineValue <;> push_cast [hba, hcd] <;> ring

theorem residueOne_exponent_sign_audit
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    Noncancelling fourTokenSign
      (blockDifferenceExponent (residueOnePair x row)) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h24 : boxX2 x < boxX4 x := h23.trans h34
  have h14 : boxX1 x < boxX4 x := h13.trans h34
  unfold Noncancelling
  intro i j hij
  cases row <;> fin_cases i <;> fin_cases j <;>
    simp [residueOnePair, blockDifferenceExponent, coordinateRecord,
      orderedFirst, orderedSecond, fourTokenSign, h12, h13, h14, h23, h24, h34,
      not_lt_of_ge h12.le, not_lt_of_ge h13.le,
      not_lt_of_ge h14.le, not_lt_of_ge h23.le,
      not_lt_of_ge h24.le, not_lt_of_ge h34.le] at hij ⊢ <;> omega

theorem residueNine_exponent_sign_audit
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    Noncancelling fourTokenSign
      (blockDifferenceExponent (residueNinePair x row)) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h24 : boxX2 x < boxX4 x := h23.trans h34
  have h14 : boxX1 x < boxX4 x := h13.trans h34
  unfold Noncancelling
  intro i j hij
  cases row <;> fin_cases i <;> fin_cases j <;>
    simp [residueNinePair, blockDifferenceExponent, coordinateRecord,
      orderedFirst, orderedSecond, fourTokenSign, h12, h13, h14, h23, h24, h34,
      not_lt_of_ge h12.le, not_lt_of_ge h13.le,
      not_lt_of_ge h14.le, not_lt_of_ge h23.le,
      not_lt_of_ge h24.le, not_lt_of_ge h34.le] at hij ⊢ <;> omega

theorem residueOnePair_mem_primitiveRecordDomain
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    residueOnePair x row ∈
      primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) := by
  classical
  unfold primitiveRecordDomain primitiveBlockDifferenceDomain
  rw [Finset.mem_filter]
  constructor
  · unfold blockPositiveDifferenceDomain
    rw [Finset.mem_filter, Finset.mem_product]
    have hrec := residueOnePair_records_mem Q0 hx row
    have hB := boxBlock_mem_translatedCanonicalBlocks t
    rw [blockOrderedDomain_eq_blockRecordDomain hB]
    refine ⟨hrec, ?_⟩
    have hdiff := residueOne_signedDifference hx row
    have hpos : (0 : ℤ) < residueOneValue x := by
      exact_mod_cast (residueValues_positive hx).1
    omega
  · exact residueOne_exponent_sign_audit hx row

theorem residueNinePair_mem_primitiveRecordDomain
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    residueNinePair x row ∈
      primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) := by
  classical
  unfold primitiveRecordDomain primitiveBlockDifferenceDomain
  rw [Finset.mem_filter]
  constructor
  · unfold blockPositiveDifferenceDomain
    rw [Finset.mem_filter, Finset.mem_product]
    have hrec := residueNinePair_records_mem Q0 hx row
    have hB := boxBlock_mem_translatedCanonicalBlocks t
    rw [blockOrderedDomain_eq_blockRecordDomain hB]
    refine ⟨hrec, ?_⟩
    have hdiff := residueNine_signedDifference hx row
    have hpos : (0 : ℤ) < residueNineValue x := by
      exact_mod_cast (residueValues_positive hx).2
    omega
  · exact residueNine_exponent_sign_audit hx row

theorem residueOne_blockDifferenceValue
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    blockDifferenceValue (residueOnePair x row) = residueOneValue x := by
  have hp := primitiveBlockDifferenceDomain_subset
    (residueOnePair_mem_primitiveRecordDomain Q0 hx row)
  have hcast := blockPositiveDifferenceValue_cast hp
  rw [residueOne_signedDifference hx row] at hcast
  exact_mod_cast hcast

theorem residueNine_blockDifferenceValue
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    blockDifferenceValue (residueNinePair x row) = residueNineValue x := by
  have hp := primitiveBlockDifferenceDomain_subset
    (residueNinePair_mem_primitiveRecordDomain Q0 hx row)
  have hcast := blockPositiveDifferenceValue_cast hp
  rw [residueNine_signedDifference hx row] at hcast
  exact_mod_cast hcast

/-- Every one of the four rows has the same exact valuation and primitive
residue. The record domain and `Q0` remain explicit through the value lemmas. -/
theorem residue_record_valuation_fiber_audit
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t)
    (row : FiberRow) :
    tenValuation (blockDifferenceValue (residueOnePair x row)) = boxX1 x ∧
      tenPrimitivePart (blockDifferenceValue (residueOnePair x row)) % 10 = 1 ∧
      tenValuation (blockDifferenceValue (residueNinePair x row)) = boxX1 x ∧
      tenPrimitivePart (blockDifferenceValue (residueNinePair x row)) % 10 = 9 := by
  rw [residueOne_blockDifferenceValue Q0 hx row,
    residueNine_blockDifferenceValue Q0 hx row]
  have h := residue_valuation_primitive_audit hx
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem residueOnePair_injective {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) :
    Function.Injective (residueOnePair x) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h24 : boxX2 x < boxX4 x := h23.trans h34
  have h14 : boxX1 x < boxX4 x := h13.trans h34
  intro r s hrs
  cases r <;> cases s <;>
    simp [residueOnePair, coordinateRecord, h12, h13, h14, h23, h24, h34,
      not_lt_of_ge h12.le, not_lt_of_ge h13.le,
      not_lt_of_ge h14.le, not_lt_of_ge h23.le,
      not_lt_of_ge h24.le, not_lt_of_ge h34.le] at hrs ⊢ <;> omega

theorem residueNinePair_injective {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) :
    Function.Injective (residueNinePair x) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h24 : boxX2 x < boxX4 x := h23.trans h34
  have h14 : boxX1 x < boxX4 x := h13.trans h34
  intro r s hrs
  cases r <;> cases s <;>
    simp [residueNinePair, coordinateRecord, h12, h13, h14, h23, h24, h34,
      not_lt_of_ge h12.le, not_lt_of_ge h13.le,
      not_lt_of_ge h14.le, not_lt_of_ge h23.le,
      not_lt_of_ge h24.le, not_lt_of_ge h34.le] at hrs ⊢ <;> omega

theorem residueOnePair_injective_on_parameters {t : ℕ}
    {xr ys : BoxQuartet × FiberRow}
    (hxr : xr ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow))
    (hys : ys ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow))
    (hp : residueOnePair xr.1 xr.2 = residueOnePair ys.1 ys.2) :
    xr = ys := by
  have hxd := mem_boxQuartetDomain_iff.mp (Finset.mem_product.mp hxr).1
  have hyd := mem_boxQuartetDomain_iff.mp (Finset.mem_product.mp hys).1
  have hx := boxQuartet_ordered (Finset.mem_product.mp hxr).1
  have hy := boxQuartet_ordered (Finset.mem_product.mp hys).1
  rcases xr with ⟨⟨⟨⟨x1, x2⟩, x3⟩, x4⟩, r⟩
  rcases ys with ⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, s⟩
  simp only [boxX1, boxX2, boxX3, boxX4] at hxd hyd hx hy hp ⊢
  cases r <;> cases s <;>
    simp only [residueOnePair, boxX1, boxX2, boxX3, boxX4,
      Prod.mk.injEq, coordinateRecord_eq_iff] at hp <;>
    simp_all only [Prod.mk.injEq] <;>
    omega

theorem residueNinePair_injective_on_parameters {t : ℕ}
    {xr ys : BoxQuartet × FiberRow}
    (hxr : xr ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow))
    (hys : ys ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow))
    (hp : residueNinePair xr.1 xr.2 = residueNinePair ys.1 ys.2) :
    xr = ys := by
  have hxd := mem_boxQuartetDomain_iff.mp (Finset.mem_product.mp hxr).1
  have hyd := mem_boxQuartetDomain_iff.mp (Finset.mem_product.mp hys).1
  have hx := boxQuartet_ordered (Finset.mem_product.mp hxr).1
  have hy := boxQuartet_ordered (Finset.mem_product.mp hys).1
  rcases xr with ⟨⟨⟨⟨x1, x2⟩, x3⟩, x4⟩, r⟩
  rcases ys with ⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, s⟩
  simp only [boxX1, boxX2, boxX3, boxX4] at hxd hyd hx hy hp ⊢
  cases r <;> cases s <;>
    simp only [residueNinePair, boxX1, boxX2, boxX3, boxX4,
      Prod.mk.injEq, coordinateRecord_eq_iff] at hp <;>
    simp_all only [Prod.mk.injEq] <;>
    omega

theorem boxQuartetDomain_card (t : ℕ) :
    (boxQuartetDomain t).card = boxLength t ^ 4 := by
  have h1 : (boxInterval1 t).card = boxLength t := by
    simp [boxInterval1]
  have h2 : (boxInterval2 t).card = boxLength t := by
    simp [boxInterval2]
    omega
  have h3 : (boxInterval3 t).card = boxLength t := by
    simp [boxInterval3]
    omega
  have h4 : (boxInterval4 t).card = boxLength t := by
    simp [boxInterval4]
    omega
  simp only [boxQuartetDomain, Finset.card_product]
  rw [h1, h2, h3, h4]
  ring

/-- Each residue subdomain contains four orientation rows over every one of
the `L^4` quartets, displaying the quartic positive-majorant scale exactly. -/
theorem residueRecordDomains_card (t : ℕ) :
    (residueOneRecordDomain t).card = 4 * boxLength t ^ 4 ∧
      (residueNineRecordDomain t).card = 4 * boxLength t ^ 4 := by
  constructor
  · unfold residueOneRecordDomain
    rw [Finset.card_image_iff.mpr (fun a ha b hb h =>
      residueOnePair_injective_on_parameters ha hb h)]
    rw [Finset.card_product, boxQuartetDomain_card]
    rw [show (Finset.univ : Finset FiberRow).card = 4 by decide]
    ring
  · unfold residueNineRecordDomain
    rw [Finset.card_image_iff.mpr (fun a ha b hb h =>
      residueNinePair_injective_on_parameters ha hb h)]
    rw [Finset.card_product, boxQuartetDomain_card]
    rw [show (Finset.univ : Finset FiberRow).card = 4 by decide]
    ring

theorem boxSignedContribution_eq_deduplicated (Q0 t : ℕ) :
    boxSignedContribution Q0 t = boxDeduplicatedSignedContribution Q0 t := by
  unfold boxSignedContribution boxDeduplicatedSignedContribution
    residueOneRecordDomain residueNineRecordDomain
  rw [Finset.sum_image (fun a ha b hb h =>
    residueOnePair_injective_on_parameters ha hb h)]
  rw [Finset.sum_image (fun a ha b hb h =>
    residueNinePair_injective_on_parameters ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro xr hxr
  ring

/-- Classification and cardinality of the selected four-row image. This is
not ambient primitive-value-fiber exhaustiveness. -/
theorem residueOne_selectedFourFiber_classification
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    (∀ p, p ∈ residueOneFiber x ↔ ∃ row : FiberRow,
        p = residueOnePair x row) ∧
      (residueOneFiber x).card = 4 := by
  constructor
  · intro p
    constructor
    · intro hp
      obtain ⟨row, _hrow, heq⟩ := Finset.mem_image.mp hp
      exact ⟨row, heq.symm⟩
    · rintro ⟨row, rfl⟩
      exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩
  · unfold residueOneFiber
    rw [Finset.card_image_of_injective _ (residueOnePair_injective hx)]
    decide

/-- Classification and cardinality of the selected residue-9 four-row image.
This is not ambient primitive-value-fiber exhaustiveness. -/
theorem residueNine_selectedFourFiber_classification
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    (∀ p, p ∈ residueNineFiber x ↔ ∃ row : FiberRow,
        p = residueNinePair x row) ∧
      (residueNineFiber x).card = 4 := by
  constructor
  · intro p
    constructor
    · intro hp
      obtain ⟨row, _hrow, heq⟩ := Finset.mem_image.mp hp
      exact ⟨row, heq.symm⟩
    · rintro ⟨row, rfl⟩
      exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩
  · unfold residueNineFiber
    rw [Finset.card_image_of_injective _ (residueNinePair_injective hx)]
    decide

theorem residueOneRecordDomain_mem_iff {t : ℕ} {p : PrimitiveRecordPair} :
    p ∈ residueOneRecordDomain t ↔
      ∃ x ∈ boxQuartetDomain t, ∃ row : FiberRow,
        p = residueOnePair x row := by
  constructor
  · intro hp
    obtain ⟨xr, hxr, heq⟩ := Finset.mem_image.mp hp
    have hprod := Finset.mem_product.mp hxr
    exact ⟨xr.1, hprod.1, xr.2, heq.symm⟩
  · rintro ⟨x, hx, row, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(x, row), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩

theorem residueNineRecordDomain_mem_iff {t : ℕ} {p : PrimitiveRecordPair} :
    p ∈ residueNineRecordDomain t ↔
      ∃ x ∈ boxQuartetDomain t, ∃ row : FiberRow,
        p = residueNinePair x row := by
  constructor
  · intro hp
    obtain ⟨xr, hxr, heq⟩ := Finset.mem_image.mp hp
    have hprod := Finset.mem_product.mp hxr
    exact ⟨xr.1, hprod.1, xr.2, heq.symm⟩
  · rintro ⟨x, hx, row, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(x, row), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩

theorem residueOneRecordDomain_subset_primitive (Q0 t : ℕ) :
    residueOneRecordDomain t ⊆
      primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) := by
  intro p hp
  obtain ⟨x, hx, row, rfl⟩ := residueOneRecordDomain_mem_iff.mp hp
  exact residueOnePair_mem_primitiveRecordDomain Q0 hx row

theorem residueNineRecordDomain_subset_primitive (Q0 t : ℕ) :
    residueNineRecordDomain t ⊆
      primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) := by
  intro p hp
  obtain ⟨x, hx, row, rfl⟩ := residueNineRecordDomain_mem_iff.mp hp
  exact residueNinePair_mem_primitiveRecordDomain Q0 hx row

/-- Exact ambient primitive value fiber over one residue-one box value.  The
left side quantifies over T49's full primitive record domain, not merely the
selected image. -/
theorem residueOne_ambientPrimitiveValueFiber_iff
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) {p : PrimitiveRecordPair} :
    (p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
      blockDifferenceValue p = residueOneValue x) ↔
      ∃ row : FiberRow, p = residueOnePair x row := by
  constructor
  · rintro ⟨hp, hpValue⟩
    have hpPos : p ∈ blockPositiveDifferenceDomain
        8 1 Q0 1 (boxEndpoint t) (boxBlock t) :=
      primitiveBlockDifferenceDomain_subset hp
    let v : Fin 4 → ℕ :=
      ![boxX4 x, boxX1 x, boxX2 x, boxX3 x]
    have hrows := residueOne_exponent_rows x
    have htarget :
        blockDifferenceExponent (residueOnePair x .row00) = v := by
      simpa [v] using hrows.1
    have hv : Function.Injective v := by
      have h := boxQuartet_ordered hx
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> omega
    have hvalue :
        signedDecimalValue fourTokenSign (blockDifferenceExponent p) =
          signedDecimalValue fourTokenSign v := by
      rw [← htarget, signedDecimalValue_blockDifferenceExponent,
        signedDecimalValue_blockDifferenceExponent]
      have hpCast := blockPositiveDifferenceValue_cast hpPos
      rw [← hpCast, residueOne_signedDifference hx .row00]
      exact_mod_cast hpValue
    have hperm := fourTokenSign_value_unique_of_target_injective
      (blockDifferenceExponent p) v hv hvalue
    rcases hperm with ⟨hpos | hpos, hneg | hneg⟩
    · refine ⟨.row00, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueOnePair_mem_primitiveRecordDomain Q0 hx .row00)) ?_⟩
      apply (show blockDifferenceExponent p = v from ?_).trans htarget.symm
      funext i
      fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
    · refine ⟨.row01, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueOnePair_mem_primitiveRecordDomain Q0 hx .row01)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 0, v 1, v 3, v 2] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.1.symm)
    · refine ⟨.row10, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueOnePair_mem_primitiveRecordDomain Q0 hx .row10)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 1, v 0, v 2, v 3] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.2.1.symm)
    · refine ⟨.row11, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueOnePair_mem_primitiveRecordDomain Q0 hx .row11)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 1, v 0, v 3, v 2] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.2.2.symm)
  · rintro ⟨row, rfl⟩
    exact ⟨residueOnePair_mem_primitiveRecordDomain Q0 hx row,
      residueOne_blockDifferenceValue Q0 hx row⟩

/-- Exact ambient primitive value fiber over one residue-nine box value. -/
theorem residueNine_ambientPrimitiveValueFiber_iff
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet}
    (hx : x ∈ boxQuartetDomain t) {p : PrimitiveRecordPair} :
    (p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
      blockDifferenceValue p = residueNineValue x) ↔
      ∃ row : FiberRow, p = residueNinePair x row := by
  constructor
  · rintro ⟨hp, hpValue⟩
    have hpPos : p ∈ blockPositiveDifferenceDomain
        8 1 Q0 1 (boxEndpoint t) (boxBlock t) :=
      primitiveBlockDifferenceDomain_subset hp
    let v : Fin 4 → ℕ :=
      ![boxX4 x, boxX2 x, boxX1 x, boxX3 x]
    have hrows := residueNine_exponent_rows x
    have htarget :
        blockDifferenceExponent (residueNinePair x .row00) = v := by
      simpa [v] using hrows.1
    have hv : Function.Injective v := by
      have h := boxQuartet_ordered hx
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> omega
    have hvalue :
        signedDecimalValue fourTokenSign (blockDifferenceExponent p) =
          signedDecimalValue fourTokenSign v := by
      rw [← htarget, signedDecimalValue_blockDifferenceExponent,
        signedDecimalValue_blockDifferenceExponent]
      have hpCast := blockPositiveDifferenceValue_cast hpPos
      rw [← hpCast, residueNine_signedDifference hx .row00]
      exact_mod_cast hpValue
    have hperm := fourTokenSign_value_unique_of_target_injective
      (blockDifferenceExponent p) v hv hvalue
    rcases hperm with ⟨hpos | hpos, hneg | hneg⟩
    · refine ⟨.row00, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueNinePair_mem_primitiveRecordDomain Q0 hx .row00)) ?_⟩
      apply (show blockDifferenceExponent p = v from ?_).trans htarget.symm
      funext i
      fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
    · refine ⟨.row01, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueNinePair_mem_primitiveRecordDomain Q0 hx .row01)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 0, v 1, v 3, v 2] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.1.symm)
    · refine ⟨.row10, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueNinePair_mem_primitiveRecordDomain Q0 hx .row10)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 1, v 0, v 2, v 3] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.2.1.symm)
    · refine ⟨.row11, blockPositiveRecordPair_eq_of_exponent_eq hpPos
        (primitiveBlockDifferenceDomain_subset
          (residueNinePair_mem_primitiveRecordDomain Q0 hx .row11)) ?_⟩
      have hpExp : blockDifferenceExponent p =
          ![v 1, v 0, v 3, v 2] := by
        funext i
        fin_cases i <;> simp [hpos.1, hpos.2, hneg.1, hneg.2]
      exact hpExp.trans (by simpa [v] using hrows.2.2.2.symm)
  · rintro ⟨row, rfl⟩
    exact ⟨residueNinePair_mem_primitiveRecordDomain Q0 hx row,
      residueNine_blockDifferenceValue Q0 hx row⟩

/-- The ambient residue-one primitive fiber is exactly the displayed
four-row fiber, hence has cardinality four. -/
theorem residueOne_ambientFourFiber_classification
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    residueOneAmbientFiber Q0 t x = residueOneFiber x ∧
      (residueOneAmbientFiber Q0 t x).card = 4 := by
  have heq : residueOneAmbientFiber Q0 t x = residueOneFiber x := by
    ext p
    rw [show p ∈ residueOneAmbientFiber Q0 t x ↔
        p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
          blockDifferenceValue p = residueOneValue x by
      simp [residueOneAmbientFiber]]
    rw [residueOne_ambientPrimitiveValueFiber_iff Q0 hx]
    exact (residueOne_selectedFourFiber_classification hx).1 p |>.symm
  exact ⟨heq, by
    rw [heq]
    exact (residueOne_selectedFourFiber_classification hx).2⟩

/-- The ambient residue-nine primitive fiber is exactly the displayed
four-row fiber, hence has cardinality four. -/
theorem residueNine_ambientFourFiber_classification
    (Q0 : ℕ) {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    residueNineAmbientFiber Q0 t x = residueNineFiber x ∧
      (residueNineAmbientFiber Q0 t x).card = 4 := by
  have heq : residueNineAmbientFiber Q0 t x = residueNineFiber x := by
    ext p
    rw [show p ∈ residueNineAmbientFiber Q0 t x ↔
        p ∈ primitiveRecordDomain 8 1 Q0 1 (boxEndpoint t) (boxBlock t) ∧
          blockDifferenceValue p = residueNineValue x by
      simp [residueNineAmbientFiber]]
    rw [residueNine_ambientPrimitiveValueFiber_iff Q0 hx]
    exact (residueNine_selectedFourFiber_classification hx).1 p |>.symm
  exact ⟨heq, by
    rw [heq]
    exact (residueNine_selectedFourFiber_classification hx).2⟩

theorem residueOne_orientation_signs
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    ((residueOnePair x .row00).1.1, (residueOnePair x .row00).2.1) =
        (true, true) ∧
      ((residueOnePair x .row01).1.1, (residueOnePair x .row01).2.1) =
        (true, true) ∧
      ((residueOnePair x .row10).1.1, (residueOnePair x .row10).2.1) =
        (false, false) ∧
      ((residueOnePair x .row11).1.1, (residueOnePair x .row11).2.1) =
        (false, false) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h13 : boxX1 x < boxX3 x := h12.trans h23
  have h24 : boxX2 x < boxX4 x := h23.trans h34
  simp [residueOnePair, coordinateRecord, h12, h13, h23, h24, h34,
    not_lt_of_ge h12.le, not_lt_of_ge h13.le,
    not_lt_of_ge h23.le, not_lt_of_ge h24.le, not_lt_of_ge h34.le]

theorem residueNine_orientation_signs
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    ((residueNinePair x .row00).1.1, (residueNinePair x .row00).2.1) =
        (true, true) ∧
      ((residueNinePair x .row01).1.1, (residueNinePair x .row01).2.1) =
        (true, false) ∧
      ((residueNinePair x .row10).1.1, (residueNinePair x .row10).2.1) =
        (true, false) ∧
      ((residueNinePair x .row11).1.1, (residueNinePair x .row11).2.1) =
        (false, false) := by
  have h := boxQuartet_ordered hx
  have h12 : boxX1 x < boxX2 x := h.2.1
  have h23 : boxX2 x < boxX3 x := h.2.2.1
  have h34 : boxX3 x < boxX4 x := h.2.2.2.1
  have h14 : boxX1 x < boxX4 x := h12.trans (h23.trans h34)
  simp [residueNinePair, coordinateRecord, h12, h14, h23, h34,
    not_lt_of_ge h12.le, not_lt_of_ge h14.le,
    not_lt_of_ge h23.le, not_lt_of_ge h34.le]

/-- At `m=1`, the exact T34 real kernel is the cosine sum on `1,...,10`.
Both the absent zero frequency and included endpoint ten are visible. -/
theorem inclusiveRealKernel_one_eq_cosineSum (d : ℕ) :
    inclusiveRealKernel 1 d Real.pi =
      ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) := by
  rw [inclusiveRealKernel_frequency_audit]
  norm_num only [pow_one]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro h hh
  unfold Theory.PiDigits.T27.phase
  rw [show
      2 * (Real.pi : ℂ) * Complex.I *
          ((((h : ℤ) * (d : ℤ) : ℤ) : ℂ)) * (Real.pi : ℂ) =
        (((2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- Swapping the two off-diagonal records contributes the conjugate phase,
so one positive record pair has exactly the displayed multiplicity two. -/
theorem swappedOrientation_pair_eq_cosine (h d : ℕ) :
    blockSignedPairSum h d Real.pi =
      ((2 * Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ)) : ℝ) : ℂ) := by
  rw [blockSignedPairSum_eq_two_re]
  unfold Theory.PiDigits.T27.phase
  rw [show
      2 * (Real.pi : ℂ) * Complex.I *
          ((((h : ℤ) * (d : ℤ) : ℤ) : ℂ)) * (Real.pi : ℂ) =
        (((2 * Real.pi ^ 2 * (h : ℝ) * (d : ℝ) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
  rw [Complex.exp_ofReal_mul_I_re]
  push_cast
  rfl

/-- Exact residue-1/residue-9 cosine pairing for every one of the ten
inclusive frequencies. -/
theorem residue_cosine_pairing
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) (h : ℕ) :
    Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (residueOneValue x : ℝ)) +
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (residueNineValue x : ℝ)) =
      2 * Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (lowerGap x : ℝ)) := by
  have horder := boxQuartet_ordered hx
  have hdom := tenPow_gap_dominates horder.2.1 horder.2.2.1 horder.2.2.2.1
  have hba : 10 ^ boxX1 x ≤ 10 ^ boxX2 x :=
    pow_le_pow_right' (by norm_num) horder.2.1.le
  have hcd : 10 ^ boxX3 x ≤ 10 ^ boxX4 x :=
    pow_le_pow_right' (by norm_num) horder.2.2.2.1.le
  have hsub : 10 ^ boxX2 x - 10 ^ boxX1 x ≤
      10 ^ boxX4 x - 10 ^ boxX3 x := hdom.le
  have hone : (residueOneValue x : ℝ) =
      (upperGap x : ℝ) - (lowerGap x : ℝ) := by
    unfold residueOneValue upperGap lowerGap
    push_cast [hba, hcd, hsub]
    ring
  have hnine : (residueNineValue x : ℝ) =
      (upperGap x : ℝ) + (lowerGap x : ℝ) := by
    unfold residueNineValue upperGap lowerGap
    push_cast [hba, hcd]
    ring
  rw [hone, hnine, mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring

/-- Exact pairing of T34's inclusive kernels; the endpoint `h=10` remains in
the theorem type. -/
theorem residue_kernel_pairing
    {t : ℕ} {x : BoxQuartet} (hx : x ∈ boxQuartetDomain t) :
    inclusiveRealKernel 1 (residueOneValue x) Real.pi +
        inclusiveRealKernel 1 (residueNineValue x) Real.pi =
      2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (lowerGap x : ℝ)) := by
  rw [inclusiveRealKernel_one_eq_cosineSum,
    inclusiveRealKernel_one_eq_cosineSum, ← Finset.sum_add_distrib]
  calc
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        (Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (residueOneValue x : ℝ)) +
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (residueNineValue x : ℝ)))) =
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          2 * (Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
            Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
              (lowerGap x : ℝ))) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [residue_cosine_pairing hx h]
      ring
    _ = 2 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
            Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
              (lowerGap x : ℝ)) := by
      rw [Finset.mul_sum]

/-- Exact cross-sum factorization into two real bilinear correlations. -/
theorem EBox_eq_crossCorrelations (t : ℕ) :
    EBox t = ∑ h ∈ Finset.Icc (1 : ℕ) 10,
      upperCorrelation t h * lowerCorrelation t h := by
  unfold EBox upperCorrelation lowerCorrelation boxQuartetDomain
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product]
  simp only [upperGap, lowerGap, boxX1, boxX2, boxX3, boxX4]
  rw [show
      (∑ x3 ∈ boxInterval3 t, ∑ x4 ∈ boxInterval4 t,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (10 ^ x4 - 10 ^ x3))) *
        (∑ x1 ∈ boxInterval1 t, ∑ x2 ∈ boxInterval2 t,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (10 ^ x2 - 10 ^ x1))) =
      (∑ x1 ∈ boxInterval1 t, ∑ x2 ∈ boxInterval2 t,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (10 ^ x2 - 10 ^ x1))) *
        (∑ x3 ∈ boxInterval3 t, ∑ x4 ∈ boxInterval4 t,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (10 ^ x4 - 10 ^ x3))) by
      ring]
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x2 hx2
  apply Finset.sum_congr rfl
  intro x3 hx3
  apply Finset.sum_congr rfl
  intro x4 hx4
  have hx12 : x1 ≤ x2 := by
    simp [boxInterval1, boxInterval2] at hx1 hx2
    omega
  have hx34 : x3 ≤ x4 := by
    simp [boxInterval3, boxInterval4] at hx3 hx4
    omega
  have hp12 : 10 ^ x1 ≤ 10 ^ x2 :=
    pow_le_pow_right' (by norm_num) hx12
  have hp34 : 10 ^ x3 ≤ 10 ^ x4 :=
    pow_le_pow_right' (by norm_num) hx34
  push_cast [hp12, hp34]
  ring

/-- Summing the paired kernels over the literal quartet box is exactly twice
`EBox`; this is the finite cross-sum pairing identity. -/
theorem boxKernelPairSum_eq_two_EBox (t : ℕ) :
    (∑ x ∈ boxQuartetDomain t,
      (inclusiveRealKernel 1 (residueOneValue x) Real.pi +
        inclusiveRealKernel 1 (residueNineValue x) Real.pi)) =
      2 * EBox t := by
  calc
    (∑ x ∈ boxQuartetDomain t,
        (inclusiveRealKernel 1 (residueOneValue x) Real.pi +
          inclusiveRealKernel 1 (residueNineValue x) Real.pi)) =
        ∑ x ∈ boxQuartetDomain t, 2 *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10,
            Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
              Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
                (lowerGap x : ℝ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact residue_kernel_pairing hx
    _ = 2 * ∑ x ∈ boxQuartetDomain t,
          ∑ h ∈ Finset.Icc (1 : ℕ) 10,
            Real.cos (2 * Real.pi ^ 2 * (h : ℝ) * (upperGap x : ℝ)) *
              Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
                (lowerGap x : ℝ)) := by
      rw [Finset.mul_sum]
    _ = 2 * EBox t := by
      unfold EBox
      congr 1
      rw [Finset.sum_comm]

/-- The theorem type displays the sole swapped-off-diagonal multiplicity:
exactly one outer factor `2`, with no absolute value or additional factor. -/
theorem boxSignedContribution_orientation_audit (Q0 t : ℕ) :
    boxSignedContribution Q0 t =
      2 * (∑ xr ∈ boxQuartetDomain t ×ˢ (Finset.univ : Finset FiberRow),
        (inclusiveRealKernel 1
            (blockDifferenceValue (residueOnePair xr.1 xr.2)) Real.pi +
          inclusiveRealKernel 1
            (blockDifferenceValue (residueNinePair xr.1 xr.2)) Real.pi) /
          widthWeight (boxBlock t)) := by
  rfl

/-- Exact selected-subdomain contribution, including four positive-domain
rows, the swapped-orientation factor two, the cosine factor two, and literal
width. -/
theorem boxSignedContribution_eq_EBox (Q0 t : ℕ) :
    boxSignedContribution Q0 t =
      16 / widthWeight (boxBlock t) * EBox t := by
  rw [boxSignedContribution_orientation_audit]
  rw [Finset.sum_product]
  have hrows :
      (∑ x ∈ boxQuartetDomain t, ∑ row : FiberRow,
        (inclusiveRealKernel 1
            (blockDifferenceValue (residueOnePair x row)) Real.pi +
          inclusiveRealKernel 1
            (blockDifferenceValue (residueNinePair x row)) Real.pi) /
          widthWeight (boxBlock t)) =
        ∑ x ∈ boxQuartetDomain t, 4 *
          ((inclusiveRealKernel 1 (residueOneValue x) Real.pi +
            inclusiveRealKernel 1 (residueNineValue x) Real.pi) /
            widthWeight (boxBlock t)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hone : ∀ row : FiberRow,
        blockDifferenceValue (residueOnePair x row) = residueOneValue x :=
      fun row => residueOne_blockDifferenceValue Q0 hx row
    have hnine : ∀ row : FiberRow,
        blockDifferenceValue (residueNinePair x row) = residueNineValue x :=
      fun row => residueNine_blockDifferenceValue Q0 hx row
    simp_rw [hone, hnine]
    rw [Finset.sum_const, Finset.card_univ]
    rw [show Fintype.card FiberRow = 4 by decide]
    simp [nsmul_eq_mul]
  rw [hrows]
  rw [← Finset.mul_sum]
  have hpair := boxKernelPairSum_eq_two_EBox t
  calc
    2 * (4 * (∑ x ∈ boxQuartetDomain t,
        (inclusiveRealKernel 1 (residueOneValue x) Real.pi +
          inclusiveRealKernel 1 (residueNineValue x) Real.pi) /
            widthWeight (boxBlock t))) =
        8 * (∑ x ∈ boxQuartetDomain t,
          (inclusiveRealKernel 1 (residueOneValue x) Real.pi +
            inclusiveRealKernel 1 (residueNineValue x) Real.pi) /
              widthWeight (boxBlock t)) := by ring
    _ =
        (8 / widthWeight (boxBlock t)) *
          (∑ x ∈ boxQuartetDomain t,
            (inclusiveRealKernel 1 (residueOneValue x) Real.pi +
              inclusiveRealKernel 1 (residueNineValue x) Real.pi)) := by
      rw [← Finset.sum_div]
      ring
    _ = (8 / widthWeight (boxBlock t)) * (2 * EBox t) := by
      rw [hpair]
    _ = 16 / widthWeight (boxBlock t) * EBox t := by ring

theorem boxWidth_sq (t : ℕ) :
    widthWeight (boxBlock t) ^ 2 =
      16 * (boxLength t : ℝ) ^ 2 + 8 * (boxLength t : ℝ) := by
  have hs := canonical_widthWeight_sq (boxBlock_mem_translatedCanonicalBlocks t)
  rw [(boxBlock_endpoints t).1, (boxBlock_endpoints t).2] at hs
  rw [hs]
  unfold boxEndpoint
  push_cast
  ring

theorem boxWidth_ge_four_mul_length (t : ℕ) :
    4 * (boxLength t : ℝ) ≤ widthWeight (boxBlock t) := by
  have hs := boxWidth_sq t
  have hw := widthWeight_nonneg (boxBlock t)
  have hL : 0 ≤ (boxLength t : ℝ) := by positivity
  nlinarith

theorem boxWidth_pos (t : ℕ) : 0 < widthWeight (boxBlock t) :=
  canonical_widthWeight_pos (boxBlock_mem_translatedCanonicalBlocks t)

/-- The explicit conditional transfer removing the quartic positive-majorant
loss for this selected box only. `EBoxBound C` is a hypothesis, not a result. -/
theorem EBoxBound_implies_boxSignedContribution_bound
    (Q0 t : ℕ) (C : ℝ) (hE : EBoxBound C) :
    |boxSignedContribution Q0 t| ≤
        4 * C * (boxLength t : ℝ) ^ 2 ∧
      |boxSignedContribution Q0 t| ≤
        (C / 4) * (boxEndpoint t : ℝ) ^ 2 := by
  have hC : 0 ≤ C := hE.1
  have hEt := hE.2 t
  have hw : 0 < widthWeight (boxBlock t) := boxWidth_pos t
  have hwLower := boxWidth_ge_four_mul_length t
  have hL : 0 < (boxLength t : ℝ) := by
    exact_mod_cast boxLength_pos t
  have hfirst : |boxSignedContribution Q0 t| ≤
      4 * C * (boxLength t : ℝ) ^ 2 := by
    rw [boxSignedContribution_eq_EBox]
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16),
      abs_of_pos hw]
    calc
      16 / widthWeight (boxBlock t) * |EBox t| ≤
          16 / widthWeight (boxBlock t) *
            (C * (boxLength t : ℝ) ^ 3) := by
        gcongr
      _ ≤ 4 * C * (boxLength t : ℝ) ^ 2 := by
        rw [show
          16 / widthWeight (boxBlock t) *
              (C * (boxLength t : ℝ) ^ 3) =
            (16 * (C * (boxLength t : ℝ) ^ 3)) /
              widthWeight (boxBlock t) by ring]
        apply (div_le_iff₀ hw).2
        have hmul := mul_le_mul_of_nonneg_left hwLower
          (show 0 ≤ 4 * C * (boxLength t : ℝ) ^ 2 by positivity)
        calc
          16 * (C * (boxLength t : ℝ) ^ 3) =
              (4 * C * (boxLength t : ℝ) ^ 2) *
                (4 * (boxLength t : ℝ)) := by ring
          _ ≤ (4 * C * (boxLength t : ℝ) ^ 2) *
                widthWeight (boxBlock t) := hmul
          _ = 4 * C * (boxLength t : ℝ) ^ 2 *
                widthWeight (boxBlock t) := by ring
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hLN : 4 * (boxLength t : ℝ) ≤ (boxEndpoint t : ℝ) := by
    unfold boxEndpoint
    push_cast
    linarith
  have hsq : (4 * (boxLength t : ℝ)) ^ 2 ≤
      (boxEndpoint t : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hLN
  calc
    4 * C * (boxLength t : ℝ) ^ 2 =
        (C / 4) * (4 * (boxLength t : ℝ)) ^ 2 := by ring
    _ ≤ (C / 4) * (boxEndpoint t : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Fully exposed form of the conditional transfer.  The cubic `EBox`
hypothesis is an argument, not a conclusion; the exact width-normalized
identity and both constants remain visible in the theorem type. -/
theorem explicitEBoxCubicBound_transfer
    (Q0 t : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ u : ℕ, |EBox u| ≤ C * (boxLength u : ℝ) ^ 3) :
    boxSignedContribution Q0 t =
        16 / widthWeight (boxBlock t) * EBox t ∧
      |boxSignedContribution Q0 t| ≤
        4 * C * (boxLength t : ℝ) ^ 2 ∧
      |boxSignedContribution Q0 t| ≤
        (C / 4) * (boxEndpoint t : ℝ) ^ 2 := by
  exact ⟨boxSignedContribution_eq_EBox Q0 t,
    EBoxBound_implies_boxSignedContribution_bound Q0 t C ⟨hC, hE⟩⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T56

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.translatedCanonicalBlocks_boxEndpoint
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxWidth_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxInclusiveFrequencies
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.fourTokenSign_value_unique_of_target_injective
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residue_factorizations
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residue_record_valuation_fiber_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOnePair_mem_primitiveRecordDomain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNinePair_mem_primitiveRecordDomain
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOnePair_injective_on_parameters
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNinePair_injective_on_parameters
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueRecordDomains_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxSignedContribution_eq_deduplicated
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOne_selectedFourFiber_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNine_selectedFourFiber_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOne_ambientPrimitiveValueFiber_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNine_ambientPrimitiveValueFiber_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOne_ambientFourFiber_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNine_ambientFourFiber_classification
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueOne_orientation_signs
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residueNine_orientation_signs
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.swappedOrientation_pair_eq_cosine
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.residue_cosine_pairing
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.EBox_eq_crossCorrelations
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxKernelPairSum_eq_two_EBox
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxSignedContribution_orientation_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.boxSignedContribution_eq_EBox
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.EBoxBound_implies_boxSignedContribution_bound
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T56.explicitEBoxCubicBound_transfer
