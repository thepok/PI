import TheoryLib.PiPositiveDecimalFactorEntropy.T18T18FiniteCircleQuantization
import TheoryLib.PiPositiveDecimalFactorEntropy.T23T23AbstractSubgroupSeparation

/-!
# T25: decimal successor exclusion for the T23 subgroup family

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file isolates local base-ten ordering information that is absent from
T23's aggregate finite-group construction.  It does not identify any T23
label multiset with the decimal orbit of pi.  Excluding this abstract family
proves no resonance amplification, no instance of C1, and no fixed-pi
estimate.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace DecimalFactorComplexity.DecimalSuccessorExclusion

open DecimalFactorComplexity.FiniteCircleQuantization
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorComplexity.AbstractSubgroupSeparation
open DecimalFactorEntropy.FinitePrefixMultiplicityTransfer

/-- The carry left after multiplying a floor-quantized cell by ten. -/
def decimalDigitError (q : ℕ) (y : ℝ) : ℕ :=
  Int.toNat ⌊10 * Int.fract ((q : ℝ) * Int.fract y)⌋

/-- Multiplication by ten splits into ten times the floor and one decimal
carry. -/
theorem floor_ten_eq_ten_floor_add_fract_floor (x : ℝ) :
    ⌊10 * x⌋ = 10 * ⌊x⌋ + ⌊10 * Int.fract x⌋ := by
  calc
    ⌊10 * x⌋ = ⌊((10 * ⌊x⌋ : ℤ) : ℝ) + 10 * Int.fract x⌋ := by
      congr 1
      push_cast
      nlinarith [Int.floor_add_fract x]
    _ = 10 * ⌊x⌋ + ⌊10 * Int.fract x⌋ :=
      Int.floor_intCast_add _ _

/-- The floor carry is a base-ten digit. -/
theorem decimalDigitError_le_nine (q : ℕ) (y : ℝ) :
    decimalDigitError q y ≤ 9 := by
  unfold decimalDigitError
  have hnonneg : (0 : ℝ) ≤ 10 * Int.fract ((q : ℝ) * Int.fract y) := by
    exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  have hlt : 10 * Int.fract ((q : ℝ) * Int.fract y) < (10 : ℝ) := by
    nlinarith [Int.fract_lt_one ((q : ℝ) * Int.fract y)]
  have hfloorNonneg : 0 ≤ ⌊10 * Int.fract ((q : ℝ) * Int.fract y)⌋ :=
    Int.floor_nonneg.mpr hnonneg
  have hfloorLt : ⌊10 * Int.fract ((q : ℝ) * Int.fract y)⌋ < (10 : ℤ) :=
    (Int.floor_lt).2 hlt
  omega

/-- Taking a base-ten step only depends on the fractional part. -/
theorem fract_ten_eq_fract_ten_fract (y : ℝ) :
    Int.fract (10 * y) = Int.fract (10 * Int.fract y) := by
  calc
    Int.fract (10 * y) =
        Int.fract (((10 * ⌊y⌋ : ℤ) : ℝ) + 10 * Int.fract y) := by
      congr 1
      push_cast
      nlinarith [Int.floor_add_fract y]
    _ = Int.fract (10 * Int.fract y) := Int.fract_intCast_add _ _

/-- Floor quantization of one base-ten step has an exact digit error in
`ZMod q`. -/
theorem cyclicCell_ten_eq (q : ℕ) [NeZero q] (y : ℝ) :
    cyclicCell q (10 * y) =
      10 * cyclicCell q y + (decimalDigitError q y : ZMod q) := by
  have hE : 0 ≤ ⌊10 * Int.fract ((q : ℝ) * Int.fract y)⌋ := by
    apply Int.floor_nonneg.mpr
    exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  have hscale :
      (q : ℝ) * Int.fract (10 * Int.fract y) =
        10 * ((q : ℝ) * Int.fract y) -
          (((q : ℤ) * ⌊10 * Int.fract y⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  unfold cyclicCell
  rw [fract_ten_eq_fract_ten_fract, hscale, Int.floor_sub_intCast,
    floor_ten_eq_ten_floor_add_fract_floor]
  have herrorCast :
      (decimalDigitError q y : ZMod q) =
        (⌊10 * Int.fract ((q : ℝ) * Int.fract y)⌋ : ZMod q) := by
    rw [decimalDigitError, ← Int.cast_natCast, Int.toNat_of_nonneg hE]
  rw [herrorCast]
  push_cast
  simp

/-- Floor-quantized labels of a finite base-ten orbit. -/
def decimalOrbitLabel (x : ℝ) (q M : ℕ) : Fin M → ZMod q :=
  quantizedOrbit (fun j : Fin M => (10 : ℝ) ^ (j : ℕ) * x) q

/-- The successor law with its linear index range and digit error exposed. -/
theorem decimalOrbitLabel_successor {M q : ℕ} [NeZero q] (x : ℝ)
    (j : ℕ) (hj : j + 1 < M) :
    ∃ e : ℕ, 0 ≤ e ∧ e ≤ 9 ∧
      decimalOrbitLabel x q M ⟨j + 1, hj⟩ =
        10 * decimalOrbitLabel x q M ⟨j, by omega⟩ + (e : ZMod q) := by
  refine ⟨decimalDigitError q ((10 : ℝ) ^ j * x), Nat.zero_le _,
    decimalDigitError_le_nine q _, ?_⟩
  change cyclicCell q ((10 : ℝ) ^ (j + 1) * x) =
    10 * cyclicCell q ((10 : ℝ) ^ j * x) +
      (decimalDigitError q ((10 : ℝ) ^ j * x) : ZMod q)
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    cyclicCell_ten_eq q ((10 : ℝ) ^ j * x)

/-- A digit smaller than the subgroup spacing cannot bridge two subgroup
points. -/
theorem digit_eq_zero_of_spaced_subgroup_eq
    (q D spacing e u v : ℕ) [NeZero q]
    (hq : q = D * spacing) (hspacing : 9 < spacing) (he : e ≤ 9)
    (heq : ((v * spacing : ℕ) : ZMod q) =
      10 * ((u * spacing : ℕ) : ZMod q) + (e : ZMod q)) :
    e = 0 := by
  have hspos : 0 < spacing := by omega
  letI : NeZero spacing := ⟨hspos.ne'⟩
  have hsq : spacing ∣ q := by
    rw [hq]
    exact dvd_mul_left _ _
  have hezero : (e : ZMod spacing) = 0 := by
    have hmap := congrArg (ZMod.castHom hsq (ZMod spacing)) heq
    simpa only [map_add, map_mul, map_ofNat, ZMod.castHom_apply,
      ZMod.cast_natCast hsq, Nat.cast_mul, ZMod.natCast_self, mul_zero,
      zero_mul, zero_add, add_zero] using hmap.symm
  have hdiv : spacing ∣ e := (ZMod.natCast_eq_zero_iff e spacing).mp hezero
  obtain ⟨c, rfl⟩ := hdiv
  by_cases hc : c = 0
  · simp [hc]
  · have : spacing ≤ spacing * c := by
      exact Nat.le_mul_of_pos_right spacing (Nat.pos_of_ne_zero hc)
    omega

/-- Equal starts in a bounded deterministic linear orbit have equal shifts. -/
theorem linearOrbit_shift {α : Type*} (f : α → α) (a : ℕ → α) (M i j k : ℕ)
    (hstep : ∀ t : ℕ, t + 1 < M → a (t + 1) = f (a t))
    (hij : a i = a j) (hik : i + k < M) (hjk : j + k < M) :
    a (i + k) = a (j + k) := by
  induction k with
  | zero => simpa using hij
  | succ k ih =>
      have hik' : i + k < M := by omega
      have hjk' : j + k < M := by omega
      rw [show i + (k + 1) = (i + k) + 1 by omega,
        show j + (k + 1) = (j + k) + 1 by omega,
        hstep (i + k) (by omega), hstep (j + k) (by omega), ih hik' hjk']

/-- Zero remains zero in a bounded orbit whose transition fixes zero. -/
theorem linearOrbit_zero_propagates {α : Type*} [Zero α]
    (f : α → α) (hf : f 0 = 0) (a : ℕ → α) (M i k : ℕ)
    (hstep : ∀ t : ℕ, t + 1 < M → a (t + 1) = f (a t))
    (hi : a i = 0) (hik : i + k < M) :
    a (i + k) = 0 := by
  induction k with
  | zero => simpa using hi
  | succ k ih =>
      have hik' : i + k < M := by omega
      rw [show i + (k + 1) = (i + k) + 1 by omega,
        hstep (i + k) (by omega), ih hik', hf]

/-- A finite deterministic orbit cannot contain zero, a nonzero value, and a
positive return to its initial value when zero is absorbing. -/
theorem no_linearOrbit_of_zero_nonzero_repeat {α : Type*} [Zero α]
    (f : α → α) (hf : f 0 = 0) (a : ℕ → α) (M : ℕ)
    (hstep : ∀ t : ℕ, t + 1 < M → a (t + 1) = f (a t))
    (hzero : ∃ t : ℕ, t < M ∧ a t = 0)
    (hnonzero : ∃ t : ℕ, t < M ∧ a t ≠ 0)
    (hrepeat : ∃ j : ℕ, 0 < j ∧ j < M ∧ a j = a 0) :
    False := by
  classical
  obtain ⟨t, htM, ht0⟩ := hnonzero
  by_cases ha0 : a 0 = 0
  · have ht := linearOrbit_zero_propagates f hf a M 0 t hstep ha0 (by omega)
    exact ht0 (by simpa using ht)
  obtain ⟨j, hjpos, hjM, hjrepeat⟩ := hrepeat
  let z := Nat.find hzero
  have hz : z < M ∧ a z = 0 := by
    simpa only [z] using Nat.find_spec hzero
  by_cases hzj : z ≤ j
  · have hjzero := linearOrbit_zero_propagates f hf a M z (j - z)
      hstep hz.2 (by omega)
    have : a j = 0 := by simpa [Nat.add_sub_of_le hzj] using hjzero
    exact ha0 (hjrepeat.symm.trans this)
  · have hjz : j < z := by omega
    have hshift := linearOrbit_shift f a M 0 j (z - j) hstep
      hjrepeat.symm (by omega) (by omega)
    have hearlier : a (z - j) = 0 := by
      have : a (z - j) = a z := by simpa [Nat.add_sub_of_le hjz.le] using hshift
      exact this.trans hz.2
    have hltfind : z - j < Nat.find hzero := by
      change z - j < z
      exact Nat.sub_lt (by omega) hjpos
    have hmin := Nat.find_min hzero hltfind
    exact hmin ⟨by omega, hearlier⟩

/-- The canonical order-`D` subgroup point with spacing `q / D`. -/
def spacedSubgroupPoint (q D : ℕ) (b : Fin D) : ZMod q :=
  (b.val * (q / D) : ℕ)

/-- An arbitrary linear ordering of an exactly and uniformly repeated
`q / D`-spaced subgroup. -/
def UniformlyRepeatedSubgroupOrdering
    (q D multiplicity : ℕ) (a : ℕ → ZMod q) : Prop :=
  (∀ j : ℕ, j < D * multiplicity →
    ∃ b : Fin D, a j = spacedSubgroupPoint q D b) ∧
  (∀ b : Fin D,
    prefixMultiplicity (fun j : Fin (D * multiplicity) => a j)
      (spacedSubgroupPoint q D b) = multiplicity)

/-- Exact decimal successor data on a linear range; no last-to-first equation
is included. -/
def LinearDecimalSuccessors {q : ℕ} (M : ℕ)
    (a : ℕ → ZMod q) (digitError : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, j + 1 < M →
    0 ≤ digitError j ∧ digitError j ≤ 9 ∧
      a (j + 1) = 10 * a j + (digitError j : ZMod q)

/-- Positive multiplicity supplies an occurrence in the finite linear
range. -/
theorem exists_index_of_prefixMultiplicity_pos {q M : ℕ}
    (label : Fin M → ZMod q) (z : ZMod q)
    (hpos : 0 < prefixMultiplicity label z) :
    ∃ i : Fin M, label i = z := by
  classical
  unfold prefixMultiplicity at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- Multiplicity greater than one supplies two distinct occurrences. -/
theorem exists_two_indices_of_one_lt_prefixMultiplicity {q M : ℕ}
    (label : Fin M → ZMod q) (z : ZMod q)
    (hone : 1 < prefixMultiplicity label z) :
    ∃ i j : Fin M, label i = z ∧ label j = z ∧ i ≠ j := by
  classical
  unfold prefixMultiplicity at hone
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hone
  exact ⟨i, j, (Finset.mem_filter.mp hi).2,
    (Finset.mem_filter.mp hj).2, hij⟩

/-- The first positive subgroup point is nonzero when `D > 1` and the
spacing is positive. -/
theorem spacedSubgroupPoint_one_ne_zero
    (q D : ℕ) [NeZero q] (hD : 1 < D) (hdiv : D ∣ q)
    (hspacing : 0 < q / D) :
    spacedSubgroupPoint q D ⟨1, hD⟩ ≠ 0 := by
  intro hz
  have hqeq : q = D * (q / D) := (Nat.mul_div_cancel' hdiv).symm
  have hsltq : q / D < q := by nlinarith
  have hz' : (q / D : ZMod q) = 0 := by
    simpa [spacedSubgroupPoint] using hz
  have hqdvd : q ∣ q / D := by
    exact (ZMod.natCast_eq_zero_iff (q / D) q).mp hz'
  exact (Nat.not_dvd_of_pos_of_lt hspacing hsltq) hqdvd

/-- Generic exclusion theorem. It exposes the ambient modulus `q`, subgroup
order `D`, spacing `q / D`, common multiplicity, linear index range, and all
digit errors. -/
theorem uniformlyRepeatedSubgroup_no_decimal_order
    (q D multiplicity : ℕ) [NeZero q]
    (hD : 1 < D) (hmultiplicity : 2 ≤ multiplicity)
    (hdiv : D ∣ q) (hspacing : 9 < q / D) :
    ¬ ∃ (a : ℕ → ZMod q) (digitError : ℕ → ℕ),
      UniformlyRepeatedSubgroupOrdering q D multiplicity a ∧
      LinearDecimalSuccessors (D * multiplicity) a digitError := by
  classical
  rintro ⟨a, digitError, huniform, hsuccessor⟩
  rcases huniform with ⟨hsupport, hmultiplicityExact⟩
  have hDpos : 0 < D := by omega
  have hMpos : 0 < D * multiplicity := Nat.mul_pos hDpos (by omega)
  have hqeq : q = D * (q / D) := (Nat.mul_div_cancel' hdiv).symm
  have hstep : ∀ j : ℕ, j + 1 < D * multiplicity →
      a (j + 1) = 10 * a j := by
    intro j hj
    obtain ⟨u, hu⟩ := hsupport j (by omega)
    obtain ⟨v, hv⟩ := hsupport (j + 1) hj
    have hs := hsuccessor j hj
    have heq : ((v.val * (q / D) : ℕ) : ZMod q) =
        10 * ((u.val * (q / D) : ℕ) : ZMod q) +
          (digitError j : ZMod q) := by
      simpa only [spacedSubgroupPoint, hu, hv] using hs.2.2
    have hezero := digit_eq_zero_of_spaced_subgroup_eq
      q D (q / D) (digitError j) u.val v.val hqeq hspacing hs.2.1 heq
    simpa only [hezero, Nat.cast_zero, add_zero] using hs.2.2
  have hzero : ∃ t : ℕ, t < D * multiplicity ∧ a t = 0 := by
    let b0 : Fin D := ⟨0, hDpos⟩
    have hcount := hmultiplicityExact b0
    have hcountPos :
        0 < prefixMultiplicity (fun j : Fin (D * multiplicity) => a j)
          (spacedSubgroupPoint q D b0) := by
      rw [hcount]
      omega
    obtain ⟨i, hi⟩ := exists_index_of_prefixMultiplicity_pos
      (fun j : Fin (D * multiplicity) => a j)
      (spacedSubgroupPoint q D b0) hcountPos
    refine ⟨i.val, i.isLt, ?_⟩
    simpa [b0, spacedSubgroupPoint] using hi
  have hnonzero : ∃ t : ℕ, t < D * multiplicity ∧ a t ≠ 0 := by
    let b1 : Fin D := ⟨1, hD⟩
    have hcount := hmultiplicityExact b1
    have hcountPos :
        0 < prefixMultiplicity (fun j : Fin (D * multiplicity) => a j)
          (spacedSubgroupPoint q D b1) := by
      rw [hcount]
      omega
    obtain ⟨i, hi⟩ := exists_index_of_prefixMultiplicity_pos
      (fun j : Fin (D * multiplicity) => a j)
      (spacedSubgroupPoint q D b1) hcountPos
    have hb1ne : spacedSubgroupPoint q D b1 ≠ 0 := by
      exact spacedSubgroupPoint_one_ne_zero q D hD hdiv (by omega)
    refine ⟨i.val, i.isLt, ?_⟩
    intro hizero
    exact hb1ne (hi.symm.trans hizero)
  have hrepeat : ∃ j : ℕ, 0 < j ∧ j < D * multiplicity ∧ a j = a 0 := by
    obtain ⟨b, hb⟩ := hsupport 0 hMpos
    have hcount := hmultiplicityExact b
    have hcountOne :
        1 < prefixMultiplicity (fun j : Fin (D * multiplicity) => a j) (a 0) := by
      rw [hb, hcount]
      omega
    obtain ⟨i, j, hi, hj, hij⟩ :=
      exists_two_indices_of_one_lt_prefixMultiplicity
        (fun k : Fin (D * multiplicity) => a k) (a 0) hcountOne
    by_cases hi0 : i.val = 0
    · have hj0 : j.val ≠ 0 := by
        intro hjzero
        apply hij
        apply Fin.ext
        omega
      exact ⟨j.val, Nat.pos_of_ne_zero hj0, j.isLt, hj⟩
    · exact ⟨i.val, Nat.pos_of_ne_zero hi0, i.isLt, hi⟩
  exact no_linearOrbit_of_zero_nonzero_repeat
    (fun z : ZMod q => 10 * z) (by simp) a (D * multiplicity)
    hstep hzero hnonzero hrepeat

/-- T23's spacing `q / D` is exactly its sample size `M`. -/
theorem T23_spacing_eq_sampleSize (r : ℕ) :
    modulus r / subgroupSize r = sampleSize r := by
  simp [modulus, subgroupSize]

/-- T23's displayed subgroup point is the generic point at spacing `q / D`. -/
theorem T23_subgroupPoint_eq_spacedSubgroupPoint
    (r : ℕ) (b : Fin (subgroupSize r)) :
    subgroupPoint r b = spacedSubgroupPoint (modulus r) (subgroupSize r) b := by
  simp [subgroupPoint, spacedSubgroupPoint, T23_spacing_eq_sampleSize]

/-- An arbitrary ordering with exactly T23's support and exact T23
multiplicity formula. -/
def T23ExactSubgroupOrdering
    (r : ℕ) (a : ℕ → ZMod (modulus r)) : Prop :=
  (∀ j : ℕ, j < sampleSize r → a j ∈ subgroupSupport r) ∧
  (∀ z : ZMod (modulus r),
    prefixMultiplicity (fun j : Fin (sampleSize r) => a j) z =
      if z ∈ subgroupSupport r then subgroupSize r else 0)

/-- The support and multiplicity formula used by `T23ExactSubgroupOrdering`
are exactly those of T23's imported `subgroupLabel`, not a replacement
family. -/
theorem T23_subgroupLabel_exact_multiset (r : ℕ) :
    (∀ j : Fin (sampleSize r), subgroupLabel r j ∈ subgroupSupport r) ∧
    (∀ z : ZMod (modulus r),
      prefixMultiplicity (subgroupLabel r) z =
        if z ∈ subgroupSupport r then subgroupSize r else 0) := by
  exact ⟨subgroupLabel_mem_support r, subgroupLabel_multiplicity_formula r⟩

/-- Every exact ordering of T23's multiset satisfies the generic uniform
subgroup predicate. -/
theorem T23ExactSubgroupOrdering.uniformlyRepeated
    (r : ℕ) (a : ℕ → ZMod (modulus r))
    (h : T23ExactSubgroupOrdering r a) :
    UniformlyRepeatedSubgroupOrdering
      (modulus r) (subgroupSize r) (subgroupSize r) a := by
  classical
  rcases h with ⟨hsupport, hmultiplicity⟩
  constructor
  · intro j hj
    have hjM : j < sampleSize r := by simpa [sampleSize] using hj
    have hjSupport := hsupport j hjM
    simp only [subgroupSupport, Finset.mem_image, Finset.mem_univ,
      true_and] at hjSupport
    obtain ⟨b, hb⟩ := hjSupport
    refine ⟨b, hb.symm.trans ?_⟩
    exact T23_subgroupPoint_eq_spacedSubgroupPoint r b
  · intro b
    have hmem :
        spacedSubgroupPoint (modulus r) (subgroupSize r) b ∈ subgroupSupport r := by
      rw [← T23_subgroupPoint_eq_spacedSubgroupPoint]
      simp [subgroupSupport]
    have hcount := hmultiplicity
      (spacedSubgroupPoint (modulus r) (subgroupSize r) b)
    rw [if_pos hmem] at hcount
    simpa [sampleSize] using hcount

/-- No linear ordering of the exact `r`-th T23 multiset admits decimal
successors with digit errors in `0..9`. -/
theorem T23_no_decimal_successor_order (r : ℕ) :
    ¬ ∃ (a : ℕ → ZMod (modulus r)) (digitError : ℕ → ℕ),
      T23ExactSubgroupOrdering r a ∧
      LinearDecimalSuccessors (sampleSize r) a digitError := by
  rintro ⟨a, digitError, hexact, hsuccessor⟩
  have hD : 1 < subgroupSize r := by
    unfold subgroupSize
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hDten : 10 ≤ subgroupSize r := by
    unfold subgroupSize
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega : 1 ≤ r + 1)
  have hdiv : subgroupSize r ∣ modulus r := by
    refine ⟨sampleSize r, ?_⟩
    simp [modulus, Nat.mul_comm]
  have hspacing : 9 < modulus r / subgroupSize r := by
    rw [T23_spacing_eq_sampleSize]
    unfold sampleSize
    nlinarith
  apply uniformlyRepeatedSubgroup_no_decimal_order
    (modulus r) (subgroupSize r) (subgroupSize r)
    hD (by omega) hdiv hspacing
  refine ⟨a, digitError, T23ExactSubgroupOrdering.uniformlyRepeated r a hexact, ?_⟩
  simpa [sampleSize] using hsuccessor

/-- The T23 parameters and the exclusion are exposed together. -/
theorem T23_parameters_and_decimal_exclusion (r : ℕ) :
    let q := modulus r
    let D := subgroupSize r
    let spacing := q / D
    let multiplicity := D
    let M := sampleSize r
    q = M * D ∧
      D = 10 ^ (r + 1) ∧
      M = D * multiplicity ∧
      spacing = M ∧
      9 < spacing ∧
      2 ≤ multiplicity ∧
      ¬ ∃ (a : ℕ → ZMod q) (digitError : ℕ → ℕ),
        T23ExactSubgroupOrdering r a ∧
        (∀ j : ℕ, j + 1 < M →
          0 ≤ digitError j ∧ digitError j ≤ 9 ∧
            a (j + 1) = 10 * a j + (digitError j : ZMod q)) := by
  dsimp only
  have hDten : 10 ≤ subgroupSize r := by
    unfold subgroupSize
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 10) (by omega : 1 ≤ r + 1)
  refine ⟨rfl, rfl, rfl, T23_spacing_eq_sampleSize r, ?_, by omega, ?_⟩
  · rw [T23_spacing_eq_sampleSize]
    unfold sampleSize
    nlinarith
  · simpa only [LinearDecimalSuccessors] using
      T23_no_decimal_successor_order r

/-- Hence exclusion holds eventually; in fact the preceding theorem proves
it for every natural family index. -/
theorem T23_eventually_no_decimal_successor_order :
    ∀ᶠ r : ℕ in atTop,
      ¬ ∃ (a : ℕ → ZMod (modulus r)) (digitError : ℕ → ℕ),
        T23ExactSubgroupOrdering r a ∧
        LinearDecimalSuccessors (sampleSize r) a digitError := by
  filter_upwards [] with r
  exact T23_no_decimal_successor_order r

end DecimalFactorComplexity.DecimalSuccessorExclusion

#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.decimalDigitError_le_nine
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.cyclicCell_ten_eq
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.decimalOrbitLabel_successor
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.digit_eq_zero_of_spaced_subgroup_eq
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.no_linearOrbit_of_zero_nonzero_repeat
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.uniformlyRepeatedSubgroup_no_decimal_order
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23_spacing_eq_sampleSize
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23_subgroupLabel_exact_multiset
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23ExactSubgroupOrdering.uniformlyRepeated
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23_no_decimal_successor_order
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23_parameters_and_decimal_exclusion
#print axioms DecimalFactorComplexity.DecimalSuccessorExclusion.T23_eventually_no_decimal_successor_order
