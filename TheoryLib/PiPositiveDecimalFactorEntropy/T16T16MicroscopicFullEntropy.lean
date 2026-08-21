import TheoryLib.PiPositiveDecimalFactorEntropy.T1CanonicalEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T2T2ExponentialCollisionCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T6T6PairCorrelationConditional
import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion
import TheoryLib.PiPositiveDecimalFactorEntropy.T9T9MesoscopicFrontier

/-!
# T16: microscopic circle pairs force full decimal factor entropy

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

All circle-pair counts are ordered, include the diagonal, and use a strict
distance cutoff.  Every conclusion about pi is conditional on C3, C4, C5, or
the explicitly displayed uniform microscopic hypothesis.
-/

noncomputable section

open scoped BigOperators
open Filter Finset Set Topology

namespace DecimalFactorComplexity.MicroscopicFullEntropy

open DecimalFactorComplexity
open DecimalFactorComplexity.ExponentialCollisionCriterion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.MesoscopicFrontier
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorEntropy

/-- Ordered, diagonal-inclusive pairs below the strict circular radius `r`. -/
def orderedCirclePairs {M : ℕ} (x : Fin M → ℝ) (r : ℝ) :
    Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij => circleDistance (x ij.2 - x ij.1) < r

/-- The strict ordered pair count `P_M(r)`, including all diagonals when
`r > 0`. -/
def orderedCirclePairCount {M : ℕ} (x : Fin M → ℝ) (r : ℝ) : ℕ :=
  (orderedCirclePairs x r).card

@[simp] theorem mem_orderedCirclePairs_iff {M : ℕ} (x : Fin M → ℝ)
    (r : ℝ) (ij : Fin M × Fin M) :
    ij ∈ orderedCirclePairs x r ↔
      circleDistance (x ij.2 - x ij.1) < r := by
  simp [orderedCirclePairs]

/-- Every diagonal is present whenever the strict radius is positive. -/
@[simp] theorem diagonal_mem_orderedCirclePairs {M : ℕ} (x : Fin M → ℝ)
    {r : ℝ} (hr : 0 < r) (i : Fin M) :
    (i, i) ∈ orderedCirclePairs x r := by
  rw [mem_orderedCirclePairs_iff]
  have hzero : circleDistance (0 : ℝ) ≤ 0 := by
    simpa using circleDistance_le_abs_sub_int (0 : ℝ) (0 : ℤ)
  simpa using hzero.trans_lt hr

/-- Diagonal-inclusive normalization gives at least `M` ordered pairs at every
positive radius. -/
theorem sampleSize_le_orderedCirclePairCount {M : ℕ} (x : Fin M → ℝ)
    {r : ℝ} (hr : 0 < r) : M ≤ orderedCirclePairCount x r := by
  unfold orderedCirclePairCount
  have hsubset : (Finset.univ : Finset (Fin M)).diag ⊆ orderedCirclePairs x r := by
    intro ij hij
    rw [Finset.mem_diag] at hij
    simpa [hij.2] using diagonal_mem_orderedCirclePairs x hr ij.1
  simpa using Finset.card_le_card hsubset

/-- The cyclic `M`-cell label of a real point. -/
def cyclicCell (M : ℕ) (y : ℝ) : ZMod M :=
  (⌊(M : ℝ) * Int.fract y⌋ : ℤ)

/-- The symmetric list of `2R+3` cyclic cells with offsets
`-(R+1), ..., R+1`. -/
def cyclicNeighbors (M R : ℕ) (a : ZMod M) : Finset (ZMod M) :=
  Finset.univ.image fun t : Fin (2 * R + 3) =>
    a + ((t : ℕ) : ℤ) - (R + 1 : ℤ)

theorem cyclicNeighbors_card_le (M R : ℕ) (a : ZMod M) :
    (cyclicNeighbors M R a).card ≤ 2 * R + 3 := by
  unfold cyclicNeighbors
  exact (Finset.card_image_le).trans (by simp)

theorem mem_cyclicNeighbors_symm {M R : ℕ} {a b : ZMod M} :
    b ∈ cyclicNeighbors M R a ↔ a ∈ cyclicNeighbors M R b := by
  classical
  have himp (c d : ZMod M) (hd : d ∈ cyclicNeighbors M R c) :
      c ∈ cyclicNeighbors M R d := by
    simp only [cyclicNeighbors, Finset.mem_image, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨t, rfl⟩ := hd
    have ht : (t : ℕ) ≤ 2 * R + 2 := by omega
    let t' : Fin (2 * R + 3) := ⟨2 * R + 2 - (t : ℕ), by omega⟩
    refine ⟨t', ?_⟩
    dsimp [t']
    have hsum : (t : ℕ) + (2 * R + 2 - (t : ℕ)) = 2 * R + 2 := by omega
    have hsumZ :
        (((t : ℕ) : ℤ) : ZMod M) +
            (((2 * R + 2 - (t : ℕ) : ℕ) : ℤ) : ZMod M) =
          (((2 * R + 2 : ℕ) : ℤ) : ZMod M) := by
      have hsumI :
          ((t : ℕ) : ℤ) + ((2 * R + 2 - (t : ℕ) : ℕ) : ℤ) =
            ((2 * R + 2 : ℕ) : ℤ) := by exact_mod_cast hsum
      simpa using congrArg (fun z : ℤ => (z : ZMod M)) hsumI
    symm
    calc
      c = c + (((2 * R + 2 : ℕ) : ℤ) - 2 * (R + 1 : ℤ)) := by
        push_cast
        ring
      _ = (c + ((t : ℕ) : ℤ) - (R + 1 : ℤ)) +
          ((2 * R + 2 - (t : ℕ) : ℕ) : ℤ) - (R + 1 : ℤ) := by
        rw [← hsumZ]
        ring
  exact ⟨himp a b, himp b a⟩

/-- A symmetric label relation of degree at most `d` has at most `d` times
as many ordered related pairs as ordered equal-label pairs. -/
theorem labelledPairs_le_degree_mul_equalPairs
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (label : ι → κ) (neighbor : κ → Finset κ) (d : ℕ)
    (hdeg : ∀ a, (neighbor a).card ≤ d)
    (hsymm : ∀ a b, b ∈ neighbor a ↔ a ∈ neighbor b) :
    ((Finset.univ.filter fun ij : ι × ι =>
        label ij.2 ∈ neighbor (label ij.1)).card : ℝ) ≤
      d * ((Finset.univ.filter fun ij : ι × ι =>
        label ij.1 = label ij.2).card : ℝ) := by
  classical
  let fiber (a : κ) := (Finset.univ : Finset ι).filter fun i => label i = a
  let related := (Finset.univ : Finset (ι × ι)).filter fun ij =>
    label ij.2 ∈ neighbor (label ij.1)
  let equal := (Finset.univ : Finset (ι × ι)).filter fun ij =>
    label ij.1 = label ij.2
  have hrelated : related.card =
      ∑ a : κ, ∑ b ∈ neighbor a, (fiber a).card * (fiber b).card := by
    have hfirst := Finset.card_eq_sum_card_fiberwise
      (s := related) (t := (Finset.univ : Finset κ))
      (f := fun ij => label ij.1) (by simp)
    rw [hfirst]
    apply Finset.sum_congr rfl
    intro a ha
    have hsecond := Finset.card_eq_sum_card_fiberwise
      (s := related.filter fun ij => label ij.1 = a)
      (t := neighbor a) (f := fun ij => label ij.2) (by
        intro ij hij
        have houter := Finset.mem_filter.mp hij
        have hr := (Finset.mem_filter.mp houter.1).2
        simpa [houter.2] using hr)
    rw [hsecond]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.card_product]
    apply congrArg Finset.card
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, fiber, related,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hla⟩, hlb⟩
      exact ⟨hla, hlb⟩
    · rintro ⟨hla, hlb⟩
      have hr : label ij.2 ∈ neighbor a := hlb ▸ hb
      exact ⟨⟨by simpa [hla] using hr, hla⟩, hlb⟩
  have hequal : equal.card = ∑ a : κ, (fiber a).card ^ 2 := by
    have hfirst := Finset.card_eq_sum_card_fiberwise
      (s := equal) (t := (Finset.univ : Finset κ))
      (f := fun ij => label ij.1) (by simp)
    rw [hfirst]
    apply Finset.sum_congr rfl
    intro a ha
    rw [pow_two, ← Finset.card_product]
    apply congrArg Finset.card
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, fiber, equal,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨heq, hla⟩
      exact ⟨hla, heq ▸ hla⟩
    · rintro ⟨hla, hlb⟩
      exact ⟨hla.trans hlb.symm, hla⟩
  change (related.card : ℝ) ≤ d * (equal.card : ℝ)
  rw [hrelated, hequal]
  norm_cast
  let energy := ∑ a : κ, (fiber a).card ^ 2
  have hfirst :
      (∑ a : κ, ∑ _b ∈ neighbor a, (fiber a).card ^ 2) ≤ d * energy := by
    calc
      (∑ a : κ, ∑ _b ∈ neighbor a, (fiber a).card ^ 2) =
          ∑ a : κ, (neighbor a).card * (fiber a).card ^ 2 := by
            apply Finset.sum_congr rfl
            intro a ha
            simp
      _ ≤ ∑ a : κ, d * (fiber a).card ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.mul_le_mul_right _ (hdeg a)
      _ = d * energy := by simp [energy, Finset.mul_sum]
  have hswap :
      (∑ a : κ, ∑ b ∈ neighbor a, (fiber b).card ^ 2) =
        ∑ b : κ, ∑ _a ∈ neighbor b, (fiber b).card ^ 2 := by
    calc
      (∑ a : κ, ∑ b ∈ neighbor a, (fiber b).card ^ 2) =
          ∑ a : κ, ∑ b : κ,
            if b ∈ neighbor a then (fiber b).card ^ 2 else 0 := by simp
      _ = ∑ b : κ, ∑ a : κ,
            if b ∈ neighbor a then (fiber b).card ^ 2 else 0 :=
        Finset.sum_comm
      _ = ∑ b : κ, ∑ a : κ,
            if a ∈ neighbor b then (fiber b).card ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro a ha
        simp only [hsymm a b]
      _ = ∑ b : κ, ∑ _a ∈ neighbor b, (fiber b).card ^ 2 := by simp
  have hsecond :
      (∑ a : κ, ∑ b ∈ neighbor a, (fiber b).card ^ 2) ≤ d * energy := by
    rw [hswap]
    exact hfirst
  have htwice :
      2 * (∑ a : κ, ∑ b ∈ neighbor a,
        (fiber a).card * (fiber b).card) ≤ 2 * (d * energy) := by
    calc
      2 * (∑ a : κ, ∑ b ∈ neighbor a,
          (fiber a).card * (fiber b).card) =
          ∑ a : κ, ∑ b ∈ neighbor a,
            2 * ((fiber a).card * (fiber b).card) := by
              simp only [Finset.mul_sum]
      _ ≤ ∑ a : κ, ∑ b ∈ neighbor a,
            ((fiber a).card ^ 2 + (fiber b).card ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        simpa [mul_assoc] using
          (two_mul_le_add_sq (fiber a).card (fiber b).card)
      _ = (∑ a : κ, ∑ _b ∈ neighbor a, (fiber a).card ^ 2) +
          (∑ a : κ, ∑ b ∈ neighbor a, (fiber b).card ^ 2) := by
            simp only [Finset.sum_add_distrib]
      _ ≤ d * energy + d * energy := Nat.add_le_add hfirst hsecond
      _ = 2 * (d * energy) := by omega
  dsimp [energy] at htwice
  omega

theorem same_cyclicCell_implies_circleDistance_lt
    {M : ℕ} (hM : 0 < M) {u v : ℝ}
    (hcell : cyclicCell M u = cyclicCell M v) :
    circleDistance (v - u) < ((M : ℝ)⁻¹) := by
  let fu : ℤ := ⌊(M : ℝ) * Int.fract u⌋
  let fv : ℤ := ⌊(M : ℝ) * Int.fract v⌋
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hfu0 : (0 : ℤ) ≤ fu := by
    exact Int.floor_nonneg.mpr (mul_nonneg hMR.le (Int.fract_nonneg u))
  have hfv0 : (0 : ℤ) ≤ fv := by
    exact Int.floor_nonneg.mpr (mul_nonneg hMR.le (Int.fract_nonneg v))
  have hfuM : fu < (M : ℤ) := by
    rw [Int.floor_lt]
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one u) hMR
  have hfvM : fv < (M : ℤ) := by
    rw [Int.floor_lt]
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one v) hMR
  have hf : fu = fv := by
    unfold cyclicCell at hcell
    change (fu : ZMod M) = (fv : ZMod M) at hcell
    rw [ZMod.intCast_eq_intCast_iff'] at hcell
    rwa [Int.emod_eq_of_lt hfu0 hfuM,
      Int.emod_eq_of_lt hfv0 hfvM] at hcell
  have hulo : (fu : ℝ) ≤ (M : ℝ) * Int.fract u := Int.floor_le _
  have huhi : (M : ℝ) * Int.fract u < (fu : ℝ) + 1 := Int.lt_floor_add_one _
  have hvlo : (fv : ℝ) ≤ (M : ℝ) * Int.fract v := Int.floor_le _
  have hvhi : (M : ℝ) * Int.fract v < (fv : ℝ) + 1 := Int.lt_floor_add_one _
  have hscaled : (M : ℝ) * |Int.fract v - Int.fract u| < 1 := by
    have hscaled' : |(M : ℝ) * (Int.fract v - Int.fract u)| < 1 := by
      rw [abs_lt]
      constructor <;> rw [hf] at hulo huhi <;> nlinarith
    simpa [abs_mul, abs_of_pos hMR] using hscaled'
  have habs : |Int.fract v - Int.fract u| < ((M : ℝ)⁻¹) := by
    simpa using (lt_inv_mul_iff₀ hMR).2 hscaled
  let z : ℤ := ⌊v⌋ - ⌊u⌋
  calc
    circleDistance (v - u) ≤ |(v - u) - (z : ℝ)| :=
      circleDistance_le_abs_sub_int _ z
    _ = |Int.fract v - Int.fract u| := by
      dsimp [z]
      simp only [Int.fract]
      push_cast
      congr 1
      ring
    _ < ((M : ℝ)⁻¹) := habs

theorem circleDistance_lt_implies_mem_cyclicNeighbors
    {M R : ℕ} (hM : 0 < M) {u v : ℝ}
    (hnear : circleDistance (v - u) < (R : ℝ) / (M : ℝ)) :
    cyclicCell M v ∈ cyclicNeighbors M R (cyclicCell M u) := by
  classical
  let A : ℤ := ⌊(M : ℝ) * Int.fract u⌋
  let B : ℤ := ⌊(M : ℝ) * Int.fract v⌋
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨z, hz⟩ :=
    DecimalFactorComplexity.WeightedFourierReduction.exists_int_abs_sub_lt_of_circleDistance_lt
      hnear
  let z' : ℤ := z - ⌊v⌋ + ⌊u⌋
  have hzfract :
      |(Int.fract v - Int.fract u) - (z' : ℝ)| <
        (R : ℝ) / (M : ℝ) := by
    convert hz using 1
    congr 1
    dsimp [z']
    simp only [Int.fract]
    push_cast
    ring
  have hdiv : (M : ℝ) * ((R : ℝ) / (M : ℝ)) = (R : ℝ) := by
    field_simp
  have hzscaled :
      -(R : ℝ) < (M : ℝ) * ((Int.fract v - Int.fract u) - (z' : ℝ)) ∧
        (M : ℝ) * ((Int.fract v - Int.fract u) - (z' : ℝ)) < (R : ℝ) := by
    rw [abs_lt] at hzfract
    constructor
    · have := mul_lt_mul_of_pos_left hzfract.1 hMR
      rw [mul_neg, hdiv] at this
      exact this
    · have := mul_lt_mul_of_pos_left hzfract.2 hMR
      rwa [hdiv] at this
  have hAlo : (A : ℝ) ≤ (M : ℝ) * Int.fract u := Int.floor_le _
  have hAhi : (M : ℝ) * Int.fract u < (A : ℝ) + 1 := Int.lt_floor_add_one _
  have hBlo : (B : ℝ) ≤ (M : ℝ) * Int.fract v := Int.floor_le _
  have hBhi : (M : ℝ) * Int.fract v < (B : ℝ) + 1 := Int.lt_floor_add_one _
  let e : ℤ := B - A - (M : ℤ) * z'
  have hecast :
      (e : ℝ) =
        (M : ℝ) * ((Int.fract v - Int.fract u) - (z' : ℝ)) +
          ((B : ℝ) - (M : ℝ) * Int.fract v) -
          ((A : ℝ) - (M : ℝ) * Int.fract u) := by
    dsimp [e]
    push_cast
    ring
  have heloR : (-(R + 1 : ℤ) : ℝ) < (e : ℝ) := by
    rw [hecast]
    push_cast
    nlinarith
  have hehiR : (e : ℝ) < ((R + 1 : ℤ) : ℝ) := by
    rw [hecast]
    push_cast
    nlinarith
  have helo : -(R + 1 : ℤ) ≤ e := by exact_mod_cast heloR.le
  have hehi : e ≤ (R + 1 : ℤ) := by exact_mod_cast hehiR.le
  have ht0 : 0 ≤ e + (R + 1 : ℤ) := by omega
  have htlt : (e + (R + 1 : ℤ)).toNat < 2 * R + 3 := by
    rw [Int.toNat_lt ht0]
    push_cast
    omega
  let t : Fin (2 * R + 3) := ⟨(e + (R + 1 : ℤ)).toNat, htlt⟩
  simp only [cyclicNeighbors, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨t, ?_⟩
  have htI : ((t : ℕ) : ℤ) = e + (R + 1 : ℤ) := by
    dsimp [t]
    exact Int.toNat_of_nonneg ht0
  have htZ : (((t : ℕ) : ℤ) : ZMod M) =
      ((e + (R + 1 : ℤ) : ℤ) : ZMod M) := by
    exact congrArg (fun w : ℤ => (w : ZMod M)) htI
  unfold cyclicCell
  change (A : ZMod M) + ((t : ℕ) : ℤ) - (R + 1 : ℤ) = (B : ZMod M)
  rw [htZ]
  dsimp [e]
  push_cast
  simp
  ring

/-- Cyclic occupancy comparison at all explicit parameters.  The constant
`2R+3` pays for the cells with offsets `-(R+1), ..., R+1`; wraparound is
implemented in `ZMod M`. -/
theorem orderedCirclePairCount_radius_le
    {M : ℕ} (x : Fin M → ℝ) (R : ℕ) (hM : 0 < M) :
    (orderedCirclePairCount x ((R : ℝ) / (M : ℝ)) : ℝ) ≤
      (2 * R + 3) *
        (orderedCirclePairCount x ((M : ℝ)⁻¹) : ℝ) := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  let label : Fin M → ZMod M := fun i => cyclicCell M (x i)
  let related := (Finset.univ : Finset (Fin M × Fin M)).filter fun ij =>
    label ij.2 ∈ cyclicNeighbors M R (label ij.1)
  let equal := (Finset.univ : Finset (Fin M × Fin M)).filter fun ij =>
    label ij.1 = label ij.2
  have hlarge :
      orderedCirclePairCount x ((R : ℝ) / (M : ℝ)) ≤ related.card := by
    unfold orderedCirclePairCount
    apply Finset.card_le_card
    intro ij hij
    simp only [related, Finset.mem_filter, Finset.mem_univ, true_and]
    exact circleDistance_lt_implies_mem_cyclicNeighbors hM
      ((mem_orderedCirclePairs_iff x _ ij).mp hij)
  have hdegree : (related.card : ℝ) ≤ (2 * R + 3) * (equal.card : ℝ) := by
    simpa [related, equal] using
      labelledPairs_le_degree_mul_equalPairs label
        (cyclicNeighbors M R) (2 * R + 3)
        (cyclicNeighbors_card_le M R)
        (fun _ _ => mem_cyclicNeighbors_symm)
  have hequal : equal.card ≤ orderedCirclePairCount x ((M : ℝ)⁻¹) := by
    unfold orderedCirclePairCount
    apply Finset.card_le_card
    intro ij hij
    have hij' := (Finset.mem_filter.mp hij).2
    rw [mem_orderedCirclePairs_iff]
    exact same_cyclicCell_implies_circleDistance_lt hM hij'
  calc
    (orderedCirclePairCount x ((R : ℝ) / (M : ℝ)) : ℝ) ≤
        (related.card : ℝ) := by exact_mod_cast hlarge
    _ ≤ (2 * R + 3) * (equal.card : ℝ) := hdegree
    _ ≤ (2 * R + 3) *
        (orderedCirclePairCount x ((M : ℝ)⁻¹) : ℝ) := by
      gcongr

/-- The strict ordered microscopic count for the first `M_n=10^n` points of
the fractional decimal orbit of pi. -/
def piMicroscopicPairCount (n : ℕ) : ℕ :=
  orderedCirclePairCount
    (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j)
    ((((10 ^ n : ℕ) : ℝ))⁻¹)

/-- One positive constant controls the strict ordered microscopic count at
every sufficiently large decimal scale.  This is an unproved pi hypothesis. -/
def PiUniformMicroscopicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n →
      (piMicroscopicPairCount n : ℝ) ≤ C * ((10 ^ n : ℕ) : ℝ)

theorem piUniformMicroscopicBound_iff_quantifiers :
    PiUniformMicroscopicBound ↔
      ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
        ∀ n : ℕ, n0 ≤ n →
          (((Finset.univ : Finset (Fin (10 ^ n) × Fin (10 ^ n))).filter
            (fun ij => circleDistance
              (piDecimalShiftOrbit ij.2 - piDecimalShiftOrbit ij.1) <
                (((10 ^ n : ℕ) : ℝ))⁻¹)).card : ℝ) ≤
            C * ((10 ^ n : ℕ) : ℝ) := by
  rfl

/-- T6's exact distance bridge identifies the microscopic orbit count with
the ordered diagonal-inclusive near-return count `Q_pi`. -/
theorem piMicroscopicPairCount_eq_Q_pi (n : ℕ) :
    piMicroscopicPairCount n = Q_pi n (10 ^ n) := by
  classical
  unfold piMicroscopicPairCount orderedCirclePairCount orderedCirclePairs Q_pi
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [circleDistance_piShift_sub_eq_powerDifference]
  rw [mem_piNearReturnPairs_iff]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- The microscopic set is literally C5's `k=0` set. -/
theorem piMicroscopicPairCount_eq_mesoscopic_zero (n : ℕ) :
    piMicroscopicPairCount n = (piMesoscopicNearPairs n 0).card := by
  classical
  unfold piMicroscopicPairCount orderedCirclePairCount orderedCirclePairs
    piMesoscopicNearPairs mesoscopicSampleSize
  apply congrArg Finset.card
  ext ij
  simp

/-- A microscopic constant `C` gives C5 with the explicit uniform constant
`A=3C`, by the cyclic occupancy theorem with `R=2^k`. -/
theorem microscopic_implies_C5_explicit
    (C : ℝ) (hC : 0 < C) (n0 : ℕ) (_hn0 : 1 ≤ n0)
    (hmicro : ∀ n : ℕ, n0 ≤ n →
      (piMicroscopicPairCount n : ℝ) ≤ C * ((10 ^ n : ℕ) : ℝ)) :
    ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
      ((piMesoscopicNearPairs n k).card : ℝ) ≤
        (3 * C) * ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ) := by
  intro n hn k hk
  have hM : 0 < 10 ^ n := by positivity
  have hgeneric := orderedCirclePairCount_radius_le
    (fun j : Fin (10 ^ n) => piDecimalShiftOrbit j) (2 ^ k) hM
  have hcount :
      ((piMesoscopicNearPairs n k).card : ℝ) ≤
        (2 * (2 ^ k) + 3) * (piMicroscopicPairCount n : ℝ) := by
    simpa [piMesoscopicNearPairs, mesoscopicSampleSize,
      piMicroscopicPairCount, orderedCirclePairCount, orderedCirclePairs] using hgeneric
  calc
    ((piMesoscopicNearPairs n k).card : ℝ) ≤
        (2 * (2 ^ k) + 3) * (piMicroscopicPairCount n : ℝ) := hcount
    _ ≤ (2 * (2 ^ k) + 3) * (C * ((10 ^ n : ℕ) : ℝ)) := by
      gcongr
      exact hmicro n hn
    _ ≤ (3 * C) * ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ) := by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hcoef : (2 : ℝ) * (2 : ℝ) ^ k + 3 ≤
          3 * ((2 : ℝ) ^ k + 1) := by linarith
      have hscale := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg hC.le
          (show (0 : ℝ) ≤ ((10 ^ n : ℕ) : ℝ) by positivity))
      calc
        (2 * (2 : ℝ) ^ k + 3) * (C * ((10 ^ n : ℕ) : ℝ)) ≤
            (3 * ((2 : ℝ) ^ k + 1)) *
              (C * ((10 ^ n : ℕ) : ℝ)) := hscale
        _ = (3 * C) * ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ) := by ring

theorem piUniformMicroscopicBound_implies_C5
    (hmicro : PiUniformMicroscopicBound) : PiMesoscopicPairCountC5 := by
  obtain ⟨C, hC, n0, hn0, hall⟩ := hmicro
  exact ⟨3 * C, by positivity, n0, hn0,
    microscopic_implies_C5_explicit C hC n0 hn0 hall⟩

/-- C5 at `k=0` gives the microscopic hypothesis with constant `2A`. -/
theorem C5_implies_microscopic_explicit
    (A : ℝ) (_hA : 0 < A) (n0 : ℕ) (_hn0 : 1 ≤ n0)
    (hC5 : ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
      ((piMesoscopicNearPairs n k).card : ℝ) ≤
        A * ((2 : ℝ) ^ k + 1) * ((10 ^ n : ℕ) : ℝ)) :
    ∀ n : ℕ, n0 ≤ n →
      (piMicroscopicPairCount n : ℝ) ≤
        (2 * A) * ((10 ^ n : ℕ) : ℝ) := by
  intro n hn
  rw [piMicroscopicPairCount_eq_mesoscopic_zero]
  have h := hC5 n hn 0 (one_le_pow₀ (by norm_num))
  norm_num at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

theorem C5_implies_piUniformMicroscopicBound
    (hC5 : PiMesoscopicPairCountC5) : PiUniformMicroscopicBound := by
  obtain ⟨A, hA, n0, hn0, hall⟩ := hC5
  exact ⟨2 * A, by positivity, n0, hn0,
    C5_implies_microscopic_explicit A hA n0 hn0 hall⟩

/-- C4 with energy constant `C` gives microscopic constant `(pi^2/2)C` via
T7 and T6's exact strict-distance bridge. -/
theorem C4_implies_microscopic_explicit
    (C : ℝ) (_hC : 0 < C) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (henergy : ∀ n : ℕ, n0 ≤ n →
      piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
        C * ((10 ^ n : ℕ) : ℝ) ^ 2) :
    ∀ n : ℕ, n0 ≤ n →
      (piMicroscopicPairCount n : ℝ) ≤
        (Real.pi ^ 2 / 2 * C) * ((10 ^ n : ℕ) : ℝ) := by
  intro n hn
  rw [piMicroscopicPairCount_eq_Q_pi]
  exact Q_pi_pow_ten_le_linear_of_energy_bound C n (hn0.trans hn)
    (henergy n hn)

theorem C4_implies_piUniformMicroscopicBound
    (hC4 : PiFejerSpectralHypothesis) : PiUniformMicroscopicBound := by
  obtain ⟨C, hC, n0, hn0, hall⟩ := hC4
  exact ⟨Real.pi ^ 2 / 2 * C, by positivity, n0, hn0,
    C4_implies_microscopic_explicit C hC n0 hn0 hall⟩

/-- The direct C4-to-C5 constant conversion obtained by composing T7's
`(pi^2/2)C` microscopic bound with the cyclic factor `3`. -/
theorem C4_implies_C5_explicit
    (C : ℝ) (hC : 0 < C) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (henergy : ∀ n : ℕ, n0 ≤ n →
      piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
        C * ((10 ^ n : ℕ) : ℝ) ^ 2) :
    ∀ n : ℕ, n0 ≤ n → ∀ k : ℕ, 4 ^ k ≤ 10 ^ n →
      ((piMesoscopicNearPairs n k).card : ℝ) ≤
        (3 * (Real.pi ^ 2 / 2 * C)) * ((2 : ℝ) ^ k + 1) *
          ((10 ^ n : ℕ) : ℝ) := by
  exact microscopic_implies_C5_explicit
    (Real.pi ^ 2 / 2 * C) (by positivity) n0 hn0
      (C4_implies_microscopic_explicit C hC n0 hn0 henergy)

/-- C3 contributes only its `s=1` upper estimate.  Restoring the diagonal
gives the explicit microscopic constant `4`. -/
theorem C3_implies_microscopic_explicit
    (hC3 : PiDecimalShiftPairCorrelationC3) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ n : ℕ, max 1 M0 ≤ n →
      (piMicroscopicPairCount n : ℝ) ≤
        4 * ((10 ^ n : ℕ) : ℝ) := by
  obtain ⟨M0, hM0, hoff⟩ := c3_eventually_offDiagonal_lt_three_mul hC3
  refine ⟨M0, hM0, ?_⟩
  intro n hn
  have hM0n : M0 ≤ n := (le_max_right 1 M0).trans hn
  have hM0pow : M0 ≤ 10 ^ n := hM0n.trans (nat_le_ten_pow n)
  rw [piMicroscopicPairCount_eq_Q_pi]
  have hQ := Q_pi_pow_ten_eq_offDiagonal_add_diagonal n
  have hoff' := hoff (10 ^ n) hM0pow
  calc
    (Q_pi n (10 ^ n) : ℝ) =
        (piOffDiagonalCount 1 (10 ^ n) : ℝ) + ((10 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hQ
    _ ≤ 4 * ((10 ^ n : ℕ) : ℝ) := by linarith

theorem C3_implies_piUniformMicroscopicBound
    (hC3 : PiDecimalShiftPairCorrelationC3) : PiUniformMicroscopicBound := by
  obtain ⟨M0, hM0, hall⟩ := C3_implies_microscopic_explicit hC3
  exact ⟨4, by norm_num, max 1 M0, le_max_left _ _, hall⟩

/-- The three fixed-pi formulations are equivalent as hypotheses; no side is
asserted.  C5-to-C4 is exactly the imported T9 implication. -/
theorem microscopic_iff_C5 :
    PiUniformMicroscopicBound ↔ PiMesoscopicPairCountC5 :=
  ⟨piUniformMicroscopicBound_implies_C5,
    C5_implies_piUniformMicroscopicBound⟩

theorem microscopic_iff_C4 :
    PiUniformMicroscopicBound ↔ PiFejerSpectralHypothesis := by
  constructor
  · intro hmicro
    exact piMesoscopicPairCountC5_implies_C4
      (piUniformMicroscopicBound_implies_C5 hmicro)
  · exact C4_implies_piUniformMicroscopicBound

theorem C4_iff_C5 :
    PiFejerSpectralHypothesis ↔ PiMesoscopicPairCountC5 := by
  rw [← microscopic_iff_C4, microscopic_iff_C5]

/-- Named import boundary for T9's C5-to-C4 direction. -/
theorem C5_implies_C4_via_T9 (hC5 : PiMesoscopicPairCountC5) :
    PiFejerSpectralHypothesis :=
  piMesoscopicPairCountC5_implies_C4 hC5

/-- T9's explicit conversion retains `M=10^n`, `H=M/2`, one uniform cutoff,
and the energy constant `750A+1`. -/
theorem C5_implies_C4_explicit_via_T9 (hC5 : PiMesoscopicPairCountC5) :
    ∃ A : ℝ, 0 < A ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n →
        piFejerEnergy (10 ^ n / 2) (10 ^ n) ≤
          (750 * A + 1) * ((10 ^ n : ℕ) : ℝ) ^ 2 :=
  piMesoscopicPairCountC5_implies_C4_explicit hC5

/-- No decimal stream has more than all `10^n` words of length `n`. -/
theorem canonicalFactorComplexity_le_ten_pow
    (s : Stream (Fin 10)) (n : ℕ) :
    canonicalFactorComplexity s n ≤ 10 ^ n := by
  unfold canonicalFactorComplexity Factor Block
  have hcard := Nat.card_le_card_of_injective
    (f := fun w : {w : Fin n → Fin 10 // w ∈ factorSet s n} => w.1)
    Subtype.val_injective
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin] at hcard
  exact hcard

/-- A linear bound for the strict microscopic ordered pair count yields the
explicit constant-factor maximal complexity bound at the same `n`. -/
theorem factorComplexity_ge_ten_pow_div_of_microscopic_bound
    (C : ℝ) (hC : 0 < C) (n : ℕ)
    (hmicro : (piMicroscopicPairCount n : ℝ) ≤
      C * ((10 ^ n : ℕ) : ℝ)) :
    ((10 ^ n : ℕ) : ℝ) / C ≤
      (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) := by
  let M : ℕ := 10 ^ n
  let p : ℕ := canonicalFactorComplexity piDecimalStream n
  have hMnat : 0 < M := by positivity
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hsquareNat :=
    square_le_observedFactorCount_mul_collisionEnergy piDecimalStream n M
  have hsquare : (M : ℝ) ^ 2 ≤
      (observedFactorCount piDecimalStream n M : ℝ) * (E_pi n M : ℝ) := by
    exact_mod_cast hsquareNat
  have hobsNat :=
    observedFactorCount_le_canonicalFactorComplexity piDecimalStream n M
  have hobs : (observedFactorCount piDecimalStream n M : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hobsNat
  have henergyNat := pi_collisionEnergy_le_Q_pi n M
  have henergy : (E_pi n M : ℝ) ≤ (Q_pi n M : ℝ) := by
    exact_mod_cast henergyNat
  have hQ : (Q_pi n M : ℝ) ≤ C * (M : ℝ) := by
    simpa [M, piMicroscopicPairCount_eq_Q_pi] using hmicro
  have hcombined : (M : ℝ) ^ 2 ≤ (p : ℝ) * (C * (M : ℝ)) := by
    calc
      (M : ℝ) ^ 2 ≤
          (observedFactorCount piDecimalStream n M : ℝ) * (E_pi n M : ℝ) := hsquare
      _ ≤ (p : ℝ) * (E_pi n M : ℝ) := by gcongr
      _ ≤ (p : ℝ) * (Q_pi n M : ℝ) := by gcongr
      _ ≤ (p : ℝ) * (C * (M : ℝ)) := by gcongr
  have hcancel : (M : ℝ) * (M : ℝ) ≤ (M : ℝ) * ((p : ℝ) * C) := by
    calc
      (M : ℝ) * (M : ℝ) = (M : ℝ) ^ 2 := by ring
      _ ≤ (p : ℝ) * (C * (M : ℝ)) := hcombined
      _ = (M : ℝ) * ((p : ℝ) * C) := by ring
  have hMC : (M : ℝ) ≤ (p : ℝ) * C :=
    le_of_mul_le_mul_left hcancel hM
  have hpbound : (M : ℝ) / C ≤ (p : ℝ) := by
    apply (div_le_iff₀ hC).2
    simpa [mul_comm] using hMC
  have hstream : piDecimalStream = Theory.PiDigits.piDigit := by
    funext i
    exact Theory.PiDigits.T20.decimalDigit_pi i
  simpa [M, p, Theory.PiDigits.FactorComplexity.piFactorComplexity,
    hstream] using hpbound

/-- Constant-factor maximal complexity forces full base-ten entropy for an
arbitrary decimal stream. -/
theorem entropyBaseTen_eq_one_of_eventually_ten_pow_div
    (s : Stream (Fin 10)) (C : ℝ) (hC : 0 < C) (n0 : ℕ)
    (hlower : ∀ n : ℕ, n0 ≤ n →
      ((10 ^ n : ℕ) : ℝ) / C ≤ (canonicalFactorComplexity s n : ℝ)) :
    entropyBaseTen s = 1 := by
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hupper : entropyBaseTen s ≤ 1 := by
    have hratio := entropyBaseTen_le_ratio s (n := 1) (by omega)
    have hcount := canonicalFactorComplexity_le_ten_pow s 1
    have hp : (0 : ℝ) < canonicalFactorComplexity s 1 := by
      exact_mod_cast canonicalFactorComplexity_pos s 1
    have hlog : Real.log (canonicalFactorComplexity s 1 : ℝ) ≤ Real.log 10 := by
      apply Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hp)
        (Set.mem_Ioi.mpr (by norm_num))
      exact_mod_cast hcount
    refine hratio.trans ?_
    rw [entropyRatio]
    norm_num
    exact (div_le_one hlogTen).2 hlog
  let lowerRatio : ℕ → ℝ := fun n =>
    1 - (Real.log C / Real.log 10) / (n : ℝ)
  have hlowerTend : Tendsto lowerRatio atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ =>
        (Real.log C / Real.log 10) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [lowerRatio] using tendsto_const_nhds.sub hdiv
  have hevent : ∀ᶠ n : ℕ in atTop, lowerRatio n ≤ entropyRatio s n := by
    filter_upwards [eventually_ge_atTop (max 1 n0)] with n hn
    have hn1 : 1 ≤ n := (le_max_left 1 n0).trans hn
    have hn0 : n0 ≤ n := (le_max_right 1 n0).trans hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hden : 0 < (n : ℝ) * Real.log 10 := mul_pos hnR hlogTen
    have hpow : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by positivity
    have hp : (0 : ℝ) < canonicalFactorComplexity s n := by
      exact_mod_cast canonicalFactorComplexity_pos s n
    have hquot : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) / C := div_pos hpow hC
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hquot) (Set.mem_Ioi.mpr hp) (hlower n hn0)
    unfold lowerRatio entropyRatio
    apply (le_div_iff₀ hden).2
    calc
      (1 - (Real.log C / Real.log 10) / (n : ℝ)) *
          ((n : ℝ) * Real.log 10) =
          Real.log (((10 ^ n : ℕ) : ℝ) / C) := by
        rw [Real.log_div hpow.ne' hC.ne', Nat.cast_pow, Nat.cast_ofNat,
          Real.log_pow]
        field_simp [hnR.ne', hlogTen.ne']
      _ ≤ Real.log (canonicalFactorComplexity s n : ℝ) := hlog
  have hlowerEntropy : 1 ≤ entropyBaseTen s :=
    le_of_tendsto_of_tendsto hlowerTend (entropyRatio_tendsto s) hevent
  exact le_antisymm hupper hlowerEntropy

/-- The microscopic hypothesis gives the agenda's explicit eventual bound
`p_pi(n) >= 10^n/C`. -/
theorem piUniformMicroscopicBound_implies_factorComplexity_explicit
    (hmicro : PiUniformMicroscopicBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n →
        ((10 ^ n : ℕ) : ℝ) / C ≤
          (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) := by
  obtain ⟨C, hC, n0, hn0, hall⟩ := hmicro
  exact ⟨C, hC, n0, hn0, fun n hn =>
    factorComplexity_ge_ten_pow_div_of_microscopic_bound C hC n (hall n hn)⟩

theorem piUniformMicroscopicBound_implies_entropy_eq_one
    (hmicro : PiUniformMicroscopicBound) : piEntropyBaseTen = 1 := by
  obtain ⟨C, hC, n0, hn0, hall⟩ :=
    piUniformMicroscopicBound_implies_factorComplexity_explicit hmicro
  unfold piEntropyBaseTen
  apply entropyBaseTen_eq_one_of_eventually_ten_pow_div
    Theory.PiDigits.piDigit C hC n0
  intro n hn
  simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using hall n hn

theorem piUniformMicroscopicBound_implies_disjunctive
    (hmicro : PiUniformMicroscopicBound) :
    ∀ u : List (Fin 10), ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < u.length,
      Theory.PiDigits.piDigit (i + j) = u.get ⟨j, hj⟩ := by
  exact (pi_entropy_eq_one_iff_canonical_word_quantifiers.mp
    (piUniformMicroscopicBound_implies_entropy_eq_one hmicro))

/-- Each named fixed-pi hypothesis remains a premise of its full-entropy
conclusion. -/
theorem C3_implies_entropy_eq_one (hC3 : PiDecimalShiftPairCorrelationC3) :
    piEntropyBaseTen = 1 :=
  piUniformMicroscopicBound_implies_entropy_eq_one
    (C3_implies_piUniformMicroscopicBound hC3)

theorem C4_implies_entropy_eq_one (hC4 : PiFejerSpectralHypothesis) :
    piEntropyBaseTen = 1 :=
  piUniformMicroscopicBound_implies_entropy_eq_one
    (C4_implies_piUniformMicroscopicBound hC4)

theorem C5_implies_entropy_eq_one (hC5 : PiMesoscopicPairCountC5) :
    piEntropyBaseTen = 1 :=
  piUniformMicroscopicBound_implies_entropy_eq_one
    (C5_implies_piUniformMicroscopicBound hC5)

theorem C3_implies_disjunctive (hC3 : PiDecimalShiftPairCorrelationC3) :
    ∀ u : List (Fin 10), ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < u.length,
      Theory.PiDigits.piDigit (i + j) = u.get ⟨j, hj⟩ :=
  piUniformMicroscopicBound_implies_disjunctive
    (C3_implies_piUniformMicroscopicBound hC3)

theorem C4_implies_disjunctive (hC4 : PiFejerSpectralHypothesis) :
    ∀ u : List (Fin 10), ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < u.length,
      Theory.PiDigits.piDigit (i + j) = u.get ⟨j, hj⟩ :=
  piUniformMicroscopicBound_implies_disjunctive
    (C4_implies_piUniformMicroscopicBound hC4)

theorem C5_implies_disjunctive (hC5 : PiMesoscopicPairCountC5) :
    ∀ u : List (Fin 10), ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < u.length,
      Theory.PiDigits.piDigit (i + j) = u.get ⟨j, hj⟩ :=
  piUniformMicroscopicBound_implies_disjunctive
    (C5_implies_piUniformMicroscopicBound hC5)

end DecimalFactorComplexity.MicroscopicFullEntropy

#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.orderedCirclePairCount_radius_le
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.sampleSize_le_orderedCirclePairCount
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.piUniformMicroscopicBound_iff_quantifiers
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.piMicroscopicPairCount_eq_Q_pi
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.microscopic_implies_C5_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C5_implies_microscopic_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C4_implies_microscopic_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C4_implies_C5_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C3_implies_microscopic_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C3_implies_piUniformMicroscopicBound
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.microscopic_iff_C5
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.microscopic_iff_C4
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C4_iff_C5
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C5_implies_C4_via_T9
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.C5_implies_C4_explicit_via_T9
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.factorComplexity_ge_ten_pow_div_of_microscopic_bound
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.entropyBaseTen_eq_one_of_eventually_ten_pow_div
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.piUniformMicroscopicBound_implies_factorComplexity_explicit
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.piUniformMicroscopicBound_implies_entropy_eq_one
#print axioms DecimalFactorComplexity.MicroscopicFullEntropy.piUniformMicroscopicBound_implies_disjunctive
