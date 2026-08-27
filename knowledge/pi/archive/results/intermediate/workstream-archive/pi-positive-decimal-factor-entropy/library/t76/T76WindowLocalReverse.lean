import TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit
import TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging
import TheoryLib.PiPositiveDecimalFactorEntropy.T75T75WindowLocalLoad

/-!
# T76: uniform reverse comparison for the T75 window-local load

Canonical source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file uses the imported T56 sample length and strict short-lag range,
T69 five-case weight `W5`, and T75 deterministic windows and load `t75ALoc`.
It proves the arbitrary-sequence reverse comparison with constants `4` and
`2`. It makes no assertion about pi, C7, C2, C1, or entropy.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.T76WindowLocalReverse

open DecimalFactorComplexity
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T69FiveCaseCharging
open DecimalFactorComplexity.T75WindowLocalLoad
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- One quotient block for T75's block width. This is only an auxiliary
partition used to analyze the imported two-block windows. -/
def quotientBlock (L h k : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun i => i.val / h = k

/-- Multiplicity of one imported decimal label in one quotient block. -/
def blockMultiplicity {L q : ℕ} (x : Fin L → Fin q) (h k : ℕ)
    (a : Fin q) : ℕ :=
  ((quotientBlock L h k).filter fun i => x i = a).card

/-- Falling-factorial equality load inside one quotient block. -/
def blockLoadAt {L q : ℕ} (x : Fin L → Fin q) (h k : ℕ) : ℕ :=
  ∑ a : Fin q,
    blockMultiplicity x h k a * (blockMultiplicity x h k a - 1)

/-- Total equality load inside the quotient blocks meeting `Fin L`. -/
def blockLoad {L q : ℕ} (x : Fin L → Fin q) (h : ℕ) : ℕ :=
  ∑ k ∈ windowIndices L, blockLoadAt x h k

/-- Ordered, distinct, equal-label pairs lying in one quotient block. -/
def sameBlockEqualPairs {L q : ℕ} (x : Fin L → Fin q) (h : ℕ) :
    Finset (Fin L × Fin L) :=
  Finset.univ.filter fun ij =>
    ij.1 ≠ ij.2 ∧ ij.1.val / h = ij.2.val / h ∧ x ij.1 = x ij.2

/-- The forward-oriented half of `sameBlockEqualPairs`. -/
def forwardSameBlockEqualPairs {L q : ℕ} (x : Fin L → Fin q) (h : ℕ) :
    Finset (Fin L × Fin L) :=
  (sameBlockEqualPairs x h).filter fun ij => ij.1.val < ij.2.val

/-- T69's short lags paired with their exact endpoint-safe start sets. -/
def adjacentShortStartPairs (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    Finset (Σ _r : ℕ, ℕ) :=
  (shortResidualLags n (t56SampleLength n)).sigma fun r =>
    adjacentStarts n x r

/-- T75's imported window is exactly the union of two consecutive quotient
blocks when its width is positive. -/
theorem localWindow_eq_quotientBlock_union {L h k : ℕ} (hh : h ≠ 0) :
    localWindow L h k =
      quotientBlock L h k ∪ quotientBlock L h (k + 1) := by
  ext i
  simp [localWindow, quotientBlock, hh]

/-- Consecutive quotient blocks are disjoint. -/
theorem quotientBlock_disjoint_succ {L h k : ℕ} :
    Disjoint (quotientBlock L h k) (quotientBlock L h (k + 1)) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [quotientBlock, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi hj
  omega

/-- T75 window multiplicity is the sum of the two block multiplicities. -/
theorem windowMultiplicity_eq_blockMultiplicity_add {L q h k : ℕ}
    (x : Fin L → Fin q) (hh : h ≠ 0) (a : Fin q) :
    windowMultiplicity x h k a =
      blockMultiplicity x h k a + blockMultiplicity x h (k + 1) a := by
  unfold windowMultiplicity blockMultiplicity
  rw [localWindow_eq_quotientBlock_union hh, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact quotientBlock_disjoint_succ.mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The elementary two-block falling-factorial inequality. -/
theorem falling_add_le (u v : ℕ) :
    (u + v) * (u + v - 1) ≤
      2 * (u * (u - 1) + v * (v - 1)) + (u + v) := by
  by_cases hu : u = 0
  · subst u
    simp
    omega
  by_cases hv : v = 0
  · subst v
    simp
    omega
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu
  have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr hv
  have huv1 : 1 ≤ u + v := by omega
  have hz :
      ((u : ℤ) + (v : ℤ)) * ((u : ℤ) + (v : ℤ) - 1) ≤
        2 * ((u : ℤ) * ((u : ℤ) - 1) +
          (v : ℤ) * ((v : ℤ) - 1)) + ((u : ℤ) + (v : ℤ)) := by
    nlinarith [sq_nonneg ((u : ℤ) - (v : ℤ))]
  exact_mod_cast hz

/-- One T75 window is controlled by twice its two internal block loads plus
the exact cardinality of the imported window. -/
theorem windowLoad_le {L q h k : ℕ} (x : Fin L → Fin q) (hh : h ≠ 0) :
    (∑ a : Fin q,
      windowMultiplicity x h k a * (windowMultiplicity x h k a - 1)) ≤
      2 * (blockLoadAt x h k + blockLoadAt x h (k + 1)) +
        (localWindow L h k).card := by
  classical
  calc
    (∑ a : Fin q,
        windowMultiplicity x h k a * (windowMultiplicity x h k a - 1)) ≤
        ∑ a : Fin q,
          (2 * (blockMultiplicity x h k a *
                (blockMultiplicity x h k a - 1) +
              blockMultiplicity x h (k + 1) a *
                (blockMultiplicity x h (k + 1) a - 1)) +
            windowMultiplicity x h k a) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [windowMultiplicity_eq_blockMultiplicity_add x hh a]
      exact falling_add_le _ _
    _ = 2 * (blockLoadAt x h k + blockLoadAt x h (k + 1)) +
          ∑ a : Fin q, windowMultiplicity x h k a := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_add_distrib
    _ = 2 * (blockLoadAt x h k + blockLoadAt x h (k + 1)) +
          (localWindow L h k).card := by
      rw [sum_windowMultiplicity_eq_card]

/-- A quotient block beyond the ambient index range is empty. -/
theorem blockLoadAt_eq_zero_of_length_le {L q h k : ℕ}
    (x : Fin L → Fin q) (hk : L ≤ k) :
    blockLoadAt x h k = 0 := by
  unfold blockLoadAt
  apply Finset.sum_eq_zero
  intro a _ha
  suffices blockMultiplicity x h k a = 0 by simp [this]
  unfold blockMultiplicity quotientBlock
  rw [Finset.card_eq_zero]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, _hlabel⟩
    have hdiv : i.val / h ≤ i.val := Nat.div_le_self i.val h
    exfalso
    omega
  · intro hi
    simp at hi

/-- Pulling the first term from a finite range bounds the shifted sum when the
last term vanishes. -/
theorem sum_range_shift_le (f : ℕ → ℕ) (L : ℕ) (hL : f L = 0) :
    (∑ k ∈ Finset.range L, f (k + 1)) ≤
      ∑ k ∈ Finset.range L, f k := by
  have hlast := Finset.sum_range_succ f L
  have hfirst := Finset.sum_range_succ' f L
  rw [hL, add_zero] at hlast
  omega

/-- Summing the two-block estimate gives the generic `4*blockLoad+2*L`
bound, retaining T75's exact overlap and endpoint conventions. -/
theorem ALoc_le_four_mul_blockLoad_add_two_mul {L q h : ℕ}
    (x : Fin L → Fin q) (hh : 0 < h) :
    ALoc x h ≤ 4 * blockLoad x h + 2 * L := by
  classical
  let shifted := ∑ k ∈ windowIndices L, blockLoadAt x h (k + 1)
  let windowMass := ∑ k ∈ windowIndices L, (localWindow L h k).card
  have hshifted : shifted ≤ blockLoad x h := by
    change (∑ k ∈ Finset.range L, blockLoadAt x h (k + 1)) ≤
      ∑ k ∈ Finset.range L, blockLoadAt x h k
    exact sum_range_shift_le (fun k => blockLoadAt x h k) L
      (blockLoadAt_eq_zero_of_length_le x (le_refl L))
  have hmass : windowMass ≤ 2 * L := by
    exact sum_localWindow_card_le_two_mul L h
  have hwindow :
      ALoc x h ≤ 2 * (blockLoad x h + shifted) + windowMass := by
    unfold ALoc
    calc
      (∑ k ∈ windowIndices L, ∑ a : Fin q,
          windowMultiplicity x h k a *
            (windowMultiplicity x h k a - 1)) ≤
          ∑ k ∈ windowIndices L,
            (2 * (blockLoadAt x h k + blockLoadAt x h (k + 1)) +
              (localWindow L h k).card) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact windowLoad_le x (Nat.ne_of_gt hh)
      _ = 2 * (blockLoad x h + shifted) + windowMass := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]
        rfl
  calc
    ALoc x h ≤ 2 * (blockLoad x h + shifted) + windowMass := hwindow
    _ ≤ 2 * (blockLoad x h + blockLoad x h) + 2 * L := by
      gcongr
    _ = 4 * blockLoad x h + 2 * L := by ring

/-- The block falling-factorial load is exactly the cardinality of ordered,
distinct, same-label pairs in one quotient block. -/
theorem blockLoad_eq_sameBlockEqualPairs_card {L q h : ℕ}
    (x : Fin L → Fin q) :
    blockLoad x h = (sameBlockEqualPairs x h).card := by
  classical
  let S := sameBlockEqualPairs x h
  let f : Fin L × Fin L → ℕ := fun ij => ij.1.val / h
  have hmaps : Set.MapsTo f (S : Set (Fin L × Fin L))
      (Finset.range L : Set ℕ) := by
    intro ij hij
    have hdiv : ij.1.val / h ≤ ij.1.val := Nat.div_le_self ij.1.val h
    exact Finset.mem_range.mpr (hdiv.trans_lt ij.1.isLt)
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := Finset.range L) (f := f) hmaps
  unfold blockLoad blockLoadAt windowIndices
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro k hk
  let Sk := S.filter fun ij => f ij = k
  have hlabelMaps : Set.MapsTo (fun ij => x ij.1)
      (Sk : Set (Fin L × Fin L))
      ((Finset.univ : Finset (Fin q)) : Set (Fin q)) := by
    intro ij hij
    simp
  have hlabelPartition := Finset.card_eq_sum_card_fiberwise
    (s := Sk) (t := (Finset.univ : Finset (Fin q)))
    (f := fun ij => x ij.1) hlabelMaps
  change (∑ a : Fin q,
      blockMultiplicity x h k a * (blockMultiplicity x h k a - 1)) = Sk.card
  rw [hlabelPartition]
  apply Finset.sum_congr rfl
  intro a _ha
  let F := (quotientBlock L h k).filter fun i => x i = a
  have hfiber : Sk.filter (fun ij => x ij.1 = a) = F.offDiag := by
    ext ij
    simp only [Sk, S, sameBlockEqualPairs, f, F, quotientBlock,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨hne, hquot, heq⟩, hk1⟩, ha1⟩
      exact ⟨⟨hk1, ha1⟩, ⟨hquot ▸ hk1, heq ▸ ha1⟩, hne⟩
    · rintro ⟨⟨hk1, ha1⟩, ⟨hk2, ha2⟩, hne⟩
      exact ⟨⟨⟨hne, hk1.trans hk2.symm, ha1.trans ha2.symm⟩, hk1⟩, ha1⟩
  rw [hfiber, Finset.offDiag_card]
  change F.card * (F.card - 1) = F.card * F.card - F.card
  rw [Nat.mul_sub_left_distrib]
  simp

/-- Swapping endpoints identifies the two orientations of the same-block
pair set. -/
theorem sameBlockEqualPairs_card_eq_two_mul_forward {L q h : ℕ}
    (x : Fin L → Fin q) :
    (sameBlockEqualPairs x h).card =
      2 * (forwardSameBlockEqualPairs x h).card := by
  classical
  let S := sameBlockEqualPairs x h
  let U := S.filter fun ij => ij.1.val < ij.2.val
  let V := S.filter fun ij => ij.2.val < ij.1.val
  have hpartition : S = U ∪ V := by
    ext ij
    simp only [U, V, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hij
      have hdata : ij.1 ≠ ij.2 ∧ ij.1.val / h = ij.2.val / h ∧
          x ij.1 = x ij.2 := by
        simpa [S, sameBlockEqualPairs] using hij
      have hne : ij.1 ≠ ij.2 := hdata.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hij, hlt⟩
      · exact Or.inr ⟨hij, hgt⟩
    · rintro (⟨hij, _⟩ | ⟨hij, _⟩) <;> exact hij
  have hdisjoint : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro ij hijU hijV
    simp only [U, V, Finset.mem_filter] at hijU hijV
    omega
  have hcard : U.card = V.card := by
    apply Finset.card_bijective Prod.swap Prod.swap_bijective
    intro ij
    simp only [U, V, S, sameBlockEqualPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hne, hquot, heq⟩, hlt⟩
      exact ⟨⟨Ne.symm hne, hquot.symm, heq.symm⟩, hlt⟩
    · rintro ⟨⟨hne, hquot, heq⟩, hlt⟩
      exact ⟨⟨Ne.symm hne, hquot.symm, heq.symm⟩, hlt⟩
  change S.card = 2 * U.card
  rw [hpartition, Finset.card_union_of_disjoint hdisjoint, ← hcard]
  omega

/-- T69's definition is twice the cardinality of the exact lag/start sigma. -/
theorem W5_eq_two_mul_adjacentShortStartPairs_card (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    W5 n x = 2 * (adjacentShortStartPairs n x).card := by
  simp [W5, adjacentShortStartPairs, Finset.card_sigma]

/-- Equal-label endpoints in one positive-width quotient block have distance
strictly below the block width. -/
theorem sub_lt_of_same_quotient {i j h : ℕ} (hh : 0 < h)
    (hij : i < j) (hq : i / h = j / h) :
    j - i < h := by
  have hi := Nat.div_add_mod i h
  have hj := Nat.div_add_mod j h
  have himod := Nat.mod_lt i hh
  have hjmod := Nat.mod_lt j hh
  rw [← hq] at hj
  omega

/-- Every forward same-block equality pair maps injectively to T69's exact
short-lag/start sigma at T75's maximum short lag. -/
theorem forwardSameBlockEqualPairs_card_le_adjacentShortStartPairs_card
    (n : ℕ) (x : Fin (t56SampleLength n) → Fin (10 ^ n))
    (hh : 0 < maxShortLag n) :
    (forwardSameBlockEqualPairs x (maxShortLag n)).card ≤
      (adjacentShortStartPairs n x).card := by
  classical
  let f : Fin (t56SampleLength n) × Fin (t56SampleLength n) →
      (Σ _r : ℕ, ℕ) := fun ij => ⟨ij.2.val - ij.1.val, ij.1.val⟩
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro ij hij
    change ij ∈ forwardSameBlockEqualPairs x (maxShortLag n) at hij
    simp only [forwardSameBlockEqualPairs, sameBlockEqualPairs,
      Finset.mem_filter, Finset.mem_univ, true_and] at hij
    rcases hij with ⟨⟨hne, hquot, heq⟩, hlt⟩
    let r := ij.2.val - ij.1.val
    have hrpos : 0 < r := by omega
    have hrlt : r < maxShortLag n :=
      sub_lt_of_same_quotient hh hlt hquot
    have hlag : r ∈ shortResidualLags n (t56SampleLength n) :=
      mem_shortLags_iff.mpr ⟨hrpos, Nat.le_of_lt hrlt⟩
    have hadd : ij.1.val + r = ij.2.val := by omega
    have hstart : ij.1.val ∈ adjacentStarts n x r := by
      simp only [adjacentStarts, Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · simp [finiteLabelAt, Nat.mod_eq_of_lt ij.1.isLt,
          hadd, Nat.mod_eq_of_lt ij.2.isLt, CyclicAdjacent, heq]
    change (⟨r, ij.1.val⟩ : Σ _r : ℕ, ℕ) ∈ adjacentShortStartPairs n x
    exact Finset.mem_sigma.mpr ⟨hlag, hstart⟩
  · intro a ha b hb hab
    have hr : a.2.val - a.1.val = b.2.val - b.1.val :=
      congrArg Sigma.fst hab
    have hi : a.1.val = b.1.val :=
      congrArg (fun z : (Σ _r : ℕ, ℕ) => z.2) hab
    change a ∈ forwardSameBlockEqualPairs x (maxShortLag n) at ha
    change b ∈ forwardSameBlockEqualPairs x (maxShortLag n) at hb
    simp only [forwardSameBlockEqualPairs, sameBlockEqualPairs,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨_ha, haltt⟩
    rcases hb with ⟨_hb, hbltt⟩
    apply Prod.ext
    · exact Fin.ext hi
    · apply Fin.ext
      omega

/-- Every ordered equal-label pair internal to a quotient block is counted by
T69's imported five-case short-lag weight. -/
theorem blockLoad_le_W5 (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n))
    (hh : 0 < maxShortLag n) :
    blockLoad x (maxShortLag n) ≤ W5 n x := by
  rw [blockLoad_eq_sameBlockEqualPairs_card,
    sameBlockEqualPairs_card_eq_two_mul_forward,
    W5_eq_two_mul_adjacentShortStartPairs_card]
  exact Nat.mul_le_mul_left 2
    (forwardSameBlockEqualPairs_card_le_adjacentShortStartPairs_card n x hh)

/-- Universal reverse comparison using literally T56's sample normalization,
T69's `W5`, and T75's `t75ALoc`. The constants are `C0=4`, `C1=2`, and the
theorem holds at every natural scale. -/
theorem t75ALoc_le_four_mul_W5_add_two_mul (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    t75ALoc n x ≤ 4 * W5 n x + 2 * t56SampleLength n := by
  by_cases hh : maxShortLag n = 0
  · simp [t75ALoc, ALoc, windowMultiplicity, localWindow, hh]
  · rw [t75ALoc_eq]
    calc
      ALoc x (maxShortLag n) ≤
          4 * blockLoad x (maxShortLag n) + 2 * t56SampleLength n :=
        ALoc_le_four_mul_blockLoad_add_two_mul x (Nat.pos_of_ne_zero hh)
      _ ≤ 4 * W5 n x + 2 * t56SampleLength n := by
        gcongr
        exact blockLoad_le_W5 n x (Nat.pos_of_ne_zero hh)

/-- Literal eventual quantified form, with explicit witnesses `4`, `2`, and
`N=1`. -/
theorem exists_uniform_reverse_comparison :
    ∃ C0 C1 N : ℕ, C0 = 4 ∧ C1 = 2 ∧ N = 1 ∧
      ∀ n : ℕ, N ≤ n →
        ∀ x : Fin (t56SampleLength n) → Fin (10 ^ n),
          t75ALoc n x ≤ C0 * W5 n x + C1 * t56SampleLength n := by
  refine ⟨4, 2, 1, rfl, rfl, rfl, ?_⟩
  intro n _hn x
  exact t75ALoc_le_four_mul_W5_add_two_mul n x

end DecimalFactorComplexity.T76WindowLocalReverse

#print axioms DecimalFactorComplexity.T76WindowLocalReverse.t75ALoc_le_four_mul_W5_add_two_mul
#print axioms DecimalFactorComplexity.T76WindowLocalReverse.exists_uniform_reverse_comparison
