import TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging

/-!
# T75: deterministic window-local equality load

Canonical source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file imports the exact T56/T69 conventions and proves the finite window
cover and local-component inverse theorem used by the accompanying note. It
makes no fixed-pi estimate and no claim about C7, C2, C1, or entropy.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.T75WindowLocalLoad

open DecimalFactorComplexity
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T69FiveCaseCharging
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The largest natural number satisfying T56's two strict short-lag bounds. -/
def maxShortLag (n : ℕ) : ℕ :=
  min (n - 1) (t56SampleLength n - 1)

/-- T75 imports exactly T56's natural-division sample length. -/
theorem sampleLength_eq (n : ℕ) :
    t56SampleLength n = 10 ^ (n / 2) := by
  rfl

/-- Exact reformulation of T56/T69's strict short-lag range by its maximum. -/
theorem mem_shortLags_iff {n r : ℕ} :
    r ∈ shortResidualLags n (t56SampleLength n) ↔
      0 < r ∧ r ≤ maxShortLag n := by
  rw [mem_W5_lags_iff]
  simp only [maxShortLag]
  omega

/-- Window `k` consists of quotient blocks `k` and `k+1`, hence is the clipped
half-open interval `[k*h, (k+2)*h) ∩ [0,L)`. For `h=0` it is empty. -/
def localWindow (L h k : ℕ) : Finset (Fin L) :=
  if h = 0 then ∅
  else Finset.univ.filter fun i => i.val / h = k ∨ i.val / h = k + 1

/-- Literal membership rule for the deterministic windows. -/
theorem mem_localWindow_iff {L h k : ℕ} {i : Fin L} :
    i ∈ localWindow L h k ↔
      h ≠ 0 ∧ (i.val / h = k ∨ i.val / h = k + 1) := by
  by_cases hh : h = 0 <;> simp [localWindow, hh]

/-- Every pair at positive distance at most `h` is contained in the window
whose index is the quotient block of its smaller endpoint. -/
theorem pair_mem_localWindow {L h : ℕ} {i j : Fin L}
    (hh : 0 < h) (hij : i.val < j.val) (hdist : j.val - i.val ≤ h) :
    i ∈ localWindow L h (i.val / h) ∧
      j ∈ localWindow L h (i.val / h) := by
  rw [mem_localWindow_iff, mem_localWindow_iff]
  constructor
  · exact ⟨Nat.ne_of_gt hh, Or.inl rfl⟩
  · refine ⟨Nat.ne_of_gt hh, ?_⟩
    have hle : j.val ≤ i.val + h := by omega
    have hqle : j.val / h ≤ i.val / h + 1 := by
      calc
        j.val / h ≤ (i.val + h) / h := Nat.div_le_div_right hle
        _ = i.val / h + 1 := Nat.add_div_right i.val hh
    have hqge : i.val / h ≤ j.val / h := Nat.div_le_div_right (Nat.le_of_lt hij)
    omega

/-- The finite set of retained window indices. Indices beyond `L-1` cannot
contain a point of `Fin L`, so `range L` is a convenient exact finite cover. -/
def windowIndices (L : ℕ) : Finset ℕ := Finset.range L

/-- Windows containing one position. -/
def containingWindows {L : ℕ} (h : ℕ) (i : Fin L) : Finset ℕ :=
  (windowIndices L).filter fun k => i ∈ localWindow L h k

/-- A position is in at most two consecutive windows. -/
theorem containingWindows_card_le_two {L h : ℕ} (i : Fin L) :
    (containingWindows h i).card ≤ 2 := by
  classical
  by_cases hh : h = 0
  · simp [containingWindows, localWindow, hh]
  · let b := i.val / h
    have hsub : containingWindows h i ⊆ ({b, b - 1} : Finset ℕ) := by
      intro k hk
      have hmem := (Finset.mem_filter.mp hk).2
      rw [mem_localWindow_iff] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hmem.2 with hbk | hbk
      · exact Or.inl hbk.symm
      · right
        omega
    calc
      (containingWindows h i).card ≤ ({b, b - 1} : Finset ℕ).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

/-- Total deterministic-window length is at most twice the ambient length. -/
theorem sum_localWindow_card_le_two_mul (L h : ℕ) :
    (∑ k ∈ windowIndices L, (localWindow L h k).card) ≤ 2 * L := by
  classical
  calc
    (∑ k ∈ windowIndices L, (localWindow L h k).card) =
        ∑ k ∈ windowIndices L, ∑ i : Fin L,
          if i ∈ localWindow L h k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      change (localWindow L h k).card =
        ∑ i ∈ (Finset.univ : Finset (Fin L)),
          if i ∈ localWindow L h k then 1 else 0
      rw [← Finset.sum_filter]
      simp
    _ = ∑ i : Fin L, ∑ k ∈ windowIndices L,
          if i ∈ localWindow L h k then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin L, (containingWindows h i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [containingWindows]
    _ ≤ ∑ _i : Fin L, 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact containingWindows_card_le_two i
    _ = 2 * L := by simp [Nat.mul_comm]

/-- Multiplicity of label `a` in deterministic window `k`. -/
def windowMultiplicity {L q : ℕ} (x : Fin L → Fin q) (h k : ℕ)
    (a : Fin q) : ℕ :=
  ((localWindow L h k).filter fun i => x i = a).card

/-- The requested local equality load. The falling factorial removes all
diagonal pairs and is independent of W5. -/
def ALoc {L q : ℕ} (x : Fin L → Fin q) (h : ℕ) : ℕ :=
  ∑ k ∈ windowIndices L, ∑ a : Fin q,
    windowMultiplicity x h k a * (windowMultiplicity x h k a - 1)

/-- The T75 statistic at exactly T56's sample length and maximum short lag. -/
def t75ALoc (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) : ℕ :=
  ALoc x (maxShortLag n)

/-- Literal scale audit for the T75 specialization. -/
theorem t75ALoc_eq (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    t75ALoc n x = ALoc x (maxShortLag n) := by
  rfl

/-- The fixed-pi local-load estimate isolated by T75. This is only a
definition of the open frontier; no theorem below supplies an inhabitant. -/
def PiALocLinearBound : Prop :=
  ∃ K N : ℕ, 0 < K ∧ 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      t75ALoc n (piLabelSequence n) ≤ K * t56SampleLength n

/-- Quantifier audit for the explicitly unproved fixed-pi frontier. -/
theorem piALocLinearBound_iff_quantifiers :
    PiALocLinearBound ↔
      ∃ K N : ℕ, 0 < K ∧ 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          t75ALoc n (piLabelSequence n) ≤ K * t56SampleLength n := by
  rfl

/-- Multiplicities partition a window exactly. -/
theorem sum_windowMultiplicity_eq_card {L q : ℕ} (x : Fin L → Fin q)
    (h k : ℕ) :
    ∑ a : Fin q, windowMultiplicity x h k a = (localWindow L h k).card := by
  classical
  simpa [windowMultiplicity] using (Finset.card_eq_sum_card_fiberwise
    (s := localWindow L h k) (t := (Finset.univ : Finset (Fin q)))
    (f := x) (by simp)).symm

/-- A uniform local multiplicity cap `K` bounds the local load by `2*K*L`.
This is the load-bearing estimate behind the inverse theorem. -/
theorem ALoc_le_two_mul_of_multiplicity_le {L q h K : ℕ}
    (x : Fin L → Fin q)
    (hcap : ∀ k ∈ windowIndices L, ∀ a : Fin q,
      windowMultiplicity x h k a ≤ K) :
    ALoc x h ≤ 2 * K * L := by
  classical
  unfold ALoc
  calc
    (∑ k ∈ windowIndices L, ∑ a : Fin q,
        windowMultiplicity x h k a * (windowMultiplicity x h k a - 1)) ≤
        ∑ k ∈ windowIndices L, K * (localWindow L h k).card := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (∑ a : Fin q,
            windowMultiplicity x h k a * (windowMultiplicity x h k a - 1)) ≤
            ∑ a : Fin q, K * windowMultiplicity x h k a := by
          apply Finset.sum_le_sum
          intro a _ha
          have ha := hcap k hk a
          have hsub : windowMultiplicity x h k a - 1 ≤ K :=
            (Nat.sub_le (windowMultiplicity x h k a) 1).trans ha
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left (windowMultiplicity x h k a) hsub
        _ = K * (localWindow L h k).card := by
          rw [← sum_windowMultiplicity_eq_card x h k]
          simp [Finset.mul_sum]
    _ = K * (∑ k ∈ windowIndices L, (localWindow L h k).card) := by
      rw [Finset.mul_sum]
    _ ≤ K * (2 * L) := Nat.mul_le_mul_left K (sum_localWindow_card_le_two_mul L h)
    _ = 2 * K * L := by ring

/-- Quantitative local-component inverse theorem: load greater than `2*K*L`
forces one label to occur more than `K` times in one retained window. -/
theorem exists_local_component_gt_of_two_mul_lt_ALoc {L q h K : ℕ}
    (x : Fin L → Fin q) (hlarge : 2 * K * L < ALoc x h) :
    ∃ k ∈ windowIndices L, ∃ a : Fin q, K < windowMultiplicity x h k a := by
  classical
  by_contra hnot
  push Not at hnot
  have hupper := ALoc_le_two_mul_of_multiplicity_le x hnot
  omega

/-- Injective labels have zero local equality load, regardless of windows. -/
theorem ALoc_eq_zero_of_injective {L q h : ℕ} (x : Fin L → Fin q)
    (hinj : Function.Injective x) :
    ALoc x h = 0 := by
  classical
  unfold ALoc
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro a ha
  suffices windowMultiplicity x h k a ≤ 1 by
    have hz : windowMultiplicity x h k a - 1 = 0 := by omega
    simp [hz]
  rw [windowMultiplicity, Finset.card_le_one]
  intro i hi j hj
  exact hinj ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

end DecimalFactorComplexity.T75WindowLocalLoad

#print axioms DecimalFactorComplexity.T75WindowLocalLoad.sampleLength_eq
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.mem_shortLags_iff
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.pair_mem_localWindow
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.containingWindows_card_le_two
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.sum_localWindow_card_le_two_mul
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.t75ALoc_eq
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.piALocLinearBound_iff_quantifiers
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.sum_windowMultiplicity_eq_card
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.ALoc_le_two_mul_of_multiplicity_le
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.exists_local_component_gt_of_two_mul_lt_ALoc
#print axioms DecimalFactorComplexity.T75WindowLocalLoad.ALoc_eq_zero_of_injective
