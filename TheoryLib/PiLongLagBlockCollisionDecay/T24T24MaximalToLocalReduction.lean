import TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff
import Mathlib.Data.Nat.BitIndices

/-!
# T24: deterministic maximal-to-local reduction

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file formalizes only a deterministic implication. It does not prove the
localized hypothesis at `Real.pi`, a fixed-`pi` spectral estimate, or C1.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T24

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22

/-- A half-open endpoint block `[start, start + 2^level)`. -/
structure DyadicBlock where
  start : ℕ
  level : ℕ
deriving DecidableEq

namespace DyadicBlock

/-- The exact power-of-two length of a binary block. -/
def blockLength (B : DyadicBlock) : ℕ := 2 ^ B.level

/-- The excluded right endpoint of a binary block. -/
def finish (B : DyadicBlock) : ℕ := B.start + B.blockLength

/-- Alignment on the endpoint grid translated by one. -/
def Aligned (B : DyadicBlock) : Prop := B.blockLength ∣ B.start - 1

/-- The local telescoping budget `L + ((a+L)^2-a^2) rho`. -/
def budget (ρ : ℝ) (B : DyadicBlock) : ℝ :=
  (B.blockLength : ℝ) +
    ((B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2) * ρ

end DyadicBlock

/-- Sum of the power-of-two lengths encoded by a list of levels. -/
def dyadicLevelSum (js : List ℕ) : ℕ :=
  (js.map fun j => 2 ^ j).sum

/-- Consecutive dyadic blocks, with `q` the already consumed zero-based length. -/
def dyadicPartitionFrom (q : ℕ) : List ℕ → List DyadicBlock
  | [] => []
  | j :: js =>
      ⟨q + 1, j⟩ :: dyadicPartitionFrom (q + 2 ^ j) js

/-- The canonical binary partition of endpoint layers `[1,N)`, using the
nonzero binary digits of `N-1` in strictly decreasing order. -/
def canonicalDyadicPartition (N : ℕ) : List DyadicBlock :=
  dyadicPartitionFrom 0 (N - 1).bitIndices.reverse

theorem dyadicPartitionFrom_levels (q : ℕ) (js : List ℕ) :
    (dyadicPartitionFrom q js).map DyadicBlock.level = js := by
  induction js generalizing q with
  | nil => rfl
  | cons j js ih => simp [dyadicPartitionFrom, ih]

theorem dyadicPartitionFrom_sum_length (q : ℕ) (js : List ℕ) :
    ((dyadicPartitionFrom q js).map DyadicBlock.blockLength).sum =
      dyadicLevelSum js := by
  induction js generalizing q with
  | nil => rfl
  | cons j js ih => simp [dyadicPartitionFrom, DyadicBlock.blockLength,
      dyadicLevelSum, ih]

theorem canonicalDyadicPartition_levels (N : ℕ) :
    (canonicalDyadicPartition N).map DyadicBlock.level =
      (N - 1).bitIndices.reverse := by
  exact dyadicPartitionFrom_levels _ _

theorem canonicalDyadicPartition_sum_length (N : ℕ) :
    ((canonicalDyadicPartition N).map DyadicBlock.blockLength).sum = N - 1 := by
  rw [canonicalDyadicPartition, dyadicPartitionFrom_sum_length]
  simp [dyadicLevelSum]

theorem dyadicPartitionFrom_start_pos
    {q : ℕ} {js : List ℕ} {B : DyadicBlock}
    (hB : B ∈ dyadicPartitionFrom q js) : 1 ≤ B.start := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp
      · exact ih hB

theorem dyadicPartitionFrom_aligned
    (q : ℕ) (js : List ℕ)
    (hdesc : js.Pairwise fun j k => k < j)
    (hq : ∀ j ∈ js, 2 ^ j ∣ q) :
    ∀ B ∈ dyadicPartitionFrom q js, B.Aligned := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom]
  | cons j js ih =>
      rw [List.pairwise_cons] at hdesc
      intro B hB
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp [DyadicBlock.Aligned, DyadicBlock.blockLength, hq j]
      · apply ih (q := q + 2 ^ j) hdesc.2
        · intro k hk
          exact (hq k (by simp [hk])).add
            ((Nat.pow_dvd_pow 2 (Nat.le_of_lt (hdesc.1 k hk))))
        · exact hB

theorem canonicalDyadicPartition_start_pos
    {N : ℕ} {B : DyadicBlock}
    (hB : B ∈ canonicalDyadicPartition N) : 1 ≤ B.start := by
  exact dyadicPartitionFrom_start_pos hB

theorem canonicalDyadicPartition_aligned
    {N : ℕ} {B : DyadicBlock}
    (hB : B ∈ canonicalDyadicPartition N) :
    2 ^ B.level ∣ B.start - 1 := by
  apply dyadicPartitionFrom_aligned 0 (N - 1).bitIndices.reverse
  · exact Nat.bitIndices_sorted.pairwise.reverse
  · intro j hj
    exact dvd_zero _
  · exact hB

theorem dyadicPartitionFrom_endpoint_telescope
    {A : Type*} [AddCommGroup A]
    (F : ℕ → A) (q : ℕ) (js : List ℕ) :
    ((dyadicPartitionFrom q js).map
        (fun B => F B.finish - F B.start)).sum =
      F (q + dyadicLevelSum js + 1) - F (q + 1) := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom, dyadicLevelSum]
  | cons j js ih =>
      change (F (q + 1 + 2 ^ j) - F (q + 1)) +
          ((dyadicPartitionFrom (q + 2 ^ j) js).map
            (fun B => F B.finish - F B.start)).sum =
        F (q + dyadicLevelSum (j :: js) + 1) - F (q + 1)
      rw [ih]
      have hleft : q + 1 + 2 ^ j = q + 2 ^ j + 1 := by omega
      have hright : q + dyadicLevelSum (j :: js) + 1 =
          q + 2 ^ j + dyadicLevelSum js + 1 := by
        simp [dyadicLevelSum]
        omega
      rw [hleft, hright]
      abel

theorem canonicalDyadicPartition_endpoint_telescope
    {A : Type*} [AddCommGroup A]
    (F : ℕ → A) {N : ℕ} (hN : 1 ≤ N) :
    ((canonicalDyadicPartition N).map
        (fun B => F B.finish - F B.start)).sum = F N - F 1 := by
  rw [canonicalDyadicPartition, dyadicPartitionFrom_endpoint_telescope]
  rw [show dyadicLevelSum (N - 1).bitIndices.reverse = N - 1 by
    simp [dyadicLevelSum]]
  simpa [Nat.sub_add_cancel hN]

/-- The exact successor endpoint layer `P_(E+1)-P_E`. -/
def endpointIncrement
    (μ c : ℝ) (Q0 m E : ℕ) (h : ℤ) (α : ℝ) : ℂ :=
  cutoffFourierSum μ c Q0 m (E + 1) h α -
    cutoffFourierSum μ c Q0 m E h α

/-- The exact cutoff increment across one aligned binary block. -/
def dyadicBlockIncrement
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock)
    (h : ℤ) (α : ℝ) : ℂ :=
  cutoffFourierSum μ c Q0 m B.finish h α -
    cutoffFourierSum μ c Q0 m B.start h α

theorem dyadicBlockIncrement_eq_sum_endpointIncrement
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (h : ℤ) (α : ℝ) :
    dyadicBlockIncrement μ c Q0 m B h α =
      ∑ E ∈ Finset.Ico B.start B.finish,
        endpointIncrement μ c Q0 m E h α := by
  unfold dyadicBlockIncrement endpointIncrement
  simpa only [DyadicBlock.finish] using (Finset.sum_Ico_sub
    (fun E => cutoffFourierSum μ c Q0 m E h α)
    (Nat.le_add_right B.start B.blockLength)).symm

/-- Vector L1 norm on the exact inclusive frequency range `1 <= h <= 10^m`. -/
def vectorL1 (m : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m), ‖v h‖

/-- L1 norm of one exact binary cutoff increment. -/
def dyadicBlockL1
    (μ c : ℝ) (Q0 m : ℕ) (B : DyadicBlock) (α : ℝ) : ℝ :=
  vectorL1 m (fun h => dyadicBlockIncrement μ c Q0 m B (h : ℤ) α)

theorem vectorL1_add_le (m : ℕ) (v w : ℕ → ℂ) :
    vectorL1 m (fun h => v h + w h) ≤ vectorL1 m v + vectorL1 m w := by
  unfold vectorL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  exact norm_add_le _ _

theorem vectorL1_list_sum_le
    (m : ℕ) (vs : List (ℕ → ℂ)) :
    vectorL1 m (fun h => (vs.map fun v => v h).sum) ≤
      (vs.map fun v => vectorL1 m v).sum := by
  induction vs with
  | nil => simp [vectorL1]
  | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (vectorL1_add_le m v _).trans (add_le_add le_rfl ih)

theorem canonicalDyadicPartition_cutoff_decomposition
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) (α : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    cutoffFourierSum μ c Q0 m N h α =
      ((canonicalDyadicPartition N).map fun B =>
        dyadicBlockIncrement μ c Q0 m B h α).sum := by
  have ht := canonicalDyadicPartition_endpoint_telescope
    (fun K => cutoffFourierSum μ c Q0 m K h α) hN
  have hzero : cutoffFourierSum μ c Q0 m 1 h α = 0 := by
    unfold cutoffFourierSum
    rw [sparseFrequencyCutoff_one_eq_empty μ c Q0 m hm]
    simp
  simpa only [dyadicBlockIncrement, hzero, sub_zero] using ht.symm

theorem canonicalDyadicPartition_cutoff_L1_le
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    vectorL1 m (fun h => cutoffFourierSum μ c Q0 m N (h : ℤ) α) ≤
      ((canonicalDyadicPartition N).map fun B =>
        dyadicBlockL1 μ c Q0 m B α).sum := by
  let vs : List (ℕ → ℂ) := (canonicalDyadicPartition N).map fun B =>
    fun h : ℕ => dyadicBlockIncrement μ c Q0 m B (h : ℤ) α
  have hpoint : (fun h : ℕ => cutoffFourierSum μ c Q0 m N (h : ℤ) α) =
      fun h => (vs.map fun v => v h).sum := by
    funext h
    simpa [vs] using canonicalDyadicPartition_cutoff_decomposition
      μ c Q0 m N (h : ℤ) α hm hN
  rw [hpoint]
  simpa [vs, dyadicBlockL1] using vectorL1_list_sum_le m vs

theorem list_sum_map_le_sum_map
    {α : Type*} (xs : List α) (f g : α → ℝ)
    (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hfg x (by simp))
        (ih (fun y hy => hfg y (by simp [hy])))

theorem sum_map_blockBudget
    (ρ : ℝ) (blocks : List DyadicBlock) :
    (blocks.map fun B => B.budget ρ).sum =
      (((blocks.map fun B => B.blockLength).sum : ℕ) : ℝ) +
        (blocks.map fun B =>
          (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2).sum * ρ := by
  induction blocks with
  | nil => simp
  | cons B blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp only [DyadicBlock.budget, Nat.cast_add]
      ring

theorem canonicalDyadicPartition_budget_sum
    (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ((canonicalDyadicPartition N).map fun B => B.budget ρ).sum =
      ((N : ℝ) - 1) + ((N : ℝ) ^ 2 - 1) * ρ := by
  rw [sum_map_blockBudget, canonicalDyadicPartition_sum_length]
  have hsquare := canonicalDyadicPartition_endpoint_telescope
    (fun K : ℕ => (K : ℝ) ^ 2) hN
  norm_num at hsquare
  rw [hsquare, Nat.cast_sub hN]
  norm_num

theorem canonicalDyadicPartition_budget_le_target
    {ρ : ℝ} (hρ : 0 ≤ ρ) {N : ℕ} (hN : 1 ≤ N) :
    ((canonicalDyadicPartition N).map fun B => B.budget ρ).sum ≤
      (N : ℝ) + (N : ℝ) ^ 2 * ρ := by
  rw [canonicalDyadicPartition_budget_sum ρ hN]
  nlinarith

/-- Exact local hypothesis at fixed `s,B`, with one constant independent of
`m,a,j` and alignment `2^j | a-1` exposed. -/
def LocalizedDyadicBlockBudgetAt
    (μ c : ℝ) (Q0 : ℕ) (α s B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ m a j : ℕ, 1 ≤ m → 1 ≤ a → 2 ^ j ∣ a - 1 →
    dyadicBlockL1 μ c Q0 m ⟨a, j⟩ α ≤
      B * (decimalFrequency m : ℝ) *
        ((2 ^ j : ℕ) +
          (((a + 2 ^ j : ℕ) : ℝ) ^ 2 - (a : ℝ) ^ 2) *
            (10 : ℝ) ^ (-s * (m : ℝ)))

/-- Uniform localized budget predicate. This definition is not inhabited here
at `alpha = pi`. -/
def LocalizedDyadicBlockBudget
    (μ c : ℝ) (Q0 : ℕ) (α : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ B : ℝ, LocalizedDyadicBlockBudgetAt μ c Q0 α s B

/-- Full audit of the local premise: exact endpoints `a,a+2^j`, alignment,
inclusive frequencies, complex norm, constant, and quantifier order. -/
theorem localizedDyadicBlockBudgetAt_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) (α s B : ℝ) :
    LocalizedDyadicBlockBudgetAt μ c Q0 α s B ↔
      0 ≤ B ∧ ∀ m a j : ℕ, 1 ≤ m → 1 ≤ a → 2 ^ j ∣ a - 1 →
        (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖cutoffFourierSum μ c Q0 m (a + 2 ^ j) (h : ℤ) α -
            cutoffFourierSum μ c Q0 m a (h : ℤ) α‖) ≤
          B * (decimalFrequency m : ℝ) *
            ((2 ^ j : ℕ) +
              (((a + 2 ^ j : ℕ) : ℝ) ^ 2 - (a : ℝ) ^ 2) *
                (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

theorem localizedDyadicBlockBudgetAt_implies_cutoff_with_multiplier_one
    (μ c : ℝ) (Q0 : ℕ) (α s B : ℝ)
    (hlocal : LocalizedDyadicBlockBudgetAt μ c Q0 α s B) :
    ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
      (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ≤
        B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  intro m N hm hN
  let ρ : ℝ := (10 : ℝ) ^ (-s * (m : ℝ))
  have htriangle := canonicalDyadicPartition_cutoff_L1_le
    μ c Q0 m N α hm hN
  have hblocks :
      ((canonicalDyadicPartition N).map fun block =>
        dyadicBlockL1 μ c Q0 m block α).sum ≤
      ((canonicalDyadicPartition N).map fun block =>
        B * (decimalFrequency m : ℝ) * block.budget ρ).sum := by
    apply list_sum_map_le_sum_map
    intro block hblock
    have hstart := canonicalDyadicPartition_start_pos hblock
    have halign := canonicalDyadicPartition_aligned hblock
    simpa only [DyadicBlock.budget, DyadicBlock.blockLength,
      DyadicBlock.finish, ρ] using hlocal.2 m block.start block.level
        hm hstart halign
  have hfactor :
      ((canonicalDyadicPartition N).map fun block =>
        B * (decimalFrequency m : ℝ) * block.budget ρ).sum =
      B * (decimalFrequency m : ℝ) *
        ((canonicalDyadicPartition N).map fun block => block.budget ρ).sum := by
    induction canonicalDyadicPartition N with
    | nil => simp
    | cons block blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  have hbudget := canonicalDyadicPartition_budget_le_target
    (show 0 ≤ ρ by positivity) hN
  have hnonneg : 0 ≤ B * (decimalFrequency m : ℝ) := by
    exact mul_nonneg hlocal.1 (Nat.cast_nonneg _)
  unfold vectorL1 at htriangle
  calc
    (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
        ‖cutoffFourierSum μ c Q0 m N (h : ℤ) α‖) ≤
        ((canonicalDyadicPartition N).map fun block =>
          dyadicBlockL1 μ c Q0 m block α).sum := htriangle
    _ ≤ ((canonicalDyadicPartition N).map fun block =>
          B * (decimalFrequency m : ℝ) * block.budget ρ).sum := hblocks
    _ = B * (decimalFrequency m : ℝ) *
          ((canonicalDyadicPartition N).map fun block => block.budget ρ).sum := hfactor
    _ ≤ B * (decimalFrequency m : ℝ) *
          ((N : ℝ) + (N : ℝ) ^ 2 * ρ) :=
      mul_le_mul_of_nonneg_left hbudget hnonneg
    _ = B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
      rfl

/-- Conditional specialization to `alpha = pi`; it asserts no localized
estimate, but converts one into T22's exact cutoff predicate. -/
theorem localizedDyadicBlockBudget_pi_implies_T22
    (μ c : ℝ) (Q0 : ℕ)
    (hlocal : LocalizedDyadicBlockBudget μ c Q0 Real.pi) :
    CutoffScaleMatchedL1Bound μ c Q0 := by
  intro s hs0 hs1
  obtain ⟨B, hB⟩ := hlocal s hs0 hs1
  exact ⟨B, hB.1,
    localizedDyadicBlockBudgetAt_implies_cutoff_with_multiplier_one
      μ c Q0 Real.pi s B hB⟩

/-- Final conditional reduction to the existing T12 predicate. The premise is
not established for `pi`, and no C1 conclusion is made. -/
theorem localizedDyadicBlockBudget_pi_implies_T12
    (μ c : ℝ) (Q0 : ℕ)
    (hlocal : LocalizedDyadicBlockBudget μ c Q0 Real.pi) :
    ScaleMatchedL1Bound μ c Q0 :=
  (cutoffScaleMatchedL1Bound_iff_T12 μ c Q0).mp
    (localizedDyadicBlockBudget_pi_implies_T22 μ c Q0 hlocal)

end Theory.PiDigits.LongLagBlockCollisionDecay.T24

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.canonicalDyadicPartition_aligned
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.dyadicBlockIncrement_eq_sum_endpointIncrement
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.canonicalDyadicPartition_endpoint_telescope
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.canonicalDyadicPartition_budget_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.localizedDyadicBlockBudgetAt_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.localizedDyadicBlockBudgetAt_implies_cutoff_with_multiplier_one
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.localizedDyadicBlockBudget_pi_implies_T22
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T24.localizedDyadicBlockBudget_pi_implies_T12
