import TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit

/-!
# T69: endpoint-safe five-case charging on the exact sparse short-lag domain

Canonical source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file proves a finite, arbitrary-sequence charging theorem.  Its final pi
specialization retains the three-layer equality-load estimate as an explicit
hypothesis.  It makes no assertion about the long sector, C7, C2, C1, or the
canonical entropy question.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.T69FiveCaseCharging

open DecimalFactorComplexity
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.T56LagSectorAudit
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The five endpoint-safe alternatives, with the two wrap cases retained. -/
inductive EndpointCase
  | equal
  | predecessor
  | successor
  | wrapPredecessor
  | wrapSuccessor
  deriving DecidableEq, Repr

/-- The literal arithmetic meaning of each endpoint case. -/
def EndpointCase.Holds (c : EndpointCase) (q a b : ℕ) : Prop :=
  match c with
  | .equal => b = a
  | .predecessor => b + 1 = a
  | .successor => a + 1 = b
  | .wrapPredecessor => a = 0 ∧ b + 1 = q
  | .wrapSuccessor => b = 0 ∧ a + 1 = q

/-- Deterministic tie-breaking: equality, predecessor, successor,
wrap-predecessor, then wrap-successor.  The final branch is certified by
`classifyFive_holds` whenever the input is cyclically adjacent. -/
def classifyFive (q a b : ℕ) : EndpointCase :=
  if b = a then .equal
  else if b + 1 = a then .predecessor
  else if a + 1 = b then .successor
  else if a = 0 ∧ b + 1 = q then .wrapPredecessor
  else .wrapSuccessor

/-- The classifier is exhaustive on the exact five-way relation exported by
T2. -/
theorem classifyFive_holds {q a b : ℕ}
    (h : CyclicAdjacent q a b) :
    (classifyFive q a b).Holds q a b := by
  unfold classifyFive
  split_ifs <;> simp_all [EndpointCase.Holds, CyclicAdjacent]

/-- All priority guards are exposed, so the classifier has inspectable and
unambiguous tie-breaking even at degenerate moduli. -/
theorem classifyFive_tie_breaking (q a b : ℕ) :
    (classifyFive q a b = .equal ↔ b = a) ∧
    (classifyFive q a b = .predecessor ↔ b ≠ a ∧ b + 1 = a) ∧
    (classifyFive q a b = .successor ↔
      b ≠ a ∧ b + 1 ≠ a ∧ a + 1 = b) ∧
    (classifyFive q a b = .wrapPredecessor ↔
      b ≠ a ∧ b + 1 ≠ a ∧ a + 1 ≠ b ∧ a = 0 ∧ b + 1 = q) ∧
    (classifyFive q a b = .wrapSuccessor ↔
      b ≠ a ∧ b + 1 ≠ a ∧ a + 1 ≠ b ∧ ¬(a = 0 ∧ b + 1 = q)) := by
  simp only [classifyFive]
  split_ifs <;> simp_all

/-- The three cyclic relations obtained after identifying endpoint wraps. -/
inductive ThreeRelation
  | equal
  | successor
  | predecessor
  deriving DecidableEq, Repr

/-- Collapse the five endpoint alternatives to equality and the two cyclic
directions. -/
def EndpointCase.collapse : EndpointCase → ThreeRelation
  | .equal => .equal
  | .predecessor => .predecessor
  | .successor => .successor
  | .wrapPredecessor => .predecessor
  | .wrapSuccessor => .successor

/-- Arithmetic form of equality, cyclic successor, and cyclic predecessor. -/
def ThreeRelation.Holds (c : ThreeRelation) (q a b : ℕ) : Prop :=
  match c with
  | .equal => b = a
  | .successor => a + 1 = b ∨ (b = 0 ∧ a + 1 = q)
  | .predecessor => b + 1 = a ∨ (a = 0 ∧ b + 1 = q)

/-- The deterministic five-case output collapses to one of the three cyclic
relations without dropping either endpoint case. -/
theorem collapse_classifyFive_holds {q a b : ℕ}
    (h : CyclicAdjacent q a b) :
    ThreeRelation.Holds (classifyFive q a b).collapse q a b := by
  have hc := classifyFive_holds h
  generalize heq : classifyFive q a b = c at hc ⊢
  cases c with
  | equal => simpa [EndpointCase.Holds, EndpointCase.collapse,
      ThreeRelation.Holds] using hc
  | predecessor =>
      exact Or.inl (by simpa [EndpointCase.Holds] using hc)
  | successor =>
      exact Or.inl (by simpa [EndpointCase.Holds] using hc)
  | wrapPredecessor =>
      exact Or.inr (by simpa [EndpointCase.Holds] using hc)
  | wrapSuccessor =>
      exact Or.inr (by simpa [EndpointCase.Holds] using hc)

/-- Upper-triangular position pairs on T56's sparse short-lag domain. -/
def shortLagPairs (n : ℕ) : Finset
    (Fin (t56SampleLength n) × Fin (t56SampleLength n)) :=
  Finset.univ.filter fun ik =>
    ik.1.val < ik.2.val ∧ ik.2.val - ik.1.val < n

/-- Exact endpoint audit: writing `j=i` and `r=k-i`, these are precisely
`0<r`, `r<n`, `r<L_n`, and `j<L_n-r`. -/
theorem mem_shortLagPairs_iff {n : ℕ}
    {ik : Fin (t56SampleLength n) × Fin (t56SampleLength n)} :
    ik ∈ shortLagPairs n ↔
      0 < ik.2.val - ik.1.val ∧
      ik.2.val - ik.1.val < n ∧
      ik.2.val - ik.1.val < t56SampleLength n ∧
      ik.1.val < t56SampleLength n - (ik.2.val - ik.1.val) := by
  simp only [shortLagPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- Starts carrying a fixed label. -/
def labelFiber {L q : ℕ} (x : Fin L → Fin q) (a : Fin q) : Finset (Fin L) :=
  Finset.univ.filter fun i => x i = a

/-- Equality-component load: the sum of squared component sizes of the label
partition. -/
def equalityComponentLoad {L q : ℕ} (x : Fin L → Fin q) : ℕ :=
  ∑ a : Fin q, (labelFiber x a).card ^ 2

/-- The graph of a permutation of finite labels. -/
def finiteCodeGraph {L q : ℕ} (x : Fin L → Fin q) (e : Equiv.Perm (Fin q)) :
    Finset (Fin L × Fin L) :=
  Finset.univ.filter fun ik => x ik.2 = e (x ik.1)

/-- A code graph is the cross-sum of its source and target fibers. -/
theorem finiteCodeGraph_card_eq_crossSum {L q : ℕ}
    (x : Fin L → Fin q) (e : Equiv.Perm (Fin q)) :
    (finiteCodeGraph x e).card =
      ∑ a : Fin q, (labelFiber x a).card * (labelFiber x (e a)).card := by
  classical
  let S := finiteCodeGraph x e
  have hpartition :
      S.card = ∑ a : Fin q, (S.filter fun ik => x ik.1 = a).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin q)))
      (f := fun ik => x ik.1) (by simp)
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.card_product]
  apply congrArg Finset.card
  ext ik
  simp only [S, finiteCodeGraph, labelFiber, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨hgraph, hi⟩
    exact ⟨hi, by simpa [hi] using hgraph⟩
  · rintro ⟨hi, hk⟩
    exact ⟨by simpa [hi] using hk, hi⟩

/-- Finite Cauchy-Schwarz charges every permutation graph to one equality
component load. -/
theorem finiteCodeGraph_card_le_equalityComponentLoad {L q : ℕ}
    (x : Fin L → Fin q) (e : Equiv.Perm (Fin q)) :
    (finiteCodeGraph x e).card ≤ equalityComponentLoad x := by
  rw [finiteCodeGraph_card_eq_crossSum, equalityComponentLoad]
  let m : Fin q → ℝ := fun a => (labelFiber x a).card
  have hperm : (∑ a : Fin q, m (e a) ^ 2) = ∑ a : Fin q, m a ^ 2 := by
    exact Equiv.sum_comp e (fun a => m a ^ 2)
  have hnonneg : 0 ≤ ∑ a : Fin q, m a ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin q)) m (fun a => m (e a))
  rw [hperm] at hcs
  change (∑ a : Fin q, m a * m (e a)) ≤
    √(∑ a : Fin q, m a ^ 2) * √(∑ a : Fin q, m a ^ 2) at hcs
  rw [Real.mul_self_sqrt hnonneg] at hcs
  dsimp [m] at hcs
  exact_mod_cast hcs

/-- Three same-label component layers corresponding to identity, cyclic
successor, and cyclic predecessor codes.  Relabeling by a permutation does not
change a component load, so this is exactly three copies of the base load. -/
def E3 (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) : ℕ :=
  equalityComponentLoad x +
    equalityComponentLoad (fun i => finRotate (10 ^ n) (x i)) +
      equalityComponentLoad (fun i => (finRotate (10 ^ n)).symm (x i))

/-- Totalize a finite label sequence for definitions whose actual sampled
indices are subsequently restricted to the sequence length. -/
def finiteLabelAt {L q : ℕ} (hL : 0 < L) (x : Fin L → Fin q) (j : ℕ) : Fin q :=
  x ⟨j % L, Nat.mod_lt j hL⟩

/-- Adjacent-label starts at one lag.  Only `j<L-r` is read, so the modular
totalization in `finiteLabelAt` never changes a sampled index. -/
def adjacentStarts (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t56SampleLength n - r)).filter fun j =>
    CyclicAdjacent (10 ^ n)
      (finiteLabelAt (by positivity) x j).val
      (finiteLabelAt (by positivity) x (j + r)).val

/-- W5 uses literally T56's endpoint-safe short-lag set. -/
theorem mem_W5_lags_iff {n r : ℕ} :
    r ∈ shortResidualLags n (t56SampleLength n) ↔
      0 < r ∧ r < n ∧ r < t56SampleLength n := by
  exact mem_sparse_short_sector_iff

/-- The unsigned five-case short-sector weight.  The factor two restores the
reverse orientation exactly as in T56. -/
def W5 (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) : ℕ :=
  2 * ∑ r ∈ shortResidualLags n (t56SampleLength n),
    (adjacentStarts n x r).card

/-- Equality-component load is invariant under a permutation of labels. -/
theorem equalityComponentLoad_comp_perm {L q : ℕ}
    (x : Fin L → Fin q) (e : Equiv.Perm (Fin q)) :
    equalityComponentLoad (fun i => e (x i)) = equalityComponentLoad x := by
  unfold equalityComponentLoad
  calc
    (∑ a : Fin q, (labelFiber (fun i => e (x i)) a).card ^ 2) =
        ∑ a : Fin q, (labelFiber x (e.symm a)).card ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _ha
      congr 2
      ext i
      simp only [labelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact e.eq_symm_apply.symm
    _ = ∑ a : Fin q, (labelFiber x a).card ^ 2 := by
      exact Equiv.sum_comp e.symm
        (fun a => (labelFiber x a).card ^ 2)

/-- The three-layer statistic is exactly three base equality loads. -/
theorem E3_eq_three_mul (n : ℕ)
    (x : Fin (t56SampleLength n) → Fin (10 ^ n)) :
    E3 n x = 3 * equalityComponentLoad x := by
  rw [E3, equalityComponentLoad_comp_perm x (finRotate (10 ^ n)),
    equalityComponentLoad_comp_perm x (finRotate (10 ^ n)).symm]
  omega

/-- The requested single uniform statement, with natural counting constants. -/
def UniformCharging : Prop :=
  ∃ C N : ℕ, 0 < C ∧ 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      ∀ x : Fin (t56SampleLength n) → Fin (10 ^ n),
        W5 n x ≤ C * (t56SampleLength n + E3 n x)

/-- The uniform charging statement holds with `C=1` and `N=1`. -/
theorem uniformCharging : UniformCharging := by
  classical
  refine ⟨1, 1, by simp, by simp, ?_⟩
  intro n _hn x
  let P : ℕ → ℕ → Prop := fun i k =>
    CyclicAdjacent (10 ^ n)
      (finiteLabelAt (by positivity) x i).val
      (finiteLabelAt (by positivity) x k).val
  let A := (Finset.univ : Finset
    (Fin (t56SampleLength n) × Fin (t56SampleLength n))).filter fun ik =>
      P ik.1.val ik.2.val
  let G0 := finiteCodeGraph x (Equiv.refl (Fin (10 ^ n)))
  let Gp := finiteCodeGraph x (finRotate (10 ^ n))
  let Gm := finiteCodeGraph x (finRotate (10 ^ n)).symm
  have hPsymm : ∀ i k, P i k ↔ P k i := by
    intro i k
    simp only [P]
    unfold CyclicAdjacent
    omega
  have hPdiag : ∀ i, P i i := by
    intro i
    simp [P, CyclicAdjacent]
  have hdecomp := symmetric_orderedPair_card_eq_lag_sum P hPsymm hPdiag
    (t56SampleLength n)
  have hshort : W5 n x ≤ A.card := by
    have hsub : shortResidualLags n (t56SampleLength n) ⊆
        Finset.Icc 1 (t56SampleLength n - 1) := by
      exact Finset.filter_subset _ _
    have hsum :
        (∑ r ∈ shortResidualLags n (t56SampleLength n),
            (adjacentStarts n x r).card) ≤
          ∑ r ∈ Finset.Icc 1 (t56SampleLength n - 1),
            ((Finset.range (t56SampleLength n - r)).filter fun j =>
              P j (j + r)).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro r _hr _hnot
      positivity
    have hA : A.card = t56SampleLength n +
        2 * ∑ r ∈ Finset.Icc 1 (t56SampleLength n - 1),
          ((Finset.range (t56SampleLength n - r)).filter fun j =>
            P j (j + r)).card := by
      simpa [A] using hdecomp
    rw [hA]
    unfold W5 adjacentStarts
    simpa [P] using Nat.mul_le_mul_left 2 hsum |>.trans
      (Nat.le_add_left _ _)
  have hsubset : A ⊆ G0 ∪ (Gp ∪ Gm) := by
    intro ik hik
    have hadj : CyclicAdjacent (10 ^ n) (x ik.1).val (x ik.2).val := by
      have hP := (Finset.mem_filter.mp hik).2
      simpa [A, P, finiteLabelAt, Nat.mod_eq_of_lt ik.1.isLt,
        Nat.mod_eq_of_lt ik.2.isLt] using hP
    have hthree := cyclicAdjacent_three_cases (by positivity)
      (x ik.1) (x ik.2) hadj
    rcases hthree with hsame | hsucc | hpred
    · simp [G0, finiteCodeGraph, hsame]
    · simp [Gp, finiteCodeGraph, hsucc]
    · simp [Gm, finiteCodeGraph, hpred]
  have hA : A.card ≤ G0.card + (Gp.card + Gm.card) := by
    calc
      A.card ≤ (G0 ∪ (Gp ∪ Gm)).card := Finset.card_le_card hsubset
      _ ≤ G0.card + (Gp ∪ Gm).card := Finset.card_union_le _ _
      _ ≤ G0.card + (Gp.card + Gm.card) := by
        gcongr
        exact Finset.card_union_le _ _
  have hG0 : G0.card ≤ equalityComponentLoad x := by
    exact finiteCodeGraph_card_le_equalityComponentLoad x (Equiv.refl _)
  have hGp : Gp.card ≤ equalityComponentLoad x := by
    exact finiteCodeGraph_card_le_equalityComponentLoad x (finRotate (10 ^ n))
  have hGm : Gm.card ≤ equalityComponentLoad x := by
    exact finiteCodeGraph_card_le_equalityComponentLoad x
      (finRotate (10 ^ n)).symm
  rw [E3_eq_three_mul]
  simp only [one_mul]
  change W5 n x ≤ t56SampleLength n + 3 * equalityComponentLoad x
  omega

/-! ## Conditional pi specialization -/

/-- The first `L_n` canonical length-`n` pi labels. -/
def piLabelSequence (n : ℕ) :
    Fin (t56SampleLength n) → Fin (10 ^ n) := fun i =>
  piCylinderCode n i

/-- Every T56 residual short incidence is included in the unsigned five-case
weight.  The arithmetic residual mask can only remove starts. -/
theorem shortResidualPairCount_le_W5
    (μ c : ℝ) (Q0 n : ℕ) :
    shortResidualPairCount μ c Q0 n (t56SampleLength n) ≤
      W5 n (piLabelSequence n) := by
  classical
  unfold shortResidualPairCount W5
  apply Nat.mul_le_mul_left 2
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.card_le_card
  intro j hj
  have hjNear : j ∈ nearReturnStarts n (t56SampleLength n) r :=
    (Finset.mem_filter.mp hj).1
  have hjData : j < t56SampleLength n - r ∧
      circleDistance
          ((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi) <
        ((10 : ℝ) ^ n)⁻¹ := by
    simpa [nearReturnStarts] using hjNear
  have hrData := mem_shortResidualLags_iff.mp hr
  have hjL : j < t56SampleLength n := by omega
  have hjrL : j + r < t56SampleLength n := by omega
  have hnearTail :
      circleDistance
          (tailOrbit piDecimalStream (j + r) - tailOrbit piDecimalStream j) <
        ((10 : ℝ) ^ n)⁻¹ := by
    rw [tailOrbit_decimalDigit_eq_baseTenOrbit Real.pi Real.pi_pos.le,
      tailOrbit_decimalDigit_eq_baseTenOrbit Real.pi Real.pi_pos.le,
      circleDistance_piShift_sub_eq_powerDifference,
      pow_lag_factorization]
    exact hjData.2
  have hadj := nearReturn_implies_prefixLabels_adjacent piDecimalStream n hnearTail
  simp only [adjacentStarts, Finset.mem_filter, Finset.mem_range]
  refine ⟨hjData.1, ?_⟩
  simpa [piLabelSequence, finiteLabelAt, piCylinderCode,
    Nat.mod_eq_of_lt hjL, Nat.mod_eq_of_lt hjrL] using hadj

/-- The unproved fixed-pi equality-load estimate required by the corollary.
Its constant and onset precede every later scale. -/
def PiE3LinearBound : Prop :=
  ∃ K N : ℕ, 0 < K ∧ 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      E3 n (piLabelSequence n) ≤ K * t56SampleLength n

/-- Only the explicit equality-load hypothesis is converted to T56's sparse
short-sector predicate.  No long-sector or downstream conclusion is made. -/
theorem piE3LinearBound_implies_sparseShortRepunitIncidenceBound
    (μ c : ℝ) (Q0 : ℕ) (hE3 : PiE3LinearBound) :
    SparseShortRepunitIncidenceBound μ c Q0 := by
  obtain ⟨K, NE, hK, hNE, hE⟩ := hE3
  obtain ⟨C, NC, hC, hNC, hcharge⟩ := uniformCharging
  refine ⟨(C * (1 + K) : ℕ), by exact_mod_cast Nat.mul_pos hC (by omega),
    max NC NE, hNC.trans (Nat.le_max_left _ _), ?_⟩
  intro n hn
  have hnC : NC ≤ n := (Nat.le_max_left NC NE).trans hn
  have hnE : NE ≤ n := (Nat.le_max_right NC NE).trans hn
  have hNat :
      shortResidualPairCount μ c Q0 n (t56SampleLength n) ≤
        (C * (1 + K)) * t56SampleLength n := by
    calc
      shortResidualPairCount μ c Q0 n (t56SampleLength n) ≤
          W5 n (piLabelSequence n) := shortResidualPairCount_le_W5 μ c Q0 n
      _ ≤ C * (t56SampleLength n + E3 n (piLabelSequence n)) :=
        hcharge n hnC (piLabelSequence n)
      _ ≤ C * (t56SampleLength n + K * t56SampleLength n) := by
        gcongr
        exact hE n hnE
      _ = (C * (1 + K)) * t56SampleLength n := by ring
  exact_mod_cast hNat

end DecimalFactorComplexity.T69FiveCaseCharging

#print axioms DecimalFactorComplexity.T69FiveCaseCharging.classifyFive_holds
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.classifyFive_tie_breaking
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.collapse_classifyFive_holds
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.mem_W5_lags_iff
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.finiteCodeGraph_card_le_equalityComponentLoad
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.E3_eq_three_mul
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.uniformCharging
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.shortResidualPairCount_le_W5
#print axioms DecimalFactorComplexity.T69FiveCaseCharging.piE3LinearBound_implies_sparseShortRepunitIncidenceBound
