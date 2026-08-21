import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting
import Mathlib.Order.KonigLemma

/-!
# Finite decimal count-tree leakage and bounded-start compactness

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This is an abstract finite-tree (A14 sibling) interface.  The final section
imports the accepted T14 theorem but does not assert C2, canonical A1, or any
unconditional property of `Real.pi`.
-/

noncomputable section

open Finset Filter MeasureTheory

namespace DecimalFactorComplexity.FiniteCountTreeLeakage

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.CoherentSuccessorSplitting

/-- Appending one base-10 digit, with value `10 * a + d`. -/
def decimalAppendEquiv (n : ℕ) :
    Fin (10 ^ n) × Fin 10 ≃ Fin (10 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ]))

/-- The child of `a` selected by digit `d`. -/
def decimalChild (n : ℕ) (a : Fin (10 ^ n)) (d : Fin 10) :
    Fin (10 ^ (n + 1)) :=
  decimalAppendEquiv n (a, d)

@[simp] theorem decimalChild_val (n : ℕ) (a : Fin (10 ^ n)) (d : Fin 10) :
    (decimalChild n a d).val = d.val + 10 * a.val := by
  rfl

theorem decimalChild_pair_injective (n : ℕ) :
    Function.Injective (fun ad : Fin (10 ^ n) × Fin 10 =>
      decimalChild n ad.1 ad.2) :=
  (decimalAppendEquiv n).injective

theorem decimalChild_parent_injective (n : ℕ) (choose : Fin (10 ^ n) → Fin 10) :
    Function.Injective (fun a => decimalChild n a (choose a)) := by
  intro a b hab
  have hp : (a, choose a) = (b, choose b) :=
    decimalChild_pair_injective n hab
  exact congrArg Prod.fst hp

/-- Counts on every decimal level.  A finite tree of depth `s` is specified
below by restricting conservation and nonnegativity to levels `n ≤ s`. -/
abbrev DecimalCounts := (n : ℕ) → Fin (10 ^ n) → ℝ

/-- Literal nonnegative-integer counts from T27. -/
abbrev NaturalDecimalCounts := (n : ℕ) → Fin (10 ^ n) → ℕ

/-- Regard integer counts as real masses for collision-energy inequalities. -/
def NaturalDecimalCounts.toReal (c : NaturalDecimalCounts) : DecimalCounts :=
  fun n a => (c n a : ℝ)

/-- A finite base-10 integer count tree through level `s`; conservation is
required exactly for `n < s`. -/
def IsFiniteBase10CountTree (c : NaturalDecimalCounts) (s : ℕ) : Prop :=
  ∀ n, n < s → ∀ a,
    c n a = ∑ d : Fin 10, c (n + 1) (decimalChild n a d)

/-- Explicit finite-tree conditions through level `s`.  Conservation is
required exactly at the refinement levels `n < s`. -/
def IsFiniteDecimalCountTree (c : DecimalCounts) (s : ℕ) : Prop :=
  (∀ n, n ≤ s → ∀ a, 0 ≤ c n a) ∧
  (∀ n, n < s → ∀ a,
    c n a = ∑ d : Fin 10, c (n + 1) (decimalChild n a d))

theorem naturalCountTree_toReal (c : NaturalDecimalCounts) (s : ℕ)
    (htree : IsFiniteBase10CountTree c s) :
    IsFiniteDecimalCountTree c.toReal s := by
  constructor
  · intro n _ a
    exact Nat.cast_nonneg _
  · intro n hn a
    simp only [NaturalDecimalCounts.toReal]
    exact_mod_cast htree n hn a

/-- Total count mass at one level. -/
def totalMass (c : DecimalCounts) (n : ℕ) : ℝ :=
  ∑ a : Fin (10 ^ n), c n a

/-- Integer total mass at one level. -/
def naturalTotalMass (c : NaturalDecimalCounts) (n : ℕ) : ℕ :=
  ∑ a : Fin (10 ^ n), c n a

/-- Ordered, diagonal-inclusive collision energy at one level. -/
def collisionEnergy (c : DecimalCounts) (n : ℕ) : ℝ :=
  ∑ a : Fin (10 ^ n), (c n a) ^ 2

/-- Conservation preserves total mass across one refinement. -/
theorem totalMass_succ_eq (c : DecimalCounts) (n : ℕ)
    (hconserve : ∀ a,
      c n a = ∑ d : Fin 10, c (n + 1) (decimalChild n a d)) :
    totalMass c (n + 1) = totalMass c n := by
  unfold totalMass
  calc
    (∑ b : Fin (10 ^ (n + 1)), c (n + 1) b) =
        ∑ ad : Fin (10 ^ n) × Fin 10,
          c (n + 1) (decimalChild n ad.1 ad.2) := by
      exact (Fintype.sum_equiv (decimalAppendEquiv n)
        (fun ad => c (n + 1) (decimalChild n ad.1 ad.2))
        (fun b => c (n + 1) b) (fun _ => rfl)).symm
    _ = ∑ a : Fin (10 ^ n), ∑ d : Fin 10,
          c (n + 1) (decimalChild n a d) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : Fin (10 ^ n), c n a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (hconserve a).symm

/-- Exact conservation for the integer count tree. -/
theorem finite_base10_countTree_mass_conservation
    (c : NaturalDecimalCounts) (n : ℕ)
    (hconserve : ∀ a,
      c n a = ∑ d : Fin 10, c (n + 1) (decimalChild n a d)) :
    naturalTotalMass c (n + 1) = naturalTotalMass c n := by
  unfold naturalTotalMass
  calc
    (∑ b : Fin (10 ^ (n + 1)), c (n + 1) b) =
        ∑ ad : Fin (10 ^ n) × Fin 10,
          c (n + 1) (decimalChild n ad.1 ad.2) := by
      exact (Fintype.sum_equiv (decimalAppendEquiv n)
        (fun ad => c (n + 1) (decimalChild n ad.1 ad.2))
        (fun b => c (n + 1) b) (fun _ => rfl)).symm
    _ = ∑ a : Fin (10 ^ n), ∑ d : Fin 10,
          c (n + 1) (decimalChild n a d) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : Fin (10 ^ n), c n a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (hconserve a).symm

/-- A child count is at most its parent count. -/
theorem child_le_parent (c : DecimalCounts) (n : ℕ)
    {a : Fin (10 ^ n)}
    (hnonneg : ∀ d : Fin 10, 0 ≤ c (n + 1) (decimalChild n a d))
    (hconserve : c n a =
      ∑ d : Fin 10, c (n + 1) (decimalChild n a d))
    (d : Fin 10) :
    c (n + 1) (decimalChild n a d) ≤ c n a := by
  rw [hconserve]
  exact Finset.single_le_sum (fun z _ => hnonneg z) (Finset.mem_univ d)

/-- Collision energy cannot increase under a nonnegative conservative
decimal refinement. -/
theorem collisionEnergy_succ_le (c : DecimalCounts) (n : ℕ)
    (hnonneg : ∀ a d, 0 ≤ c (n + 1) (decimalChild n a d))
    (hconserve : ∀ a,
      c n a = ∑ d : Fin 10, c (n + 1) (decimalChild n a d)) :
    collisionEnergy c (n + 1) ≤ collisionEnergy c n := by
  unfold collisionEnergy
  calc
    (∑ b : Fin (10 ^ (n + 1)), (c (n + 1) b) ^ 2) =
        ∑ ad : Fin (10 ^ n) × Fin 10,
          (c (n + 1) (decimalChild n ad.1 ad.2)) ^ 2 := by
      exact (Fintype.sum_equiv (decimalAppendEquiv n)
        (fun ad => (c (n + 1) (decimalChild n ad.1 ad.2)) ^ 2)
        (fun b => (c (n + 1) b) ^ 2) (fun _ => rfl)).symm
    _ = ∑ a : Fin (10 ^ n), ∑ d : Fin 10,
          (c (n + 1) (decimalChild n a d)) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ a : Fin (10 ^ n), (c n a) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      exact (sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin 10)))
        (f := fun d => c (n + 1) (decimalChild n a d))
        (fun d _ => hnonneg a d)).trans_eq (by rw [← hconserve a])

/-- Collision energy on parents declared dominant at level `n`. -/
def dominantParentEnergy (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop) (n : ℕ) : ℝ := by
  classical
  exact ∑ a : Fin (10 ^ n), if dominant n a then (c n a) ^ 2 else 0

/-- Energy retained by one explicitly selected child of each dominant parent. -/
def retainedEdgeEnergy (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10) (n : ℕ) : ℝ := by
  classical
  exact ∑ a : Fin (10 ^ n), if dominant n a then
    (c (n + 1) (decimalChild n a (choose n a))) ^ 2 else 0

/-- Full selected-edge leakage: all energy outside the chosen dominant edges. -/
def leakage (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10) (n : ℕ) : ℝ :=
  collisionEnergy c n - retainedEdgeEnergy c dominant choose n

/-- A chosen child carrying an `alpha` fraction retains its squared fraction
of dominant-parent collision energy. -/
theorem dominant_edge_retention (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (alpha : ℝ) (n : ℕ) (halpha : 0 ≤ alpha)
    (hcount : ∀ a, 0 ≤ c n a)
    (hretain : ∀ a, dominant n a →
      alpha * c n a ≤ c (n + 1) (decimalChild n a (choose n a))) :
    alpha ^ 2 * dominantParentEnergy c dominant n ≤
      retainedEdgeEnergy c dominant choose n := by
  classical
  simp only [dominantParentEnergy, retainedEdgeEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : dominant n a
  · simp only [ha, if_true]
    have hleft : 0 ≤ alpha * c n a := mul_nonneg halpha (hcount a)
    have hright := hretain a ha
    nlinarith
  · simp only [ha, if_false, mul_zero, le_refl]

/-- Explicit local leakage constant from dominant-parent mass and selected
edge retention. -/
theorem leakage_le_explicit (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (alpha mu : ℝ) (n : ℕ) (halpha : 0 ≤ alpha)
    (hcount : ∀ a, 0 ≤ c n a)
    (hdominant : (1 - mu) * collisionEnergy c n ≤
      dominantParentEnergy c dominant n)
    (hretain : ∀ a, dominant n a →
      alpha * c n a ≤ c (n + 1) (decimalChild n a (choose n a))) :
    leakage c dominant choose n ≤
      (1 - alpha ^ 2 * (1 - mu)) * collisionEnergy c n := by
  have hlocal := dominant_edge_retention c dominant choose alpha n
    halpha hcount hretain
  have hsquare : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hretained : alpha ^ 2 * ((1 - mu) * collisionEnergy c n) ≤
      retainedEdgeEnergy c dominant choose n :=
    (mul_le_mul_of_nonneg_left hdominant hsquare).trans hlocal
  unfold leakage
  nlinarith

/-- Collision energy carried by a coherent survivor set. -/
def survivorEnergy (c : DecimalCounts)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n))) (n : ℕ) : ℝ :=
  ∑ a ∈ survivors n, (c n a) ^ 2

/-- Positive-count nodes at one level. -/
def positiveSupport (c : DecimalCounts) (n : ℕ) : Finset (Fin (10 ^ n)) := by
  classical
  exact Finset.univ.filter fun a => c n a ≠ 0

/-- Removing zero-count nodes does not change collision energy. -/
theorem positiveSupport_energy_eq (c : DecimalCounts) (n : ℕ) :
    ∑ a ∈ positiveSupport c n, (c n a) ^ 2 = collisionEnergy c n := by
  classical
  rw [positiveSupport, Finset.sum_filter]
  unfold collisionEnergy
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : c n a = 0
  · simp [ha]
  · simp [ha]

/-- The exact compatibility condition between consecutive survivor sets. -/
def SurvivorStep
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n))) (n : ℕ) : Prop := by
  classical
  exact survivors (n + 1) =
    ((survivors n).filter (dominant n)).image
      (fun a => decimalChild n a (choose n a))

/-- One coherent refinement loses no more than the full-level leakage. -/
theorem survivor_step_loss_le_leakage (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n))) (n : ℕ)
    (hchild : ∀ a,
      (c (n + 1) (decimalChild n a (choose n a))) ^ 2 ≤ (c n a) ^ 2)
    (hstep : SurvivorStep dominant choose survivors n) :
    survivorEnergy c survivors n - survivorEnergy c survivors (n + 1) ≤
      leakage c dominant choose n := by
  classical
  let next : Fin (10 ^ n) → Fin (10 ^ (n + 1)) := fun a =>
    decimalChild n a (choose n a)
  have hnextInj : Function.Injective next :=
    decimalChild_parent_injective n (choose n)
  have hnext : survivorEnergy c survivors (n + 1) =
      ∑ a ∈ survivors n,
        if dominant n a then (c (n + 1) (next a)) ^ 2 else 0 := by
    rw [survivorEnergy, hstep]
    rw [Finset.sum_image (Set.injOn_of_injective hnextInj)]
    rw [Finset.sum_filter]
  rw [survivorEnergy, hnext, ← Finset.sum_sub_distrib]
  unfold leakage collisionEnergy retainedEdgeEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro a _ _
  by_cases ha : dominant n a
  · simp only [ha, if_true]
    exact sub_nonneg.mpr (hchild a)
  · simpa [ha] using sq_nonneg (c n a)

/-- Additive telescoping over exactly the levels `r, ..., r+h-1`. -/
theorem sub_le_sum_range_of_step (M L : ℕ → ℝ) (r h : ℕ)
    (hstep : ∀ i, i < h → M (r + i) - M (r + i + 1) ≤ L (r + i)) :
    M r - M (r + h) ≤ ∑ i ∈ Finset.range h, L (r + i) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ]
      have hlast : M (r + h) - M (r + (h + 1)) ≤ L (r + h) := by
        simpa [Nat.add_assoc] using hstep h (Nat.lt_succ_self h)
      have hfirst : ∀ i, i < h →
          M (r + i) - M (r + i + 1) ≤ L (r + i) :=
        fun i hi => hstep i (hi.trans (Nat.lt_succ_self h))
      have hih := ih hfirst
      linarith

/-- T27's finite full-edge leakage theorem.  The tree range, consecutive
levels, survivor start, and every successor-image compatibility equation are
theorem hypotheses. -/
theorem finite_base10_leakage_telescope (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (r h : ℕ) (htree : IsFiniteDecimalCountTree c (r + h))
    (hstartMass : survivorEnergy c survivors r = collisionEnergy c r)
    (hsteps : ∀ i, i < h →
      SurvivorStep dominant choose survivors (r + i)) :
    collisionEnergy c r - survivorEnergy c survivors (r + h) ≤
      ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) := by
  rcases htree with ⟨hnonneg, hconserve⟩
  have hlocal : ∀ i, i < h →
      survivorEnergy c survivors (r + i) -
          survivorEnergy c survivors (r + i + 1) ≤
        leakage c dominant choose (r + i) := by
    intro i hi
    apply survivor_step_loss_le_leakage c dominant choose survivors (r + i)
    · intro a
      have hlevel : r + i + 1 ≤ r + h := by omega
      have hchildren : ∀ d : Fin 10,
          0 ≤ c (r + i + 1) (decimalChild (r + i) a d) :=
        fun d => hnonneg (r + i + 1) hlevel _
      have hparentChild := child_le_parent c (r + i) hchildren
        (hconserve (r + i) (by omega) a) (choose (r + i) a)
      have hchosenNonneg := hchildren (choose (r + i) a)
      nlinarith
    · exact hsteps i hi
  have htelescope := sub_le_sum_range_of_step
    (fun n => survivorEnergy c survivors n)
    (fun n => leakage c dominant choose n) r h hlocal
  change survivorEnergy c survivors r - survivorEnergy c survivors (r + h) ≤
    ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) at htelescope
  rw [hstartMass] at htelescope
  exact htelescope

/-- Some point of a nonempty finite set is at least its average, without
division. -/
theorem exists_sum_le_card_mul_of_nonempty {ι : Type*} [Fintype ι]
    (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ S, ∑ j ∈ S, f j ≤ (S.card : ℝ) * f i := by
  obtain ⟨i, hi, himax⟩ := S.exists_max_image f hS
  refine ⟨i, hi, ?_⟩
  simpa [nsmul_eq_mul] using S.sum_le_card_nsmul f (f i) himax

/-- Multiplicative retained-count bound along one explicitly nested path.
The path uses exactly the selected edges at levels `r, ..., r+h-1`. -/
theorem selected_path_retains_product (c : DecimalCounts)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (alpha : ℕ → ℝ) (r h : ℕ)
    (path : (i : ℕ) → Fin (10 ^ (r + i)))
    (halpha : ∀ i, i < h → 0 ≤ alpha (r + i))
    (hcompat : ∀ i, i < h →
      path (i + 1) = Fin.cast (by congr 1)
        (decimalChild (r + i) (path i) (choose (r + i) (path i))))
    (hretain : ∀ i, i < h →
      alpha (r + i) * c (r + i) (path i) ≤
        c (r + i + 1)
          (decimalChild (r + i) (path i) (choose (r + i) (path i)))) :
    (∏ i ∈ Finset.range h, alpha (r + i)) * c r (path 0) ≤
      c (r + h) (path h) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.prod_range_succ]
      have hih := ih (fun i hi => halpha i (hi.trans (Nat.lt_succ_self h)))
        (fun i hi => hcompat i (hi.trans (Nat.lt_succ_self h)))
        (fun i hi => hretain i (hi.trans (Nat.lt_succ_self h)))
      have hlastRaw := hretain h (Nat.lt_succ_self h)
      have hlast : alpha (r + h) * c (r + h) (path h) ≤
          c (r + (h + 1)) (path (h + 1)) := by
        rw [hcompat h (Nat.lt_succ_self h)]
        simpa using hlastRaw
      have ha := halpha h (Nat.lt_succ_self h)
      calc
        ((∏ i ∈ Finset.range h, alpha (r + i)) * alpha (r + h)) *
              c r (path 0) =
            alpha (r + h) *
              ((∏ i ∈ Finset.range h, alpha (r + i)) * c r (path 0)) := by
                ring
        _ ≤ alpha (r + h) * c (r + h) (path h) :=
          mul_le_mul_of_nonneg_left hih ha
        _ ≤ c (r + (h + 1)) (path (h + 1)) := hlast

/-- Explicit retained-mass endpoint bound.  If total leakage is less than the
initial energy, a coherent endpoint exists and its squared count is at least
the surviving mass divided by the number of endpoints (division-free form). -/
theorem exists_endpoint_with_retained_mass (c : DecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (r h : ℕ) (htree : IsFiniteDecimalCountTree c (r + h))
    (hstartMass : survivorEnergy c survivors r = collisionEnergy c r)
    (hsteps : ∀ i, i < h →
      SurvivorStep dominant choose survivors (r + i))
    (hpositive :
      ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) <
        collisionEnergy c r) :
    ∃ b ∈ survivors (r + h),
      collisionEnergy c r -
          ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) ≤
        ((survivors (r + h)).card : ℝ) * (c (r + h) b) ^ 2 := by
  have hbound := finite_base10_leakage_telescope c dominant choose survivors
    r h htree hstartMass hsteps
  have hQpos : 0 < collisionEnergy c r -
      ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) :=
    sub_pos.mpr hpositive
  have hnonempty : (survivors (r + h)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero : survivorEnergy c survivors (r + h) = 0 := by
      simp [survivorEnergy, hempty]
    rw [hzero] at hbound
    linarith
  obtain ⟨b, hb, havg⟩ := exists_sum_le_card_mul_of_nonempty
    (survivors (r + h)) hnonempty (fun a => (c (r + h) a) ^ 2)
  have hQle : collisionEnergy c r -
        ∑ i ∈ Finset.range h, leakage c dominant choose (r + i) ≤
      survivorEnergy c survivors (r + h) := by
    linarith
  refine ⟨b, hb, hQle.trans ?_⟩
  simpa [survivorEnergy] using havg

/-- Integer-count specialization of the finite leakage theorem. -/
theorem finite_base10_countTree_leakage (c : NaturalDecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (r h : ℕ) (htree : IsFiniteBase10CountTree c (r + h))
    (hstartMass : survivorEnergy c.toReal survivors r =
      collisionEnergy c.toReal r)
    (hsteps : ∀ i, i < h →
      SurvivorStep dominant choose survivors (r + i)) :
    collisionEnergy c.toReal r -
        survivorEnergy c.toReal survivors (r + h) ≤
      ∑ i ∈ Finset.range h,
        leakage c.toReal dominant choose (r + i) :=
  finite_base10_leakage_telescope c.toReal dominant choose survivors r h
    (naturalCountTree_toReal c (r + h) htree) hstartMass hsteps

/-- Integer-count specialization of the explicit retained-mass endpoint
bound.  Its right side is the number of surviving endpoints times one
endpoint's squared integer count. -/
theorem finite_base10_countTree_retained_mass (c : NaturalDecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (r h : ℕ) (htree : IsFiniteBase10CountTree c (r + h))
    (hstartMass : survivorEnergy c.toReal survivors r =
      collisionEnergy c.toReal r)
    (hsteps : ∀ i, i < h →
      SurvivorStep dominant choose survivors (r + i))
    (hpositive :
      ∑ i ∈ Finset.range h, leakage c.toReal dominant choose (r + i) <
        collisionEnergy c.toReal r) :
    ∃ b ∈ survivors (r + h),
      collisionEnergy c.toReal r -
          ∑ i ∈ Finset.range h,
            leakage c.toReal dominant choose (r + i) ≤
        ((survivors (r + h)).card : ℝ) * (c (r + h) b : ℝ) ^ 2 := by
  simpa [NaturalDecimalCounts.toReal] using
    exists_endpoint_with_retained_mass c.toReal dominant choose survivors r h
      (naturalCountTree_toReal c (r + h) htree) hstartMass hsteps hpositive

/-- Normalized retained-mass form.  A cumulative leakage of at most
`Lambda * E_r`, with `Lambda < 1`, leaves an endpoint carrying the
explicit fraction `(1-Lambda) / card` of the initial collision energy. -/
theorem finite_base10_countTree_retained_fraction
    (c : NaturalDecimalCounts)
    (dominant : (n : ℕ) → Fin (10 ^ n) → Prop)
    (choose : (n : ℕ) → Fin (10 ^ n) → Fin 10)
    (survivors : (n : ℕ) → Finset (Fin (10 ^ n)))
    (r h : ℕ) (Lambda : ℝ)
    (htree : IsFiniteBase10CountTree c (r + h))
    (hstartMass : survivorEnergy c.toReal survivors r =
      collisionEnergy c.toReal r)
    (hsteps : ∀ i, i < h →
      SurvivorStep dominant choose survivors (r + i))
    (hLambdaOne : Lambda < 1)
    (henergy : 0 < collisionEnergy c.toReal r)
    (hleakage :
      ∑ i ∈ Finset.range h, leakage c.toReal dominant choose (r + i) ≤
        Lambda * collisionEnergy c.toReal r) :
    ∃ b ∈ survivors (r + h),
      (1 - Lambda) * collisionEnergy c.toReal r ≤
        ((survivors (r + h)).card : ℝ) * (c (r + h) b : ℝ) ^ 2 := by
  have hpositive :
      ∑ i ∈ Finset.range h, leakage c.toReal dominant choose (r + i) <
        collisionEnergy c.toReal r := by
    calc
      _ ≤ Lambda * collisionEnergy c.toReal r := hleakage
      _ < collisionEnergy c.toReal r := by nlinarith
  obtain ⟨b, hb, hbound⟩ := finite_base10_countTree_retained_mass
    c dominant choose survivors r h htree hstartMass hsteps hpositive
  refine ⟨b, hb, ?_⟩
  have hlower : (1 - Lambda) * collisionEnergy c.toReal r ≤
      collisionEnergy c.toReal r -
        ∑ i ∈ Finset.range h,
          leakage c.toReal dominant choose (r + i) := by
    nlinarith
  exact hlower.trans hbound

/-! ## Generic bounded-start compactness -/

universe u

/-- One finite path for a fixed level-indexed edge predicate.  `length`
counts edges, so `node` has `length + 1` entries. -/
structure GoodPrefix (Node : ℕ → Type u)
    (edge : (n : ℕ) → Node n → Node (n + 1) → Prop)
    (start length : ℕ) where
  node : (i : Fin (length + 1)) → Node (start + i.val)
  good : ∀ i : Fin length,
    edge (start + i.val) (node i.castSucc)
      (by simpa only [Nat.add_assoc] using node i.succ)

/-- An infinite branch beginning at the explicit level `start`. -/
def InfiniteGoodBranch {Node : ℕ → Type u}
    (edge : (n : ℕ) → Node n → Node (n + 1) → Prop)
    (start : ℕ) (node : (i : ℕ) → Node (start + i)) : Prop :=
  ∀ i, edge (start + i) (node i)
    (by simpa only [Nat.add_assoc] using node (i + 1))

theorem goodPrefix_finite {Node : ℕ → Type u} [∀ n, Finite (Node n)]
    (edge : (n : ℕ) → Node n → Node (n + 1) → Prop)
    (start length : ℕ) : Finite (GoodPrefix Node edge start length) := by
  apply Finite.of_injective (fun p : GoodPrefix Node edge start length => p.node)
  intro p q hpq
  cases p with
  | mk pn pg =>
      cases q with
      | mk qn qg =>
          dsimp only at hpq
          subst qn
          rfl

/-- Restrict a good prefix to its first `shorter` edges. -/
def GoodPrefix.restrict {Node : ℕ → Type u}
    {edge : (n : ℕ) → Node n → Node (n + 1) → Prop}
    {start shorter longer : ℕ} (h : shorter ≤ longer)
    (p : GoodPrefix Node edge start longer) :
    GoodPrefix Node edge start shorter where
  node i := p.node (Fin.castLE (Nat.add_le_add_right h 1) i)
  good i := by
    simpa only [Nat.add_assoc] using p.good (Fin.castLE h i)

theorem GoodPrefix.restrict_refl {Node : ℕ → Type u}
    {edge : (n : ℕ) → Node n → Node (n + 1) → Prop}
    {start length : ℕ} (p : GoodPrefix Node edge start length) :
    p.restrict (le_refl length) = p := by
  cases p
  rfl

theorem GoodPrefix.restrict_trans {Node : ℕ → Type u}
    {edge : (n : ℕ) → Node n → Node (n + 1) → Prop}
    {start i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (p : GoodPrefix Node edge start k) :
    (p.restrict hjk).restrict hij = p.restrict (hij.trans hjk) := by
  cases p
  rfl

/-- Generic bounded-start compactness.  The edge predicate is fixed outside
the length quantifier, every level type is finite, and all finite starts are
bounded by the same `startBound`.  Each witness is only a local dependent
prefix: levels before its start need not be inhabited.  Finite pigeonhole
selects one start occurring at unbounded lengths, after which Kőnig's
inverse-system lemma applies. -/
theorem exists_infinite_good_branch_of_bounded_starts
    {Node : ℕ → Type u} [∀ n, Finite (Node n)]
    (edge : (n : ℕ) → Node n → Node (n + 1) → Prop)
    (startBound : ℕ)
    (hlong : ∀ length, ∃ start, start ≤ startBound ∧
      Nonempty (GoodPrefix Node edge start length)) :
    ∃ start, start ≤ startBound ∧
      ∃ node : (i : ℕ) → Node (start + i),
        InfiniteGoodBranch edge start node := by
  classical
  choose start hstart hprefix using hlong
  let boundedStart : ℕ → Fin (startBound + 1) := fun length =>
    ⟨start length, Nat.lt_succ_of_le (hstart length)⟩
  have hsome : ∃ᶠ length in Filter.atTop,
      ∃ fixed : Fin (startBound + 1), boundedStart length = fixed := by
    refine frequently_atTop.2 fun lower => ?_
    exact ⟨lower, le_rfl, boundedStart lower, rfl⟩
  obtain ⟨fixed, hfixed⟩ := Filter.frequently_exists.mp hsome
  have hAtFixed : ∀ length,
      Nonempty (GoodPrefix Node edge fixed.val length) := by
    intro length
    obtain ⟨longer, hle, hsame⟩ := hfixed.forall_exists_of_atTop length
    have hstartEq : start longer = fixed.val := congrArg Fin.val hsame
    have p := Classical.choice (hprefix longer)
    rw [hstartEq] at p
    exact ⟨p.restrict hle⟩
  let Prefix : ℕ → Type u := fun length =>
    GoodPrefix Node edge fixed.val length
  letI (length : ℕ) : Nonempty (Prefix length) := by
    exact hAtFixed length
  letI (length : ℕ) : Finite (Prefix length) :=
    goodPrefix_finite edge fixed.val length
  let π : {i j : ℕ} → i ≤ j → Prefix j → Prefix i :=
    fun {i j} hij (p : Prefix j) => GoodPrefix.restrict hij p
  have hπrefl : ∀ ⦃i⦄ (p : Prefix i), π (le_refl i) p = p := by
    intro i p
    exact GoodPrefix.restrict_refl p
  have hπtrans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (p : Prefix k),
      π hij (π hjk p) = π (hij.trans hjk) p := by
    intro i j k hij hjk p
    exact GoodPrefix.restrict_trans hij hjk p
  have hπfinite : ∀ i (p : Prefix i),
      {q : Prefix (i + 1) | π (Nat.le_add_right i 1) q = p}.Finite := by
    intro i p
    exact Set.toFinite _
  obtain ⟨pref, hpref⟩ := exists_seq_forall_proj_of_forall_finite
    π hπrefl hπtrans hπfinite
  let branch : (i : ℕ) → Node (fixed.val + i) := fun i =>
    (pref i).node (Fin.last i)
  refine ⟨fixed.val, by omega, branch, ?_⟩
  intro i
  have hedge := (pref (i + 1)).good (Fin.last i)
  have hp := hpref (Nat.le_add_right i 1)
  have hpnode := congrArg
    (fun p : Prefix i => p.node (Fin.last i)) hp
  dsimp only [π, GoodPrefix.restrict] at hpnode
  dsimp only [branch]
  convert hedge using 1
  · simpa using hpnode.symm

/-! ## Fixed decimal dominant edges and the exact T14 gap -/

/-- One fixed decimal-tree predicate: both `cutoff` and `eta` are outside all
path-length quantifiers, and child compatibility is literal decimal append. -/
def PiDominantEdge (cutoff : ℕ) (eta : ℝ) (n : ℕ)
    (a : Fin (10 ^ n)) (b : Fin (10 ^ (n + 1))) : Prop :=
  ∃ d : Fin 10, b = decimalChild n a d ∧
    (1 - 9 * eta) * (piCylinderFiber n cutoff a).card ≤
      piSuccessorCount n cutoff a d

/-- The synchronization premise not supplied by T14: one fixed cutoff, one
fixed `eta`, one fixed dominant-edge predicate, and one uniform start bound
work for arbitrarily long finite paths. -/
def T14MissingBoundedFixedPredicatePremise
    (cutoff startBound : ℕ) (eta : ℝ) : Prop :=
  ∀ length, ∃ start, start ≤ startBound ∧
    Nonempty (GoodPrefix (fun n => Fin (10 ^ n))
      (PiDominantEdge cutoff eta) start length)

/-- The literal quantified splitting failure furnished by accepted T14. -/
def T14QuantifiedSplittingFailure : Prop :=
  ∀ (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle),
    0 < mu → mu < 1 → 0 < eta → eta ≤ 1 / 10 →
    0 < d → 0 ≤ B → StrictMono N → (∀ k, 0 < N k) →
    Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) Filter.atTop (nhds nu) →
    ∃ k : ℕ, k0 ≤ k ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ k ∧
      (piSplittingLevelCount m (N k) mu eta : ℝ) < d * (m : ℝ) - B

/-- T14's stronger checked interface, including the explicit weighted
dominance conclusion at every nonsplitting level of the bad row. -/
def T14FailureAndWeightedDominance : Prop :=
  ∀ (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle),
    0 < mu → mu < 1 → 0 < eta → eta ≤ 1 / 10 →
    0 < d → 0 ≤ B → StrictMono N → (∀ k, 0 < N k) →
    Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) Filter.atTop (nhds nu) →
    ∃ k : ℕ, k0 ≤ k ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ k ∧
      (piSplittingLevelCount m (N k) mu eta : ℝ) < d * (m : ℝ) - B ∧
      ∀ l ∈ Finset.range m,
        ¬ QuantitativeSplittingLevel l (N k) mu eta →
          (1 - mu) * piCylinderCollisionEnergy l (N k) <
            piDominantSuccessorEnergy l (N k) eta

/-- T14 interface.  Literal `¬ C2` gives T14's finite levelwise failure, while
an infinite nested branch follows only after separately supplying the stated
bounded-start/fixed-predicate premise.  No such premise is concluded here. -/
theorem t14_failure_and_compactness_interface
    (hnotC2 : ¬ PiPolynomialSmallBallC2) :
    T14FailureAndWeightedDominance ∧
      ∀ (cutoff startBound : ℕ) (eta : ℝ),
        T14MissingBoundedFixedPredicatePremise cutoff startBound eta →
        ∃ start, start ≤ startBound ∧
          ∃ node : (i : ℕ) → Fin (10 ^ (start + i)),
            InfiniteGoodBranch (PiDominantEdge cutoff eta) start node := by
  constructor
  · intro mu eta d B m0 k0 N nu hmu hmuUpper heta hetaUpper
      hd hB hNmono hNpos hnu
    exact not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance
      hnotC2 mu eta d B m0 k0 N nu hmu hmuUpper heta hetaUpper
        hd hB hNmono hNpos hnu
  · intro cutoff startBound eta hmissing
    exact exists_infinite_good_branch_of_bounded_starts
      (PiDominantEdge cutoff eta) startBound hmissing

end DecimalFactorComplexity.FiniteCountTreeLeakage

#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.finite_base10_countTree_mass_conservation
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.collisionEnergy_succ_le
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.dominant_edge_retention
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.leakage_le_explicit
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.finite_base10_countTree_leakage
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.finite_base10_countTree_retained_mass
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.finite_base10_countTree_retained_fraction
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.selected_path_retains_product
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.exists_infinite_good_branch_of_bounded_starts
#print axioms DecimalFactorComplexity.FiniteCountTreeLeakage.t14_failure_and_compactness_interface
