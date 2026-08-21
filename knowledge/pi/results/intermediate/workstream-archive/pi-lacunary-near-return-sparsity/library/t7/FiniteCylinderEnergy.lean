import TheoryLib.PiLacunaryNearReturnSparsity.T1LagDecomposition
import TheoryLib.PiLacunaryNearReturnSparsity.T6CylinderCollision

/-!
# Finite decimal-cylinder energy equivalent to canonical C1

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The first `N` orbit points are indexed by `Fin N`, so every pair count below is
ordered and contains all diagonal pairs. The threshold in `Q_pi` remains the
strict circle-distance threshold. This module proves an equivalent finite-prefix
reduction; it does not prove the canonical statement or any decay for pi.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.FiniteCylinderEnergy

open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The length-`n` decimal-cylinder label of the `i`th point of the pi orbit. -/
def piCylinderCode (n i : ℕ) : Fin (10 ^ n) :=
  ⟨prefixLabel piDecimalStream n i, prefixLabel_lt piDecimalStream n i⟩

/-- Starts among `0, ..., N-1` lying in decimal cylinder `a`. -/
def piCylinderFiber (n N : ℕ) (a : Fin (10 ^ n)) : Finset (Fin N) :=
  Finset.univ.filter fun i => piCylinderCode n i = a

/-- Ordered first-`N` pairs lying in the same length-`n` decimal cylinder. -/
def piCylinderEqualPairs (n N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun ij => piCylinderCode n ij.1 = piCylinderCode n ij.2

/-- The unnormalized finite collision energy, namely the sum of squared
cylinder occupancies. -/
def piCylinderCollisionEnergy (n N : ℕ) : ℕ :=
  ∑ a : Fin (10 ^ n), (piCylinderFiber n N a).card ^ 2

/-- The collision count divided by the number `N^2` of ordered pairs. -/
def normalizedPiCylinderCollisionEnergy (n N : ℕ) : ℝ :=
  (piCylinderCollisionEnergy n N : ℝ) / (N : ℝ) ^ 2

/-- Equal cyclic-code pairs are the identity graph; the other permutations
below encode the two wraparound-aware adjacent-cylinder graphs. -/
def piCylinderCodeGraph (n N : ℕ) (e : Equiv.Perm (Fin (10 ^ n))) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter fun ij => piCylinderCode n ij.2 = e (piCylinderCode n ij.1)

/-- The canonical coordinate of the circle orbit point is its ordinary
fractional-part representative in `[0,1)`. -/
theorem unitCoordinate_piDecimalCircleOrbit (i : ℕ) :
    unitCoordinate (piDecimalCircleOrbit i) =
      Theory.PiDigits.T20.baseTenOrbit Real.pi i := by
  unfold unitCoordinate piDecimalCircleOrbit Theory.PiDigits.T20.baseTenOrbit
  simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]

/-- The symbolic label used above is exactly T6's half-open decimal-cylinder
code of the corresponding pi orbit point. The strict upper endpoint follows
from irrationality of pi, including the last cylinder whose endpoint is `1`. -/
theorem piCylinderCode_eq_decimalCode (n i : ℕ) :
    piCylinderCode n i = decimalCode n (piDecimalCircleOrbit i) := by
  let a := prefixLabel piDecimalStream n i
  let q := 10 ^ n
  have ha : a < q := prefixLabel_lt piDecimalStream n i
  have hcell := tailOrbit_mem_closedCell piDecimalStream n i
  rw [tailOrbit_decimalDigit_eq_baseTenOrbit Real.pi Real.pi_pos.le] at hcell
  have hcell' : Theory.PiDigits.T20.baseTenOrbit Real.pi i ∈
      Set.Icc ((a : ℝ) / q) (((a + 1 : ℕ) : ℝ) / q) := by
    simpa [a, q] using hcell
  have hstrict : Theory.PiDigits.T20.baseTenOrbit Real.pi i <
      ((a + 1 : ℕ) : ℝ) / q := by
    have hasucc : a + 1 ≤ q := Nat.succ_le_iff.mpr ha
    rcases lt_or_eq_of_le hasucc with hlt | heq
    · have havoid :=
        Theory.PiDigits.DecimalBoundaryWordObstruction.piFractionalOrbit_avoids_grid_endpoints
          i q (by positivity)
      have hne := havoid (a + 1) hlt
      have hne' : Theory.PiDigits.T20.baseTenOrbit Real.pi i ≠
          ((a + 1 : ℕ) : ℝ) / q := by
        simpa [Theory.PiDigits.T20.baseTenOrbit,
          Theory.PiDigits.T27.piFractionalOrbit] using hne
      exact lt_of_le_of_ne hcell'.2 hne'
    · have hxlt := (Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi i).2
      have hupp : (((a + 1 : ℕ) : ℝ) / q) = 1 := by
        rw [heq]
        simp [q]
      rwa [hupp]
  have hmem : piDecimalCircleOrbit i ∈ decimalCylinder n (piCylinderCode n i) := by
    rw [mem_decimalCylinder_iff, unitCoordinate_piDecimalCircleOrbit]
    simpa [piCylinderCode, a, q] using
      (show Theory.PiDigits.T20.baseTenOrbit Real.pi i ∈
        Set.Ico ((a : ℝ) / q) (((a + 1 : ℕ) : ℝ) / q) from
          ⟨hcell'.1, hstrict⟩)
  change decimalCode n (piDecimalCircleOrbit i) = piCylinderCode n i at hmem
  exact hmem.symm

/-- The symbolic cylinder label is exactly the equality invariant of T1's
length-`n` factors. -/
theorem piCylinderCode_eq_iff_factorAt_eq (n i j : ℕ) :
    piCylinderCode n i = piCylinderCode n j ↔
      factorAt piDecimalStream n i = factorAt piDecimalStream n j := by
  constructor
  · intro hcode
    have hlabel : prefixLabel piDecimalStream n i =
        prefixLabel piDecimalStream n j := congrArg Fin.val hcode
    have hword : prefixWord piDecimalStream n i =
        prefixWord piDecimalStream n j :=
      Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_injective_of_length
        (by simp [prefixWord]) hlabel
    apply Subtype.ext
    exact List.ofFn_inj.mp (by simpa [prefixWord, factorAt, blockAt] using hword)
  · intro hfactor
    apply Fin.ext
    change prefixLabel piDecimalStream n i = prefixLabel piDecimalStream n j
    unfold prefixLabel
    apply congrArg Theory.PiDigits.T20.wordValue
    apply List.ofFn_inj.mpr
    simpa [factorAt, blockAt] using congrArg Subtype.val hfactor

/-- The sum of squared cylinder occupancies is exactly the finite cardinality
of the ordered equal-cylinder pair set. -/
theorem piCylinderCollisionEnergy_eq_equalPairs_card (n N : ℕ) :
    piCylinderCollisionEnergy n N = (piCylinderEqualPairs n N).card := by
  classical
  let S := piCylinderEqualPairs n N
  have hpartition :
      S.card = ∑ a : Fin (10 ^ n),
        (S.filter fun ij => piCylinderCode n ij.1 = a).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin (10 ^ n))))
      (f := fun ij => piCylinderCode n ij.1) (by simp)
  rw [piCylinderCollisionEnergy, hpartition]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [pow_two, ← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [S, piCylinderEqualPairs, piCylinderFiber, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨hi.trans hj.symm, hi⟩
  · rintro ⟨hij, hi⟩
    exact ⟨hi, hij.symm.trans hi⟩

/-- The normalized energy is literally the proportion of ordered first-`N`
pairs in a common half-open decimal cylinder. -/
theorem normalizedPiCylinderCollisionEnergy_eq_equalPairs_card_div (n N : ℕ) :
    normalizedPiCylinderCollisionEnergy n N =
      ((piCylinderEqualPairs n N).card : ℝ) / (N : ℝ) ^ 2 := by
  rw [normalizedPiCylinderCollisionEnergy,
    piCylinderCollisionEnergy_eq_equalPairs_card]

/-- T8's factor collision energy and the decimal-cylinder energy are the same
finite statistic, rather than two independent hypotheses. -/
theorem piCylinderCollisionEnergy_eq_E_pi (n N : ℕ) :
    piCylinderCollisionEnergy n N = E_pi n N := by
  rw [piCylinderCollisionEnergy_eq_equalPairs_card]
  change (piCylinderEqualPairs n N).card = collisionEnergy piDecimalStream n N
  rw [collisionEnergy_eq_collisionPairCount, collisionPairCount]
  apply congrArg Finset.card
  ext ij
  simp only [piCylinderEqualPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_collisionPairs_iff]
  exact piCylinderCode_eq_iff_factorAt_eq n ij.1 ij.2

/-- All `N` diagonal pairs occur in the finite cylinder collision count. -/
theorem diagonal_le_piCylinderCollisionEnergy (n N : ℕ) :
    N ≤ piCylinderCollisionEnergy n N := by
  rw [piCylinderCollisionEnergy_eq_equalPairs_card]
  calc
    N = ((Finset.univ : Finset (Fin N)).diag).card := by simp
    _ ≤ (piCylinderEqualPairs n N).card := by
      apply Finset.card_le_card
      intro ij hij
      rw [Finset.mem_diag] at hij
      rcases ij with ⟨i, j⟩
      rcases hij with ⟨_hi, hij⟩
      change i = j at hij
      subst j
      simp [piCylinderEqualPairs]

/-- At positive cutoff the normalized collision energy is positive; this is
the explicit contribution of the retained diagonal. -/
theorem normalizedPiCylinderCollisionEnergy_pos (n N : ℕ) (hN : 1 ≤ N) :
    0 < normalizedPiCylinderCollisionEnergy n N := by
  unfold normalizedPiCylinderCollisionEnergy
  apply div_pos
  · exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt hN)
      (diagonal_le_piCylinderCollisionEnergy n N)
  · positivity

/-- A code-permutation graph has the expected cross-fiber cardinality. -/
theorem piCylinderCodeGraph_card_eq_crossSum (n N : ℕ)
    (e : Equiv.Perm (Fin (10 ^ n))) :
    (piCylinderCodeGraph n N e).card =
      ∑ a : Fin (10 ^ n),
        (piCylinderFiber n N a).card * (piCylinderFiber n N (e a)).card := by
  classical
  let S := piCylinderCodeGraph n N e
  have hpartition :
      S.card = ∑ a : Fin (10 ^ n),
        (S.filter fun ij => piCylinderCode n ij.1 = a).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin (10 ^ n))))
      (f := fun ij => piCylinderCode n ij.1) (by simp)
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [S, piCylinderCodeGraph, piCylinderFiber, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨hgraph, hi⟩
    exact ⟨hi, by simpa [hi] using hgraph⟩
  · rintro ⟨hi, hj⟩
    exact ⟨by simpa [hi] using hj, hi⟩

/-- Every permutation graph cross-count is at most the collision energy. -/
theorem piCylinderCodeGraph_card_le_energy (n N : ℕ)
    (e : Equiv.Perm (Fin (10 ^ n))) :
    (piCylinderCodeGraph n N e).card ≤ piCylinderCollisionEnergy n N := by
  rw [piCylinderCodeGraph_card_eq_crossSum, piCylinderCollisionEnergy]
  let m : Fin (10 ^ n) → ℝ := fun a => (piCylinderFiber n N a).card
  have hperm : (∑ a : Fin (10 ^ n), m (e a) ^ 2) =
      ∑ a : Fin (10 ^ n), m a ^ 2 := by
    exact Equiv.sum_comp e (fun a => m a ^ 2)
  have hnonneg : 0 ≤ ∑ a : Fin (10 ^ n), m a ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin (10 ^ n))) m (fun a => m (e a))
  rw [hperm] at hcs
  change (∑ a : Fin (10 ^ n), m a * m (e a)) ≤
    √(∑ a : Fin (10 ^ n), m a ^ 2) * √(∑ a : Fin (10 ^ n), m a ^ 2) at hcs
  rw [Real.mul_self_sqrt hnonneg] at hcs
  dsimp [m] at hcs
  exact_mod_cast hcs

/-- Every strict canonical near return has equal or cyclically adjacent
decimal-cylinder labels, including the `0`/`10^n-1` wraparound. -/
theorem piNearReturnPairs_subset_three_codeGraphs (n N : ℕ) :
    piNearReturnPairs n N ⊆
      piCylinderCodeGraph n N (Equiv.refl _) ∪
        (piCylinderCodeGraph n N (finRotate (10 ^ n)) ∪
          piCylinderCodeGraph n N (finRotate (10 ^ n)).symm) := by
  intro ij hij
  have hstream : ij ∈ nearReturnPairs piDecimalStream n N := by
    rw [mem_nearReturnPairs_iff]
    rw [tailOrbit_decimalDigit_eq_baseTenOrbit Real.pi Real.pi_pos.le,
      tailOrbit_decimalDigit_eq_baseTenOrbit Real.pi Real.pi_pos.le]
    let z : ℤ :=
      ⌊(10 : ℝ) ^ (ij.2 : ℕ) * Real.pi⌋ -
        ⌊(10 : ℝ) ^ (ij.1 : ℕ) * Real.pi⌋
    have hdifference :
        Theory.PiDigits.T20.baseTenOrbit Real.pi ij.2 -
            Theory.PiDigits.T20.baseTenOrbit Real.pi ij.1 =
          (((10 : ℝ) ^ (ij.2 : ℕ) - (10 : ℝ) ^ (ij.1 : ℕ)) * Real.pi) - z := by
      dsimp [Theory.PiDigits.T20.baseTenOrbit, z]
      rw [Int.cast_sub]
      simp only [Int.fract]
      ring
    rw [hdifference, circleDistance_sub_int]
    exact (mem_piNearReturnPairs_iff n N ij).mp hij
  have hadj := nearReturn_implies_prefixLabels_adjacent piDecimalStream n
    (i := ij.1) (j := ij.2) ((mem_nearReturnPairs_iff _ _ _ _).mp hstream)
  have hadjCode : CyclicAdjacent (10 ^ n)
      (piCylinderCode n ij.1) (piCylinderCode n ij.2) := by
    simpa [piCylinderCode] using hadj
  rcases cyclicAdjacent_three_cases (by positivity) _ _ hadjCode with h | h | h
  · rw [Finset.mem_union]
    left
    simpa [piCylinderCodeGraph] using h
  · rw [Finset.mem_union]
    right
    rw [Finset.mem_union]
    left
    simpa [piCylinderCodeGraph] using h
  · rw [Finset.mem_union]
    right
    rw [Finset.mem_union]
    right
    simpa [piCylinderCodeGraph] using h

/-- Explicit finite two-sided comparison. The lower bound uses strict
distance and the upper bound uses exactly three cyclic code graphs. -/
theorem piCylinderCollisionEnergy_le_Q_pi_le_three_mul (n N : ℕ) :
    piCylinderCollisionEnergy n N ≤ Q_pi n N ∧
      Q_pi n N ≤ 3 * piCylinderCollisionEnergy n N := by
  constructor
  · rw [piCylinderCollisionEnergy_eq_E_pi]
    exact pi_collisionEnergy_le_Q_pi n N
  · let G0 := piCylinderCodeGraph n N (Equiv.refl (Fin (10 ^ n)))
    let Gp := piCylinderCodeGraph n N (finRotate (10 ^ n))
    let Gm := piCylinderCodeGraph n N (finRotate (10 ^ n)).symm
    calc
      Q_pi n N = (piNearReturnPairs n N).card := rfl
      _ ≤ (G0 ∪ (Gp ∪ Gm)).card :=
        Finset.card_le_card (piNearReturnPairs_subset_three_codeGraphs n N)
      _ ≤ G0.card + (Gp ∪ Gm).card := Finset.card_union_le _ _
      _ ≤ G0.card + (Gp.card + Gm.card) := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ piCylinderCollisionEnergy n N +
          (piCylinderCollisionEnergy n N + piCylinderCollisionEnergy n N) := by
        exact Nat.add_le_add
          (piCylinderCodeGraph_card_le_energy n N (Equiv.refl _))
          (Nat.add_le_add
            (piCylinderCodeGraph_card_le_energy n N (finRotate (10 ^ n)))
            (piCylinderCodeGraph_card_le_energy n N (finRotate (10 ^ n)).symm))
      _ = 3 * piCylinderCollisionEnergy n N := by omega

/-- The corresponding normalized comparison; positivity of `N` makes the
division by `N^2` legitimate. -/
theorem normalizedPiCylinderCollisionEnergy_Q_pi_comparison
    (n N : ℕ) (hN : 1 ≤ N) :
    normalizedPiCylinderCollisionEnergy n N ≤
        (Q_pi n N : ℝ) / (N : ℝ) ^ 2 ∧
      (Q_pi n N : ℝ) / (N : ℝ) ^ 2 ≤
        3 * normalizedPiCylinderCollisionEnergy n N := by
  have hden : 0 < (N : ℝ) ^ 2 := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hN
    positivity
  obtain ⟨hlower, hupper⟩ :=
    piCylinderCollisionEnergy_le_Q_pi_le_three_mul n N
  unfold normalizedPiCylinderCollisionEnergy
  constructor
  · apply (div_le_div_iff_of_pos_right hden).2
    exact_mod_cast hlower
  · calc
      (Q_pi n N : ℝ) / (N : ℝ) ^ 2 ≤
          (3 * piCylinderCollisionEnergy n N : ℕ) / (N : ℝ) ^ 2 := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact_mod_cast hupper
      _ = 3 * ((piCylinderCollisionEnergy n N : ℝ) / (N : ℝ) ^ 2) := by
        push_cast
        ring

/-- The finite-prefix energy frontier, with the literal every-`A`, eventually-
every-`n`, exists-`N` quantifiers and all positivity conditions exposed. -/
def PiFiniteCylinderEnergyFrontier : Prop :=
  ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
      A * n * piCylinderCollisionEnergy n N ≤ N ^ 2

/-- Canonical C1 is equivalent to the finite cylinder-energy frontier. The
left side is the unchanged canonical statement. This is an equivalent
reduction, not a proof that either side holds for pi. -/
theorem canonical_C1_iff_piFiniteCylinderEnergyFrontier :
    (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2) ↔
      PiFiniteCylinderEnergyFrontier := by
  constructor
  · intro hcanonical A hA
    obtain ⟨n0, hn0, hall⟩ := hcanonical A hA
    refine ⟨n0, hn0, ?_⟩
    intro n hn
    obtain ⟨N, hN, hbound⟩ := hall n hn
    refine ⟨N, hN, ?_⟩
    calc
      A * n * piCylinderCollisionEnergy n N ≤ A * n * Q_pi n N := by
        exact Nat.mul_le_mul_left (A * n)
          (piCylinderCollisionEnergy_le_Q_pi_le_three_mul n N).1
      _ ≤ N ^ 2 := hbound
  · intro henergy A hA
    have hthreeA : 1 ≤ 3 * A := by omega
    obtain ⟨n0, hn0, hall⟩ := henergy (3 * A) hthreeA
    refine ⟨n0, hn0, ?_⟩
    intro n hn
    obtain ⟨N, hN, hbound⟩ := hall n hn
    refine ⟨N, hN, ?_⟩
    calc
      A * n * Q_pi n N ≤
          A * n * (3 * piCylinderCollisionEnergy n N) := by
        exact Nat.mul_le_mul_left (A * n)
          (piCylinderCollisionEnergy_le_Q_pi_le_three_mul n N).2
      _ = (3 * A) * n * piCylinderCollisionEnergy n N := by ring
      _ ≤ N ^ 2 := hbound

end DecimalFactorComplexity.FiniteCylinderEnergy

#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.unitCoordinate_piDecimalCircleOrbit
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_decimalCode
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_iff_factorAt_eq
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCollisionEnergy_eq_equalPairs_card
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.normalizedPiCylinderCollisionEnergy_eq_equalPairs_card_div
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCollisionEnergy_eq_E_pi
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.diagonal_le_piCylinderCollisionEnergy
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.normalizedPiCylinderCollisionEnergy_pos
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCodeGraph_card_eq_crossSum
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCodeGraph_card_le_energy
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piNearReturnPairs_subset_three_codeGraphs
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCollisionEnergy_le_Q_pi_le_three_mul
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.normalizedPiCylinderCollisionEnergy_Q_pi_comparison
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.canonical_C1_iff_piFiniteCylinderEnergyFrontier
