import TheoryLib.PiDecimalFactorComplexity.T1DecimalFactorComplexity
import TheoryLib.PiDecimalFactorComplexity.T3RightExtensionBranching
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite-prefix collision energy for factor complexity

Source: `problems/local/pi-decimal-factor-complexity.txt`
SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

For a zero-based stream, `Fin N` indexes precisely the first `N` starting
positions `0, ..., N - 1`. Thus for the fractional digits of a decimal
expansion these starts correspond to the conventional positions `d₁, ..., d_N`.
Every factor below is T1's contiguous arbitrary-position factor.

`CollisionEnergyC1` is a stronger sufficient sibling hypothesis, not the
canonical A1 statement. In particular, this file does not prove that the
decimal digit stream of pi satisfies C1, A1, or any growth conclusion. C1
remains unproved for pi.
-/

namespace DecimalFactorComplexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Starts among the first `N` positions producing the factor `w`. -/
noncomputable def prefixFactorFiber (s : Stream α) (n N : ℕ) (w : Factor s n) :
    Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun i => factorAt s n i = w

/-- Multiplicity of `w` among starts `0, ..., N - 1`. -/
noncomputable def factorMultiplicity (s : Stream α) (n N : ℕ) (w : Factor s n) : ℕ :=
  (prefixFactorFiber s n N w).card

/-- Distinct length-`n` factors seen at starts `0, ..., N - 1`. -/
noncomputable def observedFactors (s : Stream α) (n N : ℕ) : Finset (Factor s n) := by
  classical
  exact Finset.univ.image fun i : Fin N => factorAt s n i

/-- Number of distinct length-`n` factors observed at the first `N` starts. -/
noncomputable def observedFactorCount (s : Stream α) (n N : ℕ) : ℕ :=
  (observedFactors s n N).card

/-- Ordered pairs of first-`N` starts carrying equal length-`n` factors.
Diagonal pairs are included. -/
noncomputable def collisionPairs (s : Stream α) (n N : ℕ) : Finset (Fin N × Fin N) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    factorAt s n ij.1 = factorAt s n ij.2

/-- Cardinality of the ordered collision-pair set. -/
noncomputable def collisionPairCount (s : Stream α) (n N : ℕ) : ℕ :=
  (collisionPairs s n N).card

/-- Collision pairs whose first component carries `w`. -/
noncomputable def collisionPairFiber (s : Stream α) (n N : ℕ) (w : Factor s n) :
    Finset (Fin N × Fin N) := by
  classical
  exact (collisionPairs s n N).filter fun ij => factorAt s n ij.1 = w

/-- Collision energy: the sum of squared first-`N` factor multiplicities. -/
noncomputable def collisionEnergy (s : Stream α) (n N : ℕ) : ℕ :=
  (observedFactors s n N).sum fun w => factorMultiplicity s n N w ^ 2

omit [Fintype α] [DecidableEq α] in
@[simp] lemma mem_prefixFactorFiber_iff (s : Stream α) (n N : ℕ)
    (w : Factor s n) (i : Fin N) :
    i ∈ prefixFactorFiber s n N w ↔ factorAt s n i = w := by
  classical
  simp [prefixFactorFiber]

omit [Fintype α] [DecidableEq α] in
@[simp] lemma mem_observedFactors_iff (s : Stream α) (n N : ℕ) (w : Factor s n) :
    w ∈ observedFactors s n N ↔ ∃ i : Fin N, factorAt s n i = w := by
  classical
  simp [observedFactors]

omit [Fintype α] [DecidableEq α] in
@[simp] lemma mem_collisionPairs_iff (s : Stream α) (n N : ℕ) (ij : Fin N × Fin N) :
    ij ∈ collisionPairs s n N ↔ factorAt s n ij.1 = factorAt s n ij.2 := by
  classical
  simp [collisionPairs]

omit [Fintype α] [DecidableEq α] in
/-- Each ordered collision belongs to the fiber indexed by its first factor. -/
lemma collisionPair_firstFactor_mem_observedFactors (s : Stream α) (n N : ℕ)
    {ij : Fin N × Fin N} (_hij : ij ∈ collisionPairs s n N) :
    factorAt s n ij.1 ∈ observedFactors s n N := by
  rw [mem_observedFactors_iff]
  exact ⟨ij.1, rfl⟩

omit [Fintype α] [DecidableEq α] in
/-- A collision fiber over `w` is the Cartesian square of the start fiber of `w`. -/
lemma collisionPairs_fiber_card (s : Stream α) (n N : ℕ) (w : Factor s n) :
    (collisionPairFiber s n N w).card = factorMultiplicity s n N w ^ 2 := by
  classical
  rw [collisionPairFiber, factorMultiplicity, pow_two, ← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_filter, mem_collisionPairs_iff, Finset.mem_product,
    mem_prefixFactorFiber_iff]
  constructor
  · rintro ⟨hij, hiw⟩
    exact ⟨hiw, hij.symm.trans hiw⟩
  · rintro ⟨hiw, hjw⟩
    exact ⟨hiw.trans hjw.symm, hiw⟩

omit [Fintype α] [DecidableEq α] in
/-- The multiplicity-square energy is exactly the cardinality of the ordered
collision-pair set. -/
theorem collisionEnergy_eq_collisionPairCount (s : Stream α) (n N : ℕ) :
    collisionEnergy s n N = collisionPairCount s n N := by
  classical
  have hpartition :
      (collisionPairs s n N).card =
        ∑ w ∈ observedFactors s n N,
          (collisionPairFiber s n N w).card := by
    simpa only [collisionPairFiber] using
      (Finset.card_eq_sum_card_fiberwise fun ij hij =>
        collisionPair_firstFactor_mem_observedFactors s n N hij)
  rw [collisionEnergy, collisionPairCount, hpartition]
  apply Finset.sum_congr rfl
  intro w _
  exact collisionPairs_fiber_card s n N w |>.symm

omit [Fintype α] [DecidableEq α] in
/-- The multiplicities of all observed factors sum to the number `N` of starts. -/
lemma sum_factorMultiplicity_eq (s : Stream α) (n N : ℕ) :
    ∑ w ∈ observedFactors s n N, factorMultiplicity s n N w = N := by
  classical
  have h := Finset.card_eq_sum_card_image
    (fun i : Fin N => factorAt s n i) (Finset.univ : Finset (Fin N))
  simpa [observedFactors, factorMultiplicity, prefixFactorFiber] using h.symm

omit [Fintype α] [DecidableEq α] in
/-- Finite Cauchy--Schwarz: observed support size times collision energy
dominates the square of the number of sampled starts. -/
theorem square_le_observedFactorCount_mul_collisionEnergy
    (s : Stream α) (n N : ℕ) :
    N ^ 2 ≤ observedFactorCount s n N * collisionEnergy s n N := by
  classical
  have h := sq_sum_le_card_mul_sum_sq
    (s := observedFactors s n N) (f := factorMultiplicity s n N)
  rw [sum_factorMultiplicity_eq s n N] at h
  exact h

/-- Every factor observed in the finite sample belongs to T1's full factor
language, so finite-prefix support cannot exceed canonical complexity. -/
theorem observedFactorCount_le_canonicalFactorComplexity
    (s : Stream α) (n N : ℕ) :
    observedFactorCount s n N ≤ canonicalFactorComplexity s n := by
  classical
  calc
    observedFactorCount s n N = (observedFactors s n N).card := rfl
    _ ≤ (allFactors (canonicalComplexityData s) n).card :=
      Finset.card_le_card fun _w _hw => mem_allFactors (canonicalComplexityData s) n _
    _ = canonicalFactorComplexity s n := by
      rw [card_allFactors, canonical_factorComplexity]

/-- C1, the exact stronger sufficient sibling criterion from the agenda.

For every positive real `C`, eventually at every length `n` there is a
positive sample size `N` for which `N² > C * n * E(n,N)`, with all quantities
coerced to reals in the displayed inequality. This is not canonical A1. Its
specialization to the decimal digits of pi is an open, unproved hypothesis. -/
def CollisionEnergyC1 (s : Stream (Fin 10)) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 1 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → ∃ N : ℕ, 1 ≤ N ∧
      C * (n : ℝ) * (collisionEnergy s n N : ℝ) < (N : ℝ) ^ 2

/-- The stronger sibling C1 is sufficient for T1's exact canonical A1
predicate. This implication does not assert C1 for pi. -/
theorem collisionEnergyC1_implies_canonical_A1 (s : Stream (Fin 10))
    (hC1 : CollisionEnergyC1 s) : A1 s (canonicalComplexityData s) := by
  intro C hC
  obtain ⟨n₀, hn₀, hall⟩ := hC1 C hC
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn
  obtain ⟨N, hN, henergy⟩ := hall n hn
  have hcsNat := square_le_observedFactorCount_mul_collisionEnergy s n N
  have hcsReal :
      (N : ℝ) ^ 2 ≤
        (observedFactorCount s n N : ℝ) * (collisionEnergy s n N : ℝ) := by
    exact_mod_cast hcsNat
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hcountNonneg : 0 ≤ (observedFactorCount s n N : ℝ) := by positivity
  have hcollisionEnergyPos : 0 < (collisionEnergy s n N : ℝ) := by
    by_contra hnot
    have henergyNonpos : (collisionEnergy s n N : ℝ) ≤ 0 := le_of_not_gt hnot
    have hproductNonpos :
        (observedFactorCount s n N : ℝ) * (collisionEnergy s n N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcountNonneg henergyNonpos
    have hNsquarePos : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNReal
    linarith
  have hobservedNat := observedFactorCount_le_canonicalFactorComplexity s n N
  have hobservedRealCanonical :
      (observedFactorCount s n N : ℝ) ≤ (canonicalFactorComplexity s n : ℝ) := by
    exact_mod_cast hobservedNat
  have hobservedReal :
      (observedFactorCount s n N : ℝ) ≤
        (factorComplexity (canonicalComplexityData s) n : ℝ) := by
    simpa only [canonical_factorComplexity] using hobservedRealCanonical
  have hproduct :
      (observedFactorCount s n N : ℝ) * (collisionEnergy s n N : ℝ) ≤
        (factorComplexity (canonicalComplexityData s) n : ℝ) *
          (collisionEnergy s n N : ℝ) :=
    mul_le_mul_of_nonneg_right hobservedReal hcollisionEnergyPos.le
  have hscaled :
      (C * (n : ℝ)) * (collisionEnergy s n N : ℝ) <
        (factorComplexity (canonicalComplexityData s) n : ℝ) *
          (collisionEnergy s n N : ℝ) :=
    henergy.trans_le (hcsReal.trans hproduct)
  exact lt_of_mul_lt_mul_right hscaled hcollisionEnergyPos.le

/-- The same C1 hypothesis implies T3's canonical branching-Cesaro divergence
predicate by importing and applying T3's equivalence. -/
theorem collisionEnergyC1_implies_canonical_branchingCesaroDiverges
    (s : Stream (Fin 10)) (hC1 : CollisionEnergyC1 s) :
    BranchingCesaroDiverges (canonicalComplexityData s) := by
  exact (canonical_A1_iff_branchingCesaroDiverges s).mp
    (collisionEnergyC1_implies_canonical_A1 s hC1)

end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.collisionEnergy_eq_collisionPairCount
#print axioms DecimalFactorComplexity.square_le_observedFactorCount_mul_collisionEnergy
#print axioms DecimalFactorComplexity.observedFactorCount_le_canonicalFactorComplexity
#print axioms DecimalFactorComplexity.collisionEnergyC1_implies_canonical_A1
#print axioms DecimalFactorComplexity.collisionEnergyC1_implies_canonical_branchingCesaroDiverges
