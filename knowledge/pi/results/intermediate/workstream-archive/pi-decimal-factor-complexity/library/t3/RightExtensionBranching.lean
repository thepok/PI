import TheoryLib.PiDecimalFactorComplexity.T1DecimalFactorComplexity

/-!
# Right-extension branching and factor complexity

Source: `problems/local/pi-decimal-factor-complexity.txt`
SHA-256: `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

This file imports T1 and gives an equivalent structural reduction of its exact
canonical A1 predicate. Factors remain T1's contiguous blocks beginning at
arbitrary stream positions. A right extension is an occurring length-`n+1`
factor with the prescribed length-`n` initial factor.

No theorem below proves superlinear factor complexity for the decimal digits
of pi, or any other pi-specific growth claim.
-/

namespace DecimalFactorComplexity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite set of all occurring factors, enumerated through T1's exact
finite presentation. -/
noncomputable def allFactors {s : Stream α} (P : ComplexityData s) (n : ℕ) :
    Finset (Factor s n) := by
  classical
  exact (Finset.univ : Finset (Fin (P.value n))).image (P.classify n).symm

omit [Fintype α] [DecidableEq α] in
@[simp] lemma mem_allFactors {s : Stream α} (P : ComplexityData s) (n : ℕ)
    (w : Factor s n) : w ∈ allFactors P n := by
  classical
  rw [allFactors, Finset.mem_image]
  exact ⟨P.classify n w, Finset.mem_univ _, by simp⟩

omit [Fintype α] [DecidableEq α] in
@[simp] lemma card_allFactors {s : Stream α} (P : ComplexityData s) (n : ℕ) :
    (allFactors P n).card = factorComplexity P n := by
  classical
  rw [allFactors, Finset.card_image_of_injective _ (P.classify n).symm.injective]
  simp [factorComplexity]

/-- All occurring one-symbol right extensions of `w`. The elements are
length-`n+1` factors, so different elements differ in their appended symbol. -/
noncomputable def rightExtensions {s : Stream α} (P : ComplexityData s) (n : ℕ)
    (w : Factor s n) : Finset (Factor s (n + 1)) := by
  classical
  exact (allFactors P (n + 1)).filter fun v => initialFactor s n v = w

@[simp] lemma mem_rightExtensions_iff {s : Stream α} (P : ComplexityData s) (n : ℕ)
    (w : Factor s n) (v : Factor s (n + 1)) :
    v ∈ rightExtensions P n w ↔ initialFactor s n v = w := by
  classical
  simp [rightExtensions]

lemma extendFactor_mem_rightExtensions {s : Stream α} (P : ComplexityData s) (n : ℕ)
    (w : Factor s n) : extendFactor s n w ∈ rightExtensions P n w := by
  rw [mem_rightExtensions_iff]
  exact initial_extendFactor s n w

lemma rightExtensions_card_pos {s : Stream α} (P : ComplexityData s) (n : ℕ)
    (w : Factor s n) : 0 < (rightExtensions P n w).card := by
  exact Finset.card_pos.mpr ⟨extendFactor s n w, extendFactor_mem_rightExtensions P n w⟩

/-- Total right-branching excess at length `n`. -/
noncomputable def branchingExcess {s : Stream α} (P : ComplexityData s) (n : ℕ) : ℕ :=
  (allFactors P n).sum fun w => (rightExtensions P n w).card - 1

/-- Length-`n+1` factors partition exactly into the right-extension fibers of
the length-`n` factors. -/
lemma factorComplexity_succ_eq_sum_rightExtensions {s : Stream α}
    (P : ComplexityData s) (n : ℕ) :
    factorComplexity P (n + 1) =
      ∑ w ∈ allFactors P n, (rightExtensions P n w).card := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := allFactors P (n + 1)) (t := allFactors P n)
    (f := initialFactor s n) (fun _ _ => mem_allFactors P n _)
  simpa [rightExtensions] using hpartition

/-- The exact right-extension identity
`p(n+1) - p(n) = sum_w (#R(w) - 1)`. -/
theorem factorComplexity_succ_sub_eq_branchingExcess {s : Stream α}
    (P : ComplexityData s) (n : ℕ) :
    factorComplexity P (n + 1) - factorComplexity P n = branchingExcess P n := by
  classical
  symm
  calc
    branchingExcess P n =
        (∑ w ∈ allFactors P n, (rightExtensions P n w).card) -
          ∑ _w ∈ allFactors P n, 1 := by
      rw [branchingExcess]
      exact Finset.sum_tsub_distrib (allFactors P n)
        (f := fun w => (rightExtensions P n w).card) (g := fun _ => 1)
        fun w _ => rightExtensions_card_pos P n w
    _ = factorComplexity P (n + 1) - factorComplexity P n := by
      rw [← factorComplexity_succ_eq_sum_rightExtensions P n]
      simp

/-- The right-extension identity with the sum displayed explicitly. -/
theorem factorComplexity_right_extension_identity {s : Stream α}
    (P : ComplexityData s) (n : ℕ) :
    factorComplexity P (n + 1) - factorComplexity P n =
      (allFactors P n).sum fun w => (rightExtensions P n w).card - 1 := by
  exact factorComplexity_succ_sub_eq_branchingExcess P n

/-- The identity stated directly for T1's canonical factor cardinality. -/
theorem canonicalFactorComplexity_succ_sub_eq_branchingExcess (s : Stream α) (n : ℕ) :
    canonicalFactorComplexity s (n + 1) - canonicalFactorComplexity s n =
      branchingExcess (canonicalComplexityData s) n := by
  simpa only [canonical_factorComplexity] using
    factorComplexity_succ_sub_eq_branchingExcess (canonicalComplexityData s) n

/-- The canonical right-extension identity with the sum displayed explicitly. -/
theorem canonicalFactorComplexity_right_extension_identity (s : Stream α) (n : ℕ) :
    canonicalFactorComplexity s (n + 1) - canonicalFactorComplexity s n =
      (allFactors (canonicalComplexityData s) n).sum fun w =>
        (rightExtensions (canonicalComplexityData s) n w).card - 1 := by
  exact canonicalFactorComplexity_succ_sub_eq_branchingExcess s n

lemma factorComplexity_one_le {s : Stream α} (P : ComplexityData s) (n : ℕ) :
    1 ≤ factorComplexity P n := by
  have hmono : Monotone (factorComplexity P) :=
    monotone_nat_of_le_succ (factorComplexity_mono s P)
  have h := hmono (Nat.zero_le n)
  simpa [factorComplexity_zero s P] using h

/-- The cumulative branching excess telescopes to `p(n) - 1`. -/
theorem sum_branchingExcess_eq {s : Stream α} (P : ComplexityData s) (n : ℕ) :
    (Finset.range n).sum (branchingExcess P) = factorComplexity P n - 1 := by
  calc
    (Finset.range n).sum (branchingExcess P) =
        (Finset.range n).sum
          (fun k => factorComplexity P (k + 1) - factorComplexity P k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (factorComplexity_succ_sub_eq_branchingExcess P k).symm
    _ = factorComplexity P n - factorComplexity P 0 := by
      exact Finset.sum_range_tsub
        (monotone_nat_of_le_succ (factorComplexity_mono s P)) n
    _ = factorComplexity P n - 1 := by rw [factorComplexity_zero s P]

/-- The Cesaro average through lengths `0, ..., n-1`; it is used only at
positive `n` in `BranchingCesaroDiverges`. -/
noncomputable def cesaroBranchingAverage {s : Stream α} (P : ComplexityData s)
    (n : ℕ) : ℝ :=
  ((Finset.range n).sum (branchingExcess P) : ℕ) / (n : ℝ)

lemma cesaroBranchingAverage_eq {s : Stream α} (P : ComplexityData s) (n : ℕ) :
    cesaroBranchingAverage P n = ((factorComplexity P n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  rw [cesaroBranchingAverage, sum_branchingExcess_eq P n]

/-- Exact quantified divergence to `+∞` of the Cesaro branching averages. -/
def BranchingCesaroDiverges {s : Stream α} (P : ComplexityData s) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → C < cesaroBranchingAverage P n

/-- T1's exact A1 predicate is equivalent to divergence of average
right-extension branching. This is a structural reduction, not a growth
theorem for any particular stream. -/
theorem A1_iff_branchingCesaroDiverges {s : Stream α} (P : ComplexityData s) :
    A1 s P ↔ BranchingCesaroDiverges P := by
  constructor
  · intro hA C hC
    obtain ⟨N, hNpos, hN⟩ := hA (C + 1) (by linarith)
    refine ⟨N, hNpos, ?_⟩
    intro n hn
    have hnNat : 1 ≤ n := hNpos.trans hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnNat)
    have hp := hN n hn
    rw [cesaroBranchingAverage_eq]
    apply (lt_div_iff₀ hnReal).2
    rw [Nat.cast_sub (factorComplexity_one_le P n)]
    norm_num
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
    nlinarith
  · intro hB C hC
    obtain ⟨N, hNpos, hN⟩ := hB C hC
    refine ⟨N, hNpos, ?_⟩
    intro n hn
    have hnNat : 1 ≤ n := hNpos.trans hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnNat)
    have havg := hN n hn
    rw [cesaroBranchingAverage_eq] at havg
    have hmul := (lt_div_iff₀ hnReal).mp havg
    rw [Nat.cast_sub (factorComplexity_one_le P n)] at hmul
    norm_num at hmul
    nlinarith

/-- Canonical specialization using exactly T1's canonical complexity data. -/
theorem canonical_A1_iff_branchingCesaroDiverges (s : Stream α) :
    A1 s (canonicalComplexityData s) ↔
      BranchingCesaroDiverges (canonicalComplexityData s) := by
  exact A1_iff_branchingCesaroDiverges (canonicalComplexityData s)

/-- Decimal specialization. It applies to any decimal stream and makes no
claim that the decimal stream of pi satisfies either equivalent predicate. -/
theorem decimal_canonical_A1_iff_branchingCesaroDiverges (s : Stream (Fin 10)) :
    A1 s (canonicalComplexityData s) ↔
      BranchingCesaroDiverges (canonicalComplexityData s) := by
  exact canonical_A1_iff_branchingCesaroDiverges s

end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.canonicalFactorComplexity_right_extension_identity
#print axioms DecimalFactorComplexity.canonical_A1_iff_branchingCesaroDiverges
#print axioms DecimalFactorComplexity.decimal_canonical_A1_iff_branchingCesaroDiverges
