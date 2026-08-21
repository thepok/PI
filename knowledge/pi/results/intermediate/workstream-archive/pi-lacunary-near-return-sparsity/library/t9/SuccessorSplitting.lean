import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# Successor splitting for finite pi-cylinder energy

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

All conclusions about pi below are conditional on explicit finite-prefix
splitting hypotheses. No splitting property of pi is asserted.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.FiniteCylinderEnergy

open DecimalFactorComplexity.NormalOrbitNearReturns

/-- Starts in parent cylinder `a` whose next digit is `d`. -/
def piSuccessorFiber (n N : ℕ) (a : Fin (10 ^ n)) (d : Fin 10) :
    Finset (Fin N) :=
  Finset.univ.filter fun i =>
    piCylinderCode n i = a ∧ piDecimalStream (i + n) = d

/-- Number of first-`N` starts in parent cylinder `a` with successor digit `d`. -/
def piSuccessorCount (n N : ℕ) (a : Fin (10 ^ n)) (d : Fin 10) : ℕ :=
  (piSuccessorFiber n N a d).card

/-- A parent has two distinct successor digits, each carrying at least an
`eta` fraction of its parent count. -/
def QuantitativelySplitParent (n N : ℕ) (eta : ℝ)
    (a : Fin (10 ^ n)) : Prop :=
  ∃ d e : Fin 10, d ≠ e ∧
    eta * (piCylinderFiber n N a).card ≤ piSuccessorCount n N a d ∧
    eta * (piCylinderFiber n N a).card ≤ piSuccessorCount n N a e

/-- The split parents carry at least a `mu` fraction of level-`n` collision
energy. This is a finite hypothesis, not an asserted property of pi. -/
noncomputable def QuantitativeSplittingLevel (n N : ℕ) (mu eta : ℝ) : Prop := by
  classical
  exact mu * piCylinderCollisionEnergy n N ≤
    ∑ a : Fin (10 ^ n),
      if QuantitativelySplitParent n N eta a then
        ((piCylinderFiber n N a).card : ℝ) ^ 2
      else 0

/-- Equality of successor factors is exactly equality of their parents and
their newly appended digits. -/
theorem factorAt_succ_eq_iff_parent_and_digit (n i j : ℕ) :
    factorAt piDecimalStream (n + 1) i = factorAt piDecimalStream (n + 1) j ↔
      factorAt piDecimalStream n i = factorAt piDecimalStream n j ∧
        piDecimalStream (i + n) = piDecimalStream (j + n) := by
  constructor
  · intro h
    constructor
    · rw [← initial_factorAt piDecimalStream n i,
        ← initial_factorAt piDecimalStream n j]
      exact congrArg (initialFactor piDecimalStream n) h
    · have hv := congrArg Subtype.val h
      simpa [factorAt, blockAt] using congrFun hv (Fin.last n)
  · rintro ⟨hparent, hdigit⟩
    apply Subtype.ext
    funext k
    refine Fin.lastCases ?_ (fun r => ?_) k
    · simpa [factorAt, blockAt] using hdigit
    · have hv := congrArg Subtype.val hparent
      simpa [factorAt, blockAt] using congrFun hv r

/-- Parent occupancy is the sum of its ten successor occupancies. -/
theorem piCylinderFiber_card_eq_sum_successorCount (n N : ℕ)
    (a : Fin (10 ^ n)) :
    (piCylinderFiber n N a).card =
      ∑ d : Fin 10, piSuccessorCount n N a d := by
  classical
  have hpartition :
      (piCylinderFiber n N a).card =
        ∑ d : Fin 10,
          ((piCylinderFiber n N a).filter fun i : Fin N =>
            piDecimalStream (i + n) = d).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := piCylinderFiber n N a) (t := (Finset.univ : Finset (Fin 10)))
      (f := fun i : Fin N => piDecimalStream (i + n)) (by simp)
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro d _hd
  change ((piCylinderFiber n N a).filter fun i : Fin N =>
      piDecimalStream (i + n) = d).card = (piSuccessorFiber n N a d).card
  apply congrArg Finset.card
  ext i
  simp [piSuccessorFiber, piCylinderFiber]

/-- Exact refinement: level-`n+1` energy is the sum of the squares of all
successor-extension counts at level `n`. -/
theorem piCylinderCollisionEnergy_succ_refinement (n N : ℕ) :
    piCylinderCollisionEnergy (n + 1) N =
      ∑ a : Fin (10 ^ n), ∑ d : Fin 10,
        piSuccessorCount n N a d ^ 2 := by
  classical
  rw [piCylinderCollisionEnergy_eq_equalPairs_card]
  let S := piCylinderEqualPairs (n + 1) N
  have hpartition : S.card =
      ∑ ad : Fin (10 ^ n) × Fin 10,
        (S.filter fun ij : Fin N × Fin N =>
          (piCylinderCode n ij.1, piDecimalStream (ij.1 + n)) = ad).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin (10 ^ n) × Fin 10)))
      (f := fun ij : Fin N × Fin N =>
        (piCylinderCode n ij.1, piDecimalStream (ij.1 + n))) (by simp)
  rw [hpartition, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro d _hd
  rw [pow_two]
  change (S.filter fun ij : Fin N × Fin N =>
      (piCylinderCode n ij.1, piDecimalStream (ij.1 + n)) = (a, d)).card =
    (piSuccessorFiber n N a d).card * (piSuccessorFiber n N a d).card
  rw [← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [S, piCylinderEqualPairs, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.mk.injEq, Finset.mem_product]
  constructor
  · rintro ⟨hlongCode, hparent, hdigit⟩
    have hlongFactor :=
      (piCylinderCode_eq_iff_factorAt_eq (n + 1) ij.1 ij.2).mp hlongCode
    obtain ⟨hshortFactor, hnext⟩ :=
      (factorAt_succ_eq_iff_parent_and_digit n ij.1 ij.2).mp hlongFactor
    have hshortCode :=
      (piCylinderCode_eq_iff_factorAt_eq n ij.1 ij.2).mpr hshortFactor
    constructor
    · simp [piSuccessorFiber, hparent, hdigit]
    · simp [piSuccessorFiber, ← hshortCode, ← hnext, hparent, hdigit]
  · rintro ⟨hi, hj⟩
    simp only [piSuccessorFiber, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hj
    obtain ⟨hiCode, hiDigit⟩ := hi
    obtain ⟨hjCode, hjDigit⟩ := hj
    have hshortFactor : factorAt piDecimalStream n ij.1 =
        factorAt piDecimalStream n ij.2 :=
      (piCylinderCode_eq_iff_factorAt_eq n ij.1 ij.2).mp
        (hiCode.trans hjCode.symm)
    have hlongFactor : factorAt piDecimalStream (n + 1) ij.1 =
        factorAt piDecimalStream (n + 1) ij.2 :=
      (factorAt_succ_eq_iff_parent_and_digit n ij.1 ij.2).mpr
        ⟨hshortFactor, hiDigit.trans hjDigit.symm⟩
    exact ⟨(piCylinderCode_eq_iff_factorAt_eq (n + 1) ij.1 ij.2).mpr
      hlongFactor, hiCode, hiDigit⟩

/-- A nonnegative finite family with two entries of mass at least `eta * m`
has squared energy at most `(1 - eta) * m^2`. -/
theorem sum_sq_le_one_sub_mul_sq_of_two_large
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (eta m : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = m)
    (hlarge : ∃ d e : ι, d ≠ e ∧ eta * m ≤ x d ∧ eta * m ≤ x e) :
    ∑ i, x i ^ 2 ≤ (1 - eta) * m ^ 2 := by
  obtain ⟨d, e, hde, hd, he⟩ := hlarge
  have hupper : ∀ k, x k ≤ (1 - eta) * m := by
    intro k
    obtain ⟨q, hqk, hq⟩ : ∃ q, q ≠ k ∧ eta * m ≤ x q := by
      by_cases hkd : k = d
      · exact ⟨e, by simpa [hkd] using hde.symm, he⟩
      · exact ⟨d, by exact fun h => hkd h.symm, hd⟩
    have hpair : x k + x q ≤ ∑ z, x z := by
      calc
        x k + x q = ∑ z ∈ ({k, q} : Finset ι), x z := by
          rw [Finset.sum_insert (by simpa using hqk.symm), Finset.sum_singleton]
        _ ≤ ∑ z ∈ (Finset.univ : Finset ι), x z :=
          Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun z _hz _ => hx z)
        _ = ∑ z, x z := rfl
    rw [hsum] at hpair
    linarith
  calc
    ∑ i, x i ^ 2 ≤ ∑ i, ((1 - eta) * m) * x i := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa [pow_two] using mul_le_mul_of_nonneg_right (hupper i) (hx i)
    _ = ((1 - eta) * m) * ∑ i, x i := by rw [Finset.mul_sum]
    _ = (1 - eta) * m ^ 2 := by rw [hsum]; ring

/-- A split parent loses the explicit fraction `eta` of its own squared
collision mass under one refinement. -/
theorem splitParent_successor_energy_le (n N : ℕ) (eta : ℝ)
    (a : Fin (10 ^ n)) (hsplit : QuantitativelySplitParent n N eta a) :
    (∑ d : Fin 10, (piSuccessorCount n N a d : ℝ) ^ 2) ≤
      (1 - eta) * ((piCylinderFiber n N a).card : ℝ) ^ 2 := by
  apply sum_sq_le_one_sub_mul_sq_of_two_large
      (x := fun d : Fin 10 => (piSuccessorCount n N a d : ℝ))
  · intro d
    positivity
  · exact_mod_cast (piCylinderFiber_card_eq_sum_successorCount n N a).symm
  · simpa only [QuantitativelySplitParent, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_ofNat] using hsplit

/-- Refinement never increases finite-prefix collision energy. -/
theorem piCylinderCollisionEnergy_succ_le (n N : ℕ) :
    piCylinderCollisionEnergy (n + 1) N ≤ piCylinderCollisionEnergy n N := by
  rw [piCylinderCollisionEnergy_succ_refinement, piCylinderCollisionEnergy]
  apply Finset.sum_le_sum
  intro a _ha
  exact_mod_cast sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin 10)))
    (f := fun d => (piSuccessorCount n N a d : ℕ)) (by omega)
    |>.trans_eq (by rw [piCylinderFiber_card_eq_sum_successorCount])

/-- A quantitative splitting level gives the explicit multiplicative
decrement `1 - mu * eta` for T7's finite-prefix energy. -/
theorem quantitativeSplittingLevel_energy_decrement
    (n N : ℕ) (mu eta : ℝ) (_hmu : 0 < mu) (heta : 0 < eta)
    (_hproduct : mu * eta ≤ 1)
    (hsplit : QuantitativeSplittingLevel n N mu eta) :
    (piCylinderCollisionEnergy (n + 1) N : ℝ) ≤
      (1 - mu * eta) * piCylinderCollisionEnergy n N := by
  classical
  let parentMass : Fin (10 ^ n) → ℝ := fun a =>
    ((piCylinderFiber n N a).card : ℝ) ^ 2
  let splitMass : Fin (10 ^ n) → ℝ := fun a =>
    if QuantitativelySplitParent n N eta a then parentMass a else 0
  let childMass : Fin (10 ^ n) → ℝ := fun a =>
    ∑ d : Fin 10, (piSuccessorCount n N a d : ℝ) ^ 2
  have hrefine : (piCylinderCollisionEnergy (n + 1) N : ℝ) =
      ∑ a, childMass a := by
    dsimp only [childMass]
    exact_mod_cast piCylinderCollisionEnergy_succ_refinement n N
  have hparent : (piCylinderCollisionEnergy n N : ℝ) =
      ∑ a, parentMass a := by
    simp [piCylinderCollisionEnergy, parentMass]
  have hsplit' : mu * (piCylinderCollisionEnergy n N : ℝ) ≤
      ∑ a, splitMass a := by
    simpa only [QuantitativeSplittingLevel, splitMass, parentMass] using hsplit
  have hpoint : ∀ a, childMass a ≤ parentMass a - eta * splitMass a := by
    intro a
    by_cases ha : QuantitativelySplitParent n N eta a
    · have h := splitParent_successor_energy_le n N eta a ha
      dsimp only [childMass, parentMass, splitMass]
      simp only [ha, if_true]
      exact h.trans_eq (by ring)
    · have hsum : ∑ d : Fin 10, (piSuccessorCount n N a d : ℝ) =
          ((piCylinderFiber n N a).card : ℝ) := by
        exact_mod_cast (piCylinderFiber_card_eq_sum_successorCount n N a).symm
      have hbase : (∑ d : Fin 10, (piSuccessorCount n N a d : ℝ) ^ 2) ≤
          ((piCylinderFiber n N a).card : ℝ) ^ 2 :=
        (sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin 10)))
          (f := fun d => (piSuccessorCount n N a d : ℝ))
          (fun _ _ => by positivity)).trans_eq (by rw [hsum])
      dsimp only [childMass, parentMass, splitMass]
      simpa only [ha, if_false, mul_zero, sub_zero] using hbase
  calc
    (piCylinderCollisionEnergy (n + 1) N : ℝ) = ∑ a, childMass a := hrefine
    _ ≤ ∑ a, (parentMass a - eta * splitMass a) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = (∑ a, parentMass a) - eta * ∑ a, splitMass a := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (piCylinderCollisionEnergy n N : ℝ) - eta * ∑ a, splitMass a := by
      rw [← hparent]
    _ ≤ (piCylinderCollisionEnergy n N : ℝ) -
        eta * (mu * piCylinderCollisionEnergy n N) := by
      gcongr
    _ = (1 - mu * eta) * piCylinderCollisionEnergy n N := by ring

/-- Splitting levels among `0, ..., n-1` for the fixed finite prefix `N`. -/
noncomputable def piSplittingLevels (n N : ℕ) (mu eta : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun k => QuantitativeSplittingLevel k N mu eta

/-- Number of quantitative splitting levels below `n`. -/
noncomputable def piSplittingLevelCount (n N : ℕ) (mu eta : ℝ) : ℕ :=
  (piSplittingLevels n N mu eta).card

theorem piSplittingLevelCount_succ_of_splitting
    (n N : ℕ) (mu eta : ℝ) (hs : QuantitativeSplittingLevel n N mu eta) :
    piSplittingLevelCount (n + 1) N mu eta =
      piSplittingLevelCount n N mu eta + 1 := by
  classical
  have hlevels : piSplittingLevels (n + 1) N mu eta =
      insert n (piSplittingLevels n N mu eta) := by
    ext k
    by_cases hkn : k = n
    · subst k
      simp [piSplittingLevels, hs]
    · simp [piSplittingLevels, hkn]
      omega
  have hn : n ∉ piSplittingLevels n N mu eta := by
    simp [piSplittingLevels]
  rw [piSplittingLevelCount, hlevels, piSplittingLevelCount]
  simp [hn, Nat.add_comm]

theorem piSplittingLevelCount_succ_of_not_splitting
    (n N : ℕ) (mu eta : ℝ) (hs : ¬ QuantitativeSplittingLevel n N mu eta) :
    piSplittingLevelCount (n + 1) N mu eta =
      piSplittingLevelCount n N mu eta := by
  classical
  apply congrArg Finset.card
  ext k
  by_cases hkn : k = n
  · subst k
    simp [piSplittingLevels, hs]
  · simp [piSplittingLevels]
    omega

/-- At level zero all starts have the unique empty cylinder code. -/
theorem piCylinderCollisionEnergy_zero (N : ℕ) :
    piCylinderCollisionEnergy 0 N = N ^ 2 := by
  simp [piCylinderCollisionEnergy, piCylinderFiber, piCylinderCode,
    prefixLabel, prefixWord, Theory.PiDigits.T20.wordValue]

/-- Iterating splitting and ordinary refinement gives a power of the explicit
decrement factor. The exponent counts exactly the splitting levels below `n`. -/
theorem energy_le_decrement_pow_splittingLevelCount
    (n N : ℕ) (mu eta : ℝ)
    (hmu : 0 < mu) (heta : 0 < eta) (hproduct : mu * eta ≤ 1) :
    (piCylinderCollisionEnergy n N : ℝ) ≤
      (1 - mu * eta) ^ piSplittingLevelCount n N mu eta * (N : ℝ) ^ 2 := by
  induction n with
  | zero =>
      simp [piSplittingLevelCount, piSplittingLevels,
        piCylinderCollisionEnergy_zero]
  | succ n ih =>
      have hrho : 0 ≤ 1 - mu * eta := sub_nonneg.mpr hproduct
      by_cases hs : QuantitativeSplittingLevel n N mu eta
      · have hdec := quantitativeSplittingLevel_energy_decrement
          n N mu eta hmu heta hproduct hs
        have hcount : piSplittingLevelCount (n + 1) N mu eta =
            piSplittingLevelCount n N mu eta + 1 :=
          piSplittingLevelCount_succ_of_splitting n N mu eta hs
        calc
          (piCylinderCollisionEnergy (n + 1) N : ℝ) ≤
              (1 - mu * eta) * piCylinderCollisionEnergy n N := hdec
          _ ≤ (1 - mu * eta) *
              ((1 - mu * eta) ^ piSplittingLevelCount n N mu eta *
                (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left ih hrho
          _ = (1 - mu * eta) ^
              piSplittingLevelCount (n + 1) N mu eta * (N : ℝ) ^ 2 := by
            rw [hcount, pow_succ]
            ring
      · have hmono : (piCylinderCollisionEnergy (n + 1) N : ℝ) ≤
            piCylinderCollisionEnergy n N := by
          exact_mod_cast piCylinderCollisionEnergy_succ_le n N
        have hcount : piSplittingLevelCount (n + 1) N mu eta =
            piSplittingLevelCount n N mu eta :=
          piSplittingLevelCount_succ_of_not_splitting n N mu eta hs
        rw [hcount]
        exact hmono.trans ih

/-- Explicit finite hypothesis saying there are enough splitting levels for
the power decrement to beat every canonical factor `A*n`. -/
def PiSufficientSplitting (mu eta : ℝ) : Prop :=
  0 < mu ∧ 0 < eta ∧ mu * eta ≤ 1 ∧
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        ((A * n : ℕ) : ℝ) *
          (1 - mu * eta) ^ piSplittingLevelCount n N mu eta ≤ 1

/-- Sufficiently many quantitative splitting levels imply literal canonical
C1. This theorem is conditional and does not assert its premise for pi. -/
theorem piSufficientSplitting_implies_canonical_C1
    (mu eta : ℝ) (hsplit : PiSufficientSplitting mu eta) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2 := by
  obtain ⟨hmu, heta, hproduct, hlevels⟩ := hsplit
  apply canonical_C1_iff_piFiniteCylinderEnergyFrontier.mpr
  intro A hA
  obtain ⟨n0, hn0, hall⟩ := hlevels A hA
  refine ⟨n0, hn0, ?_⟩
  intro n hn
  obtain ⟨N, hN, hpower⟩ := hall n hn
  refine ⟨N, hN, ?_⟩
  have henergy := energy_le_decrement_pow_splittingLevelCount
    n N mu eta hmu heta hproduct
  have hreal : ((A * n * piCylinderCollisionEnergy n N : ℕ) : ℝ) ≤
      ((N ^ 2 : ℕ) : ℝ) := by
    calc
      ((A * n * piCylinderCollisionEnergy n N : ℕ) : ℝ) =
          ((A * n : ℕ) : ℝ) * (piCylinderCollisionEnergy n N : ℝ) := by
            push_cast
            ring
      _ ≤ ((A * n : ℕ) : ℝ) *
          ((1 - mu * eta) ^ piSplittingLevelCount n N mu eta *
            (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = (((A * n : ℕ) : ℝ) *
          (1 - mu * eta) ^ piSplittingLevelCount n N mu eta) *
            (N : ℝ) ^ 2 := by ring
      _ ≤ 1 * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hpower (sq_nonneg (N : ℝ))
      _ = ((N ^ 2 : ℕ) : ℝ) := by norm_num
  exact_mod_cast hreal

/-- A parent has a successor carrying the explicit fraction `1 - 9*eta` of
its count. The coefficient nine is the number of other decimal digits. -/
def HasDominantSuccessor (n N : ℕ) (eta : ℝ) (a : Fin (10 ^ n)) : Prop :=
  ∃ d : Fin 10,
    (1 - 9 * eta) * (piCylinderFiber n N a).card ≤
      piSuccessorCount n N a d

/-- Every parent which is not quantitatively split has a dominant successor
when `eta ≤ 1/10`. This is the local rigidity alternative behind the inverse
theorem. -/
theorem not_splitParent_hasDominantSuccessor
    (n N : ℕ) (eta : ℝ) (a : Fin (10 ^ n))
    (_hetaPos : 0 < eta) (heta : eta ≤ 1 / 10)
    (hnot : ¬ QuantitativelySplitParent n N eta a) :
    HasDominantSuccessor n N eta a := by
  classical
  have htotal :
      ∑ e : Fin 10, (piSuccessorCount n N a e : ℝ) =
        ((piCylinderFiber n N a).card : ℝ) := by
    exact_mod_cast (piCylinderFiber_card_eq_sum_successorCount n N a).symm
  have hlarge : ∃ d : Fin 10,
      eta * (piCylinderFiber n N a).card ≤ piSuccessorCount n N a d := by
    by_contra hnone
    push Not at hnone
    have hlt :
        (∑ d : Fin 10, (piSuccessorCount n N a d : ℝ)) <
          ∑ _d : Fin 10, eta * (piCylinderFiber n N a).card := by
      exact Finset.sum_lt_sum_of_nonempty (by simp) fun d _ => hnone d
    rw [htotal] at hlt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hlt
    have hm : 0 ≤ ((piCylinderFiber n N a).card : ℝ) := by positivity
    norm_num at heta hlt
    nlinarith
  obtain ⟨d, hd⟩ := hlarge
  refine ⟨d, ?_⟩
  have hother : ∀ e ∈ (Finset.univ : Finset (Fin 10)).erase d,
      (piSuccessorCount n N a e : ℝ) ≤
        eta * (piCylinderFiber n N a).card := by
    intro e he
    have hed : e ≠ d := (Finset.mem_erase.mp he).1
    by_contra hlarge
    have heLarge : eta * (piCylinderFiber n N a).card <
        piSuccessorCount n N a e := lt_of_not_ge hlarge
    apply hnot
    refine ⟨d, e, hed.symm, ?_, heLarge.le⟩
    exact hd
  have hothers :
      ∑ e ∈ (Finset.univ : Finset (Fin 10)).erase d,
          (piSuccessorCount n N a e : ℝ) ≤
        9 * (eta * (piCylinderFiber n N a).card) := by
    calc
      ∑ e ∈ (Finset.univ : Finset (Fin 10)).erase d,
          (piSuccessorCount n N a e : ℝ) ≤
          ∑ _e ∈ (Finset.univ : Finset (Fin 10)).erase d,
            eta * (piCylinderFiber n N a).card :=
        Finset.sum_le_sum hother
      _ = 9 * (eta * (piCylinderFiber n N a).card) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ d)]
        norm_num
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin 10))
    (fun e => (piSuccessorCount n N a e : ℝ)) (Finset.mem_univ d)
  rw [htotal] at herase
  nlinarith

/-- Collision energy carried by parents with a dominant successor. -/
noncomputable def piDominantSuccessorEnergy
    (n N : ℕ) (eta : ℝ) : ℝ := by
  classical
  exact ∑ a : Fin (10 ^ n),
    if HasDominantSuccessor n N eta a then
      ((piCylinderFiber n N a).card : ℝ) ^ 2
    else 0

/-- If level `n` fails the weighted splitting condition, more than a
`1-mu` fraction of its collision energy lies on dominant-successor parents. -/
theorem not_splittingLevel_dominant_energy_concentration
    (n N : ℕ) (mu eta : ℝ)
    (_hmu : 0 < mu) (_hmuUpper : mu < 1)
    (hetaPos : 0 < eta) (heta : eta ≤ 1 / 10)
    (hnot : ¬ QuantitativeSplittingLevel n N mu eta) :
    (1 - mu) * piCylinderCollisionEnergy n N <
      piDominantSuccessorEnergy n N eta := by
  classical
  let parentMass : Fin (10 ^ n) → ℝ := fun a =>
    ((piCylinderFiber n N a).card : ℝ) ^ 2
  let splitMass : Fin (10 ^ n) → ℝ := fun a =>
    if QuantitativelySplitParent n N eta a then parentMass a else 0
  let dominantMass : Fin (10 ^ n) → ℝ := fun a =>
    if HasDominantSuccessor n N eta a then parentMass a else 0
  have hsplitlt : (∑ a, splitMass a) <
      mu * (piCylinderCollisionEnergy n N : ℝ) := by
    apply lt_of_not_ge
    intro hge
    apply hnot
    simpa only [QuantitativeSplittingLevel, splitMass, parentMass] using hge
  have hpoint : ∀ a, parentMass a ≤ splitMass a + dominantMass a := by
    intro a
    by_cases hs : QuantitativelySplitParent n N eta a
    · have hdominantNonneg : 0 ≤ dominantMass a := by
        dsimp only [dominantMass]
        split_ifs
        · positivity
        · exact le_rfl
      dsimp only [splitMass]
      rw [if_pos hs]
      exact le_add_of_nonneg_right hdominantNonneg
    · have hd := not_splitParent_hasDominantSuccessor n N eta a hetaPos heta hs
      simp [splitMass, dominantMass, hs, hd, parentMass]
  have htotal : (piCylinderCollisionEnergy n N : ℝ) ≤
      (∑ a, splitMass a) + ∑ a, dominantMass a := by
    rw [piCylinderCollisionEnergy]
    push_cast
    calc
      ∑ a : Fin (10 ^ n), ((piCylinderFiber n N a).card : ℝ) ^ 2 ≤
          ∑ a, (splitMass a + dominantMass a) :=
        Finset.sum_le_sum fun a _ => hpoint a
      _ = (∑ a, splitMass a) + ∑ a, dominantMass a :=
        Finset.sum_add_distrib
  change (1 - mu) * (piCylinderCollisionEnergy n N : ℝ) <
    piDominantSuccessorEnergy n N eta
  have hdominant : piDominantSuccessorEnergy n N eta =
      ∑ a, dominantMass a := by
    simp [piDominantSuccessorEnergy, dominantMass, parentMass]
  rw [hdominant]
  nlinarith

/-- Literal failure of canonical C1 yields arbitrarily large bad scales. At
each such scale every finite prefix has fewer than `K` splitting levels as
soon as the explicit power threshold at `K` would force C1. Thus the splitting
count is logarithmic in the precise power-threshold sense. Every nonsplitting
level also has the dominant-successor energy concentration above.

The premise repeats all canonical quantifiers and no failure is asserted for
pi. -/
theorem not_canonical_C1_implies_logarithmic_splitting_and_dominance
    (mu eta : ℝ) (hmu : 0 < mu) (hmuUpper : mu < 1) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 10) (hproduct : mu * eta ≤ 1)
    (hnot : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧
        ∀ N : ℕ, 1 ≤ N →
          N ^ 2 < A * n * piCylinderCollisionEnergy n N ∧
          (∀ K : ℕ,
            ((A * n : ℕ) : ℝ) * (1 - mu * eta) ^ K ≤ 1 →
              piSplittingLevelCount n N mu eta < K) ∧
          ∀ k ∈ Finset.range n,
            ¬ QuantitativeSplittingLevel k N mu eta →
              (1 - mu) * piCylinderCollisionEnergy k N <
                piDominantSuccessorEnergy k N eta := by
  have hnotEnergy : ¬ PiFiniteCylinderEnergyFrontier := by
    intro henergy
    exact hnot (canonical_C1_iff_piFiniteCylinderEnergyFrontier.mpr henergy)
  unfold PiFiniteCylinderEnergyFrontier at hnotEnergy
  push Not at hnotEnergy
  obtain ⟨A, hA, hbad⟩ := hnotEnergy
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hbadN⟩ := hbad n0 hn0
  have hn : 1 ≤ n := hn0.trans hn0n
  refine ⟨n, hn0n, hn, ?_⟩
  intro N hN
  have hbadHere := hbadN N hN
  refine ⟨hbadHere, ?_, ?_⟩
  · intro K hthreshold
    by_contra hcount
    have hKcount : K ≤ piSplittingLevelCount n N mu eta :=
      Nat.le_of_not_gt hcount
    have hrho0 : 0 ≤ 1 - mu * eta := sub_nonneg.mpr hproduct
    have hrho1 : 1 - mu * eta ≤ 1 := by
      have : 0 ≤ mu * eta := mul_nonneg hmu.le heta.le
      linarith
    have hpow : (1 - mu * eta) ^ piSplittingLevelCount n N mu eta ≤
        (1 - mu * eta) ^ K :=
      pow_le_pow_of_le_one hrho0 hrho1 hKcount
    have henergy := energy_le_decrement_pow_splittingLevelCount
      n N mu eta hmu heta hproduct
    have hscale : 0 ≤ ((A * n : ℕ) : ℝ) := by positivity
    have hforced :
        ((A * n * piCylinderCollisionEnergy n N : ℕ) : ℝ) ≤
          ((N ^ 2 : ℕ) : ℝ) := by
      calc
        ((A * n * piCylinderCollisionEnergy n N : ℕ) : ℝ) =
            ((A * n : ℕ) : ℝ) * (piCylinderCollisionEnergy n N : ℝ) := by
              push_cast
              ring
        _ ≤ ((A * n : ℕ) : ℝ) *
            ((1 - mu * eta) ^ piSplittingLevelCount n N mu eta *
              (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left henergy hscale
        _ ≤ ((A * n : ℕ) : ℝ) *
            ((1 - mu * eta) ^ K * (N : ℝ) ^ 2) := by
              gcongr
        _ = (((A * n : ℕ) : ℝ) * (1 - mu * eta) ^ K) *
            (N : ℝ) ^ 2 := by ring
        _ ≤ 1 * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hthreshold (sq_nonneg (N : ℝ))
        _ = ((N ^ 2 : ℕ) : ℝ) := by norm_num
    have hforcedNat : A * n * piCylinderCollisionEnergy n N ≤ N ^ 2 := by
      exact_mod_cast hforced
    omega
  · intro k _hk hnotSplit
    exact not_splittingLevel_dominant_energy_concentration
      k N mu eta hmu hmuUpper heta hetaUpper hnotSplit

end DecimalFactorComplexity.FiniteCylinderEnergy

#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderFiber_card_eq_sum_successorCount
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCollisionEnergy_succ_refinement
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.splitParent_successor_energy_le
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.quantitativeSplittingLevel_energy_decrement
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.energy_le_decrement_pow_splittingLevelCount
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.piSufficientSplitting_implies_canonical_C1
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.not_splitParent_hasDominantSuccessor
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.not_splittingLevel_dominant_energy_concentration
#print axioms DecimalFactorComplexity.FiniteCylinderEnergy.not_canonical_C1_implies_logarithmic_splitting_and_dominance
