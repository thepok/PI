import TheoryLib.PiLacunaryNearReturnSparsity.T100T100UniversalCharging

/-!
# T166: power-free finite-word separation and collision packing

This module proves a substitution-independent finite-word sibling theorem for
the canonical fixed-pi near-return question. It makes no assertion about
`Real.pi`, A1, C1, C2, or any substitution fixed point.

Canonical statement: `problems/local/pi-lacunary-near-return-sparsity.txt`
Canonical SHA-256:
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
Original source URL: none; the canonical file records a local formulation on
2026-07-22. This result is an A13/A14 finite-word sibling, not a result about
the canonical fixed-pi metric count.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiLacunaryNearReturnSparsity.T166

variable {α : Type*}

/-- Number of legal length-`m` factor starts in a word of length `L`.
The starts are `0, ..., L - m` when `m ≤ L`, and there are none when `m > L`.
-/
def legalStartCount (L m : ℕ) : ℕ := L + 1 - m

/-- The length-`m` factor at a legal start. The endpoint convention is
inclusive: start `L-m` reads the final coordinate `L-1`. -/
def factorAt {L : ℕ} (x : Fin L → α) (m : ℕ)
    (i : Fin (legalStartCount L m)) : Fin m → α :=
  fun t => x ⟨i + t, by
    have hi := i.isLt
    have ht := t.isLt
    simp only [legalStartCount] at hi
    omega⟩

/-- A legal start really does allow reading through its inclusive final
coordinate. -/
theorem legal_start_endpoint {L m : ℕ}
    (i : Fin (legalStartCount L m)) : i.val + m ≤ L := by
  have hi := i.isLt
  simp only [legalStartCount] at hi
  omega

/-- A literal `P`-fold power of positive root length `d` beginning at `a`,
entirely contained before the exclusive endpoint `L`. Adjacent root copies
are required to agree coordinatewise. -/
def HasPowerAt {L : ℕ} (x : Fin L → α) (P a d : ℕ) : Prop :=
  0 < d ∧ a + P * d ≤ L ∧
    ∀ q r : ℕ, q + 1 < P → r < d →
      ∀ hleft : a + q * d + r < L,
      ∀ hright : a + (q + 1) * d + r < L,
        x ⟨a + q * d + r, hleft⟩ =
          x ⟨a + (q + 1) * d + r, hright⟩

/-- The finite word contains no `P` consecutive copies of a nonempty word.
All starts and the right endpoint are quantified explicitly by `HasPowerAt`.
-/
def PPowerFree {L : ℕ} (x : Fin L → α) (P : ℕ) : Prop :=
  ∀ a d : ℕ, ¬ HasPowerAt x P a d

/-- The integer separation forced by `P`-power-freeness. Natural division is
the floor, so this is exactly `floor(m/(P-1)) + 1`. -/
def separation (P m : ℕ) : ℕ := m / (P - 1) + 1

/-- Ordered equal factors force a power whenever their positive gap is at
most `floor(m/(P-1))`. This is the overlap/endpoint core and does not use T164.
-/
theorem ordered_equal_factors_separated {L P m : ℕ} (x : Fin L → α)
    (hP : 2 ≤ P) (hfree : PPowerFree x P)
    {i j : Fin (legalStartCount L m)} (hij : i.val < j.val)
    (heq : factorAt x m i = factorAt x m j) :
    separation P m ≤ j.val - i.val := by
  let d := j.val - i.val
  have hd : 0 < d := Nat.sub_pos_of_lt hij
  by_contra hnot
  have hddiv : d ≤ m / (P - 1) := by
    unfold separation at hnot
    omega
  have hpred : 0 < P - 1 := by omega
  have hmul : d * (P - 1) ≤ m :=
    (Nat.le_div_iff_mul_le hpred).mp hddiv
  have hPeq : P = (P - 1) + 1 := by omega
  have hjEndpoint := legal_start_endpoint j
  have hji : i.val + d = j.val := Nat.add_sub_of_le hij.le
  have hPd : P * d = d + d * (P - 1) := by
    calc
      P * d = ((P - 1) + 1) * d := congrArg (fun z => z * d) hPeq
      _ = d + d * (P - 1) := by
        simp only [Nat.add_mul, one_mul]
        rw [Nat.mul_comm (P - 1) d, Nat.add_comm]
  have hendpoint : i.val + P * d ≤ L := by
    calc
      i.val + P * d = j.val + d * (P - 1) := by
        rw [hPd]
        omega
      _ ≤ j.val + m := Nat.add_le_add_left hmul j.val
      _ ≤ L := hjEndpoint
  have hpower : HasPowerAt x P i.val d := by
    refine ⟨hd, hendpoint, ?_⟩
    intro q r hq hr hleft hright
    have hqpred : q + 1 ≤ P - 1 := by omega
    have hqd : (q + 1) * d ≤ (P - 1) * d :=
      Nat.mul_le_mul_right d hqpred
    have hqr : q * d + r < (q + 1) * d := by
      rw [Nat.add_mul]
      omega
    have ht : q * d + r < m := by
      rw [Nat.mul_comm d (P - 1)] at hmul
      omega
    have heval := congrFun heq ⟨q * d + r, ht⟩
    change x ⟨i.val + (q * d + r), _⟩ =
      x ⟨j.val + (q * d + r), _⟩ at heval
    calc
      x ⟨i.val + q * d + r, hleft⟩ =
          x ⟨i.val + (q * d + r), by omega⟩ := by
            apply congrArg x
            apply Fin.ext
            simp only
            omega
      _ = x ⟨j.val + (q * d + r), by omega⟩ := heval
      _ = x ⟨i.val + (q + 1) * d + r, hright⟩ := by
        apply congrArg x
        apply Fin.ext
        simp only
        rw [Nat.add_mul, one_mul]
        omega
  exact hfree i.val d hpower

/-- Public separation theorem. For any two distinct legal starts carrying
equal length-`m` factors, their start distance is at least
`floor(m/(P-1)) + 1`. -/
theorem equal_factors_start_separation {L P m : ℕ} (x : Fin L → α)
    (hP : 2 ≤ P) (hfree : PPowerFree x P)
    {i j : Fin (legalStartCount L m)} (hne : i ≠ j)
    (heq : factorAt x m i = factorAt x m j) :
    separation P m ≤ Nat.dist i.val j.val := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij.le]
    exact ordered_equal_factors_separated x hP hfree hij heq
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji.le]
    exact ordered_equal_factors_separated x hP hfree hji heq.symm

variable [DecidableEq α]

/-- Legal starts carrying one specified factor. -/
def occurrenceStarts {L : ℕ} (x : Fin L → α) (m : ℕ) (u : Fin m → α) :
    Finset (Fin (legalStartCount L m)) :=
  Finset.univ.filter fun i => factorAt x m i = u

/-- Length-`m` factors observed at legal starts. -/
def observedFactors {L : ℕ} (x : Fin L → α) (m : ℕ) : Finset (Fin m → α) :=
  Finset.univ.image fun i : Fin (legalStartCount L m) => factorAt x m i

/-- Multiplicity of a factor among all legal starts. -/
def factorMultiplicity {L : ℕ} (x : Fin L → α) (m : ℕ)
    (u : Fin m → α) : ℕ :=
  (occurrenceStarts x m u).card

/-- Exact maximum factor multiplicity; it is zero when there are no legal
starts. -/
def maximumOccurrence {L : ℕ} (x : Fin L → α) (m : ℕ) : ℕ :=
  (observedFactors x m).sup (factorMultiplicity x m)

/-- Collision energy as a sum of squared multiplicities over observed labels.
Equivalently it counts ordered pairs of legal starts with equal factors, so
all legal diagonal pairs are included. -/
def collisionEnergy {L : ℕ} (x : Fin L → α) (m : ℕ) : ℕ :=
  ∑ u ∈ observedFactors x m, factorMultiplicity x m u ^ 2

/-- Ordered pairs of legal starts carrying equal factors. The full diagonal
`(i,i)` is present by definition. -/
def orderedCollisionPairs {L : ℕ} (x : Fin L → α) (m : ℕ) :
    Finset (Fin (legalStartCount L m) × Fin (legalStartCount L m)) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    factorAt x m ij.1 = factorAt x m ij.2

/-- Ordered collisions whose first start carries `u`. -/
def collisionPairFiber {L : ℕ} (x : Fin L → α) (m : ℕ)
    (u : Fin m → α) :
    Finset (Fin (legalStartCount L m) × Fin (legalStartCount L m)) :=
  (orderedCollisionPairs x m).filter fun ij => factorAt x m ij.1 = u

@[simp] theorem mem_occurrenceStarts_iff {L : ℕ} (x : Fin L → α)
    (m : ℕ) (u : Fin m → α) (i : Fin (legalStartCount L m)) :
    i ∈ occurrenceStarts x m u ↔ factorAt x m i = u := by
  simp [occurrenceStarts]

@[simp] theorem mem_observedFactors_iff {L : ℕ} (x : Fin L → α)
    (m : ℕ) (u : Fin m → α) :
    u ∈ observedFactors x m ↔
      ∃ i : Fin (legalStartCount L m), factorAt x m i = u := by
  simp [observedFactors]

/-- The multiplicities partition every legal start, including the final legal
start when `m ≤ L`. -/
theorem sum_factorMultiplicity_eq_legalStartCount {L : ℕ}
    (x : Fin L → α) (m : ℕ) :
    ∑ u ∈ observedFactors x m, factorMultiplicity x m u =
      legalStartCount L m := by
  classical
  have h := Finset.card_eq_sum_card_image
    (fun i : Fin (legalStartCount L m) => factorAt x m i)
    (Finset.univ : Finset (Fin (legalStartCount L m)))
  simpa [observedFactors, factorMultiplicity, occurrenceStarts] using h.symm

/-- A collision fiber is exactly the Cartesian square of one occurrence
fiber. -/
theorem collisionPairFiber_card {L : ℕ} (x : Fin L → α) (m : ℕ)
    (u : Fin m → α) :
    (collisionPairFiber x m u).card = factorMultiplicity x m u ^ 2 := by
  classical
  rw [collisionPairFiber, factorMultiplicity, pow_two, ← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [orderedCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and, mem_occurrenceStarts_iff]
  constructor
  · rintro ⟨hij, hiu⟩
    exact ⟨hiu, hij.symm.trans hiu⟩
  · rintro ⟨hiu, hju⟩
    exact ⟨hiu.trans hju.symm, hiu⟩

/-- The squared-multiplicity energy is exactly the cardinality of the ordered,
diagonal-inclusive collision set. -/
theorem collisionEnergy_eq_orderedCollisionPairs_card {L : ℕ}
    (x : Fin L → α) (m : ℕ) :
    collisionEnergy x m = (orderedCollisionPairs x m).card := by
  classical
  have hpartition :
      (orderedCollisionPairs x m).card =
        ∑ u ∈ observedFactors x m, (collisionPairFiber x m u).card := by
    simpa only [collisionPairFiber] using
      (Finset.card_eq_sum_card_fiberwise fun ij hij => by
        exact (mem_observedFactors_iff x m (factorAt x m ij.1)).mpr
          ⟨ij.1, rfl⟩)
  rw [collisionEnergy, hpartition]
  apply Finset.sum_congr rfl
  intro u _hu
  exact (collisionPairFiber_card x m u).symm

/-- Every legal start contributes its ordered diagonal collision, including
the final legal start. Thus the energy has at least the legal-start count.
-/
theorem legalStartCount_le_collisionEnergy {L : ℕ}
    (x : Fin L → α) (m : ℕ) :
    legalStartCount L m ≤ collisionEnergy x m := by
  classical
  let D := (Finset.univ : Finset (Fin (legalStartCount L m))).image
    fun i => (i, i)
  have hDcard : D.card = legalStartCount L m := by
    dsimp [D]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _ j _ hij
      exact congrArg Prod.fst hij
  have hsubset : D ⊆ orderedCollisionPairs x m := by
    intro ij hij
    dsimp [D] at hij
    rw [Finset.mem_image] at hij
    obtain ⟨i, _hi, rfl⟩ := hij
    simp [orderedCollisionPairs]
  calc
    legalStartCount L m = D.card := hDcard.symm
    _ ≤ (orderedCollisionPairs x m).card := Finset.card_le_card hsubset
    _ = collisionEnergy x m :=
      (collisionEnergy_eq_orderedCollisionPairs_card x m).symm

/-- Exact packing capacity for starts in a window of length
`legalStartCount L m` separated by `floor(m/(P-1)) + 1`. The explicit zero
branch is essential: when `m > L`, there are no legal starts and the exact
capacity is zero, not one. -/
def packingCapacity (L P m : ℕ) : ℕ :=
  if legalStartCount L m = 0 then 0
  else 1 + (legalStartCount L m - 1) / separation P m

/-- If the requested factor is longer than the finite word, there are no legal
starts and the exact packing capacity is zero. -/
theorem packingCapacity_eq_zero_of_word_shorter {L P m : ℕ} (hm : L < m) :
    packingCapacity L P m = 0 := by
  have hzero : legalStartCount L m = 0 := by
    unfold legalStartCount
    omega
  simp [packingCapacity, hzero]

/-- Exact finite packing bound for every factor label. It returns zero at the
empty legal-start endpoint. Positivity is needed only for the separation
denominator in the nonempty branch. -/
theorem factorMultiplicity_le_packing {L P m : ℕ} (x : Fin L → α)
    (hP : 2 ≤ P) (hfree : PPowerFree x P) (u : Fin m → α) :
    factorMultiplicity x m u ≤ packingCapacity L P m := by
  classical
  by_cases hzero : legalStartCount L m = 0
  · rw [packingCapacity, if_pos hzero, Nat.le_zero, factorMultiplicity,
      Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro i _hi
    exfalso
    have hi := i.isLt
    omega
  · rw [packingCapacity, if_neg hzero]
    let A := (occurrenceStarts x m u).image fun i => i.val
    have hcard : A.card = factorMultiplicity x m u := by
      dsimp [A, factorMultiplicity]
      rw [Finset.card_image_iff.mpr]
      intro i _ j _ hij
      exact Fin.ext hij
    have hwindow : ∀ i ∈ A,
        0 ≤ i ∧ i < 0 + legalStartCount L m := by
      intro i hi
      dsimp [A] at hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, _hj, rfl⟩ := hi
      exact ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact j.isLt⟩
    have hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j →
        separation P m ≤ Nat.dist i j := by
      intro i hi j hj hne
      dsimp [A] at hi hj
      rw [Finset.mem_image] at hi hj
      obtain ⟨i', hi', rfl⟩ := hi
      obtain ⟨j', hj', rfl⟩ := hj
      apply equal_factors_start_separation x hP hfree
      · exact fun heq => hne (congrArg Fin.val heq)
      · exact (mem_occurrenceStarts_iff x m u i').mp hi' |>.trans
          ((mem_occurrenceStarts_iff x m u j').mp hj').symm
    have hp : 0 < separation P m := by
      simp [separation]
    rw [← hcard]
    exact
      DecimalFactorComplexity.T100UniversalCharging.card_le_one_add_div_of_separated
        A hp hwindow hsep

/-- Exact maximum-occurrence packing bound. The nested natural divisions are
the displayed integer floors, and the capacity is exactly zero when `m > L`.
-/
theorem maximumOccurrence_le_packing {L P m : ℕ} (x : Fin L → α)
    (hP : 2 ≤ P) (hfree : PPowerFree x P) :
    maximumOccurrence x m ≤ packingCapacity L P m := by
  classical
  unfold maximumOccurrence
  apply Finset.sup_le
  intro u hu
  exact factorMultiplicity_le_packing x hP hfree u

/-- The maximum occurrence count is exactly zero when the factor length is
longer than the word. This is the empty legal-start endpoint omitted by the
weaker `1 + (S - 1) / d` formula. -/
theorem maximumOccurrence_eq_zero_of_word_shorter {L P m : ℕ}
    (x : Fin L → α) (hP : 2 ≤ P) (hfree : PPowerFree x P) (hm : L < m) :
    maximumOccurrence x m = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    maximumOccurrence x m ≤ packingCapacity L P m :=
      maximumOccurrence_le_packing x hP hfree
    _ = 0 := packingCapacity_eq_zero_of_word_shorter hm

/-- Ordered, diagonal-inclusive collision energy obeys legal-start count times
the exact maximum packing capacity. For no legal starts both factors on the
right are zero. -/
theorem collisionEnergy_le_packing {L P m : ℕ} (x : Fin L → α)
    (hP : 2 ≤ P) (hfree : PPowerFree x P) :
    collisionEnergy x m ≤
      legalStartCount L m * packingCapacity L P m := by
  classical
  have hpoint (u : Fin m → α) :
      factorMultiplicity x m u ^ 2 ≤
        factorMultiplicity x m u * packingCapacity L P m := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _
      (factorMultiplicity_le_packing x hP hfree u)
  unfold collisionEnergy
  calc
    (∑ u ∈ observedFactors x m, factorMultiplicity x m u ^ 2) ≤
        ∑ u ∈ observedFactors x m,
          factorMultiplicity x m u * packingCapacity L P m := by
      exact Finset.sum_le_sum fun u _hu => hpoint u
    _ = (∑ u ∈ observedFactors x m, factorMultiplicity x m u) *
        packingCapacity L P m := by
      rw [Finset.sum_mul]
    _ = legalStartCount L m * packingCapacity L P m := by
      rw [sum_factorMultiplicity_eq_legalStartCount]

/-- The ordered, diagonal-inclusive collision energy is exactly zero when
there are no legal starts. In this endpoint the diagonal itself is empty. -/
theorem collisionEnergy_eq_zero_of_word_shorter {L P m : ℕ}
    (x : Fin L → α) (hP : 2 ≤ P) (hfree : PPowerFree x P) (hm : L < m) :
    collisionEnergy x m = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    collisionEnergy x m ≤ legalStartCount L m * packingCapacity L P m :=
      collisionEnergy_le_packing x hP hfree
    _ = 0 := by rw [packingCapacity_eq_zero_of_word_shorter hm, Nat.mul_zero]

/-- Wrapper for callers that provide an external finite-word power-free
certificate. It adds no substitution or fixed-pi premise. -/
theorem finite_word_sibling_of_external_power_free_certificate
    {L P m : ℕ} (x : Fin L → α) (hP : 2 ≤ P)
    (certificate : PPowerFree x P) :
    (∀ i j : Fin (legalStartCount L m), i ≠ j →
      factorAt x m i = factorAt x m j →
        m / (P - 1) + 1 ≤ Nat.dist i.val j.val) ∧
    maximumOccurrence x m ≤ packingCapacity L P m ∧
    collisionEnergy x m ≤
      legalStartCount L m * packingCapacity L P m := by
  exact ⟨fun i j hne heq => by
      simpa [separation] using
        equal_factors_start_separation x hP certificate hne heq,
    maximumOccurrence_le_packing x hP certificate,
    collisionEnergy_le_packing x hP certificate⟩

end Theory.PiLacunaryNearReturnSparsity.T166

#print axioms Theory.PiLacunaryNearReturnSparsity.T166.equal_factors_start_separation
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.maximumOccurrence_le_packing
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.maximumOccurrence_eq_zero_of_word_shorter
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.collisionEnergy_eq_orderedCollisionPairs_card
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.legalStartCount_le_collisionEnergy
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.collisionEnergy_le_packing
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.collisionEnergy_eq_zero_of_word_shorter
#print axioms Theory.PiLacunaryNearReturnSparsity.T166.finite_word_sibling_of_external_power_free_certificate
