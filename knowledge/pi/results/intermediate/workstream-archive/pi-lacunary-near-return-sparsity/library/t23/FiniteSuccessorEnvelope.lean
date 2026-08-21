import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting

/-!
# Exact finite successor-splitting envelopes

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves only a finite, one-row A14 sibling statement. It neither
asserts C2 nor canonical A1, and it asserts no unconditional asymptotic property
of the decimal expansion of `Real.pi`.
-/

noncomputable section

open Finset

namespace DecimalFactorComplexity.FiniteSuccessorEnvelope

/-- The ten successor counts sum to the occupancy of their parent. -/
def parentOccupancy {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) (a : ι) : ℕ :=
  ∑ d : Fin 10, count a d

/-- Ordered pairs of distinct decimal successor digits. -/
def distinctDigitPairs : Finset (Fin 10 × Fin 10) :=
  (Finset.univ ×ˢ Finset.univ).filter fun de => de.1 ≠ de.2

theorem distinctDigitPairs_nonempty : distinctDigitPairs.Nonempty := by
  refine ⟨(0, 1), ?_⟩
  simp [distinctDigitPairs]

/-- The second-largest successor count, expressed without choosing a sorting
convention: maximize the smaller count over all distinct pairs of digits. -/
def secondLargestSuccessor {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) (a : ι) : ℕ :=
  distinctDigitPairs.sup fun de => min (count a de.1) (count a de.2)

/-- A threshold is met by two distinct successors exactly when it is at most
the explicit second-largest successor count. -/
theorem two_successors_iff_le_secondLargest
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ)
    (a : ι) (eta : ℝ) :
    (∃ d e : Fin 10, d ≠ e ∧
        eta * parentOccupancy count a ≤ count a d ∧
        eta * parentOccupancy count a ≤ count a e) ↔
      eta * parentOccupancy count a ≤ secondLargestSuccessor count a := by
  classical
  constructor
  · rintro ⟨d, e, hde, hd, he⟩
    have hmem : (d, e) ∈ distinctDigitPairs := by
      simp [distinctDigitPairs, hde]
    have hpair : min (count a d) (count a e) ≤
        secondLargestSuccessor count a := by
      exact Finset.le_sup (f := fun de : Fin 10 × Fin 10 =>
        min (count a de.1) (count a de.2)) hmem
    have hmin : eta * parentOccupancy count a ≤
        (min (count a d) (count a e) : ℕ) := by
      push_cast
      exact le_min hd he
    exact hmin.trans (by exact_mod_cast hpair)
  · intro h
    obtain ⟨de, hde, hsup⟩ := Finset.exists_mem_eq_sup
      distinctDigitPairs distinctDigitPairs_nonempty
      (fun de : Fin 10 × Fin 10 => min (count a de.1) (count a de.2))
    rcases de with ⟨d, e⟩
    have hdne : d ≠ e := by
      simpa [distinctDigitPairs] using hde
    change eta * parentOccupancy count a ≤
      (distinctDigitPairs.sup fun de : Fin 10 × Fin 10 =>
        min (count a de.1) (count a de.2) : ℕ) at h
    rw [hsup] at h
    refine ⟨d, e, hdne, h.trans ?_, h.trans ?_⟩
    · exact_mod_cast Nat.min_le_left (count a d) (count a e)
    · exact_mod_cast Nat.min_le_right (count a d) (count a e)

/-- Collision energy of one finite parent row. -/
def rowEnergy {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) : ℝ :=
  ∑ a : ι, (parentOccupancy count a : ℝ) ^ 2

/-- Squared parent mass whose second-largest successor meets `eta`. -/
def rowSplitEnergy {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) (eta : ℝ) : ℝ := by
  classical
  exact ∑ a : ι,
    if eta * parentOccupancy count a ≤ secondLargestSuccessor count a then
      (parentOccupancy count a : ℝ) ^ 2
    else 0

/-- Exact finite feasible region, including T14's decimal endpoint conditions. -/
def FeasibleParameters {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) (eta mu : ℝ) : Prop :=
  0 < eta ∧ eta ≤ 1 / 10 ∧ 0 < mu ∧ mu < 1 ∧
    mu * rowEnergy count ≤ rowSplitEnergy count eta

/-- At positive total energy, the sharp `mu` endpoint is the displayed ratio. -/
theorem feasibleParameters_iff_exact_envelope
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ)
    (eta mu : ℝ) (henergy : 0 < rowEnergy count) :
    FeasibleParameters count eta mu ↔
      0 < eta ∧ eta ≤ 1 / 10 ∧ 0 < mu ∧ mu < 1 ∧
        mu ≤ rowSplitEnergy count eta / rowEnergy count := by
  constructor
  · rintro ⟨heta, hetaUpper, hmu, hmuUpper, henvelope⟩
    exact ⟨heta, hetaUpper, hmu, hmuUpper,
      (le_div_iff₀ henergy).2 henvelope⟩
  · rintro ⟨heta, hetaUpper, hmu, hmuUpper, henvelope⟩
    exact ⟨heta, hetaUpper, hmu, hmuUpper,
      (le_div_iff₀ henergy).1 henvelope⟩

/-- All raw second-largest/parent ratios. Division by zero contributes `0`,
which is already an explicit endpoint and carries zero squared parent mass. -/
def rawBreakpoints {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image fun a =>
    (secondLargestSuccessor count a : ℝ) / parentOccupancy count a

/-- Complete breakpoints in T14's domain. The cells are left-open and
right-closed; `0` and `1/10` are always present as explicit endpoints. -/
def parameterBreakpoints {ι : Type*} [Fintype ι]
    (count : ι → Fin 10 → ℕ) : Finset ℝ := by
  classical
  exact insert 0 (insert (1 / 10)
    ((rawBreakpoints count).filter fun r => 0 < r ∧ r < 1 / 10))

theorem zero_mem_parameterBreakpoints
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ) :
    0 ∈ parameterBreakpoints count := by
  simp [parameterBreakpoints]

theorem one_tenth_mem_parameterBreakpoints
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ) :
    (1 / 10 : ℝ) ∈ parameterBreakpoints count := by
  simp [parameterBreakpoints]

/-- Literal membership characterization: apart from the two domain endpoints,
every breakpoint is a second-largest-successor ratio of an explicit parent. -/
theorem mem_parameterBreakpoints_iff
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ) (r : ℝ) :
    r ∈ parameterBreakpoints count ↔
      r = 0 ∨ r = 1 / 10 ∨
        (0 < r ∧ r < 1 / 10 ∧ ∃ a : ι,
          (secondLargestSuccessor count a : ℝ) /
            parentOccupancy count a = r) := by
  simp only [parameterBreakpoints, rawBreakpoints, Finset.mem_insert,
    Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  aesop

/-- There are no missing changes between consecutive listed breakpoints.
Thus every left-open/right-closed cell has one constant split energy. -/
theorem rowSplitEnergy_eq_of_no_breakpoint
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ)
    (eta b : ℝ) (heta : 0 < eta) (hetab : eta ≤ b)
    (hb : b ≤ 1 / 10)
    (hgap : ∀ r ∈ parameterBreakpoints count, eta ≤ r → ¬ r < b) :
    rowSplitEnergy count eta = rowSplitEnergy count b := by
  classical
  unfold rowSplitEnergy
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hpzero : parentOccupancy count a = 0
  · simp [hpzero]
  · have hpNat : 0 < parentOccupancy count a := Nat.pos_of_ne_zero hpzero
    have hp : 0 < (parentOccupancy count a : ℝ) := by exact_mod_cast hpNat
    let r : ℝ := (secondLargestSuccessor count a : ℝ) /
      parentOccupancy count a
    have hrRaw : r ∈ rawBreakpoints count := by
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_univ a, rfl⟩
    have hthreshold :
        eta * parentOccupancy count a ≤ secondLargestSuccessor count a ↔
          b * parentOccupancy count a ≤ secondLargestSuccessor count a := by
      constructor
      · intro hetaSplit
        have hetaR : eta ≤ r := by
          exact (le_div_iff₀ hp).2 hetaSplit
        have hbR : b ≤ r := by
          apply le_of_not_gt
          intro hrb
          have hrpos : 0 < r := heta.trans_le hetaR
          have hrupper : r < 1 / 10 := hrb.trans_le hb
          have hrmem : r ∈ parameterBreakpoints count := by
            simp only [parameterBreakpoints, Finset.mem_insert,
              Finset.mem_filter]
            exact Or.inr (Or.inr ⟨hrRaw, hrpos, hrupper⟩)
          exact (hgap r hrmem hetaR) hrb
        exact (le_div_iff₀ hp).1 hbR
      · intro hbSplit
        have hmul : eta * (parentOccupancy count a : ℝ) ≤
            b * parentOccupancy count a :=
          mul_le_mul_of_nonneg_right hetab (by positivity)
        exact hmul.trans hbSplit
    by_cases hetaSplit :
        eta * parentOccupancy count a ≤ secondLargestSuccessor count a
    · have hbSplit := hthreshold.mp hetaSplit
      simp only [hetaSplit, hbSplit, if_true]
    · have hbSplit : ¬ b * parentOccupancy count a ≤
          secondLargestSuccessor count a := fun h =>
        hetaSplit (hthreshold.mpr h)
      simp only [hetaSplit, hbSplit, if_false]

/-- Consequently the full feasible `mu` envelope is constant on each
left-open/right-closed breakpoint cell. -/
theorem feasibleParameters_iff_at_cell_endpoint
    {ι : Type*} [Fintype ι] (count : ι → Fin 10 → ℕ)
    (eta b mu : ℝ) (heta : 0 < eta) (hetab : eta ≤ b)
    (hb : b ≤ 1 / 10)
    (hgap : ∀ r ∈ parameterBreakpoints count, eta ≤ r → ¬ r < b) :
    FeasibleParameters count eta mu ↔ FeasibleParameters count b mu := by
  have hsplit := rowSplitEnergy_eq_of_no_breakpoint
    count eta b heta hetab hb hgap
  constructor
  · rintro ⟨_heta, _hetaUpper, hmu, hmuUpper, henvelope⟩
    exact ⟨heta.trans_le hetab, hb, hmu, hmuUpper, by simpa [hsplit] using henvelope⟩
  · rintro ⟨_hbpos, _hbUpper, hmu, hmuUpper, henvelope⟩
    exact ⟨heta, hetab.trans hb, hmu, hmuUpper, by simpa [hsplit] using henvelope⟩

/-- Energy carried by parents whose occupancy is at most `R`. -/
def lowMultiplicityEnergy {ι : Type*} [Fintype ι]
    (occupancy : ι → ℕ) (R : ℕ) : ℝ := by
  classical
  exact ∑ a : ι, if occupancy a ≤ R then (occupancy a : ℝ) ^ 2 else 0

/-- Total (non-squared) parent occupancy. -/
def totalOccupancy {ι : Type*} [Fintype ι]
    (occupancy : ι → ℕ) : ℝ :=
  ∑ a : ι, occupancy a

/-- Low-multiplicity parents have at most `R` times total occupancy in
collision energy. -/
theorem lowMultiplicityEnergy_le
    {ι : Type*} [Fintype ι] (occupancy : ι → ℕ) (R : ℕ) :
    lowMultiplicityEnergy occupancy R ≤ R * totalOccupancy occupancy := by
  classical
  unfold lowMultiplicityEnergy totalOccupancy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hlow : occupancy a ≤ R
  · simp only [hlow, if_true]
    have hcast : (occupancy a : ℝ) ≤ R := by exact_mod_cast hlow
    have hnonneg : 0 ≤ (occupancy a : ℝ) := by positivity
    nlinarith
  · simp only [hlow, if_false]
    positivity

/-- Explicit occupancy ceiling: if low-multiplicity parents carry at least a
positive `kappa` fraction of all collision energy, then total energy is at most
`R * totalOccupancy / kappa`. -/
theorem energy_le_of_lowMultiplicity_dominates
    {ι : Type*} [Fintype ι] (occupancy : ι → ℕ)
    (R : ℕ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hdominates : kappa * (∑ a : ι, (occupancy a : ℝ) ^ 2) ≤
      lowMultiplicityEnergy occupancy R) :
    (∑ a : ι, (occupancy a : ℝ) ^ 2) ≤
      R * totalOccupancy occupancy / kappa := by
  have hbound := hdominates.trans (lowMultiplicityEnergy_le occupancy R)
  rw [le_div_iff₀ hkappa]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hbound

/-- Singleton specialization of the occupancy ceiling. -/
theorem energy_le_of_singletons_dominate
    {ι : Type*} [Fintype ι] (occupancy : ι → ℕ)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hdominates : kappa * (∑ a : ι, (occupancy a : ℝ) ^ 2) ≤
      lowMultiplicityEnergy occupancy 1) :
    (∑ a : ι, (occupancy a : ℝ) ^ 2) ≤
      totalOccupancy occupancy / kappa := by
  simpa using energy_le_of_lowMultiplicity_dominates
    occupancy 1 kappa hkappa hdominates

open DecimalFactorComplexity.FiniteCylinderEnergy

/-- T14's second-largest successor count for one pi-cylinder parent. -/
def piSecondLargestSuccessor (n N : ℕ) (a : Fin (10 ^ n)) : ℕ :=
  secondLargestSuccessor (piSuccessorCount n N) a

/-- The exact finite split mass for a T14 row. -/
def piRowSplitEnergy (n N : ℕ) (eta : ℝ) : ℝ :=
  rowSplitEnergy (piSuccessorCount n N) eta

/-- The explicit finite breakpoint set for a T14 row. -/
def piRowParameterBreakpoints (n N : ℕ) : Finset ℝ :=
  parameterBreakpoints (piSuccessorCount n N)

theorem pi_parentOccupancy_eq_fiber_card
    (n N : ℕ) (a : Fin (10 ^ n)) :
    parentOccupancy (piSuccessorCount n N) a =
      (piCylinderFiber n N a).card := by
  exact (piCylinderFiber_card_eq_sum_successorCount n N a).symm

theorem pi_rowEnergy_eq_collisionEnergy (n N : ℕ) :
    rowEnergy (piSuccessorCount n N) = piCylinderCollisionEnergy n N := by
  unfold rowEnergy piCylinderCollisionEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro a _ha
  rw [pi_parentOccupancy_eq_fiber_card]

/-- Literal finite breakpoint list for the T14 row. -/
theorem mem_piRowParameterBreakpoints_iff
    (n N : ℕ) (r : ℝ) :
    r ∈ piRowParameterBreakpoints n N ↔
      r = 0 ∨ r = 1 / 10 ∨
        (0 < r ∧ r < 1 / 10 ∧ ∃ a : Fin (10 ^ n),
          (piSecondLargestSuccessor n N a : ℝ) /
            (piCylinderFiber n N a).card = r) := by
  simpa [piRowParameterBreakpoints, piSecondLargestSuccessor,
    pi_parentOccupancy_eq_fiber_card] using
      mem_parameterBreakpoints_iff (piSuccessorCount n N) r

/-- Exact specialization of the generic envelope to T14's finite splitting
predicate, with every parent, weight, and inequality visible. -/
theorem pi_quantitativeSplittingLevel_iff_exact_envelope
    (n N : ℕ) (mu eta : ℝ) :
    QuantitativeSplittingLevel n N mu eta ↔
      mu * (piCylinderCollisionEnergy n N : ℝ) ≤
        ∑ a : Fin (10 ^ n),
          if eta * (piCylinderFiber n N a).card ≤
              piSecondLargestSuccessor n N a then
            ((piCylinderFiber n N a).card : ℝ) ^ 2
          else 0 := by
  classical
  have hsplit : ∀ a : Fin (10 ^ n),
      QuantitativelySplitParent n N eta a ↔
        eta * parentOccupancy (piSuccessorCount n N) a ≤
          piSecondLargestSuccessor n N a := by
    intro a
    unfold piSecondLargestSuccessor
    rw [← two_successors_iff_le_secondLargest]
    simp only [QuantitativelySplitParent, pi_parentOccupancy_eq_fiber_card]
  unfold QuantitativeSplittingLevel
  apply iff_of_eq
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [if_congr (hsplit a) rfl rfl, pi_parentOccupancy_eq_fiber_card]

/-- Sharp T14 row envelope with all positivity and endpoint assumptions
exposed. No coherent, C2, or A1 conclusion is made. -/
theorem pi_admissible_splitting_iff_mu_le_cap
    (n N : ℕ) (mu eta : ℝ) (hN : 1 ≤ N) :
    (0 < eta ∧ eta ≤ 1 / 10 ∧ 0 < mu ∧ mu < 1 ∧
      QuantitativeSplittingLevel n N mu eta) ↔
    (0 < eta ∧ eta ≤ 1 / 10 ∧ 0 < mu ∧ mu < 1 ∧
      mu ≤ (∑ a : Fin (10 ^ n),
        if eta * (piCylinderFiber n N a).card ≤
            piSecondLargestSuccessor n N a then
          ((piCylinderFiber n N a).card : ℝ) ^ 2
        else 0) / piCylinderCollisionEnergy n N) := by
  have henergyNat : 0 < piCylinderCollisionEnergy n N :=
    lt_of_lt_of_le (Nat.zero_lt_of_lt hN)
      (diagonal_le_piCylinderCollisionEnergy n N)
  have henergy : 0 < (piCylinderCollisionEnergy n N : ℝ) := by
    exact_mod_cast henergyNat
  constructor
  · rintro ⟨heta, hetaUpper, hmu, hmuUpper, hsplit⟩
    have henvelope :=
      (pi_quantitativeSplittingLevel_iff_exact_envelope n N mu eta).mp hsplit
    exact ⟨heta, hetaUpper, hmu, hmuUpper,
      (le_div_iff₀ henergy).2 henvelope⟩
  · rintro ⟨heta, hetaUpper, hmu, hmuUpper, henvelope⟩
    refine ⟨heta, hetaUpper, hmu, hmuUpper,
      (pi_quantitativeSplittingLevel_iff_exact_envelope n N mu eta).mpr ?_⟩
    exact (le_div_iff₀ henergy).1 henvelope

/-- Breakpoint completeness specialized to the accepted T14 definitions. -/
theorem pi_rowSplitEnergy_eq_of_no_breakpoint
    (n N : ℕ) (eta b : ℝ) (heta : 0 < eta) (hetab : eta ≤ b)
    (hb : b ≤ 1 / 10)
    (hgap : ∀ r ∈ piRowParameterBreakpoints n N, eta ≤ r → ¬ r < b) :
    (∑ a : Fin (10 ^ n),
      if eta * (piCylinderFiber n N a).card ≤
          piSecondLargestSuccessor n N a then
        ((piCylinderFiber n N a).card : ℝ) ^ 2
      else 0) =
    ∑ a : Fin (10 ^ n),
      if b * (piCylinderFiber n N a).card ≤
          piSecondLargestSuccessor n N a then
        ((piCylinderFiber n N a).card : ℝ) ^ 2
      else 0 := by
  have h := rowSplitEnergy_eq_of_no_breakpoint
    (piSuccessorCount n N) eta b heta hetab hb hgap
  simpa [rowSplitEnergy, piSecondLargestSuccessor,
    pi_parentOccupancy_eq_fiber_card] using h

/-- The level-`n` parent occupancies partition exactly the `N` sampled starts. -/
theorem pi_totalParentOccupancy_eq_cutoff (n N : ℕ) :
    (∑ a : Fin (10 ^ n), (piCylinderFiber n N a).card) = N := by
  simpa [piCylinderFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset (Fin (10 ^ n))))
      (f := fun i : Fin N => piCylinderCode n i) (by simp)).symm

/-- Occupancy ceiling for the actual finite pi-cylinder row. -/
theorem pi_collisionEnergy_le_of_lowMultiplicity_dominates
    (n N R : ℕ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hdominates : kappa * (piCylinderCollisionEnergy n N : ℝ) ≤
      lowMultiplicityEnergy
        (fun a : Fin (10 ^ n) => (piCylinderFiber n N a).card) R) :
    (piCylinderCollisionEnergy n N : ℝ) ≤ R * N / kappa := by
  classical
  let occupancy : Fin (10 ^ n) → ℕ := fun a =>
    (piCylinderFiber n N a).card
  have henergy : (∑ a : Fin (10 ^ n), (occupancy a : ℝ) ^ 2) =
      (piCylinderCollisionEnergy n N : ℝ) := by
    unfold occupancy piCylinderCollisionEnergy
    push_cast
    rfl
  have htotal : totalOccupancy occupancy = N := by
    unfold totalOccupancy
    exact_mod_cast pi_totalParentOccupancy_eq_cutoff n N
  have hdominates' : kappa *
      (∑ a : Fin (10 ^ n), (occupancy a : ℝ) ^ 2) ≤
        lowMultiplicityEnergy occupancy R := by
    simpa [occupancy, henergy] using hdominates
  have hbound := energy_le_of_lowMultiplicity_dominates
    occupancy R kappa hkappa hdominates'
  simpa [henergy, htotal] using hbound

end DecimalFactorComplexity.FiniteSuccessorEnvelope

#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.two_successors_iff_le_secondLargest
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.feasibleParameters_iff_exact_envelope
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.mem_parameterBreakpoints_iff
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.rowSplitEnergy_eq_of_no_breakpoint
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.feasibleParameters_iff_at_cell_endpoint
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.lowMultiplicityEnergy_le
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.energy_le_of_lowMultiplicity_dominates
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.energy_le_of_singletons_dominate
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.mem_piRowParameterBreakpoints_iff
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.pi_quantitativeSplittingLevel_iff_exact_envelope
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.pi_admissible_splitting_iff_mu_le_cap
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.pi_rowSplitEnergy_eq_of_no_breakpoint
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.pi_totalParentOccupancy_eq_cutoff
#print axioms DecimalFactorComplexity.FiniteSuccessorEnvelope.pi_collisionEnergy_le_of_lowMultiplicity_dominates
