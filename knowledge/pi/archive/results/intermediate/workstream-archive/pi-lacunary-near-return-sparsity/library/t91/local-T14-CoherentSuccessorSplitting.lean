import TheoryLib.PiLacunaryNearReturnSparsity.T9SuccessorSplitting
import TheoryLib.PiLacunaryNearReturnSparsity.T12CoherentFinitePrefixDecay

/-!
# Coherent positive-density successor splitting

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module characterizes the agenda's open C2 hypothesis.  It does not assert
C2, canonical A1, or any unconditional splitting property of `Real.pi`.
-/

noncomputable section

open Filter Finset Topology
open MeasureTheory ProbabilityTheory

namespace DecimalFactorComplexity.CoherentSuccessorSplitting

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.CoherentFinitePrefixDecay

/-- Fixed-parameter positive-density splitting on the same finite-prefix rows
and weak limit as T12.  The count includes exactly the levels `l < m`. -/
def PiCoherentPositiveDensitySplittingAt
    (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle) : Prop :=
  0 < mu ∧ mu < 1 ∧ 0 < eta ∧ eta ≤ 1 / 10 ∧
    0 < d ∧ 0 ≤ B ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
    Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 nu) ∧
    ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
      d * (m : ℝ) - B ≤ (piSplittingLevelCount m (N k) mu eta : ℝ)

/-- Existential coherent splitting.  All quantitative parameters are fixed
outside the row/depth triangle. -/
def PiCoherentPositiveDensitySplitting : Prop :=
  ∃ mu eta d B : ℝ, ∃ m0 k0 : ℕ, ∃ N : ℕ → ℕ,
    ∃ nu : ProbabilityMeasure UnitAddCircle,
      PiCoherentPositiveDensitySplittingAt mu eta d B m0 k0 N nu

/-- The definition with every fixed parameter and triangular quantifier
visible. -/
theorem piCoherentPositiveDensitySplittingAt_iff_quantifiers
    (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle) :
    PiCoherentPositiveDensitySplittingAt mu eta d B m0 k0 N nu ↔
      0 < mu ∧ mu < 1 ∧ 0 < eta ∧ eta ≤ 1 / 10 ∧
      0 < d ∧ 0 ≤ B ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
      Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 nu) ∧
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        d * (m : ℝ) - B ≤
          (piSplittingLevelCount m (N k) mu eta : ℝ) :=
  Iff.rfl

/-- Cauchy--Schwarz for the ten successor digits of one parent. -/
theorem one_tenth_parent_energy_le_successor_energy
    (n cutoff : ℕ) (a : Fin (10 ^ n)) :
    (1 / 10 : ℝ) * ((piCylinderFiber n cutoff a).card : ℝ) ^ 2 ≤
      ∑ e : Fin 10, (piSuccessorCount n cutoff a e : ℝ) ^ 2 := by
  have hsum : ((piCylinderFiber n cutoff a).card : ℝ) =
      ∑ e : Fin 10, (piSuccessorCount n cutoff a e : ℝ) := by
    exact_mod_cast piCylinderFiber_card_eq_sum_successorCount n cutoff a
  have hsq : ((piCylinderFiber n cutoff a).card : ℝ) ^ 2 ≤
      (10 : ℝ) * ∑ e : Fin 10,
        (piSuccessorCount n cutoff a e : ℝ) ^ 2 := by
    rw [hsum]
    exact sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 10)))
      (f := fun e : Fin 10 => (piSuccessorCount n cutoff a e : ℝ))
  linarith

/-- Every decimal refinement retains at least one tenth of collision energy. -/
theorem one_tenth_energy_le_energy_succ (n cutoff : ℕ) :
    (1 / 10 : ℝ) * (piCylinderCollisionEnergy n cutoff : ℝ) ≤
      piCylinderCollisionEnergy (n + 1) cutoff := by
  rw [piCylinderCollisionEnergy_succ_refinement, piCylinderCollisionEnergy]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    one_tenth_parent_energy_le_successor_energy n cutoff a

/-- Normalized form of the base-10 lower refinement ratio. -/
theorem one_tenth_normalized_energy_le_succ
    (n cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    (1 / 10 : ℝ) * normalizedPiCylinderCollisionEnergy n cutoff ≤
      normalizedPiCylinderCollisionEnergy (n + 1) cutoff := by
  have hden : 0 < (cutoff : ℝ) ^ 2 := by positivity
  unfold normalizedPiCylinderCollisionEnergy
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hden]
  exact one_tenth_energy_le_energy_succ n cutoff

/-- A nonsplitting parent retains the square of T9's dominant-successor
fraction of its collision energy. -/
theorem not_splitParent_successor_energy_lower
    (n cutoff : ℕ) (eta : ℝ) (a : Fin (10 ^ n))
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 10)
    (hnot : ¬ QuantitativelySplitParent n cutoff eta a) :
    (1 - 9 * eta) ^ 2 * ((piCylinderFiber n cutoff a).card : ℝ) ^ 2 ≤
      ∑ e : Fin 10, (piSuccessorCount n cutoff a e : ℝ) ^ 2 := by
  obtain ⟨e, he⟩ := not_splitParent_hasDominantSuccessor
    n cutoff eta a heta hetaUpper hnot
  have hcoefficient : 0 ≤ 1 - 9 * eta := by
    have : eta ≤ (1 / 10 : ℝ) := hetaUpper
    linarith
  have hcount : 0 ≤ (piSuccessorCount n cutoff a e : ℝ) := by positivity
  have hleft : 0 ≤
      (1 - 9 * eta) * ((piCylinderFiber n cutoff a).card : ℝ) :=
    mul_nonneg hcoefficient (by positivity)
  have hsquare :
      ((1 - 9 * eta) * ((piCylinderFiber n cutoff a).card : ℝ)) ^ 2 ≤
        (piSuccessorCount n cutoff a e : ℝ) ^ 2 := by
    nlinarith
  calc
    (1 - 9 * eta) ^ 2 * ((piCylinderFiber n cutoff a).card : ℝ) ^ 2 =
        ((1 - 9 * eta) * ((piCylinderFiber n cutoff a).card : ℝ)) ^ 2 := by
      ring
    _ ≤ (piSuccessorCount n cutoff a e : ℝ) ^ 2 := hsquare
    _ ≤ ∑ z : Fin 10, (piSuccessorCount n cutoff a z : ℝ) ^ 2 := by
      exact Finset.single_le_sum (fun z _ => sq_nonneg
        (piSuccessorCount n cutoff a z : ℝ)) (Finset.mem_univ e)

/-- The reverse local bridge missing from T9.  A definite one-step decrement
forces T9 splitting; the explicit `mu` is obtained by comparing the universal
base-10 lower ratio with the stronger nonsplitting lower ratio. -/
theorem energy_decrement_implies_quantitativeSplittingLevel
    (n cutoff : ℕ) (rho eta : ℝ)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 10)
    (hrhoLower : 1 / 10 < rho)
    (hrhoUpper : rho < (1 - 9 * eta) ^ 2)
    (hdec : (piCylinderCollisionEnergy (n + 1) cutoff : ℝ) ≤
      rho * piCylinderCollisionEnergy n cutoff) :
    QuantitativeSplittingLevel n cutoff
      (((1 - 9 * eta) ^ 2 - rho) /
        ((1 - 9 * eta) ^ 2 - 1 / 10)) eta := by
  classical
  let q : ℝ := (1 - 9 * eta) ^ 2
  let b : ℝ := 1 / 10
  let parentMass : Fin (10 ^ n) → ℝ := fun a =>
    ((piCylinderFiber n cutoff a).card : ℝ) ^ 2
  let splitMass : Fin (10 ^ n) → ℝ := fun a =>
    if QuantitativelySplitParent n cutoff eta a then parentMass a else 0
  let childMass : Fin (10 ^ n) → ℝ := fun a =>
    ∑ e : Fin 10, (piSuccessorCount n cutoff a e : ℝ) ^ 2
  have hrefine : (piCylinderCollisionEnergy (n + 1) cutoff : ℝ) =
      ∑ a, childMass a := by
    dsimp only [childMass]
    exact_mod_cast piCylinderCollisionEnergy_succ_refinement n cutoff
  have hparent : (piCylinderCollisionEnergy n cutoff : ℝ) =
      ∑ a, parentMass a := by
    simp [piCylinderCollisionEnergy, parentMass]
  have hpoint : ∀ a, q * parentMass a - (q - b) * splitMass a ≤
      childMass a := by
    intro a
    by_cases hs : QuantitativelySplitParent n cutoff eta a
    · have hbase := one_tenth_parent_energy_le_successor_energy n cutoff a
      dsimp only [q, b, parentMass, splitMass, childMass]
      simp only [hs, if_true]
      convert hbase using 1
      all_goals ring
    · have hnonsplit := not_splitParent_successor_energy_lower
        n cutoff eta a heta hetaUpper hs
      dsimp only [q, b, parentMass, splitMass, childMass]
      simp only [hs, if_false, mul_zero, sub_zero]
      exact hnonsplit
  have hlower :
      q * (piCylinderCollisionEnergy n cutoff : ℝ) -
          (q - b) * ∑ a, splitMass a ≤
        piCylinderCollisionEnergy (n + 1) cutoff := by
    calc
      q * (piCylinderCollisionEnergy n cutoff : ℝ) -
          (q - b) * ∑ a, splitMass a =
          ∑ a, (q * parentMass a - (q - b) * splitMass a) := by
            rw [hparent, Finset.mul_sum, Finset.mul_sum,
              Finset.sum_sub_distrib]
      _ ≤ ∑ a, childMass a := Finset.sum_le_sum fun a _ => hpoint a
      _ = piCylinderCollisionEnergy (n + 1) cutoff := hrefine.symm
  have hweighted :
      (q - rho) * (piCylinderCollisionEnergy n cutoff : ℝ) ≤
        (q - b) * ∑ a, splitMass a := by
    nlinarith
  have hden : 0 < q - b := by
    dsimp only [q, b]
    linarith
  unfold QuantitativeSplittingLevel
  change ((q - rho) / (q - b)) *
      (piCylinderCollisionEnergy n cutoff : ℝ) ≤ ∑ a, splitMass a
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  simpa [mul_assoc, mul_comm] using hweighted

/-- A level at which normalized collision energy decreases by the fixed
factor `rho`. -/
def PiEnergyDecrementLevel (n cutoff : ℕ) (rho : ℝ) : Prop :=
  normalizedPiCylinderCollisionEnergy (n + 1) cutoff ≤
    rho * normalizedPiCylinderCollisionEnergy n cutoff

/-- Decrement levels `l < m` for one fixed finite prefix. -/
noncomputable def piEnergyDecrementLevels
    (m cutoff : ℕ) (rho : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun l =>
    PiEnergyDecrementLevel l cutoff rho

/-- Number of fixed-factor decrement levels below `m`. -/
noncomputable def piEnergyDecrementCount
    (m cutoff : ℕ) (rho : ℝ) : ℕ :=
  (piEnergyDecrementLevels m cutoff rho).card

theorem piEnergyDecrementCount_succ_of_decrement
    (m cutoff : ℕ) (rho : ℝ)
    (h : PiEnergyDecrementLevel m cutoff rho) :
    piEnergyDecrementCount (m + 1) cutoff rho =
      piEnergyDecrementCount m cutoff rho + 1 := by
  classical
  have hlevels : piEnergyDecrementLevels (m + 1) cutoff rho =
      insert m (piEnergyDecrementLevels m cutoff rho) := by
    ext l
    by_cases hlm : l = m
    · subst l
      simp [piEnergyDecrementLevels, h]
    · simp [piEnergyDecrementLevels, hlm]
      omega
  have hm : m ∉ piEnergyDecrementLevels m cutoff rho := by
    simp [piEnergyDecrementLevels]
  rw [piEnergyDecrementCount, hlevels, piEnergyDecrementCount]
  simp [hm, Nat.add_comm]

theorem piEnergyDecrementCount_succ_of_not_decrement
    (m cutoff : ℕ) (rho : ℝ)
    (h : ¬ PiEnergyDecrementLevel m cutoff rho) :
    piEnergyDecrementCount (m + 1) cutoff rho =
      piEnergyDecrementCount m cutoff rho := by
  classical
  apply congrArg Finset.card
  ext l
  by_cases hlm : l = m
  · subst l
    simp [piEnergyDecrementLevels, h]
  · simp [piEnergyDecrementLevels]
    omega

/-- Multiplicative telescoping lower bound.  Special levels use the universal
ratio `1/10`; every other level has ratio strictly larger than `rho`. -/
theorem decrement_telescope_lower
    (m cutoff : ℕ) (rho : ℝ) (hcutoff : 1 ≤ cutoff) (hrho : 0 < rho) :
    rho ^ m * ((1 / 10 : ℝ) / rho) ^
        piEnergyDecrementCount m cutoff rho ≤
      normalizedPiCylinderCollisionEnergy m cutoff := by
  induction m with
  | zero =>
      rw [piEnergyDecrementCount]
      simp [piEnergyDecrementLevels, normalizedPiCylinderCollisionEnergy,
        piCylinderCollisionEnergy_zero]
      field_simp
      norm_num
  | succ m ih =>
      by_cases hdec : PiEnergyDecrementLevel m cutoff rho
      · have hcount := piEnergyDecrementCount_succ_of_decrement
          m cutoff rho hdec
        rw [hcount, pow_succ, pow_succ]
        have hrearrange :
            (rho ^ m * rho) *
                (((1 / 10 : ℝ) / rho) ^
                  piEnergyDecrementCount m cutoff rho * ((1 / 10) / rho)) =
              (1 / 10 : ℝ) *
                (rho ^ m * ((1 / 10 : ℝ) / rho) ^
                  piEnergyDecrementCount m cutoff rho) := by
          field_simp [hrho.ne']
        rw [hrearrange]
        exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans
          (one_tenth_normalized_energy_le_succ m cutoff hcutoff)
      · have hcount := piEnergyDecrementCount_succ_of_not_decrement
          m cutoff rho hdec
        rw [hcount, pow_succ]
        have hrearrange :
            (rho ^ m * rho) *
                ((1 / 10 : ℝ) / rho) ^
                  piEnergyDecrementCount m cutoff rho =
              rho * (rho ^ m * ((1 / 10 : ℝ) / rho) ^
                piEnergyDecrementCount m cutoff rho) := by ring
        rw [hrearrange]
        have hstrict :
            rho * normalizedPiCylinderCollisionEnergy m cutoff <
              normalizedPiCylinderCollisionEnergy (m + 1) cutoff :=
          lt_of_not_ge hdec
        exact (mul_le_mul_of_nonneg_left ih hrho.le).trans hstrict.le

/-- Normalized and unnormalized decrement inequalities are equivalent at a
positive cutoff, so the local reverse lemma applies to the telescope. -/
theorem normalized_decrement_implies_quantitativeSplittingLevel
    (n cutoff : ℕ) (rho eta : ℝ) (hcutoff : 1 ≤ cutoff)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 10)
    (hrhoLower : 1 / 10 < rho)
    (hrhoUpper : rho < (1 - 9 * eta) ^ 2)
    (hdec : PiEnergyDecrementLevel n cutoff rho) :
    QuantitativeSplittingLevel n cutoff
      (((1 - 9 * eta) ^ 2 - rho) /
        ((1 - 9 * eta) ^ 2 - 1 / 10)) eta := by
  apply energy_decrement_implies_quantitativeSplittingLevel
    n cutoff rho eta heta hetaUpper hrhoLower hrhoUpper
  have hden : 0 < (cutoff : ℝ) ^ 2 := by positivity
  unfold PiEnergyDecrementLevel normalizedPiCylinderCollisionEnergy at hdec
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hden] at hdec
  exact hdec

/-- Every decrement counted by the telescope is a T9 splitting level, by the
proved reverse local bridge rather than an extra assumption. -/
theorem piEnergyDecrementCount_le_piSplittingLevelCount
    (m cutoff : ℕ) (rho eta : ℝ) (hcutoff : 1 ≤ cutoff)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 10)
    (hrhoLower : 1 / 10 < rho)
    (hrhoUpper : rho < (1 - 9 * eta) ^ 2) :
    piEnergyDecrementCount m cutoff rho ≤
      piSplittingLevelCount m cutoff
        (((1 - 9 * eta) ^ 2 - rho) /
          ((1 - 9 * eta) ^ 2 - 1 / 10)) eta := by
  classical
  unfold piEnergyDecrementCount piSplittingLevelCount
  apply Finset.card_le_card
  intro l hl
  simp only [piEnergyDecrementLevels, Finset.mem_filter,
    Finset.mem_range] at hl
  simp only [piSplittingLevels, Finset.mem_filter, Finset.mem_range]
  exact ⟨hl.1, normalized_decrement_implies_quantitativeSplittingLevel
    l cutoff rho eta hcutoff heta hetaUpper hrhoLower hrhoUpper hl.2⟩

/-- The logarithm of the decimal endpoint, used only to convert T9's
multiplicative decrement into T12's decimal-power normalization. -/
theorem log_decimalRadius (m : ℕ) :
    Real.log (decimalRadius m) = -(m : ℝ) * Real.log 10 := by
  rw [decimalRadius_eq_one_tenth_pow, Real.log_pow]
  rw [Real.log_inv]
  ring

theorem log_one_tenth : Real.log (1 / 10 : ℝ) = -Real.log 10 := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (10 : ℝ) ≠ 0)]
  simp

/-- Exponential normalized energy decay forces a positive density of definite
one-step decrements.  This is the quantitative conclusion of the
multiplicative telescope above. -/
theorem exponential_energy_bound_implies_decrement_density
    (m cutoff : ℕ) (beta D rho : ℝ)
    (_hbeta : 0 < beta) (hD : 0 < D)
    (hrhoLower : 1 / 10 < rho) (_hrhoUpper : rho < 1)
    (hrhoBeta : (1 / 10 : ℝ) ^ beta < rho)
    (hcutoff : 1 ≤ cutoff)
    (henergy : normalizedPiCylinderCollisionEnergy m cutoff ≤
      D * (decimalRadius m) ^ beta) :
    ((beta * Real.log 10 + Real.log rho) /
        (Real.log 10 + Real.log rho)) * (m : ℝ) -
      max 0 (Real.log D / (Real.log 10 + Real.log rho)) ≤
        (piEnergyDecrementCount m cutoff rho : ℝ) := by
  have hrho : 0 < rho := (by norm_num : (0 : ℝ) < 1 / 10).trans hrhoLower
  have hratio : 0 < (1 / 10 : ℝ) / rho := div_pos (by norm_num) hrho
  have hlower := decrement_telescope_lower m cutoff rho hcutoff hrho
  have hcombined :
      rho ^ m * ((1 / 10 : ℝ) / rho) ^
          piEnergyDecrementCount m cutoff rho ≤
        D * (decimalRadius m) ^ beta := hlower.trans henergy
  have hleftPos : 0 <
      rho ^ m * ((1 / 10 : ℝ) / rho) ^
        piEnergyDecrementCount m cutoff rho :=
    mul_pos (pow_pos hrho _) (pow_pos hratio _)
  have hlog := Real.log_le_log hleftPos hcombined
  rw [Real.log_mul (pow_ne_zero _ hrho.ne')
      (pow_ne_zero _ hratio.ne'),
    Real.log_pow, Real.log_pow,
    Real.log_mul hD.ne'
      (Real.rpow_pos_of_pos (decimalRadius_pos m) beta).ne',
    Real.log_rpow (decimalRadius_pos m),
    Real.log_div (by norm_num : (1 / 10 : ℝ) ≠ 0) hrho.ne',
    log_one_tenth, log_decimalRadius] at hlog
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log 10 + Real.log rho := by
    have htenrho : 1 < 10 * rho := by nlinarith
    have hp := Real.log_pos htenrho
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hrho.ne'] at hp
    exact hp
  have hnum : 0 < beta * Real.log 10 + Real.log rho := by
    have hbpos : 0 < (1 / 10 : ℝ) := by norm_num
    have hlogs := Real.log_lt_log
      (Real.rpow_pos_of_pos hbpos beta) hrhoBeta
    rw [Real.log_rpow hbpos, log_one_tenth] at hlogs
    nlinarith
  have hmain :
      ((beta * Real.log 10 + Real.log rho) * (m : ℝ) - Real.log D) /
          (Real.log 10 + Real.log rho) ≤
        (piEnergyDecrementCount m cutoff rho : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    ((beta * Real.log 10 + Real.log rho) /
          (Real.log 10 + Real.log rho)) * (m : ℝ) -
        max 0 (Real.log D / (Real.log 10 + Real.log rho)) ≤
      ((beta * Real.log 10 + Real.log rho) /
          (Real.log 10 + Real.log rho)) * (m : ℝ) -
        Real.log D / (Real.log 10 + Real.log rho) := by
          gcongr
          exact le_max_right _ _
    _ = ((beta * Real.log 10 + Real.log rho) * (m : ℝ) - Real.log D) /
          (Real.log 10 + Real.log rho) := by
          field_simp [hden.ne']
    _ ≤ (piEnergyDecrementCount m cutoff rho : ℝ) := hmain

/-- T12 coherent decay supplies fixed splitting parameters on the same
prefixes.  The choices below work for every positive T12 exponent. -/
theorem coherentFinitePrefixDecayAt_implies_coherentPositiveDensitySplittingAt
    (beta D : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hcoh : PiCoherentFinitePrefixDecayAt beta D m0 k0 N nu) :
    ∃ mu eta d B : ℝ,
      PiCoherentPositiveDensitySplittingAt mu eta d B m0 k0 N nu := by
  rcases hcoh with ⟨hbeta, hD, hNmono, hNpos, hnu, henergy⟩
  let t : ℝ := (1 / 10 : ℝ) ^ beta
  let rho : ℝ := (1 + t) / 2
  let eta : ℝ := (1 - rho) / 36
  let q : ℝ := (1 - 9 * eta) ^ 2
  let mu : ℝ := (q - rho) / (q - 1 / 10)
  let d : ℝ := (beta * Real.log 10 + Real.log rho) /
    (Real.log 10 + Real.log rho)
  let B : ℝ := max 0 (Real.log D / (Real.log 10 + Real.log rho))
  have htpos : 0 < t := by
    dsimp only [t]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have htOne : t < 1 := by
    dsimp only [t]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hbeta
  have hrhoHalf : 1 / 2 < rho := by dsimp only [rho]; linarith
  have hrhoLower : 1 / 10 < rho := by linarith
  have hrhoUpper : rho < 1 := by dsimp only [rho]; linarith
  have htRho : t < rho := by dsimp only [rho]; linarith
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaUpper : eta ≤ 1 / 10 := by
    dsimp only [eta]
    have hrhoPos : 0 < rho := hrhoHalf.trans' (by norm_num)
    linarith
  have hqrho : rho < q := by
    have hfactor : q - rho = (1 - rho) * (9 - rho) / 16 := by
      dsimp only [q, eta]
      ring
    rw [← sub_pos, hfactor]
    exact div_pos (mul_pos (sub_pos.mpr hrhoUpper) (by linarith)) (by norm_num)
  have hqden : 0 < q - 1 / 10 := by linarith
  have hmu : 0 < mu := by
    dsimp only [mu]
    exact div_pos (sub_pos.mpr hqrho) hqden
  have hmuUpper : mu < 1 := by
    dsimp only [mu]
    rw [div_lt_one hqden]
    linarith
  have hlogDen : 0 < Real.log 10 + Real.log rho := by
    have htenrho : 1 < 10 * rho := by nlinarith
    have hp := Real.log_pos htenrho
    have hrhoPos : 0 < rho := hrhoHalf.trans' (by norm_num)
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hrhoPos.ne'] at hp
    exact hp
  have hlogNum : 0 < beta * Real.log 10 + Real.log rho := by
    have hbpos : 0 < (1 / 10 : ℝ) := by norm_num
    have hrhoPos : 0 < rho := hrhoHalf.trans' (by norm_num)
    have hlogs := Real.log_lt_log (Real.rpow_pos_of_pos hbpos beta) htRho
    rw [Real.log_rpow hbpos, log_one_tenth] at hlogs
    nlinarith
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos hlogNum hlogDen
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact le_max_left _ _
  refine ⟨mu, eta, d, B, hmu, hmuUpper, heta, hetaUpper, hd, hB,
    hNmono, hNpos, hnu, ?_⟩
  intro k hk m hm hmk
  have hdecrements := exponential_energy_bound_implies_decrement_density
    m (N k) beta D rho hbeta hD hrhoLower hrhoUpper htRho
      (hNpos k) (henergy k hk m hm hmk)
  have hsubset := piEnergyDecrementCount_le_piSplittingLevelCount
    m (N k) rho eta (hNpos k) heta hetaUpper hrhoLower hqrho
  have hsubsetReal : (piEnergyDecrementCount m (N k) rho : ℝ) ≤
      (piSplittingLevelCount m (N k) mu eta : ℝ) := by
    exact_mod_cast (show piEnergyDecrementCount m (N k) rho ≤
      piSplittingLevelCount m (N k) mu eta by
        simpa [mu, q] using hsubset)
  exact (show d * (m : ℝ) - B ≤
      (piEnergyDecrementCount m (N k) rho : ℝ) by
        simpa [d, B] using hdecrements).trans hsubsetReal

/-- C2 gives coherent positive-density splitting.  T12 first supplies the
coherent energy rows, then the proved telescope and reverse local lemma supply
the splitting counts. -/
theorem piPolynomialSmallBallC2_implies_coherentPositiveDensitySplitting
    (hC2 : PiPolynomialSmallBallC2) :
    PiCoherentPositiveDensitySplitting := by
  rcases piPolynomialSmallBallC2_implies_coherentFinitePrefixDecay hC2 with
    ⟨beta, D, m0, k0, N, nu, hcoh⟩
  obtain ⟨mu, eta, d, B, hsplit⟩ :=
    coherentFinitePrefixDecayAt_implies_coherentPositiveDensitySplittingAt
      beta D m0 k0 N nu hcoh
  exact ⟨mu, eta, d, B, m0, k0, N, nu, hsplit⟩

/-- A linear lower bound for T9 splitting counts gives a polynomial decimal
energy bound with explicit exponent and additive-defect constant. -/
theorem splittingCount_bound_implies_normalized_energy_bound
    (m cutoff : ℕ) (mu eta d B : ℝ)
    (hmu : 0 < mu) (heta : 0 < eta) (hproduct : mu * eta < 1)
    (hcutoff : 1 ≤ cutoff)
    (hcount : d * (m : ℝ) - B ≤
      (piSplittingLevelCount m cutoff mu eta : ℝ)) :
    normalizedPiCylinderCollisionEnergy m cutoff ≤
      (1 - mu * eta) ^ (-B) *
        (decimalRadius m) ^
          (-d * Real.log (1 - mu * eta) / Real.log 10) := by
  let q : ℝ := 1 - mu * eta
  have hqpos : 0 < q := by dsimp [q]; linarith
  have hqle : q ≤ 1 := by
    dsimp [q]
    have : 0 ≤ mu * eta := mul_nonneg hmu.le heta.le
    linarith
  have hraw := energy_le_decrement_pow_splittingLevelCount
    m cutoff mu eta hmu heta hproduct.le
  have hcutoffReal : 0 < (cutoff : ℝ) ^ 2 := by positivity
  have hnormalized : normalizedPiCylinderCollisionEnergy m cutoff ≤
      q ^ piSplittingLevelCount m cutoff mu eta := by
    unfold normalizedPiCylinderCollisionEnergy
    rw [div_le_iff₀ hcutoffReal]
    simpa [q, mul_assoc, mul_comm] using hraw
  have hpower : q ^ piSplittingLevelCount m cutoff mu eta ≤
      q ^ (d * (m : ℝ) - B) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hqpos hqle hcount
  refine hnormalized.trans (hpower.trans_eq ?_)
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hqpos,
    Real.rpow_def_of_pos (decimalRadius_pos m), ← Real.exp_add]
  congr 1
  rw [log_decimalRadius]
  field_simp [hlogTen.ne']
  ring

/-- Coherent positive-density splitting implies T12 coherent finite-prefix
decay on the identical prefixes and finite triangles. -/
theorem coherentPositiveDensitySplittingAt_implies_coherentFinitePrefixDecayAt
    (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hsplit : PiCoherentPositiveDensitySplittingAt
      mu eta d B m0 k0 N nu) :
    PiCoherentFinitePrefixDecayAt
      (-d * Real.log (1 - mu * eta) / Real.log 10)
      ((1 - mu * eta) ^ (-B)) m0 k0 N nu := by
  rcases hsplit with
    ⟨hmu, hmuUpper, heta, hetaUpper, hd, hB, hNmono, hNpos, hnu, hcount⟩
  have hproduct : mu * eta < 1 := by
    have hetaOne : eta < 1 := hetaUpper.trans_lt (by norm_num)
    nlinarith
  have hqpos : 0 < 1 - mu * eta := by linarith
  have hqOne : 1 - mu * eta < 1 := by
    have := mul_pos hmu heta
    linarith
  have hlogq : Real.log (1 - mu * eta) < 0 :=
    Real.log_neg hqpos hqOne
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hbeta : 0 < -d * Real.log (1 - mu * eta) / Real.log 10 := by
    have hnum : 0 < -d * Real.log (1 - mu * eta) := by
      nlinarith [mul_pos hd (neg_pos.mpr hlogq)]
    exact div_pos hnum hlogTen
  refine ⟨hbeta, Real.rpow_pos_of_pos hqpos _, hNmono, hNpos, hnu, ?_⟩
  intro k hk m hm hmk
  exact splittingCount_bound_implies_normalized_energy_bound
    m (N k) mu eta d B hmu heta hproduct (hNpos k)
      (hcount k hk m hm hmk)

/-- The splitting condition implies the agenda's open C2 hypothesis. -/
theorem coherentPositiveDensitySplitting_implies_piPolynomialSmallBallC2
    (hsplit : PiCoherentPositiveDensitySplitting) :
    PiPolynomialSmallBallC2 := by
  rcases hsplit with ⟨mu, eta, d, B, m0, k0, N, nu, hsplit⟩
  apply coherentFinitePrefixDecay_implies_piPolynomialSmallBallC2
  exact ⟨-d * Real.log (1 - mu * eta) / Real.log 10,
    (1 - mu * eta) ^ (-B), m0, k0, N, nu,
    coherentPositiveDensitySplittingAt_implies_coherentFinitePrefixDecayAt
      mu eta d B m0 k0 N nu hsplit⟩

/-- Exact coherent local-splitting characterization of the agenda's open C2
hypothesis.  Neither side is asserted unconditionally for pi. -/
theorem piPolynomialSmallBallC2_iff_coherentPositiveDensitySplitting :
    PiPolynomialSmallBallC2 ↔ PiCoherentPositiveDensitySplitting :=
  ⟨piPolynomialSmallBallC2_implies_coherentPositiveDensitySplitting,
    coherentPositiveDensitySplitting_implies_piPolynomialSmallBallC2⟩

/-- Literal quantified failure of coherent splitting, hence of C2.  Every
fixed admissible parameter tuple and every candidate coherent prefix sequence
has a bad finite triangle entry. -/
theorem not_piPolynomialSmallBallC2_iff_quantified_splitting_failure :
    ¬ PiPolynomialSmallBallC2 ↔
      ∀ (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
        (nu : ProbabilityMeasure UnitAddCircle),
        0 < mu → mu < 1 → 0 < eta → eta ≤ 1 / 10 →
        0 < d → 0 ≤ B → StrictMono N → (∀ k, 0 < N k) →
        Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 nu) →
        ∃ k : ℕ, k0 ≤ k ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ k ∧
          (piSplittingLevelCount m (N k) mu eta : ℝ) <
            d * (m : ℝ) - B := by
  constructor
  · intro hnot mu eta d B m0 k0 N nu hmu hmuUpper heta hetaUpper
      hd hB hNmono hNpos hnu
    by_contra hnone
    apply hnot
    apply coherentPositiveDensitySplitting_implies_piPolynomialSmallBallC2
    refine ⟨mu, eta, d, B, m0, k0, N, nu, hmu, hmuUpper, heta,
      hetaUpper, hd, hB, hNmono, hNpos, hnu, ?_⟩
    intro k hk m hm hmk
    apply le_of_not_gt
    intro hbad
    apply hnone
    exact ⟨k, hk, m, hm, hmk, hbad⟩
  · intro hfailure hC2
    obtain ⟨mu, eta, d, B, m0, k0, N, nu, hsplit⟩ :=
      piPolynomialSmallBallC2_implies_coherentPositiveDensitySplitting hC2
    rcases hsplit with
      ⟨hmu, hmuUpper, heta, hetaUpper, hd, hB, hNmono, hNpos, hnu, hcount⟩
    obtain ⟨k, hk, m, hm, hmk, hbad⟩ := hfailure
      mu eta d B m0 k0 N nu hmu hmuUpper heta hetaUpper hd hB
        hNmono hNpos hnu
    exact (not_lt_of_ge (hcount k hk m hm hmk)) hbad

/-- Failure of C2 gives a bad triangular splitting count and, at each
nonsplitting level in that row, exactly T9's energy-weighted
dominant-successor conclusion.  No common or nested branch is claimed. -/
theorem not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance
    (hnot : ¬ PiPolynomialSmallBallC2)
    (mu eta d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hmu : 0 < mu) (hmuUpper : mu < 1)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 10)
    (hd : 0 < d) (hB : 0 ≤ B)
    (hNmono : StrictMono N) (hNpos : ∀ k, 0 < N k)
    (hnu : Tendsto (fun k => piDecimalEmpiricalMeasure (N k))
      atTop (𝓝 nu)) :
    ∃ k : ℕ, k0 ≤ k ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ k ∧
      (piSplittingLevelCount m (N k) mu eta : ℝ) <
        d * (m : ℝ) - B ∧
      ∀ l ∈ Finset.range m,
        ¬ QuantitativeSplittingLevel l (N k) mu eta →
          (1 - mu) * piCylinderCollisionEnergy l (N k) <
            piDominantSuccessorEnergy l (N k) eta := by
  obtain ⟨k, hk, m, hm, hmk, hbad⟩ :=
    not_piPolynomialSmallBallC2_iff_quantified_splitting_failure.mp hnot
      mu eta d B m0 k0 N nu hmu hmuUpper heta hetaUpper hd hB
        hNmono hNpos hnu
  refine ⟨k, hk, m, hm, hmk, hbad, ?_⟩
  intro l _hl hnonsplit
  exact not_splittingLevel_dominant_energy_concentration
    l (N k) mu eta hmu hmuUpper heta hetaUpper hnonsplit

end DecimalFactorComplexity.CoherentSuccessorSplitting

#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.one_tenth_energy_le_energy_succ
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.piCoherentPositiveDensitySplittingAt_iff_quantifiers
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.energy_decrement_implies_quantitativeSplittingLevel
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.decrement_telescope_lower
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.exponential_energy_bound_implies_decrement_density
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.coherentFinitePrefixDecayAt_implies_coherentPositiveDensitySplittingAt
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.coherentPositiveDensitySplittingAt_implies_coherentFinitePrefixDecayAt
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.piPolynomialSmallBallC2_implies_coherentPositiveDensitySplitting
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.coherentPositiveDensitySplitting_implies_piPolynomialSmallBallC2
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.piPolynomialSmallBallC2_iff_coherentPositiveDensitySplitting
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.not_piPolynomialSmallBallC2_iff_quantified_splitting_failure
#print axioms DecimalFactorComplexity.CoherentSuccessorSplitting.not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance
