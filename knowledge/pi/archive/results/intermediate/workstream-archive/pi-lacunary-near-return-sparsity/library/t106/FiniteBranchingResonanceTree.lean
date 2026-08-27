import TheoryLib.PiLacunaryNearReturnSparsity.T13IteratedLagResonance
import TheoryLib.PiLacunaryNearReturnSparsity.T24FiniteInverseDichotomy
import TheoryLib.PiLacunaryNearReturnSparsity.T26SharedResonanceChain
import TheoryLib.PiLacunaryNearReturnSparsity.T73ManyChildResonance

/-!
# T106: finite branching resonance trees

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The agenda's C1 is source-canonical A1, not source sibling A10. Everything
below is a necessary consequence of the literal negation of canonical C1.
No result asserts compatibility between distinct nodes, an irrationality
contradiction, or a positive canonical-C1 conclusion.
-/

noncomputable section

open Finset
open scoped ComplexConjugate Real

namespace DecimalFactorComplexity.FiniteBranchingResonanceTreeT106

open IteratedLagResonance
open FiniteInverseDichotomy
open ManyChildResonanceT73

/-- The explicit T24 threshold at density denominator `D`. -/
def nodeTau (D : ℕ) : ℝ := 1 / (8 * (D : ℝ) ^ 2)

/-- The literal T24 cycle-or-positive-preperiod alternative. -/
def NodeT24Witness (c : ℝ) (D M : ℕ) : Prop :=
  (∃ s : ℕ, 1 ≤ s ∧ s < M ∧
      EventuallyPeriodicApproximation c (nodeTau D) 0 s) ∨
    (¬ (∃ s : ℕ, 1 ≤ s ∧ s < M ∧
        EventuallyPeriodicApproximation c (nodeTau D) 0 s) ∧
      ∃ j s : ℕ, 1 ≤ j ∧ 1 ≤ s ∧ j + s < M ∧
        EventuallyPeriodicApproximation c (nodeTau D) j s)

/-- A recursive request paying for T24 at each node and T73 at each edge. -/
def treeLengthThreshold (D B branching forbiddenCard : ℕ) : ℕ → ℕ
  | 0 => 2 * D ^ 2
  | depth + 1 =>
      let childRequest := treeLengthThreshold
        (nextDensityDenominator D) B branching (forbiddenCard + 1) depth
      max (2 * D ^ 2)
        (8 * D ^ 2 * (branching + B + forbiddenCard + childRequest + 3))

/-- Every recursive tree request is positive when its density is positive. -/
theorem treeLengthThreshold_pos (D B branching forbiddenCard depth : ℕ)
    (hD : 1 ≤ D) :
    1 ≤ treeLengthThreshold D B branching forbiddenCard depth := by
  cases depth with
  | zero =>
      simp only [treeLengthThreshold]
      have : 0 < 2 * D ^ 2 := by positivity
      omega
  | succ depth =>
      simp only [treeLengthThreshold]
      apply (show 1 ≤ 2 * D ^ 2 by
        have : 0 < 2 * D ^ 2 := by positivity
        omega).trans
      exact le_max_left _ _

/-- A finite tree containing all T73-good children at every internal node. -/
inductive ResonanceTree (B branching : ℕ) :
    (depth : ℕ) → (c : ℝ) → (M D : ℕ) → (F : Finset ℕ) → Type
  | leaf {c M D F}
      (density_pos : 1 ≤ D)
      (recursive_length : treeLengthThreshold D B branching F.card 0 ≤ M)
      (resonance : (M : ℝ) / D <
        ‖∑ j ∈ range M, geometricPhase c j‖)
      (inverse_witness : NodeT24Witness c D M) :
      ResonanceTree B branching 0 c M D F
  | branch {depth c M D F}
      (density_pos : 1 ≤ D)
      (recursive_length :
        treeLengthThreshold D B branching F.card (depth + 1) ≤ M)
      (resonance : (M : ℝ) / D <
        ‖∑ j ∈ range M, geometricPhase c j‖)
      (inverse_witness : NodeT24Witness c D M)
      (child_cardinality : branching ≤
        (goodMiddleShifts (geometricPhase c) M D B
          (treeLengthThreshold (nextDensityDenominator D) B branching
            (F.card + 1) depth) F).card)
      (child_legal : ∀ s ∈
          goodMiddleShifts (geometricPhase c) M D B
            (treeLengthThreshold (nextDensityDenominator D) B branching
              (F.card + 1) depth) F,
        B ≤ s ∧
        s ≤ M - treeLengthThreshold (nextDensityDenominator D) B branching
          (F.card + 1) depth ∧
        s ∉ F ∧
        treeLengthThreshold (nextDensityDenominator D) B branching
          (F.card + 1) depth ≤ M - s ∧
        ((M - s : ℕ) : ℝ) / nextDensityDenominator D <
          ‖∑ j ∈ range (M - s),
            geometricPhase (c * ((10 : ℝ) ^ s - 1)) j‖)
      (child_tree : ∀ s, (hs : s ∈
          goodMiddleShifts (geometricPhase c) M D B
            (treeLengthThreshold (nextDensityDenominator D) B branching
              (F.card + 1) depth) F) →
        ResonanceTree B branching depth
          (c * ((10 : ℝ) ^ s - 1)) (M - s)
          (nextDensityDenominator D) (insert s F)) :
      ResonanceTree B branching (depth + 1) c M D F

/-- T24 supplies the literal witness at one sufficiently long resonant node. -/
theorem resonance_implies_nodeT24Witness
    (c : ℝ) (M D : ℕ) (hD : 1 ≤ D) (hM : 2 * D ^ 2 ≤ M)
    (hlarge : (M : ℝ) / D <
      ‖∑ j ∈ range M, geometricPhase c j‖) :
    NodeT24Witness c D M := by
  have hDreal : 0 < (D : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have htauPos : 0 < nodeTau D := by
    unfold nodeTau
    positivity
  have htauDelta : nodeTau D < (D : ℝ)⁻¹ := by
    have hlocal : 1 / (8 * (D : ℝ) ^ 2) < 1 / (D : ℝ) := by
      apply one_div_lt_one_div_of_lt hDreal
      nlinarith
    simpa [nodeTau, one_div] using hlocal
  have hdeltaOne : (D : ℝ)⁻¹ ≤ 1 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hDone)
  have henergy := stage_energy_inequality D M hD hM
  have hlarge' : (D : ℝ)⁻¹ * (M : ℝ) <
      ‖∑ j ∈ range M, geometricPhase c j‖ := by
    simpa [div_eq_mul_inv, mul_comm] using hlarge
  simpa [NodeT24Witness, CycleApproximation,
      PositivePreperiodApproximation] using
    finite_cycle_or_positivePreperiod_inverse c (D : ℝ)⁻¹
      (nodeTau D) M htauPos htauDelta hdeltaOne
      (by simpa [nodeTau] using henergy) hlarge'

/-- The explicit parent threshold forces the requested T73 cardinality. -/
theorem branching_le_goodMiddleShifts_card
    (c : ℝ) (M D B branching R : ℕ) (F : Finset ℕ)
    (hD : 1 ≤ D) (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hscale : 8 * D ^ 2 * (branching + B + F.card + R + 3) ≤ M)
    (hlarge : (M : ℝ) / D <
      ‖∑ j ∈ range M, geometricPhase c j‖) :
    branching ≤
      (goodMiddleShifts (geometricPhase c) M D B R F).card := by
  have hz : ∀ j, ‖geometricPhase c j‖ = 1 := by
    intro j
    simpa [geometricPhase, Theory.PiDigits.T27.phase] using
      Theory.PiDigits.T27.norm_phase (1 : ℤ) ((10 : ℝ) ^ j * c)
  have hlower := goodMiddleShifts_card_lower
    (geometricPhase c) M D B R F hz hD hB hR hlarge
  have hden : 0 < 8 * (D : ℝ) ^ 2 := by positivity
  have hscaleReal :
      8 * (D : ℝ) ^ 2 *
          (((branching + B + F.card + R + 3 : ℕ) : ℝ)) ≤ (M : ℝ) := by
    exact_mod_cast hscale
  have hbase :
      (((branching + B + F.card + R + 3 : ℕ) : ℝ)) ≤
        (M : ℝ) / (8 * (D : ℝ) ^ 2) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaleReal)
  have hbranchLower : (branching : ℝ) ≤
      3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
        ((B + F.card + R : ℕ) : ℝ) := by
    have hcoarse : (branching : ℝ) ≤
        3 * (((branching + B + F.card + R + 3 : ℕ) : ℝ)) -
          1 / 2 - ((B + F.card + R : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add]
      have hb : 0 ≤ (branching : ℝ) := Nat.cast_nonneg branching
      have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
      have hF : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg F.card
      have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith
    calc
      (branching : ℝ) ≤
          3 * (((branching + B + F.card + R + 3 : ℕ) : ℝ)) -
            1 / 2 - ((B + F.card + R : ℕ) : ℝ) := hcoarse
      _ ≤ 3 * ((M : ℝ) / (8 * (D : ℝ) ^ 2)) -
            1 / 2 - ((B + F.card + R : ℕ) : ℝ) := by linarith
      _ = 3 * (M : ℝ) / (8 * (D : ℝ) ^ 2) - 1 / 2 -
            ((B + F.card + R : ℕ) : ℝ) := by ring
  have hcardReal : (branching : ℝ) <
      ((goodMiddleShifts (geometricPhase c) M D B R F).card : ℝ) :=
    hbranchLower.trans_lt hlower
  exact_mod_cast hcardReal.le

/-- Every tree carries a T24 witness independently at every node. -/
def ResonanceTree.NodewiseT24Witness :
    {B branching depth M D : ℕ} → {c : ℝ} → {F : Finset ℕ} →
      ResonanceTree B branching depth c M D F → Prop
  | _, _, 0, M, D, c, _, .leaf _ _ _ _ => NodeT24Witness c D M
  | B, branching, depth + 1, M, D, c, _,
      .branch _ _ _ witness _ _ children =>
      NodeT24Witness c D M ∧
        ∀ s hs, (children s hs).NodewiseT24Witness

/-- Every internal node has the requested number of T73-good children. -/
def ResonanceTree.NodewiseChildCardinality :
    {B branching depth M D : ℕ} → {c : ℝ} → {F : Finset ℕ} →
      ResonanceTree B branching depth c M D F → Prop
  | _, _, 0, _, _, _, _, .leaf _ _ _ _ => True
  | B, branching, depth + 1, M, D, c, F,
      .branch _ _ _ _ childCard _ children =>
      branching ≤
          (goodMiddleShifts (geometricPhase c) M D B
            (treeLengthThreshold (nextDensityDenominator D) B branching
              (F.card + 1) depth) F).card ∧
        ∀ s hs, (children s hs).NodewiseChildCardinality

theorem ResonanceTree.nodewise_t24_witness
    {B branching depth M D : ℕ} {c : ℝ} {F : Finset ℕ}
    (tree : ResonanceTree B branching depth c M D F) :
    tree.NodewiseT24Witness := by
  induction tree with
  | leaf hD hM hlarge hwitness => exact hwitness
  | branch hD hM hlarge hwitness hcard hlegal children ih =>
      exact ⟨hwitness, ih⟩

theorem ResonanceTree.nodewise_child_cardinality
    {B branching depth M D : ℕ} {c : ℝ} {F : Finset ℕ}
    (tree : ResonanceTree B branching depth c M D F) :
    tree.NodewiseChildCardinality := by
  induction tree with
  | leaf hD hM hlarge hwitness => trivial
  | branch hD hM hlarge hwitness hcard hlegal children ih =>
      exact ⟨hcard, ih⟩

/-- A sufficiently long resonant parent supplies the full finite tree. -/
theorem exists_resonanceTree
    (B branching depth : ℕ) (c : ℝ) (M D : ℕ) (F : Finset ℕ)
    (hB : 1 ≤ B) (hbranching : 1 ≤ branching) (hD : 1 ≤ D)
    (hM : treeLengthThreshold D B branching F.card depth ≤ M)
    (hlarge : (M : ℝ) / D <
      ‖∑ j ∈ range M, geometricPhase c j‖) :
    Nonempty (ResonanceTree B branching depth c M D F) := by
  induction depth generalizing c M D F with
  | zero =>
      have hwitness := resonance_implies_nodeT24Witness c M D hD
        (by simpa [treeLengthThreshold] using hM) hlarge
      exact ⟨.leaf hD hM hlarge hwitness⟩
  | succ depth ih =>
      let R := treeLengthThreshold (nextDensityDenominator D) B branching
        (F.card + 1) depth
      have hR : 1 ≤ R := treeLengthThreshold_pos
        (nextDensityDenominator D) B branching (F.card + 1) depth
          (nextDensityDenominator_pos D hD)
      have hMtwo : 2 * D ^ 2 ≤ M := by
        exact (le_max_left _ _).trans (by
          simpa [treeLengthThreshold, R] using hM)
      have hscale :
          8 * D ^ 2 * (branching + B + F.card + R + 3) ≤ M := by
        exact (le_max_right _ _).trans (by
          simpa [treeLengthThreshold, R] using hM)
      have hwitness := resonance_implies_nodeT24Witness c M D hD hMtwo hlarge
      have hcard := branching_le_goodMiddleShifts_card
        c M D B branching R F hD hB hR hscale hlarge
      have hlegal : ∀ s ∈
          goodMiddleShifts (geometricPhase c) M D B R F,
          B ≤ s ∧ s ≤ M - R ∧ s ∉ F ∧ R ≤ M - s ∧
            ((M - s : ℕ) : ℝ) / nextDensityDenominator D <
              ‖∑ j ∈ range (M - s),
                geometricPhase (c * ((10 : ℝ) ^ s - 1)) j‖ := by
        intro s hs
        have hsChild := goodGeometricMiddleShift_child_resonance
          c M D B R F s hB hs
        simpa [nextDensityDenominator] using
          ⟨hsChild.1, hsChild.2.1, hsChild.2.2.1,
            hsChild.2.2.2.1, hsChild.2.2.2.2.2⟩
      have hchildren : ∀ s, (hs : s ∈
          goodMiddleShifts (geometricPhase c) M D B R F) →
          Nonempty (ResonanceTree B branching depth
            (c * ((10 : ℝ) ^ s - 1)) (M - s)
            (nextDensityDenominator D) (insert s F)) := by
        intro s hs
        have hsLegal := hlegal s hs
        have hcardInsert : (insert s F).card = F.card + 1 :=
          card_insert_of_notMem hsLegal.2.2.1
        apply ih (c * ((10 : ℝ) ^ s - 1)) (M - s)
          (nextDensityDenominator D) (insert s F)
          (nextDensityDenominator_pos D hD)
        · rw [hcardInsert]
          exact hsLegal.2.2.2.1
        · exact hsLegal.2.2.2.2
      exact ⟨.branch hD hM hlarge hwitness
        (by simpa [R] using hcard)
        (by simpa [R] using hlegal)
        (fun s hs => Classical.choice (hchildren s (by simpa [R] using hs)))⟩

/-- T13's initial density denominator, explicit in the final theorem. -/
def initialDensity (A n : ℕ) : ℕ := 131072 * A ^ 2 * n ^ 2

/-- T13's initial real phase coefficient, explicit in the final theorem. -/
def initialCoefficient (h r : ℕ) : ℝ :=
  (h : ℝ) * ((10 : ℝ) ^ r - 1) * Real.pi

/-- Literal failure of canonical C1 supplies arbitrary finite branching trees.
Node witnesses are independent and no compatibility is asserted. -/
theorem literal_not_canonical_C1_implies_finite_branching_resonanceTree
    (hnotC1 : ¬ (∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n0 : ℕ, 1 ≤ n0 →
      ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧
        ∀ depth branching : ℕ, 1 ≤ branching →
          let D := initialDensity A n
          let K := treeLengthThreshold D 1 branching 1 depth
          ∃ N r h : ℕ,
            N = 16 * A * n * K ∧
            r ∈ Icc 1 (N - 1) ∧
            h ∈ Icc 1 (256 * A * n) ∧
            K ≤ N - r ∧
            ((N - r : ℕ) : ℝ) / D <
              ‖∑ j ∈ range (N - r),
                geometricPhase (initialCoefficient h r) j‖ ∧
            ∃ tree : ResonanceTree 1 branching depth
                (initialCoefficient h r) (N - r) D {r},
              tree.NodewiseChildCardinality ∧
              tree.NodewiseT24Witness := by
  obtain ⟨A, hA, hinitial⟩ :=
    literal_not_A1_implies_arbitrarily_long_initial_resonance hnotC1
  refine ⟨A, hA, ?_⟩
  intro n0 hn0
  obtain ⟨n, hn0n, hn, hinitialn⟩ := hinitial n0 hn0
  refine ⟨n, hn0n, hn, ?_⟩
  intro depth branching hbranching
  let D := initialDensity A n
  let K := treeLengthThreshold D 1 branching 1 depth
  have hD : 1 ≤ D := by
    dsimp [D, initialDensity]
    have : 0 < 131072 * A ^ 2 * n ^ 2 := by positivity
    omega
  have hK : 1 ≤ K := treeLengthThreshold_pos D 1 branching 1 depth hD
  obtain ⟨N, r, h, hN, hr, hKlength, hh, hresonanceRaw⟩ :=
    hinitialn K hK
  let c := initialCoefficient h r
  have hphase (j : ℕ) :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
            (((10 : ℝ) ^ j * ((10 : ℝ) ^ r - 1) * Real.pi : ℝ) : ℂ)) =
        geometricPhase c j := by
    unfold geometricPhase c initialCoefficient
    congr 1
    push_cast
    ring
  have hDcast : (D : ℝ) =
      131072 * (A : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    dsimp [D, initialDensity]
    push_cast
    ring
  have hresonance : ((N - r : ℕ) : ℝ) / D <
      ‖∑ j ∈ range (N - r), geometricPhase c j‖ := by
    rw [hDcast]
    simpa only [hphase] using hresonanceRaw
  obtain ⟨tree⟩ := exists_resonanceTree 1 branching depth c (N - r) D {r}
    (by norm_num) hbranching hD (by simpa [K] using hKlength) hresonance
  refine ⟨N, r, h, ?_, hr, hh, ?_, ?_, ?_⟩
  · simpa [K] using hN
  · simpa [K] using hKlength
  · simpa [c] using hresonance
  · let tree' : ResonanceTree 1 branching depth
        (initialCoefficient h r) (N - r) D {r} := by
      simpa [c] using tree
    exact ⟨tree', tree'.nodewise_child_cardinality,
      tree'.nodewise_t24_witness⟩

end DecimalFactorComplexity.FiniteBranchingResonanceTreeT106

#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.treeLengthThreshold_pos
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.resonance_implies_nodeT24Witness
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.branching_le_goodMiddleShifts_card
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.ResonanceTree.nodewise_t24_witness
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.ResonanceTree.nodewise_child_cardinality
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.exists_resonanceTree
#print axioms DecimalFactorComplexity.FiniteBranchingResonanceTreeT106.literal_not_canonical_C1_implies_finite_branching_resonanceTree
