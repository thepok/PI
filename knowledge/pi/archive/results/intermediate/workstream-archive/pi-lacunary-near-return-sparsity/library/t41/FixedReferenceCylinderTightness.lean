import TheoryLib.PiLacunaryNearReturnSparsity.T29FiniteCountTreeLeakage
import TheoryLib.PiLacunaryNearReturnSparsity.T33MovingRootTangent
import TheoryLib.PiLacunaryNearReturnSparsity.T37ArtificialStreamObstruction

/-!
# T41: fixed-reference cylinder tightness prevents moving-root escape

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves an abstract decimal-tree interface. It is an A14 sibling,
not a theorem about the decimal expansion of `Real.pi`. It makes no assertion
of C2 or canonical A1.
-/

noncomputable section

open Finset MeasureTheory

namespace DecimalFactorComplexity.FixedReferenceCylinderTightnessT41

open DecimalFactorComplexity.FiniteCountTreeLeakage

/-- Decimal cylinders at absolute depth `n`. -/
abbrev DecimalNode (n : ℕ) := Fin (10 ^ n)

/-- The absolute depth-`n` decimal cylinder encoded by T37's proved numeric
word decoder. -/
def decimalCylinder (n : ℕ) (a : DecimalNode n) : Set (ℕ → Fin 10) :=
  {x | ∀ i : Fin n,
    x i = ArtificialStreamObstruction.decodedTuple n a i}

/-- A probability measure presented by all of its finite decimal-cylinder
masses. Nonnegativity, unit root mass, and exact child conservation are the
projective probability axioms used by this module. -/
structure DecimalCylinderProbability where
  probabilityMeasure : ProbabilityMeasure (ℕ → Fin 10)
  mass : (n : ℕ) → DecimalNode n → ℝ
  mass_eq_measure : ∀ n a,
    mass n a = ENNReal.toReal (probabilityMeasure (decimalCylinder n a))
  nonneg : ∀ n a, 0 ≤ mass n a
  root_mass : ∀ a : DecimalNode 0, mass 0 a = 1
  conservation : ∀ n a,
    mass n a = ∑ d : Fin 10, mass (n + 1) (decimalChild n a d)

/-- An explicit cylinder-tightness modulus for one fixed reference
probability. The modulus is antitone in the absolute cylinder depth. -/
structure CylinderTightness (reference : DecimalCylinderProbability) where
  modulus : ℕ → ℝ
  modulus_nonneg : ∀ n, 0 ≤ modulus n
  antitone : Antitone modulus
  cylinder_mass_le : ∀ n a, reference.mass n a ≤ modulus n

/-- One changing finite row. The count is unnormalized; its root and displayed
depth range `[startDepth, startDepth + windowLength]` are explicit. -/
structure FiniteCylinderRow where
  count : (n : ℕ) → DecimalNode n → ℝ
  startDepth : ℕ
  windowLength : ℕ
  root : DecimalNode startDepth

/-- Uniform comparison and positive unnormalized root mass for changing rows.
The constants and the cutoff inequality are all outside the row quantifier. -/
def FixedReferenceControl
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ)
    (rows : ℕ → FiniteCylinderRow) : Prop :=
  0 ≤ comparisonConstant ∧
  0 < rootThreshold ∧
  comparisonConstant * tightness.modulus (startBound + 1) < rootThreshold ∧
  ∀ q : ℕ,
    rootThreshold ≤ (rows q).count (rows q).startDepth (rows q).root ∧
    ∀ n : ℕ, (rows q).startDepth ≤ n →
      n ≤ (rows q).startDepth + (rows q).windowLength →
      ∀ a : DecimalNode n,
        (rows q).count n a ≤ comparisonConstant * reference.mass n a

/-- The complete fixed-reference interface with every constant, row range,
root threshold, and cylinder comparison quantifier visible. -/
theorem fixedReferenceControl_iff_quantifiers
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ)
    (rows : ℕ → FiniteCylinderRow) :
    FixedReferenceControl reference tightness comparisonConstant
        rootThreshold startBound rows ↔
      0 ≤ comparisonConstant ∧
      0 < rootThreshold ∧
      comparisonConstant * tightness.modulus (startBound + 1) < rootThreshold ∧
      ∀ q : ℕ,
        rootThreshold ≤ (rows q).count (rows q).startDepth (rows q).root ∧
        ∀ n : ℕ, (rows q).startDepth ≤ n →
          n ≤ (rows q).startDepth + (rows q).windowLength →
          ∀ a : DecimalNode n,
            (rows q).count n a ≤ comparisonConstant * reference.mass n a :=
  Iff.rfl

/-- Quantitative moving-root bound. A root deeper than `startBound` would have
reference mass at most `modulus (startBound+1)`, contradicting its fixed
positive unnormalized row mass after comparison. -/
theorem movingRoot_startDepth_le
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ)
    (rows : ℕ → FiniteCylinderRow)
    (hcontrol : FixedReferenceControl reference tightness comparisonConstant
      rootThreshold startBound rows) (q : ℕ) :
    (rows q).startDepth ≤ startBound := by
  rcases hcontrol with
    ⟨hcomparisonNonneg, _hthresholdPos, hcutoff, hrows⟩
  by_contra hnot
  have hdepth : startBound + 1 ≤ (rows q).startDepth := by omega
  have hrow := hrows q
  have hcompare := hrow.2 (rows q).startDepth (le_refl _)
    (Nat.le_add_right _ _) (rows q).root
  have hcylinder := tightness.cylinder_mass_le
    (rows q).startDepth (rows q).root
  have hmodulus := tightness.antitone hdepth
  have hscaledCylinder :
      comparisonConstant * reference.mass (rows q).startDepth (rows q).root ≤
        comparisonConstant * tightness.modulus (rows q).startDepth :=
    mul_le_mul_of_nonneg_left hcylinder hcomparisonNonneg
  have hscaledModulus :
      comparisonConstant * tightness.modulus (rows q).startDepth ≤
        comparisonConstant * tightness.modulus (startBound + 1) :=
    mul_le_mul_of_nonneg_left hmodulus hcomparisonNonneg
  linarith

/-- The fixed original-coordinate predicate used for every row and every path
length. It records literal decimal append, positive parent mass, and the same
fixed retention factor `alpha`. -/
def ReferenceDominantEdge (reference : DecimalCylinderProbability)
    (alpha : ℝ) (n : ℕ) (a : DecimalNode n) (b : DecimalNode (n + 1)) : Prop :=
  0 < reference.mass n a ∧
  ∃ d : Fin 10, b = decimalChild n a d ∧
    alpha * reference.mass n a ≤ reference.mass (n + 1) b

/-- A finite changing row carrying a good prefix for the one fixed reference
edge predicate. The prefix has exactly `windowLength` edges and starts at the
explicit absolute `startDepth`. -/
structure ReferenceGoodRow (reference : DecimalCylinderProbability)
    (alpha : ℝ) extends FiniteCylinderRow where
  goodPrefix : GoodPrefix DecimalNode (ReferenceDominantEdge reference alpha)
    startDepth windowLength
  prefix_root : goodPrefix.node ⟨0, Nat.zero_lt_succ _⟩ = root

/-- Arbitrarily long means that for each requested edge length one row has a
window at least that long. The witnessing row may change with the length. -/
def ArbitrarilyLongRows {reference : DecimalCylinderProbability} {alpha : ℝ}
    (rows : ℕ → ReferenceGoodRow reference alpha) : Prop :=
  ∀ length : ℕ, ∃ q : ℕ, length ≤ (rows q).windowLength

/-- T29 pullback in original decimal coordinates. Every branch quantifier,
absolute level, decimal child, positivity condition, and retention inequality
is expanded in the conclusion. -/
theorem exists_originalCoordinate_infinite_reference_branch
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold alpha : ℝ) (startBound : ℕ)
    (rows : ℕ → ReferenceGoodRow reference alpha)
    (hcontrol : FixedReferenceControl reference tightness comparisonConstant
      rootThreshold startBound (fun q => (rows q).toFiniteCylinderRow))
    (hlong : ArbitrarilyLongRows rows) :
    ∃ start : ℕ, start ≤ startBound ∧
      ∃ node : (i : ℕ) → DecimalNode (start + i),
        ∀ i : ℕ,
          0 < reference.mass (start + i) (node i) ∧
          ∃ d : Fin 10,
            (by simpa only [Nat.add_assoc] using node (i + 1)) =
                decimalChild (start + i) (node i) d ∧
            alpha * reference.mass (start + i) (node i) ≤
              reference.mass (start + i + 1)
                (by simpa only [Nat.add_assoc] using node (i + 1)) := by
  have hbounded : ∀ length : ℕ, ∃ start : ℕ, start ≤ startBound ∧
      Nonempty (GoodPrefix DecimalNode
        (ReferenceDominantEdge reference alpha) start length) := by
    intro length
    obtain ⟨q, hlength⟩ := hlong length
    refine ⟨(rows q).startDepth, ?_, ?_⟩
    · exact movingRoot_startDepth_le reference tightness comparisonConstant
        rootThreshold startBound (fun q => (rows q).toFiniteCylinderRow)
        hcontrol q
    · exact ⟨(rows q).goodPrefix.restrict hlength⟩
  obtain ⟨start, hstart, node, hbranch⟩ :=
    exists_infinite_good_branch_of_bounded_starts
      (ReferenceDominantEdge reference alpha) startBound hbounded
  refine ⟨start, hstart, node, ?_⟩
  intro i
  exact hbranch i

/-- T14 plus the T41 hypotheses. This definition keeps the logical boundary
visible: T14's finite bad-row/weighted-dominance statement is one conjunct;
fixed-reference comparison and positive unnormalized root mass are another. -/
def T14WithFixedReferenceControl
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ)
    (rows : ℕ → FiniteCylinderRow) : Prop :=
  FiniteCountTreeLeakage.T14FailureAndWeightedDominance ∧
    FixedReferenceControl reference tightness comparisonConstant
      rootThreshold startBound rows

/-- Exact T14 non-instantiation statement. Once T14's checked conclusion is
given, satisfying the T41 interface is equivalent to separately supplying all
fixed-reference comparison, modulus-cutoff, and positive-root-mass hypotheses.
No implication from T14 to those hypotheses is asserted. -/
theorem t14_nonInstantiation_fixedReference_and_rootMass_are_extra
    (hT14 : FiniteCountTreeLeakage.T14FailureAndWeightedDominance)
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ)
    (rows : ℕ → FiniteCylinderRow) :
    T14WithFixedReferenceControl reference tightness comparisonConstant
        rootThreshold startBound rows ↔
      0 ≤ comparisonConstant ∧
      0 < rootThreshold ∧
      comparisonConstant * tightness.modulus (startBound + 1) < rootThreshold ∧
      ∀ q : ℕ,
        rootThreshold ≤ (rows q).count (rows q).startDepth (rows q).root ∧
        ∀ n : ℕ, (rows q).startDepth ≤ n →
          n ≤ (rows q).startDepth + (rows q).windowLength →
          ∀ a : DecimalNode n,
            (rows q).count n a ≤ comparisonConstant * reference.mass n a := by
  rw [T14WithFixedReferenceControl, and_iff_right hT14]
  exact fixedReferenceControl_iff_quantifiers reference tightness
    comparisonConstant rootThreshold startBound rows

open DecimalFactorComplexity.ArtificialStreamObstruction

/-- T37's actual artificial-stream count row, with its moving all-zero root
and exact displayed range `[stageOrder q, 2 * stageOrder q]`. -/
def t37ArtificialFiniteCylinderRow (q : ℕ) : FiniteCylinderRow where
  count := (streamCountTree artificialStream (sampledCheckpoint q)).toReal
  startDepth := stageOrder q
  windowLength := stageOrder q
  root := zeroCode (stageOrder q)

/-- T37 boundary theorem. Its actual artificial rows cannot satisfy the T41
fixed-reference interface for any fixed reference, modulus, constants, and
finite start bound: the quantitative theorem would bound `stageOrder q = q+1`
uniformly, contradicted already by row `q = startBound`. -/
theorem t37_artificialStream_does_not_satisfy_fixedReferenceControl
    (reference : DecimalCylinderProbability)
    (tightness : CylinderTightness reference)
    (comparisonConstant rootThreshold : ℝ) (startBound : ℕ) :
    ¬ FixedReferenceControl reference tightness comparisonConstant
      rootThreshold startBound t37ArtificialFiniteCylinderRow := by
  intro hcontrol
  have hbound := movingRoot_startDepth_le reference tightness
    comparisonConstant rootThreshold startBound
    t37ArtificialFiniteCylinderRow hcontrol startBound
  change stageOrder startBound ≤ startBound at hbound
  unfold stageOrder at hbound
  omega

end DecimalFactorComplexity.FixedReferenceCylinderTightnessT41

#print axioms DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.movingRoot_startDepth_le
#print axioms DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.fixedReferenceControl_iff_quantifiers
#print axioms DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.exists_originalCoordinate_infinite_reference_branch
#print axioms DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.t14_nonInstantiation_fixedReference_and_rootMass_are_extra
#print axioms DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.t37_artificialStream_does_not_satisfy_fixedReferenceControl
