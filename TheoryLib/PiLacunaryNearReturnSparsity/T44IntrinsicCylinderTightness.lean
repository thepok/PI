import TheoryLib.PiLacunaryNearReturnSparsity.T41FixedReferenceCylinderTightness

/-!
# T44: intrinsic atom control for T41's fixed decimal cylinders

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This is an abstract A14 sibling interface. It does not establish C1, C2,
canonical A1, or any unconditional statement about `Real.pi`.
-/

noncomputable section

open Finset Filter MeasureTheory

namespace DecimalFactorComplexity.IntrinsicCylinderTightnessT44

open DecimalFactorComplexity.FiniteCountTreeLeakage
open DecimalFactorComplexity.ArtificialStreamObstruction

namespace T41

abbrev DecimalNode :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.DecimalNode
abbrev DecimalCylinderProbability :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.DecimalCylinderProbability
abbrev CylinderTightness :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.CylinderTightness
abbrev FiniteCylinderRow :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.FiniteCylinderRow
abbrev ReferenceGoodRow :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.ReferenceGoodRow
abbrev ReferenceDominantEdge :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.ReferenceDominantEdge
abbrev FixedReferenceControl :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.FixedReferenceControl
abbrev T14WithFixedReferenceControl :=
  DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.T14WithFixedReferenceControl

end T41

/-- T41 uses literal digit streams, not real intervals: a terminating stream
and a repeating-nine stream are distinct points. Thus there is no unidentified
left/right decimal endpoint in this cylinder representation. -/
inductive DecimalEndpointConvention where
  | literalDigitStreams
  deriving DecidableEq

/-- T41's exact probability model, packaged with its explicit endpoint
convention. The mass field remains tied by T41 to subsets of `ℕ → Fin 10`. -/
structure LiteralCylinderModel where
  reference : T41.DecimalCylinderProbability
  endpointConvention : DecimalEndpointConvention
  endpointConvention_eq :
    endpointConvention = DecimalEndpointConvention.literalDigitStreams

/-- The code of the first `n` literal digits of a stream. -/
def prefixNode (x : ℕ → Fin 10) (n : ℕ) : T41.DecimalNode n :=
  (decodedTupleEquiv n).symm (fun i : Fin n => x i)

@[simp] theorem decodedTuple_prefixNode (x : ℕ → Fin 10) (n : ℕ) :
    decodedTuple n (prefixNode x n) = fun i : Fin n => x i := by
  exact (decodedTupleEquiv n).apply_symm_apply (fun i : Fin n => x i)

/-- Literal prefix extension is exactly T29/T41's decimal-child operation. -/
theorem prefixNode_succ (x : ℕ → Fin 10) (n : ℕ) :
    prefixNode x (n + 1) = decimalChild n (prefixNode x n) (x n) := by
  apply decodedTuple_injective
  rw [decodedTuple_decimalChild, decodedTuple_prefixNode,
    decodedTuple_prefixNode]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- A decimal atom is a compatible choice of one nested cylinder at every
absolute depth, beginning at the unique depth-zero cylinder. -/
structure CompatibleDecimalAtom where
  node : (n : ℕ) → T41.DecimalNode n
  compatible : ∀ n, ∃ d : Fin 10,
    node (n + 1) = decimalChild n (node n) d

/-- Every literal digit stream gives a compatible nested-cylinder atom. -/
def atomOfStream (x : ℕ → Fin 10) : CompatibleDecimalAtom where
  node := prefixNode x
  compatible n := ⟨x n, prefixNode_succ x n⟩

/-- Every child cylinder has mass at most its parent cylinder. -/
theorem child_mass_le (model : LiteralCylinderModel) (n : ℕ)
    (a : T41.DecimalNode n) (d : Fin 10) :
    model.reference.mass (n + 1) (decimalChild n a d) ≤
      model.reference.mass n a := by
  rw [model.reference.conservation n a]
  exact Finset.single_le_sum
    (fun d _ => model.reference.nonneg (n + 1) (decimalChild n a d))
    (Finset.mem_univ d)

/-- Masses along a compatible atom form an antitone sequence. -/
theorem atomCylinderMass_antitone (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) :
    Antitone (fun n => model.reference.mass n (atom.node n)) := by
  apply antitone_nat_of_succ_le
  intro n
  obtain ⟨d, hd⟩ := atom.compatible n
  rw [hd]
  exact child_mass_le model n (atom.node n) d

/-- The atomic mass is the infimum of the masses of its compatible nested
cylinders. -/
def atomMass (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) : ℝ :=
  ⨅ n, model.reference.mass n (atom.node n)

theorem atomMass_nonneg (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) : 0 ≤ atomMass model atom := by
  apply le_ciInf
  intro n
  exact model.reference.nonneg n (atom.node n)

theorem atomCylinderMass_tendsto_atomMass (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) :
    Tendsto (fun n => model.reference.mass n (atom.node n)) atTop
      (nhds (atomMass model atom)) := by
  exact tendsto_atTop_ciInf (atomCylinderMass_antitone model atom)
    ⟨0, Set.forall_mem_range.2 fun n =>
      model.reference.nonneg n (atom.node n)⟩

/-- The largest mass of a depth-`n` reference cylinder. -/
def maxCylinderMass (model : LiteralCylinderModel) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (model.reference.mass n)

theorem cylinderMass_le_maxCylinderMass (model : LiteralCylinderModel)
    (n : ℕ) (a : T41.DecimalNode n) :
    model.reference.mass n a ≤ maxCylinderMass model n :=
  Finset.le_sup' (model.reference.mass n) (Finset.mem_univ a)

theorem maxCylinderMass_nonneg (model : LiteralCylinderModel) (n : ℕ) :
    0 ≤ maxCylinderMass model n :=
  (model.reference.nonneg n 0).trans
    (cylinderMass_le_maxCylinderMass model n 0)

theorem maxCylinderMass_eq_some (model : LiteralCylinderModel) (n : ℕ) :
    ∃ a : T41.DecimalNode n,
      maxCylinderMass model n = model.reference.mass n a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (T41.DecimalNode n)).Nonempty)
    (model.reference.mass n)
  exact ⟨a, ha⟩

/-- Maximum reference-cylinder masses decrease with absolute depth. -/
theorem maxCylinderMass_antitone (model : LiteralCylinderModel) :
    Antitone (maxCylinderMass model) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold maxCylinderMass
  apply Finset.sup'_le Finset.univ_nonempty
  intro b _
  let ad := (decimalAppendEquiv n).symm b
  have hb : b = decimalChild n ad.1 ad.2 := by
    exact ((decimalAppendEquiv n).apply_symm_apply b).symm
  rw [hb]
  exact (child_mass_le model n ad.1 ad.2).trans
    (cylinderMass_le_maxCylinderMass model n ad.1)

theorem maxCylinderMass_zero (model : LiteralCylinderModel) :
    maxCylinderMass model 0 = 1 := by
  apply le_antisymm
  · unfold maxCylinderMass
    apply Finset.sup'_le Finset.univ_nonempty
    intro a _
    exact le_of_eq (model.reference.root_mass a)
  · simpa [model.reference.root_mass (0 : T41.DecimalNode 0)] using
      cylinderMass_le_maxCylinderMass model 0 (0 : T41.DecimalNode 0)

theorem maxCylinderMass_le_one (model : LiteralCylinderModel) (n : ℕ) :
    maxCylinderMass model n ≤ 1 := by
  rw [← maxCylinderMass_zero model]
  exact maxCylinderMass_antitone model (Nat.zero_le n)

/-- The largest atomic mass among all compatible nested decimal cylinders. -/
def maximalAtomicMass (model : LiteralCylinderModel) : ℝ :=
  sSup (Set.range (atomMass model))

theorem atomMass_le_one (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) : atomMass model atom ≤ 1 := by
  exact (ciInf_le
    ⟨0, Set.forall_mem_range.2 fun n =>
      model.reference.nonneg n (atom.node n)⟩ 0).trans_eq
    (model.reference.root_mass (atom.node 0))

theorem atomMass_range_nonempty (model : LiteralCylinderModel) :
    (Set.range (atomMass model)).Nonempty := by
  exact ⟨atomMass model (atomOfStream fun _ => 0),
    Set.mem_range_self (atomOfStream fun _ => 0)⟩

theorem atomMass_range_bddAbove (model : LiteralCylinderModel) :
    BddAbove (Set.range (atomMass model)) := by
  exact ⟨1, Set.forall_mem_range.2 (atomMass_le_one model)⟩

theorem atomMass_le_maximalAtomicMass (model : LiteralCylinderModel)
    (atom : CompatibleDecimalAtom) :
    atomMass model atom ≤ maximalAtomicMass model := by
  exact le_csSup (atomMass_range_bddAbove model) (Set.mem_range_self atom)

theorem maximalAtomicMass_le_maxCylinderMass (model : LiteralCylinderModel)
    (n : ℕ) : maximalAtomicMass model ≤ maxCylinderMass model n := by
  apply csSup_le (atomMass_range_nonempty model)
  intro value hvalue
  obtain ⟨atom, rfl⟩ := hvalue
  exact (ciInf_le
    ⟨0, Set.forall_mem_range.2 fun i =>
      model.reference.nonneg i (atom.node i)⟩ n).trans
    (cylinderMass_le_maxCylinderMass model n (atom.node n))

/-- Extend one finite decoded node by zero digits. -/
def extendNode (n : ℕ) (a : T41.DecimalNode n) : ℕ → Fin 10 :=
  fun i => if hi : i < n then decodedTuple n a ⟨i, hi⟩ else 0

theorem prefixNode_extendNode_self (n : ℕ) (a : T41.DecimalNode n) :
    prefixNode (extendNode n a) n = a := by
  apply decodedTuple_injective
  rw [decodedTuple_prefixNode]
  funext i
  simp [extendNode, i.isLt]

/-- Finite branching prevents maximum mass from escaping between incompatible
cylinders: depth maxima converge exactly to the maximal compatible atom mass. -/
theorem maxCylinderMass_tendsto_maximalAtomicMass
    (model : LiteralCylinderModel) :
    Tendsto (maxCylinderMass model) atTop
      (nhds (maximalAtomicMass model)) := by
  let L : ℝ := ⨅ n, maxCylinderMass model n
  have hmaxBdd : BddBelow (Set.range (maxCylinderMass model)) :=
    ⟨0, Set.forall_mem_range.2 (maxCylinderMass_nonneg model)⟩
  let edge : (n : ℕ) → T41.DecimalNode n →
      T41.DecimalNode (n + 1) → Prop := fun n a b =>
    ∃ d : Fin 10, b = decimalChild n a d ∧
      L ≤ model.reference.mass (n + 1) b
  have hlong : ∀ length : ℕ, ∃ start : ℕ, start ≤ 0 ∧
      Nonempty (GoodPrefix T41.DecimalNode edge start length) := by
    intro length
    obtain ⟨a, ha⟩ := maxCylinderMass_eq_some model length
    let x := extendNode length a
    refine ⟨0, le_rfl, ⟨{
      node := fun i => prefixNode x (0 + i.val)
      good := ?_ }⟩⟩
    intro i
    dsimp only [edge]
    refine ⟨x (0 + i.val), ?_, ?_⟩
    · simpa only [Nat.add_assoc] using prefixNode_succ x (0 + i.val)
    · have hLmax : L ≤ maxCylinderMass model length := by
        exact ciInf_le hmaxBdd length
      have hdeep :
          L ≤ model.reference.mass length (prefixNode x length) := by
        rw [show prefixNode x length = a by
          exact prefixNode_extendNode_self length a]
        exact hLmax.trans_eq ha
      have hanti := atomCylinderMass_antitone model (atomOfStream x)
      have hlevel := hanti (show 0 + i.val + 1 ≤ length by omega)
      have hmass : L ≤ model.reference.mass (0 + i.val + 1)
          (prefixNode x (0 + i.val + 1)) :=
        hdeep.trans (by simpa [atomOfStream] using hlevel)
      simpa only [Nat.add_assoc] using hmass
  obtain ⟨start, hstart, node, hbranch⟩ :=
    exists_infinite_good_branch_of_bounded_starts edge 0 hlong
  have hstartZero : start = 0 := Nat.eq_zero_of_le_zero hstart
  subst start
  let node0 : (i : ℕ) → T41.DecimalNode i := fun i =>
    cast (congrArg T41.DecimalNode (Nat.zero_add i)) (node i)
  have hbranch' : ∀ i : ℕ, edge i (node0 i) (node0 (i + 1)) := by
    intro i
    convert hbranch i using 1 <;> simp [node0]
  let atom : CompatibleDecimalAtom := {
    node := node0
    compatible := fun n => by
      have hb := hbranch' n
      change ∃ d : Fin 10, node0 (n + 1) = decimalChild n (node0 n) d ∧
        L ≤ model.reference.mass (n + 1) (node0 (n + 1)) at hb
      obtain ⟨d, hd, _⟩ := hb
      exact ⟨d, hd⟩ }
  have hLatom : L ≤ atomMass model atom := by
    apply le_ciInf
    intro n
    cases n with
    | zero =>
        calc
          L ≤ maxCylinderMass model 0 := ciInf_le hmaxBdd 0
          _ = 1 := maxCylinderMass_zero model
          _ = model.reference.mass 0 (atom.node 0) :=
            (model.reference.root_mass (atom.node 0)).symm
    | succ n =>
        have hb := hbranch' n
        change ∃ d : Fin 10, node0 (n + 1) = decimalChild n (node0 n) d ∧
          L ≤ model.reference.mass (n + 1) (node0 (n + 1)) at hb
        obtain ⟨_, _, hmass⟩ := hb
        exact (by simpa [atom] using hmass)
  have hLle : L ≤ maximalAtomicMass model :=
    hLatom.trans (atomMass_le_maximalAtomicMass model atom)
  have hmaximalLe : maximalAtomicMass model ≤ L := by
    apply le_ciInf
    intro n
    exact maximalAtomicMass_le_maxCylinderMass model n
  have hL : L = maximalAtomicMass model := le_antisymm hLle hmaximalLe
  rw [← hL]
  exact tendsto_atTop_ciInf (maxCylinderMass_antitone model) hmaxBdd

/-- Nonatomicity is stated intrinsically on all compatible nested cylinders. -/
def IsNonatomic (model : LiteralCylinderModel) : Prop :=
  ∀ atom : CompatibleDecimalAtom, atomMass model atom = 0

theorem maximalAtomicMass_eq_zero_of_nonatomic
    (model : LiteralCylinderModel) (hnonatomic : IsNonatomic model) :
    maximalAtomicMass model = 0 := by
  apply le_antisymm
  · apply csSup_le (atomMass_range_nonempty model)
    intro value hvalue
    obtain ⟨atom, rfl⟩ := hvalue
    exact le_of_eq (hnonatomic atom)
  · exact (atomMass_nonneg model (atomOfStream fun _ => 0)).trans
      (atomMass_le_maximalAtomicMass model (atomOfStream fun _ => 0))

/-- The intrinsic depth maximum is a T41 cylinder-tightness modulus. -/
def intrinsicTightness (model : LiteralCylinderModel) :
    T41.CylinderTightness model.reference where
  modulus := maxCylinderMass model
  modulus_nonneg := maxCylinderMass_nonneg model
  antitone := maxCylinderMass_antitone model
  cylinder_mass_le := cylinderMass_le_maxCylinderMass model

/-- Nonatomicity makes T41's intrinsic cylinder-tightness modulus vanish. -/
theorem nonatomic_intrinsicTightness_tendsto_zero
    (model : LiteralCylinderModel) (hnonatomic : IsNonatomic model) :
    Tendsto (intrinsicTightness model).modulus atTop (nhds 0) := by
  rw [← maximalAtomicMass_eq_zero_of_nonatomic model hnonatomic]
  exact maxCylinderMass_tendsto_maximalAtomicMass model

/-! ## Exact comparison transport -/

/-- Dominance for one changing row, with positive parent mass and literal
decimal append included in the predicate. -/
def RowDominantEdge (row : T41.FiniteCylinderRow) (alpha : ℝ)
    (n : ℕ) (a : T41.DecimalNode n) (b : T41.DecimalNode (n + 1)) : Prop :=
  0 < row.count n a ∧
    ∃ d : Fin 10, b = decimalChild n a d ∧
      alpha * row.count n a ≤ row.count (n + 1) b

/-- A changing row with one synchronized good prefix. Its edge predicate uses
the same `alpha` at every displayed depth. -/
structure SynchronizedRowGood (alpha : ℝ) extends T41.FiniteCylinderRow where
  goodPrefix : GoodPrefix T41.DecimalNode
    (RowDominantEdge toFiniteCylinderRow alpha) startDepth windowLength
  prefix_root : goodPrefix.node ⟨0, Nat.zero_lt_succ _⟩ = root

/-- Uniform two-sided comparison on every displayed row cylinder. Both
orientations use the same constant `C`; positivity of `C` is stated separately
in the transport theorem and wrapper. -/
def UniformTwoSidedComparison (model : LiteralCylinderModel) (C : ℝ)
    {alpha : ℝ} (rows : ℕ → SynchronizedRowGood alpha) : Prop :=
  ∀ q n, (rows q).startDepth ≤ n →
    n ≤ (rows q).startDepth + (rows q).windowLength →
    ∀ a : T41.DecimalNode n,
      (rows q).count n a ≤ C * model.reference.mass n a ∧
      model.reference.mass n a ≤ C * (rows q).count n a

/-- Exact local transport: two-sided comparison by `C > 0` sends row
successor dominance `alpha` to fixed-reference dominance `alpha / C^2`.
The parent positivity and both comparison orientations are explicit. -/
theorem rowDominance_transports_alpha_div_C_sq
    (model : LiteralCylinderModel)
    (C alpha rowParent rowChild : ℝ) (n : ℕ)
    (a : T41.DecimalNode n) (b : T41.DecimalNode (n + 1))
    (hC : 0 < C) (halpha : 0 ≤ alpha) (hrowParent : 0 < rowParent)
    (hparent : rowParent ≤ C * model.reference.mass n a ∧
      model.reference.mass n a ≤ C * rowParent)
    (hchild : rowChild ≤ C * model.reference.mass (n + 1) b ∧
      model.reference.mass (n + 1) b ≤ C * rowChild)
    (d : Fin 10) (hb : b = decimalChild n a d)
    (hdominant : alpha * rowParent ≤ rowChild) :
    T41.ReferenceDominantEdge model.reference (alpha / C ^ 2) n a b := by
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hrefParent : 0 < model.reference.mass n a := by
    by_contra hnot
    have hrefNonpos : model.reference.mass n a ≤ 0 := le_of_not_gt hnot
    have hscaledNonpos : C * model.reference.mass n a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hCnonneg hrefNonpos
    linarith [hparent.1]
  refine ⟨hrefParent, d, hb, ?_⟩
  have hfirst : alpha * model.reference.mass n a ≤ C * rowChild := by
    calc
      alpha * model.reference.mass n a ≤ alpha * (C * rowParent) :=
        mul_le_mul_of_nonneg_left hparent.2 halpha
      _ = C * (alpha * rowParent) := by ring
      _ ≤ C * rowChild := mul_le_mul_of_nonneg_left hdominant hCnonneg
  have hscaled :
      alpha * model.reference.mass n a ≤
        C ^ 2 * model.reference.mass (n + 1) b := by
    calc
      alpha * model.reference.mass n a ≤ C * rowChild := hfirst
      _ ≤ C * (C * model.reference.mass (n + 1) b) :=
        mul_le_mul_of_nonneg_left hchild.1 hCnonneg
      _ = C ^ 2 * model.reference.mass (n + 1) b := by ring
  calc
    (alpha / C ^ 2) * model.reference.mass n a =
        (alpha * model.reference.mass n a) / C ^ 2 := by ring
    _ ≤ model.reference.mass (n + 1) b := by
      apply (div_le_iff₀ (sq_pos_of_pos hC)).2
      simpa [mul_comm] using hscaled

/-- Convert every synchronized row-good prefix to T41's fixed-reference edge
predicate using the exact `alpha / C^2` transport. -/
def transportedReferenceRow (model : LiteralCylinderModel)
    (C alpha : ℝ) (hC : 0 < C) (halpha : 0 ≤ alpha)
    (rows : ℕ → SynchronizedRowGood alpha)
    (hcomparison : UniformTwoSidedComparison model C rows)
    (q : ℕ) : T41.ReferenceGoodRow model.reference (alpha / C ^ 2) where
  toFiniteCylinderRow := (rows q).toFiniteCylinderRow
  goodPrefix := {
    node := (rows q).goodPrefix.node
    good := by
      intro i
      let depth := (rows q).startDepth + i.val
      let parent : T41.DecimalNode depth :=
        (rows q).goodPrefix.node i.castSucc
      let child : T41.DecimalNode (depth + 1) := by
        simpa only [depth, Nat.add_assoc] using
          (rows q).goodPrefix.node i.succ
      change T41.ReferenceDominantEdge model.reference (alpha / C ^ 2)
        depth parent child
      have hgood := (rows q).goodPrefix.good i
      change RowDominantEdge (rows q).toFiniteCylinderRow alpha
        depth parent child at hgood
      obtain ⟨hparentPos, d, hchildNode, hdominant⟩ := hgood
      exact rowDominance_transports_alpha_div_C_sq model C alpha
        ((rows q).count depth parent)
        ((rows q).count (depth + 1) child)
        depth parent child
        hC halpha hparentPos
        (hcomparison q depth (by dsimp [depth]; omega)
          (by dsimp [depth]; omega) parent)
        (hcomparison q (depth + 1) (by dsimp [depth]; omega)
          (by dsimp [depth]; omega) child)
        d hchildNode hdominant }
  prefix_root := (rows q).prefix_root

/-! ## T41 wrapper -/

/-- T14 is only carried as a separate conjunct. The nonatomic reference,
positive root threshold, two-sided comparison, cutoff, and synchronized
arbitrarily long row-good prefixes are all independent explicit hypotheses;
none is inferred from T14. The proof invokes T41's existing bounded-start and
original-coordinate branch theorem. -/
theorem t14_intrinsic_tightness_wrapper
    (hT14 : T14FailureAndWeightedDominance)
    (model : LiteralCylinderModel) (hnonatomic : IsNonatomic model)
    (C rootThreshold alpha : ℝ) (startBound : ℕ)
    (rows : ℕ → SynchronizedRowGood alpha)
    (hC : 0 < C) (halpha : 0 ≤ alpha)
    (hrootThreshold : 0 < rootThreshold)
    (hcutoff : C * maxCylinderMass model (startBound + 1) < rootThreshold)
    (hroot : ∀ q, rootThreshold ≤
      (rows q).count (rows q).startDepth (rows q).root)
    (hcomparison : UniformTwoSidedComparison model C rows)
    (hsynchronized : ∀ length : ℕ, ∃ q : ℕ,
      length ≤ (rows q).windowLength) :
    T14FailureAndWeightedDominance ∧
      Tendsto (intrinsicTightness model).modulus atTop (nhds 0) ∧
      ∃ start : ℕ, start ≤ startBound ∧
        ∃ node : (i : ℕ) → T41.DecimalNode (start + i),
          ∀ i : ℕ,
            0 < model.reference.mass (start + i) (node i) ∧
            ∃ d : Fin 10,
              (by simpa only [Nat.add_assoc] using node (i + 1)) =
                  decimalChild (start + i) (node i) d ∧
              (alpha / C ^ 2) *
                  model.reference.mass (start + i) (node i) ≤
                model.reference.mass (start + i + 1)
                  (by simpa only [Nat.add_assoc] using node (i + 1)) := by
  let referenceRows : ℕ →
      T41.ReferenceGoodRow model.reference (alpha / C ^ 2) :=
    transportedReferenceRow model C alpha hC halpha rows hcomparison
  have hcontrol : T41.FixedReferenceControl model.reference
      (intrinsicTightness model) C rootThreshold startBound
      (fun q => (referenceRows q).toFiniteCylinderRow) := by
    refine ⟨le_of_lt hC, hrootThreshold, hcutoff, ?_⟩
    intro q
    constructor
    · simpa [referenceRows, transportedReferenceRow] using hroot q
    · intro n hnLower hnUpper a
      simpa [referenceRows, transportedReferenceRow] using
        (hcomparison q n hnLower hnUpper a).1
  have hlong :
      DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.ArbitrarilyLongRows
        referenceRows := by
    intro length
    obtain ⟨q, hq⟩ := hsynchronized length
    exact ⟨q, by simpa [referenceRows, transportedReferenceRow] using hq⟩
  refine ⟨hT14, nonatomic_intrinsicTightness_tendsto_zero model hnonatomic, ?_⟩
  exact DecimalFactorComplexity.FixedReferenceCylinderTightnessT41.exists_originalCoordinate_infinite_reference_branch model.reference
      (intrinsicTightness model) C rootThreshold (alpha / C ^ 2)
      startBound referenceRows hcontrol hlong

end DecimalFactorComplexity.IntrinsicCylinderTightnessT44

#print axioms DecimalFactorComplexity.IntrinsicCylinderTightnessT44.maxCylinderMass_antitone
#print axioms DecimalFactorComplexity.IntrinsicCylinderTightnessT44.maxCylinderMass_tendsto_maximalAtomicMass
#print axioms DecimalFactorComplexity.IntrinsicCylinderTightnessT44.nonatomic_intrinsicTightness_tendsto_zero
#print axioms DecimalFactorComplexity.IntrinsicCylinderTightnessT44.rowDominance_transports_alpha_div_C_sq
#print axioms DecimalFactorComplexity.IntrinsicCylinderTightnessT44.t14_intrinsic_tightness_wrapper
