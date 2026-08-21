import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
import TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP
import TheoryLib.PiPositiveDecimalFactorEntropy.T72T72ProjectedPeriodicity
import TheoryLib.PiPositiveDecimalFactorEntropy.T77T77FixedWordCoreStabilization
import TheoryLib.PiPositiveDecimalFactorEntropy.T78T78SquareSparseProjectedPhaseObstruction

/-!
# T80: interval-wise projected-periodicity selector

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This module states one explicit unproved interval-selector hypothesis and proves
that it implies C6. It does not assert the selector, C6, C1, or any property of
the T78 witnesses beyond the imported kernel-checked declarations.
-/

noncomputable section

open Finset Set Topology

namespace DecimalFactorEntropy.T80IntervalProjectedPhaseSelector

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T46LiveSCC
open DecimalFactorEntropy.T48EndpointCarryKMP
open DecimalFactorEntropy.T65RationalCoreCertificate
open DecimalFactorEntropy.T72ProjectedPeriodicity
open DecimalFactorEntropy.T72ProjectedPeriodicity.T48
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.FactorComplexity
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- A decimal word with its length in the type. -/
abbrev DecimalWord (m : ℕ) := Fin m → Fin 10

/-- The list representation consumed by T44, T48, and T72. -/
def wordList {m : ℕ} (u : DecimalWord m) : List (Fin 10) :=
  List.ofFn u

@[simp] theorem wordList_length {m : ℕ} (u : DecimalWord m) :
    (wordList u).length = m := by
  simp [wordList]

theorem wordList_nonempty {m : ℕ} (hm : 0 < m) (u : DecimalWord m) :
    wordList u ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-- T72's executable global projected-periodicity check for one nonempty word,
one inclusive depth, and one supplied endpoint-complete SCC table. -/
def GoodAtDepth (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate) : Prop :=
  @decide
      (T72ProjectedPeriodicity.Graph.GlobalPrimitivePhaseCriterion
        (carryKMPGraph w hw R) coordinateZeroProjection)
      (T72ProjectedPeriodicity.Graph.globalPrimitivePhaseCriterion_decidable_of_certificate
        (carryKMPGraph w hw R) cert coordinateZeroProjection) = true

/-- The word is good exactly when the displayed finite T72 checker succeeds. -/
theorem goodAtDepth_iff_T72_decide_eq_true
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate) :
    GoodAtDepth w hw R cert ↔
      @decide
          (T72ProjectedPeriodicity.Graph.GlobalPrimitivePhaseCriterion
            (carryKMPGraph w hw R) coordinateZeroProjection)
          (T72ProjectedPeriodicity.Graph.globalPrimitivePhaseCriterion_decidable_of_certificate
            (carryKMPGraph w hw R) cert coordinateZeroProjection) = true := by
  rfl

/-- Logical meaning of the executable check, with all T48 endpoint data and the
inclusive certificate depth retained by the imported definitions. -/
theorem goodAtDepth_iff_globalProjectedPeriodicity
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate) :
    GoodAtDepth w hw R cert ↔
      T72ProjectedPeriodicity.Graph.GlobalEveryInternalProjectionEventuallyPeriodic
        (carryKMPGraph w hw R) coordinateZeroProjection := by
  simpa [GoodAtDepth] using
    endpointComplete_global_decide_eq_true_iff w hw R cert

theorem goodAtDepth_implies_globalCriterion
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate)
    (hgood : GoodAtDepth w hw R cert) :
    T72ProjectedPeriodicity.Graph.GlobalPrimitivePhaseCriterion
      (carryKMPGraph w hw R) coordinateZeroProjection := by
  exact (@decide_eq_true_iff
    (T72ProjectedPeriodicity.Graph.GlobalPrimitivePhaseCriterion
      (carryKMPGraph w hw R) coordinateZeroProjection)
    (T72ProjectedPeriodicity.Graph.globalPrimitivePhaseCriterion_decidable_of_certificate
      (carryKMPGraph w hw R) cert coordinateZeroProjection)).mp hgood

/-- The unique length-`m` decimal word with numerical label `q`. -/
def labelWord (m : ℕ) (q : Fin (10 ^ m)) : List (Fin 10) :=
  Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord m q.val

@[simp] theorem labelWord_length (m : ℕ) (q : Fin (10 ^ m)) :
    (labelWord m q).length = m := by
  exact Theory.PiDigits.DecimalBoundaryWordObstruction.fixedWord_length q.isLt

theorem labelWord_nonempty {m : ℕ} (hm : 0 < m) (q : Fin (10 ^ m)) :
    labelWord m q ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-- A numerical length-`m` label is good when a supplied finite SCC table makes
T72's executable global projected-periodicity check succeed at depth `R`. -/
def CertifiedGoodLabelAtDepth (m : ℕ) (hm : 0 < m) (R : ℕ)
    (q : Fin (10 ^ m)) : Prop :=
  ∃ cert : (carryKMPGraph (labelWord m q) (labelWord_nonempty hm q) R).SCCCertificate,
    GoodAtDepth (labelWord m q) (labelWord_nonempty hm q) R cert

/-! ## Lexicographic runs of endpoint-inclusive cylinders -/

/-- Membership of a label in the non-wrapping run `[start,start+length)`. -/
def InLexRun {m : ℕ} (start length : ℕ) (q : Fin (10 ^ m)) : Prop :=
  start ≤ q.val ∧ q.val < start + length

/-- The union of a lexicographically consecutive run of closed decimal cells.
Closed cells deliberately share their decimal endpoints. -/
def lexCylinderRun (m start length : ℕ) : Set UnitAddCircle :=
  ⋃ q : Fin (10 ^ m), ⋃ (_h : InLexRun start length q), closedDecimalCell m q

theorem mem_lexCylinderRun_iff (m start length : ℕ) (x : UnitAddCircle) :
    x ∈ lexCylinderRun m start length ↔
      ∃ q : Fin (10 ^ m), InLexRun start length q ∧
        x ∈ closedDecimalCell m q := by
  simp [lexCylinderRun]

/-- Exact endpoint formula for every cylinder in a consecutive run. -/
theorem lexCylinder_endpoints (m start length : ℕ) (q : Fin (10 ^ m))
    (_hq : InLexRun start length q) :
    closedDecimalCell m q =
      (fun x : ℝ => (x : UnitAddCircle)) ''
        Set.Icc ((q.val : ℝ) / (10 : ℝ) ^ m)
          (((q.val + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) := by
  simp [closedDecimalCell]

/-- Every bad non-wrapping run has length at most `K`. -/
def BadRunBound (m K : ℕ) (good : Fin (10 ^ m) → Prop) : Prop :=
  ∀ start length : ℕ, start + length ≤ 10 ^ m →
    (∀ q : Fin (10 ^ m), InLexRun start length q → ¬ good q) →
      length ≤ K

/-- Every valid run longer than `K` contains a good cylinder. -/
def EveryLongRunContainsGood (m K : ℕ)
    (good : Fin (10 ^ m) → Prop) : Prop :=
  ∀ start length : ℕ, start + length ≤ 10 ^ m → K < length →
    ∃ q : Fin (10 ^ m), InLexRun start length q ∧ good q

/-- Endpoint-safe bad-run equivalence. The cylinder union uses closed endpoints,
while consecutiveness is exactly the numerical order of length-`m` words. -/
theorem badRunBound_iff_everyLongRunContainsGood
    (m K : ℕ) (good : Fin (10 ^ m) → Prop) :
    BadRunBound m K good ↔ EveryLongRunContainsGood m K good := by
  classical
  constructor
  · intro hbound start length hvalid hlong
    by_contra hnone
    push Not at hnone
    have hle := hbound start length hvalid fun q hq => hnone q hq
    omega
  · intro hhit start length hvalid hbad
    by_contra hnot
    have hlong : K < length := by omega
    obtain ⟨q, hq, hgood⟩ := hhit start length hvalid hlong
    exact hbad q hq hgood

/-- The bad-run equivalence specialized to T72-certified good words at one
explicit word length and inclusive certificate depth. -/
theorem T72_badRunBound_iff_everyLongRunContainsGood
    (m : ℕ) (hm : 0 < m) (R K : ℕ) :
    BadRunBound m K (CertifiedGoodLabelAtDepth m hm R) ↔
      EveryLongRunContainsGood m K (CertifiedGoodLabelAtDepth m hm R) :=
  badRunBound_iff_everyLongRunContainsGood m K
    (CertifiedGoodLabelAtDepth m hm R)

/-! ## Fixed-depth refinements -/

/-- Concatenate a parent word and a fixed-depth refinement word. -/
def appendWord {m s : ℕ} (u : DecimalWord m) (v : DecimalWord s) :
    DecimalWord (m + s) :=
  Fin.append u v

@[simp] theorem wordList_appendWord {m s : ℕ}
    (u : DecimalWord m) (v : DecimalWord s) :
    wordList (appendWord u v) = wordList u ++ wordList v := by
  simp [wordList, appendWord]

@[simp] theorem appendWord_length {m s : ℕ}
    (u : DecimalWord m) (v : DecimalWord s) :
    (wordList (appendWord u v)).length = m + s := by
  simp

theorem appendWord_nonempty {m s : ℕ} (hm : 0 < m)
    (u : DecimalWord m) (v : DecimalWord s) :
    wordList (appendWord u v) ≠ [] := by
  exact wordList_nonempty (by omega) (appendWord u v)

/-- The refined label lies in the parent's block of exactly `10^s`
lexicographically consecutive length-`m+s` labels. -/
theorem appendWord_index_in_parent_run {m s : ℕ}
    (u : DecimalWord m) (v : DecimalWord s) :
    InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
      (wordIndex (wordList (appendWord u v))) := by
  have hvalue :
      (wordIndex (wordList (appendWord u v))).val =
        (wordIndex (wordList u)).val * 10 ^ s +
          (wordIndex (wordList v)).val := by
    simp only [wordList_appendWord, wordIndex,
      Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_append,
      wordList_length]
  constructor
  · omega
  · rw [hvalue]
    have hv := (wordIndex (wordList v)).isLt
    simpa using Nat.add_lt_add_left hv ((wordIndex (wordList u)).val * 10 ^ s)

/-- Appending a refinement shrinks the closed cylinder, including both shared
decimal endpoints. -/
theorem appendWord_wordCell_subset {m s : ℕ}
    (u : DecimalWord m) (v : DecimalWord s) :
    wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) := by
  have hvalue :
      (wordIndex (wordList (appendWord u v))).val =
        (wordIndex (wordList u)).val * 10 ^ s +
          (wordIndex (wordList v)).val := by
    simp only [wordList_appendWord, wordIndex,
      Theory.PiDigits.DecimalBoundaryWordObstruction.wordValue_append,
      wordList_length]
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩
  refine ⟨y, ?_, hxy⟩
  simp only [wordList_length] at hy ⊢
  rw [hvalue] at hy
  have hden : (10 : ℝ) ^ (m + s) = (10 : ℝ) ^ m * (10 : ℝ) ^ s := by
    rw [pow_add]
  have hvlt : (wordIndex (wordList v)).val < 10 ^ s := by
    simpa using (wordIndex (wordList v)).isLt
  have hv : (wordIndex (wordList v)).val + 1 ≤ 10 ^ s := by omega
  constructor
  · calc
      ((wordIndex (wordList u)).val : ℝ) / (10 : ℝ) ^ m =
          (((wordIndex (wordList u)).val * 10 ^ s : ℕ) : ℝ) /
            (10 : ℝ) ^ (m + s) := by
              rw [hden]
              push_cast
              field_simp
      _ ≤ ((((wordIndex (wordList u)).val * 10 ^ s +
          (wordIndex (wordList v)).val : ℕ) : ℝ) /
            (10 : ℝ) ^ (m + s)) := by
              apply (div_le_div_iff_of_pos_right (by positivity)).2
              norm_cast
              omega
      _ ≤ y := hy.1
  · calc
      y ≤ (((((wordIndex (wordList u)).val * 10 ^ s +
          (wordIndex (wordList v)).val : ℕ) : ℝ) + 1) /
            (10 : ℝ) ^ (m + s)) := hy.2
      _ ≤ ((((wordIndex (wordList u)).val : ℝ) + 1) /
            (10 : ℝ) ^ m) := by
              rw [hden]
              have hmpos : 0 < (10 : ℝ) ^ m := by positivity
              have hspos : 0 < (10 : ℝ) ^ s := by positivity
              apply (div_le_div_iff₀ (mul_pos hmpos hspos) hmpos).2
              have hvR : ((wordIndex (wordList v)).val : ℝ) + 1 ≤
                  (10 : ℝ) ^ s := by exact_mod_cast hv
              push_cast
              nlinarith [hvR, hmpos.le]

theorem occursAt_append_left {m s : ℕ} (u : DecimalWord m) (v : DecimalWord s)
    (a : DecimalStream) (start : ℕ)
    (hocc : OccursAt (wordList (appendWord u v)) a start) :
    OccursAt (wordList u) a start := by
  intro i
  have hi : i.val < (wordList (appendWord u v)).length := by
    have him : i.val < m := by simpa using i.isLt
    rw [appendWord_length]
    omega
  have h := hocc ⟨i.val, hi⟩
  simpa only [wordList_appendWord, List.get_eq_getElem,
    List.getElem_append_left i.isLt] using h

theorem avoidsWord_append {m s : ℕ} (u : DecimalWord m) (v : DecimalWord s)
    (a : DecimalStream) (ha : AvoidsWord (wordList u) a) :
    AvoidsWord (wordList (appendWord u v)) a := by
  intro start hocc
  exact ha start (occursAt_append_left u v a start hocc)

/-- Avoiding a parent word implies avoiding every refinement, hence the T44
core is monotone in the required direction. -/
theorem Core_parent_subset_refinement {m s R : ℕ}
    (u : DecimalWord m) (v : DecimalWord s) :
    Core (wordList u) R ⊆ Core (wordList (appendWord u v)) R := by
  intro x hx n j hj
  obtain ⟨a, ha, hvalue⟩ := hx n j hj
  exact ⟨a, avoidsWord_append u v a ha, hvalue⟩

/-! ## The explicit unproved selector frontier -/

/-- At every positive parent depth `m`, one common inclusive certificate depth
`R ≤ L*m+C` works as follows: inside each parent cylinder, one word at the
fixed refined depth `m+s` has a supplied SCC table whose exact T72 checker
returns true. This does not quantify over all refined words. -/
def IntervalSelectorHypothesis : Prop :=
  ∃ s : ℕ, 0 < s ∧ ∃ L C : ℝ, 0 ≤ L ∧
    ∀ m : ℕ, ∀ hm : 0 < m,
      ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
        ∀ u : DecimalWord m,
          ∃ v : DecimalWord s,
            ∃ cert : (carryKMPGraph
                (wordList (appendWord u v)) (appendWord_nonempty hm u v) R).SCCCertificate,
              InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
                  (wordIndex (wordList (appendWord u v))) ∧
                wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) ∧
                GoodAtDepth (wordList (appendWord u v))
                  (appendWord_nonempty hm u v) R cert

theorem intervalSelectorHypothesis_iff_quantifiers :
    IntervalSelectorHypothesis ↔
      ∃ s : ℕ, 0 < s ∧ ∃ L C : ℝ, 0 ≤ L ∧
        ∀ m : ℕ, ∀ hm : 0 < m,
          ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
            ∀ u : DecimalWord m,
              ∃ v : DecimalWord s,
                ∃ cert : (carryKMPGraph
                    (wordList (appendWord u v))
                      (appendWord_nonempty hm u v) R).SCCCertificate,
                  InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
                      (wordIndex (wordList (appendWord u v))) ∧
                    wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) ∧
                    GoodAtDepth (wordList (appendWord u v))
                      (appendWord_nonempty hm u v) R cert := by
  rfl

/-- Literal C6, with all epsilon and depth quantifiers displayed, follows from
the fixed-refinement interval selector. -/
theorem intervalSelector_implies_literal_C6
    (s : ℕ) (hs : 0 < s) (L C : ℝ) (hL : 0 ≤ L)
    (hselector : ∀ m : ℕ, ∀ hm : 0 < m,
      ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
        ∀ u : DecimalWord m,
          ∃ v : DecimalWord s,
            ∃ cert : (carryKMPGraph
                (wordList (appendWord u v)) (appendWord_nonempty hm u v) R).SCCCertificate,
              InLexRun ((wordIndex (wordList u)).val * 10 ^ s) (10 ^ s)
                  (wordIndex (wordList (appendWord u v))) ∧
                wordCell (wordList (appendWord u v)) ⊆ wordCell (wordList u) ∧
                GoodAtDepth (wordList (appendWord u v))
                  (appendWord_nonempty hm u v) R cert) :
    0 < (L + 1) / Real.log 10 ∧ 0 < (1 / 2 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ R : ℕ,
          EpsilonDense (timesSixteenTransversal piOrbitClosure R) ε ∧
          (R : ℝ) ≤ ((L + 1) / Real.log 10) * Real.log (1 / ε) +
            (2 * L + C) := by
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  refine ⟨div_pos (by linarith) hlogTen, by norm_num, ?_⟩
  intro ε hε hεhalf
  let m := boundaryWordLength ε
  have hm : 0 < m := boundaryWordLength_pos ε
  obtain ⟨R, hRbound, hselect⟩ := hselector m hm
  refine ⟨R, ?_, ?_⟩
  · by_contra hfail
    obtain ⟨m', u, hm'eq, _hm'pos, _hm'bound, hsubset⟩ :=
      failure_epsilonDense_exists_avoidingWord R ε hε hεhalf hfail
    have hm'm : m' = m := by simpa [m] using hm'eq
    subst m'
    obtain ⟨v, cert, _hlex, _hcell, hgood⟩ := hselect u
    have hglobal := goodAtDepth_implies_globalCriterion
      (wordList (appendWord u v)) (appendWord_nonempty hm u v) R cert hgood
    have hrational := endpointComplete_globalProjectedPhase_implies_rationalCore
      (wordList (appendWord u v)) (appendWord_nonempty hm u v) R hglobal
    have horbit : piCircleOrbit 0 ∈ piOrbitClosure := by
      change piCircleOrbit 0 ∈ closure (Set.range piCircleOrbit)
      exact subset_closure (Set.mem_range_self 0)
    apply piCircleOrbit_not_rational 0
    apply hrational (piCircleOrbit 0)
    apply Core_parent_subset_refinement u v
    exact hsubset horbit
  · let t : ℝ := Real.log (1 / ε) / Real.log 10
    have honeDiv : 1 < 1 / ε := (lt_div_iff₀ hε).2 (by linarith)
    have hlogε : 0 < Real.log (1 / ε) := Real.log_pos honeDiv
    have ht : 0 ≤ t := (div_pos hlogε hlogTen).le
    have hceil : (Nat.ceil t : ℝ) < t + 1 := Nat.ceil_lt_add_one ht
    have hmle : (m : ℝ) ≤ t + 2 := by
      dsimp [m, boundaryWordLength, t] at hceil ⊢
      push_cast
      linarith
    have hlinear : L * (m : ℝ) + C ≤ L * (t + 2) + C := by
      gcongr
    calc
      (R : ℝ) ≤ L * (m : ℝ) + C := hRbound
      _ ≤ L * (t + 2) + C := hlinear
      _ ≤ ((L + 1) / Real.log 10) * Real.log (1 / ε) +
          (2 * L + C) := by
        dsimp [t]
        have hbonus : 0 ≤ Real.log (1 / ε) / Real.log 10 :=
          (div_pos hlogε hlogTen).le
        field_simp [hlogTen.ne']
        nlinarith [mul_nonneg hL hlogTen.le]

/-- Final conditional implication. The selector remains an explicit argument;
no universal all-word certificate is introduced or asserted. -/
theorem intervalSelectorHypothesis_implies_piC6
    (h : IntervalSelectorHypothesis) : PiC6 := by
  obtain ⟨s, hs, L, C, hL, hselector⟩ := h
  refine ⟨(L + 1) / Real.log 10, 2 * L + C, 1 / 2, ?_⟩
  exact intervalSelector_implies_literal_C6 s hs L C hL hselector

end DecimalFactorEntropy.T80IntervalProjectedPhaseSelector

#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.wordList_length
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.goodAtDepth_iff_T72_decide_eq_true
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.goodAtDepth_iff_globalProjectedPeriodicity
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.labelWord_length
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.mem_lexCylinderRun_iff
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.lexCylinder_endpoints
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.badRunBound_iff_everyLongRunContainsGood
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.T72_badRunBound_iff_everyLongRunContainsGood
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.appendWord_index_in_parent_run
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.appendWord_wordCell_subset
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.Core_parent_subset_refinement
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.intervalSelectorHypothesis_iff_quantifiers
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.intervalSelector_implies_literal_C6
#print axioms DecimalFactorEntropy.T80IntervalProjectedPhaseSelector.intervalSelectorHypothesis_implies_piC6
