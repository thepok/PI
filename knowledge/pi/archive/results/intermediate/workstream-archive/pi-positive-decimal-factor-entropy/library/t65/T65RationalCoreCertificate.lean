import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
import TheoryLib.PiPositiveDecimalFactorEntropy.T46T46T46LiveSCC
import TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP
import TheoryLib.PiDigits.T11PiDigitFactorComplexity

/-!
# T65: eventual-periodic rational-core certificate

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The source is locally formulated and has no external source URL. This module
formalizes a conditional route to C6. It does not assert the uniform graph
hypothesis, C6, C1, or any new fact about pi.
-/

noncomputable section

open Finset Set Topology

namespace DecimalFactorEntropy.T65RationalCoreCertificate

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T46LiveSCC
open DecimalFactorEntropy.T48EndpointCarryKMP
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.FactorComplexity
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-! ## Generic relaxed live-SCC theorem -/

/-- T46's reachable/live/cyclic and internal simple-directed-cycle condition,
with only terminality in the reachable-live graph omitted. -/
def RelaxedLiveSCCCriterion (G : DecimalFactorEntropy.T46LiveSCC.Graph) : Prop :=
  ∀ q, G.Reachable q → G.Live q → G.Cyclic q → G.SimpleDirectedCycleSCC q

theorem relaxedLiveSCCCriterion_iff_quantifiers
    (G : DecimalFactorEntropy.T46LiveSCC.Graph) :
    RelaxedLiveSCCCriterion G ↔
      ∀ q, G.Reachable q → G.Live q → G.Cyclic q →
        ∀ r, G.SameSCC q r →
          ∃! e : G.Edge,
            e.src = r ∧ G.ReachableLiveEdge e ∧ G.SameSCC q e.dst := by
  rfl

/-- Expanded form exposing both internal simple-cycle uniqueness and T46's
right-resolving projected determinism. The latter follows from the partial
transition function and does not restore terminality. -/
theorem relaxedLiveSCCCriterion_iff_internal_and_projected_determinism
    (G : DecimalFactorEntropy.T46LiveSCC.Graph) :
    RelaxedLiveSCCCriterion G ↔
      ∀ q, G.Reachable q → G.Live q → G.Cyclic q →
        G.SimpleDirectedCycleSCC q ∧
          ∀ r, G.SameSCC q r → ∀ e f : G.Edge,
            e.src = r → f.src = r → G.ReachableLiveEdge e →
              G.ReachableLiveEdge f → e.label = f.label → e.dst = f.dst := by
  constructor
  · intro h q hreach hlive hcyclic
    refine ⟨h q hreach hlive hcyclic, ?_⟩
    intro r _hscc e f hesrc hfsrc he hf hlabel
    exact congrArg DecimalFactorEntropy.T46LiveSCC.Graph.Edge.dst
      (G.edge_eq_of_same_source_label he.1 hf.1
        (hesrc.trans hfsrc.symm) hlabel)
  · intro h q hreach hlive hcyclic
    exact (h q hreach hlive hcyclic).1

/-- A finite segment of an infinite walk reaches its later source. -/
theorem infiniteWalk_reaches_source
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) {i j : ℕ} (hij : i ≤ j) :
    G.Reaches (z i).src (z j).src := by
  refine ⟨List.ofFn fun k : Fin (j - i) => z (i + k), ?_⟩
  simpa [Nat.add_sub_of_le hij] using
    G.infiniteWalk_prefix (G.infiniteWalk_tail hz i) (j - i)

/-- Repeating a source along an infinite walk witnesses cyclicity. -/
theorem cyclic_of_infiniteWalk_source_repeat
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) {i j : ℕ} (hij : i < j)
    (heq : (z i).src = (z j).src) : G.Cyclic (z i).src := by
  let u : List G.Edge := List.ofFn fun k : Fin (j - i) => z (i + k)
  have hu : G.IsWalk (z i).src u (z i).src := by
    have hp := G.infiniteWalk_prefix (G.infiniteWalk_tail hz i) (j - i)
    simpa [u, Nat.add_sub_of_le hij.le, heq] using hp
  have hune : u ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [u] at hlen
    omega
  rcases u with _ | ⟨e, es⟩
  · exact (hune rfl).elim
  · exact ⟨e, es, hu⟩

/-- Every edge of a tail that stays in one SCC is a reachable-live internal
edge of that SCC. -/
theorem infiniteWalk_edge_internal_of_stays_sameSCC
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    {q r : G.State} {z : ℕ → G.Edge}
    (hqreach : G.Reachable q) (hz : G.IsInfiniteWalk r z)
    (hstay : ∀ n, G.SameSCC q (z n).src) (n : ℕ) :
    G.ReachableLiveEdge (z n) ∧ G.SameSCC q (z n).dst := by
  have hdst : G.SameSCC q (z n).dst := by
    rw [(hz.2 n).2]
    exact hstay (n + 1)
  refine ⟨⟨(hz.2 n).1, ?_, G.infiniteWalk_tail_live hz n, ?_,
    G.infiniteWalk_edge_live hz n⟩, hdst⟩
  · exact G.reachable_of_reachable_reaches hqreach (hstay n).1
  · exact G.reachable_of_reachable_reaches hqreach hdst.1

/-- Internal edge uniqueness makes two infinite walks in the same simple SCC
equal when they start at the same state. -/
theorem infiniteWalk_eq_of_simpleSCC
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    {q r : G.State} (hqreach : G.Reachable q)
    (hsimple : G.SimpleDirectedCycleSCC q)
    {z w : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk r z) (hw : G.IsInfiniteWalk r w)
    (hzstay : ∀ n, G.SameSCC q (z n).src)
    (hwstay : ∀ n, G.SameSCC q (w n).src) : z = w := by
  funext n
  induction n with
  | zero =>
      have hsrc : (z 0).src = (w 0).src := hz.1.trans hw.1.symm
      have hzint := infiniteWalk_edge_internal_of_stays_sameSCC G
        hqreach hz hzstay 0
      have hwint := infiniteWalk_edge_internal_of_stays_sameSCC G
        hqreach hw hwstay 0
      rcases hsimple (z 0).src (hzstay 0) with ⟨e, _he, hunique⟩
      exact (hunique (z 0) ⟨rfl, hzint.1, hzint.2⟩).trans
        (hunique (w 0) ⟨hsrc.symm, hwint.1, hwint.2⟩).symm
  | succ n ih =>
      have hsrc : (z (n + 1)).src = (w (n + 1)).src :=
        (hz.2 n).2.symm.trans
          ((congrArg DecimalFactorEntropy.T46LiveSCC.Graph.Edge.dst ih).trans
            (hw.2 n).2)
      have hzint := infiniteWalk_edge_internal_of_stays_sameSCC G
        hqreach hz hzstay (n + 1)
      have hwint := infiniteWalk_edge_internal_of_stays_sameSCC G
        hqreach hw hwstay (n + 1)
      rcases hsimple (z (n + 1)).src (hzstay (n + 1)) with
        ⟨e, _he, hunique⟩
      exact (hunique (z (n + 1)) ⟨rfl, hzint.1, hzint.2⟩).trans
        (hunique (w (n + 1)) ⟨hsrc.symm, hwint.1, hwint.2⟩).symm

/-- Generic finite-graph theorem: every accepted edge path is eventually
periodic when terminality is dropped but T46's internal simple-cycle condition
is retained on every reachable live cyclic SCC. -/
theorem infiniteWalk_eventuallyPeriodic_of_relaxedLiveSCCCriterion
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    (hcriterion : RelaxedLiveSCCCriterion G)
    {z : ℕ → G.Edge} (hz : G.IsInfiniteWalk G.start z) :
    EventuallyPeriodic z := by
  classical
  obtain ⟨q, hqinf'⟩ :=
    Finite.exists_infinite_fiber (fun n : ℕ => (z n).src)
  have hqinf : ((fun n : ℕ => (z n).src) ⁻¹' {q}).Infinite :=
    Set.infinite_coe_iff.mp hqinf'
  obtain ⟨i, hi⟩ := hqinf.nonempty
  have hiq : (z i).src = q := by simpa using hi
  obtain ⟨j, hj, hij⟩ := hqinf.exists_gt i
  have hjq : (z j).src = q := by simpa using hj
  let p := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  have hqreach : G.Reachable q := by
    rw [← hiq]
    exact ⟨List.ofFn fun k : Fin i => z k, G.infiniteWalk_prefix hz i⟩
  have hqlive : G.Live q := by
    rw [← hiq]
    exact G.infiniteWalk_tail_live hz i
  have hqcyclic : G.Cyclic q := by
    rw [← hiq]
    exact cyclic_of_infiniteWalk_source_repeat G hz hij (hiq.trans hjq.symm)
  have hsimple := hcriterion q hqreach hqlive hqcyclic
  let u : ℕ → G.Edge := fun n => z (i + n)
  have hu : G.IsInfiniteWalk q u := by
    simpa [u, hiq] using G.infiniteWalk_tail hz i
  have hustay : ∀ n, G.SameSCC q (u n).src := by
    intro n
    constructor
    · rw [← hiq]
      exact infiniteWalk_reaches_source G hz (Nat.le_add_right i n)
    · obtain ⟨k, hk, hik⟩ := hqinf.exists_gt (i + n)
      have hkq : (z k).src = q := by simpa using hk
      rw [← hkq]
      exact infiniteWalk_reaches_source G hz hik.le
  have hup : (u p).src = q := by
    simp only [u, p]
    rw [Nat.add_sub_of_le hij.le, hjq]
  have hshift : G.IsInfiniteWalk q (fun n => u (p + n)) := by
    simpa [hup] using G.infiniteWalk_tail hu p
  have heq : u = fun n => u (p + n) :=
    infiniteWalk_eq_of_simpleSCC G hqreach hsimple hu hshift hustay
      (fun n => hustay (p + n))
  refine ⟨i, p, hp, ?_⟩
  intro n
  have hn := congrFun heq n
  simpa [u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn.symm

/-- Generic label-level form, with the distinguished start state and liveness
semantics inherited literally from T46's infinite language. -/
theorem infiniteLabelLanguage_eventuallyPeriodic_of_relaxedLiveSCCCriterion
    (G : DecimalFactorEntropy.T46LiveSCC.Graph)
    (hcriterion : RelaxedLiveSCCCriterion G)
    {x : ℕ → G.Label} (hx : x ∈ G.InfiniteLabelLanguage) :
    EventuallyPeriodic x := by
  rcases hx with ⟨z, hz, rfl⟩
  obtain ⟨N, p, hp, hperiod⟩ :=
    infiniteWalk_eventuallyPeriodic_of_relaxedLiveSCCCriterion G hcriterion hz
  refine ⟨N, p, hp, ?_⟩
  intro n
  exact congrArg DecimalFactorEntropy.T46LiveSCC.Graph.Edge.label (hperiod n)

/-! ## T48 specialization and endpoint-safe rational evaluation -/

/-- T48's accepted labels start at the synthetic root, use one exact initial
carry tuple in `[-1,16]^R`, and have all KMP coordinates initially empty. -/
theorem t48_accepted_iff_exact_endpoint_raw_run
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ) (x : ℕ → Label R) :
    x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage ↔
      ∃ (q : ℕ → RawState w hw R) (d : ℕ → DigitColumn R),
        (∀ i, (q 0).kmp i = (singletonFamily w hw).initialState) ∧
        (∀ j : Fin R, (-1 : ℤ) ≤ ((q 0).carry j).1 ∧
          ((q 0).carry j).1 ≤ 16) ∧
        (∀ n, RawStep (q n) (d n) (q (n + 1))) ∧
        x 0 = Label.initial (q 0).carry (d 0) ∧
        x = encodeLabels q d := by
  constructor
  · intro hx
    obtain ⟨q, d, hrun, hxeq⟩ :=
      (mem_graphLanguage_iff_exists_rawRun hw R x).mp hx
    refine ⟨q, d, hrun.1, ?_, hrun.2, ?_, hxeq⟩
    · intro j
      exact ⟨carry_lower ((q 0).carry j), carry_upper ((q 0).carry j)⟩
    · rw [hxeq]
      rfl
  · rintro ⟨q, d, hkmp, _hcarry, hstep, _hfirst, hxeq⟩
    exact (mem_graphLanguage_iff_exists_rawRun hw R x).mpr
      ⟨q, d, ⟨hkmp, hstep⟩, hxeq⟩

/-- Named T48-specialized eventual-periodicity theorem. -/
theorem t48_accepted_path_eventuallyPeriodic
    {w : List (Fin 10)} (hw : w ≠ []) (R : ℕ)
    (hcriterion : RelaxedLiveSCCCriterion (carryKMPGraph w hw R))
    {x : ℕ → Label R}
    (hx : x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage) :
    EventuallyPeriodic x :=
  infiniteLabelLanguage_eventuallyPeriodic_of_relaxedLiveSCCCriterion
    (carryKMPGraph w hw R) hcriterion hx

/-- A rational point of the circle is the image of an explicitly quantified
rational real. This convention includes zero/one decimal endpoints. -/
def IsRationalCirclePoint (x : UnitAddCircle) : Prop :=
  ∃ q : ℚ, (((q : ℝ) : UnitAddCircle)) = x

theorem isRationalCirclePoint_iff_exists_rat (x : UnitAddCircle) :
    IsRationalCirclePoint x ↔ ∃ q : ℚ, (((q : ℝ) : UnitAddCircle)) = x := by
  rfl

/-- Generic endpoint-inclusive decimal theorem: an eventually periodic
decimal stream has a rational real value and therefore a rational circle
value, including the terminating/repeating-nine endpoint convention. -/
theorem eventuallyPeriodic_decimal_evaluation_rational
    (d : ℕ → Fin 10) (hd : EventuallyPeriodic d) :
    ∃ q : ℚ, Real.ofDigits d = (q : ℝ) ∧
      IsRationalCirclePoint (circleValue d) := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational
    (not_irrational_ofDigits_of_eventuallyPeriodic d hd)
  refine ⟨q, hq, q, ?_⟩
  change (((q : ℝ) : UnitAddCircle)) = ((Real.ofDigits d : ℝ) : UnitAddCircle)
  exact congrArg (fun r : ℝ => (r : UnitAddCircle)) hq.symm

/-- Endpoint-inclusive coordinate-zero evaluation of an eventually periodic
T48 label stream is represented by a rational real. -/
theorem graphEvaluation_exists_rational_real_of_eventuallyPeriodic
    {R : ℕ} (x : ℕ → Label R) (hx : EventuallyPeriodic x) :
    ∃ q : ℚ,
      Real.ofDigits (fun n => (x n).digits ⟨0, by omega⟩) = (q : ℝ) := by
  let d : ℕ → Fin 10 := fun n => (x n).digits ⟨0, by omega⟩
  have hd : EventuallyPeriodic d := by
    obtain ⟨N, p, hp, hperiod⟩ := hx
    refine ⟨N, p, hp, ?_⟩
    intro n
    exact congrArg (fun a : Label R => a.digits ⟨0, by omega⟩) (hperiod n)
  exact exists_rat_of_not_irrational
    (not_irrational_ofDigits_of_eventuallyPeriodic d hd)

/-- Circle-valued T48 evaluation retains both decimal endpoint expansions and
is rational for every eventually periodic accepted label stream. -/
theorem graphEvaluation_isRationalCirclePoint_of_eventuallyPeriodic
    {R : ℕ} (x : ℕ → Label R) (hx : EventuallyPeriodic x) :
    IsRationalCirclePoint (graphEvaluation x) := by
  obtain ⟨q, hq⟩ :=
    graphEvaluation_exists_rational_real_of_eventuallyPeriodic x hx
  refine ⟨q, ?_⟩
  change (((q : ℝ) : UnitAddCircle)) =
    ((Real.ofDigits (fun n => (x n).digits ⟨0, by omega⟩) : ℝ) : UnitAddCircle)
  exact congrArg (fun r : ℝ => (r : UnitAddCircle)) hq.symm

/-- The relaxed T48 SCC certificate makes every point of the exact
endpoint-safe core a rational circle point. -/
theorem t48_relaxedSCC_implies_core_rational
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (hcriterion : RelaxedLiveSCCCriterion (carryKMPGraph w hw R)) :
    ∀ y ∈ Core w R, IsRationalCirclePoint y := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_graphEvaluation_image_of_mem_core hw R y hy
  rw [← hxy]
  exact graphEvaluation_isRationalCirclePoint_of_eventuallyPeriodic x
    (t48_accepted_path_eventuallyPeriodic hw R hcriterion hx)

/-! ## A checked strict separation from T46 terminality -/

/-- State `0` has a false-labelled loop and a true-labelled exit to state `1`.
State `1` has only a false-labelled loop. Both singleton SCCs are reachable,
live, cyclic, and internally simple, but the SCC of `0` is nonterminal. -/
def strictSeparationGraph : DecimalFactorEntropy.T46LiveSCC.Graph where
  State := Fin 2
  Label := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  labelFintype := inferInstance
  labelDecEq := inferInstance
  start := 0
  transition q a :=
    if q = 0 then
      if a = false then some 0 else some 1
    else if a = false then some 1 else none

def strictZeroLoop : strictSeparationGraph.Edge :=
  ⟨(0 : Fin 2), false, (0 : Fin 2)⟩

def strictExit : strictSeparationGraph.Edge :=
  ⟨(0 : Fin 2), true, (1 : Fin 2)⟩

def strictOneLoop : strictSeparationGraph.Edge :=
  ⟨(1 : Fin 2), false, (1 : Fin 2)⟩

theorem strictZeroLoop_valid : strictZeroLoop.Valid := by
  simp [strictZeroLoop, DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
    strictSeparationGraph]

theorem strictExit_valid : strictExit.Valid := by
  simp [strictExit, DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
    strictSeparationGraph]

theorem strictOneLoop_valid : strictOneLoop.Valid := by
  simp [strictOneLoop, DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
    strictSeparationGraph]

theorem strictSeparationGraph_not_reaches_one_zero :
    ¬ strictSeparationGraph.Reaches (1 : Fin 2) (0 : Fin 2) := by
  rintro ⟨es, hes⟩
  induction es with
  | nil =>
      change (1 : Fin 2) = (0 : Fin 2) at hes
      omega
  | cons e es ih =>
      rcases hes with ⟨hsrc, hvalid, hrest⟩
      have hdst : e.dst = (1 : Fin 2) := by
        rcases e with ⟨src, label, dst⟩
        fin_cases src <;> fin_cases label <;> fin_cases dst <;>
          simp_all [DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
            strictSeparationGraph]
      rw [hdst] at hrest
      exact ih hrest

theorem strictSeparationGraph_reachable_zero :
    strictSeparationGraph.Reachable (0 : Fin 2) :=
  strictSeparationGraph.reaches_refl (0 : Fin 2)

theorem strictSeparationGraph_reachable_one :
    strictSeparationGraph.Reachable (1 : Fin 2) :=
  ⟨[strictExit], ⟨rfl, strictExit_valid, rfl⟩⟩

theorem strictSeparationGraph_live_zero :
    strictSeparationGraph.Live (0 : Fin 2) := by
  refine ⟨fun _ => strictZeroLoop, ?_⟩
  exact ⟨rfl, fun _ => ⟨strictZeroLoop_valid, rfl⟩⟩

theorem strictSeparationGraph_live_one :
    strictSeparationGraph.Live (1 : Fin 2) := by
  refine ⟨fun _ => strictOneLoop, ?_⟩
  exact ⟨rfl, fun _ => ⟨strictOneLoop_valid, rfl⟩⟩

theorem strictSeparationGraph_cyclic_zero :
    strictSeparationGraph.Cyclic (0 : Fin 2) :=
  ⟨strictZeroLoop, [], ⟨rfl, strictZeroLoop_valid, rfl⟩⟩

theorem strictSeparationGraph_cyclic_one :
    strictSeparationGraph.Cyclic (1 : Fin 2) :=
  ⟨strictOneLoop, [], ⟨rfl, strictOneLoop_valid, rfl⟩⟩

theorem strictSeparationGraph_simple_zero :
    strictSeparationGraph.SimpleDirectedCycleSCC (0 : Fin 2) := by
  intro r hsame
  fin_cases r
  · refine ⟨strictZeroLoop, ?_, ?_⟩
    · exact ⟨rfl,
        ⟨strictZeroLoop_valid, strictSeparationGraph_reachable_zero,
          strictSeparationGraph_live_zero, strictSeparationGraph_reachable_zero,
          strictSeparationGraph_live_zero⟩,
        strictSeparationGraph.sameSCC_refl (0 : Fin 2)⟩
    · intro e he
      rcases he with ⟨hsrc, hlive, hinternal⟩
      rcases e with ⟨src, label, dst⟩
      simp only at hsrc ⊢
      subst src
      cases label with
      | false =>
          have hdst : dst = (0 : Fin 2) := by
            symm
            simpa [DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
              strictSeparationGraph] using hlive.1
          subst dst
          rfl
      | true =>
          have hdst : dst = (1 : Fin 2) := by
            symm
            simpa [DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
              strictSeparationGraph] using hlive.1
          subst dst
          exact (strictSeparationGraph_not_reaches_one_zero hinternal.2).elim
  · exact (strictSeparationGraph_not_reaches_one_zero hsame.2).elim

theorem strictSeparationGraph_simple_one :
    strictSeparationGraph.SimpleDirectedCycleSCC (1 : Fin 2) := by
  intro r hsame
  fin_cases r
  · exact (strictSeparationGraph_not_reaches_one_zero hsame.1).elim
  · refine ⟨strictOneLoop, ?_, ?_⟩
    · exact ⟨rfl,
        ⟨strictOneLoop_valid, strictSeparationGraph_reachable_one,
          strictSeparationGraph_live_one, strictSeparationGraph_reachable_one,
          strictSeparationGraph_live_one⟩,
        strictSeparationGraph.sameSCC_refl (1 : Fin 2)⟩
    · intro e he
      rcases he with ⟨hsrc, hlive, _hinternal⟩
      rcases e with ⟨src, label, dst⟩
      simp only at hsrc ⊢
      subst src
      cases label with
      | false =>
          have hdst : dst = (1 : Fin 2) := by
            symm
            simpa [DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
              strictSeparationGraph] using hlive.1
          subst dst
          rfl
      | true =>
          have hfalse : False := by
            simpa [DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid,
              strictSeparationGraph] using hlive.1
          exact hfalse.elim

/-- The relaxed condition is fully checked on the finite witness. -/
theorem strictSeparationGraph_relaxedLiveSCCCriterion :
    RelaxedLiveSCCCriterion strictSeparationGraph := by
  intro q _hreach _hlive _hcyclic
  fin_cases q
  · exact strictSeparationGraph_simple_zero
  · exact strictSeparationGraph_simple_one

/-- The first SCC has a reachable-live exit, so T46 terminality fails. -/
theorem strictSeparationGraph_zero_not_terminal :
    ¬ strictSeparationGraph.TerminalInReachableLive (0 : Fin 2) := by
  intro hterminal
  have hexit : strictSeparationGraph.ReachableLiveEdge strictExit :=
    ⟨strictExit_valid, strictSeparationGraph_reachable_zero,
      strictSeparationGraph_live_zero, strictSeparationGraph_reachable_one,
      strictSeparationGraph_live_one⟩
  have hscc := hterminal (0 : Fin 2)
    (strictSeparationGraph.sameSCC_refl (0 : Fin 2)) strictExit rfl hexit
  exact strictSeparationGraph_not_reaches_one_zero hscc.2

theorem strictSeparationGraph_not_liveSCCCriterion :
    ¬ strictSeparationGraph.LiveSCCCriterion := by
  intro hcriterion
  exact strictSeparationGraph_zero_not_terminal
    (hcriterion (0 : Fin 2) strictSeparationGraph_reachable_zero
      strictSeparationGraph_live_zero strictSeparationGraph_cyclic_zero).1

/-- Checked strictness bundle: the relaxed condition holds, T46's condition
fails only through terminality, and all accepted labels are still eventually
periodic. -/
theorem strictSeparationGraph_certificate :
    RelaxedLiveSCCCriterion strictSeparationGraph ∧
      ¬ strictSeparationGraph.LiveSCCCriterion ∧
      (∀ x ∈ strictSeparationGraph.InfiniteLabelLanguage,
        EventuallyPeriodic x) := by
  refine ⟨strictSeparationGraph_relaxedLiveSCCCriterion,
    strictSeparationGraph_not_liveSCCCriterion, ?_⟩
  intro x hx
  exact infiniteLabelLanguage_eventuallyPeriodic_of_relaxedLiveSCCCriterion
    strictSeparationGraph strictSeparationGraph_relaxedLiveSCCCriterion hx

/-! ## Uniform linear depth and the conditional implication to C6 -/

/-- Fractional parts of all decimal pi-orbit points are irrational. This is a
named repackaging of mathlib's `irrational_pi`, not a new fact about pi. -/
theorem irrational_fract_ten_pow_pi (n : ℕ) :
    Irrational (Int.fract ((10 : ℝ) ^ n * Real.pi)) := by
  have hproduct : Irrational ((10 : ℝ) ^ n * Real.pi) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      irrational_pi.natCast_mul
        (pow_ne_zero n (by norm_num : (10 : ℕ) ≠ 0))
  rw [Int.fract]
  exact hproduct.sub_intCast _

/-- No point `frac(10^n*pi)` on the circle is the image of a rational real. -/
theorem piCircleOrbit_not_rational (n : ℕ) :
    ¬ IsRationalCirclePoint (piCircleOrbit n) := by
  rintro ⟨q, hq⟩
  have hzero :
      ((((10 : ℝ) ^ n * Real.pi - (q : ℝ) : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    change piCircleOrbit n - (((q : ℝ) : UnitAddCircle)) = 0
    rw [← hq]
    simp
  obtain ⟨z, hz⟩ :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero
  have hzreal :
      (z : ℝ) = (10 : ℝ) ^ n * Real.pi - (q : ℝ) := by
    simpa [zsmul_eq_mul] using hz
  have hirr : Irrational ((10 : ℝ) ^ n * Real.pi) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      irrational_pi.natCast_mul
        (pow_ne_zero n (by norm_num : (10 : ℕ) ≠ 0))
  apply hirr
  refine ⟨q + (z : ℚ), ?_⟩
  push_cast
  linarith

/-- Every point of one endpoint-safe core is rational on the circle. -/
def RationalCoreAt (w : List (Fin 10)) (R : ℕ) : Prop :=
  ∀ x ∈ Core w R, IsRationalCirclePoint x

/-- Increasing the inclusive times-16 depth shrinks the core, so a rational
core certificate persists monotonically to every greater depth. -/
theorem rationalCoreAt_antitone
    (w : List (Fin 10)) {R R' : ℕ} (hRR' : R ≤ R')
    (hR : RationalCoreAt w R) : RationalCoreAt w R' := by
  intro x hx
  exact hR x (core_antitone_radius w hRR' hx)

/-- The sole unproved T65 frontier. One pair of real affine constants works
for every nonempty word; the word is quantified before its depth witness. -/
def UniformLinearRelaxedSCCHypothesis : Prop :=
  ∃ L C : ℝ, 0 ≤ L ∧
    ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        RelaxedLiveSCCCriterion (carryKMPGraph w hw r)

theorem uniformLinearRelaxedSCCHypothesis_iff_quantifiers :
    UniformLinearRelaxedSCCHypothesis ↔
      ∃ L C : ℝ, 0 ≤ L ∧
        ∀ w : List (Fin 10), ∀ hw : w ≠ [],
          ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
            RelaxedLiveSCCCriterion (carryKMPGraph w hw r) := by
  rfl

/-- Finitely many words of one positive length have one common depth. Core
antitonicity transfers each word's rational-core conclusion to that depth. -/
theorem exists_common_rational_core_depth_from_relaxed
    (L C : ℝ)
    (hgraph : ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        RelaxedLiveSCCCriterion (carryKMPGraph w hw r))
    (m : ℕ) (hm : 0 < m) :
    ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
      ∀ u : Fin m → Fin 10, RationalCoreAt (List.ofFn u) R := by
  classical
  have hwne (u : Fin m → Fin 10) : List.ofFn u ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  let r : (Fin m → Fin 10) → ℕ := fun u =>
    Classical.choose (hgraph (List.ofFn u) (hwne u))
  have hrspec (u : Fin m → Fin 10) :
      (r u : ℝ) ≤ L * (m : ℝ) + C ∧
        RelaxedLiveSCCCriterion
          (carryKMPGraph (List.ofFn u) (hwne u) (r u)) := by
    simpa [r] using Classical.choose_spec (hgraph (List.ofFn u) (hwne u))
  let depths : Finset ℕ := Finset.univ.image r
  have huniv : (Finset.univ : Finset (Fin m → Fin 10)).Nonempty :=
    Finset.univ_nonempty
  have hdepths : depths.Nonempty := by
    change (Finset.univ.image r).Nonempty
    exact Finset.image_nonempty.mpr huniv
  let R : ℕ := depths.max' hdepths
  have hRmem : R ∈ depths := Finset.max'_mem depths hdepths
  obtain ⟨uMax, _huMax, huMaxEq⟩ := Finset.mem_image.mp hRmem
  refine ⟨R, ?_, ?_⟩
  · rw [← huMaxEq]
    exact (hrspec uMax).1
  · intro u
    have hru : r u ∈ depths :=
      Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    have hle : r u ≤ R := Finset.le_max' depths (r u) hru
    apply rationalCoreAt_antitone (List.ofFn u) hle
    exact t48_relaxedSCC_implies_core_rational
      (List.ofFn u) (hwne u) (r u) (hrspec u).2

/-- Natural-log conversion and T44's endpoint-safe `+1` word length give
`A = (L+1)/log 10`, `B = 2L+C`, and `epsilon_0 = 1/2` literally. -/
theorem uniform_relaxedSCC_implies_literal_C6
    (L C : ℝ) (hL : 0 ≤ L)
    (hgraph : ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        RelaxedLiveSCCCriterion (carryKMPGraph w hw r)) :
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
  obtain ⟨R, hRbound, hRrational⟩ :=
    exists_common_rational_core_depth_from_relaxed L C hgraph m hm
  refine ⟨R, ?_, ?_⟩
  · by_contra hfail
    obtain ⟨m', u, hm'eq, _hm'pos, _hm'bound, hsubset⟩ :=
      failure_epsilonDense_exists_avoidingWord R ε hε hεhalf hfail
    have hm'm : m' = m := by simpa [m] using hm'eq
    subst m'
    have horbit : piCircleOrbit 0 ∈ piOrbitClosure := by
      change piCircleOrbit 0 ∈ closure (Set.range piCircleOrbit)
      exact subset_closure (Set.mem_range_self 0)
    exact piCircleOrbit_not_rational 0
      (hRrational u (piCircleOrbit 0) (hsubset horbit))
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

/-- Conditional implication only: no witness of the uniform hypothesis is
constructed and no unconditional C6 claim is made. -/
theorem uniformLinearRelaxedSCCHypothesis_implies_piC6
    (h : UniformLinearRelaxedSCCHypothesis) : PiC6 := by
  obtain ⟨L, C, hL, hgraph⟩ := h
  refine ⟨(L + 1) / Real.log 10, 2 * L + C, 1 / 2, ?_⟩
  exact uniform_relaxedSCC_implies_literal_C6 L C hL hgraph

end DecimalFactorEntropy.T65RationalCoreCertificate

#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.relaxedLiveSCCCriterion_iff_internal_and_projected_determinism
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.infiniteWalk_eventuallyPeriodic_of_relaxedLiveSCCCriterion
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.infiniteLabelLanguage_eventuallyPeriodic_of_relaxedLiveSCCCriterion
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.t48_accepted_iff_exact_endpoint_raw_run
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.t48_accepted_path_eventuallyPeriodic
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.eventuallyPeriodic_decimal_evaluation_rational
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.graphEvaluation_exists_rational_real_of_eventuallyPeriodic
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.t48_relaxedSCC_implies_core_rational
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.strictSeparationGraph_certificate
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.irrational_fract_ten_pow_pi
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.piCircleOrbit_not_rational
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.rationalCoreAt_antitone
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.uniformLinearRelaxedSCCHypothesis_iff_quantifiers
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.exists_common_rational_core_depth_from_relaxed
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.uniform_relaxedSCC_implies_literal_C6
#print axioms DecimalFactorEntropy.T65RationalCoreCertificate.uniformLinearRelaxedSCCHypothesis_implies_piC6
