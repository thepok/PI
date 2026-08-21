import Mathlib

/-!
# T46: live SCC criterion for finite right-resolving graphs

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file proves a generic supporting theorem about finite labeled graphs.  It
is not a canonical resolution of the source problem, does not prove a fact
about pi, and does not assert C6 or universal extinction.  No unverified note
is used as a premise.

The graph transition is a partial function `State → Label → Option State`.
Thus two edges with the same source and label have the same target: the usual
right-resolving hypothesis is structural rather than an extra proposition.
-/

namespace DecimalFactorEntropy.T46LiveSCC

open Function Set

/-- A finite right-resolving labeled graph with a distinguished start state. -/
structure Graph where
  State : Type
  Label : Type
  stateFintype : Fintype State
  stateDecEq : DecidableEq State
  labelFintype : Fintype Label
  labelDecEq : DecidableEq Label
  start : State
  transition : State → Label → Option State

attribute [instance] Graph.stateFintype Graph.stateDecEq
  Graph.labelFintype Graph.labelDecEq

namespace Graph

variable (G : Graph)

/-- Finite search decides unique existence.  Core Lean has no general
`Decidable (∃! x, p x)` instance, so the finite graph certificate supplies the
missing bounded search explicitly. -/
@[reducible] def decidableExistsUniqueOfFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] : Decidable (∃! x, p x) :=
  decidable_of_iff (∃ x, p x ∧ ∀ y, p y → y = x) (by rfl)

attribute [local instance] decidableExistsUniqueOfFintype

/-- An edge records its source, label, and target.  Validity is checked against
the partial deterministic transition function. -/
structure Edge where
  src : G.State
  label : G.Label
  dst : G.State
  deriving DecidableEq, Fintype

/-- The edge agrees with the graph transition. -/
def Edge.Valid (e : G.Edge) : Prop :=
  G.transition e.src e.label = some e.dst

/-- A finite coherent edge walk, including the empty walk. -/
def IsWalk : G.State → List G.Edge → G.State → Prop
  | q, [], r => q = r
  | q, e :: es, r => e.src = q ∧ e.Valid ∧ IsWalk e.dst es r

/-- Unbounded finite-walk reachability. -/
def Reaches (q r : G.State) : Prop :=
  ∃ es : List G.Edge, G.IsWalk q es r

/-- A nonempty closed walk witnesses cyclicity. -/
def Cyclic (q : G.State) : Prop :=
  ∃ e : G.Edge, ∃ es : List G.Edge, G.IsWalk q (e :: es) q

/-- A coherent one-sided infinite edge walk from `q`. -/
def IsInfiniteWalk (q : G.State) (z : ℕ → G.Edge) : Prop :=
  (z 0).src = q ∧
    ∀ n, (z n).Valid ∧ (z n).dst = (z (n + 1)).src

/-- A state is live when an infinite walk starts there. -/
def Live (q : G.State) : Prop :=
  ∃ z : ℕ → G.Edge, G.IsInfiniteWalk q z

/-- Reachability from the distinguished start state. -/
def Reachable (q : G.State) : Prop := G.Reaches G.start q

/-- Two states lie in the same strongly connected component. -/
def SameSCC (q r : G.State) : Prop := G.Reaches q r ∧ G.Reaches r q

/-- The infinite label language read from the start state. -/
def InfiniteLabelLanguage : Set (ℕ → G.Label) :=
  {x | ∃ z : ℕ → G.Edge,
    G.IsInfiniteWalk G.start z ∧ x = fun n => (z n).label}

/-- Edges of the reachable-live induced graph. -/
def ReachableLiveEdge (e : G.Edge) : Prop :=
  e.Valid ∧ G.Reachable e.src ∧ G.Live e.src ∧
    G.Reachable e.dst ∧ G.Live e.dst

/-- The SCC of `q` has no outgoing edge in the reachable-live induced graph. -/
def TerminalInReachableLive (q : G.State) : Prop :=
  ∀ r, G.SameSCC q r → ∀ e : G.Edge,
    e.src = r → G.ReachableLiveEdge e → G.SameSCC q e.dst

/-- Edge/label-sensitive simple-cycle condition.  At every vertex in the SCC
there is exactly one reachable-live edge staying in the SCC.  Since an `Edge`
contains its label, parallel choices with distinct labels are not collapsed. -/
def SimpleDirectedCycleSCC (q : G.State) : Prop :=
  ∀ r, G.SameSCC q r →
    ∃! e : G.Edge,
      e.src = r ∧ G.ReachableLiveEdge e ∧ G.SameSCC q e.dst

/-- The exact live-trimmed SCC certificate appearing in the characterization. -/
def LiveSCCCriterion : Prop :=
  ∀ q, G.Reachable q → G.Live q → G.Cyclic q →
    G.TerminalInReachableLive q ∧ G.SimpleDirectedCycleSCC q

/-- Edges in the untrimmed live-state induced graph. -/
def LiveEdge (e : G.Edge) : Prop :=
  e.Valid ∧ G.Live e.src ∧ G.Live e.dst

/-- Untrimmed live terminality, used only to state the counterexample. -/
def TerminalInLive (q : G.State) : Prop :=
  ∀ r, G.SameSCC q r → ∀ e : G.Edge,
    e.src = r → G.LiveEdge e → G.SameSCC q e.dst

/-- Untrimmed edge/label-sensitive simple-cycle condition. -/
def SimpleDirectedCycleSCCInLive (q : G.State) : Prop :=
  ∀ r, G.SameSCC q r →
    ∃! e : G.Edge, e.src = r ∧ G.LiveEdge e ∧ G.SameSCC q e.dst

/-- The tempting but false criterion obtained by omitting reachability. -/
def UntrimmedLiveSCCCriterion : Prop :=
  ∀ q, G.Live q → G.Cyclic q →
    G.TerminalInLive q ∧ G.SimpleDirectedCycleSCCInLive q

lemma isWalk_nil (q : G.State) : G.IsWalk q [] q := rfl

lemma isWalk_cons {q r : G.State} {e : G.Edge} {es : List G.Edge}
    (hsrc : e.src = q) (hvalid : e.Valid) (hrest : G.IsWalk e.dst es r) :
    G.IsWalk q (e :: es) r :=
  ⟨hsrc, hvalid, hrest⟩

lemma isWalk_append {q r s : G.State} {u v : List G.Edge}
    (hu : G.IsWalk q u r) (hv : G.IsWalk r v s) :
    G.IsWalk q (u ++ v) s := by
  induction u generalizing q with
  | nil =>
      change q = r at hu
      subst q
      exact hv
  | cons e u ih =>
      rcases hu with ⟨hsrc, hvalid, hu⟩
      exact ⟨hsrc, hvalid, ih hu⟩

lemma reaches_refl (q : G.State) : G.Reaches q q :=
  ⟨[], G.isWalk_nil q⟩

lemma reaches_trans {q r s : G.State}
    (hqr : G.Reaches q r) (hrs : G.Reaches r s) : G.Reaches q s := by
  rcases hqr with ⟨u, hu⟩
  rcases hrs with ⟨v, hv⟩
  exact ⟨u ++ v, G.isWalk_append hu hv⟩

lemma sameSCC_refl (q : G.State) : G.SameSCC q q :=
  ⟨G.reaches_refl q, G.reaches_refl q⟩

lemma sameSCC_symm {q r : G.State} (h : G.SameSCC q r) : G.SameSCC r q :=
  ⟨h.2, h.1⟩

lemma sameSCC_trans {q r s : G.State}
    (hqr : G.SameSCC q r) (hrs : G.SameSCC r s) : G.SameSCC q s :=
  ⟨G.reaches_trans hqr.1 hrs.1, G.reaches_trans hrs.2 hqr.2⟩

/-- Add one edge in front of an infinite edge stream. -/
def consInfinite (e : G.Edge) (z : ℕ → G.Edge) : ℕ → G.Edge
  | 0 => e
  | n + 1 => z n

/-- Add a finite edge list in front of an infinite edge stream. -/
def prependInfinite : List G.Edge → (ℕ → G.Edge) → (ℕ → G.Edge)
  | [], z => z
  | e :: es, z => G.consInfinite e (prependInfinite es z)

@[simp] lemma prependInfinite_nil (z : ℕ → G.Edge) :
    G.prependInfinite [] z = z := rfl

@[simp] lemma prependInfinite_append (u v : List G.Edge) (z : ℕ → G.Edge) :
    G.prependInfinite (u ++ v) z =
      G.prependInfinite u (G.prependInfinite v z) := by
  induction u with
  | nil => rfl
  | cons e u ih => simp only [List.cons_append, prependInfinite, ih]

lemma prependInfinite_length_add (u : List G.Edge) (z : ℕ → G.Edge) (n : ℕ) :
    G.prependInfinite u z (u.length + n) = z n := by
  induction u with
  | nil => simp [prependInfinite]
  | cons e u ih =>
      change G.consInfinite e (G.prependInfinite u z) ((e :: u).length + n) = z n
      simp only [List.length_cons, Nat.succ_add, consInfinite]
      exact ih

lemma infiniteWalk_prepend {q r : G.State} {u : List G.Edge}
    {z : ℕ → G.Edge} (hu : G.IsWalk q u r) (hz : G.IsInfiniteWalk r z) :
    G.IsInfiniteWalk q (G.prependInfinite u z) := by
  induction u generalizing q with
  | nil =>
      change q = r at hu
      subst q
      exact hz
  | cons e u ih =>
      rcases hu with ⟨hsrc, hvalid, hu⟩
      have htail := ih hu
      refine ⟨?_, ?_⟩
      · simpa [prependInfinite, consInfinite] using hsrc
      · intro n
        cases n with
        | zero =>
            exact ⟨hvalid, by simpa [prependInfinite, consInfinite] using htail.1.symm⟩
        | succ n => simpa [prependInfinite, consInfinite, Nat.add_assoc] using htail.2 n

lemma live_of_reaches {q r : G.State} (hqr : G.Reaches q r) (hr : G.Live r) :
    G.Live q := by
  rcases hqr with ⟨u, hu⟩
  rcases hr with ⟨z, hz⟩
  exact ⟨G.prependInfinite u z, G.infiniteWalk_prepend hu hz⟩

lemma reachable_of_reachable_reaches {q r : G.State}
    (hq : G.Reachable q) (hqr : G.Reaches q r) : G.Reachable r :=
  G.reaches_trans hq hqr

lemma infiniteWalk_tail_live {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) (n : ℕ) : G.Live (z n).src := by
  let tail : ℕ → G.Edge := fun k => z (n + k)
  refine ⟨tail, ?_⟩
  refine ⟨rfl, ?_⟩
  intro k
  simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz.2 (n + k)

lemma infiniteWalk_tail {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) (n : ℕ) :
    G.IsInfiniteWalk (z n).src (fun k => z (n + k)) := by
  refine ⟨rfl, ?_⟩
  intro k
  simpa [Nat.add_assoc] using hz.2 (n + k)

lemma infiniteWalk_edge_live {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) (n : ℕ) : G.Live (z n).dst := by
  rw [hz.2 n |>.2]
  exact G.infiniteWalk_tail_live hz (n + 1)

lemma edge_eq_of_same_source_label {e f : G.Edge}
    (he : e.Valid) (hf : f.Valid) (hsrc : e.src = f.src)
    (hlab : e.label = f.label) : e = f := by
  cases e with
  | mk es el ed =>
      cases f with
      | mk fs fl fd =>
          simp only at hsrc hlab ⊢
          subst fs
          subst fl
          simp only [Edge.Valid] at he hf
          congr
          exact Option.some.inj (he.symm.trans hf)

lemma infiniteWalk_prefix {q : G.State} {z : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) (n : ℕ) :
    G.IsWalk q (List.ofFn fun i : Fin n => z i) (z n).src := by
  induction n generalizing q z with
  | zero => simpa [IsWalk] using hz.1.symm
  | succ n ih =>
      rw [List.ofFn_succ]
      refine ⟨hz.1, (hz.2 0).1, ?_⟩
      simpa [Nat.add_assoc] using ih
        (q := (z 0).dst) (z := fun k => z (k + 1))
        ⟨(hz.2 0).2.symm, fun k => by
          simpa [Nat.add_assoc] using hz.2 (k + 1)⟩

lemma infiniteWalk_eq_of_labels {q : G.State} {z w : ℕ → G.Edge}
    (hz : G.IsInfiniteWalk q z) (hw : G.IsInfiniteWalk q w)
    (hlab : ∀ n, (z n).label = (w n).label) : z = w := by
  funext n
  induction n with
  | zero =>
      exact G.edge_eq_of_same_source_label (hz.2 0).1 (hw.2 0).1
        (hz.1.trans hw.1.symm) (hlab 0)
  | succ n ih =>
      exact G.edge_eq_of_same_source_label (hz.2 (n + 1)).1 (hw.2 (n + 1)).1
        ((hz.2 n).2.symm.trans <| congrArg Edge.dst ih |>.trans (hw.2 n).2)
        (hlab (n + 1))

lemma infiniteWalk_source_eq_of_labels_before {q : G.State}
    {z w : ℕ → G.Edge} (hz : G.IsInfiniteWalk q z)
    (hw : G.IsInfiniteWalk q w) {n : ℕ}
    (hlab : ∀ k < n, (z k).label = (w k).label) :
    (z n).src = (w n).src := by
  induction n with
  | zero => exact hz.1.trans hw.1.symm
  | succ n ih =>
      have heq := G.edge_eq_of_same_source_label (hz.2 n).1 (hw.2 n).1
        (ih fun k hk => hlab k (hk.trans (Nat.lt_succ_self n)))
        (hlab n (Nat.lt_succ_self n))
      exact (hz.2 n).2.symm.trans ((congrArg Edge.dst heq).trans (hw.2 n).2)

lemma infiniteWalk_unique_from_goodSCC
    (hcriterion : G.LiveSCCCriterion) {q : G.State}
    (hqreach : G.Reachable q) (hqlive : G.Live q) (hqcyclic : G.Cyclic q)
    {z w : ℕ → G.Edge} (hz : G.IsInfiniteWalk q z)
    (hw : G.IsInfiniteWalk q w) :
    ∀ n, z n = w n := by
  rcases hcriterion q hqreach hqlive hqcyclic with ⟨hterminal, hsimple⟩
  have step (n : ℕ) (hsrc : (z n).src = (w n).src)
      (hscc : G.SameSCC q (z n).src) :
      z n = w n ∧ G.SameSCC q (z n).dst := by
    have zreach : G.Reachable (z n).src :=
      G.reachable_of_reachable_reaches hqreach hscc.1
    have zlive := G.infiniteWalk_tail_live hz n
    have zdstreach : G.Reachable (z n).dst :=
      G.reachable_of_reachable_reaches zreach
        ⟨[z n], ⟨rfl, (hz.2 n).1, rfl⟩⟩
    have zedge : G.ReachableLiveEdge (z n) :=
      ⟨(hz.2 n).1, zreach, zlive, zdstreach, G.infiniteWalk_edge_live hz n⟩
    have zinternal := hterminal (z n).src hscc (z n) rfl zedge
    have wscc : G.SameSCC q (w n).src := by simpa [hsrc] using hscc
    have wreach : G.Reachable (w n).src :=
      G.reachable_of_reachable_reaches hqreach wscc.1
    have wdstreach : G.Reachable (w n).dst :=
      G.reachable_of_reachable_reaches wreach
        ⟨[w n], ⟨rfl, (hw.2 n).1, rfl⟩⟩
    have wedge : G.ReachableLiveEdge (w n) :=
      ⟨(hw.2 n).1, wreach, G.infiniteWalk_tail_live hw n,
        wdstreach, G.infiniteWalk_edge_live hw n⟩
    have winternal := hterminal (w n).src wscc (w n) rfl wedge
    rcases hsimple (z n).src hscc with ⟨unique, hunique, huniq⟩
    have hzunique : z n = unique := huniq (z n) ⟨rfl, zedge, zinternal⟩
    have hwunique : w n = unique := huniq (w n) ⟨hsrc.symm, wedge, winternal⟩
    exact ⟨hzunique.trans hwunique.symm, zinternal⟩
  have hall : ∀ n, z n = w n ∧ G.SameSCC q (z n).dst := by
    intro n
    induction n with
    | zero =>
        apply step 0 (hz.1.trans hw.1.symm)
        rw [hz.1]
        exact G.sameSCC_refl q
    | succ n ih =>
        apply step (n + 1)
        · exact (hz.2 n).2.symm.trans
            ((congrArg Edge.dst ih.1).trans (hw.2 n).2)
        · simpa [(hz.2 n).2] using ih.2
  exact fun n => (hall n).1

/-- Concatenate `n` copies of a finite edge list. -/
def repeatEdges (u : List G.Edge) : ℕ → List G.Edge
  | 0 => []
  | n + 1 => u ++ repeatEdges u n

@[simp] lemma repeatEdges_zero (u : List G.Edge) : G.repeatEdges u 0 = [] := rfl

@[simp] lemma repeatEdges_succ (u : List G.Edge) (n : ℕ) :
    G.repeatEdges u (n + 1) = u ++ G.repeatEdges u n := rfl

lemma repeatEdges_add (u : List G.Edge) (m n : ℕ) :
    G.repeatEdges u (m + n) = G.repeatEdges u m ++ G.repeatEdges u n := by
  induction m with
  | zero => simp [repeatEdges]
  | succ m ih =>
      rw [Nat.succ_add, repeatEdges_succ, ih, repeatEdges_succ,
        List.append_assoc]

@[simp] lemma length_repeatEdges (u : List G.Edge) (n : ℕ) :
    (G.repeatEdges u n).length = n * u.length := by
  induction n with
  | zero => simp [repeatEdges]
  | succ n ih => simp [repeatEdges, ih, Nat.succ_mul, Nat.add_comm]

lemma isWalk_repeat {q : G.State} {u : List G.Edge}
    (hu : G.IsWalk q u q) (n : ℕ) : G.IsWalk q (G.repeatEdges u n) q := by
  induction n with
  | zero => exact G.isWalk_nil q
  | succ n ih => exact G.isWalk_append hu ih

lemma prepend_repeat_boundary (u : List G.Edge) (z : ℕ → G.Edge) (n : ℕ) :
    G.prependInfinite (G.repeatEdges u n) z (n * u.length) = z 0 := by
  simpa using G.prependInfinite_length_add (G.repeatEdges u n) z 0

lemma prepend_repeat_before_later {f : G.Edge} {fs : List G.Edge}
    (z : ℕ → G.Edge) {n m : ℕ} (hnm : n < m) :
    G.prependInfinite (G.repeatEdges (f :: fs) m) z
        (n * (f :: fs).length) = f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  rw [show n + k + 1 = n + (k + 1) by omega, G.repeatEdges_add,
    G.prependInfinite_append]
  rw [G.prepend_repeat_boundary]
  rfl

lemma infiniteWalk_from_repeated_loop {q r : G.State} {pref loop alt : List G.Edge}
    {z : ℕ → G.Edge} (hpref : G.IsWalk q pref r)
    (hloop : G.IsWalk r loop r) (halt : G.IsWalk r alt (z 0).src)
    (hz : G.IsInfiniteWalk (z 0).src z) (n : ℕ) :
    G.IsInfiniteWalk q
      (G.prependInfinite pref
        (G.prependInfinite (G.repeatEdges loop n)
          (G.prependInfinite alt z))) := by
  apply G.infiniteWalk_prepend hpref
  apply G.infiniteWalk_prepend (G.isWalk_repeat hloop n)
  exact G.infiniteWalk_prepend halt hz

/-- Pumping a nonempty loop before a live alternative whose first label differs
produces infinitely many start-label streams. -/
lemma finite_language_forbids_loop_alternative
    (hfinite : G.InfiniteLabelLanguage.Finite)
    {r s : G.State} {pref fs es : List G.Edge} {f e : G.Edge}
    (hpref : G.IsWalk G.start pref r)
    (hloop : G.IsWalk r (f :: fs) r)
    (halt : G.IsWalk r (e :: es) s)
    (hlive : G.Live s) (hlabel : f.label ≠ e.label) : False := by
  classical
  rcases hlive with ⟨z, hz⟩
  have hz' : G.IsInfiniteWalk (z 0).src z := by
    rw [hz.1]
    exact hz
  have halt' : G.IsWalk r (e :: es) (z 0).src := by
    rw [hz.1]
    exact halt
  let walk : ℕ → ℕ → G.Edge := fun n =>
    G.prependInfinite pref
      (G.prependInfinite (G.repeatEdges (f :: fs) n)
        (G.prependInfinite (e :: es) z))
  have hwalk (n : ℕ) : G.IsInfiniteWalk G.start (walk n) := by
    exact G.infiniteWalk_from_repeated_loop hpref hloop halt' hz' n
  let code : ℕ → G.InfiniteLabelLanguage := fun n =>
    ⟨fun k => (walk n k).label, ⟨walk n, hwalk n, rfl⟩⟩
  have hinj : Function.Injective code := by
    intro n m hnm
    by_contra hne
    have hlt_imp {a b : ℕ} (hab : a < b) (heq : code a = code b) : False := by
      have hv := congrFun (congrArg Subtype.val heq)
        (pref.length + a * (f :: fs).length)
      simp only [code, walk] at hv
      rw [G.prependInfinite_length_add] at hv
      rw [G.prepend_repeat_boundary] at hv
      simp only [prependInfinite, consInfinite] at hv
      rw [G.prependInfinite_length_add] at hv
      rw [G.prepend_repeat_before_later _ hab] at hv
      exact hlabel hv.symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt_imp hlt hnm
    · exact hlt_imp hgt hnm.symm
  letI : Fintype G.InfiniteLabelLanguage := hfinite.fintype
  haveI : Finite ℕ := Finite.of_injective code hinj
  exact Finite.false (inferInstance : Finite ℕ)

lemma cyclic_closed_walk_in_sameSCC {q r : G.State}
    (hq : G.Cyclic q) (hqr : G.SameSCC q r) :
    ∃ f : G.Edge, ∃ fs : List G.Edge, G.IsWalk r (f :: fs) r := by
  rcases hq with ⟨e, es, he⟩
  rcases hqr.1 with ⟨qr, hqrw⟩
  rcases hqr.2 with ⟨rq, hrqw⟩
  let u := rq ++ (e :: es) ++ qr
  have hu : G.IsWalk r u r :=
    G.isWalk_append (G.isWalk_append hrqw he) hqrw
  have hne : u ≠ [] := by
    have : e ∈ u := by simp [u]
    exact List.ne_nil_of_mem this
  rcases u with _ | ⟨f, fs⟩
  · exact (hne rfl).elim
  · exact ⟨f, fs, hu⟩

lemma first_edge_sameSCC {q r : G.State} {f : G.Edge} {fs : List G.Edge}
    (hqr : G.SameSCC q r) (hloop : G.IsWalk r (f :: fs) r) :
    G.SameSCC q f.dst := by
  rcases hloop with ⟨hsrc, hvalid, hrest⟩
  constructor
  · exact G.reaches_trans hqr.1
      ⟨[f], ⟨hsrc, hvalid, rfl⟩⟩
  · exact G.reaches_trans ⟨fs, hrest⟩ hqr.2

lemma first_edge_reachableLive {q r : G.State} {f : G.Edge} {fs : List G.Edge}
    (hqreach : G.Reachable q) (hqlive : G.Live q)
    (hqr : G.SameSCC q r) (hloop : G.IsWalk r (f :: fs) r) :
    G.ReachableLiveEdge f := by
  have hfdst := G.first_edge_sameSCC hqr hloop
  rcases hloop with ⟨hsrc, hvalid, _⟩
  refine ⟨hvalid, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact G.reachable_of_reachable_reaches hqreach hqr.1
  · rw [hsrc]
    exact G.live_of_reaches hqr.2 hqlive
  · exact G.reachable_of_reachable_reaches hqreach hfdst.1
  · exact G.live_of_reaches hfdst.2 hqlive

/-- Trimming to reachable live states preserves the infinite label language. -/
theorem reachable_live_trimming_correct :
    G.InfiniteLabelLanguage =
      {x | ∃ z : ℕ → G.Edge, G.IsInfiniteWalk G.start z ∧
        (∀ n, G.Reachable (z n).src ∧ G.Live (z n).src) ∧
        x = fun n => (z n).label} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_, rfl⟩
    intro n
    constructor
    · exact ⟨List.ofFn fun i : Fin n => z i, G.infiniteWalk_prefix hz n⟩
    · exact G.infiniteWalk_tail_live hz n
  · rintro ⟨z, hz, _, rfl⟩
    exact ⟨z, hz, rfl⟩

/- The core equivalence is proved below through two finite-graph facts.  They
are stated as public lemmas because they are useful independently: finite
languages prohibit a live exit from a recurrent SCC and prohibit two internal
live choices, while the live terminal simple-cycle condition makes every run
uniquely determined by a bounded prefix. -/

lemma finite_language_implies_live_scc_condition
    (hfinite : G.InfiniteLabelLanguage.Finite) : G.LiveSCCCriterion := by
  classical
  intro q hqreach hqlive hqcyclic
  constructor
  · intro r hqr e hesrc helive
    by_contra hout
    rcases G.cyclic_closed_walk_in_sameSCC hqcyclic hqr with ⟨f, fs, hloop⟩
    have hfscc := G.first_edge_sameSCC hqr hloop
    have hlabel : f.label ≠ e.label := by
      intro hlab
      have hef : f = e := G.edge_eq_of_same_source_label
        hloop.2.1 helive.1 (hloop.1.trans hesrc.symm) hlab
      exact hout (hef ▸ hfscc)
    rcases G.reaches_trans hqreach hqr.1 with ⟨pref, hpref⟩
    exact G.finite_language_forbids_loop_alternative
      (s := e.dst) (es := []) hfinite hpref hloop
      (G.isWalk_cons hesrc helive.1 (G.isWalk_nil e.dst))
      helive.2.2.2.2 hlabel
  · intro r hqr
    rcases G.cyclic_closed_walk_in_sameSCC hqcyclic hqr with ⟨f, fs, hloop⟩
    have hfscc := G.first_edge_sameSCC hqr hloop
    have hflive := G.first_edge_reachableLive hqreach hqlive hqr hloop
    refine ⟨f, ⟨hloop.1, hflive, hfscc⟩, ?_⟩
    intro e he
    by_contra hne
    have hlabel : f.label ≠ e.label := by
      intro hlab
      exact hne (G.edge_eq_of_same_source_label he.2.1.1 hloop.2.1
        (he.1.trans hloop.1.symm) hlab.symm)
    rcases G.reaches_trans he.2.2.2 hqr.1 with ⟨back, hback⟩
    have halt : G.IsWalk r (e :: back) r :=
      ⟨he.1, he.2.1.1, hback⟩
    rcases G.reaches_trans hqreach hqr.1 with ⟨pref, hpref⟩
    have hrlive : G.Live r := G.live_of_reaches hqr.2 hqlive
    exact (G.finite_language_forbids_loop_alternative hfinite hpref hloop
      halt hrlive hlabel).elim

lemma live_scc_condition_implies_finite_language
    (hcriterion : G.LiveSCCCriterion) : G.InfiniteLabelLanguage.Finite := by
  classical
  let N := Fintype.card G.State + 1
  let witness (x : G.InfiniteLabelLanguage) : ℕ → G.Edge :=
    Classical.choose x.property
  have witness_spec (x : G.InfiniteLabelLanguage) :
      G.IsInfiniteWalk G.start (witness x) ∧
        x.1 = fun n => (witness x n).label :=
    Classical.choose_spec x.property
  let code : G.InfiniteLabelLanguage → (Fin N → G.Label) :=
    fun x i => x.1 i
  have code_injective : Function.Injective code := by
    intro x y hcode
    let z := witness x
    let w := witness y
    have hz : G.IsInfiniteWalk G.start z := (witness_spec x).1
    have hw : G.IsInfiniteWalk G.start w := (witness_spec y).1
    have hlabN : ∀ k < N, (z k).label = (w k).label := by
      intro k hk
      have h := congrFun hcode (⟨k, hk⟩ : Fin N)
      simpa [code, z, w, (witness_spec x).2, (witness_spec y).2] using h
    obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin N => (z i).src) (by simp [N])
    have ordered : ∃ i j : Fin N, i < j ∧ (z i).src = (z j).src := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨a, b, hlt, heq⟩
      · exact ⟨b, a, hgt, heq.symm⟩
    rcases ordered with ⟨i, j, hij, heqij⟩
    let q := (z i).src
    have hqreach : G.Reachable q := by
      exact ⟨List.ofFn fun k : Fin i => z k,
        G.infiniteWalk_prefix hz i⟩
    have hqlive : G.Live q := G.infiniteWalk_tail_live hz i
    have hqcyclic : G.Cyclic q := by
      let tail : ℕ → G.Edge := fun k => z (i + k)
      let u : List G.Edge := List.ofFn fun k : Fin (j - i) => tail k
      have hu : G.IsWalk q u q := by
        have hp := G.infiniteWalk_prefix (G.infiniteWalk_tail hz i) (j - i)
        simpa [q, u, tail, Nat.add_sub_of_le hij.le, heqij] using hp
      have hune : u ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        simp [u] at hlen
        omega
      rcases u with _ | ⟨f, fs⟩
      · exact (hune rfl).elim
      · exact ⟨f, fs, hu⟩
    have hsrc : (z i).src = (w i).src :=
      G.infiniteWalk_source_eq_of_labels_before hz hw
        (fun k hk => hlabN k (hk.trans i.isLt))
    have htails := G.infiniteWalk_unique_from_goodSCC hcriterion hqreach hqlive hqcyclic
      (G.infiniteWalk_tail hz i)
      (show G.IsInfiniteWalk q (fun k => w (i + k)) by
        have ht := G.infiniteWalk_tail hw i
        simpa [q, hsrc] using ht)
    apply Subtype.ext
    funext k
    rw [(witness_spec x).2, (witness_spec y).2]
    by_cases hki : k < i
    · exact hlabN k (hki.trans i.isLt)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hki)
      exact congrArg Edge.label (htails d)
  letI : Finite G.InfiniteLabelLanguage := Finite.of_injective code code_injective
  exact Set.finite_coe_iff.mp inferInstance

/-- Named forward direction of the live-SCC characterization. -/
theorem infiniteLabelLanguage_finite_implies_liveSCCCriterion
    (hfinite : G.InfiniteLabelLanguage.Finite) : G.LiveSCCCriterion :=
  G.finite_language_implies_live_scc_condition hfinite

/-- Named reverse direction of the live-SCC characterization. -/
theorem liveSCCCriterion_implies_infiniteLabelLanguage_finite
    (hcriterion : G.LiveSCCCriterion) : G.InfiniteLabelLanguage.Finite :=
  G.live_scc_condition_implies_finite_language hcriterion

/-- Infinite labels are finite exactly for terminal simple cyclic SCCs after
reachable-live trimming. -/
theorem infiniteLabelLanguage_finite_iff_liveSCCCriterion :
    G.InfiniteLabelLanguage.Finite ↔ G.LiveSCCCriterion :=
  ⟨G.infiniteLabelLanguage_finite_implies_liveSCCCriterion,
    G.liveSCCCriterion_implies_infiniteLabelLanguage_finite⟩

/-- A Boolean certificate carries independently checkable reachability,
liveness, cyclicity, and SCC tables. -/
structure SCCCertificate where
  reachable : G.State → Bool
  live : G.State → Bool
  cyclic : G.State → Bool
  sameSCC : G.State → G.State → Bool
  reachable_correct : ∀ q, reachable q = true ↔ G.Reachable q
  live_correct : ∀ q, live q = true ↔ G.Live q
  cyclic_correct : ∀ q, cyclic q = true ↔ G.Cyclic q
  sameSCC_correct : ∀ q r, sameSCC q r = true ↔ G.SameSCC q r

/-- A supplied Boolean SCC table gives an executable decision procedure for
membership in the same SCC. -/
def sameSCC_decidable_of_certificate (c : G.SCCCertificate) (q r : G.State) :
    Decidable (G.SameSCC q r) :=
  decidable_of_iff (c.sameSCC q r = true) (c.sameSCC_correct q r)

/-- Terminality in the finite reachable-live graph is decidable from the
certificate tables. -/
def terminalInReachableLive_decidable_of_certificate
    (c : G.SCCCertificate) (q : G.State) :
    Decidable (G.TerminalInReachableLive q) := by
  letI (v : G.State) : Decidable (G.Reachable v) :=
    decidable_of_iff (c.reachable v = true) (c.reachable_correct v)
  letI (v : G.State) : Decidable (G.Live v) :=
    decidable_of_iff (c.live v = true) (c.live_correct v)
  letI (v w : G.State) : Decidable (G.SameSCC v w) :=
    G.sameSCC_decidable_of_certificate c v w
  unfold TerminalInReachableLive ReachableLiveEdge Edge.Valid
  infer_instance

/-- The edge-sensitive simple-cycle property is decidable from the finite
certificate tables. -/
def simpleDirectedCycleSCC_decidable_of_certificate
    (c : G.SCCCertificate) (q : G.State) :
    Decidable (G.SimpleDirectedCycleSCC q) := by
  letI (v : G.State) : Decidable (G.Reachable v) :=
    decidable_of_iff (c.reachable v = true) (c.reachable_correct v)
  letI (v : G.State) : Decidable (G.Live v) :=
    decidable_of_iff (c.live v = true) (c.live_correct v)
  letI (v w : G.State) : Decidable (G.SameSCC v w) :=
    G.sameSCC_decidable_of_certificate c v w
  unfold SimpleDirectedCycleSCC ReachableLiveEdge Edge.Valid
  infer_instance

/-- All predicates in the live-SCC condition are decidable from the supplied
finite Boolean tables.  In particular, this decides the complete certificate,
not only membership in one SCC. -/
def liveSCCCriterion_decidable_of_certificate (c : G.SCCCertificate) :
    Decidable G.LiveSCCCriterion := by
  letI (q : G.State) : Decidable (G.Reachable q) :=
    decidable_of_iff (c.reachable q = true) (c.reachable_correct q)
  letI (q : G.State) : Decidable (G.Live q) :=
    decidable_of_iff (c.live q = true) (c.live_correct q)
  letI (q : G.State) : Decidable (G.Cyclic q) :=
    decidable_of_iff (c.cyclic q = true) (c.cyclic_correct q)
  letI (q r : G.State) : Decidable (G.SameSCC q r) :=
    G.sameSCC_decidable_of_certificate c q r
  letI (q : G.State) : Decidable (G.TerminalInReachableLive q) :=
    G.terminalInReachableLive_decidable_of_certificate c q
  letI (q : G.State) : Decidable (G.SimpleDirectedCycleSCC q) :=
    G.simpleDirectedCycleSCC_decidable_of_certificate c q
  unfold LiveSCCCriterion
  infer_instance

/-- The Boolean answer produced by an SCC certificate has the advertised
logical meaning. -/
theorem sccCertificate_checked (c : G.SCCCertificate) (q r : G.State) :
    c.sameSCC q r = true ↔ G.SameSCC q r :=
  c.sameSCC_correct q r

/-- The executable decision attached to a supplied certificate returns true
exactly when the complete terminal-simple live-SCC condition holds. -/
theorem liveSCCCriterion_decide_eq_true_iff (c : G.SCCCertificate) :
    @decide G.LiveSCCCriterion
      (G.liveSCCCriterion_decidable_of_certificate c) = true ↔
        G.LiveSCCCriterion := by
  exact @decide_eq_true_iff G.LiveSCCCriterion
    (G.liveSCCCriterion_decidable_of_certificate c)

/-- Generic finite-fiber image transfer.  It applies to any later evaluation
map once finite fibers on the relevant source set have been proved. -/
theorem finite_iff_finite_image_of_finite_fibers
    {X Y : Type*} (f : X → Y) (s : Set X)
    (hfiber : ∀ y ∈ f '' s, (s ∩ f ⁻¹' {y}).Finite) :
    s.Finite ↔ (f '' s).Finite := by
  constructor
  · exact fun hs => hs.image f
  · intro himage
    exact Set.Finite.of_finite_fibers f himage fun y hy => hfiber y hy

/-! ## Checked unreachable-bad-SCC counterexample -/

/-- State `0` is the accessible one-symbol loop.  States `1,2` form an
unreachable live SCC with two label choices at each state. -/
def unreachableBadGraph : Graph where
  State := Fin 3
  Label := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  labelFintype := inferInstance
  labelDecEq := inferInstance
  start := 0
  transition q a :=
    if q = 0 then if a = false then some 0 else none
    else if a = false then some 1 else some 2

/-- The counterexample's start language consists only of the all-false word. -/
theorem unreachableBadGraph_language_eq_singleton :
    unreachableBadGraph.InfiniteLabelLanguage = {fun _ => false} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have step (n : ℕ) (hsrc : (z n).src = (0 : Fin 3)) :
        (z n).label = false ∧ (z n).dst = (0 : Fin 3) := by
      have hv := (hz.2 n).1
      simp only [Edge.Valid, unreachableBadGraph] at hv
      rw [hsrc] at hv
      simp only [ite_true] at hv
      cases hlabel : (z n).label <;> simp [hlabel] at hv
      exact ⟨rfl, hv.symm⟩
    have hs : ∀ n, (z n).src = (0 : Fin 3) := by
      intro n
      induction n with
      | zero => exact hz.1
      | succ n ih => exact (hz.2 n).2.symm.trans (step n ih).2
    change (fun n => (z n).label) = (fun _ => false)
    funext n
    exact (step n (hs n)).1
  · intro hx
    change x = (fun _ => false) at hx
    subst x
    let e : unreachableBadGraph.Edge :=
      ⟨(0 : Fin 3), false, (0 : Fin 3)⟩
    refine ⟨fun _ => e, ?_, rfl⟩
    refine ⟨rfl, fun n => ?_⟩
    exact ⟨by simp [e, Edge.Valid, unreachableBadGraph], rfl⟩

/-- Consequently the accessible infinite language is finite. -/
theorem unreachableBadGraph_language_finite :
    unreachableBadGraph.InfiniteLabelLanguage.Finite := by
  rw [unreachableBadGraph_language_eq_singleton]
  exact Set.finite_singleton _

/-- The all-state analogue fails: unreachable state `1` is live and cyclic but
its SCC is not an edge/label-sensitive simple directed cycle. -/
theorem untrimmed_all_state_criterion_fails :
    ¬ unreachableBadGraph.UntrimmedLiveSCCCriterion := by
  intro hall
  let e11 : unreachableBadGraph.Edge := ⟨(1 : Fin 3), false, (1 : Fin 3)⟩
  let e12 : unreachableBadGraph.Edge := ⟨(1 : Fin 3), true, (2 : Fin 3)⟩
  let e21 : unreachableBadGraph.Edge := ⟨(2 : Fin 3), false, (1 : Fin 3)⟩
  let e22 : unreachableBadGraph.Edge := ⟨(2 : Fin 3), true, (2 : Fin 3)⟩
  have he11 : e11.Valid := by simp [e11, Edge.Valid, unreachableBadGraph]
  have he12 : e12.Valid := by simp [e12, Edge.Valid, unreachableBadGraph]
  have he21 : e21.Valid := by simp [e21, Edge.Valid, unreachableBadGraph]
  have he22 : e22.Valid := by simp [e22, Edge.Valid, unreachableBadGraph]
  have hlive : unreachableBadGraph.Live (1 : Fin 3) := by
    refine ⟨fun _ => e11, ?_⟩
    exact ⟨rfl, fun _ => ⟨he11, rfl⟩⟩
  have hlive2 : unreachableBadGraph.Live (2 : Fin 3) := by
    refine ⟨fun _ => e22, ?_⟩
    exact ⟨rfl, fun _ => ⟨he22, rfl⟩⟩
  have hcyclic : unreachableBadGraph.Cyclic (1 : Fin 3) :=
    ⟨e11, [], ⟨rfl, he11, rfl⟩⟩
  have hscc12 : unreachableBadGraph.SameSCC (1 : Fin 3) (2 : Fin 3) :=
    ⟨⟨[e12], ⟨rfl, he12, rfl⟩⟩,
      ⟨[e21], ⟨rfl, he21, rfl⟩⟩⟩
  have hsimple := (hall (1 : Fin 3) hlive hcyclic).2
  rcases hsimple (1 : Fin 3)
    (unreachableBadGraph.sameSCC_refl (1 : Fin 3)) with ⟨e, _, hunique⟩
  have h11 : e11 = e := hunique e11
    ⟨rfl, ⟨he11, hlive, hlive⟩,
      unreachableBadGraph.sameSCC_refl (1 : Fin 3)⟩
  have h12 : e12 = e := hunique e12
    ⟨rfl, ⟨he12, hlive, hlive2⟩, hscc12⟩
  have := congrArg Edge.label (h11.trans h12.symm)
  simp [e11, e12] at this

#print axioms reachable_live_trimming_correct
#print axioms infiniteLabelLanguage_finite_implies_liveSCCCriterion
#print axioms liveSCCCriterion_implies_infiniteLabelLanguage_finite
#print axioms infiniteLabelLanguage_finite_iff_liveSCCCriterion
#print axioms sccCertificate_checked
#print axioms liveSCCCriterion_decide_eq_true_iff
#print axioms finite_iff_finite_image_of_finite_fibers
#print axioms unreachableBadGraph_language_eq_singleton
#print axioms unreachableBadGraph_language_finite
#print axioms untrimmed_all_state_criterion_fails

end Graph

end DecimalFactorEntropy.T46LiveSCC
