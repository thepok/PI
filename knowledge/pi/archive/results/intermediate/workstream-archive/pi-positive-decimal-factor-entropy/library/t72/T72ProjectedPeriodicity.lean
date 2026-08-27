import TheoryLib.PiPositiveDecimalFactorEntropy.T46T46T46LiveSCC
import TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP
import TheoryLib.PiPositiveDecimalFactorEntropy.T65T65RationalCoreCertificate

/-!
# T72: exact projected periodicity certificates

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The source was formulated locally and has no external source URL.
This module proves finite-graph sibling statements used by the conditional C6
route. It does not prove the canonical positive-entropy question, the uniform
linear-depth hypothesis, C6, C1, or any new fact about pi. The T70 note is used
only as an unverified roadmap; every result below is proved in Lean.
-/

noncomputable section

namespace DecimalFactorEntropy.T72ProjectedPeriodicity

open DecimalFactorComplexity
open DecimalFactorEntropy.T46LiveSCC
open DecimalFactorEntropy.T48EndpointCarryKMP
open DecimalFactorEntropy.T65RationalCoreCertificate

abbrev Graph := DecimalFactorEntropy.T46LiveSCC.Graph

namespace Graph

variable (G : Graph)

/-- A valid edge whose two endpoints lie in the complete SCC of `q`. -/
def InternalEdge (q : G.State) (e : G.Edge) : Prop :=
  e.Valid ∧ G.SameSCC q e.src ∧ G.SameSCC q e.dst

/-- A right-infinite walk from the explicitly supplied vertex `v`, all of
whose edge endpoints remain in the complete SCC of `q`. -/
def IsInternalInfiniteWalk (q v : G.State) (z : ℕ → G.Edge) : Prop :=
  G.IsInfiniteWalk v z ∧ ∀ n, G.InternalEdge q (z n)

/-- Circular primitivity for a nonempty table. No smaller positive rotation is
a period of the table. -/
def PrimitiveWord {A : Type*} {p : ℕ} (P : Fin p → A) : Prop :=
  0 < p ∧ ∀ d : Fin p, 0 < d.val →
    ∃ i j : Fin p, j.val = (i.val + d.val) % p ∧ P j ≠ P i

/-- One SCC has a common primitive projected word and compatible vertex
phases. Every internal edge emits the symbol at its source phase and advances
the phase by exactly one. -/
structure PrimitivePhaseCertificate {A : Type*}
    (q : G.State) (rho : G.Edge → A) where
  period : ℕ
  period_pos : 0 < period
  root : Fin period → A
  primitive : PrimitiveWord root
  phase : G.State → Fin period
  output_eq : ∀ e : G.Edge, G.InternalEdge q e → rho e = root (phase e.src)
  phase_step : ∀ e : G.Edge, G.InternalEdge q e →
    phase e.dst =
      ⟨(phase e.src).val.succ % period, Nat.mod_lt _ period_pos⟩

/-- Semantic SCC-local condition: every internal right-infinite hidden walk,
from every vertex of the SCC, has eventually periodic projected output. -/
def EveryInternalProjectionEventuallyPeriodic {A : Type*}
    (q : G.State) (rho : G.Edge → A) : Prop :=
  ∀ v : G.State, G.SameSCC q v → ∀ z : ℕ → G.Edge,
    G.IsInternalInfiniteWalk q v z →
      EventuallyPeriodic (fun n => rho (z n))

/-- Add a natural offset to a certificate phase, modulo its positive period. -/
def PrimitivePhaseCertificate.phaseOffset {A : Type*} {q : G.State}
    {rho : G.Edge → A} (c : PrimitivePhaseCertificate G q rho)
    (v : G.State) (n : ℕ) : Fin c.period :=
  ⟨((c.phase v).val + n) % c.period, Nat.mod_lt _ c.period_pos⟩

lemma phase_along_internal_walk {A : Type*} {q v : G.State}
    {rho : G.Edge → A} (c : PrimitivePhaseCertificate G q rho)
    {z : ℕ → G.Edge} (hz : G.IsInternalInfiniteWalk q v z) :
    ∀ n, c.phase (z n).src =
      PrimitivePhaseCertificate.phaseOffset G c v n := by
  intro n
  induction n with
  | zero =>
      apply Fin.ext
      simpa [PrimitivePhaseCertificate.phaseOffset,
        Nat.mod_eq_of_lt (c.phase v).isLt] using
        congrArg (fun s => (c.phase s).val) hz.1.1
  | succ n ih =>
      calc
        c.phase (z (n + 1)).src = c.phase (z n).dst := by
          rw [hz.1.2 n |>.2]
        _ = ⟨(c.phase (z n).src).val.succ % c.period,
              Nat.mod_lt _ c.period_pos⟩ := c.phase_step (z n) (hz.2 n)
        _ = PrimitivePhaseCertificate.phaseOffset G c v (n + 1) := by
          apply Fin.ext
          have hval := congrArg Fin.val ih
          simp only [PrimitivePhaseCertificate.phaseOffset] at hval ⊢
          rw [hval]
          change Nat.ModEq c.period
            ((((c.phase v).val + n) % c.period) + 1)
            ((c.phase v).val + (n + 1))
          simpa [Nat.add_assoc] using
            (Nat.mod_modEq ((c.phase v).val + n) c.period).add_right 1

/-- SCC-local forward direction. The certificate gives periodicity from index
zero, uniformly for every internal hidden walk and every SCC start vertex. -/
theorem primitivePhaseCertificate_implies_everyInternalProjectionEventuallyPeriodic
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (c : PrimitivePhaseCertificate G q rho) :
    G.EveryInternalProjectionEventuallyPeriodic q rho := by
  intro v _hv z hz
  refine ⟨0, c.period, c.period_pos, ?_⟩
  intro i
  have hleft := phase_along_internal_walk G c hz (i + c.period)
  have hright := phase_along_internal_walk G c hz i
  simp only [zero_add]
  change rho (z (i + c.period)) = rho (z i)
  rw [c.output_eq (z (i + c.period)) (hz.2 (i + c.period))]
  rw [c.output_eq (z i) (hz.2 i)]
  rw [hleft, hright]
  congr 1
  apply Fin.ext
  simp [PrimitivePhaseCertificate.phaseOffset, Nat.add_mod]

/-! ## Closed-walk block infrastructure -/

lemma isWalk_get_valid {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (i : Fin u.length) : (u.get i).Valid := by
  induction u generalizing s with
  | nil => exact Fin.elim0 i
  | cons e u ih =>
      rcases hu with ⟨_hsrc, he, hu⟩
      refine Fin.cases he (fun j => ?_) i
      exact ih hu j

lemma isWalk_get_zero_src {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (hne : u ≠ []) :
    (u.get ⟨0, List.length_pos_of_ne_nil hne⟩).src = s := by
  rcases u with _ | ⟨e, u⟩
  · exact (hne rfl).elim
  · exact hu.1

lemma isWalk_get_adjacent {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (i : ℕ) (hi : i + 1 < u.length) :
    (u.get ⟨i, by omega⟩).dst = (u.get ⟨i + 1, hi⟩).src := by
  induction u generalizing s i with
  | nil => simp at hi
  | cons e u ih =>
      rcases hu with ⟨_hsrc, _he, hu⟩
      cases i with
      | zero =>
          simpa using (isWalk_get_zero_src G hu (by
            intro h
            simp [h] at hi)) |>.symm
      | succ i =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih hu i (by simpa using hi)

lemma isWalk_take_to_get_src {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (i : Fin u.length) :
    G.IsWalk s (u.take i.val) (u.get i).src := by
  induction u generalizing s with
  | nil => exact Fin.elim0 i
  | cons e u ih =>
      rcases hu with ⟨hsrc, he, hu⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hsrc] using G.isWalk_nil s
      · simpa using G.isWalk_cons hsrc he (ih hu j)

lemma isWalk_drop_succ_from_get_dst {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (i : Fin u.length) :
    G.IsWalk (u.get i).dst (u.drop (i.val + 1)) t := by
  induction u generalizing s with
  | nil => exact Fin.elim0 i
  | cons e u ih =>
      rcases hu with ⟨_hsrc, _he, hu⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu
      · simpa [Nat.add_assoc] using ih hu j

lemma closedWalk_get_internal {q : G.State} {u : List G.Edge}
    (hu : G.IsWalk q u q) (i : Fin u.length) :
    G.InternalEdge q (u.get i) := by
  refine ⟨isWalk_get_valid G hu i, ?_, ?_⟩
  · constructor
    · exact ⟨u.take i.val, isWalk_take_to_get_src G hu i⟩
    · refine ⟨(u.get i) :: u.drop (i.val + 1), ?_⟩
      exact G.isWalk_cons rfl (isWalk_get_valid G hu i)
        (isWalk_drop_succ_from_get_dst G hu i)
  · constructor
    · refine ⟨u.take i.val ++ [u.get i], ?_⟩
      exact G.isWalk_append (isWalk_take_to_get_src G hu i)
        (G.isWalk_cons rfl (isWalk_get_valid G hu i) (G.isWalk_nil _))
    · exact ⟨u.drop (i.val + 1), isWalk_drop_succ_from_get_dst G hu i⟩

/-! ## An explicit non-eventually-periodic control stream -/

/-- Boolean spikes exactly at powers of two. -/
noncomputable def powerTwoSpike (n : ℕ) : Bool := by
  classical
  exact if ∃ k : ℕ, n = 2 ^ k then true else false

@[simp] lemma powerTwoSpike_pow (k : ℕ) : powerTwoSpike (2 ^ k) = true := by
  simp [powerTwoSpike]

lemma powerTwoSpike_eq_false_of_between_powers {n k : ℕ}
    (hlow : 2 ^ k < n) (hhigh : n < 2 ^ (k + 1)) :
    powerTwoSpike n = false := by
  rw [powerTwoSpike, if_neg]
  rintro ⟨j, rfl⟩
  have hkj : k < j :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlow
  have hjk : j < k + 1 :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hhigh
  omega

/-- The powers-of-two control stream is not eventually periodic. -/
theorem powerTwoSpike_not_eventuallyPeriodic :
    ¬ EventuallyPeriodic powerTwoSpike := by
  rintro ⟨N, p, hp, hperiod⟩
  let k := max N p
  have hk : max N p < 2 ^ k := by
    simpa [k] using (max N p).lt_two_pow_self
  let n := 2 ^ k
  have hN : N ≤ n := by dsimp [n]; omega
  have hpn : p < n := by dsimp [n]; omega
  have hlow : 2 ^ k < n + p := by dsimp [n]; omega
  have hhigh : n + p < 2 ^ (k + 1) := by
    rw [pow_succ]
    dsimp [n]
    omega
  have h := hperiod (n - N)
  rw [Nat.add_sub_of_le hN] at h
  rw [powerTwoSpike_pow k] at h
  have hfalse := powerTwoSpike_eq_false_of_between_powers hlow hhigh
  rw [hfalse] at h
  simp at h

lemma getElem?_repeatEdges_eq_mod (u : List G.Edge) (hu : u ≠ [])
    (k i : ℕ) (hi : i < (G.repeatEdges u k).length) :
    (G.repeatEdges u k)[i]? = u[i % u.length]? := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
      rw [G.repeatEdges_succ]
      by_cases hil : i < u.length
      · rw [List.getElem?_append_left hil, Nat.mod_eq_of_lt hil]
      · have hle : u.length ≤ i := Nat.le_of_not_gt hil
        rw [List.getElem?_append_right hle]
        have hi' : i - u.length < (G.repeatEdges u k).length := by
          rw [G.length_repeatEdges] at hi ⊢
          rw [Nat.succ_mul] at hi
          omega
        rw [ih (i - u.length) hi']
        congr 1
        exact Nat.mod_eq_sub_mod hle |>.symm

lemma isWalk_get_last_dst {s t : G.State} {u : List G.Edge}
    (hu : G.IsWalk s u t) (hne : u ≠ []) :
    (u.get ⟨u.length - 1, by
      have := List.length_pos_of_ne_nil hne
      omega⟩).dst = t := by
  let i : Fin u.length := ⟨u.length - 1, by
    have := List.length_pos_of_ne_nil hne
    omega⟩
  have hs := isWalk_drop_succ_from_get_dst G hu i
  have hlen : i.val + 1 = u.length := by
    dsimp [i]
    have := List.length_pos_of_ne_nil hne
    omega
  rw [hlen, List.drop_length] at hs
  exact hs

/-- Select equal-length closed blocks according to a Boolean control stream. -/
def blockWalk (u v : List G.Edge) (hu : u ≠ []) (hlen : u.length = v.length)
    (b : ℕ → Bool) (n : ℕ) : G.Edge :=
  if b (n / u.length) then
    u.get ⟨n % u.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hu)⟩
  else
    v.get ⟨n % u.length, by
      rw [← hlen]
      exact Nat.mod_lt _ (List.length_pos_of_ne_nil hu)⟩

lemma blockWalk_mul_add (u v : List G.Edge) (hu : u ≠ [])
    (hlen : u.length = v.length) (b : ℕ → Bool)
    (k i : ℕ) (hi : i < u.length) :
    G.blockWalk u v hu hlen b (k * u.length + i) =
      if b k then u.get ⟨i, hi⟩ else
        v.get ⟨i, by simpa [← hlen] using hi⟩ := by
  have hdiv : (k * u.length + i) / u.length = k := by
    rw [Nat.mul_comm k u.length,
      Nat.mul_add_div (List.length_pos_of_ne_nil hu)]
    simp [Nat.div_eq_of_lt hi]
  have hmod : (k * u.length + i) % u.length = i := by
    rw [Nat.mul_comm k u.length, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  simp [blockWalk, hdiv, hmod]

lemma blockWalk_isInfiniteWalk {q : G.State} {u v : List G.Edge}
    (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    (hv : G.IsWalk q v q) (hv0 : v ≠ [])
    (hlen : u.length = v.length) (b : ℕ → Bool) :
    G.IsInfiniteWalk q (G.blockWalk u v hu0 hlen b) := by
  have hL : 0 < u.length := List.length_pos_of_ne_nil hu0
  constructor
  · rw [show (0 : ℕ) = 0 * u.length + 0 by simp]
    rw [blockWalk_mul_add G u v hu0 hlen b 0 0 hL]
    split
    · exact isWalk_get_zero_src G hu hu0
    · exact isWalk_get_zero_src G hv hv0
  · intro n
    let k := n / u.length
    let i := n % u.length
    have hi : i < u.length := Nat.mod_lt _ hL
    have hn : n = k * u.length + i := by
      dsimp [k, i]
      nth_rw 1 [← Nat.div_add_mod n u.length]
      rw [Nat.mul_comm]
    constructor
    · rw [hn, blockWalk_mul_add G u v hu0 hlen b k i hi]
      split
      · exact isWalk_get_valid G hu ⟨i, hi⟩
      · exact isWalk_get_valid G hv ⟨i, by simpa [← hlen] using hi⟩
    · by_cases hnext : i + 1 < u.length
      · have hadd : k * u.length + i + 1 = k * u.length + (i + 1) := by omega
        rw [hn, hadd,
          blockWalk_mul_add G u v hu0 hlen b k i hi,
          blockWalk_mul_add G u v hu0 hlen b k (i + 1) hnext]
        split
        · exact isWalk_get_adjacent G hu i hnext
        · exact isWalk_get_adjacent G hv i (by simpa [← hlen] using hnext)
      · have hilast : i = u.length - 1 := by omega
        have hadd : k * u.length + i + 1 = (k + 1) * u.length + 0 := by
          rw [hilast, Nat.succ_mul]
          omega
        rw [hn, hadd,
          blockWalk_mul_add G u v hu0 hlen b k i hi,
          blockWalk_mul_add G u v hu0 hlen b (k + 1) 0 hL]
        have hulast := isWalk_get_last_dst G hu hu0
        have hvlast := isWalk_get_last_dst G hv hv0
        have huzero := isWalk_get_zero_src G hu hu0
        have hvzero := isWalk_get_zero_src G hv hv0
        split <;> split
        · simpa [hilast] using hulast.trans huzero.symm
        · simpa [hilast] using hulast.trans hvzero.symm
        · simpa [hilast, hlen] using hvlast.trans huzero.symm
        · simpa [hilast, hlen] using hvlast.trans hvzero.symm

lemma blockWalk_isInternalInfiniteWalk {q : G.State} {u v : List G.Edge}
    (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    (hv : G.IsWalk q v q) (hv0 : v ≠ [])
    (hlen : u.length = v.length) (b : ℕ → Bool) :
    G.IsInternalInfiniteWalk q q (G.blockWalk u v hu0 hlen b) := by
  refine ⟨blockWalk_isInfiniteWalk G hu hu0 hv hv0 hlen b, ?_⟩
  intro n
  let k := n / u.length
  let i := n % u.length
  have hL : 0 < u.length := List.length_pos_of_ne_nil hu0
  have hi : i < u.length := Nat.mod_lt _ hL
  have hn : n = k * u.length + i := by
    dsimp [k, i]
    nth_rw 1 [← Nat.div_add_mod n u.length]
    rw [Nat.mul_comm]
  rw [hn, blockWalk_mul_add G u v hu0 hlen b k i hi]
  split
  · exact closedWalk_get_internal G hu ⟨i, hi⟩
  · exact closedWalk_get_internal G hv ⟨i, by simpa [← hlen] using hi⟩

lemma eventuallyPeriodic_iterate_period {X : Type*} {x : ℕ → X}
    {N p : ℕ} (hperiod : ∀ i, x (N + i + p) = x (N + i))
    (i m : ℕ) : x (N + i + m * p) = x (N + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        x (N + i + (m + 1) * p) = x (N + (i + m * p) + p) := by
          rw [Nat.succ_mul]
          congr 1
          omega
        _ = x (N + (i + m * p)) := hperiod (i + m * p)
        _ = x (N + i + m * p) := by congr 1 <;> omega
        _ = x (N + i) := ih

/-- Universal projected eventual periodicity forces equal projected symbols at
corresponding positions of any two equal-length nonempty based closed walks. -/
lemma equalLength_closedWalk_output_eq
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hEP : G.EveryInternalProjectionEventuallyPeriodic q rho)
    {u v : List G.Edge} (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    (hv : G.IsWalk q v q) (hv0 : v ≠ [])
    (hlen : u.length = v.length) (i : Fin u.length) :
    rho (u.get i) = rho (v.get ⟨i.val, by simpa [← hlen] using i.isLt⟩) := by
  by_contra hne
  let z := G.blockWalk u v hu0 hlen powerTwoSpike
  have hz : G.IsInternalInfiniteWalk q q z :=
    blockWalk_isInternalInfiniteWalk G hu hu0 hv hv0 hlen powerTwoSpike
  obtain ⟨N, p, hp, hperiod⟩ := hEP q (G.sameSCC_refl q) z hz
  apply powerTwoSpike_not_eventuallyPeriodic
  refine ⟨N, p, hp, ?_⟩
  intro j
  let k := N + j
  let base := k * u.length + i.val
  have hL : 0 < u.length := List.length_pos_of_ne_nil hu0
  have hk : N ≤ k := by simp [k]
  have hkL : k ≤ k * u.length := Nat.le_mul_of_pos_right k hL
  have hNbase : N ≤ base := hk.trans (hkL.trans (Nat.le_add_right _ _))
  have hm := eventuallyPeriodic_iterate_period
    (x := fun n => rho (z n)) (N := N) (p := p)
    hperiod (base - N) u.length
  have hbase : N + (base - N) = base := Nat.add_sub_of_le hNbase
  have hshift : base + u.length * p = (k + p) * u.length + i.val := by
    dsimp [base]
    calc
      k * u.length + i.val + u.length * p =
          k * u.length + p * u.length + i.val := by
            rw [Nat.mul_comm u.length p]
            omega
      _ = (k + p) * u.length + i.val := by
        simp [k, Nat.add_mul, Nat.add_assoc]
  rw [hbase, hshift] at hm
  change powerTwoSpike (N + j + p) = powerTwoSpike (N + j)
  change powerTwoSpike (k + p) = powerTwoSpike k
  have hzshift :
      z ((k + p) * u.length + i.val) =
        if powerTwoSpike (k + p) then u.get i else
          v.get ⟨i.val, by simpa [← hlen] using i.isLt⟩ := by
    exact blockWalk_mul_add G u v hu0 hlen powerTwoSpike (k + p) i.val i.isLt
  have hzbase :
      z (k * u.length + i.val) =
        if powerTwoSpike k then u.get i else
          v.get ⟨i.val, by simpa [← hlen] using i.isLt⟩ := by
    exact blockWalk_mul_add G u v hu0 hlen powerTwoSpike k i.val i.isLt
  rw [hzshift, hzbase] at hm
  cases hk₁ : powerTwoSpike (k + p) <;>
    cases hk₀ : powerTwoSpike k <;> simp_all

lemma repeatEdges_get_periodic (u : List G.Edge) (hu : u ≠ [])
    (k : ℕ) (hk : 0 < k) (n : ℕ) :
    (G.repeatEdges u k).get ⟨n % (G.repeatEdges u k).length,
        Nat.mod_lt _ (by
          rw [G.length_repeatEdges]
          exact Nat.mul_pos hk (List.length_pos_of_ne_nil hu))⟩ =
      u.get ⟨n % u.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hu)⟩ := by
  let U := G.repeatEdges u k
  have hUpos : 0 < U.length := by
    dsimp [U]
    rw [G.length_repeatEdges]
    exact Nat.mul_pos hk (List.length_pos_of_ne_nil hu)
  let i := n % U.length
  have hi : i < U.length := Nat.mod_lt _ hUpos
  have hg := getElem?_repeatEdges_eq_mod G u hu k i hi
  have hir : i % u.length < u.length :=
    Nat.mod_lt _ (List.length_pos_of_ne_nil hu)
  have hg' : U.get ⟨i, hi⟩ =
      u.get ⟨i % u.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hu)⟩ := by
    change U[i]? = u[i % u.length]? at hg
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hir] at hg
    exact Option.some.inj hg
  have hdvd : u.length ∣ U.length := by
    rw [show U.length = k * u.length by simp [U]]
    exact dvd_mul_left _ _
  have hmod : i % u.length = n % u.length := by
    dsimp [i]
    exact Nat.mod_mod_of_dvd n hdvd
  simpa [U, i, hmod] using hg'

/-- All nonempty based closed walks in the SCC have the same literal projected
right-infinite periodic word at the common base vertex. -/
lemma basedClosedWalk_periodicOutput_eq
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hEP : G.EveryInternalProjectionEventuallyPeriodic q rho)
    {u v : List G.Edge} (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    (hv : G.IsWalk q v q) (hv0 : v ≠ []) (n : ℕ) :
    rho (u.get ⟨n % u.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hu0)⟩) =
      rho (v.get ⟨n % v.length,
        Nat.mod_lt _ (List.length_pos_of_ne_nil hv0)⟩) := by
  let U := G.repeatEdges u v.length
  let V := G.repeatEdges v u.length
  have huLen : 0 < u.length := List.length_pos_of_ne_nil hu0
  have hvLen : 0 < v.length := List.length_pos_of_ne_nil hv0
  have hU0 : U ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [U, Nat.mul_pos hvLen huLen]
  have hV0 : V ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [V, Nat.mul_pos huLen hvLen]
  have hUVlen : U.length = V.length := by
    simp [U, V, Nat.mul_comm]
  let i : Fin U.length :=
    ⟨n % U.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hU0)⟩
  have heq := equalLength_closedWalk_output_eq G hEP
    (G.isWalk_repeat hu v.length) hU0
    (G.isWalk_repeat hv u.length) hV0 hUVlen i
  have hUget := repeatEdges_get_periodic G u hu0 v.length hvLen n
  have hVget := repeatEdges_get_periodic G v hv0 u.length huLen n
  rw [hUget] at heq
  have hVi : (V.get ⟨i.val, by simpa [← hUVlen] using i.isLt⟩) =
      V.get ⟨n % V.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hV0)⟩ := by
    apply congrArg (fun j : Fin V.length => V.get j)
    apply Fin.ext
    dsimp [i]
    rw [hUVlen]
  rw [hVi, hVget] at heq
  exact heq

/-! ## Least positive periods and primitive finite roots -/

def StreamPeriod {A : Type*} (x : ℕ → A) (p : ℕ) : Prop :=
  0 < p ∧ ∀ n, x (n + p) = x n

lemma streamPeriod_iterate {A : Type*} {x : ℕ → A} {p : ℕ}
    (hp : StreamPeriod x p) (n k : ℕ) : x (n + k * p) = x n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul]
      calc
        x (n + (k * p + p)) = x ((n + k * p) + p) := by congr 1 <;> omega
        _ = x (n + k * p) := hp.2 (n + k * p)
        _ = x n := ih

lemma streamPeriod_mod {A : Type*} {x : ℕ → A} {p : ℕ}
    (hp : StreamPeriod x p) (n : ℕ) : x (n % p) = x n := by
  have hi := streamPeriod_iterate hp (n % p) (n / p)
  have hdecomp : n % p + n / p * p = n := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div n p
  simpa [hdecomp] using hi.symm

lemma least_streamPeriod_dvd {A : Type*} {x : ℕ → A} {p d : ℕ}
    (hp : StreamPeriod x p)
    (hminimal : ∀ r : ℕ, StreamPeriod x r → p ≤ r)
    (hd : StreamPeriod x d) : p ∣ d := by
  by_contra hnot
  have hremPos : 0 < d % p := Nat.pos_of_ne_zero (by
    intro hzero
    exact hnot (Nat.dvd_iff_mod_eq_zero.mpr hzero))
  have hremLt : d % p < p := Nat.mod_lt _ hp.1
  have hrem : StreamPeriod x (d % p) := by
    refine ⟨hremPos, ?_⟩
    intro n
    have hiter := streamPeriod_iterate hp (n + d % p) (d / p)
    have hdecomp : d % p + d / p * p = d := by
      rw [Nat.mul_comm]
      exact Nat.mod_add_div d p
    calc
      x (n + d % p) = x (n + d % p + d / p * p) := hiter.symm
      _ = x (n + d) := by congr 1 <;> omega
      _ = x n := hd.2 n
  exact (not_le_of_gt hremLt) (hminimal (d % p) hrem)

/-- A stream with one positive period has a least positive period, a primitive
finite root table, and that least period divides every other positive period. -/
theorem exists_primitive_root_of_streamPeriod
    {A : Type*} (x : ℕ → A) {m : ℕ} (hm : StreamPeriod x m) :
    ∃ p : ℕ, ∃ hp : 0 < p, ∃ P : Fin p → A,
      p ≤ m ∧ PrimitiveWord P ∧
      (∀ n, x n = P ⟨n % p, Nat.mod_lt _ hp⟩) ∧
      ∀ d, StreamPeriod x d → p ∣ d := by
  classical
  let good : ℕ → Prop := fun p => StreamPeriod x p
  have hex : ∃ p, good p := ⟨m, hm⟩
  let p := Nat.find hex
  have hp : StreamPeriod x p := Nat.find_spec hex
  have hminimal : ∀ d, StreamPeriod x d → p ≤ d := by
    intro d hd
    exact Nat.find_min' hex hd
  let P : Fin p → A := fun i => x i.val
  refine ⟨p, hp.1, P, hminimal m hm, ?_, ?_, ?_⟩
  · refine ⟨hp.1, ?_⟩
    intro d hdpos
    by_contra hnone
    push Not at hnone
    have hall (i : Fin p) :
        P ⟨(i.val + d.val) % p, Nat.mod_lt _ hp.1⟩ = P i := by
      exact hnone i ⟨(i.val + d.val) % p, Nat.mod_lt _ hp.1⟩ rfl
    have hdperiod : StreamPeriod x d.val := by
      refine ⟨hdpos, ?_⟩
      intro n
      calc
        x (n + d.val) = x ((n + d.val) % p) :=
          (streamPeriod_mod hp (n + d.val)).symm
        _ = x ((n % p + d.val) % p) := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt d.isLt]
        _ = P ⟨(n % p + d.val) % p, Nat.mod_lt _ hp.1⟩ := rfl
        _ = P ⟨n % p, Nat.mod_lt _ hp.1⟩ := by
          exact hall ⟨n % p, Nat.mod_lt _ hp.1⟩
        _ = x (n % p) := rfl
        _ = x n := streamPeriod_mod hp n
    exact (not_le_of_gt d.isLt) (hminimal d.val hdperiod)
  · intro n
    exact (streamPeriod_mod hp n).symm
  · intro d hd
    exact least_streamPeriod_dvd hp hminimal hd

/-! ## Reconstruction of phases from closed walks -/

/-- The literal projected periodic output of a nonempty based closed walk. -/
def closedWalkOutput {A : Type*} (rho : G.Edge → A)
    (u : List G.Edge) (hu0 : u ≠ []) (n : ℕ) : A :=
  rho (u.get ⟨n % u.length, Nat.mod_lt _ (List.length_pos_of_ne_nil hu0)⟩)

lemma closedWalkOutput_period_length {A : Type*} (rho : G.Edge → A)
    (u : List G.Edge) (hu0 : u ≠ []) :
    StreamPeriod (closedWalkOutput G rho u hu0) u.length := by
  refine ⟨List.length_pos_of_ne_nil hu0, ?_⟩
  intro n
  unfold closedWalkOutput
  congr 2
  apply Fin.ext
  simp

lemma baseOutput_hasPeriod_of_closedWalk
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hEP : G.EveryInternalProjectionEventuallyPeriodic q rho)
    {u w : List G.Edge} (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    (hw : G.IsWalk q w q) (hw0 : w ≠ []) :
    StreamPeriod (closedWalkOutput G rho u hu0) w.length := by
  refine ⟨List.length_pos_of_ne_nil hw0, ?_⟩
  intro n
  unfold closedWalkOutput
  rw [basedClosedWalk_periodicOutput_eq G hEP hu hu0 hw hw0 (n + w.length)]
  rw [basedClosedWalk_periodicOutput_eq G hEP hu hu0 hw hw0 n]
  congr 2
  apply Fin.ext
  simp

lemma basePeriod_dvd_closedWalk_length
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hEP : G.EveryInternalProjectionEventuallyPeriodic q rho)
    {u : List G.Edge} (hu : G.IsWalk q u q) (hu0 : u ≠ [])
    {p : ℕ}
    (hdiv : ∀ d, StreamPeriod (closedWalkOutput G rho u hu0) d → p ∣ d)
    {w : List G.Edge} (hw : G.IsWalk q w q) : p ∣ w.length := by
  by_cases hw0 : w = []
  · subst w
    exact dvd_zero p
  · exact hdiv w.length
      (baseOutput_hasPeriod_of_closedWalk G hEP hu hu0 hw hw0)

/-- SCC-local reverse direction. Reachability, liveness, cyclicity, the
projection, every start vertex, and all internal hidden walks are explicit. -/
theorem everyInternalProjectionEventuallyPeriodic_implies_primitivePhaseCertificate
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hqReachable : G.Reachable q) (hqLive : G.Live q) (hqCyclic : G.Cyclic q)
    (hEP : G.EveryInternalProjectionEventuallyPeriodic q rho) :
    Nonempty (G.PrimitivePhaseCertificate q rho) := by
  classical
  rcases hqCyclic with ⟨e0, es0, hu⟩
  let u : List G.Edge := e0 :: es0
  have hu0 : u ≠ [] := by simp [u]
  have hu' : G.IsWalk q u q := by simpa [u] using hu
  let S := closedWalkOutput G rho u hu0
  have hSperiod : StreamPeriod S u.length := by
    exact closedWalkOutput_period_length G rho u hu0
  obtain ⟨p, hp, P, hple, hprimitive, hroot, hdiv⟩ :=
    exists_primitive_root_of_streamPeriod S hSperiod
  let pathTo : G.State → List G.Edge := fun v =>
    if hv : G.SameSCC q v then Classical.choose hv.1 else []
  have pathTo_walk (v : G.State) (hv : G.SameSCC q v) :
      G.IsWalk q (pathTo v) v := by
    simp only [pathTo, dif_pos hv]
    exact Classical.choose_spec hv.1
  let phase : G.State → Fin p := fun v =>
    ⟨(pathTo v).length % p, Nat.mod_lt _ hp⟩
  apply Nonempty.intro
  refine
    { period := p
      period_pos := hp
      root := P
      primitive := hprimitive
      phase := phase
      output_eq := ?_
      phase_step := ?_ }
  · intro e he
    let back : List G.Edge := Classical.choose he.2.2.2
    have hback : G.IsWalk e.dst back q := Classical.choose_spec he.2.2.2
    let loop : List G.Edge := pathTo e.src ++ [e] ++ back
    have hloop : G.IsWalk q loop q := by
      dsimp [loop]
      exact G.isWalk_append
        (G.isWalk_append (pathTo_walk e.src he.2.1)
          (G.isWalk_cons rfl he.1 (G.isWalk_nil e.dst))) hback
    have hloop0 : loop ≠ [] := by
      intro hnil
      have hmem : e ∈ loop := by simp [loop]
      simpa [hnil] using hmem
    have hcompat := basedClosedWalk_periodicOutput_eq G hEP hu' hu0
      hloop hloop0 (pathTo e.src).length
    have hlt : (pathTo e.src).length < loop.length := by
      simp [loop]
    have hedge :
        loop.get ⟨(pathTo e.src).length % loop.length,
          Nat.mod_lt _ (List.length_pos_of_ne_nil hloop0)⟩ = e := by
      have hind :
          (⟨(pathTo e.src).length % loop.length,
            Nat.mod_lt _ (List.length_pos_of_ne_nil hloop0)⟩ : Fin loop.length) =
          ⟨(pathTo e.src).length, hlt⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hlt
      rw [hind]
      simp [loop]
    rw [hedge] at hcompat
    change rho e = P (phase e.src)
    rw [← hcompat]
    exact hroot (pathTo e.src).length
  · intro e he
    let back : List G.Edge := Classical.choose he.2.2.2
    have hback : G.IsWalk e.dst back q := Classical.choose_spec he.2.2.2
    let loopSrc : List G.Edge := pathTo e.src ++ [e] ++ back
    let loopDst : List G.Edge := pathTo e.dst ++ back
    have hloopSrc : G.IsWalk q loopSrc q := by
      dsimp [loopSrc]
      exact G.isWalk_append
        (G.isWalk_append (pathTo_walk e.src he.2.1)
          (G.isWalk_cons rfl he.1 (G.isWalk_nil e.dst))) hback
    have hloopDst : G.IsWalk q loopDst q := by
      exact G.isWalk_append (pathTo_walk e.dst he.2.2) hback
    have hdSrc : p ∣ loopSrc.length :=
      basePeriod_dvd_closedWalk_length G hEP hu' hu0 hdiv hloopSrc
    have hdDst : p ∣ loopDst.length :=
      basePeriod_dvd_closedWalk_length G hEP hu' hu0 hdiv hloopDst
    have hmodSrc : (pathTo e.src).length + 1 + back.length ≡ 0 [MOD p] := by
      have hlenSrc : loopSrc.length =
          (pathTo e.src).length + 1 + back.length := by
        simp [loopSrc]
        omega
      rw [← hlenSrc]
      exact hdSrc.modEq_zero_nat
    have hmodDst : (pathTo e.dst).length + back.length ≡ 0 [MOD p] := by
      simpa [loopDst] using hdDst.modEq_zero_nat
    have hmod : (pathTo e.src).length + 1 ≡ (pathTo e.dst).length [MOD p] :=
      Nat.ModEq.add_right_cancel' back.length (hmodSrc.trans hmodDst.symm)
    apply Fin.ext
    change (pathTo e.dst).length % p =
      (((pathTo e.src).length % p + 1) % p)
    rw [← hmod]
    simp [Nat.add_mod]

/-- Exact SCC-local equivalence, with the start-derived reachability, liveness,
cyclicity, projection, and all internal starts explicit. -/
theorem primitivePhaseCertificate_iff_everyInternalProjectionEventuallyPeriodic
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hqReachable : G.Reachable q) (hqLive : G.Live q) (hqCyclic : G.Cyclic q) :
    Nonempty (G.PrimitivePhaseCertificate q rho) ↔
      G.EveryInternalProjectionEventuallyPeriodic q rho := by
  constructor
  · rintro ⟨c⟩
    exact primitivePhaseCertificate_implies_everyInternalProjectionEventuallyPeriodic G c
  · exact everyInternalProjectionEventuallyPeriodic_implies_primitivePhaseCertificate G
      hqReachable hqLive hqCyclic

lemma PrimitivePhaseCertificate.phaseOffset_succ
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (c : G.PrimitivePhaseCertificate q rho) (v : G.State) (n : ℕ) :
    ⟨(PrimitivePhaseCertificate.phaseOffset G c v n).val.succ % c.period,
      Nat.mod_lt _ c.period_pos⟩ =
      PrimitivePhaseCertificate.phaseOffset G c v (n + 1) := by
  apply Fin.ext
  change Nat.ModEq c.period
    ((((c.phase v).val + n) % c.period) + 1)
    ((c.phase v).val + (n + 1))
  simpa [Nat.add_assoc] using
    (Nat.mod_modEq ((c.phase v).val + n) c.period).add_right 1

lemma PrimitivePhaseCertificate.phase_closedWalk_source
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (c : G.PrimitivePhaseCertificate q rho)
    {u : List G.Edge} (hu : G.IsWalk q u q) (i : Fin u.length) :
    c.phase (u.get i).src =
      PrimitivePhaseCertificate.phaseOffset G c q i.val := by
  have H : ∀ n : ℕ, ∀ hn : n < u.length,
      c.phase (u.get ⟨n, hn⟩).src =
        PrimitivePhaseCertificate.phaseOffset G c q n := by
    intro n hn
    induction n with
    | zero =>
        apply Fin.ext
        simpa [PrimitivePhaseCertificate.phaseOffset,
          Nat.mod_eq_of_lt (c.phase q).isLt] using
          congrArg (fun s => (c.phase s).val)
            (isWalk_get_zero_src G hu (by
              intro hnil
              simp [hnil] at hn))
    | succ n ih =>
        have hn' : n < u.length := by omega
        calc
          c.phase (u.get ⟨n + 1, hn⟩).src =
              c.phase (u.get ⟨n, hn'⟩).dst := by
                rw [isWalk_get_adjacent G hu n hn]
          _ = ⟨(c.phase (u.get ⟨n, hn'⟩).src).val.succ % c.period,
                Nat.mod_lt _ c.period_pos⟩ :=
            c.phase_step _ (closedWalk_get_internal G hu ⟨n, hn'⟩)
          _ = ⟨(PrimitivePhaseCertificate.phaseOffset G c q n).val.succ % c.period,
                Nat.mod_lt _ c.period_pos⟩ := by rw [ih hn']
          _ = PrimitivePhaseCertificate.phaseOffset G c q (n + 1) :=
            PrimitivePhaseCertificate.phaseOffset_succ G c q n
  exact H i.val i.isLt

/-- Any primitive-phase certificate on a cyclic SCC has period at most the
number of graph states. This supplies the finite search bound. -/
theorem PrimitivePhaseCertificate.period_le_card_state
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (c : G.PrimitivePhaseCertificate q rho) (hqCyclic : G.Cyclic q) :
    c.period ≤ Fintype.card G.State := by
  rcases hqCyclic with ⟨e, es, hu⟩
  let u : List G.Edge := e :: es
  have hu0 : u ≠ [] := by simp [u]
  have hu' : G.IsWalk q u q := by simpa [u] using hu
  have hlast := PrimitivePhaseCertificate.phase_closedWalk_source G c hu'
    (⟨u.length - 1, by
      have := List.length_pos_of_ne_nil hu0
      omega⟩ : Fin u.length)
  have hstep := c.phase_step
    (u.get ⟨u.length - 1, by
      have := List.length_pos_of_ne_nil hu0
      omega⟩)
    (closedWalk_get_internal G hu' _)
  have hdst := isWalk_get_last_dst G hu' hu0
  have hend : c.phase q = PrimitivePhaseCertificate.phaseOffset G c q u.length := by
    calc
      c.phase q = c.phase (u.get ⟨u.length - 1, by
          have := List.length_pos_of_ne_nil hu0
          omega⟩).dst := by rw [hdst]
      _ = ⟨(c.phase (u.get ⟨u.length - 1, by
          have := List.length_pos_of_ne_nil hu0
          omega⟩).src).val.succ % c.period,
          Nat.mod_lt _ c.period_pos⟩ := hstep
      _ = ⟨(PrimitivePhaseCertificate.phaseOffset G c q (u.length - 1)).val.succ %
          c.period, Nat.mod_lt _ c.period_pos⟩ := by rw [hlast]
      _ = PrimitivePhaseCertificate.phaseOffset G c q ((u.length - 1) + 1) :=
        PrimitivePhaseCertificate.phaseOffset_succ G c q (u.length - 1)
      _ = PrimitivePhaseCertificate.phaseOffset G c q u.length := by
        rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil hu0)]
  have hval := congrArg Fin.val hend
  have hmod : (c.phase q).val + u.length ≡ (c.phase q).val [MOD c.period] := by
    unfold Nat.ModEq
    simp only [PrimitivePhaseCertificate.phaseOffset] at hval
    rw [Nat.mod_eq_of_lt (c.phase q).isLt]
    exact hval.symm
  have hdvd : c.period ∣ u.length :=
    Nat.modEq_zero_iff_dvd.mp
      (Nat.ModEq.add_left_cancel' (c.phase q).val hmod)
  have hple : c.period ≤ u.length :=
    Nat.le_of_dvd (List.length_pos_of_ne_nil hu0) hdvd
  let f : Fin c.period → G.State := fun i =>
    (u.get ⟨i.val, i.isLt.trans_le hple⟩).src
  have hf : Function.Injective f := by
    intro i j hij
    have hphase := congrArg c.phase hij
    have hiPhase := PrimitivePhaseCertificate.phase_closedWalk_source G c hu'
      (⟨i.val, i.isLt.trans_le hple⟩ : Fin u.length)
    have hjPhase := PrimitivePhaseCertificate.phase_closedWalk_source G c hu'
      (⟨j.val, j.isLt.trans_le hple⟩ : Fin u.length)
    rw [hiPhase, hjPhase] at hphase
    have hvals := congrArg Fin.val hphase
    simp only [PrimitivePhaseCertificate.phaseOffset] at hvals
    have hmodij : (c.phase q).val + i.val ≡
        (c.phase q).val + j.val [MOD c.period] := hvals
    have hijmod := Nat.ModEq.add_left_cancel' (c.phase q).val hmodij
    unfold Nat.ModEq at hijmod
    rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hijmod
    exact Fin.ext hijmod
  simpa using Fintype.card_le_of_injective f hf

/-! ## Finite certificates, global equivalence, and decidability -/

/-- Positive candidate periods bounded by the finite state count. -/
abbrev PeriodIndex :=
  {p : Fin (Fintype.card G.State + 1) // 0 < p.val}

/-- All bounded root and phase tables form a finite type when the output
alphabet is finite. -/
abbrev BoundedPhaseData (A : Type*) :=
  Σ p : G.PeriodIndex,
    (Fin p.val → A) × (G.State → Fin p.val)

def BoundedPhaseData.Valid {A : Type*} (q : G.State) (rho : G.Edge → A)
    (d : G.BoundedPhaseData A) : Prop :=
  PrimitiveWord d.2.1 ∧
    ∀ e : G.Edge, G.InternalEdge q e →
      rho e = d.2.1 (d.2.2 e.src) ∧
      d.2.2 e.dst =
        ⟨(d.2.2 e.src).val.succ % d.1.val, Nat.mod_lt _ d.1.2⟩

def BoundedPhaseData.toCertificate {A : Type*} {q : G.State}
    {rho : G.Edge → A} (d : G.BoundedPhaseData A)
    (hd : BoundedPhaseData.Valid G q rho d) : G.PrimitivePhaseCertificate q rho where
  period := d.1.val
  period_pos := d.1.2
  root := d.2.1
  primitive := hd.1
  phase := d.2.2
  output_eq := fun e he => (hd.2 e he).1
  phase_step := fun e he => (hd.2 e he).2

lemma PrimitivePhaseCertificate.exists_boundedPhaseData
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (c : G.PrimitivePhaseCertificate q rho)
    (hc : c.period ≤ Fintype.card G.State) :
    ∃ d : G.BoundedPhaseData A, BoundedPhaseData.Valid G q rho d := by
  let pi : G.PeriodIndex :=
    ⟨⟨c.period, by omega⟩, c.period_pos⟩
  let d : G.BoundedPhaseData A := ⟨pi, c.root, c.phase⟩
  refine ⟨d, c.primitive, ?_⟩
  intro e he
  exact ⟨c.output_eq e he, c.phase_step e he⟩

/-- The bounded finite search predicate is exactly the semantic SCC-local
eventual-periodicity property. -/
theorem exists_boundedPhaseData_iff_everyInternalProjectionEventuallyPeriodic
    {A : Type*} {q : G.State} {rho : G.Edge → A}
    (hqReachable : G.Reachable q) (hqLive : G.Live q) (hqCyclic : G.Cyclic q) :
    (∃ d : G.BoundedPhaseData A, BoundedPhaseData.Valid G q rho d) ↔
      G.EveryInternalProjectionEventuallyPeriodic q rho := by
  constructor
  · rintro ⟨d, hd⟩
    exact primitivePhaseCertificate_implies_everyInternalProjectionEventuallyPeriodic G
      (BoundedPhaseData.toCertificate G d hd)
  · intro hEP
    rcases everyInternalProjectionEventuallyPeriodic_implies_primitivePhaseCertificate G
      hqReachable hqLive hqCyclic hEP with ⟨c⟩
    exact PrimitivePhaseCertificate.exists_boundedPhaseData G c
      (PrimitivePhaseCertificate.period_le_card_state G c hqCyclic)

/-- The global projected primitive-phase criterion ranges over every SCC that
is reachable from the distinguished start, live, and cyclic. -/
def GlobalPrimitivePhaseCriterion {A : Type*} (rho : G.Edge → A) : Prop :=
  ∀ q : G.State, G.Reachable q → G.Live q → G.Cyclic q →
    ∃ d : G.BoundedPhaseData A, BoundedPhaseData.Valid G q rho d

/-- Global semantic condition with the same start, liveness, cyclicity, SCC,
hidden-walk, and projection quantifiers. -/
def GlobalEveryInternalProjectionEventuallyPeriodic {A : Type*}
    (rho : G.Edge → A) : Prop :=
  ∀ q : G.State, G.Reachable q → G.Live q → G.Cyclic q →
    G.EveryInternalProjectionEventuallyPeriodic q rho

/-- Named global reachable-live equivalence. -/
theorem globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic
    {A : Type*} (rho : G.Edge → A) :
    G.GlobalPrimitivePhaseCriterion rho ↔
      G.GlobalEveryInternalProjectionEventuallyPeriodic rho := by
  constructor
  · intro h q hreach hlive hcyclic
    exact (exists_boundedPhaseData_iff_everyInternalProjectionEventuallyPeriodic G
      hreach hlive hcyclic).mp (h q hreach hlive hcyclic)
  · intro h q hreach hlive hcyclic
    exact (exists_boundedPhaseData_iff_everyInternalProjectionEventuallyPeriodic G
      hreach hlive hcyclic).mpr (h q hreach hlive hcyclic)

/-- A supplied T46 Boolean SCC certificate makes validity of one bounded phase
table executable. -/
def boundedPhaseDataValid_decidable_of_certificate
    {A : Type*} [Fintype A] [DecidableEq A]
    (cert : G.SCCCertificate) (q : G.State) (rho : G.Edge → A)
    (d : G.BoundedPhaseData A) :
    Decidable (BoundedPhaseData.Valid G q rho d) := by
  letI (v w : G.State) : Decidable (G.SameSCC v w) :=
    G.sameSCC_decidable_of_certificate cert v w
  letI : Decidable (PrimitiveWord d.2.1) := by
    unfold PrimitiveWord
    infer_instance
  letI (e : G.Edge) : Decidable (G.InternalEdge q e) := by
    unfold InternalEdge DecimalFactorEntropy.T46LiveSCC.Graph.Edge.Valid
    infer_instance
  unfold BoundedPhaseData.Valid
  infer_instance

/-- Executable decidability of the complete global projected criterion from
the explicit finite T46 reachability/liveness/cyclicity/SCC tables. -/
def globalPrimitivePhaseCriterion_decidable_of_certificate
    {A : Type*} [Fintype A] [DecidableEq A]
    (cert : G.SCCCertificate) (rho : G.Edge → A) :
    Decidable (G.GlobalPrimitivePhaseCriterion rho) := by
  letI (q : G.State) : Decidable (G.Reachable q) :=
    decidable_of_iff (cert.reachable q = true) (cert.reachable_correct q)
  letI (q : G.State) : Decidable (G.Live q) :=
    decidable_of_iff (cert.live q = true) (cert.live_correct q)
  letI (q : G.State) : Decidable (G.Cyclic q) :=
    decidable_of_iff (cert.cyclic q = true) (cert.cyclic_correct q)
  letI (v w : G.State) : Decidable (G.SameSCC v w) :=
    G.sameSCC_decidable_of_certificate cert v w
  letI (q : G.State) (d : G.BoundedPhaseData A) :
      Decidable (BoundedPhaseData.Valid G q rho d) :=
    boundedPhaseDataValid_decidable_of_certificate G cert q rho d
  unfold GlobalPrimitivePhaseCriterion
  infer_instance

/-- The Boolean result of the global finite checker has its exact semantic
meaning. -/
theorem globalPrimitivePhaseCriterion_decide_eq_true_iff
    {A : Type*} [Fintype A] [DecidableEq A]
    (cert : G.SCCCertificate) (rho : G.Edge → A) :
    @decide (G.GlobalPrimitivePhaseCriterion rho)
      (G.globalPrimitivePhaseCriterion_decidable_of_certificate cert rho) = true ↔
      G.GlobalEveryInternalProjectionEventuallyPeriodic rho := by
  rw [@decide_eq_true_iff (G.GlobalPrimitivePhaseCriterion rho)
    (G.globalPrimitivePhaseCriterion_decidable_of_certificate cert rho)]
  exact globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic G rho

/-- Global SCC certificates control the projection of every infinite walk from
the distinguished start: a finite prefix leads to one recurrent SCC. -/
theorem infiniteWalk_projection_eventuallyPeriodic_of_globalPrimitivePhaseCriterion
    {A : Type*} (rho : G.Edge → A)
    (hglobal : G.GlobalPrimitivePhaseCriterion rho)
    {z : ℕ → G.Edge} (hz : G.IsInfiniteWalk G.start z) :
    EventuallyPeriodic (fun n => rho (z n)) := by
  classical
  obtain ⟨q, hqinf'⟩ :=
    Finite.exists_infinite_fiber (fun n : ℕ => (z n).src)
  have hqinf : ((fun n : ℕ => (z n).src) ⁻¹' {q}).Infinite :=
    Set.infinite_coe_iff.mp hqinf'
  obtain ⟨i, hi⟩ := hqinf.nonempty
  have hiq : (z i).src = q := by simpa using hi
  obtain ⟨j, hj, hij⟩ := hqinf.exists_gt i
  have hjq : (z j).src = q := by simpa using hj
  have hqReach : G.Reachable q := by
    rw [← hiq]
    exact ⟨List.ofFn fun k : Fin i => z k, G.infiniteWalk_prefix hz i⟩
  have hqLive : G.Live q := by
    rw [← hiq]
    exact G.infiniteWalk_tail_live hz i
  have hqCyclic : G.Cyclic q := by
    rw [← hiq]
    exact cyclic_of_infiniteWalk_source_repeat G hz hij (hiq.trans hjq.symm)
  let tail : ℕ → G.Edge := fun n => z (i + n)
  have htailWalk : G.IsInfiniteWalk q tail := by
    simpa [tail, hiq] using G.infiniteWalk_tail hz i
  have hstay : ∀ n, G.SameSCC q (tail n).src := by
    intro n
    constructor
    · rw [← hiq]
      exact infiniteWalk_reaches_source G hz (Nat.le_add_right i n)
    · obtain ⟨k, hk, hik⟩ := hqinf.exists_gt (i + n)
      have hkq : (z k).src = q := by simpa using hk
      rw [← hkq]
      exact infiniteWalk_reaches_source G hz hik.le
  have htail : G.IsInternalInfiniteWalk q q tail := by
    refine ⟨htailWalk, ?_⟩
    intro n
    refine ⟨(htailWalk.2 n).1, hstay n, ?_⟩
    rw [(htailWalk.2 n).2]
    exact hstay (n + 1)
  have hsemantic :=
    (globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic G rho).mp
      hglobal
  obtain ⟨N, p, hp, hperiod⟩ :=
    hsemantic q hqReach hqLive hqCyclic q (G.sameSCC_refl q) tail htail
  refine ⟨i + N, p, hp, ?_⟩
  intro n
  have h := hperiod n
  simpa [tail, Nat.add_assoc] using h

end Graph

/-! ## T48 endpoint-complete coordinate-zero specialization -/

namespace T48

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.FactorComplexity
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The exact T48 projection: coordinate zero of every endpoint-complete
digit-column edge label. -/
def coordinateZeroProjection {w : List (Fin 10)} {hw : w ≠ []} {R : ℕ}
    (e : (carryKMPGraph w hw R).Edge) : Fin 10 :=
  e.label.digits ⟨0, by omega⟩

/-- Named SCC-local T48 specialization, retaining the nonempty forbidden word,
inclusive depth, SCC state, start reachability, liveness, and cyclicity. -/
theorem endpointComplete_local_primitivePhase_iff_coordinateZeroEventuallyPeriodic
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (q : (carryKMPGraph w hw R).State)
    (hqReachable : (carryKMPGraph w hw R).Reachable q)
    (hqLive : (carryKMPGraph w hw R).Live q)
    (hqCyclic : (carryKMPGraph w hw R).Cyclic q) :
    Nonempty (Graph.PrimitivePhaseCertificate (carryKMPGraph w hw R) q
      coordinateZeroProjection) ↔
    Graph.EveryInternalProjectionEventuallyPeriodic (carryKMPGraph w hw R) q
      coordinateZeroProjection :=
  Graph.primitivePhaseCertificate_iff_everyInternalProjectionEventuallyPeriodic
    (carryKMPGraph w hw R) hqReachable hqLive hqCyclic

/-- Named global T48 specialization over every SCC reachable from the
synthetic endpoint-complete start and satisfying the explicit live/cyclic
hypotheses. -/
theorem endpointComplete_global_primitivePhase_iff_coordinateZeroEventuallyPeriodic
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ) :
    Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw R)
        coordinateZeroProjection ↔
      Graph.GlobalEveryInternalProjectionEventuallyPeriodic (carryKMPGraph w hw R)
        coordinateZeroProjection :=
  Graph.globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic
    (carryKMPGraph w hw R) coordinateZeroProjection

/-- Executable T48 specialization from an explicit endpoint-complete SCC
table. -/
theorem endpointComplete_global_decide_eq_true_iff
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (cert : (carryKMPGraph w hw R).SCCCertificate) :
    @decide (Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw R)
      coordinateZeroProjection)
      (Graph.globalPrimitivePhaseCriterion_decidable_of_certificate
        (carryKMPGraph w hw R) cert coordinateZeroProjection) = true ↔
      Graph.GlobalEveryInternalProjectionEventuallyPeriodic (carryKMPGraph w hw R)
        coordinateZeroProjection :=
  Graph.globalPrimitivePhaseCriterion_decide_eq_true_iff
    (carryKMPGraph w hw R) cert coordinateZeroProjection

/-- A global T48 projected certificate makes coordinate zero eventually
periodic on every accepted path from the synthetic endpoint-complete start. -/
theorem accepted_coordinateZero_eventuallyPeriodic
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (hglobal : Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw R)
      coordinateZeroProjection)
    {x : ℕ → Label R}
    (hx : x ∈ (carryKMPGraph w hw R).InfiniteLabelLanguage) :
    EventuallyPeriodic (fun n => (x n).digits ⟨0, by omega⟩) := by
  rcases hx with ⟨z, hz, rfl⟩
  simpa [coordinateZeroProjection] using
    Graph.infiniteWalk_projection_eventuallyPeriodic_of_globalPrimitivePhaseCriterion
      (carryKMPGraph w hw R) coordinateZeroProjection hglobal hz

/-- Fully expanded endpoint/start interface for the T48 specialization. The
initial KMP states, every carry in `[-1,16]`, every raw transition, the first
endpoint label, and the complete encoding equality are explicit hypotheses. -/
theorem exactEndpointRawRun_coordinateZero_eventuallyPeriodic
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (hglobal : Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw R)
      coordinateZeroProjection)
    (x : ℕ → Label R) (q : ℕ → RawState w hw R)
    (d : ℕ → DigitColumn R)
    (hkmp : ∀ i, (q 0).kmp i = (singletonFamily w hw).initialState)
    (hcarry : ∀ j : Fin R, (-1 : ℤ) ≤ ((q 0).carry j).1 ∧
      ((q 0).carry j).1 ≤ 16)
    (hstep : ∀ n, RawStep (q n) (d n) (q (n + 1)))
    (hfirst : x 0 = Label.initial (q 0).carry (d 0))
    (hencode : x = encodeLabels q d) :
    EventuallyPeriodic (fun n => (x n).digits ⟨0, by omega⟩) := by
  apply accepted_coordinateZero_eventuallyPeriodic w hw R hglobal
  exact (t48_accepted_iff_exact_endpoint_raw_run hw R x).2
    ⟨q, d, hkmp, hcarry, hstep, hfirst, hencode⟩

/-- T65's endpoint-inclusive rational-core consequence under the explicit
T72 global projected certificate at one word and one depth. -/
theorem endpointComplete_globalProjectedPhase_implies_rationalCore
    (w : List (Fin 10)) (hw : w ≠ []) (R : ℕ)
    (hglobal : Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw R)
      coordinateZeroProjection) :
    RationalCoreAt w R := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_graphEvaluation_image_of_mem_core hw R y hy
  have hd := accepted_coordinateZero_eventuallyPeriodic w hw R hglobal hx
  have hrat := eventuallyPeriodic_decimal_evaluation_rational
    (fun n => (x n).digits ⟨0, by omega⟩) hd
  rw [← hxy]
  rcases hrat with ⟨_rat, _hvalue, hratCircle⟩
  exact hratCircle

/-- The sole T72 uniform frontier: one nonnegative linear coefficient and one
intercept bound a depth carrying the exact global projected certificate for
every nonempty decimal word. No witness is asserted. -/
def UniformLinearProjectedPhaseHypothesis : Prop :=
  ∃ L C : ℝ, 0 ≤ L ∧
    ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw r)
          coordinateZeroProjection

theorem uniformLinearProjectedPhaseHypothesis_iff_quantifiers :
    UniformLinearProjectedPhaseHypothesis ↔
      ∃ L C : ℝ, 0 ≤ L ∧
        ∀ w : List (Fin 10), ∀ hw : w ≠ [],
          ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
            Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw r)
              coordinateZeroProjection := by
  rfl

/-- At each positive word length, finitely many projected certificates combine
at one depth, where every endpoint-safe core is rational. -/
theorem exists_common_rational_core_depth_from_projectedPhase
    (L C : ℝ)
    (hgraph : ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw r)
          coordinateZeroProjection)
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
        Graph.GlobalPrimitivePhaseCriterion
          (carryKMPGraph (List.ofFn u) (hwne u) (r u))
          coordinateZeroProjection := by
    simpa [r] using Classical.choose_spec (hgraph (List.ofFn u) (hwne u))
  let depths : Finset ℕ := Finset.univ.image r
  have hdepths : depths.Nonempty := by
    change (Finset.univ.image r).Nonempty
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
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
    exact endpointComplete_globalProjectedPhase_implies_rationalCore
      (List.ofFn u) (hwne u) (r u) (hrspec u).2

/-- Literal C6 constants derived from the explicit uniform linear projected
phase hypothesis. This theorem assumes the hypothesis and does not assert it. -/
theorem uniform_projectedPhase_implies_literal_C6
    (L C : ℝ) (hL : 0 ≤ L)
    (hgraph : ∀ w : List (Fin 10), ∀ hw : w ≠ [],
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
        Graph.GlobalPrimitivePhaseCriterion (carryKMPGraph w hw r)
          coordinateZeroProjection) :
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
    exists_common_rational_core_depth_from_projectedPhase L C hgraph m hm
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

/-- Conditional implication only. No witness for uniform linear depth, C6, or
any pi-specific conclusion is constructed here. -/
theorem uniformLinearProjectedPhaseHypothesis_implies_piC6
    (h : UniformLinearProjectedPhaseHypothesis) : PiC6 := by
  obtain ⟨L, C, hL, hgraph⟩ := h
  refine ⟨(L + 1) / Real.log 10, 2 * L + C, 1 / 2, ?_⟩
  exact uniform_projectedPhase_implies_literal_C6 L C hL hgraph

end T48

end DecimalFactorEntropy.T72ProjectedPeriodicity

#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.primitivePhaseCertificate_implies_everyInternalProjectionEventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.everyInternalProjectionEventuallyPeriodic_implies_primitivePhaseCertificate
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.primitivePhaseCertificate_iff_everyInternalProjectionEventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.globalPrimitivePhaseCriterion_decide_eq_true_iff
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.endpointComplete_local_primitivePhase_iff_coordinateZeroEventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.endpointComplete_global_primitivePhase_iff_coordinateZeroEventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.endpointComplete_global_decide_eq_true_iff
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.accepted_coordinateZero_eventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.exactEndpointRawRun_coordinateZero_eventuallyPeriodic
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.endpointComplete_globalProjectedPhase_implies_rationalCore
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.uniform_projectedPhase_implies_literal_C6
#print axioms DecimalFactorEntropy.T72ProjectedPeriodicity.T48.uniformLinearProjectedPhaseHypothesis_implies_piC6
