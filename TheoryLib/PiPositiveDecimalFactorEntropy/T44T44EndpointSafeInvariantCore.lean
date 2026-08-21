import TheoryLib.PiPositiveDecimalFactorEntropy.T20T20TransversalEntropy

/-!
# T44: endpoint-safe finite invariant-core reduction

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The source is a locally formulated problem, so it has no external source URL.
This module formalizes a conditional route to C6.  It does not prove the
uniform finite-core premise, C6 for pi, or positive decimal factor entropy.

An endpoint is allowed either of its decimal expansions: `KWord w` is the
image of all avoiding streams, so membership is existential in the expansion.
All density balls are closed because T20's `EpsilonDense` uses `dist ≤ ε`.
-/

noncomputable section

open Finset Set Topology

namespace DecimalFactorEntropy.T44EndpointSafeInvariantCore

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- Infinite decimal expansions.  Both expansions of a terminating point are
permitted by the circle-valued evaluation below. -/
abbrev DecimalStream := ℕ → Fin 10

/-- Delete the first `n` decimal digits. -/
def streamShift (n : ℕ) (a : DecimalStream) : DecimalStream :=
  fun i => a (i + n)

/-- Circle value of an infinite decimal expansion. -/
def circleValue (a : DecimalStream) : UnitAddCircle :=
  (Real.ofDigits a : UnitAddCircle)

/-- A finite decimal word occurs at a specified zero-based position. -/
def OccursAt (w : List (Fin 10)) (a : DecimalStream) (start : ℕ) : Prop :=
  ∀ i : Fin w.length, a (start + i.val) = w.get i

/-- An expansion avoids a word at every position. -/
def AvoidsWord (w : List (Fin 10)) (a : DecimalStream) : Prop :=
  ∀ start : ℕ, ¬ OccursAt w a start

/-- The closed symbolic avoidance language. -/
def avoidingStreams (w : List (Fin 10)) : Set DecimalStream :=
  {a | AvoidsWord w a}

/-- `K_w`: circle points having at least one infinite decimal expansion that
avoids `w`.  This existential convention includes decimal endpoints safely. -/
def KWord (w : List (Fin 10)) : Set UnitAddCircle :=
  circleValue '' avoidingStreams w

/-- Membership explicitly exposes the existential decimal expansion. -/
theorem mem_KWord_iff_exists_avoiding_expansion (w : List (Fin 10))
    (x : UnitAddCircle) :
    x ∈ KWord w ↔ ∃ a : DecimalStream, AvoidsWord w a ∧ circleValue a = x := by
  rfl

/-- The endpoint-inclusive decimal cell selected by `w`. -/
def wordCell (w : List (Fin 10)) : Set UnitAddCircle :=
  closedDecimalCell w.length (wordIndex w)

theorem occursAt_isClopen (w : List (Fin 10)) (start : ℕ) :
    IsClopen {a : DecimalStream | OccursAt w a start} := by
  have hset : {a : DecimalStream | OccursAt w a start} =
      ⋂ i : Fin w.length,
        (fun a : DecimalStream => a (start + i.val)) ⁻¹' {w.get i} := by
    ext a
    simp only [OccursAt, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  apply isClopen_iInter_of_finite
  intro i
  exact (isClopen_discrete {w.get i}).preimage
    (continuous_apply (start + i.val))

theorem avoidingStreams_isClosed (w : List (Fin 10)) :
    IsClosed (avoidingStreams w) := by
  have hset : avoidingStreams w =
      ⋂ start : ℕ, {a : DecimalStream | OccursAt w a start}ᶜ := by
    ext a
    simp [avoidingStreams, AvoidsWord]
  rw [hset]
  exact isClosed_iInter fun start => (occursAt_isClopen w start).compl.isClosed

theorem circleValue_continuous : Continuous circleValue := by
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp Real.continuous_ofDigits

/-- Compactness is the load-bearing reason for using all expansions rather
than a discontinuous preferred-expansion convention. -/
theorem KWord_isCompact (w : List (Fin 10)) : IsCompact (KWord w) := by
  exact (avoidingStreams_isClosed w).isCompact.image circleValue_continuous

theorem KWord_isClosed (w : List (Fin 10)) : IsClosed (KWord w) :=
  (KWord_isCompact w).isClosed

theorem real_nat_circle_eq_zero (n : ℕ) :
    ((n : ℝ) : UnitAddCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
  exact ⟨n, by simp⟩

/-- Decimal shift is exactly multiplication by `10^n` on the circle. -/
theorem circleValue_streamShift (a : DecimalStream) (n : ℕ) :
    circleValue (streamShift n a) = circleMul (10 ^ n) (circleValue a) := by
  induction n with
  | zero =>
      rw [pow_zero]
      change circleValue (streamShift 0 a) = 1 • circleValue a
      rw [one_nsmul]
      congr 1
  | succ n ih =>
      have hone (x : DecimalStream) :
          circleValue (streamShift 1 x) = circleMul 10 (circleValue x) := by
        have hreal := Real.ofDigits_eq_sum_add_ofDigits x 1
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          Real.ofDigitsTerm, pow_one] at hreal ⊢
        have hscaled : (10 : ℝ) * Real.ofDigits x =
            x 0 + Real.ofDigits (fun i => x (i + 1)) := by
          field_simp at hreal
          calc
            (10 : ℝ) * Real.ofDigits x = Real.ofDigits x * 10 := by ring
            _ = x 0 + Real.ofDigits (fun i => x (i + 1)) := hreal
        change (Real.ofDigits (fun i => x (i + 1)) : UnitAddCircle) =
          10 • (Real.ofDigits x : UnitAddCircle)
        rw [← AddCircle.coe_nsmul (p := (1 : ℝ))]
        simp only [nsmul_eq_mul]
        change (Real.ofDigits (fun i => x (i + 1)) : UnitAddCircle) =
          (((10 : ℝ) * Real.ofDigits x : ℝ) : UnitAddCircle)
        rw [hscaled, AddCircle.coe_add, real_nat_circle_eq_zero]
        simp
      calc
        circleValue (streamShift (n + 1) a) =
            circleValue (streamShift 1 (streamShift n a)) := by
              congr 1
              funext i
              simp [streamShift, Nat.add_comm, Nat.add_left_comm]
        _ = circleMul 10 (circleValue (streamShift n a)) := hone _
        _ = circleMul 10 (circleMul (10 ^ n) (circleValue a)) := by rw [ih]
        _ = circleMul (10 ^ (n + 1)) (circleValue a) := by
          simp [circleMul, ← mul_nsmul', pow_succ, Nat.mul_comm]

/-- Every circle point has an infinite decimal expansion. -/
theorem exists_decimal_expansion (z : UnitAddCircle) :
    ∃ a : DecimalStream, circleValue a = z := by
  let r : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z).val
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [r] using (AddCircle.equivIco (1 : ℝ) 0 z).property
  refine ⟨Real.digits r 10, ?_⟩
  rw [circleValue, Real.ofDigits_digits (by norm_num) hr]
  change (r : UnitAddCircle) = z
  simpa [r] using (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z

theorem avoidsWord_streamShift (w : List (Fin 10)) (a : DecimalStream)
    (n : ℕ) (ha : AvoidsWord w a) : AvoidsWord w (streamShift n a) := by
  intro start hocc
  apply ha (n + start)
  intro i
  simpa [streamShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hocc i

/-- `K_w` is forward invariant under multiplication by ten. -/
theorem KWord_forward_timesTen_invariant (w : List (Fin 10)) :
    ForwardTimesTenInvariant (KWord w) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨streamShift 1 a, avoidsWord_streamShift w a 1 ha, ?_⟩
  rw [circleValue_streamShift]
  rfl

theorem circleMul_comp (m n : ℕ) (x : UnitAddCircle) :
    circleMul m (circleMul n x) = circleMul (m * n) x := by
  simpa [circleMul, Nat.mul_comm] using (mul_nsmul x n m).symm

theorem circleMul_commute (m n : ℕ) (x : UnitAddCircle) :
    circleMul m (circleMul n x) = circleMul n (circleMul m x) := by
  rw [circleMul_comp, circleMul_comp, Nat.mul_comm]

/-- The finite intersection of the first `R + 1` inverse times-16 images. -/
def finiteAvoidanceIntersection (w : List (Fin 10)) (R : ℕ) :
    Set UnitAddCircle :=
  {x | ∀ j : ℕ, j ≤ R → circleMul (16 ^ j) x ∈ KWord w}

/-- The largest forward-times-10-invariant subset of the finite avoidance
intersection, written with all forward iterates explicit. -/
def Core (w : List (Fin 10)) (R : ℕ) : Set UnitAddCircle :=
  {x | ∀ n : ℕ, circleMul (10 ^ n) x ∈ finiteAvoidanceIntersection w R}

theorem finiteAvoidanceIntersection_isClosed (w : List (Fin 10)) (R : ℕ) :
    IsClosed (finiteAvoidanceIntersection w R) := by
  have hset : finiteAvoidanceIntersection w R =
      ⋂ j : ℕ, ⋂ (_h : j ≤ R), circleMul (16 ^ j) ⁻¹' KWord w := by
    ext x
    simp [finiteAvoidanceIntersection]
  rw [hset]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    (KWord_isClosed w).preimage (circleMul_continuous (16 ^ j))

/-- Named closedness theorem for the invariant core. -/
theorem core_isClosed (w : List (Fin 10)) (R : ℕ) : IsClosed (Core w R) := by
  have hset : Core w R =
      ⋂ n : ℕ, circleMul (10 ^ n) ⁻¹' finiteAvoidanceIntersection w R := by
    ext x
    simp [Core]
  rw [hset]
  exact isClosed_iInter fun n =>
    (finiteAvoidanceIntersection_isClosed w R).preimage
      (circleMul_continuous (10 ^ n))

theorem finiteAvoidanceIntersection_forward_timesTen
    (w : List (Fin 10)) (R : ℕ) :
    Set.MapsTo timesTen (finiteAvoidanceIntersection w R)
      (finiteAvoidanceIntersection w R) := by
  intro x hx j hj
  have hk := KWord_forward_timesTen_invariant w (hx j hj)
  change circleMul (16 ^ j) (timesTen x) ∈ KWord w
  rw [show timesTen x = circleMul 10 x by rfl, circleMul_commute]
  exact hk

/-- The core is forward-times-10 invariant. -/
theorem core_forward_timesTen_invariant (w : List (Fin 10)) (R : ℕ) :
    ForwardTimesTenInvariant (Core w R) := by
  intro x hx n
  rw [show timesTen x = circleMul 10 x by rfl, circleMul_comp]
  simpa [pow_succ] using hx (n + 1)

/-- The expanded core equals the finite intersection because that intersection
is already forward-times-10 invariant. -/
theorem core_eq_finiteAvoidanceIntersection (w : List (Fin 10)) (R : ℕ) :
    Core w R = finiteAvoidanceIntersection w R := by
  apply Set.Subset.antisymm
  · intro x hx
    simpa [circleMul] using hx 0
  · intro x hx n
    induction n with
    | zero => simpa [circleMul] using hx
    | succ n ih =>
        have hnext := finiteAvoidanceIntersection_forward_timesTen w R ih
        change circleMul 10 (circleMul (10 ^ n) x) ∈
          finiteAvoidanceIntersection w R at hnext
        simpa [circleMul_comp, pow_succ, Nat.mul_comm] using hnext

/-- Maximality among closed forward-times-10-invariant subsets.  Closedness is
displayed even though forward invariance alone suffices for the inclusion. -/
theorem core_maximal (w : List (Fin 10)) (R : ℕ) (F : Set UnitAddCircle)
    (hFclosed : IsClosed F) (hFsub : F ⊆ finiteAvoidanceIntersection w R)
    (hFinv : Set.MapsTo timesTen F F) : F ⊆ Core w R := by
  intro x hx n
  apply hFsub
  induction n with
  | zero => simpa [circleMul] using hx
  | succ n ih =>
      have hnext := hFinv ih
      change circleMul 10 (circleMul (10 ^ n) x) ∈ F at hnext
      simpa [circleMul_comp, pow_succ, Nat.mul_comm] using hnext

/-- Increasing the times-16 depth can only shrink the core. -/
theorem core_antitone_radius (w : List (Fin 10)) {R R' : ℕ} (hRR' : R ≤ R') :
    Core w R' ⊆ Core w R := by
  rw [core_eq_finiteAvoidanceIntersection, core_eq_finiteAvoidanceIntersection]
  intro x hx j hj
  exact hx j (hj.trans hRR')

/-- Two points in one endpoint-inclusive decimal cell are at most one cell
width apart on the circle. -/
theorem closedDecimalCell_dist_le_mesh (m : ℕ) (q : Fin (10 ^ m))
    (x y : UnitAddCircle) (hx : x ∈ closedDecimalCell m q)
    (hy : y ∈ closedDecimalCell m q) :
    dist x y ≤ ((10 : ℝ) ^ m)⁻¹ := by
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    ‖((u - v : ℝ) : UnitAddCircle)‖ ≤ ‖u - v‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = |u - v| := Real.norm_eq_abs _
    _ ≤ (((q.val + 1 : ℕ) : ℝ) / (10 : ℝ) ^ m) -
        (q.val : ℝ) / (10 : ℝ) ^ m := by
      push_cast at hu hv ⊢
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    _ = ((10 : ℝ) ^ m)⁻¹ := by
      have hp : (10 : ℝ) ^ m ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- A displayed block puts the corresponding shifted expansion in the closed
word cell, including a tail of repeating nines. -/
theorem occurrence_shift_mem_wordCell (w : List (Fin 10))
    (a : DecimalStream) (start : ℕ) (hocc : OccursAt w a start) :
    circleValue (streamShift start a) ∈ wordCell w := by
  have hpref : prefixWord a w.length start = w := by
    apply List.ext_get
    · simp [prefixWord]
    · intro i hi₁ hi₂
      simpa [prefixWord, hi₁, hi₂, List.get_eq_getElem] using hocc ⟨i, hi₂⟩
  refine ⟨Real.ofDigits (streamShift start a), ?_, rfl⟩
  have hcell := tailOrbit_mem_closedCell a w.length start
  have hshift : (fun i => a (start + i)) = streamShift start a := by
    funext i
    simp [streamShift, Nat.add_comm]
  rw [← hshift]
  simpa [wordCell, closedDecimalCell, tailOrbit, prefixLabel,
    hpref, wordIndex, add_comm] using hcell

/-- The explicit `+1` boundary-safe word length.  `log` is natural, so the
quotient is `log_10`. -/
def boundaryWordLength (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / ε) / Real.log 10) + 1

theorem boundaryWordLength_pos (ε : ℝ) : 0 < boundaryWordLength ε := by
  simp [boundaryWordLength]

/-- The chosen cell width is no larger than the requested radius. -/
theorem boundaryWordLength_mesh_le {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    ((10 : ℝ) ^ boundaryWordLength ε)⁻¹ ≤ ε := by
  let t : ℝ := Real.log (1 / ε) / Real.log 10
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have honeDiv : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg honeDiv
  have ht : 0 ≤ t := div_nonneg hlog hlogTen.le
  have htceil : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
  have htlength : t ≤ (boundaryWordLength ε : ℝ) := by
    dsimp [boundaryWordLength, t] at htceil ⊢
    push_cast
    linarith
  have hlogBound : Real.log (1 / ε) ≤
      (boundaryWordLength ε : ℝ) * Real.log 10 := by
    exact (div_le_iff₀ hlogTen).mp htlength
  have hbase : 1 / ε ≤ (10 : ℝ) ^ boundaryWordLength ε := by
    calc
      1 / ε = Real.exp (Real.log (1 / ε)) :=
        (Real.exp_log (by positivity : 0 < 1 / ε)).symm
      _ ≤ Real.exp ((boundaryWordLength ε : ℝ) * Real.log 10) :=
        Real.exp_le_exp.mpr hlogBound
      _ = (10 : ℝ) ^ boundaryWordLength ε := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        ring
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < 1 / ε) hbase
  simpa [one_div] using hinv

theorem piOrbitClosure_timesTen_iterate (x : UnitAddCircle)
    (hx : x ∈ piOrbitClosure) (n : ℕ) :
    circleMul (10 ^ n) x ∈ piOrbitClosure := by
  induction n with
  | zero => simpa [circleMul] using hx
  | succ n ih =>
      have hnext := piOrbitClosure_forward_timesTen_invariant ih
      change circleMul 10 (circleMul (10 ^ n) x) ∈ piOrbitClosure at hnext
      simpa [circleMul_comp, pow_succ, Nat.mul_comm] using hnext

/-- Failure of closed-radius density gives an existential nonempty decimal
word, of length exactly `ceil(log_10(1/ε)) + 1`, whose core contains `K_pi`. -/
theorem failure_epsilonDense_exists_avoidingWord
    (R : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hfail : ¬ EpsilonDense (timesSixteenTransversal piOrbitClosure R) ε) :
    ∃ m : ℕ, ∃ u : Fin m → Fin 10,
      m = boundaryWordLength ε ∧ 0 < m ∧
      m ≤ Nat.ceil (Real.log (1 / ε) / Real.log 10) + 1 ∧
      piOrbitClosure ⊆ Core (List.ofFn u) R := by
  rw [EpsilonDense] at hfail
  push Not at hfail
  obtain ⟨y, hy⟩ := hfail
  obtain ⟨a, ha⟩ := exists_decimal_expansion y
  let m := boundaryWordLength ε
  let u : Fin m → Fin 10 := fun i => a i.val
  let w : List (Fin 10) := List.ofFn u
  have hwlen : w.length = m := by simp [w]
  have hocc : OccursAt w a 0 := by
    intro i
    simp [w, u]
  have hycell : y ∈ wordCell w := by
    rw [← ha]
    have hcell := occurrence_shift_mem_wordCell w a 0 hocc
    simpa [circleMul] using hcell
  have hmesh : ((10 : ℝ) ^ w.length)⁻¹ ≤ ε := by
    rw [hwlen]
    exact boundaryWordLength_mesh_le hε (hεhalf.trans (by norm_num))
  have hcellDisjoint : Disjoint (wordCell w)
      (timesSixteenTransversal piOrbitClosure R) := by
    rw [Set.disjoint_left]
    intro z hzcell hzU
    have hdist := closedDecimalCell_dist_le_mesh w.length (wordIndex w)
      y z hycell hzcell
    have hfar := hy z hzU
    linarith
  have hsubset : piOrbitClosure ⊆ Core w R := by
    rw [core_eq_finiteAvoidanceIntersection]
    intro x hx j hj
    obtain ⟨b, hb⟩ := exists_decimal_expansion (circleMul (16 ^ j) x)
    have hbavoid : AvoidsWord w b := by
      intro n hnocc
      have hcell := occurrence_shift_mem_wordCell w b n hnocc
      have hxn := piOrbitClosure_timesTen_iterate x hx n
      have hU : circleValue (streamShift n b) ∈
          timesSixteenTransversal piOrbitClosure R := by
        have heq : circleValue (streamShift n b) =
            circleMul (16 ^ j) (circleMul (10 ^ n) x) := by
          calc
            circleValue (streamShift n b) =
                circleMul (10 ^ n) (circleValue b) := circleValue_streamShift b n
            _ = circleMul (10 ^ n) (circleMul (16 ^ j) x) := by rw [hb]
            _ = circleMul (16 ^ j) (circleMul (10 ^ n) x) :=
              circleMul_commute _ _ _
        rw [heq]
        refine Set.mem_iUnion_of_mem j ?_
        refine Set.mem_iUnion_of_mem (show j ∈ Finset.range (R + 1) by simp; omega) ?_
        exact ⟨circleMul (10 ^ n) x, hxn, rfl⟩
      exact hcellDisjoint.le_bot ⟨hcell, hU⟩
    exact ⟨b, hbavoid, hb⟩
  refine ⟨m, u, rfl, boundaryWordLength_pos ε, ?_, ?_⟩
  · rfl
  · simpa [w] using hsubset

/-- Distinct powers of ten give distinct points in the pi orbit. -/
theorem piCircleOrbit_injective : Function.Injective piCircleOrbit := by
  have hneq {n k : ℕ} (hnk : n < k) : piCircleOrbit n ≠ piCircleOrbit k := by
    intro heq
    let D : ℕ := 10 ^ k - 10 ^ n
    have hpow : 10 ^ n < 10 ^ k := Nat.pow_lt_pow_right (by norm_num) hnk
    have hD : D ≠ 0 := by omega
    have hzero : (((D : ℝ) * Real.pi : ℝ) : UnitAddCircle) = 0 := by
      have hcast : (D : ℝ) = (10 : ℝ) ^ k - (10 : ℝ) ^ n := by
        dsimp [D]
        rw [Nat.cast_sub hpow.le]
        push_cast
        rfl
      rw [hcast]
      have hsub : (((10 : ℝ) ^ k * Real.pi -
          (10 : ℝ) ^ n * Real.pi : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub]
        change piCircleOrbit k - piCircleOrbit n = 0
        rw [← heq]
        simp
      convert hsub using 1 <;> ring_nf
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hzero with ⟨z, hz⟩
    have hzi : ((z : ℝ) = (D : ℝ) * Real.pi) := by
      simpa [zsmul_eq_mul] using hz
    have hirr : Irrational ((D : ℝ) * Real.pi) :=
      irrational_pi.natCast_mul hD
    exact hirr.ne_int z hzi.symm
  intro n k h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnk | hkn
  · exact hneq hnk h
  · exact hneq hkn h.symm

/-- The pi orbit closure is infinite; this is the irrationality obstruction
used against a finite core. -/
theorem piOrbitClosure_infinite : piOrbitClosure.Infinite := by
  apply (Set.infinite_range_of_injective piCircleOrbit_injective).mono
  exact subset_closure

/-- The sole unproved frontier.  The constants are uniform, the word is
quantified before its depth witness, and the depth may depend on the whole
nonempty word. -/
def UniformLinearFiniteCoreHypothesis : Prop :=
  ∃ L C : ℝ, 0 ≤ L ∧
    ∀ w : List (Fin 10), w ≠ [] →
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧ (Core w r).Finite

theorem uniformLinearFiniteCoreHypothesis_iff_quantifiers :
    UniformLinearFiniteCoreHypothesis ↔
      ∃ L C : ℝ, 0 ≤ L ∧
        ∀ w : List (Fin 10), w ≠ [] →
          ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧
            (Core w r).Finite := by
  rfl

/-- Finitely many words of one positive length have one common depth without
changing the linear bound. -/
theorem exists_common_finite_core_depth
    (L C : ℝ) (hcore : ∀ w : List (Fin 10), w ≠ [] →
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧ (Core w r).Finite)
    (m : ℕ) (hm : 0 < m) :
    ∃ R : ℕ, (R : ℝ) ≤ L * (m : ℝ) + C ∧
      ∀ u : Fin m → Fin 10, (Core (List.ofFn u) R).Finite := by
  classical
  have hwne (u : Fin m → Fin 10) : List.ofFn u ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  let r : (Fin m → Fin 10) → ℕ := fun u => Classical.choose (hcore (List.ofFn u) (hwne u))
  have hrspec (u : Fin m → Fin 10) :
      (r u : ℝ) ≤ L * (m : ℝ) + C ∧ (Core (List.ofFn u) (r u)).Finite := by
    simpa [r] using Classical.choose_spec (hcore (List.ofFn u) (hwne u))
  let depths : Finset ℕ := Finset.univ.image r
  have huniv : (Finset.univ : Finset (Fin m → Fin 10)).Nonempty := by
    exact Finset.univ_nonempty
  have hdepths : depths.Nonempty := by
    simpa [depths] using (Finset.image_nonempty.mpr huniv)
  let R : ℕ := depths.max' hdepths
  have hRmem : R ∈ depths := Finset.max'_mem depths hdepths
  obtain ⟨uMax, _huMax, huMaxEq⟩ := Finset.mem_image.mp hRmem
  refine ⟨R, ?_, ?_⟩
  · rw [← huMaxEq]
    exact (hrspec uMax).1
  · intro u
    have hru : r u ∈ depths := by
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    have hle : r u ≤ R := Finset.le_max' depths (r u) hru
    exact (hrspec u).2.subset (core_antitone_radius (List.ofFn u) hle)

/-- Natural-log conversion and the `+1` word boundary give the displayed C6
time constants `A = (L+1)/log 10`, `B = 2L+C`, and `ε₀ = 1/2`. -/
theorem uniform_finite_cores_imply_literal_C6
    (L C : ℝ) (hL : 0 ≤ L)
    (hcore : ∀ w : List (Fin 10), w ≠ [] →
      ∃ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C ∧ (Core w r).Finite) :
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
  obtain ⟨R, hRbound, hRfinite⟩ :=
    exists_common_finite_core_depth L C hcore m hm
  refine ⟨R, ?_, ?_⟩
  · by_contra hfail
    obtain ⟨m', u, hm'eq, _hm'pos, _hm'bound, hsubset⟩ :=
      failure_epsilonDense_exists_avoidingWord R ε hε hεhalf hfail
    have hm'm : m' = m := by simpa [m] using hm'eq
    subst m'
    exact piOrbitClosure_infinite
      ((hRfinite u).subset hsubset)
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

/-- The final implication is conditional on the displayed universal finite-core
hypothesis; no instance of that hypothesis is asserted. -/
theorem uniformLinearFiniteCoreHypothesis_implies_piC6
    (h : UniformLinearFiniteCoreHypothesis) : PiC6 := by
  obtain ⟨L, C, hL, hcore⟩ := h
  refine ⟨(L + 1) / Real.log 10, 2 * L + C, 1 / 2, ?_⟩
  exact uniform_finite_cores_imply_literal_C6 L C hL hcore

end DecimalFactorEntropy.T44EndpointSafeInvariantCore

#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.mem_KWord_iff_exists_avoiding_expansion
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.KWord_isCompact
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.KWord_forward_timesTen_invariant
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_isClosed
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_forward_timesTen_invariant
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_maximal
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.core_antitone_radius
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.closedDecimalCell_dist_le_mesh
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.occurrence_shift_mem_wordCell
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.boundaryWordLength_mesh_le
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.failure_epsilonDense_exists_avoidingWord
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.piOrbitClosure_infinite
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.uniformLinearFiniteCoreHypothesis_iff_quantifiers
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.exists_common_finite_core_depth
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.uniform_finite_cores_imply_literal_C6
#print axioms DecimalFactorEntropy.T44EndpointSafeInvariantCore.uniformLinearFiniteCoreHypothesis_implies_piC6
