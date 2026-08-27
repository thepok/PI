import TheoryLib.PiLongLagBlockCollisionDecay.T19T19SparsePeriodicIslands
import TheoryLib.PiLongLagBlockCollisionDecay.T51T51FiniteSparsePeriodicSelection

/-!
# T53: prefix-faithful finite sparse-periodic words

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
Canonical SHA-256:
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
Original source URL: none; the canonical file records a local formulation on 2026-07-23.

This finite sibling strengthens T51's completed-island spaces by imposing every
T19 periodic equality visible below an exclusive cutoff, including a final
partially visible period.  It constructs only finite restriction and extension
maps.  It asserts no infinite selection, measure, irrationality exponent,
statement about `Real.pi`, or conclusion about the canonical collision problem.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T53

open Theory.PiDigits.LongLagBlockCollisionDecay.T19
open Theory.PiDigits.LongLagBlockCollisionDecay.T51

/-- A coordinate lies in a repeated (non-first) part of a T19 island. -/
def ConstrainedAt (i : ℕ) : Prop :=
  ∃ k : ℕ, scheduleStart k + scheduleBlockLength k ≤ i ∧
    i < scheduleSampleSize k

/-- Every constrained coordinate below the exclusive cutoff `n`, including
coordinates in an island which is only partially visible at `n`. -/
def partialConstrainedCoordinates (n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion fun k =>
    Finset.Ico (scheduleStart k + scheduleBlockLength k)
      (min (scheduleSampleSize k) n)

/-- The genuinely free coordinates below `n`. -/
def partialFreeCoordinates (n : ℕ) : Finset ℕ :=
  Finset.range n \ partialConstrainedCoordinates n

theorem mem_partialConstrainedCoordinates {n i : ℕ} :
    i ∈ partialConstrainedCoordinates n ↔ i < n ∧ ConstrainedAt i := by
  simp only [partialConstrainedCoordinates, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨k, hk, hlo, hhi, hin⟩
    exact ⟨hin, k, hlo, hhi⟩
  · rintro ⟨hin, k, hlo, hhi⟩
    refine ⟨k, ?_, hlo, hhi, hin⟩
    have hki : k < i := (scheduleIndex_lt_start k).trans_le
      ((Nat.le_add_right _ _).trans hlo)
    exact hki.trans hin

theorem partialConstrainedCoordinates_subset_range (n : ℕ) :
    partialConstrainedCoordinates n ⊆ Finset.range n := by
  intro i hi
  exact Finset.mem_range.mpr (mem_partialConstrainedCoordinates.mp hi).1

theorem partial_free_constrained_partition (n : ℕ) :
    (partialFreeCoordinates n).card +
        (partialConstrainedCoordinates n).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card
    (partialConstrainedCoordinates_subset_range n)
  simpa [partialFreeCoordinates] using h

/-- Scales for which at least one repeated-period coordinate is visible. -/
def visibleRepeatedScales (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k =>
    scheduleStart k + scheduleBlockLength k < n

@[simp] theorem mem_visibleRepeatedScales {n k : ℕ} :
    k ∈ visibleRepeatedScales n ↔
      scheduleStart k + scheduleBlockLength k < n := by
  constructor
  · simp [visibleRepeatedScales]
  · intro hk
    have hkStart := scheduleIndex_lt_start k
    have hkn : k < n := by omega
    simp [visibleRepeatedScales, hk, hkn]

/-- Partial final islands do not spoil the explicit one-half free density. -/
theorem partialConstrainedCoordinates_card_twice_le (n : ℕ) :
    2 * (partialConstrainedCoordinates n).card ≤ n := by
  classical
  by_cases hscales : (visibleRepeatedScales n).Nonempty
  · let k := (visibleRepeatedScales n).max' hscales
    have hk : k ∈ visibleRepeatedScales n :=
      Finset.max'_mem (visibleRepeatedScales n) hscales
    have hkVisible := mem_visibleRepeatedScales.mp hk
    have hmax : ∀ j ∈ visibleRepeatedScales n, j ≤ k := by
      intro j hj
      exact Finset.le_max' (visibleRepeatedScales n) j hj
    cases hkval : k with
    | zero =>
        have hsubset : partialConstrainedCoordinates n ⊆
            Finset.Ico (scheduleStart 0 + scheduleBlockLength 0)
              (min (scheduleSampleSize 0) n) := by
          intro i hi
          obtain ⟨hin, j, hjlo, hjhi⟩ :=
            mem_partialConstrainedCoordinates.mp hi
          have hjmem : j ∈ visibleRepeatedScales n :=
            mem_visibleRepeatedScales.mpr (hjlo.trans_lt hin)
          have hjle : j ≤ 0 := by simpa [hkval] using hmax j hjmem
          have hj : j = 0 := by omega
          subst j
          exact Finset.mem_Ico.mpr ⟨hjlo, lt_min hjhi hin⟩
        have hcard := Finset.card_le_card hsubset
        have hIco :
            (Finset.Ico (scheduleStart 0 + scheduleBlockLength 0)
              (min (scheduleSampleSize 0) n)).card ≤
                scheduleIslandLength 0 := by
          rw [Nat.card_Ico]
          simp only [scheduleSampleSize, scheduleIslandLength]
          omega
        have hlength := five_mul_scheduleIslandLength_le_start 0
        have hvisible : scheduleStart 0 < n := by
          have hkVisible0 : scheduleStart 0 + scheduleBlockLength 0 < n := by
            simpa [hkval] using hkVisible
          omega
        omega
    | succ s =>
        have hsubset : partialConstrainedCoordinates n ⊆
            Finset.range (scheduleSampleSize s) ∪
              Finset.Ico
                (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
                (min (scheduleSampleSize (s + 1)) n) := by
          intro i hi
          obtain ⟨hin, j, hjlo, hjhi⟩ :=
            mem_partialConstrainedCoordinates.mp hi
          have hjmem : j ∈ visibleRepeatedScales n :=
            mem_visibleRepeatedScales.mpr (hjlo.trans_lt hin)
          have hjle : j ≤ s + 1 := by simpa [hkval] using hmax j hjmem
          by_cases hj : j = s + 1
          · subst j
            exact Finset.mem_union_right _
              (Finset.mem_Ico.mpr ⟨hjlo, lt_min hjhi hin⟩)
          · have hjs : j ≤ s := by omega
            exact Finset.mem_union_left _
              (Finset.mem_range.mpr (hjhi.trans_le (scheduleSampleSize_mono hjs)))
        have hcard := Finset.card_le_card hsubset
        have hunion := Finset.card_union_le
          (Finset.range (scheduleSampleSize s))
          (Finset.Ico
            (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
            (min (scheduleSampleSize (s + 1)) n))
        have hIco :
            (Finset.Ico
              (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
              (min (scheduleSampleSize (s + 1)) n)).card ≤
                scheduleIslandLength (s + 1) := by
          rw [Nat.card_Ico]
          simp only [scheduleSampleSize, scheduleIslandLength]
          omega
        have hcover : (partialConstrainedCoordinates n).card ≤
            scheduleSampleSize s + scheduleIslandLength (s + 1) := by
          rw [Finset.card_range] at hunion
          omega
        have hprevious := five_mul_scheduleSampleSize_le_next_start s
        have hcurrent := five_mul_scheduleIslandLength_le_start (s + 1)
        have hvisible : scheduleStart (s + 1) < n := by
          have hkVisibleSucc : scheduleStart (s + 1) +
              scheduleBlockLength (s + 1) < n := by
            simpa [hkval] using hkVisible
          omega
        omega
  · have hempty : visibleRepeatedScales n = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hscales
    have hconstrained : partialConstrainedCoordinates n = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨i, hi⟩
      obtain ⟨hin, k, hklo, _hkhi⟩ :=
        mem_partialConstrainedCoordinates.mp hi
      have hk : k ∈ visibleRepeatedScales n :=
        mem_visibleRepeatedScales.mpr (hklo.trans_lt hin)
      simp [hempty] at hk
    simp [hconstrained]

/-- Explicit onset `1` and free-density constant `1/2`. -/
theorem partialFreeCoordinates_eventual_density :
    ∀ n : ℕ, 1 ≤ n → n / 2 ≤ (partialFreeCoordinates n).card := by
  intro n _hn
  have hpartition := partial_free_constrained_partition n
  have hconstrained := partialConstrainedCoordinates_card_twice_le n
  omega

/-- The unique scheduled island constraining `i`. -/
def constrainingScale (i : ℕ) (hi : ConstrainedAt i) : ℕ :=
  Classical.choose hi

theorem constrainingScale_spec (i : ℕ) (hi : ConstrainedAt i) :
    scheduleStart (constrainingScale i hi) +
        scheduleBlockLength (constrainingScale i hi) ≤ i ∧
      i < scheduleSampleSize (constrainingScale i hi) :=
  Classical.choose_spec hi

theorem constrainingScale_unique {i j k : ℕ}
    (hj : scheduleStart j + scheduleBlockLength j ≤ i)
    (hj' : i < scheduleSampleSize j)
    (hk : scheduleStart k + scheduleBlockLength k ≤ i)
    (hk' : i < scheduleSampleSize k) : j = k := by
  exact completed_constraint_scale_unique
    (Finset.mem_Ico.mpr ⟨hj, hj'⟩) (Finset.mem_Ico.mpr ⟨hk, hk'⟩)

/-- Cutoff-independent root of a coordinate: constrained coordinates point to
the matching coordinate in their island's first period. -/
def rootIndex (i : ℕ) : ℕ :=
  by
    classical
    exact if hi : ConstrainedAt i then
      scheduleRepresentative (constrainingScale i hi) i
    else i

theorem rootIndex_eq_representative {i k : ℕ}
    (hlo : scheduleStart k + scheduleBlockLength k ≤ i)
    (hhi : i < scheduleSampleSize k) :
    rootIndex i = scheduleRepresentative k i := by
  classical
  let hi : ConstrainedAt i := ⟨k, hlo, hhi⟩
  rw [rootIndex, dif_pos hi]
  congr 1
  have hs := constrainingScale_spec i hi
  exact constrainingScale_unique hs.1 hs.2 hlo hhi

theorem rootIndex_le (i : ℕ) : rootIndex i ≤ i := by
  classical
  by_cases hi : ConstrainedAt i
  · rw [rootIndex, dif_pos hi]
    have hr := Finset.mem_Ico.mp
      (scheduleRepresentative_mem_firstPeriod
        (k := constrainingScale i hi) (i := i))
    exact (le_of_lt hr.2).trans (constrainingScale_spec i hi).1
  · simp [rootIndex, hi]

theorem rootIndex_not_constrained (i : ℕ) : ¬ ConstrainedAt (rootIndex i) := by
  classical
  intro hroot
  by_cases hi : ConstrainedAt i
  · rw [rootIndex, dif_pos hi] at hroot
    have hk := constrainingScale_spec i hi
    have hrep := Finset.mem_Ico.mp
      (scheduleRepresentative_mem_firstPeriod
        (k := constrainingScale i hi) (i := i))
    obtain ⟨j, hjlo, hjhi⟩ := hroot
    rcases lt_trichotomy j (constrainingScale i hi) with hjk | hjk | hkj
    · have hsep := scheduleSampleSize_le_start_of_lt hjk
      omega
    · subst j
      omega
    · have hsep := scheduleSampleSize_le_start_of_lt hkj
      omega
  · rw [rootIndex, dif_neg hi] at hroot
    exact hi hroot

@[simp] theorem rootIndex_idempotent (i : ℕ) :
    rootIndex (rootIndex i) = rootIndex i := by
  rw [rootIndex]
  simp [rootIndex_not_constrained]

/-- Free coordinate type displayed by a prefix-faithful finite space. -/
abbrev FreeCoordinate (n : ℕ) := ↥(partialFreeCoordinates n)

def freeCoordinateToFin {n : ℕ} (i : FreeCoordinate n) : Fin n :=
  ⟨i.val, (Finset.mem_sdiff.mp i.property).1 |> Finset.mem_range.mp⟩

/-- The cutoff-independent root, regarded as a free coordinate below `n`. -/
def rootCoordinate (n : ℕ) (i : Fin n) : FreeCoordinate n :=
  ⟨rootIndex i.val, Finset.mem_sdiff.mpr
    ⟨Finset.mem_range.mpr (lt_of_le_of_lt (rootIndex_le i.val) i.isLt), by
      intro h
      exact rootIndex_not_constrained i.val
        (mem_partialConstrainedCoordinates.mp h).2⟩⟩

@[simp] theorem rootCoordinate_of_free {n : ℕ} (i : FreeCoordinate n) :
    rootCoordinate n (freeCoordinateToFin i) = i := by
  apply Subtype.ext
  have hi : ¬ ConstrainedAt i.val := by
    intro h
    exact (Finset.mem_sdiff.mp i.property).2
      (mem_partialConstrainedCoordinates.mpr
        ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp i.property).1, h⟩)
  change rootIndex i.val = i.val
  rw [rootIndex]
  simp [hi]

/-- A zero-based base-ten word of length `n`. -/
abbrev DecimalWord (n : ℕ) := Fin n → Fin 10

/-- Length-`n` words faithful to every portion of every T19 island visible
below the exclusive cutoff `n`. -/
def PrefixFaithfulWordSpace (n : ℕ) :=
  {w : DecimalWord n //
    ∀ i, w i = w (freeCoordinateToFin (rootCoordinate n i))}

/-- Restriction to genuinely free coordinates exactly parametrizes the space. -/
def prefixFaithfulWordEquiv (n : ℕ) :
    PrefixFaithfulWordSpace n ≃ (FreeCoordinate n → Fin 10) where
  toFun w i := w.1 (freeCoordinateToFin i)
  invFun g := ⟨fun i => g (rootCoordinate n i), by
    intro i
    change g (rootCoordinate n i) =
      g (rootCoordinate n (freeCoordinateToFin (rootCoordinate n i)))
    rw [rootCoordinate_of_free]⟩
  left_inv := by
    rintro ⟨w, hw⟩
    apply Subtype.ext
    funext i
    exact (hw i).symm
  right_inv := by
    intro g
    funext i
    change g (rootCoordinate n (freeCoordinateToFin i)) = g i
    rw [rootCoordinate_of_free]

theorem prefixFaithfulWordSpace_card (n : ℕ) :
    Nat.card (PrefixFaithfulWordSpace n) =
      10 ^ (partialFreeCoordinates n).card := by
  classical
  rw [Nat.card_congr (prefixFaithfulWordEquiv n), Nat.card_fun]
  simp

/-- Every constrained coordinate is equal to its first-period representative,
with no completed-island hypothesis. -/
theorem prefixFaithfulWord_coordinate_eq_representative {n k i : ℕ}
    (w : PrefixFaithfulWordSpace n) (hin : i < n)
    (hlo : scheduleStart k + scheduleBlockLength k ≤ i)
    (hhi : i < scheduleSampleSize k) :
    w.1 ⟨i, hin⟩ = w.1 ⟨scheduleRepresentative k i,
      by
        have hr := rootIndex_le i
        rw [rootIndex_eq_representative hlo hhi] at hr
        exact hr.trans_lt hin⟩ := by
  have hw := w.2 ⟨i, hin⟩
  exact hw.trans (congrArg w.1 (Fin.ext
    (rootIndex_eq_representative hlo hhi)))

/-- Literal partial-island constraint: every visible coordinate of every copy,
including a truncated final copy, equals the corresponding first-period digit. -/
theorem prefixFaithfulWord_partialIslandConstraint
    {n k t : ℕ} (w : PrefixFaithfulWordSpace n)
    (ht : t < schedulePeriodCount k)
    (r : Fin (scheduleBlockLength k))
    (hvisible : scheduleStart k + t * scheduleBlockLength k + r.val < n) :
    w.1 ⟨scheduleStart k + t * scheduleBlockLength k + r.val, hvisible⟩ =
      w.1 ⟨scheduleStart k + r.val, by omega⟩ := by
  by_cases ht0 : t = 0
  · subst t
    apply congrArg w.1
    apply Fin.ext
    simp
  · have hone : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
    have hlo : scheduleStart k + scheduleBlockLength k ≤
        scheduleStart k + t * scheduleBlockLength k + r.val := by
      have hm := (schedule_parameters k).1
      nlinarith
    have hhi : scheduleStart k + t * scheduleBlockLength k + r.val <
        scheduleSampleSize k := by
      have ht1 : t + 1 ≤ schedulePeriodCount k := by omega
      have hr := r.isLt
      simp only [scheduleSampleSize]
      have hmul : (t + 1) * scheduleBlockLength k ≤
          schedulePeriodCount k * scheduleBlockLength k :=
        Nat.mul_le_mul_right (scheduleBlockLength k) ht1
      nlinarith
    have hword := prefixFaithfulWord_coordinate_eq_representative w
      hvisible hlo hhi
    have hrep := scheduleRepresentative_periodic_coordinate k t r
    exact hword.trans (congrArg w.1 (Fin.ext hrep))

/-- Restrict a prefix-faithful word along an explicit cutoff comparison. -/
def restrictWord {m n : ℕ} (hmn : m ≤ n) :
    PrefixFaithfulWordSpace n → PrefixFaithfulWordSpace m := fun w =>
  ⟨fun i => w.1 ⟨i.val, i.isLt.trans_le hmn⟩, by
    intro i
    simpa [freeCoordinateToFin, rootCoordinate] using
      w.2 ⟨i.val, i.isLt.trans_le hmn⟩⟩

@[simp] theorem restrictWord_apply {m n : ℕ} (hmn : m ≤ n)
    (w : PrefixFaithfulWordSpace n) (i : Fin m) :
    (restrictWord hmn w).1 i = w.1 ⟨i.val, i.isLt.trans_le hmn⟩ := rfl

theorem restrictWord_refl (n : ℕ) :
    restrictWord (le_refl n) = id := by
  funext w
  apply Subtype.ext
  funext i
  rfl

theorem restrictWord_comp {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (w : PrefixFaithfulWordSpace n) :
    restrictWord hlm (restrictWord hmn w) =
      restrictWord (hlm.trans hmn) w := by
  apply Subtype.ext
  funext i
  rfl

/-- Explicit zero-filled extension witness.  Existing root values are retained;
new genuinely free roots receive digit zero. -/
def extendWord {m n : ℕ} (_hmn : m ≤ n)
    (w : PrefixFaithfulWordSpace m) : PrefixFaithfulWordSpace n :=
  ⟨fun i => if hi : rootIndex i.val < m then
      w.1 ⟨rootIndex i.val, hi⟩ else 0, by
    intro i
    simp only [freeCoordinateToFin, rootCoordinate]
    simp [rootIndex_idempotent]⟩

theorem restrictWord_extendWord {m n : ℕ} (hmn : m ≤ n)
    (w : PrefixFaithfulWordSpace m) :
    restrictWord hmn (extendWord hmn w) = w := by
  apply Subtype.ext
  funext i
  have hroot : rootIndex i.val < m := (rootIndex_le i.val).trans_lt i.isLt
  change (if hi : rootIndex i.val < m then
    w.1 ⟨rootIndex i.val, hi⟩ else 0) = w.1 i
  rw [dif_pos hroot]
  exact (w.2 i).symm

theorem restrictWord_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (restrictWord hmn) := by
  intro w
  exact ⟨extendWord hmn w, restrictWord_extendWord hmn w⟩

/-- Forget the extra partial-island constraints and retain T51's completed
island constraints.  This map lets T53 reuse T51's decimal encoding. -/
def toCompletedWord {n : ℕ} (w : PrefixFaithfulWordSpace n) :
    Theory.PiDigits.LongLagBlockCollisionDecay.T51.FiniteSparseWordSpace n :=
  ⟨w.1, by
    classical
    intro i
    by_cases hi : i.val ∈
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.completedConstrainedCoordinates n
    · have hs :=
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.constrainedScale_spec i hi
      have hword := prefixFaithfulWord_coordinate_eq_representative w
        i.isLt hs.2.1 hs.2.2
      simpa only [
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.freeCoordinateToFin,
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.rootCoordinate,
        dif_pos hi] using hword
    · simp only [
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.freeCoordinateToFin,
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.rootCoordinate,
        dif_neg hi]⟩

theorem toCompletedWord_injective (n : ℕ) :
    Function.Injective
      (toCompletedWord : PrefixFaithfulWordSpace n →
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.FiniteSparseWordSpace n) := by
  intro w v hwv
  apply Subtype.ext
  exact congrArg (fun z => z.1) hwv

/-- Most-significant-first label, inherited from the injective T51 encoding. -/
def finiteWordCode {n : ℕ} (w : PrefixFaithfulWordSpace n) : Fin (10 ^ n) :=
  Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCode
    (toCompletedWord w)

theorem finiteWordCode_injective (n : ℕ) :
    Function.Injective
      (finiteWordCode : PrefixFaithfulWordSpace n → Fin (10 ^ n)) := by
  intro w v hwv
  apply toCompletedWord_injective n
  apply Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCode_injective n
  exact hwv

/-- Half-open level-`n` decimal cylinder of a prefix-faithful word. -/
def finiteWordCylinder {n : ℕ} (w : PrefixFaithfulWordSpace n) : Set ℝ :=
  Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCylinder
    (toCompletedWord w)

/-- Every prefix-faithful level-`n` cylinder has exact length `10⁻ⁿ`. -/
theorem finiteWordCylinder_length {n : ℕ} (w : PrefixFaithfulWordSpace n) :
    (((finiteWordCode w).val + 1 : ℕ) : ℝ) / ((10 ^ n : ℕ) : ℝ) -
        (finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ) =
      (10 : ℝ) ^ (-(n : ℤ)) := by
  exact Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCylinder_length
    (toCompletedWord w)

/-- Prefix-faithful words whose cylinders meet the closed interval `[a,b]`. -/
def IntervalWordEvent (n : ℕ) (a b : ℝ) :=
  {w : PrefixFaithfulWordSpace n //
    (finiteWordCylinder w ∩ Set.Icc a b).Nonempty}

def intervalEventToCompleted {n : ℕ} {a b : ℝ} :
    IntervalWordEvent n a b →
      Theory.PiDigits.LongLagBlockCollisionDecay.T51.IntervalWordEvent n a b :=
  fun w => ⟨toCompletedWord w.1, w.2⟩

theorem intervalEventToCompleted_injective (n : ℕ) (a b : ℝ) :
    Function.Injective
      (intervalEventToCompleted : IntervalWordEvent n a b →
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.IntervalWordEvent n a b) := by
  intro w v hwv
  apply Subtype.ext
  apply toCompletedWord_injective n
  exact congrArg Subtype.val hwv

/-- T51's endpoint-safe three-cylinder constant remains valid for the smaller
prefix-faithful space. -/
theorem intervalWordEvent_card_le_three (n : ℕ) (a b : ℝ)
    (hab : a ≤ b)
    (hlength : b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹) :
    Nat.card (IntervalWordEvent n a b) ≤ 3 := by
  classical
  letI : Finite
      (Theory.PiDigits.LongLagBlockCollisionDecay.T51.IntervalWordEvent n a b) :=
    Finite.of_injective
      (fun w =>
        Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCode w.1)
      (by
        intro w v hwv
        apply Subtype.ext
        apply Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCode_injective n
        exact hwv)
  letI : Finite (IntervalWordEvent n a b) :=
    Finite.of_injective intervalEventToCompleted
      (intervalEventToCompleted_injective n a b)
  calc
    Nat.card (IntervalWordEvent n a b) ≤
        Nat.card
          (Theory.PiDigits.LongLagBlockCollisionDecay.T51.IntervalWordEvent n a b) :=
      Nat.card_le_card_of_injective intervalEventToCompleted
        (intervalEventToCompleted_injective n a b)
    _ ≤ 3 :=
      Theory.PiDigits.LongLagBlockCollisionDecay.T51.intervalWordEvent_card_le_three
        n a b hab hlength

/-- Uniform mass on the finite prefix-faithful word space. -/
def finiteIntervalMass (n : ℕ) (a b : ℝ) : ℝ :=
  (Nat.card (IntervalWordEvent n a b) : ℝ) /
    Nat.card (PrefixFaithfulWordSpace n)

/-- Exact finite anti-concentration before applying the density estimate. -/
theorem finiteIntervalMass_le_freePower (n : ℕ) (a b : ℝ)
    (hab : a ≤ b)
    (hlength : b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹) :
    finiteIntervalMass n a b ≤
      3 * (10 : ℝ) ^ (-((partialFreeCoordinates n).card : ℤ)) := by
  have hcard := intervalWordEvent_card_le_three n a b hab hlength
  rw [finiteIntervalMass, prefixFaithfulWordSpace_card]
  calc
    (Nat.card (IntervalWordEvent n a b) : ℝ) /
          (10 ^ (partialFreeCoordinates n).card : ℕ) ≤
        3 / (10 ^ (partialFreeCoordinates n).card : ℕ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = 3 * (10 : ℝ) ^ (-((partialFreeCoordinates n).card : ℤ)) := by
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
      norm_num

/-- Explicit onset `1`, neighbour constant `3`, base `10`, and density `1/2`. -/
theorem finiteIntervalMass_le_halfDensity :
    ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ, a ≤ b →
      b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
  intro n hn a b hab hlength
  have hmass := finiteIntervalMass_le_freePower n a b hab hlength
  have hfree := partialFreeCoordinates_eventual_density n hn
  have hpow : (10 : ℝ) ^ (n / 2) ≤
      (10 : ℝ) ^ (partialFreeCoordinates n).card :=
    pow_le_pow_right₀ (by norm_num) hfree
  have hinv : ((10 : ℝ) ^ (partialFreeCoordinates n).card)⁻¹ ≤
      ((10 : ℝ) ^ (n / 2))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hnegative :
      (10 : ℝ) ^ (-((partialFreeCoordinates n).card : ℤ)) ≤
        (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
    simpa [zpow_neg, zpow_natCast] using hinv
  exact hmass.trans (mul_le_mul_of_nonneg_left hnegative (by norm_num))

/-- Shell-ready exponent-seven specialization with numerator `2`.  This is
only a finite estimate and has no Borel--Cantelli conclusion. -/
theorem exponentSeven_finiteInterval_antiConcentration :
    ∀ n q : ℕ, 1 ≤ n → 1 ≤ q → ∀ a b : ℝ, a ≤ b →
      b - a ≤ 2 / (q : ℝ) ^ 7 →
      2 / (q : ℝ) ^ 7 ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
  intro n q hn _hq a b hab hlength hscale
  exact finiteIntervalMass_le_halfDensity n hn a b hab
    (hlength.trans hscale)

/-- One inspectable theorem type collecting the complete finite T53 surface:
the T19 schedule, partial-island cutoff constraints, projective restrictions,
explicit extension witnesses, free density and onset, decimal interval length,
and all shell anti-concentration constants. -/
theorem prefixFaithfulFiniteCore_audit :
    (∀ n i : ℕ, i ∈ partialConstrainedCoordinates n ↔
      i < n ∧ ∃ k : ℕ,
        scheduleStart k + scheduleBlockLength k ≤ i ∧
          i < scheduleSampleSize k) ∧
    (∀ n k t : ℕ, ∀ w : PrefixFaithfulWordSpace n,
      t < schedulePeriodCount k →
      ∀ r : Fin (scheduleBlockLength k),
      ∀ hvisible : scheduleStart k + t * scheduleBlockLength k + r.val < n,
        w.1 ⟨scheduleStart k + t * scheduleBlockLength k + r.val, hvisible⟩ =
          w.1 ⟨scheduleStart k + r.val, by omega⟩) ∧
    (∀ l m n : ℕ, ∀ hlm : l ≤ m, ∀ hmn : m ≤ n,
      ∀ w : PrefixFaithfulWordSpace n,
        restrictWord hlm (restrictWord hmn w) =
          restrictWord (hlm.trans hmn) w) ∧
    (∀ m n : ℕ, ∀ hmn : m ≤ n, ∀ w : PrefixFaithfulWordSpace m,
      restrictWord hmn (extendWord hmn w) = w) ∧
    (∀ m n : ℕ, ∀ hmn : m ≤ n,
      Function.Surjective (restrictWord hmn)) ∧
    (∀ n : ℕ, 1 ≤ n →
      n / 2 ≤ (partialFreeCoordinates n).card) ∧
    (∀ n : ℕ, ∀ w : PrefixFaithfulWordSpace n,
      (((finiteWordCode w).val + 1 : ℕ) : ℝ) / ((10 ^ n : ℕ) : ℝ) -
          (finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ) =
        (10 : ℝ) ^ (-(n : ℤ))) ∧
    (∀ n q : ℕ, 1 ≤ n → 1 ≤ q → ∀ a b : ℝ, a ≤ b →
      b - a ≤ 2 / (q : ℝ) ^ 7 →
      2 / (q : ℝ) ^ 7 ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ))) := by
  exact ⟨fun n i => by
      simpa [ConstrainedAt] using
        (mem_partialConstrainedCoordinates (n := n) (i := i)),
    fun _n _k _t w ht r hvisible =>
      prefixFaithfulWord_partialIslandConstraint w ht r hvisible,
    fun _l _m _n hlm hmn w => restrictWord_comp hlm hmn w,
    fun _m _n hmn w => restrictWord_extendWord hmn w,
    fun _m _n hmn => restrictWord_surjective hmn,
    partialFreeCoordinates_eventual_density,
    fun _n w => finiteWordCylinder_length w,
    exponentSeven_finiteInterval_antiConcentration⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T53

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.mem_partialConstrainedCoordinates
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.partialConstrainedCoordinates_card_twice_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.partialFreeCoordinates_eventual_density
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.prefixFaithfulWordSpace_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.prefixFaithfulWord_coordinate_eq_representative
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.prefixFaithfulWord_partialIslandConstraint
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.restrictWord_comp
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.restrictWord_extendWord
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.restrictWord_surjective
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.finiteWordCylinder_length
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.intervalWordEvent_card_le_three
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.finiteIntervalMass_le_freePower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.finiteIntervalMass_le_halfDensity
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.exponentSeven_finiteInterval_antiConcentration
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T53.prefixFaithfulFiniteCore_audit
