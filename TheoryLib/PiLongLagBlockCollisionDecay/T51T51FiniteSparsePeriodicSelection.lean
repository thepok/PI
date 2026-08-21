import TheoryLib.PiLongLagBlockCollisionDecay.T19T19SparsePeriodicIslands
import TheoryLib.PiLacunaryNearReturnSparsity.T6CylinderCollision

/-!
# T51: finite sparse-periodic selection

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
Canonical SHA-256:
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
Original source URL: none; the canonical file records a local formulation on 2026-07-23.

This module is only a finite base-ten selection core for the explicit T19
schedule.  It makes no assertion about an infinite product, irrationality
exponents, `Real.pi`, or the canonical collision question.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T51

open Theory.PiDigits.LongLagBlockCollisionDecay.T19

/-- Length of the coordinate interval occupied by T19 island `k`. -/
def scheduleIslandLength (k : ℕ) : ℕ :=
  schedulePeriodCount k * scheduleBlockLength k

/-- T19 scales whose entire island lies below the exclusive cutoff `n`. -/
def completedIslandScales (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k => scheduleSampleSize k ≤ n

/-- Coordinates forced by later copies of every T19 island completed below
the exclusive cutoff `n`.  The first period of each island remains free. -/
def completedConstrainedCoordinates (n : ℕ) : Finset ℕ :=
  (completedIslandScales n).biUnion fun k =>
    Finset.Ico (scheduleStart k + scheduleBlockLength k)
      (scheduleSampleSize k)

/-- Coordinates below `n` not designated as dependent by a completed island. -/
def completedFreeCoordinates (n : ℕ) : Finset ℕ :=
  Finset.range n \ completedConstrainedCoordinates n

theorem scheduleIndex_lt_start (k : ℕ) : k < scheduleStart k := by
  have hscale : k < 10 ^ scheduleScale k := by
    calc
      k < 10 ^ k := Nat.lt_pow_self (by norm_num)
      _ ≤ 10 ^ scheduleScale k := by
        apply Nat.pow_le_pow_right (by norm_num)
        simp [scheduleScale]
  calc
    k < 10 ^ scheduleScale k := hscale
    _ ≤ 10 ^ (5 * scheduleScale k) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have : 1 ≤ scheduleScale k := by simp [scheduleScale]
      omega
    _ = scheduleStart k := rfl

@[simp] theorem mem_completedIslandScales {n k : ℕ} :
    k ∈ completedIslandScales n ↔ scheduleSampleSize k ≤ n := by
  constructor
  · simp [completedIslandScales]
  · intro hk
    have hstartSample : scheduleStart k ≤ scheduleSampleSize k := by
      simp [scheduleSampleSize]
    have hkn : k < n :=
      (scheduleIndex_lt_start k).trans_le (hstartSample.trans hk)
    simp [completedIslandScales, hkn, hk]

theorem mem_completedConstrainedCoordinates {n i : ℕ} :
    i ∈ completedConstrainedCoordinates n ↔
      ∃ k, scheduleSampleSize k ≤ n ∧
        scheduleStart k + scheduleBlockLength k ≤ i ∧
        i < scheduleSampleSize k := by
  simp only [completedConstrainedCoordinates, Finset.mem_biUnion,
    mem_completedIslandScales, Finset.mem_Ico]

theorem completedConstrainedCoordinates_subset_range (n : ℕ) :
    completedConstrainedCoordinates n ⊆ Finset.range n := by
  intro i hi
  rw [mem_completedConstrainedCoordinates] at hi
  obtain ⟨k, hk, _hi0, hi1⟩ := hi
  exact Finset.mem_range.mpr (hi1.trans_le hk)

theorem completed_free_constrained_partition (n : ℕ) :
    (completedFreeCoordinates n).card +
        (completedConstrainedCoordinates n).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card
    (completedConstrainedCoordinates_subset_range n)
  simpa [completedFreeCoordinates] using h

theorem scheduleStart_monotone : Monotone scheduleStart := by
  intro j k hjk
  unfold scheduleStart scheduleScale
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem scheduleSampleSize_mono {j k : ℕ} (hjk : j ≤ k) :
    scheduleSampleSize j ≤ scheduleSampleSize k := by
  rcases hjk.eq_or_lt with rfl | hjk
  · rfl
  · calc
      scheduleSampleSize j ≤ scheduleStart (j + 1) :=
        scheduleSampleSize_le_next_start j
      _ ≤ scheduleStart k := scheduleStart_monotone (by omega)
      _ ≤ scheduleSampleSize k := by simp [scheduleSampleSize]

theorem five_mul_scheduleIslandLength_le_start (k : ℕ) :
    5 * scheduleIslandLength k ≤ scheduleStart k := by
  let t := scheduleScale k
  have ht : 100 * t ≤ 100 ^ t :=
    Nat.mul_le_pow (a := 100) (by norm_num) t
  calc
    5 * scheduleIslandLength k =
        10 ^ (3 * t) * (100 * t) := by
      dsimp [scheduleIslandLength, schedulePeriodCount,
        scheduleBlockLength, t]
      ring
    _ ≤ 10 ^ (3 * t) * 100 ^ t := Nat.mul_le_mul_left _ ht
    _ = 10 ^ (3 * t) * 10 ^ (2 * t) := by
      congr 1
      rw [pow_mul]
      norm_num
    _ = 10 ^ (5 * t) := by
      rw [← pow_add]
      congr 1
      omega
    _ = scheduleStart k := rfl

theorem ten_pow_five_mul_start_eq_next (k : ℕ) :
    10 ^ 5 * scheduleStart k = scheduleStart (k + 1) := by
  unfold scheduleStart scheduleScale
  rw [← pow_add]
  congr 1
  omega

theorem five_mul_scheduleSampleSize_le_next_start (k : ℕ) :
    5 * scheduleSampleSize k ≤ scheduleStart (k + 1) := by
  calc
    5 * scheduleSampleSize k ≤ 5 * (2 * scheduleStart k) :=
      Nat.mul_le_mul_left 5 (scheduleSampleSize_le_two_start k)
    _ ≤ 10 ^ 5 * scheduleStart k := by
      have h : 5 * 2 ≤ 10 ^ 5 := by norm_num
      calc
        5 * (2 * scheduleStart k) = (5 * 2) * scheduleStart k := by ring
        _ ≤ 10 ^ 5 * scheduleStart k :=
          Nat.mul_le_mul_right (scheduleStart k) h
    _ = scheduleStart (k + 1) := ten_pow_five_mul_start_eq_next k

theorem completedConstrainedCoordinates_card_twice_le (n : ℕ) :
    2 * (completedConstrainedCoordinates n).card ≤ n := by
  classical
  by_cases hscales : (completedIslandScales n).Nonempty
  · let k := (completedIslandScales n).max' hscales
    have hk : k ∈ completedIslandScales n :=
      Finset.max'_mem (completedIslandScales n) hscales
    have hkN : scheduleSampleSize k ≤ n :=
      mem_completedIslandScales.mp hk
    have hmax : ∀ j ∈ completedIslandScales n, j ≤ k := by
      intro j hj
      exact Finset.le_max' (completedIslandScales n) j hj
    cases hkval : k with
    | zero =>
        have hsubset : completedConstrainedCoordinates n ⊆
            Finset.Ico (scheduleStart 0 + scheduleBlockLength 0)
              (scheduleSampleSize 0) := by
          intro i hi
          rw [mem_completedConstrainedCoordinates] at hi
          obtain ⟨j, hjN, hj0, hj1⟩ := hi
          have hjmem : j ∈ completedIslandScales n :=
            mem_completedIslandScales.mpr hjN
          have hjle : j ≤ 0 := by simpa [hkval] using hmax j hjmem
          have hj : j = 0 := by omega
          subst j
          exact Finset.mem_Ico.mpr ⟨hj0, hj1⟩
        have hcard := Finset.card_le_card hsubset
        have hIco :
            (Finset.Ico (scheduleStart 0 + scheduleBlockLength 0)
              (scheduleSampleSize 0)).card ≤ scheduleIslandLength 0 := by
          rw [Nat.card_Ico]
          simp only [scheduleSampleSize, scheduleIslandLength]
          omega
        have hlength := five_mul_scheduleIslandLength_le_start 0
        have hsample : scheduleSampleSize 0 ≤ n := by simpa [hkval] using hkN
        have hsampleEq : scheduleSampleSize 0 =
            scheduleStart 0 + scheduleIslandLength 0 := rfl
        omega
    | succ s =>
        have hsubset : completedConstrainedCoordinates n ⊆
            Finset.range (scheduleSampleSize s) ∪
              Finset.Ico
                (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
                (scheduleSampleSize (s + 1)) := by
          intro i hi
          rw [mem_completedConstrainedCoordinates] at hi
          obtain ⟨j, hjN, hj0, hj1⟩ := hi
          have hjmem : j ∈ completedIslandScales n :=
            mem_completedIslandScales.mpr hjN
          have hjle : j ≤ s + 1 := by simpa [hkval] using hmax j hjmem
          by_cases hj : j = s + 1
          · subst j
            exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hj0, hj1⟩)
          · have hjs : j ≤ s := by omega
            have hiSample : i < scheduleSampleSize s :=
              hj1.trans_le (scheduleSampleSize_mono hjs)
            exact Finset.mem_union_left _ (Finset.mem_range.mpr hiSample)
        have hcard := Finset.card_le_card hsubset
        have hunion := Finset.card_union_le
          (Finset.range (scheduleSampleSize s))
          (Finset.Ico
            (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
            (scheduleSampleSize (s + 1)))
        have hIco :
            (Finset.Ico
              (scheduleStart (s + 1) + scheduleBlockLength (s + 1))
              (scheduleSampleSize (s + 1))).card ≤
                scheduleIslandLength (s + 1) := by
          rw [Nat.card_Ico]
          simp only [scheduleSampleSize, scheduleIslandLength]
          omega
        have hcover : (completedConstrainedCoordinates n).card ≤
            scheduleSampleSize s + scheduleIslandLength (s + 1) := by
          rw [Finset.card_range] at hunion
          omega
        have hprevious := five_mul_scheduleSampleSize_le_next_start s
        have hcurrent := five_mul_scheduleIslandLength_le_start (s + 1)
        have hsample : scheduleSampleSize (s + 1) ≤ n := by
          simpa [hkval] using hkN
        have hsampleEq : scheduleSampleSize (s + 1) =
            scheduleStart (s + 1) + scheduleIslandLength (s + 1) := rfl
        omega
  · have hempty : completedIslandScales n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hscales
    simp [completedConstrainedCoordinates, hempty]

/-- Every cutoff retains at least half of its coordinates as free choices.
The explicit onset is therefore `0`; the positive-cutoff form below uses `1`. -/
theorem completedFreeCoordinates_card_ge_half (n : ℕ) :
    n / 2 ≤ (completedFreeCoordinates n).card := by
  have hpartition := completed_free_constrained_partition n
  have hconstrained := completedConstrainedCoordinates_card_twice_le n
  omega

/-- Explicit positive onset and density constant: for every `n ≥ 1`, at least
one half of the first `n` coordinates are free. -/
theorem completedFreeCoordinates_eventual_density :
    ∀ n : ℕ, 1 ≤ n → n / 2 ≤ (completedFreeCoordinates n).card := by
  intro n _hn
  exact completedFreeCoordinates_card_ge_half n

/-- The first-period coordinate representing `i` in T19 island `k`. -/
def scheduleRepresentative (k i : ℕ) : ℕ :=
  scheduleStart k + (i - scheduleStart k) % scheduleBlockLength k

theorem scheduleSampleSize_le_start_of_lt {j k : ℕ} (hjk : j < k) :
    scheduleSampleSize j ≤ scheduleStart k := by
  calc
    scheduleSampleSize j ≤ scheduleStart (j + 1) :=
      scheduleSampleSize_le_next_start j
    _ ≤ scheduleStart k := scheduleStart_monotone (by omega)

theorem scheduleRepresentative_mem_firstPeriod {k i : ℕ} :
    scheduleRepresentative k i ∈
      Finset.Ico (scheduleStart k)
        (scheduleStart k + scheduleBlockLength k) := by
  have hm : 0 < scheduleBlockLength k := (schedule_parameters k).1
  rw [Finset.mem_Ico]
  constructor
  · exact Nat.le_add_right _ _
  · exact Nat.add_lt_add_left (Nat.mod_lt _ hm) _

theorem completed_constraint_scale_unique {i j k : ℕ}
    (hij : i ∈ Finset.Ico
      (scheduleStart j + scheduleBlockLength j) (scheduleSampleSize j))
    (hik : i ∈ Finset.Ico
      (scheduleStart k + scheduleBlockLength k) (scheduleSampleSize k)) :
    j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hsep := scheduleSampleSize_le_start_of_lt hjk
    have hij' := Finset.mem_Ico.mp hij
    have hik' := Finset.mem_Ico.mp hik
    omega
  · have hsep := scheduleSampleSize_le_start_of_lt hkj
    have hij' := Finset.mem_Ico.mp hij
    have hik' := Finset.mem_Ico.mp hik
    omega

theorem scheduleRepresentative_mem_completedFree {n k i : ℕ}
    (hk : k ∈ completedIslandScales n) :
    scheduleRepresentative k i ∈ completedFreeCoordinates n := by
  rw [completedFreeCoordinates, Finset.mem_sdiff, Finset.mem_range]
  have hrep := Finset.mem_Ico.mp
    (scheduleRepresentative_mem_firstPeriod (k := k) (i := i))
  have hkN := mem_completedIslandScales.mp hk
  constructor
  · have hmle : scheduleBlockLength k ≤
        schedulePeriodCount k * scheduleBlockLength k := by
      have hq : 1 ≤ schedulePeriodCount k := by
        have := two_le_schedulePeriodCount k
        omega
      exact Nat.le_mul_of_pos_left _ hq
    have hperiodEnd : scheduleStart k + scheduleBlockLength k ≤
        scheduleSampleSize k := by
      simp only [scheduleSampleSize]
      omega
    exact (hrep.2.trans_le hperiodEnd).trans_le hkN
  · intro hconstrained
    rw [mem_completedConstrainedCoordinates] at hconstrained
    obtain ⟨j, hjN, hj0, hj1⟩ := hconstrained
    have hj : j ∈ completedIslandScales n :=
      mem_completedIslandScales.mpr hjN
    by_cases hjk : j = k
    · subst j
      omega
    · rcases lt_or_gt_of_ne hjk with hjk | hkj
      · have hsep := scheduleSampleSize_le_start_of_lt hjk
        omega
      · have hsep := scheduleSampleSize_le_start_of_lt hkj
        have hmle : scheduleBlockLength k ≤
            schedulePeriodCount k * scheduleBlockLength k := by
          have hq : 1 ≤ schedulePeriodCount k := by
            have := two_le_schedulePeriodCount k
            omega
          exact Nat.le_mul_of_pos_left _ hq
        have hperiodEnd : scheduleStart k + scheduleBlockLength k ≤
            scheduleSampleSize k := by
          simp only [scheduleSampleSize]
          omega
        omega

/-- Free coordinate type displayed by the finite sample space. -/
abbrev FreeCoordinate (n : ℕ) := ↥(completedFreeCoordinates n)

/-- Every designated free natural coordinate is canonically a coordinate of a
length-`n` word. -/
def freeCoordinateToFin {n : ℕ} (i : FreeCoordinate n) : Fin n :=
  ⟨i.val, (Finset.mem_sdiff.mp i.property).1 |> Finset.mem_range.mp⟩

/-- A witness scale for a constrained coordinate. -/
def constrainedScale {n : ℕ} (i : Fin n)
    (hi : i.val ∈ completedConstrainedCoordinates n) : ℕ :=
  Classical.choose (mem_completedConstrainedCoordinates.mp hi)

theorem constrainedScale_spec {n : ℕ} (i : Fin n)
    (hi : i.val ∈ completedConstrainedCoordinates n) :
    scheduleSampleSize (constrainedScale i hi) ≤ n ∧
      scheduleStart (constrainedScale i hi) +
          scheduleBlockLength (constrainedScale i hi) ≤ i.val ∧
      i.val < scheduleSampleSize (constrainedScale i hi) :=
  Classical.choose_spec (mem_completedConstrainedCoordinates.mp hi)

/-- Root each word coordinate at its unique free first-period coordinate. -/
def rootCoordinate (n : ℕ) (i : Fin n) : FreeCoordinate n := by
  classical
  by_cases hi : i.val ∈ completedConstrainedCoordinates n
  · let k := constrainedScale i hi
    exact ⟨scheduleRepresentative k i.val,
      scheduleRepresentative_mem_completedFree
        (mem_completedIslandScales.mpr (constrainedScale_spec i hi).1)⟩
  · exact ⟨i.val, Finset.mem_sdiff.mpr
      ⟨Finset.mem_range.mpr i.isLt, hi⟩⟩

theorem rootCoordinate_of_free {n : ℕ} (i : FreeCoordinate n) :
    rootCoordinate n (freeCoordinateToFin i) = i := by
  classical
  apply Subtype.ext
  simp only [rootCoordinate]
  split
  · rename_i hi
    exact (Finset.mem_sdiff.mp i.property).2 hi |>.elim
  · rfl

theorem rootCoordinate_eq_scheduleRepresentative {n k : ℕ} (i : Fin n)
    (hk : k ∈ completedIslandScales n)
    (hi : i.val ∈ Finset.Ico
      (scheduleStart k + scheduleBlockLength k) (scheduleSampleSize k)) :
    (rootCoordinate n i).val = scheduleRepresentative k i.val := by
  classical
  have hconstrained : i.val ∈ completedConstrainedCoordinates n := by
    rw [mem_completedConstrainedCoordinates]
    exact ⟨k, mem_completedIslandScales.mp hk,
      (Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2⟩
  simp only [rootCoordinate, dif_pos hconstrained]
  let j := constrainedScale i hconstrained
  have hjSpec := constrainedScale_spec i hconstrained
  have hj : j ∈ completedIslandScales n :=
    mem_completedIslandScales.mpr hjSpec.1
  have hjmem : i.val ∈ Finset.Ico
      (scheduleStart j + scheduleBlockLength j) (scheduleSampleSize j) :=
    Finset.mem_Ico.mpr ⟨hjSpec.2.1, hjSpec.2.2⟩
  have hjk := completed_constraint_scale_unique hjmem hi
  have hjk' : constrainedScale i hconstrained = k := by
    simpa [j] using hjk
  change scheduleRepresentative (constrainedScale i hconstrained) i.val =
    scheduleRepresentative k i.val
  rw [hjk']

/-- A zero-based length-`n` decimal word. -/
abbrev DecimalWord (n : ℕ) := Fin n → Fin 10

/-- Finite base-ten words generated by the free coordinates under all T19
island constraints completed below the cutoff `n`. -/
def FiniteSparseWordSpace (n : ℕ) :=
  {w : DecimalWord n // ∀ i, w i = w (freeCoordinateToFin (rootCoordinate n i))}

/-- Restriction to free coordinates is an exact parametrization of the finite
sparse-periodic word space. -/
def finiteSparseWordEquiv (n : ℕ) :
    FiniteSparseWordSpace n ≃ (FreeCoordinate n → Fin 10) where
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

/-- Exact finite sample-space cardinality: one base-ten choice per displayed
free coordinate and no hidden multiplicative factor. -/
theorem finiteSparseWordSpace_card (n : ℕ) :
    Nat.card (FiniteSparseWordSpace n) =
      10 ^ (completedFreeCoordinates n).card := by
  classical
  rw [Nat.card_congr (finiteSparseWordEquiv n), Nat.card_fun]
  simp

theorem scheduleRepresentative_periodic_coordinate (k t : ℕ)
    (r : Fin (scheduleBlockLength k)) :
    scheduleRepresentative k
        (scheduleStart k + t * scheduleBlockLength k + r.val) =
      scheduleStart k + r.val := by
  have hsub : scheduleStart k + t * scheduleBlockLength k + r.val -
      scheduleStart k = t * scheduleBlockLength k + r.val := by omega
  rw [scheduleRepresentative, hsub]
  simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]

/-- Every sampled word obeys the displayed T19 coordinate constraint in each
island completed below its cutoff. -/
theorem finiteSparseWord_coordinate_eq_representative {n k : ℕ}
    (w : FiniteSparseWordSpace n) (hk : scheduleSampleSize k ≤ n)
    (i : Fin n)
    (hi : i.val ∈ Finset.Ico
      (scheduleStart k + scheduleBlockLength k) (scheduleSampleSize k)) :
    w.1 i = w.1 ⟨scheduleRepresentative k i.val,
      (Finset.mem_sdiff.mp (scheduleRepresentative_mem_completedFree
        (mem_completedIslandScales.mpr hk))).1 |> Finset.mem_range.mp⟩ := by
  have hw := w.2 i
  have hroot := rootCoordinate_eq_scheduleRepresentative i
    (mem_completedIslandScales.mpr hk) hi
  exact hw.trans (congrArg w.1 (Fin.ext hroot))

/-- Extend a finite sampled word by zero outside its displayed cutoff. -/
def finiteWordStream {n : ℕ} (w : FiniteSparseWordSpace n) : DecimalStream :=
  fun i => if hi : i < n then w.1 ⟨i, hi⟩ else 0

@[simp] theorem finiteWordStream_of_lt {n : ℕ} (w : FiniteSparseWordSpace n)
    {i : ℕ} (hi : i < n) : finiteWordStream w i = w.1 ⟨i, hi⟩ := by
  simp [finiteWordStream, hi]

/-- The finite sample space satisfies T19's exact periodic-island certificate
at every scale whose sample-size cutoff has been reached. -/
theorem finiteSparseWord_periodicIslandCertificate {n k : ℕ}
    (w : FiniteSparseWordSpace n) (hk : scheduleSampleSize k ≤ n) :
    PeriodicIslandCertificate (finiteWordStream w) (scheduleStart k)
      (scheduleBlockLength k) (schedulePeriodCount k)
      (scheduleSampleSize k) := by
  refine
    { period_pos := (schedule_parameters k).1
      island_fits := le_of_eq (schedule_parameters k).2
      periodic := ?_ }
  intro t ht
  funext r
  have hr : r.val < scheduleBlockLength k := r.isLt
  have hleftSample :
      scheduleStart k + t * scheduleBlockLength k + r.val <
        scheduleSampleSize k := by
    have ht1 : t + 1 ≤ schedulePeriodCount k := by omega
    have hwithin : t * scheduleBlockLength k + r.val <
        schedulePeriodCount k * scheduleBlockLength k := by
      calc
        t * scheduleBlockLength k + r.val <
            t * scheduleBlockLength k + scheduleBlockLength k :=
          Nat.add_lt_add_left hr _
        _ = (t + 1) * scheduleBlockLength k := by ring
        _ ≤ schedulePeriodCount k * scheduleBlockLength k :=
          Nat.mul_le_mul_right (scheduleBlockLength k) ht1
    simp only [scheduleSampleSize]
    omega
  have hrightSample : scheduleStart k + r.val < scheduleSampleSize k := by
    have hmle : scheduleBlockLength k ≤
        schedulePeriodCount k * scheduleBlockLength k := by
      have hq : 1 ≤ schedulePeriodCount k := by
        have := two_le_schedulePeriodCount k
        omega
      exact Nat.le_mul_of_pos_left _ hq
    simp only [scheduleSampleSize]
    omega
  have hleftCutoff := hleftSample.trans_le hk
  have hrightCutoff := hrightSample.trans_le hk
  simp only [streamBlock, finiteWordStream_of_lt w hleftCutoff,
    finiteWordStream_of_lt w hrightCutoff]
  by_cases ht0 : t = 0
  · subst t
    apply congrArg w.1
    apply Fin.ext
    simp
  · have hone : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
    let i : Fin n :=
      ⟨scheduleStart k + t * scheduleBlockLength k + r.val, hleftCutoff⟩
    have hi : i.val ∈ Finset.Ico
        (scheduleStart k + scheduleBlockLength k) (scheduleSampleSize k) := by
      rw [Finset.mem_Ico]
      dsimp [i]
      constructor
      · have hmpos := (schedule_parameters k).1
        nlinarith
      · exact hleftSample
    have hword := finiteSparseWord_coordinate_eq_representative w hk i hi
    have hrep := scheduleRepresentative_periodic_coordinate k t r
    dsimp [i] at hword
    exact hword.trans (congrArg w.1 (Fin.ext hrep))

/-- Most-significant-first numerical label of a sampled decimal word. -/
def finiteWordCode {n : ℕ} (w : FiniteSparseWordSpace n) : Fin (10 ^ n) :=
  Theory.PiDigits.PositiveLowerBlockDensity.T12.decimalWordIndexEquiv n w.1

theorem finiteWordCode_injective (n : ℕ) :
    Function.Injective (finiteWordCode : FiniteSparseWordSpace n → Fin (10 ^ n)) := by
  intro w v h
  apply Subtype.ext
  exact (Theory.PiDigits.PositiveLowerBlockDensity.T12.decimalWordIndexEquiv n).injective h

/-- Half-open real decimal cylinder selected by a sampled word. -/
def finiteWordCylinder {n : ℕ} (w : FiniteSparseWordSpace n) : Set ℝ :=
  Set.Ico ((finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ))
    ((((finiteWordCode w).val + 1 : ℕ) : ℝ) / ((10 ^ n : ℕ) : ℝ))

/-- Exact length of every level-`n` sampled decimal cylinder. -/
theorem finiteWordCylinder_length {n : ℕ} (w : FiniteSparseWordSpace n) :
    (((finiteWordCode w).val + 1 : ℕ) : ℝ) / ((10 ^ n : ℕ) : ℝ) -
        (finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ) =
      (10 : ℝ) ^ (-(n : ℤ)) := by
  have hpow : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by positivity
  rw [zpow_neg, zpow_natCast]
  field_simp
  norm_num

/-- Sampled words whose half-open decimal cylinders meet the closed interval
`[a,b]`. -/
def IntervalWordEvent (n : ℕ) (a b : ℝ) :=
  {w : FiniteSparseWordSpace n //
    (finiteWordCylinder w ∩ Set.Icc a b).Nonempty}

/-- Uniform finite mass of sampled words whose decimal cylinders meet
`[a,b]`. -/
def finiteIntervalMass (n : ℕ) (a b : ℝ) : ℝ :=
  (Nat.card (IntervalWordEvent n a b) : ℝ) /
    Nat.card (FiniteSparseWordSpace n)

/-- A closed real interval of at most one level-`n` cylinder width meets at
most three sampled cylinders.  The constant `3` includes both endpoint-safe
cyclic neighbours. -/
theorem intervalWordEvent_card_le_three (n : ℕ) (a b : ℝ)
    (_hab : a ≤ b)
    (hlength : b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹) :
    Nat.card (IntervalWordEvent n a b) ≤ 3 := by
  classical
  by_cases hEvent : Nonempty (IntervalWordEvent n a b)
  · let w0 : IntervalWordEvent n a b := Classical.choice hEvent
    let c0 : Fin (10 ^ n) := finiteWordCode w0.val
    let labels : Finset (Fin (10 ^ n)) :=
      {c0, finRotate (10 ^ n) c0, (finRotate (10 ^ n)).symm c0}
    let encode : IntervalWordEvent n a b → ↥labels := fun w =>
      ⟨finiteWordCode w.val, by
        obtain ⟨x, hxCylinder, hxInterval⟩ := w.property
        obtain ⟨y, hyCylinder, hyInterval⟩ := w0.property
        have hxy : |x - y| ≤ b - a := by
          rw [abs_le]
          constructor <;> linarith [hxInterval.1, hxInterval.2,
            hyInterval.1, hyInterval.2]
        have hnear : dist (y : UnitAddCircle) (x : UnitAddCircle) ≤
            (((10 ^ n : ℕ) : ℝ))⁻¹ := by
          rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
          calc
            ‖((y - x : ℝ) : UnitAddCircle)‖ ≤ ‖y - x‖ :=
              QuotientAddGroup.norm_mk_le_norm
            _ = |x - y| := by rw [Real.norm_eq_abs, abs_sub_comm]
            _ ≤ b - a := hxy
            _ ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ := hlength
        have hadj : DecimalFactorComplexity.NormalOrbitNearReturns.CyclicAdjacent
            (10 ^ n) c0 (finiteWordCode w.val) := by
          apply DecimalFactorComplexity.CylinderCollision.dist_le_inv_of_mem_Ico_implies_cyclicAdjacent
              (q := 10 ^ n) (a := c0.val) (b := (finiteWordCode w.val).val)
              (x := y) (y := x) (by positivity) c0.isLt
              (finiteWordCode w.val).isLt
          · exact hyCylinder
          · exact hxCylinder
          · exact hnear
        rcases DecimalFactorComplexity.CylinderCollision.cyclicAdjacent_three_cases
            (by positivity) c0 (finiteWordCode w.val) hadj with h | h | h
        · simp [labels, h]
        · simp [labels, h]
        · simp [labels, h]⟩
    have hencode : Function.Injective encode := by
      intro w v hwv
      apply Subtype.ext
      apply finiteWordCode_injective n
      exact congrArg Subtype.val hwv
    calc
      Nat.card (IntervalWordEvent n a b) ≤ Nat.card ↥labels :=
        Nat.card_le_card_of_injective encode hencode
      _ = labels.card := by simp
      _ ≤ 3 := by
        dsimp [labels]
        exact (Finset.card_insert_le c0
          {finRotate (10 ^ n) c0, (finRotate (10 ^ n)).symm c0}).trans
            (by
              have htwo := Finset.card_insert_le (finRotate (10 ^ n) c0)
                {(finRotate (10 ^ n)).symm c0}
              simp only [Finset.card_singleton] at htwo
              omega)
  · letI : IsEmpty (IntervalWordEvent n a b) :=
      ⟨fun w => hEvent ⟨w⟩⟩
    simp

/-- Exact finite interval anti-concentration before applying free density. -/
theorem finiteIntervalMass_le_freePower (n : ℕ) (a b : ℝ)
    (hab : a ≤ b)
    (hlength : b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹) :
    finiteIntervalMass n a b ≤
      3 * (10 : ℝ) ^ (-((completedFreeCoordinates n).card : ℤ)) := by
  have hcard := intervalWordEvent_card_le_three n a b hab hlength
  rw [finiteIntervalMass, finiteSparseWordSpace_card]
  calc
    (Nat.card (IntervalWordEvent n a b) : ℝ) /
          (10 ^ (completedFreeCoordinates n).card : ℕ) ≤
        3 / (10 ^ (completedFreeCoordinates n).card : ℕ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = 3 * (10 : ℝ) ^ (-((completedFreeCoordinates n).card : ℤ)) := by
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
      norm_num

/-- Explicit-onset anti-concentration: onset `1`, interval constant `3`,
base `10`, and free-density exponent `n/2` are all visible. -/
theorem finiteIntervalMass_le_halfDensity :
    ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ, a ≤ b →
      b - a ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
  intro n _hn a b hab hlength
  have hmass := finiteIntervalMass_le_freePower n a b hab hlength
  have hfree := completedFreeCoordinates_card_ge_half n
  have hpow : (10 : ℝ) ^ (n / 2) ≤
      (10 : ℝ) ^ (completedFreeCoordinates n).card :=
    pow_le_pow_right₀ (by norm_num) hfree
  have hinv : ((10 : ℝ) ^ (completedFreeCoordinates n).card)⁻¹ ≤
      ((10 : ℝ) ^ (n / 2))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hnegative :
      (10 : ℝ) ^ (-((completedFreeCoordinates n).card : ℤ)) ≤
        (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
    simpa [zpow_neg, zpow_natCast] using hinv
  exact hmass.trans (mul_le_mul_of_nonneg_left hnegative (by norm_num))

/-- Exponent-seven shell-ready specialization.  This remains a finite
selection estimate: it asserts no Borel--Cantelli or Diophantine conclusion. -/
theorem exponentSeven_finiteInterval_antiConcentration :
    ∀ n q : ℕ, 1 ≤ n → 1 ≤ q → ∀ a b : ℝ, a ≤ b →
      b - a ≤ 2 / (q : ℝ) ^ 7 →
      2 / (q : ℝ) ^ 7 ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ)) := by
  intro n q hn _hq a b hab hlength hscale
  exact finiteIntervalMass_le_halfDensity n hn a b hab (hlength.trans hscale)

/-- One inspectable theorem type collecting the finite T51 acceptance surface:
the T19 schedule and cutoff, constrained/free partition, exact sample-space
cardinality, exact decimal-cylinder length, onset, exponent seven, and every
The constant in the anti-concentration bound. -/
theorem finiteSelectionCore_audit :
    (∀ n : ℕ,
      (completedFreeCoordinates n).card +
        (completedConstrainedCoordinates n).card = n) ∧
    (∀ n : ℕ, Nat.card (FiniteSparseWordSpace n) =
      10 ^ (completedFreeCoordinates n).card) ∧
    (∀ n k : ℕ, ∀ w : FiniteSparseWordSpace n,
      scheduleSampleSize k ≤ n →
      PeriodicIslandCertificate (finiteWordStream w) (scheduleStart k)
        (scheduleBlockLength k) (schedulePeriodCount k)
        (scheduleSampleSize k)) ∧
    (∀ n : ℕ, ∀ w : FiniteSparseWordSpace n,
      (((finiteWordCode w).val + 1 : ℕ) : ℝ) / ((10 ^ n : ℕ) : ℝ) -
          (finiteWordCode w).val / ((10 ^ n : ℕ) : ℝ) =
        (10 : ℝ) ^ (-(n : ℤ))) ∧
    (∀ n q : ℕ, 1 ≤ n → 1 ≤ q → ∀ a b : ℝ, a ≤ b →
      b - a ≤ 2 / (q : ℝ) ^ 7 →
      2 / (q : ℝ) ^ 7 ≤ (((10 ^ n : ℕ) : ℝ))⁻¹ →
      finiteIntervalMass n a b ≤
        3 * (10 : ℝ) ^ (-((n / 2 : ℕ) : ℤ))) := by
  exact ⟨completed_free_constrained_partition,
    finiteSparseWordSpace_card,
    fun _n _k w hk => finiteSparseWord_periodicIslandCertificate w hk,
    fun _n w => finiteWordCylinder_length w,
    exponentSeven_finiteInterval_antiConcentration⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T51

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.mem_completedConstrainedCoordinates
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.completedFreeCoordinates_card_ge_half
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.completedFreeCoordinates_eventual_density
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.scheduleRepresentative_mem_completedFree
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteSparseWordSpace_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteSparseWord_periodicIslandCertificate
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteWordCylinder_length
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.intervalWordEvent_card_le_three
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteIntervalMass_le_freePower
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteIntervalMass_le_halfDensity
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.exponentSeven_finiteInterval_antiConcentration
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T51.finiteSelectionCore_audit
