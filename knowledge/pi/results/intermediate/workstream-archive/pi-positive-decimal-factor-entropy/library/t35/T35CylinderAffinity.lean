import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# T35: finite-cylinder Hellinger affinity

Canonical source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This module concerns arbitrary probability measures on the one-sided decimal
shift.  It makes no assertion that any overlap hypothesis holds for the
decimal orbit of `Real.pi`.
-/

noncomputable section

open Filter Finset Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace DecimalFactorEntropy.CylinderAffinity

/-- Decimal digits, represented without an implicit coercion to natural numbers. -/
abbrev Digit := Fin 10

/-- The one-sided decimal shift space. -/
abbrev DecimalShift := ℕ → Digit

/-- Recursive finite words.  The successor constructor appends one digit. -/
def Word : ℕ → Type
  | 0 => Fin 1
  | m + 1 => Word m × Digit

instance wordFintype (m : ℕ) : Fintype (Word m) := by
  induction m with
  | zero => change Fintype (Fin 1); infer_instance
  | succ m ih => change Fintype (Word m × Digit); infer_instance

instance wordDecidableEq (m : ℕ) : DecidableEq (Word m) := by
  induction m with
  | zero => change DecidableEq (Fin 1); infer_instance
  | succ m ih => change DecidableEq (Word m × Digit); infer_instance

/-- The complete prefix cylinder determined by a recursive word. -/
def cylinder : (m : ℕ) → Word m → Set DecimalShift
  | 0, _ => Set.univ
  | m + 1, (w, a) => cylinder m w ∩ {x | x m = a}

theorem cylinder_zero (w : Word 0) : cylinder 0 w = Set.univ := rfl

theorem cylinder_succ (m : ℕ) (w : Word m) (a : Digit) :
    cylinder (m + 1) (w, a) = cylinder m w ∩ {x | x m = a} := rfl

/-- Every prefix cylinder is measurable in the product sigma algebra. -/
theorem cylinder_measurable : ∀ (m : ℕ) (w : Word m), MeasurableSet (cylinder m w)
  | 0, _ => MeasurableSet.univ
  | m + 1, (w, a) =>
      (cylinder_measurable m w).inter
        (measurableSet_eq_fun (measurable_pi_apply m)
          (measurable_const : Measurable (fun _ : DecimalShift => a)))

/-- Distinct words at one depth define disjoint cylinders. -/
theorem cylinder_pairwise_disjoint (m : ℕ) :
    Pairwise fun u v : Word m => Disjoint (cylinder m u) (cylinder m v) := by
  induction m with
  | zero =>
      intro u v huv
      apply (huv ?_).elim
      exact Fin.ext (by omega)
  | succ m ih =>
      rintro ⟨u, a⟩ ⟨v, b⟩ huv
      by_cases huvParent : u = v
      · subst v
        have hab : a ≠ b := by
          intro hab
          apply huv
          simp [hab]
        rw [Set.disjoint_left]
        intro x hx hy
        exact hab (hx.2.symm.trans hy.2)
      · exact (ih huvParent).mono inter_subset_left inter_subset_left

/-- The depth-`m` cylinders cover the shift space. -/
theorem iUnion_cylinder (m : ℕ) : (⋃ w : Word m, cylinder m w) = Set.univ := by
  induction m with
  | zero =>
      change (⋃ _ : Fin 1, Set.univ) = Set.univ
      ext x
      simp
  | succ m ih =>
      change (⋃ wa : Word m × Digit, cylinder (m + 1) wa) = Set.univ
      rw [Set.iUnion_prod']
      ext x
      constructor
      · intro hx
        exact Set.mem_univ x
      · intro hx
        have hxall : x ∈ ⋃ w : Word m, cylinder m w := by
          rw [ih]
          exact Set.mem_univ x
        obtain ⟨w, hxw⟩ := Set.mem_iUnion.mp hxall
        apply Set.mem_iUnion.2
        refine ⟨w, Set.mem_iUnion.2 ⟨x m, ?_⟩⟩
        exact ⟨hxw, rfl⟩

/-- A depth-`m` cylinder is the disjoint union of its ten children. -/
theorem cylinder_eq_iUnion_children (m : ℕ) (w : Word m) :
    cylinder m w = ⋃ a : Digit, cylinder (m + 1) (w, a) := by
  ext x
  simp [cylinder]

theorem children_pairwise_disjoint (m : ℕ) (w : Word m) :
    Pairwise fun a b : Digit =>
      Disjoint (cylinder (m + 1) (w, a)) (cylinder (m + 1) (w, b)) := by
  intro a b hab
  apply cylinder_pairwise_disjoint (m + 1)
  intro h
  exact hab (congrArg Prod.snd h)

/-- Real mass of a finite prefix cylinder. -/
def cylinderMass (μ : Measure DecimalShift) (m : ℕ) (w : Word m) : ℝ :=
  (μ (cylinder m w)).toReal

theorem cylinderMass_nonneg (μ : Measure DecimalShift) (m : ℕ) (w : Word m) :
    0 ≤ cylinderMass μ m w := ENNReal.toReal_nonneg

/-- Child masses sum exactly to the parent mass for a finite measure. -/
theorem sum_child_cylinderMass [IsFiniteMeasure μ]
    (m : ℕ) (w : Word m) :
    ∑ a : Digit, cylinderMass μ (m + 1) (w, a) = cylinderMass μ m w := by
  simp only [cylinderMass]
  rw [cylinder_eq_iUnion_children,
    measure_iUnion (children_pairwise_disjoint m w)
      (fun a => cylinder_measurable (m + 1) (w, a)),
    tsum_fintype]
  rw [ENNReal.toReal_sum]
  intro a ha
  exact measure_ne_top μ _

/-- Finite-cylinder Hellinger affinity at exactly depth `m`. -/
def affinity (μ ν : Measure DecimalShift) (m : ℕ) : ℝ :=
  ∑ w : Word m, √(cylinderMass μ m w * cylinderMass ν m w)

theorem affinity_nonneg (μ ν : Measure DecimalShift) (m : ℕ) :
    0 ≤ affinity μ ν m := by
  exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- Cylinder masses at any complete depth sum to the total mass. -/
theorem sum_cylinderMass_eq_univ [IsFiniteMeasure μ] (m : ℕ) :
    ∑ w : Word m, cylinderMass μ m w = (μ Set.univ).toReal := by
  induction m with
  | zero =>
      simp [cylinderMass, cylinder, Word]
  | succ m ih =>
      change (∑ wa : Word m × Digit, cylinderMass μ (m + 1) wa) = (μ Set.univ).toReal
      rw [Fintype.sum_prod_type]
      simp_rw [sum_child_cylinderMass]
      exact ih

/-- Probability specialization of `sum_cylinderMass_eq_univ`. -/
theorem sum_cylinderMass_eq_one [IsProbabilityMeasure μ] (m : ℕ) :
    ∑ w : Word m, cylinderMass μ m w = 1 := by
  rw [sum_cylinderMass_eq_univ, measure_univ]
  norm_num

/-- Cauchy--Schwarz after splitting a complete depth partition into selected
and unselected words.  Every depth and both finite measures remain explicit. -/
theorem affinity_le_split [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : ℕ) (selected : Finset (Word m)) :
    affinity μ ν m ≤
      √(∑ w ∈ selected, cylinderMass μ m w) *
          √(∑ w ∈ selected, cylinderMass ν m w) +
        √(∑ w ∈ (Finset.univ : Finset (Word m)).filter (· ∉ selected),
            cylinderMass μ m w) *
          √(∑ w ∈ (Finset.univ : Finset (Word m)).filter (· ∉ selected),
            cylinderMass ν m w) := by
  rw [affinity, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ selected)]
  apply add_le_add
  · calc
      (∑ x ∈ Finset.univ.filter (· ∈ selected),
          √(cylinderMass μ m x * cylinderMass ν m x)) =
          ∑ x ∈ selected,
            √(cylinderMass μ m x) * √(cylinderMass ν m x) := by
              apply Finset.sum_congr (by ext x; simp)
              intro x hx
              rw [Real.sqrt_mul (cylinderMass_nonneg μ m x)]
      _ ≤ √(∑ x ∈ selected, cylinderMass μ m x) *
          √(∑ x ∈ selected, cylinderMass ν m x) := by
            exact Real.sum_sqrt_mul_sqrt_le selected
              (fun x => cylinderMass_nonneg μ m x)
              (fun x => cylinderMass_nonneg ν m x)
  · let remaining := (Finset.univ : Finset (Word m)).filter (· ∉ selected)
    change (∑ x ∈ Finset.univ.filter (· ∉ selected),
      √(cylinderMass μ m x * cylinderMass ν m x)) ≤ _
    calc
      (∑ x ∈ remaining, √(cylinderMass μ m x * cylinderMass ν m x)) =
          ∑ x ∈ remaining,
            √(cylinderMass μ m x) * √(cylinderMass ν m x) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Real.sqrt_mul (cylinderMass_nonneg μ m x)]
      _ ≤ √(∑ x ∈ remaining, cylinderMass μ m x) *
          √(∑ x ∈ remaining, cylinderMass ν m x) := by
            exact Real.sum_sqrt_mul_sqrt_le remaining
              (fun x => cylinderMass_nonneg μ m x)
              (fun x => cylinderMass_nonneg ν m x)

/-- Refining the complete decimal-cylinder partition cannot increase affinity. -/
theorem affinity_antitone [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Antitone (affinity μ ν) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [affinity, affinity]
  change (∑ wa : Word m × Digit,
      √(cylinderMass μ (m + 1) wa * cylinderMass ν (m + 1) wa)) ≤ _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro w hw
  calc
    (∑ a : Digit,
        √(cylinderMass μ (m + 1) (w, a) * cylinderMass ν (m + 1) (w, a))) =
        ∑ a : Digit,
          √(cylinderMass μ (m + 1) (w, a)) *
            √(cylinderMass ν (m + 1) (w, a)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Real.sqrt_mul (cylinderMass_nonneg μ _ _)]
    _ ≤ √(∑ a : Digit, cylinderMass μ (m + 1) (w, a)) *
          √(∑ a : Digit, cylinderMass ν (m + 1) (w, a)) := by
      simpa using Real.sum_sqrt_mul_sqrt_le (f := fun a : Digit =>
          cylinderMass μ (m + 1) (w, a)) (g := fun a : Digit =>
          cylinderMass ν (m + 1) (w, a))
        (Finset.univ : Finset Digit)
        (fun a => cylinderMass_nonneg μ _ _)
        (fun a => cylinderMass_nonneg ν _ _)
    _ = √(cylinderMass μ m w * cylinderMass ν m w) := by
      rw [sum_child_cylinderMass, sum_child_cylinderMass,
        Real.sqrt_mul (cylinderMass_nonneg μ _ _)]

/-- The affinity limit is the infimum over every finite depth. -/
def affinityLimit (μ ν : Measure DecimalShift) : ℝ :=
  sInf (Set.range (affinity μ ν))

theorem affinity_tendsto_limit [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Tendsto (affinity μ ν) atTop (𝓝 (affinityLimit μ ν)) := by
  exact tendsto_atTop_ciInf affinity_antitone
    ⟨0, by rintro _ ⟨m, rfl⟩; exact affinity_nonneg μ ν m⟩

/-- Explicit finite-cylinder approximation consequence of generation in measure.
It records both measures, every measurable set, the selected depth and words,
and the two one-sided errors needed to approximate a separating set. -/
def GeneratesInMeasure (μ ν : Measure DecimalShift) : Prop :=
  ∀ s : Set DecimalShift, MeasurableSet s → ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ, ∃ words : Finset (Word m),
      (∑ w ∈ words, cylinderMass μ m w) ≤ (μ s).toReal + ε ∧
        (∑ w ∈ (Finset.univ : Finset (Word m)).filter (· ∉ words),
          cylinderMass ν m w) ≤ (ν sᶜ).toReal + ε

/-- The generation hypothesis plus mutual singularity forces the affinity
infimum to vanish.  The proof uses only finite partition Cauchy--Schwarz. -/
theorem mutuallySingular_implies_affinityLimit_eq_zero
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hgenerate : GeneratesInMeasure μ ν) (hsing : μ ⟂ₘ ν) :
    affinityLimit μ ν = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨m, words, hμwords, hνremaining⟩ :=
      hgenerate hsing.nullSet hsing.measurableSet_nullSet ((δ / 2) ^ 2) (by positivity)
    have hμsmall : (∑ w ∈ words, cylinderMass μ m w) ≤ (δ / 2) ^ 2 := by
      simpa using hμwords
    have hνsmall : (∑ w ∈ (Finset.univ : Finset (Word m)).filter (· ∉ words),
        cylinderMass ν m w) ≤ (δ / 2) ^ 2 := by
      simpa using hνremaining
    have hμall : (∑ w ∈ words, cylinderMass μ m w) ≤ 1 := by
      calc
        (∑ w ∈ words, cylinderMass μ m w) ≤
            ∑ w : Word m, cylinderMass μ m w := by
              apply Finset.sum_le_univ_sum_of_nonneg
              exact cylinderMass_nonneg μ m
        _ = 1 := sum_cylinderMass_eq_one m
    have hνall : (∑ w ∈ words, cylinderMass ν m w) ≤ 1 := by
      calc
        (∑ w ∈ words, cylinderMass ν m w) ≤
            ∑ w : Word m, cylinderMass ν m w := by
              apply Finset.sum_le_univ_sum_of_nonneg
              exact cylinderMass_nonneg ν m
        _ = 1 := sum_cylinderMass_eq_one m
    have hμremaining :
        (∑ w ∈ (Finset.univ : Finset (Word m)).filter (· ∉ words),
          cylinderMass μ m w) ≤ 1 := by
      calc
        _ ≤ ∑ w : Word m, cylinderMass μ m w := by
          apply Finset.sum_le_univ_sum_of_nonneg
          exact cylinderMass_nonneg μ m
        _ = 1 := sum_cylinderMass_eq_one m
    have hbdd : BddBelow (Set.range (affinity μ ν)) :=
      ⟨0, by rintro _ ⟨n, rfl⟩; exact affinity_nonneg μ ν n⟩
    have hlimit_le : affinityLimit μ ν ≤ affinity μ ν m :=
      csInf_le hbdd (Set.mem_range_self m)
    calc
      affinityLimit μ ν ≤ affinity μ ν m := hlimit_le
      _ ≤ √((δ / 2) ^ 2) * √1 + √1 * √((δ / 2) ^ 2) := by
        refine (affinity_le_split m words).trans ?_
        gcongr
      _ = 0 + δ := by
        rw [Real.sqrt_sq (by positivity : 0 ≤ δ / 2)]
        norm_num
  · apply le_csInf (Set.range_nonempty (affinity μ ν))
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact affinity_nonneg μ ν n

/-- A finite common submeasure gives a depth-independent lower bound for the
finite-cylinder affinity. -/
theorem commonSubmeasure_mass_le_affinity
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (hξμ : ξ ≤ μ) (hξν : ξ ≤ ν) (m : ℕ) :
    (ξ Set.univ).toReal ≤ affinity μ ν m := by
  rw [← sum_cylinderMass_eq_univ (μ := ξ) m, affinity]
  apply Finset.sum_le_sum
  intro w hw
  have hμ : cylinderMass ξ m w ≤ cylinderMass μ m w := by
    exact ENNReal.toReal_mono (measure_ne_top μ _) (hξμ (cylinder m w))
  have hν : cylinderMass ξ m w ≤ cylinderMass ν m w := by
    exact ENNReal.toReal_mono (measure_ne_top ν _) (hξν (cylinder m w))
  have hsquare : (cylinderMass ξ m w) ^ 2 ≤
      cylinderMass μ m w * cylinderMass ν m w := by
    nlinarith [cylinderMass_nonneg ξ m w, cylinderMass_nonneg μ m w,
      cylinderMass_nonneg ν m w]
  exact Real.le_sqrt_of_sq_le hsquare

/-- Non-mutual-singularity forces a strictly positive affinity limit.  The
common measure is the lattice infimum `μ ⊓ ν`; no generation hypothesis is
needed in this direction. -/
theorem not_mutuallySingular_implies_affinityLimit_pos
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hnonsingular : ¬ μ ⟂ₘ ν) :
    0 < affinityLimit μ ν := by
  let ξ : Measure DecimalShift := μ ⊓ ν
  have hnondisjoint : ¬Disjoint μ ν := by
    rwa [← Measure.mutuallySingular_iff_disjoint]
  have hξne : ξ ≠ 0 := by
    intro hzero
    apply hnondisjoint
    rw [disjoint_iff_inf_le]
    change ξ ≤ ⊥
    rw [hzero]
    rfl
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le μ inf_le_left
  have hmass : 0 < (ξ Set.univ).toReal := by
    exact ENNReal.toReal_pos (Measure.measure_univ_pos.mpr hξne).ne'
      (measure_ne_top ξ _)
  have hlower : (ξ Set.univ).toReal ≤ affinityLimit μ ν := by
    apply le_csInf (Set.range_nonempty (affinity μ ν))
    intro y hy
    obtain ⟨m, rfl⟩ := hy
    exact commonSubmeasure_mass_le_affinity inf_le_left inf_le_right m
  exact hmass.trans_le hlower

/-- Exact all-depth criterion on the one-sided decimal shift.  Generation is
explicit because it is used only for the singular-to-zero direction. -/
theorem positive_affinityLimit_iff_not_mutuallySingular
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hgenerate : GeneratesInMeasure μ ν) :
    0 < affinityLimit μ ν ↔ ¬ μ ⟂ₘ ν := by
  constructor
  · intro hpos hsing
    rw [mutuallySingular_implies_affinityLimit_eq_zero hgenerate hsing] at hpos
    exact lt_irrefl 0 hpos
  · exact not_mutuallySingular_implies_affinityLimit_pos

/-- Equivalent infimum formulation, exposing that the bound ranges over every
depth for one fixed pair of measures. -/
theorem positive_allDepth_inf_iff_not_mutuallySingular
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hgenerate : GeneratesInMeasure μ ν) :
    0 < sInf (Set.range (affinity μ ν)) ↔ ¬ μ ⟂ₘ ν :=
  positive_affinityLimit_iff_not_mutuallySingular hgenerate

/-- Zero affinity limit already forces mutual singularity; generation is only
needed for the converse implication. -/
theorem affinityLimit_eq_zero_implies_mutuallySingular
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hzero : affinityLimit μ ν = 0) : μ ⟂ₘ ν := by
  by_contra hnonsingular
  have hpos := not_mutuallySingular_implies_affinityLimit_pos hnonsingular
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- Equivalent zero-limit formulation of the singularity criterion. -/
theorem affinityLimit_eq_zero_iff_mutuallySingular
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hgenerate : GeneratesInMeasure μ ν) :
    affinityLimit μ ν = 0 ↔ μ ⟂ₘ ν := by
  constructor
  · exact affinityLimit_eq_zero_implies_mutuallySingular
  · exact mutuallySingular_implies_affinityLimit_eq_zero hgenerate

/-- The recursive prefix word read from a one-sided decimal sequence. -/
def prefixWord : (m : ℕ) → DecimalShift → Word m
  | 0, _ => by change Fin 1; exact 0
  | m + 1, x => (prefixWord m x, x m)

theorem mem_cylinder_iff_prefixWord_eq : ∀ (m : ℕ) (w : Word m) (x : DecimalShift),
    x ∈ cylinder m w ↔ prefixWord m x = w
  | 0, w, x => by
      change x ∈ Set.univ ↔ (0 : Fin 1) = w
      exact ⟨fun _ => Fin.ext (by omega), fun _ => Set.mem_univ x⟩
  | m + 1, (w, a), x => by
      simp only [cylinder, Set.mem_inter_iff, Set.mem_setOf_eq, prefixWord,
        mem_cylinder_iff_prefixWord_eq m w x]
      constructor
      · rintro ⟨hw, ha⟩
        exact Prod.ext hw ha
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem prefixWord_congr {x y : DecimalShift} : ∀ {m : ℕ},
    (∀ i : ℕ, i < m → x i = y i) → prefixWord m x = prefixWord m y
  | 0, h => Fin.ext (by omega)
  | m + 1, h => by
      change (prefixWord m x, x m) = (prefixWord m y, y m)
      exact Prod.ext (prefixWord_congr fun i hi => h i (hi.trans (Nat.lt_succ_self m)))
        (h m (Nat.lt_succ_self m))

theorem cylinderMass_dirac (x : DecimalShift) (m : ℕ) (w : Word m) :
    cylinderMass (Measure.dirac x) m w = if prefixWord m x = w then 1 else 0 := by
  unfold cylinderMass
  rw [Measure.dirac_apply' _ (cylinder_measurable m w)]
  by_cases h : x ∈ cylinder m w
  · rw [Set.indicator_of_mem h]
    simp [(mem_cylinder_iff_prefixWord_eq m w x).mp h]
  · rw [Set.indicator_of_notMem h]
    have hp : prefixWord m x ≠ w := fun hp =>
      h ((mem_cylinder_iff_prefixWord_eq m w x).mpr hp)
    simp [hp]

/-- Affinity between two Dirac measures is one exactly while their depth
prefixes agree, and zero otherwise. -/
theorem affinity_dirac_eq_ite (x y : DecimalShift) (m : ℕ) :
    affinity (Measure.dirac x) (Measure.dirac y) m =
      if prefixWord m x = prefixWord m y then 1 else 0 := by
  classical
  unfold affinity
  simp_rw [cylinderMass_dirac]
  by_cases hxy : prefixWord m x = prefixWord m y
  · rw [hxy, if_pos rfl]
    rw [Fintype.sum_eq_single (prefixWord m y)]
    · simp
    · intro w hw
      simp [hw.symm]
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hxw : prefixWord m x = w
    · have hyw : prefixWord m y ≠ w := by
        intro hyw
        exact hxy (hxw.trans hyw.symm)
      simp [hxw, hyw]
    · simp [hxw]

/-- The all-zero decimal sequence. -/
def zeroShift : DecimalShift := fun _ => 0

/-- A sequence agreeing with `zeroShift` through coordinate `N-1` and having
digit one at coordinate `N`. -/
def lateOneShift (N : ℕ) : DecimalShift := fun i => if i = N then 1 else 0

theorem zeroShift_ne_lateOneShift (N : ℕ) : zeroShift ≠ lateOneShift N := by
  intro h
  have hN := congrFun h N
  simp [zeroShift, lateOneShift] at hN

theorem prefixWord_zero_eq_lateOne_of_depth_le {m N : ℕ} (hmN : m ≤ N) :
    prefixWord m zeroShift = prefixWord m (lateOneShift N) := by
  apply prefixWord_congr
  intro i hi
  simp [zeroShift, lateOneShift, ne_of_lt (hi.trans_le hmN)]

theorem prefixWord_zero_ne_lateOne_succ (N : ℕ) :
    prefixWord (N + 1) zeroShift ≠ prefixWord (N + 1) (lateOneShift N) := by
  intro h
  have hlast := congrArg Prod.snd h
  simp [prefixWord, zeroShift, lateOneShift] at hlast

/-- Counterexample 1: every prescribed finite cutoff has a singular pair with
perfect affinity at every tested depth, followed by zero affinity one level
later.  The pair depends on the cutoff. -/
theorem finiteDepth_overlap_counterexample (N : ℕ) :
    (Measure.dirac zeroShift : Measure DecimalShift) ⟂ₘ Measure.dirac (lateOneShift N) ∧
      (∀ m : ℕ, m ≤ N →
        affinity (Measure.dirac zeroShift) (Measure.dirac (lateOneShift N)) m = 1) ∧
      affinity (Measure.dirac zeroShift) (Measure.dirac (lateOneShift N)) (N + 1) = 0 := by
  constructor
  · refine ⟨{zeroShift}ᶜ, (measurableSet_singleton zeroShift).compl, ?_, ?_⟩
    · rw [Measure.dirac_apply' _ (measurableSet_singleton zeroShift).compl]
      simp
    · rw [compl_compl, Measure.dirac_apply' _ (measurableSet_singleton zeroShift)]
      simp [zeroShift_ne_lateOneShift N |>.symm]
  · constructor
    · intro m hm
      rw [affinity_dirac_eq_ite, if_pos (prefixWord_zero_eq_lateOne_of_depth_le hm)]
    · rw [affinity_dirac_eq_ite, if_neg (prefixWord_zero_ne_lateOne_succ N)]

/-- The digit at a coordinate of a recursive word; values outside the word's
depth are irrelevant and are set to zero. -/
def wordAt : (m : ℕ) → Word m → ℕ → Digit
  | 0, _, _ => 0
  | m + 1, (w, a), i => if i = m then a else wordAt m w i

theorem mem_cylinder_iff_wordAt : ∀ (m : ℕ) (w : Word m) (x : DecimalShift),
    x ∈ cylinder m w ↔ ∀ i : ℕ, i < m → x i = wordAt m w i
  | 0, w, x => by simp [cylinder]
  | m + 1, (w, a), x => by
      rw [cylinder, Set.mem_inter_iff, mem_cylinder_iff_wordAt m w x]
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hprefix, hlast⟩ i hi
        by_cases him : i = m
        · subst i
          simpa [wordAt] using hlast
        · have hiless : i < m := by omega
          simpa [wordAt, him] using hprefix i hiless
      · intro hall
        constructor
        · intro i hi
          simpa [wordAt, ne_of_lt hi] using hall i (hi.trans (Nat.lt_succ_self m))
        · simpa [wordAt] using hall m (Nat.lt_succ_self m)

/-- Prefix cylinders are literal finite-coordinate product sets. -/
theorem cylinder_eq_pi (m : ℕ) (w : Word m) :
    cylinder m w = Set.pi (Finset.range m : Set ℕ) (fun i => {wordAt m w i}) := by
  ext x
  rw [mem_cylinder_iff_wordAt]
  simp [Set.mem_pi]

/-- Product of the one-coordinate singleton masses along a recursive word. -/
def wordWeight (law : Measure Digit) : (m : ℕ) → Word m → ℝ
  | 0, _ => 1
  | m + 1, (w, a) => wordWeight law m w * (law {a}).toReal

theorem prod_coordinateMass_eq_wordWeight (law : Measure Digit) :
    ∀ (m : ℕ) (w : Word m),
      ∏ i ∈ Finset.range m, (law {wordAt m w i}).toReal = wordWeight law m w
  | 0, w => by simp [wordWeight]
  | m + 1, (w, a) => by
      rw [Finset.prod_range_succ]
      have hprefix :
          (∏ i ∈ Finset.range m, (law {wordAt (m + 1) (w, a) i}).toReal) =
            ∏ i ∈ Finset.range m, (law {wordAt m w i}).toReal := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [wordAt, if_neg (ne_of_lt (Finset.mem_range.mp hi))]
      rw [hprefix, prod_coordinateMass_eq_wordWeight law m w]
      simp [wordAt, wordWeight]

/-- Exact cylinder mass for an infinite independent product digit law. -/
theorem infinitePi_cylinderMass (law : Measure Digit) [IsProbabilityMeasure law]
    (m : ℕ) (w : Word m) :
    cylinderMass (Measure.infinitePi fun _ : ℕ => law) m w = wordWeight law m w := by
  unfold cylinderMass
  rw [cylinder_eq_pi, Measure.infinitePi_pi]
  · rw [ENNReal.toReal_prod, prod_coordinateMass_eq_wordWeight]
  · intro i hi
    exact measurableSet_singleton _

/-- Fair law on digits zero and one. -/
def fairBinaryLaw : Measure Digit :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

instance fairBinaryLaw_isProbability : IsProbabilityMeasure fairBinaryLaw where
  measure_univ := by
    simp [fairBinaryLaw, Measure.add_apply, Measure.smul_apply]
    calc
      (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ := by ring
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Biased law assigning probabilities `1/4` and `3/4` to digits zero and one. -/
def biasedBinaryLaw : Measure Digit :=
  (4 : ℝ≥0∞)⁻¹ • Measure.dirac 0 +
    ((3 : ℝ≥0∞) / 4) • Measure.dirac 1

instance biasedBinaryLaw_isProbability : IsProbabilityMeasure biasedBinaryLaw where
  measure_univ := by
    simp [biasedBinaryLaw, Measure.add_apply, Measure.smul_apply]
    calc
      (4 : ℝ≥0∞)⁻¹ + 3 / 4 = 4 * (4 : ℝ≥0∞)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- The two Bernoulli product measures used in Counterexample 2. -/
def fairBinaryShift : Measure DecimalShift :=
  Measure.infinitePi fun _ : ℕ => fairBinaryLaw

def biasedBinaryShift : Measure DecimalShift :=
  Measure.infinitePi fun _ : ℕ => biasedBinaryLaw

instance fairBinaryShift_isProbability : IsProbabilityMeasure fairBinaryShift := by
  unfold fairBinaryShift
  infer_instance

instance biasedBinaryShift_isProbability : IsProbabilityMeasure biasedBinaryShift := by
  unfold biasedBinaryShift
  infer_instance

theorem fairBinaryLaw_singleton (a : Digit) :
    (fairBinaryLaw {a}).toReal = if a = 0 ∨ a = 1 then (1 : ℝ) / 2 else 0 := by
  fin_cases a <;>
    simp [fairBinaryLaw, Measure.add_apply, Measure.smul_apply]

theorem biasedBinaryLaw_singleton (a : Digit) :
    (biasedBinaryLaw {a}).toReal =
      if a = 0 then (1 : ℝ) / 4 else if a = 1 then (3 : ℝ) / 4 else 0 := by
  fin_cases a <;>
    simp [biasedBinaryLaw, Measure.add_apply, Measure.smul_apply]

theorem wordWeight_nonneg (law : Measure Digit) :
    ∀ (m : ℕ) (w : Word m), 0 ≤ wordWeight law m w
  | 0, w => by simp [wordWeight]
  | m + 1, (w, a) => mul_nonneg (wordWeight_nonneg law m w) ENNReal.toReal_nonneg

/-- Collision sum of one measure over the complete depth partition. -/
def selfCollision (μ : Measure DecimalShift) (m : ℕ) : ℝ :=
  ∑ w : Word m, cylinderMass μ m w ^ 2

/-- One-coordinate collision factor of a digit law. -/
def lawSelfCollision (law : Measure Digit) : ℝ :=
  ∑ a : Digit, (law {a}).toReal ^ 2

/-- One-coordinate cross-affinity factor of two digit laws. -/
def lawAffinity (law₁ law₂ : Measure Digit) : ℝ :=
  ∑ a : Digit, √((law₁ {a}).toReal * (law₂ {a}).toReal)

/-- Self-collision of an independent product is the corresponding one-digit
collision factor to the depth power. -/
theorem infinitePi_selfCollision_eq_pow
    (law : Measure Digit) [IsProbabilityMeasure law] (m : ℕ) :
    selfCollision (Measure.infinitePi fun _ : ℕ => law) m =
      (lawSelfCollision law) ^ m := by
  induction m with
  | zero => simp [selfCollision, lawSelfCollision, cylinderMass, cylinder, Word]
  | succ m ih =>
      unfold selfCollision
      change (∑ wa : Word m × Digit,
        cylinderMass (Measure.infinitePi fun _ : ℕ => law) (m + 1) wa ^ 2) = _
      rw [Fintype.sum_prod_type]
      simp_rw [infinitePi_cylinderMass, wordWeight, mul_pow]
      rw [← Fintype.sum_mul_sum]
      have hleft : (∑ w : Word m, wordWeight law m w ^ 2) =
          selfCollision (Measure.infinitePi fun _ : ℕ => law) m := by
        unfold selfCollision
        simp_rw [infinitePi_cylinderMass]
      rw [hleft, ih]
      simp [lawSelfCollision, pow_succ]

/-- Cross-affinity of two independent products is the one-digit affinity
factor to the depth power. -/
theorem infinitePi_affinity_eq_pow
    (law₁ law₂ : Measure Digit) [IsProbabilityMeasure law₁]
    [IsProbabilityMeasure law₂] (m : ℕ) :
    affinity (Measure.infinitePi fun _ : ℕ => law₁)
        (Measure.infinitePi fun _ : ℕ => law₂) m =
      (lawAffinity law₁ law₂) ^ m := by
  induction m with
  | zero => simp [affinity, lawAffinity, cylinderMass, cylinder, Word]
  | succ m ih =>
      unfold affinity
      change (∑ wa : Word m × Digit,
        √(cylinderMass (Measure.infinitePi fun _ : ℕ => law₁) (m + 1) wa *
          cylinderMass (Measure.infinitePi fun _ : ℕ => law₂) (m + 1) wa)) = _
      rw [Fintype.sum_prod_type]
      simp_rw [infinitePi_cylinderMass, wordWeight]
      have hfactor (w : Word m) (a : Digit) :
          √((wordWeight law₁ m w * (law₁ {a}).toReal) *
              (wordWeight law₂ m w * (law₂ {a}).toReal)) =
            √(wordWeight law₁ m w * wordWeight law₂ m w) *
              √((law₁ {a}).toReal * (law₂ {a}).toReal) := by
        rw [show (wordWeight law₁ m w * (law₁ {a}).toReal) *
            (wordWeight law₂ m w * (law₂ {a}).toReal) =
            (wordWeight law₁ m w * wordWeight law₂ m w) *
              ((law₁ {a}).toReal * (law₂ {a}).toReal) by ring]
        rw [Real.sqrt_mul (mul_nonneg (wordWeight_nonneg law₁ m w)
          (wordWeight_nonneg law₂ m w))]
      simp_rw [hfactor]
      rw [← Fintype.sum_mul_sum]
      have hleft : (∑ w : Word m,
          √(wordWeight law₁ m w * wordWeight law₂ m w)) =
          affinity (Measure.infinitePi fun _ : ℕ => law₁)
            (Measure.infinitePi fun _ : ℕ => law₂) m := by
        unfold affinity
        simp_rw [infinitePi_cylinderMass]
      rw [hleft, ih]
      simp [lawAffinity, pow_succ]

theorem fairBinaryLaw_selfCollision :
    lawSelfCollision fairBinaryLaw = (1 : ℝ) / 2 := by
  norm_num [lawSelfCollision, fairBinaryLaw_singleton,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem biasedBinaryLaw_selfCollision :
    lawSelfCollision biasedBinaryLaw = (5 : ℝ) / 8 := by
  norm_num [lawSelfCollision, biasedBinaryLaw_singleton,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem binary_lawAffinity_exact :
    lawAffinity fairBinaryLaw biasedBinaryLaw =
      (√(2 : ℝ))⁻¹ * (√(4 : ℝ))⁻¹ +
        (√(2 : ℝ))⁻¹ * (√(3 : ℝ) / √(4 : ℝ)) := by
  simp [lawAffinity, fairBinaryLaw_singleton, biasedBinaryLaw_singleton,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem binary_lawAffinity_pos :
    0 < lawAffinity fairBinaryLaw biasedBinaryLaw := by
  rw [binary_lawAffinity_exact]
  positivity

theorem binary_lawAffinity_lt_one :
    lawAffinity fairBinaryLaw biasedBinaryLaw < 1 := by
  rw [binary_lawAffinity_exact]
  let a := (√(2 : ℝ))⁻¹ * (√(4 : ℝ))⁻¹
  let b := (√(2 : ℝ))⁻¹ * (√(3 : ℝ) / √(4 : ℝ))
  have hs2 : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hs3 : (√(3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by positivity)
  have hs4 : (√(4 : ℝ)) ^ 2 = 4 := Real.sq_sqrt (by positivity)
  have ha : a ^ 2 = (1 : ℝ) / 8 := by
    dsimp [a]
    rw [mul_pow, inv_pow, hs2, inv_pow, hs4]
    norm_num
  have hb : b ^ 2 = (3 : ℝ) / 8 := by
    dsimp [b]
    rw [mul_pow, inv_pow, hs2, div_pow, hs3, hs4]
    norm_num
  have ha0 : 0 ≤ a := mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hb0 : 0 ≤ b := mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have habsq : (a * b) ^ 2 = (3 : ℝ) / 64 := by
    rw [mul_pow, ha, hb]
    ring
  have hablt : a * b < (1 : ℝ) / 4 := by
    nlinarith
  change a + b < 1
  nlinarith

/-- Counterexample 2: both measures have exponential self-collision decay,
but their positive finite-depth cross-affinities tend to zero and the measures
are mutually singular.  This refutes any inference from separate T27-type
self-collision control to a uniform cross-affinity bound. -/
theorem selfCollision_does_not_imply_crossAffinity :
    (∀ m : ℕ, selfCollision fairBinaryShift m = ((1 : ℝ) / 2) ^ m) ∧
      (∀ m : ℕ, selfCollision biasedBinaryShift m = ((5 : ℝ) / 8) ^ m) ∧
      (∀ m : ℕ, affinity fairBinaryShift biasedBinaryShift m =
        (lawAffinity fairBinaryLaw biasedBinaryLaw) ^ m) ∧
      0 < lawAffinity fairBinaryLaw biasedBinaryLaw ∧
      lawAffinity fairBinaryLaw biasedBinaryLaw < 1 ∧
      (∀ m : ℕ, 0 < affinity fairBinaryShift biasedBinaryShift m) ∧
      Tendsto (affinity fairBinaryShift biasedBinaryShift) atTop (𝓝 0) ∧
      fairBinaryShift ⟂ₘ biasedBinaryShift := by
  refine ⟨?_, ?_, ?_, binary_lawAffinity_pos, binary_lawAffinity_lt_one, ?_, ?_, ?_⟩
  · intro m
    rw [fairBinaryShift, infinitePi_selfCollision_eq_pow, fairBinaryLaw_selfCollision]
  · intro m
    rw [biasedBinaryShift, infinitePi_selfCollision_eq_pow, biasedBinaryLaw_selfCollision]
  · intro m
    rw [fairBinaryShift, biasedBinaryShift, infinitePi_affinity_eq_pow]
  · intro m
    rw [fairBinaryShift, biasedBinaryShift, infinitePi_affinity_eq_pow]
    exact pow_pos binary_lawAffinity_pos m
  · rw [show affinity fairBinaryShift biasedBinaryShift = fun m =>
        (lawAffinity fairBinaryLaw biasedBinaryLaw) ^ m by
      funext m
      rw [fairBinaryShift, biasedBinaryShift, infinitePi_affinity_eq_pow]]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one binary_lawAffinity_pos.le
      binary_lawAffinity_lt_one
  · apply affinityLimit_eq_zero_implies_mutuallySingular
    apply tendsto_nhds_unique (affinity_tendsto_limit (μ := fairBinaryShift)
      (ν := biasedBinaryShift))
    rw [show affinity fairBinaryShift biasedBinaryShift = fun m =>
        (lawAffinity fairBinaryLaw biasedBinaryLaw) ^ m by
      funext m
      rw [fairBinaryShift, biasedBinaryShift, infinitePi_affinity_eq_pow]]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one binary_lawAffinity_pos.le
      binary_lawAffinity_lt_one

/-- Boundary-safe fixed-depth convergence.  For symbolic measures this is the
exact conclusion supplied by a weak-limit argument after proving that every
relevant decimal-cell boundary has limiting mass zero. -/
def BoundarySafeCylinderConvergence
    (μs νs : ℕ → Measure DecimalShift) (μ ν : Measure DecimalShift) : Prop :=
  ∀ m : ℕ, ∀ w : Word m,
    Tendsto (fun n => cylinderMass (μs n) m w) atTop (𝓝 (cylinderMass μ m w)) ∧
      Tendsto (fun n => cylinderMass (νs n) m w) atTop (𝓝 (cylinderMass ν m w))

/-- Explicit boundary-safe cylinder convergence transfers affinity at each
fixed depth.  No growing-depth interchange is hidden in this statement. -/
theorem affinity_tendsto_of_boundarySafe
    (μs νs : ℕ → Measure DecimalShift) (μ ν : Measure DecimalShift)
    (hboundary : BoundarySafeCylinderConvergence μs νs μ ν) (m : ℕ) :
    Tendsto (fun n => affinity (μs n) (νs n) m) atTop (𝓝 (affinity μ ν m)) := by
  unfold affinity
  apply tendsto_finsetSum
  intro w hw
  exact ((hboundary m w).1.mul (hboundary m w).2).sqrt

/-- Prefix cylinders are clopen in the product topology on the symbolic shift. -/
theorem cylinder_isClopen : ∀ (m : ℕ) (w : Word m), IsClopen (cylinder m w)
  | 0, w => isClopen_univ
  | m + 1, (w, a) => by
      have ha : IsClopen ({a} : Set Digit) := ⟨isClosed_discrete _, isOpen_discrete _⟩
      exact (cylinder_isClopen m w).inter
        (by
          change IsClopen ((fun x : DecimalShift => x m) ⁻¹' {a})
          exact ha.preimage (continuous_apply m))

/-- Explicit all-depth boundary-null hypothesis for a limiting symbolic
probability measure.  It is automatic for intrinsic shift cylinders, but is
kept as a premise in the Portmanteau transfer theorem so a circle coding must
discharge it rather than silently ignore decimal endpoints. -/
def BoundaryNullAtAllDepths (μ : ProbabilityMeasure DecimalShift) : Prop :=
  ∀ m : ℕ, ∀ w : Word m,
    (μ : Measure DecimalShift) (frontier (cylinder m w)) = 0

theorem intrinsic_cylinders_boundaryNull (μ : ProbabilityMeasure DecimalShift) :
    BoundaryNullAtAllDepths μ := by
  intro m w
  simp [cylinder_isClopen m w]

/-- Weak convergence plus the displayed boundary hypotheses implies the exact
fixed-depth real cylinder-mass convergence used above. -/
theorem boundarySafeCylinderConvergence_of_weakLimits
    (μs νs : ℕ → ProbabilityMeasure DecimalShift)
    (μ ν : ProbabilityMeasure DecimalShift)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hμboundary : BoundaryNullAtAllDepths μ)
    (hνboundary : BoundaryNullAtAllDepths ν) :
    BoundarySafeCylinderConvergence
      (fun n => (μs n : Measure DecimalShift))
      (fun n => (νs n : Measure DecimalShift)) μ ν := by
  intro m w
  constructor
  · have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hμ (hμboundary m w)
    exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure DecimalShift) _)).comp hmass
  · have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hν (hνboundary m w)
    exact (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure DecimalShift) _)).comp hmass

end DecimalFactorEntropy.CylinderAffinity

#print axioms DecimalFactorEntropy.CylinderAffinity.cylinder_pairwise_disjoint
#print axioms DecimalFactorEntropy.CylinderAffinity.iUnion_cylinder
#print axioms DecimalFactorEntropy.CylinderAffinity.cylinder_eq_iUnion_children
#print axioms DecimalFactorEntropy.CylinderAffinity.affinity_antitone
#print axioms DecimalFactorEntropy.CylinderAffinity.affinity_tendsto_limit
#print axioms DecimalFactorEntropy.CylinderAffinity.mutuallySingular_implies_affinityLimit_eq_zero
#print axioms DecimalFactorEntropy.CylinderAffinity.not_mutuallySingular_implies_affinityLimit_pos
#print axioms DecimalFactorEntropy.CylinderAffinity.positive_allDepth_inf_iff_not_mutuallySingular
#print axioms DecimalFactorEntropy.CylinderAffinity.affinityLimit_eq_zero_iff_mutuallySingular
#print axioms DecimalFactorEntropy.CylinderAffinity.finiteDepth_overlap_counterexample
#print axioms DecimalFactorEntropy.CylinderAffinity.infinitePi_selfCollision_eq_pow
#print axioms DecimalFactorEntropy.CylinderAffinity.infinitePi_affinity_eq_pow
#print axioms DecimalFactorEntropy.CylinderAffinity.selfCollision_does_not_imply_crossAffinity
#print axioms DecimalFactorEntropy.CylinderAffinity.affinity_tendsto_of_boundarySafe
#print axioms DecimalFactorEntropy.CylinderAffinity.boundarySafeCylinderConvergence_of_weakLimits
