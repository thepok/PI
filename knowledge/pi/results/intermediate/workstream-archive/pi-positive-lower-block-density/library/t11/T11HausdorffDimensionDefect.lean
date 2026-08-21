import TheoryLib.PiPositiveLowerBlockDensity.T8T8AlignedEntropyDeficit
import TheoryLib.PiPositiveLowerBlockDensity.T10T10HaarSingularCluster
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# T11: Hausdorff-dimension defect forced by failure of C1

Source: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a necessary consequence of the literal negation of
canonical C1, together with a conditional implication to C1. It makes no
unconditional assertion about the decimal digits of pi.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace Theory.PiDigits.PositiveLowerBlockDensity.T11

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T10

/-- The scale of a length-`n` decimal cylinder, written as `10⁻ⁿ`. -/
def decimalScale (n : ℕ) : ℝ := ((10 : ℝ) ^ n)⁻¹

/-- Two points in the same boundary-safe decimal cylinder are at most one
decimal scale apart. -/
theorem dist_le_decimalScale_of_mem {n : ℕ} {a : Fin (10 ^ n)}
    {x y : UnitAddCircle} (hx : x ∈ decimalCylinder n a)
    (hy : y ∈ decimalCylinder n a) :
    dist x y ≤ decimalScale n := by
  rw [mem_decimalCylinder_iff] at hx hy
  have hwidth :
      (((a : ℕ) + 1 : ℝ) / (10 : ℝ) ^ n) -
          (a : ℕ) / (10 : ℝ) ^ n = decimalScale n := by
    unfold decimalScale
    have hpow : (10 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  rw [← coe_unitCoordinate x, ← coe_unitCoordinate y, dist_eq_norm,
    ← QuotientAddGroup.mk_sub]
  refine QuotientAddGroup.norm_mk_le_norm.trans ?_
  change |unitCoordinate x - unitCoordinate y| ≤ decimalScale n
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, hwidth]

/-- Boundary-safe decimal cylinders have diameter at most their decimal
scale. -/
theorem decimalCylinder_diam_le (n : ℕ) (a : Fin (10 ^ n)) :
    Metric.diam (decimalCylinder n a) ≤ decimalScale n := by
  apply Metric.diam_le_of_forall_dist_le (by unfold decimalScale; positivity)
  intro x hx y hy
  exact dist_le_decimalScale_of_mem hx hy

/-- Extended-diameter form of `decimalCylinder_diam_le`, used by mathlib's
Hausdorff-cover API. -/
theorem decimalCylinder_ediam_le (n : ℕ) (a : Fin (10 ^ n)) :
    Metric.ediam (decimalCylinder n a) ≤ ENNReal.ofReal (decimalScale n) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  exact dist_le_decimalScale_of_mem hx hy

/-- The ordinary decimal-cylinder indices corresponding to the positive-mass
aligned atoms. -/
def positiveDecimalIndices (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) :
    Finset (Fin (10 ^ (m * k))) := by
  classical
  letI : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  exact Finset.univ.image fun c : PositiveAlignedAtom ν k m =>
    alignedIndexEquiv k m c.1

/-- T8's atom count becomes a count of ordinary decimal intervals. -/
theorem positiveDecimalIndices_card_le
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0)
    (m : ℕ) :
    (positiveDecimalIndices ν k m).card ≤ (10 ^ k - 1) ^ m := by
  classical
  letI : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  calc
    (positiveDecimalIndices ν k m).card ≤
        (Finset.univ : Finset (PositiveAlignedAtom ν k m)).card := by
      unfold positiveDecimalIndices
      exact Finset.card_image_le
    _ = Nat.card (PositiveAlignedAtom ν k m) := by
      rw [Nat.card_eq_fintype_card]
      simp
    _ ≤ (10 ^ k - 1) ^ m :=
      positive_mass_atom_count ν hinvariant a hzero m

/-- The full-mass intersection from T10 is covered, at every level, by the
ordinary decimal intervals indexed by `positiveDecimalIndices`. -/
theorem fullMassIntersection_subset_decimalCover
    (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ) :
    fullMassHaarNullIntersection ν k ⊆
      ⋃ a ∈ positiveDecimalIndices ν k m, decimalCylinder (m * k) a := by
  classical
  intro x hx
  have hxm : x ∈ positiveAlignedCylinderUnion ν k m :=
    Set.mem_iInter.mp hx m
  obtain ⟨c, hc, hxc⟩ :=
    (mem_positiveAlignedCylinderUnion_iff ν k m x).mp hxm
  have ha : alignedIndexEquiv k m c ∈ positiveDecimalIndices ν k m := by
    unfold positiveDecimalIndices
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨c, hc⟩, rfl⟩
  apply Set.mem_iUnion.2
  refine ⟨alignedIndexEquiv k m c, Set.mem_iUnion.2 ⟨ha, ?_⟩⟩
  rw [← alignedDecimalCylinder_eq_decimalCylinder]
  exact hxc

/-- Every interval in the level-`m` decimal cover has diameter at most
`10⁻(m*k)`. -/
theorem positiveDecimalIndices_diam_le
    (ν : ProbabilityMeasure UnitAddCircle) (k m : ℕ)
    (a : Fin (10 ^ (m * k))) (_ha : a ∈ positiveDecimalIndices ν k m) :
    Metric.diam (decimalCylinder (m * k) a) ≤ decimalScale (m * k) := by
  exact decimalCylinder_diam_le (m * k) a

/-- The critical dimension associated to forbidding one of the `10^k`
length-`k` decimal words. -/
def criticalDimension (k : ℕ) : ℝ :=
  Real.log (10 ^ k - 1 : ℕ) / ((k : ℝ) * Real.log 10)

/-- The critical dimension is nonnegative for nonempty blocks. -/
theorem criticalDimension_nonneg {k : ℕ} (hk : 0 < k) :
    0 ≤ criticalDimension k := by
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
  have hA : 1 ≤ 10 ^ k - 1 := by omega
  unfold criticalDimension
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hA))
    (mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num)))

/-- The critical dimension is strictly below one for nonempty blocks. -/
theorem criticalDimension_lt_one {k : ℕ} (hk : 0 < k) :
    criticalDimension k < 1 := by
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
  have hA : 0 < 10 ^ k - 1 := by omega
  have hpowpos : 0 < 10 ^ k := pow_pos (by norm_num) k
  have hlt : 10 ^ k - 1 < 10 ^ k := Nat.sub_lt hpowpos (by norm_num)
  have hloglt : Real.log (10 ^ k - 1 : ℕ) < Real.log (10 ^ k : ℕ) := by
    apply Real.strictMonoOn_log
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hA)
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hpowpos)
    · exact_mod_cast hlt
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlogten : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold criticalDimension
  rw [div_lt_one (mul_pos hkreal hlogten)]
  rw [Nat.cast_pow, Real.log_pow] at hloglt
  simpa using hloglt

/-- A reusable cover-to-dimension theorem specialized to one missing decimal
cylinder of an invariant measure. -/
theorem fullMassIntersection_dimH_le
    (ν : ProbabilityMeasure UnitAddCircle) (hinvariant : timesTenMap ν = ν)
    {k : ℕ} (hk : 0 < k) (a : Fin (10 ^ k))
    (hzero : (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0) :
    dimH (fullMassHaarNullIntersection ν k) ≤
      ENNReal.ofReal (criticalDimension k) := by
  classical
  let A : ℕ := 10 ^ k - 1
  let B : ℕ := 10 ^ k
  have hpow : 10 ≤ 10 ^ k := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (10 : ℕ)) hk
  have hA : 0 < A := by dsimp [A]; omega
  have hA1 : 1 ≤ A := hA
  have hB1 : 1 < B := by dsimp [B]; omega
  let d : ℝ≥0 := ⟨criticalDimension k, criticalDimension_nonneg hk⟩
  have hd_real :
      (d : ℝ) = Real.log (A : ℝ) / Real.log (B : ℝ) := by
    change criticalDimension k = _
    dsimp [A, B]
    unfold criticalDimension
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hscale (m : ℕ) :
      ENNReal.ofReal (decimalScale (m * k)) =
        (B : ENNReal)⁻¹ ^ m := by
    simp [decimalScale, B, ENNReal.ofReal_inv_of_pos, Nat.mul_comm]
    rw [← ENNReal.inv_pow, ← pow_mul]
  have hBpow : (B : ENNReal) ^ (d : ℝ) = (A : ENNReal) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
      (ENNReal.rpow_ne_top_of_nonneg d.coe_nonneg
        (ENNReal.natCast_ne_top B))
      (ENNReal.natCast_ne_top A)]
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, hd_real, Real.log_div_log]
    exact Real.rpow_logb
      (by exact_mod_cast zero_lt_one.trans hB1)
      (by exact_mod_cast hB1.ne')
      (by exact_mod_cast hA)
  have hunit :
      (A : ENNReal) * ((B : ENNReal)⁻¹ ^ (d : ℝ)) = 1 := by
    rw [ENNReal.inv_rpow, hBpow]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast hA.ne') (ENNReal.natCast_ne_top A)
  have hcomm (m : ℕ) :
      (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) =
        (((B : ENNReal)⁻¹ ^ (d : ℝ)) ^ m) := by
    calc
      (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) =
          (B : ENNReal)⁻¹ ^ ((m : ℝ) * (d : ℝ)) :=
        (ENNReal.rpow_natCast_mul _ m (d : ℝ)).symm
      _ = (B : ENNReal)⁻¹ ^ ((d : ℝ) * (m : ℝ)) := by rw [mul_comm]
      _ = (((B : ENNReal)⁻¹ ^ (d : ℝ)) ^ m) :=
        ENNReal.rpow_mul_natCast _ (d : ℝ) m
  have hcriticalPower (m : ℕ) :
      ((A ^ m : ℕ) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) = 1 := by
    rw [Nat.cast_pow, hcomm, ← mul_pow, hunit, one_pow]
  letI (m : ℕ) : Fintype (PositiveAlignedAtom ν k m) := by
    unfold PositiveAlignedAtom
    infer_instance
  let t : (m : ℕ) → PositiveAlignedAtom ν k m → Set UnitAddCircle :=
    fun m c => alignedDecimalCylinder k m c.1
  let r : ℕ → ENNReal := fun m => (B : ENNReal)⁻¹ ^ m
  have hr : Tendsto r atTop (nhds 0) := by
    apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    exact ENNReal.inv_lt_one.mpr (by exact_mod_cast hB1)
  have hdiam (m : ℕ) (c : PositiveAlignedAtom ν k m) :
      Metric.ediam (t m c) ≤ r m := by
    dsimp only [t, r]
    rw [alignedDecimalCylinder_eq_decimalCylinder]
    exact (decimalCylinder_ediam_le (m * k) (alignedIndexEquiv k m c.1)).trans_eq
      (hscale m)
  have hcover (m : ℕ) :
      fullMassHaarNullIntersection ν k ⊆ ⋃ c, t m c := by
    intro x hx
    have hxm : x ∈ positiveAlignedCylinderUnion ν k m :=
      Set.mem_iInter.mp hx m
    simpa only [t, positiveAlignedCylinderUnion] using hxm
  have hcount (m : ℕ) :
      Nat.card (PositiveAlignedAtom ν k m) ≤ A ^ m := by
    simpa only [A] using positive_mass_atom_count ν hinvariant a hzero m
  have hsum (m : ℕ) :
      ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ) ≤ (1 : ENNReal) := by
    calc
      ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ) ≤
          ∑ _c : PositiveAlignedAtom ν k m,
            ((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ) :=
        Finset.sum_le_sum fun c _ =>
          ENNReal.rpow_le_rpow (hdiam m c) d.coe_nonneg
      _ = (Nat.card (PositiveAlignedAtom ν k m) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) := by
        rw [Nat.card_eq_fintype_card, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((A ^ m : ℕ) : ENNReal) *
          (((B : ENNReal)⁻¹ ^ m) ^ (d : ℝ)) := by
        gcongr
        exact_mod_cast hcount m
      _ = 1 := hcriticalPower m
  have hμ := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (d : ℝ) (fullMassHaarNullIntersection ν k) r hr t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  have hlim :
      liminf (fun m => ∑ c : PositiveAlignedAtom ν k m,
        Metric.ediam (t m c) ^ (d : ℝ)) atTop ≤ (1 : ENNReal) := by
    calc
      liminf (fun m => ∑ c : PositiveAlignedAtom ν k m,
          Metric.ediam (t m c) ^ (d : ℝ)) atTop ≤
          liminf (fun _m : ℕ => (1 : ENNReal)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hsum)
      _ = 1 := Filter.liminf_const 1
  have hdim : dimH (fullMassHaarNullIntersection ν k) ≤ (d : ENNReal) := by
    apply dimH_le_of_hausdorffMeasure_ne_top
    exact ((hμ.trans hlim).trans_lt ENNReal.one_lt_top).ne
  calc
    dimH (fullMassHaarNullIntersection ν k) ≤ (d : ENNReal) := hdim
    _ = ENNReal.ofReal (criticalDimension k) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl

/-- Necessary-only T11 conclusion. Literal failure of canonical C1 yields an
invariant pi empirical cluster carried by a measurable set with the displayed
all-level decimal covers and a strict Hausdorff-dimension defect. -/
theorem not_piPositiveLowerBlockDensity_implies_hausdorffDimension_defect
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ ell : ℕ, 1 ≤ ell ∧ ∃ E : Set UnitAddCircle,
        MeasurableSet E ∧ (ν : Measure UnitAddCircle) E = 1 ∧
        (∀ m : ℕ, 1 ≤ m →
          ∃ C : Finset (Fin (10 ^ (m * ell))),
            C.card ≤ (10 ^ ell - 1) ^ m ∧
            E ⊆ ⋃ a ∈ C, decimalCylinder (m * ell) a ∧
            ∀ a ∈ C,
              Metric.diam (decimalCylinder (m * ell) a) ≤
                ((10 : ℝ) ^ (m * ell))⁻¹) ∧
        dimH E ≤ ENNReal.ofReal
          (Real.log (10 ^ ell - 1 : ℕ) / ((ell : ℝ) * Real.log 10)) ∧
        Real.log (10 ^ ell - 1 : ℕ) / ((ell : ℝ) * Real.log 10) < 1 ∧
        dimH E < 1 := by
  obtain ⟨ν, hcluster, hinvariant, v, hvpos, hzero, hcount,
      hentropy, hrate⟩ :=
    T8.not_piPositiveLowerBlockDensity_implies_aligned_entropy_deficit hnot
  let E := fullMassHaarNullIntersection ν v.length
  have hEmeas : MeasurableSet E :=
    fullMassHaarNullIntersection_measurable ν v.length
  have hEfull : (ν : Measure UnitAddCircle) E = 1 :=
    fullMassHaarNullIntersection_full_measure ν v.length
  have hdim : dimH E ≤ ENNReal.ofReal (criticalDimension v.length) :=
    fullMassIntersection_dimH_le ν hinvariant hvpos (wordIndex v) hzero
  have hcritical : criticalDimension v.length < 1 :=
    criticalDimension_lt_one hvpos
  have hdimExplicit : dimH E ≤ ENNReal.ofReal
      (Real.log (10 ^ v.length - 1 : ℕ) /
        ((v.length : ℝ) * Real.log 10)) := by
    simpa [criticalDimension] using hdim
  have hcriticalExplicit :
      Real.log (10 ^ v.length - 1 : ℕ) /
          ((v.length : ℝ) * Real.log 10) < 1 := by
    simpa [criticalDimension] using hcritical
  have hdimlt : dimH E < 1 :=
    hdim.trans_lt (ENNReal.ofReal_lt_one.mpr hcritical)
  refine ⟨ν, hcluster, hinvariant, v.length, hvpos, E, hEmeas, hEfull,
    ?_, hdimExplicit, hcriticalExplicit, hdimlt⟩
  intro m _hm
  refine ⟨positiveDecimalIndices ν v.length m,
    positiveDecimalIndices_card_le ν hinvariant (wordIndex v) hzero m,
    fullMassIntersection_subset_decimalCover ν v.length m, ?_⟩
  intro a ha
  simpa [decimalScale] using
    positiveDecimalIndices_diam_le ν v.length m a ha

/-- Conditional implication to C1. If every pi empirical cluster gives zero
mass to every set of Hausdorff dimension below one, then canonical C1 holds. -/
theorem piPositiveLowerBlockDensity_of_clusters_zero_on_dimH_lt_one
    (hregular : ∀ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure →
      ∀ E : Set UnitAddCircle, dimH E < 1 →
        (ν : Measure UnitAddCircle) E = 0) :
    PiPositiveLowerBlockDensity := by
  by_contra hnot
  obtain ⟨ν, hcluster, hinvariant, ell, hell, E, hEmeas, hEfull,
      hcovers, hdim, hcritical, hdimlt⟩ :=
    not_piPositiveLowerBlockDensity_implies_hausdorffDimension_defect hnot
  have hzero := hregular ν hcluster E hdimlt
  rw [hEfull] at hzero
  exact one_ne_zero hzero

end Theory.PiDigits.PositiveLowerBlockDensity.T11

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.decimalCylinder_diam_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.positiveDecimalIndices_card_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.fullMassIntersection_subset_decimalCover
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.criticalDimension_lt_one
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.fullMassIntersection_dimH_le
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.not_piPositiveLowerBlockDensity_implies_hausdorffDimension_defect
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T11.piPositiveLowerBlockDensity_of_clusters_zero_on_dimH_lt_one
