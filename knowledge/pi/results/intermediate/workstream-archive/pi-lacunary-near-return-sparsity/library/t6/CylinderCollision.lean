import TheoryLib.PiLacunaryNearReturnSparsity.T4ClusterNearReturns
import TheoryLib.PiLacunaryNearReturnSparsity.T2NormalOrbitNearReturns
import TheoryLib.PiPositiveLowerBlockDensity.T11T11HausdorffDimensionDefect

/-!
# Decimal-cylinder collision energy and circular small balls

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module gives conditional criteria only. In particular, it does not assert
any cylinder-energy or small-ball decay for the decimal orbit of `Real.pi`.
All pair counts inherited from T4 are ordered and include the diagonal.
-/

noncomputable section

open Filter Finset Set Topology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

namespace DecimalFactorComplexity.CylinderCollision

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.PositiveLowerBlockDensity.T11

/-- Closed circle distance at one cell width forces half-open cell labels to
be equal or cyclically adjacent. The strict upper endpoints are exactly what
exclude a two-cell jump when the metric inequality is closed. -/
theorem dist_le_inv_of_mem_Ico_implies_cyclicAdjacent
    {q a b : ℕ} {x y : ℝ} (hq : 0 < q) (ha : a < q) (hb : b < q)
    (hx : x ∈ Set.Ico ((a : ℝ) / q) (((a + 1 : ℕ) : ℝ) / q))
    (hy : y ∈ Set.Ico ((b : ℝ) / q) (((b + 1 : ℕ) : ℝ) / q))
    (hnear : dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ (q : ℝ)⁻¹) :
    CyclicAdjacent q a b := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwidth : (q : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ hqR).2 (by exact_mod_cast hq)
  have hqinv : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hqR.ne'
  have hx0 : 0 ≤ x :=
    (div_nonneg (by positivity) hqR.le).trans hx.1
  have hy0 : 0 ≤ y :=
    (div_nonneg (by positivity) hqR.le).trans hy.1
  have hx1 : x < 1 := by
    refine hx.2.trans_le ?_
    exact (div_le_one hqR).2 (by exact_mod_cast (Nat.succ_le_iff.mpr ha))
  have hy1 : y < 1 := by
    refine hy.2.trans_le ?_
    exact (div_le_one hqR).2 (by exact_mod_cast (Nat.succ_le_iff.mpr hb))
  have hmem : x ∈ ((fun t : ℝ => (t : UnitAddCircle)) ⁻¹'
      Metric.closedBall (y : UnitAddCircle) ((q : ℝ)⁻¹)) := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall] using hnear
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨z : ℤ, hz⟩ := hmem
  have hzabs : |x - (y + (z : ℝ))| ≤ (q : ℝ)⁻¹ := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one] using hz
  rw [abs_le] at hzabs
  have hzlower : -(q : ℝ)⁻¹ ≤ x - (y + (z : ℝ)) := by linarith
  have hzupper : x - (y + (z : ℝ)) ≤ (q : ℝ)⁻¹ := by linarith
  have hzloR : (-2 : ℝ) < (z : ℝ) := by linarith
  have hzhiR : (z : ℝ) < 2 := by linarith
  have hzlo : (-2 : ℤ) < z := by exact_mod_cast hzloR
  have hzhi : z < (2 : ℤ) := by exact_mod_cast hzhiR
  have hzcase : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  have hxa : (a : ℝ) ≤ q * x := by
    have := (div_le_iff₀ hqR).mp hx.1
    nlinarith
  have hxa1 : q * x < (a + 1 : ℕ) := by
    have := (lt_div_iff₀ hqR).mp hx.2
    push_cast at this ⊢
    nlinarith
  have hyb : (b : ℝ) ≤ q * y := by
    have := (div_le_iff₀ hqR).mp hy.1
    nlinarith
  have hyb1 : q * y < (b + 1 : ℕ) := by
    have := (lt_div_iff₀ hqR).mp hy.2
    push_cast at this ⊢
    nlinarith
  push_cast at hxa hxa1 hyb hyb1
  rcases hzcase with rfl | rfl | rfl
  · norm_num at hzabs hzlower hzupper
    have hmetric : (q : ℝ) * x - q * y + q ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hzupper hqR.le
      nlinarith
    have hscaled : (q : ℝ) + a < b + 2 := by
      linarith
    have hscaledNat : q + a < b + 2 := by exact_mod_cast hscaled
    unfold CyclicAdjacent
    omega
  · norm_num at hzabs hzlower hzupper
    have hxy : (q : ℝ) * x - q * y ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hzupper hqR.le
      nlinarith
    have hyx : (q : ℝ) * y - q * x ≤ 1 := by
      calc
        (q : ℝ) * y - q * x = -q * (x - (y + (0 : ℝ))) := by ring
        _ ≤ q * (q : ℝ)⁻¹ := by
          nlinarith [mul_le_mul_of_nonneg_left hzlower hqR.le]
        _ = 1 := hqinv
    have habR : (a : ℝ) < b + 2 := by linarith
    have hbaR : (b : ℝ) < a + 2 := by linarith
    have hab : a < b + 2 := by exact_mod_cast habR
    have hba : b < a + 2 := by exact_mod_cast hbaR
    unfold CyclicAdjacent
    omega
  · norm_num at hzabs hzlower hzupper
    have hmetric : (q : ℝ) * y - q * x + q ≤ 1 := by
      calc
        (q : ℝ) * y - q * x + q = -q * (x - (y + (1 : ℝ))) := by ring
        _ ≤ q * (q : ℝ)⁻¹ := by
          nlinarith [mul_le_mul_of_nonneg_left hzlower hqR.le]
        _ = 1 := hqinv
    have hscaled : (q : ℝ) + b < a + 2 := by
      linarith
    have hscaledNat : q + b < a + 2 := by exact_mod_cast hscaled
    unfold CyclicAdjacent
    omega

/-- Closed small-ball pairs have equal or cyclically adjacent decimal codes.
This includes the wraparound pairs with codes `0` and `10^n-1`. -/
theorem closedDiagonal_implies_decimalCodes_cyclicAdjacent
    (n : ℕ) {x y : UnitAddCircle}
    (hxy : (x, y) ∈ closedDiagonal (decimalRadius n)) :
    CyclicAdjacent (10 ^ n) (decimalCode n x) (decimalCode n y) := by
  apply dist_le_inv_of_mem_Ico_implies_cyclicAdjacent
      (q := 10 ^ n) (a := decimalCode n x) (b := decimalCode n y)
      (x := unitCoordinate x) (y := unitCoordinate y)
      (by positivity) (decimalCode n x).isLt (decimalCode n y).isLt
  · have hx := (mem_decimalCylinder_iff n (decimalCode n x) x).mp rfl
    convert hx using 1 <;> norm_cast
  · have hy := (mem_decimalCylinder_iff n (decimalCode n y) y).mp rfl
    convert hy using 1 <;> norm_cast
  · rw [coe_unitCoordinate, coe_unitCoordinate]
    simpa only [closedDiagonal, decimalRadius, Set.mem_setOf_eq,
      Nat.cast_pow, Nat.cast_ofNat] using hxy

/-- The real mass of a half-open decimal cylinder. -/
def cylinderMass (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ)
    (a : Fin (10 ^ n)) : ℝ :=
  ((ν : Measure UnitAddCircle) (decimalCylinder n a)).toReal

/-- Collision energy of the `10^n` half-open decimal cylinders. -/
def cylinderCollisionEnergy (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ) : ℝ :=
  ∑ a : Fin (10 ^ n), cylinderMass ν n a ^ 2

/-- The cyclic adjacency relation is the union of the identity, successor,
and predecessor permutation graphs. -/
theorem cyclicAdjacent_three_cases {q : ℕ} (hq : 0 < q) (a b : Fin q)
    (hab : CyclicAdjacent q a b) :
    b = a ∨ b = finRotate q a ∨ b = (finRotate q).symm a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  unfold CyclicAdjacent at hab
  rcases hab with hsame | hpred | hsucc | hwrapPred | hwrapSucc
  · exact Or.inl (Fin.ext hsame)
  · right; right
    apply (finRotate (k + 1)).eq_symm_apply.mpr
    apply Fin.ext
    rw [coe_finRotate]
    split_ifs with hbLast
    · have hbval : b.val = k := by
        simpa using congrArg Fin.val hbLast
      omega
    · have hbval : b.val ≠ k := by
        intro h
        apply hbLast
        apply Fin.ext
        simpa using h
      omega
  · right; left
    apply Fin.ext
    rw [coe_finRotate]
    split_ifs with haLast
    · have haval : a.val = k := by
        simpa using congrArg Fin.val haLast
      omega
    · have haval : a.val ≠ k := by
        intro h
        apply haLast
        apply Fin.ext
        simpa using h
      omega
  · right; right
    apply (finRotate (k + 1)).eq_symm_apply.mpr
    apply Fin.ext
    rw [coe_finRotate]
    split_ifs with hbLast
    · have hbval : b.val = k := by
        simpa using congrArg Fin.val hbLast
      omega
    · have hbval : b.val ≠ k := by
        intro h
        apply hbLast
        apply Fin.ext
        simpa using h
      omega
  · right; left
    apply Fin.ext
    rw [coe_finRotate]
    split_ifs with haLast
    · have haval : a.val = k := by
        simpa using congrArg Fin.val haLast
      omega
    · have haval : a.val ≠ k := by
        intro h
        apply haLast
        apply Fin.ext
        simpa using h
      omega

/-- Pairs whose second decimal code is obtained from the first by `e`. -/
def codeGraph (n : ℕ) (e : Equiv.Perm (Fin (10 ^ n))) :
    Set (UnitAddCircle × UnitAddCircle) :=
  ⋃ a : Fin (10 ^ n), decimalCylinder n a ×ˢ decimalCylinder n (e a)

theorem mem_codeGraph_iff (n : ℕ) (e : Equiv.Perm (Fin (10 ^ n)))
    (xy : UnitAddCircle × UnitAddCircle) :
    xy ∈ codeGraph n e ↔ decimalCode n xy.2 = e (decimalCode n xy.1) := by
  constructor
  · rw [codeGraph]
    simp only [Set.mem_iUnion, Set.mem_prod, decimalCylinder,
      Set.mem_preimage, Set.mem_singleton_iff]
    rintro ⟨a, ha, hb⟩
    simpa [ha] using hb
  · intro h
    refine Set.mem_iUnion.2 ⟨decimalCode n xy.1, ?_⟩
    exact ⟨rfl, h⟩

theorem codeGraph_measurable (n : ℕ) (e : Equiv.Perm (Fin (10 ^ n))) :
    MeasurableSet (codeGraph n e) := by
  exact MeasurableSet.iUnion fun a =>
    (decimalCylinder_measurable n a).prod
      (decimalCylinder_measurable n (e a))

/-- The mass of a permutation graph is bounded by its cylinder cross sum. -/
theorem codeGraph_mass_le_crossSum (ν : ProbabilityMeasure UnitAddCircle)
    (n : ℕ) (e : Equiv.Perm (Fin (10 ^ n))) :
    ((ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) (codeGraph n e)).toReal ≤
      ∑ a : Fin (10 ^ n), cylinderMass ν n a * cylinderMass ν n (e a) := by
  have hENN :
      (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) (codeGraph n e) ≤
        ∑ a : Fin (10 ^ n),
          (ν : Measure UnitAddCircle) (decimalCylinder n a) *
            (ν : Measure UnitAddCircle) (decimalCylinder n (e a)) := by
    calc
      (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) (codeGraph n e) ≤
          ∑' a : Fin (10 ^ n),
            (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
              (decimalCylinder n a ×ˢ decimalCylinder n (e a)) := by
        exact measure_iUnion_le _
      _ = ∑ a : Fin (10 ^ n),
          (ν : Measure UnitAddCircle) (decimalCylinder n a) *
            (ν : Measure UnitAddCircle) (decimalCylinder n (e a)) := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro a _
        exact Measure.prod_prod _ _
  have hsumTop : (∑ a : Fin (10 ^ n),
      (ν : Measure UnitAddCircle) (decimalCylinder n a) *
        (ν : Measure UnitAddCircle) (decimalCylinder n (e a))) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro a _
    exact ENNReal.mul_ne_top
      (measure_ne_top (ν : Measure UnitAddCircle) _)
      (measure_ne_top (ν : Measure UnitAddCircle) _)
  have hreal := (ENNReal.toReal_le_toReal
    (measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _)
    hsumTop).2 hENN
  rw [ENNReal.toReal_sum] at hreal
  · simpa only [ENNReal.toReal_mul, cylinderMass] using hreal
  · intro a ha
    exact ENNReal.mul_ne_top
      (measure_ne_top (ν : Measure UnitAddCircle) _)
      (measure_ne_top (ν : Measure UnitAddCircle) _)

/-- Cauchy--Schwarz and permutation invariance bound every graph cross sum by
the collision energy. -/
theorem crossSum_le_cylinderCollisionEnergy
    (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ)
    (e : Equiv.Perm (Fin (10 ^ n))) :
    (∑ a : Fin (10 ^ n), cylinderMass ν n a * cylinderMass ν n (e a)) ≤
      cylinderCollisionEnergy ν n := by
  have hperm : (∑ a : Fin (10 ^ n), cylinderMass ν n (e a) ^ 2) =
      cylinderCollisionEnergy ν n := by
    exact Equiv.sum_comp e (fun a => cylinderMass ν n a ^ 2)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin (10 ^ n)))
    (cylinderMass ν n) (fun a => cylinderMass ν n (e a))
  rw [hperm] at hcs
  have henergy : 0 ≤ cylinderCollisionEnergy ν n := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (∑ a : Fin (10 ^ n),
      cylinderMass ν n a * cylinderMass ν n (e a)) ≤
        √(cylinderCollisionEnergy ν n) * √(cylinderCollisionEnergy ν n) at hcs
  rw [Real.mul_self_sqrt henergy] at hcs
  exact hcs

/-- Closed diagonal pairs are covered by the equal, successor, and predecessor
code graphs. The successor and predecessor graphs include wraparound. -/
theorem closedDiagonal_subset_three_codeGraphs (n : ℕ) :
    closedDiagonal (decimalRadius n) ⊆
      codeGraph n (Equiv.refl _) ∪ (
        codeGraph n (finRotate (10 ^ n)) ∪
          codeGraph n (finRotate (10 ^ n)).symm) := by
  intro xy hxy
  have hadj := closedDiagonal_implies_decimalCodes_cyclicAdjacent n hxy
  rcases cyclicAdjacent_three_cases (by positivity) _ _ hadj with h | h | h
  · left
    rw [mem_codeGraph_iff]
    simpa using h
  · right; left
    rwa [mem_codeGraph_iff]
  · right; right
    rwa [mem_codeGraph_iff]

/-- The identity graph is a disjoint union of same-cylinder rectangles, so
its mass is exactly the cylinder collision energy. -/
theorem codeGraph_refl_mass_eq_cylinderCollisionEnergy
    (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ) :
    ((ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
      (codeGraph n (Equiv.refl _))).toReal = cylinderCollisionEnergy ν n := by
  have hdisj : Pairwise (fun a b : Fin (10 ^ n) => Disjoint
      (decimalCylinder n a ×ˢ decimalCylinder n a)
      (decimalCylinder n b ×ˢ decimalCylinder n b)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro xy hxa hxb
    apply hab
    have ha : decimalCode n xy.1 = a := hxa.1
    have hb : decimalCode n xy.1 = b := hxb.1
    exact ha.symm.trans hb
  have hmeasure := measure_iUnion
    (μ := (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))) hdisj
    (fun a => (decimalCylinder_measurable n a).prod
      (decimalCylinder_measurable n a))
  change ((ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
    (⋃ a : Fin (10 ^ n), decimalCylinder n a ×ˢ decimalCylinder n a)).toReal = _
  rw [hmeasure, tsum_fintype, ENNReal.toReal_sum]
  · unfold cylinderCollisionEnergy
    apply Finset.sum_congr rfl
    intro a _
    change ((Measure.prod (ν : Measure UnitAddCircle) (ν : Measure UnitAddCircle)
      (decimalCylinder n a ×ˢ decimalCylinder n a)).toReal) = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    simp only [cylinderMass, pow_two]
  · intro a ha
    exact measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _

/-- Same half-open cylinder implies membership in the closed diagonal at one
decimal scale. Endpoint pairs are retained because the small ball is closed. -/
theorem codeGraph_refl_subset_closedDiagonal (n : ℕ) :
    codeGraph n (Equiv.refl _) ⊆ closedDiagonal (decimalRadius n) := by
  intro xy hxy
  rw [mem_codeGraph_iff] at hxy
  change dist xy.1 xy.2 ≤ decimalRadius n
  have hx : xy.1 ∈ decimalCylinder n (decimalCode n xy.1) := rfl
  have hy : xy.2 ∈ decimalCylinder n (decimalCode n xy.1) := by
    change decimalCode n xy.2 = decimalCode n xy.1
    simpa using hxy
  simpa only [decimalRadius, decimalScale] using
    (dist_le_decimalScale_of_mem hx hy)

/-- Real mass of the closed diagonal neighborhood. -/
def closedSmallBallMass (ν : ProbabilityMeasure UnitAddCircle) (r : ℝ) : ℝ :=
  ((ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal r)).toReal

/-- Cylinder collisions are contained in the closed small ball. -/
theorem cylinderCollisionEnergy_le_closedSmallBallMass
    (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ) :
    cylinderCollisionEnergy ν n ≤ closedSmallBallMass ν (decimalRadius n) := by
  rw [← codeGraph_refl_mass_eq_cylinderCollisionEnergy]
  exact ENNReal.toReal_mono
    (measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _)
    (measure_mono (codeGraph_refl_subset_closedDiagonal n))

/-- The closed small ball is at most three times the cylinder collision
energy: one identity graph and the two cyclic neighbor graphs. -/
theorem closedSmallBallMass_le_three_mul_cylinderCollisionEnergy
    (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ) :
    closedSmallBallMass ν (decimalRadius n) ≤
      3 * cylinderCollisionEnergy ν n := by
  let μ : Measure (UnitAddCircle × UnitAddCircle) := ν.prod ν
  let G₀ := codeGraph n (Equiv.refl (Fin (10 ^ n)))
  let Gp := codeGraph n (finRotate (10 ^ n))
  let Gm := codeGraph n (finRotate (10 ^ n)).symm
  have hset : closedDiagonal (decimalRadius n) ⊆ G₀ ∪ (Gp ∪ Gm) :=
    closedDiagonal_subset_three_codeGraphs n
  have hENN : μ (closedDiagonal (decimalRadius n)) ≤ μ G₀ + μ Gp + μ Gm := by
    calc
      μ (closedDiagonal (decimalRadius n)) ≤ μ (G₀ ∪ (Gp ∪ Gm)) := measure_mono hset
      _ ≤ μ G₀ + μ (Gp ∪ Gm) := measure_union_le _ _
      _ ≤ μ G₀ + (μ Gp + μ Gm) := by
        gcongr
        exact measure_union_le _ _
      _ = μ G₀ + μ Gp + μ Gm := by ac_rfl
  have h0top : μ G₀ ≠ ∞ := measure_ne_top μ _
  have hptop : μ Gp ≠ ∞ := measure_ne_top μ _
  have hmtop : μ Gm ≠ ∞ := measure_ne_top μ _
  have htop : μ G₀ + μ Gp + μ Gm ≠ ∞ := by
    rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
    exact ⟨⟨h0top, hptop⟩, hmtop⟩
  have hreal := ENNReal.toReal_mono htop hENN
  have h₀ : (μ G₀).toReal ≤ cylinderCollisionEnergy ν n := by
    exact (codeGraph_mass_le_crossSum ν n (Equiv.refl _)).trans
      (crossSum_le_cylinderCollisionEnergy ν n (Equiv.refl _))
  have hp : (μ Gp).toReal ≤ cylinderCollisionEnergy ν n := by
    exact (codeGraph_mass_le_crossSum ν n (finRotate (10 ^ n))).trans
      (crossSum_le_cylinderCollisionEnergy ν n (finRotate (10 ^ n)))
  have hm : (μ Gm).toReal ≤ cylinderCollisionEnergy ν n := by
    exact (codeGraph_mass_le_crossSum ν n (finRotate (10 ^ n)).symm).trans
      (crossSum_le_cylinderCollisionEnergy ν n (finRotate (10 ^ n)).symm)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h0top, hptop⟩) hmtop,
    ENNReal.toReal_add h0top hptop] at hreal
  simp only [μ, G₀, Gp, Gm, closedSmallBallMass] at hreal h₀ hp hm ⊢
  linarith

/-- The explicit two-sided cylinder/small-ball comparison at decimal scale. -/
theorem cylinderCollisionEnergy_smallBall_comparison
    (ν : ProbabilityMeasure UnitAddCircle) (n : ℕ) :
    cylinderCollisionEnergy ν n ≤ closedSmallBallMass ν (decimalRadius n) ∧
      closedSmallBallMass ν (decimalRadius n) ≤
        3 * cylinderCollisionEnergy ν n :=
  ⟨cylinderCollisionEnergy_le_closedSmallBallMass ν n,
    closedSmallBallMass_le_three_mul_cylinderCollisionEnergy ν n⟩

theorem decimalRadius_eq_one_tenth_pow (n : ℕ) :
    decimalRadius n = ((10 : ℝ)⁻¹) ^ n := by
  rw [decimalRadius, inv_pow]

theorem decimalRadius_antitone : Antitone decimalRadius := by
  rw [funext decimalRadius_eq_one_tenth_pow]
  exact antitone_nat_of_succ_le fun n => by
    rw [pow_succ]
    have hnonneg : 0 ≤ ((10 : ℝ)⁻¹) ^ n := by positivity
    nlinarith

/-- Every radius in `(0,1]` lies between consecutive decimal radii. -/
theorem exists_decimalRadius_bracket {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, decimalRadius (n + 1) < r ∧ r ≤ decimalRadius n := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < (10 : ℝ)⁻¹)
    (by norm_num : (10 : ℝ)⁻¹ < 1)
  exact ⟨n, by simpa only [decimalRadius_eq_one_tenth_pow] using hn1,
    by simpa only [decimalRadius_eq_one_tenth_pow] using hn2⟩

theorem decimalRadius_succ_eq_div_ten (n : ℕ) :
    decimalRadius (n + 1) = decimalRadius n / 10 := by
  rw [decimalRadius_eq_one_tenth_pow, decimalRadius_eq_one_tenth_pow, pow_succ]
  ring

theorem closedSmallBallMass_mono (ν : ProbabilityMeasure UnitAddCircle)
    {r s : ℝ} (hrs : r ≤ s) :
    closedSmallBallMass ν r ≤ closedSmallBallMass ν s := by
  apply ENNReal.toReal_mono
    (measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _)
  apply measure_mono
  intro xy hxy
  exact hxy.trans hrs

/-- Eventual power decay of decimal-cylinder collision energy. -/
def PolynomialCylinderDecay (ν : ProbabilityMeasure UnitAddCircle) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    cylinderCollisionEnergy ν n ≤ C * (decimalRadius n) ^ α

/-- The real-valued version of C2's polynomial closed-small-ball clause. -/
def PolynomialClosedSmallBall (ν : ProbabilityMeasure UnitAddCircle) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∃ r0 : ℝ, 0 < r0 ∧
    ∀ r : ℝ, 0 < r → r ≤ r0 →
      closedSmallBallMass ν r ≤ C * r ^ α

/-- C2's polynomial small-ball clause implies cylinder decay with the same
exponent and constant at all sufficiently fine decimal scales. -/
theorem polynomialClosedSmallBall_implies_polynomialCylinderDecay
    (ν : ProbabilityMeasure UnitAddCircle)
    (hsmall : PolynomialClosedSmallBall ν) : PolynomialCylinderDecay ν := by
  obtain ⟨α, C, hα, hC, r0, hr0, hsmall⟩ := hsmall
  have hevent : ∀ᶠ n : ℕ in atTop, decimalRadius n < r0 :=
    decimalRadius_tendsto_zero.eventually (Iio_mem_nhds hr0)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hevent
  refine ⟨α, C, hα, hC, n0, ?_⟩
  intro n hn
  exact (cylinderCollisionEnergy_le_closedSmallBallMass ν n).trans
    (hsmall (decimalRadius n) (decimalRadius_pos n) (hn0 n hn).le)

/-- Cylinder decay implies C2's all-small-radii clause. The scale
interpolation is explicit: the constant changes from `C` to `3*C*10^α`, while
the exponent is unchanged. -/
theorem polynomialCylinderDecay_implies_polynomialClosedSmallBall
    (ν : ProbabilityMeasure UnitAddCircle)
    (hcyl : PolynomialCylinderDecay ν) : PolynomialClosedSmallBall ν := by
  obtain ⟨α, C, hα, hC, n0, hcyl⟩ := hcyl
  let r0 := min 1 (decimalRadius n0)
  refine ⟨α, 3 * C * 10 ^ α, hα, by positivity, r0,
    lt_min zero_lt_one (decimalRadius_pos n0), ?_⟩
  intro r hr hr0
  have hr1 : r ≤ 1 := hr0.trans (min_le_left _ _)
  have hrn0 : r ≤ decimalRadius n0 := hr0.trans (min_le_right _ _)
  obtain ⟨n, hnnext, hrn⟩ := exists_decimalRadius_bracket hr hr1
  have hn0n : n0 ≤ n := by
    by_contra hnot
    have hsucc : n + 1 ≤ n0 := by omega
    have hmono := decimalRadius_antitone hsucc
    linarith
  have hnTen : decimalRadius n < 10 * r := by
    rw [decimalRadius_succ_eq_div_ten] at hnnext
    linarith
  have hrpow : (decimalRadius n) ^ α ≤ (10 * r) ^ α :=
    Real.rpow_le_rpow (decimalRadius_pos n).le hnTen.le hα.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hr.le] at hrpow
  calc
    closedSmallBallMass ν r ≤ closedSmallBallMass ν (decimalRadius n) :=
      closedSmallBallMass_mono ν hrn
    _ ≤ 3 * cylinderCollisionEnergy ν n :=
      closedSmallBallMass_le_three_mul_cylinderCollisionEnergy ν n
    _ ≤ 3 * (C * (decimalRadius n) ^ α) := by gcongr; exact hcyl n hn0n
    _ ≤ (3 * C * 10 ^ α) * r ^ α := by nlinarith

/-- Polynomial cylinder decay is equivalent to the polynomial closed-small-
ball clause, with the quantitative constants recorded by the two directions. -/
theorem polynomialCylinderDecay_iff_polynomialClosedSmallBall
    (ν : ProbabilityMeasure UnitAddCircle) :
    PolynomialCylinderDecay ν ↔ PolynomialClosedSmallBall ν :=
  ⟨polynomialCylinderDecay_implies_polynomialClosedSmallBall ν,
    polynomialClosedSmallBall_implies_polynomialCylinderDecay ν⟩

/-- The literal measure-valued polynomial clause appearing inside T4's C2. -/
def C2PolynomialSmallBallClause (ν : ProbabilityMeasure UnitAddCircle) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∃ r0 : ℝ, 0 < r0 ∧
    ∀ r : ℝ, 0 < r → r ≤ r0 →
      (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal r) ≤
        ENNReal.ofReal (C * r ^ α)

theorem polynomialClosedSmallBall_iff_C2PolynomialSmallBallClause
    (ν : ProbabilityMeasure UnitAddCircle) :
    PolynomialClosedSmallBall ν ↔ C2PolynomialSmallBallClause ν := by
  constructor
  · rintro ⟨α, C, hα, hC, r0, hr0, hsmall⟩
    refine ⟨α, C, hα, hC, r0, hr0, ?_⟩
    intro r hr hr0r
    have hnonneg : 0 ≤ C * r ^ α := by positivity
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _)
      hnonneg).2 (hsmall r hr hr0r)
  · rintro ⟨α, C, hα, hC, r0, hr0, hsmall⟩
    refine ⟨α, C, hα, hC, r0, hr0, ?_⟩
    intro r hr hr0r
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hsmall r hr hr0r)

/-- Exact characterization of C2's polynomial clause by decimal-cylinder
collision decay. -/
theorem polynomialCylinderDecay_iff_C2PolynomialSmallBallClause
    (ν : ProbabilityMeasure UnitAddCircle) :
    PolynomialCylinderDecay ν ↔ C2PolynomialSmallBallClause ν :=
  (polynomialCylinderDecay_iff_polynomialClosedSmallBall ν).trans
    (polynomialClosedSmallBall_iff_C2PolynomialSmallBallClause ν)

/-- A weakly convergent empirical cluster whose limiting cylinder energy
satisfies `n * P_n → 0`. This is weaker than polynomial decay. -/
def VanishingCylinderEnergyCluster (u : ℕ → UnitAddCircle) : Prop :=
  ∃ cutoffs : ℕ → ℕ, StrictMono cutoffs ∧ (∀ k, 0 < cutoffs k) ∧
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      Tendsto (fun k => circleEmpiricalMeasure u (cutoffs k)) atTop (𝓝 ν) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * cylinderCollisionEnergy ν n)
        atTop (𝓝 0)

/-- The weak condition `n * P_n → 0` on an empirical cluster implies the
ordered, diagonal-inclusive near-return estimate. -/
theorem vanishingCylinderEnergyCluster_implies_nearReturnEstimate
    (u : ℕ → UnitAddCircle) (hcluster : VanishingCylinderEnergyCluster u) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * orderedNearReturnCount u (decimalRadius n) N ≤ N ^ 2 := by
  rintro A hA
  obtain ⟨cutoffs, _hmono, hcutoffsPos, ν, hν, henergy⟩ := hcluster
  have hscaled : Tendsto (fun n : ℕ =>
      (3 * (A : ℝ)) * ((n : ℝ) * cylinderCollisionEnergy ν n))
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (3 * (A : ℝ))) atTop
        (𝓝 (3 * (A : ℝ))) := tendsto_const_nhds
    have h := hconst.mul henergy
    simpa only [mul_zero] using h
  have hevent : ∀ᶠ n : ℕ in atTop,
      (3 * (A : ℝ)) * ((n : ℝ) * cylinderCollisionEnergy ν n) < 1 :=
    hscaled.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨m, hm⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  have hnm : m ≤ n := (le_max_right 1 m).trans hn
  have hdecayN := hm n hnm
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 m).trans hn)
  have hAn : 0 < (A : ℝ) * (n : ℝ) := by positivity
  have hnumeric : 3 * cylinderCollisionEnergy ν n <
      1 / ((A : ℝ) * (n : ℝ)) := by
    apply (lt_div_iff₀ hAn).2
    calc
      (3 * cylinderCollisionEnergy ν n) * ((A : ℝ) * (n : ℝ)) =
          (3 * (A : ℝ)) * ((n : ℝ) * cylinderCollisionEnergy ν n) := by ring
      _ < 1 := hdecayN
  have hνReal : closedSmallBallMass ν (decimalRadius n) <
      1 / ((A : ℝ) * (n : ℝ)) :=
    (closedSmallBallMass_le_three_mul_cylinderCollisionEnergy ν n).trans_lt hnumeric
  have hνENN :
      (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
          (closedDiagonal (decimalRadius n)) <
        ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) := by
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (measure_ne_top (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle)) _)).2 hνReal
  have hprodTendsto := empiricalProduct_tendsto hν
  have hport : limsup (fun k =>
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)))
        atTop ≤ (ν.prod ν : Measure (UnitAddCircle × UnitAddCircle))
          (closedDiagonal (decimalRadius n)) :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hprodTendsto
      (closedDiagonal_isClosed (decimalRadius n))
  have hlimitStrict : limsup (fun k =>
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)))
        atTop < ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) :=
    hport.trans_lt hνENN
  have heventProduct : ∀ᶠ k : ℕ in atTop,
      ((circleEmpiricalMeasure u (cutoffs k)).prod
        (circleEmpiricalMeasure u (cutoffs k)) :
          Measure (UnitAddCircle × UnitAddCircle)) (closedDiagonal (decimalRadius n)) <
        ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) :=
    eventually_lt_of_limsup_lt hlimitStrict
  obtain ⟨k, hk⟩ := heventProduct.exists
  let N := cutoffs k
  have hN : 0 < N := hcutoffsPos k
  have hk' : (orderedClosedPairCount u (decimalRadius n) N : ENNReal) /
      (N : ENNReal) ^ 2 < ENNReal.ofReal (1 / ((A : ℝ) * (n : ℝ))) := by
    rw [← empiricalProduct_apply_closedDiagonal u (decimalRadius n) N hN]
    exact hk
  have hthresholdPos : 0 < 1 / ((A : ℝ) * (n : ℝ)) := by positivity
  have hkReal : (orderedClosedPairCount u (decimalRadius n) N : ℝ) /
      (N : ℝ) ^ 2 < 1 / ((A : ℝ) * (n : ℝ)) := by
    have hconverted := (ENNReal.toReal_lt_toReal (by finiteness)
      ENNReal.ofReal_ne_top).2 hk'
    simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hthresholdPos.le] using hconverted
  have hNreal : 0 < (N : ℝ) ^ 2 := by positivity
  have hclosed : (orderedClosedPairCount u (decimalRadius n) N : ℝ) <
      (N : ℝ) ^ 2 / ((A : ℝ) * (n : ℝ)) := by
    calc
      (orderedClosedPairCount u (decimalRadius n) N : ℝ) <
          (1 / ((A : ℝ) * (n : ℝ))) * (N : ℝ) ^ 2 :=
        (div_lt_iff₀ hNreal).1 hkReal
      _ = (N : ℝ) ^ 2 / ((A : ℝ) * (n : ℝ)) := by ring
  have hscaledClosed : (A : ℝ) * (n : ℝ) *
      (orderedClosedPairCount u (decimalRadius n) N : ℝ) < (N : ℝ) ^ 2 := by
    have := (lt_div_iff₀ hAn).1 hclosed
    nlinarith
  have hnearReal : (A : ℝ) * (n : ℝ) *
      (orderedNearReturnCount u (decimalRadius n) N : ℝ) < (N : ℝ) ^ 2 := by
    calc
      (A : ℝ) * (n : ℝ) *
          (orderedNearReturnCount u (decimalRadius n) N : ℝ) ≤
          (A : ℝ) * (n : ℝ) *
            (orderedClosedPairCount u (decimalRadius n) N : ℝ) := by
        gcongr
        exact_mod_cast orderedNearReturnCount_le_closed u (decimalRadius n) N
      _ < (N : ℝ) ^ 2 := hscaledClosed
  refine ⟨N, hN, ?_⟩
  have hnat : A * n * orderedNearReturnCount u (decimalRadius n) N < N ^ 2 := by
    exact_mod_cast hnearReal
  exact hnat.le

/-- The corresponding explicit hypothesis for the decimal orbit of pi. It is
not asserted by this module. -/
def PiVanishingCylinderEnergyCluster : Prop :=
  VanishingCylinderEnergyCluster piDecimalCircleOrbit

/-- Conditional pi specialization with the canonical quantifier order and
T1's ordered, diagonal-inclusive `Q_pi`. No decay assertion for pi is made. -/
theorem piVanishingCylinderEnergyCluster_implies_canonical_C1
    (hcluster : PiVanishingCylinderEnergyCluster) :
    ∀ A : ℕ, 1 ≤ A → ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∃ N : ℕ, 1 ≤ N ∧
        A * n * Q_pi n N ≤ N ^ 2 := by
  intro A hA
  obtain ⟨n0, hn0, hall⟩ :=
    vanishingCylinderEnergyCluster_implies_nearReturnEstimate
      piDecimalCircleOrbit hcluster A hA
  refine ⟨n0, hn0, ?_⟩
  intro n hn
  obtain ⟨N, hN, hbound⟩ := hall n hn
  refine ⟨N, hN, ?_⟩
  calc
    A * n * Q_pi n N ≤ A * n *
        orderedNearReturnCount piDecimalCircleOrbit (decimalRadius n) N := by
      gcongr
      exact Q_pi_le_orderedNearReturnCount n N
    _ ≤ N ^ 2 := hbound

end DecimalFactorComplexity.CylinderCollision

#print axioms DecimalFactorComplexity.CylinderCollision.dist_le_inv_of_mem_Ico_implies_cyclicAdjacent
#print axioms DecimalFactorComplexity.CylinderCollision.closedDiagonal_implies_decimalCodes_cyclicAdjacent
#print axioms DecimalFactorComplexity.CylinderCollision.cylinderCollisionEnergy_smallBall_comparison
#print axioms DecimalFactorComplexity.CylinderCollision.polynomialCylinderDecay_iff_C2PolynomialSmallBallClause
#print axioms DecimalFactorComplexity.CylinderCollision.vanishingCylinderEnergyCluster_implies_nearReturnEstimate
#print axioms DecimalFactorComplexity.CylinderCollision.piVanishingCylinderEnergyCluster_implies_canonical_C1
