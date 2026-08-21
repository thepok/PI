import TheoryLib.PiQuantitativeBlockHitting.T75T75UniformShadowCover

/-!
# Independent T75 replay

This audit file deliberately does not invoke any of T75's four bridge
theorems.  It rederives the cover-to-circle-density transfer, the endpoint
zero return, the interior-color return, and the final implication to
canonical V1 from the definitions and the previously audited T26/T72
interfaces.
-/

noncomputable section

namespace T75UniformShadowCoverIndependentReplay

open Theory.PiDigits.T72ColoredRepunitReturn
open Theory.PiDigits.T75UniformShadowCover

/-- Independent replay of the quantifier and shift bookkeeping in T75's
first bridge. -/
theorem replay_uniformShadowCover_implies_circleDenseArbitrarilyLate
    {x : ℝ} {shift : UnitAddCircle}
    {width : ℕ → ℕ}
    {shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle}
    {exponent : ∀ e : ℕ, Fin (width e) → ℕ}
    (hcover : EventuallyUniformCircleCover width shadow)
    (hlate : ShadowExponentsTendToInfinity width exponent)
    (herror : ShiftedShadowErrorTendsToZero x shift width shadow exponent) :
    BaseTenOrbitCircleDenseArbitrarilyLate x := by
  intro y N ε hε
  let r : ℝ := ε / 4
  have hr : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨Ec, hc⟩ := hcover r hr
  obtain ⟨Ee, he⟩ := herror r hr
  obtain ⟨En, hn⟩ := hlate N
  let row : ℕ := max Ec (max Ee En)
  have hEc : Ec ≤ row := le_max_left _ _
  have hEe : Ee ≤ row :=
    (le_max_left Ee En).trans (le_max_right Ec _)
  have hEn : En ≤ row :=
    (le_max_right Ee En).trans (le_max_right Ec _)
  obtain ⟨j, hjc⟩ := hc row hEc (y - shift)
  have hje := he row hEe j
  let orbit : UnitAddCircle :=
    ((Theory.PiDigits.T20.baseTenOrbit x (exponent row j) : ℝ) :
      UnitAddCircle)
  have hshadowTarget : dist (shadow row j + shift) y < r := by
    calc
      dist (shadow row j + shift) y =
          dist (shadow row j + shift) ((y - shift) + shift) := by
            rw [sub_add_cancel]
      _ = dist (shadow row j) (y - shift) :=
        dist_add_right (shadow row j) (y - shift) shift
      _ < r := hjc
  have hshadowOrbit : dist (shadow row j + shift) orbit < r := by
    calc
      dist (shadow row j + shift) orbit =
          dist (shadow row j + shift) ((orbit - shift) + shift) := by
            rw [sub_add_cancel]
      _ = dist (shadow row j) (orbit - shift) :=
        dist_add_right (shadow row j) (orbit - shift) shift
      _ < r := by
        simpa only [orbit] using hje
  refine ⟨exponent row j, hn row hEn j, ?_⟩
  calc
    dist orbit y ≤ dist orbit (shadow row j + shift) +
        dist (shadow row j + shift) y := dist_triangle _ _ _
    _ < r + r :=
      add_lt_add (by simpa [dist_comm] using hshadowOrbit) hshadowTarget
    _ < ε := by
      dsimp [r]
      linarith

/-- Independent endpoint check: circle density gives ordinary real returns to
zero by aiming at a small positive interior center. -/
theorem replay_zero_endpoint_return
    {x : ℝ} (hdense : BaseTenOrbitCircleDenseArbitrarilyLate x)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, N ≤ n ∧
      |Theory.PiDigits.T20.baseTenOrbit x n - 0| < ε := by
  let center : ℝ := min (ε / 8) (1 / 8)
  let r : ℝ := center / 2
  have hcenter : 0 < center := by
    dsimp [center]
    exact lt_min (by positivity) (by norm_num)
  have hcenterEps : center ≤ ε / 8 := min_le_left _ _
  have hcenterUpper : center ≤ 1 / 8 := min_le_right _ _
  have hr : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨n, hnN, hnCircle⟩ :=
    hdense ((center : ℝ) : UnitAddCircle) N r hr
  have hnCircle' :
      dist ((((10 : ℝ) ^ n * x : ℝ) : UnitAddCircle))
        ((center : ℝ) : UnitAddCircle) < r := by
    simpa only [Theory.PiDigits.T20.baseTenOrbit, AddCircle.coe_fract] using
      hnCircle
  have hnReal :
      |Theory.PiDigits.T20.baseTenOrbit x n - center| < r := by
    simpa only [Theory.PiDigits.T20.baseTenOrbit] using
      (Theory.PiDigits.T26.abs_fract_sub_lt_of_circle_dist_lt
        (x := (10 : ℝ) ^ n * x) (y := center) (r := r)
        (by dsimp [r]; linarith)
        (by dsimp [r]; linarith)
        hnCircle')
  refine ⟨n, hnN, ?_⟩
  have hnNonneg := (Theory.PiDigits.T20.baseTenOrbit_mem_Ico x n).1
  have hnUpper := (abs_lt.mp hnReal).2
  rw [sub_zero, abs_of_nonneg hnNonneg]
  dsimp [r] at hnUpper
  linarith

/-- Independent nonzero-color check: the circle ball is kept inside the
ordinary interval `(0,1)`. -/
theorem replay_interior_return
    {x y : ℝ} (hdense : BaseTenOrbitCircleDenseArbitrarilyLate x)
    (hy0 : 0 < y) (hy1 : y < 1)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, N ≤ n ∧
      |Theory.PiDigits.T20.baseTenOrbit x n - y| < ε := by
  let r : ℝ := min (ε / 2) (min (y / 2) ((1 - y) / 2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity)
      (lt_min (by positivity) (by linarith))
  have hry : r < y := by
    have hrle : r ≤ y / 2 :=
      (min_le_right (ε / 2) _).trans (min_le_left _ _)
    linarith
  have hry1 : r < 1 - y := by
    have hrle : r ≤ (1 - y) / 2 :=
      (min_le_right (ε / 2) _).trans (min_le_right _ _)
    linarith
  have hrε : r < ε := by
    have hrle : r ≤ ε / 2 := min_le_left _ _
    linarith
  obtain ⟨n, hnN, hnCircle⟩ :=
    hdense ((y : ℝ) : UnitAddCircle) N r hr
  have hnCircle' :
      dist ((((10 : ℝ) ^ n * x : ℝ) : UnitAddCircle))
        ((y : ℝ) : UnitAddCircle) < r := by
    simpa only [Theory.PiDigits.T20.baseTenOrbit, AddCircle.coe_fract] using
      hnCircle
  refine ⟨n, hnN, ?_⟩
  exact (Theory.PiDigits.T26.abs_fract_sub_lt_of_circle_dist_lt
    (x := (10 : ℝ) ^ n * x) (y := y) (r := r)
    hry hry1 hnCircle').trans hrε

/-- Independent assembly of the zero and positive color cases. -/
theorem replay_circleDenseArbitrarilyLate_implies_coloredRepunitReturns
    {x : ℝ} (hdense : BaseTenOrbitCircleDenseArbitrarilyLate x) :
    ColoredRepunitReturns x := by
  intro P hP k N ε hε
  let y : ℝ := repunitGridPoint P k
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [y] using repunitGridPoint_mem_Ico hP k
  by_cases hy0 : y = 0
  · simpa only [y, hy0] using replay_zero_endpoint_return hdense N ε hε
  · have hyPos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    simpa only [y] using
      replay_interior_return hdense hyPos hy.2 N ε hε

/-- Full independent replay of the abstract T75 implication.  This does not
assert that a BBP shadow family satisfies any premise. -/
theorem replay_pi_uniformShadowCover_implies_canonicalV1
    {shift : UnitAddCircle}
    {width : ℕ → ℕ}
    {shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle}
    {exponent : ∀ e : ℕ, Fin (width e) → ℕ}
    (hcover : EventuallyUniformCircleCover width shadow)
    (hlate : ShadowExponentsTendToInfinity width exponent)
    (herror : ShiftedShadowErrorTendsToZero Real.pi shift width shadow exponent) :
    Theory.PiDigits.V1 := by
  apply canonicalV1_iff_coloredRepunitReturns.mpr
  apply replay_circleDenseArbitrarilyLate_implies_coloredRepunitReturns
  exact replay_uniformShadowCover_implies_circleDenseArbitrarilyLate
    hcover hlate herror

end T75UniformShadowCoverIndependentReplay

#print axioms
  T75UniformShadowCoverIndependentReplay.replay_uniformShadowCover_implies_circleDenseArbitrarilyLate
#print axioms
  T75UniformShadowCoverIndependentReplay.replay_zero_endpoint_return
#print axioms
  T75UniformShadowCoverIndependentReplay.replay_interior_return
#print axioms
  T75UniformShadowCoverIndependentReplay.replay_circleDenseArbitrarilyLate_implies_coloredRepunitReturns
#print axioms
  T75UniformShadowCoverIndependentReplay.replay_pi_uniformShadowCover_implies_canonicalV1
