import TheoryLib.PiDigits.T26WeylCancellationV1
import TheoryLib.PiQuantitativeBlockHitting.T72T72ColoredRepunitReturn

/-!
# T75: endpoint-safe transfer from uniformly covering shadows

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This module isolates the exact abstract conclusion needed from the proposed
BBP endpoint grids.  A row of circle-valued shadows must eventually cover the
whole circle at every positive scale, its associated decimal exponents must
eventually exceed every prescribed threshold, and its uniform error from the
shifted base-ten orbit must tend to zero.  Those three hypotheses imply all
colored repunit returns and hence canonical V1 for pi.

No BBP grid is asserted here to satisfy any of the hypotheses.  In
particular, this module does not prove the open largest-gap estimate.  The
proof treats color zero separately: circle closeness to zero alone would also
allow points near one, whereas `ColoredRepunitReturns` uses ordinary real
absolute value.
-/

noncomputable section

namespace Theory.PiDigits.T75UniformShadowCover

open Theory.PiDigits.T72ColoredRepunitReturn

/-- Every sufficiently late shadow row covers the unit circle at the
prescribed radius.  In the intended finite-grid application, `width e` is the
row length and the hypothesis follows from a largest-gap bound tending to
zero. -/
def EventuallyUniformCircleCover
    (width : ℕ → ℕ)
    (shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
    ∀ y : UnitAddCircle, ∃ j : Fin (width e), dist (shadow e j) y < r

/-- The exponents attached to every sufficiently late row occur after every
prescribed starting time. -/
def ShadowExponentsTendToInfinity
    (width : ℕ → ℕ)
    (exponent : ∀ e : ℕ, Fin (width e) → ℕ) : Prop :=
  ∀ N : ℕ, ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
    ∀ j : Fin (width e), N ≤ exponent e j

/-- Uniform vanishing circle error between each shadow and the corresponding
base-ten orbit point after subtracting the fixed shift.  For the BBP phase
`(10^n - 16) B`, the intended shift is the class of `16 * x`. -/
def ShiftedShadowErrorTendsToZero
    (x : ℝ) (shift : UnitAddCircle)
    (width : ℕ → ℕ)
    (shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle)
    (exponent : ∀ e : ℕ, Fin (width e) → ℕ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
    ∀ j : Fin (width e),
      dist (shadow e j)
        (((Theory.PiDigits.T20.baseTenOrbit x (exponent e j) : ℝ) :
            UnitAddCircle) - shift) < r

/-- Arbitrarily late circle-density of the real base-ten fractional-part
orbit.  This remains a circle statement; the endpoint-safe conversion to
ordinary distance is proved separately below. -/
def BaseTenOrbitCircleDenseArbitrarilyLate (x : ℝ) : Prop :=
  ∀ y : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
    ∃ n : ℕ, N ≤ n ∧
      dist (((Theory.PiDigits.T20.baseTenOrbit x n : ℝ) : UnitAddCircle)) y < r

/-- Uniform circle coverage plus vanishing shifted-shadow error transfers to
arbitrarily late circle-density of the actual decimal orbit. -/
theorem uniformShadowCover_implies_circleDenseArbitrarilyLate
    {x : ℝ} {shift : UnitAddCircle}
    {width : ℕ → ℕ}
    {shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle}
    {exponent : ∀ e : ℕ, Fin (width e) → ℕ}
    (hcover : EventuallyUniformCircleCover width shadow)
    (hlate : ShadowExponentsTendToInfinity width exponent)
    (herror : ShiftedShadowErrorTendsToZero x shift width shadow exponent) :
    BaseTenOrbitCircleDenseArbitrarilyLate x := by
  intro y N ε hε
  let r : ℝ := ε / 3
  have hr : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨Ecover, hEcover⟩ := hcover r hr
  obtain ⟨Eerror, hEerror⟩ := herror r hr
  obtain ⟨Elate, hElate⟩ := hlate N
  let e : ℕ := max Ecover (max Eerror Elate)
  have heCover : Ecover ≤ e := by
    exact le_max_left _ _
  have heError : Eerror ≤ e := by
    exact (le_max_left Eerror Elate).trans (le_max_right Ecover _)
  have heLate : Elate ≤ e := by
    exact (le_max_right Eerror Elate).trans (le_max_right Ecover _)
  obtain ⟨j, hjCover⟩ := hEcover e heCover (y - shift)
  have hjError := hEerror e heError j
  refine ⟨exponent e j, hElate e heLate j, ?_⟩
  let orbit : UnitAddCircle :=
    ((Theory.PiDigits.T20.baseTenOrbit x (exponent e j) : ℝ) : UnitAddCircle)
  have hcoverShift : dist (shadow e j + shift) y < r := by
    calc
      dist (shadow e j + shift) y =
          dist (shadow e j + shift) ((y - shift) + shift) := by
            rw [sub_add_cancel]
      _ = dist (shadow e j) (y - shift) := by
        exact dist_add_right (shadow e j) (y - shift) shift
      _ < r := hjCover
  have herrorShift : dist (shadow e j + shift) orbit < r := by
    calc
      dist (shadow e j + shift) orbit =
          dist (shadow e j + shift) ((orbit - shift) + shift) := by
            rw [sub_add_cancel]
      _ = dist (shadow e j) (orbit - shift) := by
        exact dist_add_right (shadow e j) (orbit - shift) shift
      _ < r := by
        simpa only [orbit] using hjError
  calc
    dist orbit y ≤ dist orbit (shadow e j + shift) +
        dist (shadow e j + shift) y := dist_triangle _ _ _
    _ < r + r := add_lt_add (by simpa [dist_comm] using herrorShift) hcoverShift
    _ < ε := by
      dsimp [r]
      linarith

/-- Arbitrarily late circle-density gives every colored repunit return in
ordinary real distance.  Positive colors are protected from both endpoints;
for color zero the proof instead targets a small positive interior point. -/
theorem circleDenseArbitrarilyLate_implies_coloredRepunitReturns
    {x : ℝ} (hdense : BaseTenOrbitCircleDenseArbitrarilyLate x) :
    ColoredRepunitReturns x := by
  intro P hP k N ε hε
  let y : ℝ := repunitGridPoint P k
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [y] using repunitGridPoint_mem_Ico hP k
  by_cases hy0 : y = 0
  · let center : ℝ := min (ε / 4) (1 / 4)
    let r : ℝ := center / 2
    have hcenter : 0 < center := by
      dsimp [center]
      exact lt_min (by positivity) (by norm_num)
    have hcenterLe : center ≤ 1 / 4 := by
      exact min_le_right _ _
    have hcenterEps : center ≤ ε / 4 := by
      exact min_le_left _ _
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
    have hn0 := (Theory.PiDigits.T20.baseTenOrbit_mem_Ico x n).1
    have hnUpper := (abs_lt.mp hnReal).2
    change |Theory.PiDigits.T20.baseTenOrbit x n - y| < ε
    rw [hy0, sub_zero, abs_of_nonneg hn0]
    dsimp [r] at hnUpper
    linarith
  · have hyPos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    let r : ℝ := min (ε / 2) (min (y / 2) ((1 - y) / 2))
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (by positivity)
        (lt_min (by positivity) (by linarith [hy.2]))
    have hry : r < y := by
      have := min_le_left (y / 2) ((1 - y) / 2)
      have hrle : r ≤ y / 2 :=
        (min_le_right (ε / 2) _).trans this
      linarith
    have hryOne : r < 1 - y := by
      have := min_le_right (y / 2) ((1 - y) / 2)
      have hrle : r ≤ (1 - y) / 2 :=
        (min_le_right (ε / 2) _).trans this
      linarith
    have hrEps : r < ε := by
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
    have hnReal :=
      Theory.PiDigits.T26.abs_fract_sub_lt_of_circle_dist_lt
        (x := (10 : ℝ) ^ n * x) (y := y) (r := r)
        hry hryOne hnCircle'
    exact (by
      simpa only [Theory.PiDigits.T20.baseTenOrbit, y] using
        hnReal.trans hrEps)

/-- The complete generic endpoint-safe bridge from finite shadow rows to
colored repunit returns.  All analytic and arithmetic work is isolated in its
three explicit premises. -/
theorem uniformShadowCover_implies_coloredRepunitReturns
    {x : ℝ} {shift : UnitAddCircle}
    {width : ℕ → ℕ}
    {shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle}
    {exponent : ∀ e : ℕ, Fin (width e) → ℕ}
    (hcover : EventuallyUniformCircleCover width shadow)
    (hlate : ShadowExponentsTendToInfinity width exponent)
    (herror : ShiftedShadowErrorTendsToZero x shift width shadow exponent) :
    ColoredRepunitReturns x :=
  circleDenseArbitrarilyLate_implies_coloredRepunitReturns
    (uniformShadowCover_implies_circleDenseArbitrarilyLate hcover hlate herror)

/-- Pi specialization: the same three explicit hypotheses settle canonical
V1.  This theorem proves only the implication and asserts none of the
hypotheses for the currently studied BBP grids. -/
theorem pi_uniformShadowCover_implies_canonicalV1
    {shift : UnitAddCircle}
    {width : ℕ → ℕ}
    {shadow : ∀ e : ℕ, Fin (width e) → UnitAddCircle}
    {exponent : ∀ e : ℕ, Fin (width e) → ℕ}
    (hcover : EventuallyUniformCircleCover width shadow)
    (hlate : ShadowExponentsTendToInfinity width exponent)
    (herror : ShiftedShadowErrorTendsToZero Real.pi shift width shadow exponent) :
    Theory.PiDigits.V1 := by
  exact canonicalV1_iff_coloredRepunitReturns.mpr
    (uniformShadowCover_implies_coloredRepunitReturns hcover hlate herror)

end Theory.PiDigits.T75UniformShadowCover

#print axioms
  Theory.PiDigits.T75UniformShadowCover.uniformShadowCover_implies_circleDenseArbitrarilyLate
#print axioms
  Theory.PiDigits.T75UniformShadowCover.circleDenseArbitrarilyLate_implies_coloredRepunitReturns
#print axioms Theory.PiDigits.T75UniformShadowCover.uniformShadowCover_implies_coloredRepunitReturns
#print axioms Theory.PiDigits.T75UniformShadowCover.pi_uniformShadowCover_implies_canonicalV1
