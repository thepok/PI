import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit
import TheoryLib.PiQuantitativeBlockHitting.T75T75UniformShadowCover
import TheoryLib.PiDigits.T21PiDigitsV1V3Relationship

/-!
# T108: endpoint-safe circle-density transfer for the sampled BBP orbit

The sampled BBP orbit and the canonical decimal pi orbit become asymptotic in
`UnitAddCircle`.  Arbitrarily-late circle density is stable under any such
asymptotic perturbation, so the two density predicates are equivalent.

This module proves no density, mixing, normality, digit occurrence, or V1
statement unconditionally.  The final V1 implication retains arbitrarily-late
circle density of the sampled BBP orbit as an explicit premise.
-/

noncomputable section

namespace Theory.PiDigits.T108BBPCircleDensityTransfer

open Theory.PiDigits.T106BBPForcedOrbit
open Theory.PiDigits.T75UniformShadowCover

/-- The circle distance from the sampled BBP point to the matching canonical
decimal pi point is bounded by the nonnegative scaled BBP error.  This bound
is endpoint-safe because it is proved in `UnitAddCircle`. -/
theorem circleDist_sampledBBPOrbit_le_sampledBBPError (N : ℕ) :
    dist (((sampledBBPOrbit N : ℝ) : UnitAddCircle))
      (((Theory.PiDigits.T20.baseTenOrbit Real.pi N : ℝ) : UnitAddCircle))
      ≤ sampledBBPError N := by
  have key :
      ((sampledBBPOrbit N + sampledBBPError N : ℝ) : UnitAddCircle) =
        (((10 : ℝ) ^ N * Real.pi : ℝ) : UnitAddCircle) := by
    have h := congrArg (fun z : ℝ => (z : UnitAddCircle))
      (fract_sampledBBPOrbit_add_error N)
    simpa only [AddCircle.coe_fract] using h
  have hpi : ((Theory.PiDigits.T20.baseTenOrbit Real.pi N : ℝ) : UnitAddCircle)
      = ((sampledBBPOrbit N + sampledBBPError N : ℝ) : UnitAddCircle) := by
    rw [show Theory.PiDigits.T20.baseTenOrbit Real.pi N =
      Int.fract ((10 : ℝ) ^ N * Real.pi) from rfl,
      AddCircle.coe_fract, ← key]
  rw [hpi, AddCircle.coe_add, dist_eq_norm]
  have hsub : ((sampledBBPOrbit N : ℝ) : UnitAddCircle) -
      (((sampledBBPOrbit N : ℝ) : UnitAddCircle) +
        ((sampledBBPError N : ℝ) : UnitAddCircle)) =
        -((sampledBBPError N : ℝ) : UnitAddCircle) := by
    abel
  rw [hsub, norm_neg]
  have hround := round_le (sampledBBPError N) (0 : ℤ)
  rw [Int.cast_zero, sub_zero] at hround
  rw [AddCircle.norm_eq (p := (1 : ℝ)), inv_one, mul_one, one_mul]
  exact hround.trans_eq (abs_of_nonneg (sampledBBPError_nonneg N))

/-- The circle distance between the sampled BBP orbit and the matching
canonical decimal pi orbit tends to zero. -/
theorem tendsto_circleDist_sampledBBP_pi_zero :
    Filter.Tendsto
      (fun N : ℕ =>
        dist (((sampledBBPOrbit N : ℝ) : UnitAddCircle))
          (((Theory.PiDigits.T20.baseTenOrbit Real.pi N : ℝ) : UnitAddCircle)))
      Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto sampledBBPError Filter.atTop (nhds 0) :=
    summable_sampledBBPError.tendsto_atTop_zero
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨E, hE⟩ := Metric.tendsto_atTop.1 hzero eps heps
  refine ⟨E, fun N hN => ?_⟩
  have hsmall := hE N hN
  simp only [Real.dist_eq, sub_zero,
    abs_of_nonneg (sampledBBPError_nonneg N),
    abs_of_nonneg dist_nonneg] at hsmall ⊢
  exact lt_of_le_of_lt
    (circleDist_sampledBBPOrbit_le_sampledBBPError N) hsmall

/-- Arbitrarily-late circle density is invariant under a perturbation whose
pointwise circle distance tends to zero. -/
theorem circleDenseArbitrarilyLate_iff_of_tendsto_dist_zero
    {u v : ℕ → UnitAddCircle}
    (hzero : Filter.Tendsto (fun n => dist (u n) (v n)) Filter.atTop
      (nhds 0)) :
    (∀ y : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (u n) y < r) ↔
      ∀ y : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (v n) y < r := by
  constructor
  · intro hu y N r hr
    have hr2 : 0 < r / 2 := by positivity
    obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp
      (hzero.eventually_lt_const hr2)
    obtain ⟨n, hnN, hn⟩ := hu y (max N N') (r / 2) hr2
    refine ⟨n, (le_max_left N N').trans hnN, ?_⟩
    have htriangle : dist (v n) y ≤ dist (v n) (u n) + dist (u n) y :=
      dist_triangle _ _ _
    have hclose := hN' n ((le_max_right N N').trans hnN)
    rw [dist_comm (v n) (u n)] at htriangle
    linarith
  · intro hv y N r hr
    have hr2 : 0 < r / 2 := by positivity
    obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp
      (hzero.eventually_lt_const hr2)
    obtain ⟨n, hnN, hn⟩ := hv y (max N N') (r / 2) hr2
    refine ⟨n, (le_max_left N N').trans hnN, ?_⟩
    have htriangle : dist (u n) y ≤ dist (u n) (v n) + dist (v n) y :=
      dist_triangle _ _ _
    have hclose := hN' n ((le_max_right N N').trans hnN)
    linarith

private theorem unitAddCircle_dist_coe_le_abs (a b : ℝ) :
    dist ((a : UnitAddCircle)) ((b : UnitAddCircle)) ≤ |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- Canonical V1 implies arbitrarily-late circle density of the canonical
base-ten fractional-part orbit of pi.  V1 remains an explicit premise. -/
theorem canonicalV1_implies_pi_circleDenseArbitrarilyLate :
    Theory.PiDigits.V1 →
      BaseTenOrbitCircleDenseArbitrarilyLate Real.pi := by
  intro hV1 y N r hr
  have hlate : Theory.PiDigits.T21.EveryFiniteWordOccursArbitrarilyLate
      Theory.PiDigits.piDigit :=
    (Theory.PiDigits.T21.everyFiniteWordOccurs_iff_arbitrarilyLate
      Theory.PiDigits.piDigit).mp
      (Theory.PiDigits.T21.canonicalV1_iff_everyFiniteWordOccurs_piDigit.mp hV1)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr
    (by norm_num : (10 : ℝ)⁻¹ < 1)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : UnitAddCircle)) = y :=
    ⟨y.out, Quotient.out_eq y⟩
  have huCoe : ((Int.fract t : ℝ) : UnitAddCircle) = y := by
    rw [AddCircle.coe_fract, ht]
  have huIco : Int.fract t ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  let s : List (Fin 10) :=
    List.ofFn fun i : Fin m =>
      Theory.PiDigits.T20.decimalDigit (Int.fract t) i.val
  obtain ⟨n, hnN, hnOcc⟩ := hlate s N
  have hmatch : ∀ i : Fin m,
      Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val) =
        Theory.PiDigits.T20.decimalDigit (Int.fract t) i.val := by
    intro i
    have hi : i.val < s.length := by
      simpa only [s, List.length_ofFn] using i.isLt
    simpa only [s, List.getElem_ofFn,
      Theory.PiDigits.T20.decimalDigit_pi] using hnOcc i.val hi
  have hbound :=
    Theory.PiDigits.T72ColoredRepunitReturn.abs_baseTenOrbit_sub_le_of_prefixMatch
      Real.pi_pos.le huIco hmatch
  refine ⟨n, hnN, ?_⟩
  have hfinal :=
    calc
      dist ((Theory.PiDigits.T20.baseTenOrbit Real.pi n : ℝ) : UnitAddCircle)
          ((Int.fract t : ℝ) : UnitAddCircle) ≤
          |Theory.PiDigits.T20.baseTenOrbit Real.pi n - Int.fract t| :=
        unitAddCircle_dist_coe_le_abs _ _
      _ ≤ ((10 : ℝ) ^ m)⁻¹ := hbound
      _ < r := by simpa [inv_pow] using hm
  rwa [huCoe] at hfinal

/-- Arbitrarily-late circle density of the sampled BBP orbit.  This is an
explicit premise, not an assertion that the orbit is dense. -/
def SampledBBPOrbitCircleDenseArbitrarilyLate : Prop :=
  ∀ y : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
    ∃ n : ℕ, N ≤ n ∧
      dist (((sampledBBPOrbit n : ℝ) : UnitAddCircle)) y < r

/-- Arbitrarily-late circle density of the sampled BBP orbit is equivalent to
T75's canonical arbitrarily-late circle-density predicate for pi. -/
theorem sampledBBP_circleDense_iff_pi_circleDense :
    SampledBBPOrbitCircleDenseArbitrarilyLate ↔
      BaseTenOrbitCircleDenseArbitrarilyLate Real.pi := by
  simpa only [SampledBBPOrbitCircleDenseArbitrarilyLate,
    BaseTenOrbitCircleDenseArbitrarilyLate] using
    (circleDenseArbitrarilyLate_iff_of_tendsto_dist_zero
      (u := fun N => ((sampledBBPOrbit N : ℝ) : UnitAddCircle))
      (v := fun N =>
        ((Theory.PiDigits.T20.baseTenOrbit Real.pi N : ℝ) : UnitAddCircle))
      tendsto_circleDist_sampledBBP_pi_zero)

/-- Conditional endpoint: arbitrarily-late circle density of the sampled BBP
orbit, kept as an explicit premise, implies canonical V1. -/
theorem sampledBBP_circleDense_implies_canonicalV1
    (hdense : SampledBBPOrbitCircleDenseArbitrarilyLate) :
    Theory.PiDigits.V1 :=
  Theory.PiDigits.T72ColoredRepunitReturn.canonicalV1_iff_coloredRepunitReturns.mpr
    (circleDenseArbitrarilyLate_implies_coloredRepunitReturns
      (sampledBBP_circleDense_iff_pi_circleDense.mp hdense))

/-- Canonical V1 is equivalent to arbitrarily-late circle density of the
sampled BBP orbit.  This equivalence asserts neither proposition. -/
theorem canonicalV1_iff_sampledBBPOrbitCircleDenseArbitrarilyLate :
    Theory.PiDigits.V1 ↔ SampledBBPOrbitCircleDenseArbitrarilyLate :=
  ⟨fun hV1 => sampledBBP_circleDense_iff_pi_circleDense.mpr
      (canonicalV1_implies_pi_circleDenseArbitrarilyLate hV1),
    sampledBBP_circleDense_implies_canonicalV1⟩

end Theory.PiDigits.T108BBPCircleDensityTransfer
