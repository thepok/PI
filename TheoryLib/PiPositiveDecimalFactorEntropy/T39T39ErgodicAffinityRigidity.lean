import TheoryLib.PiPositiveDecimalFactorEntropy.T20T20TransversalEntropy
import TheoryLib.PiPositiveDecimalFactorEntropy.T35T35CylinderAffinity
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.MeasureTheory.Measure.Support

/-!
# T39: conditional ergodic-affinity rigidity bootstrap

Canonical source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This module imports the kernel-checked T20 and T35 modules.  The T32 note is not
imported and is used only as an unverified roadmap.  The final theorem is wholly
conditional: it does not construct a measure for pi, prove positive metric
entropy, prove an affinity bound, or formalize the Rudolph--Johnson source
theorem.  Those inputs remain explicit hypotheses.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal MeasureTheory

namespace DecimalFactorEntropy.T39ErgodicAffinityRigidity

open DecimalFactorEntropy.CylinderAffinity
open DecimalFactorEntropy.TransversalEntropy

/-- Multiplication by ten on the circle, named locally to keep the T39
interfaces explicit. -/
def timesTenMap : UnitAddCircle → UnitAddCircle := circleMul 10

/-- Multiplication by sixteen on the circle. -/
def timesSixteenMap : UnitAddCircle → UnitAddCircle := circleMul 16

/-- The times-sixteen pushforward of a circle measure. -/
def timesSixteenPushforward (μ : Measure UnitAddCircle) : Measure UnitAddCircle :=
  Measure.map timesSixteenMap μ

theorem timesTenMap_measurable : Measurable timesTenMap :=
  (circleMul_continuous 10).measurable

theorem timesSixteenMap_measurable : Measurable timesSixteenMap :=
  (circleMul_continuous 16).measurable

/-- The two multiplication maps commute pointwise. -/
theorem timesTen_timesSixteen_commute :
    Function.Commute timesSixteenMap timesTenMap := by
  intro x
  change 16 • (10 • x) = 10 • (16 • x)
  rw [← mul_nsmul, ← mul_nsmul]

/-- Measurable pushforward preserves the probability normalization. -/
theorem timesSixteenPushforward_isProbability (μ : Measure UnitAddCircle)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (timesSixteenPushforward μ) := by
  unfold timesSixteenPushforward
  exact Measure.isProbabilityMeasure_map timesSixteenMap_measurable.aemeasurable

/-- Ergodicity for times ten passes through the commuting times-sixteen
pushforward.  No invertibility of either map is assumed. -/
theorem timesSixteenPushforward_ergodic (μ : Measure UnitAddCircle)
    (hμ : Ergodic timesTenMap μ) :
    Ergodic timesTenMap (timesSixteenPushforward μ) := by
  unfold timesSixteenPushforward
  exact (timesSixteenMap_measurable.measurePreserving μ).ergodic_of_ergodic_semiconj
    hμ timesTenMap_measurable timesTen_timesSixteen_commute.semiconj

/-- The explicit decimal-boundary interface used by T39.  A circle decimal
coding must be a measurable embedding, so terminating-decimal endpoints cannot
identify distinct circle points, and its finite cylinders must generate in
measure for the displayed pair. -/
def DecimalBoundarySafe
    (decimalCoding : UnitAddCircle → DecimalShift)
    (μ ν : Measure UnitAddCircle) : Prop :=
  MeasurableEmbedding decimalCoding ∧
    GeneratesInMeasure (Measure.map decimalCoding μ) (Measure.map decimalCoding ν)

/-- One depth-independent positive lower bound for every finite decimal
cylinder affinity rules out mutual singularity of the original circle
measures. -/
theorem positive_allDepth_decimalAffinity_implies_not_mutuallySingular
    (μ ν : Measure UnitAddCircle) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (decimalCoding : UnitAddCircle → DecimalShift)
    (hboundary : DecimalBoundarySafe decimalCoding μ ν)
    (δ : ℝ) (hδ : 0 < δ)
    (haffinity : ∀ m : ℕ,
      δ ≤ affinity (Measure.map decimalCoding μ) (Measure.map decimalCoding ν) m) :
    ¬ μ ⟂ₘ ν := by
  letI : IsProbabilityMeasure (Measure.map decimalCoding μ) :=
    Measure.isProbabilityMeasure_map hboundary.1.measurable.aemeasurable
  letI : IsProbabilityMeasure (Measure.map decimalCoding ν) :=
    Measure.isProbabilityMeasure_map hboundary.1.measurable.aemeasurable
  have hInf : δ ≤ sInf (Set.range
      (affinity (Measure.map decimalCoding μ) (Measure.map decimalCoding ν))) := by
    apply le_csInf (Set.range_nonempty _)
    intro y hy
    obtain ⟨m, rfl⟩ := hy
    exact haffinity m
  have hencoded : ¬(Measure.map decimalCoding μ) ⟂ₘ
      (Measure.map decimalCoding ν) :=
    (positive_allDepth_inf_iff_not_mutuallySingular hboundary.2).mp
      (hδ.trans_le hInf)
  intro hsing
  exact hencoded (hboundary.1.mutuallySingular_map hsing)

/-- Two probability measures ergodic for the same map are equal or mutually
singular.  Mathlib v4.30 supplies the invariant Lebesgue decomposition but does
not package this dichotomy as a named theorem. -/
theorem ergodic_eq_or_mutuallySingular
    {X : Type*} [MeasurableSpace X] (f : X → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hν : Ergodic f ν) :
    μ = ν ∨ μ ⟂ₘ ν := by
  let ρ := μ.singularPart ν
  have hρinv : MeasurePreserving f ρ ρ :=
    hμ.toMeasurePreserving.singularPart hν.toMeasurePreserving
  have hρac : ρ ≪ μ :=
    absolutelyContinuous_of_le (singularPart_le μ ν)
  obtain ⟨c, hc⟩ := hμ.eq_smul_of_absolutelyContinuous hρinv hρac
  by_cases hc₀ : c = 0
  · left
    have hρ₀ : ρ = 0 := by simp [hc, hc₀]
    have hμν : μ ≪ ν :=
      (singularPart_eq_zero μ ν).mp (by simpa [ρ] using hρ₀)
    exact hν.eq_of_absolutelyContinuous hμ.toMeasurePreserving hμν
  · right
    have hμρ : μ ≪ ρ := by
      rw [hc]
      exact absolutelyContinuous_smul hc₀
    exact (mutuallySingular_singularPart μ ν).mono_ac
      hμρ AbsolutelyContinuous.rfl

theorem common_ergodic_not_mutuallySingular_eq
    {X : Type*} [MeasurableSpace X] (f : X → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hν : Ergodic f ν) (hnonsingular : ¬ μ ⟂ₘ ν) :
    μ = ν := by
  rcases ergodic_eq_or_mutuallySingular f μ ν hμ hν with h | h
  · exact h
  · exact (hnonsingular h).elim

/-- The elementary bootstrap from decimal affinity to times-sixteen
invariance. -/
theorem positive_affinity_implies_timesSixteen_invariant
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (decimalCoding : UnitAddCircle → DecimalShift)
    (hTenErgodic : Ergodic timesTenMap μ)
    (hboundary : DecimalBoundarySafe decimalCoding μ (timesSixteenPushforward μ))
    (δ : ℝ) (hδ : 0 < δ)
    (haffinity : ∀ m : ℕ,
      δ ≤ affinity (Measure.map decimalCoding μ)
        (Measure.map decimalCoding (timesSixteenPushforward μ)) m) :
    timesSixteenPushforward μ = μ := by
  letI : IsProbabilityMeasure (timesSixteenPushforward μ) :=
    timesSixteenPushforward_isProbability μ
  have hPushErgodic := timesSixteenPushforward_ergodic μ hTenErgodic
  have hnonsingular : ¬ μ ⟂ₘ timesSixteenPushforward μ :=
    positive_allDepth_decimalAffinity_implies_not_mutuallySingular
      μ (timesSixteenPushforward μ) decimalCoding hboundary δ hδ haffinity
  exact (common_ergodic_not_mutuallySingular_eq timesTenMap μ
    (timesSixteenPushforward μ) hTenErgodic hPushErgodic hnonsingular).symm

/-- Exact formal interface to the external Rudolph--Johnson rigidity input.
The supplied `metricEntropy` is intentionally abstract because mathlib v4.30
has no Kolmogorov--Sinai metric-entropy definition.  The premise exposes the
probability, both generator invariances, times-ten ergodicity, and strict
positivity of that metric entropy before concluding normalized Lebesgue
measure. -/
def RudolphJohnsonRigidityPremise
    (metricEntropy : Measure UnitAddCircle → ℝ) : Prop :=
  ∀ μ : Measure UnitAddCircle,
    IsProbabilityMeasure μ →
    MeasurePreserving timesTenMap μ μ →
    MeasurePreserving timesSixteenMap μ μ →
    Ergodic timesTenMap μ →
    0 < metricEntropy μ →
    μ = (volume : Measure UnitAddCircle)

/-- Affinity supplies the missing invariance, after which the explicit source
premise supplies the only rigidity step. -/
theorem affinity_and_source_rigidity_imply_lebesgue
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (decimalCoding : UnitAddCircle → DecimalShift)
    (hTenInvariant : MeasurePreserving timesTenMap μ μ)
    (hTenErgodic : Ergodic timesTenMap μ)
    (hboundary : DecimalBoundarySafe decimalCoding μ (timesSixteenPushforward μ))
    (δ : ℝ) (hδ : 0 < δ)
    (haffinity : ∀ m : ℕ,
      δ ≤ affinity (Measure.map decimalCoding μ)
        (Measure.map decimalCoding (timesSixteenPushforward μ)) m)
    (metricEntropy : Measure UnitAddCircle → ℝ)
    (hentropy : 0 < metricEntropy μ)
    (hrigidity : RudolphJohnsonRigidityPremise metricEntropy) :
    timesSixteenPushforward μ = μ ∧ μ = (volume : Measure UnitAddCircle) := by
  have hSixteen := positive_affinity_implies_timesSixteen_invariant μ decimalCoding
    hTenErgodic hboundary δ hδ haffinity
  have hSixteenPreserving : MeasurePreserving timesSixteenMap μ μ :=
    ⟨timesSixteenMap_measurable, by simpa [timesSixteenPushforward] using hSixteen⟩
  exact ⟨hSixteen, hrigidity μ inferInstance hTenInvariant hSixteenPreserving
    hTenErgodic hentropy⟩

/-- Normalized Lebesgue/Haar measure on the unit circle has full support. -/
theorem volume_fullSupport :
    (volume : Measure UnitAddCircle).support = Set.univ :=
  Measure.support_eq_univ

/-- A measure identified with normalized Lebesgue measure has full support. -/
theorem fullSupport_of_eq_volume
    (μ : Measure UnitAddCircle)
    (hlebesgue : μ = (volume : Measure UnitAddCircle)) :
    μ.support = Set.univ := by
  rw [hlebesgue]
  exact volume_fullSupport

/-- A closed pi orbit closure carrying all of a measure which rigidity has
identified as Lebesgue must be the whole circle. -/
theorem piOrbitClosure_eq_univ_of_lebesgue_supported
    (μ : Measure UnitAddCircle)
    (hlebesgue : μ = (volume : Measure UnitAddCircle))
    (hsupported : μ piOrbitClosure = 1) :
    piOrbitClosure = (Set.univ : Set UnitAddCircle) := by
  apply (piOrbitClosure_isClosed.measure_eq_univ_iff_eq
    (μ := (volume : Measure UnitAddCircle))).mp
  simpa only [hlebesgue, UnitAddCircle.measure_univ] using hsupported

/-- Literal strengthening of C6 recording the constants and requiring every
radius witness to equal zero. -/
def PiC6WithZeroWitness : Prop :=
  ∃ A B ε₀ : ℝ,
    A = 1 ∧ B = 0 ∧ ε₀ = 1 ∧ 0 < A ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ R : ℕ, R = 0 ∧ IsTransversalTime piOrbitClosure ε R ∧
          (R : ℝ) ≤ A * Real.log (1 / ε) + B

/-- If the pi orbit closure is the circle, C6 holds with the literal witness
`R = 0` and constants `A = 1`, `B = 0`, `ε₀ = 1`. -/
theorem piC6WithZeroWitness_of_orbitClosure_eq_univ
    (hK : piOrbitClosure = (Set.univ : Set UnitAddCircle)) :
    PiC6WithZeroWitness := by
  refine ⟨1, 0, 1, rfl, rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro ε hε hε1
  refine ⟨0, rfl, ?_, ?_⟩
  · rw [hK]
    intro y
    refine ⟨y, ?_, by simpa using hε.le⟩
    simp [timesSixteenTransversal, circleMul]
  · norm_num
    exact Real.log_nonpos hε.le hε1.le

theorem piC6_of_zeroWitness (h : PiC6WithZeroWitness) : PiC6 := by
  obtain ⟨A, B, ε₀, _hAeq, _hBeq, _hεeq, hA, hε₀, hrest⟩ := h
  refine ⟨A, B, ε₀, hA, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨R, _hR, htime, hbound⟩ := hrest ε hε hεsmall
  exact ⟨R, htime, hbound⟩

/-- Complete conditional pi bootstrap.  Every unresolved input remains in the
signature: the measure, probability normalization, times-ten invariance and
ergodicity, support on `K_pi`, decimal-boundary-safe coding, all-depth affinity,
positive metric entropy, and the source-rigidity premise. -/
theorem pi_conditional_ergodic_affinity_rigidity
    (μ : Measure UnitAddCircle) [IsProbabilityMeasure μ]
    (decimalCoding : UnitAddCircle → DecimalShift)
    (hTenInvariant : MeasurePreserving timesTenMap μ μ)
    (hTenErgodic : Ergodic timesTenMap μ)
    (hsupported : μ piOrbitClosure = 1)
    (hboundary : DecimalBoundarySafe decimalCoding μ (timesSixteenPushforward μ))
    (δ : ℝ) (hδ : 0 < δ)
    (haffinity : ∀ m : ℕ,
      δ ≤ affinity (Measure.map decimalCoding μ)
        (Measure.map decimalCoding (timesSixteenPushforward μ)) m)
    (metricEntropy : Measure UnitAddCircle → ℝ)
    (hentropy : 0 < metricEntropy μ)
    (hrigidity : RudolphJohnsonRigidityPremise metricEntropy) :
    timesSixteenPushforward μ = μ ∧
      μ = (volume : Measure UnitAddCircle) ∧
      μ.support = Set.univ ∧
      piOrbitClosure = (Set.univ : Set UnitAddCircle) ∧
      PiC6WithZeroWitness ∧ PiC6 := by
  obtain ⟨hSixteen, hLebesgue⟩ := affinity_and_source_rigidity_imply_lebesgue
    μ decimalCoding hTenInvariant hTenErgodic hboundary δ hδ haffinity
      metricEntropy hentropy hrigidity
  have hK := piOrbitClosure_eq_univ_of_lebesgue_supported μ hLebesgue hsupported
  have hZero := piC6WithZeroWitness_of_orbitClosure_eq_univ hK
  exact ⟨hSixteen, hLebesgue, fullSupport_of_eq_volume μ hLebesgue, hK, hZero,
    piC6_of_zeroWitness hZero⟩

end DecimalFactorEntropy.T39ErgodicAffinityRigidity

#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.timesSixteenPushforward_isProbability
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.timesSixteenPushforward_ergodic
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.positive_allDepth_decimalAffinity_implies_not_mutuallySingular
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.ergodic_eq_or_mutuallySingular
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.common_ergodic_not_mutuallySingular_eq
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.positive_affinity_implies_timesSixteen_invariant
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.affinity_and_source_rigidity_imply_lebesgue
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.volume_fullSupport
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.fullSupport_of_eq_volume
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.piOrbitClosure_eq_univ_of_lebesgue_supported
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.piC6WithZeroWitness_of_orbitClosure_eq_univ
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.piC6_of_zeroWitness
#print axioms DecimalFactorEntropy.T39ErgodicAffinityRigidity.pi_conditional_ergodic_affinity_rigidity
