import TheoryLib.PiLacunaryNearReturnSparsity.T24FiniteInverseDichotomy
import TheoryLib.PiLacunaryNearReturnSparsity.T26SharedResonanceChain
import TheoryLib.PiLacunaryNearReturnSparsity.T28AdjacentNodeCompatibility
import TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy

/-!
# T34: finite mixed-product bridge for adjacent fixed-pi resonance nodes

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The Fourier lower bound and exponent-eight irrationality estimate used below
are explicit hypotheses. This module proves neither hypothesis and makes no
unconditional compatibility or canonical-A1 claim for `Real.pi`.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace MixedProductBridge

open IteratedLagResonance
open FiniteInverseDichotomy
open SharedResonanceChain
open AdjacentNodeCompatibility

namespace Fourier

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel
abbrev signedFrequenciesZero :=
  Theory.PiDigits.BoundaryRobustFejerDichotomy.signedFrequenciesZero
abbrev triangularCoefficient :=
  Theory.PiDigits.BoundaryRobustFejerDichotomy.triangularCoefficient

end Fourier

lemma mem_fourierCutoff_iff {H : ℕ} {u : ℤ} :
    u ∈ Fourier.signedFrequenciesZero H ↔ u.natAbs ≤ H :=
  Theory.PiDigits.BoundaryRobustFejerDichotomy.mem_signedFrequenciesZero

lemma triangularCoefficient_explicit (H : ℕ) (u : ℤ) :
    Fourier.triangularCoefficient H u =
      1 - (u.natAbs : ℝ) / (H + 1 : ℝ) := rfl

lemma nodeTau_explicit (D k : ℕ) :
    nodeTau D k = 1 / (8 * (densityDenominator D k : ℝ) ^ 2) := rfl

/-- The common legal T24 pair domain at adjacent nodes `k` and `k+1`.
Both residual inequalities are retained literally. -/
def commonPairDomain
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) : Finset (ℕ × ℕ) :=
  ((range (chain.nodeResidual k)) ×ˢ
      (range (chain.nodeResidual (k + 1)))).filter fun js =>
    1 ≤ js.2 ∧
    js.1 + js.2 < chain.nodeResidual k ∧
    js.1 + js.2 < chain.nodeResidual (k + 1)

/-- The natural denominator `10^j (10^s - 1)` attached to a pair. -/
def pairDenominator (js : ℕ × ℕ) : ℕ :=
  decimalDenominatorNat js.1 js.2

/-- A finite, nonnegative Fejer smoothing weight with cutoff `H`. -/
def smoothNodeWeight (H : ℕ) (beta : ℝ) (js : ℕ × ℕ) : ℝ :=
  Fourier.fejerKernel H ((pairDenominator js : ℝ) * beta)

/-- The scaled-error form of T24's good-pair predicate. The common legal range
is imposed separately by `commonPairDomain`. -/
def T24GoodPair (beta tau : ℝ) (js : ℕ × ℕ) : Prop :=
  ∃ a : ℤ, scaledIntegerError beta js.1 js.2 a < inverseError tau

/-- The two T24 predicates at one common pair, plus exactly T28's weighted
cross-node error budget. This is the formal JWMO endpoint, not a theorem. -/
def JointGoodPair
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (js : ℕ × ℕ) : Prop :=
  ∃ a0 a1 : ℤ,
    scaledIntegerError (chain.nodeCoefficient k) js.1 js.2 a0 <
        inverseError (nodeTau D k) ∧
      scaledIntegerError (chain.nodeCoefficient (k + 1)) js.1 js.2 a1 <
        inverseError (nodeTau D (k + 1)) ∧
      (pairDenominator js : ℝ) *
            scaledIntegerError (chain.nodeCoefficient (k + 1))
              js.1 js.2 a1 +
          (GeometricResonanceChain.adjacentFactor chain k : ℝ) *
            (pairDenominator js : ℝ) *
              scaledIntegerError (chain.nodeCoefficient k) js.1 js.2 a0 < 1

/-- Product of the two finite smooth weights at adjacent chain nodes. -/
def commonPairWeight
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) (js : ℕ × ℕ) : ℝ :=
  smoothNodeWeight H0 (chain.nodeCoefficient k) js *
    smoothNodeWeight H1 (chain.nodeCoefficient (k + 1)) js

/-- The complete mixed product sum over the common legal pair domain. -/
def mixedProductSum
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) : ℝ :=
  ∑ js ∈ commonPairDomain chain k,
    commonPairWeight chain k H0 H1 js

/-- The exact boundary contribution: legal pairs at which the two T24 errors
and T28 mixed budget do not hold jointly. No boundary term is discarded. -/
noncomputable def boundaryLoss
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) : ℝ := by
  classical
  exact ∑ js ∈ (commonPairDomain chain k).filter fun js =>
    ¬ JointGoodPair chain k js,
      commonPairWeight chain k H0 H1 js

/-- The retained smooth mass on legal pairs satisfying both T24 predicates
and the mixed T28 budget. -/
noncomputable def commonGoodMass
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) : ℝ := by
  classical
  exact ∑ js ∈ (commonPairDomain chain k).filter fun js =>
    JointGoodPair chain k js,
      commonPairWeight chain k H0 H1 js

theorem mixedProductSum_eq_goodMass_add_boundaryLoss
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) :
    mixedProductSum chain k H0 H1 =
      commonGoodMass chain k H0 H1 + boundaryLoss chain k H0 H1 := by
  classical
  unfold mixedProductSum commonGoodMass boundaryLoss
  exact (sum_filter_add_sum_filter_not
    (commonPairDomain chain k) (JointGoodPair chain k)
      (commonPairWeight chain k H0 H1)).symm

/-- The explicit mixed double-frequency expression. The frequency transported
from node `k+1` is visibly multiplied by the genuine chain successor factor
`U = 10^(shiftAt k)-1`. -/
def mixedDoubleFrequencySum
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) : ℂ :=
  ∑ u ∈ Fourier.signedFrequenciesZero H0,
    ∑ v ∈ Fourier.signedFrequenciesZero H1,
      ((Fourier.triangularCoefficient H0 u *
          Fourier.triangularCoefficient H1 v : ℝ) : ℂ) *
        ∑ js ∈ commonPairDomain chain k,
          Fourier.phase
            (u + (GeometricResonanceChain.adjacentFactor chain k : ℤ) * v)
            ((pairDenominator js : ℝ) * chain.nodeCoefficient k)

lemma mem_commonPairDomain_iff
    {M D K d h r : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} {js : ℕ × ℕ} :
    js ∈ commonPairDomain chain k ↔
      js.1 < chain.nodeResidual k ∧
      js.2 < chain.nodeResidual (k + 1) ∧
      1 ≤ js.2 ∧
      js.1 + js.2 < chain.nodeResidual k ∧
      js.1 + js.2 < chain.nodeResidual (k + 1) := by
  simp [commonPairDomain, and_assoc]

/-- On a positive-period pair, the scaled predicate is exactly T24's original
eventually-periodic approximation predicate. -/
theorem t24GoodPair_iff_eventuallyPeriodicApproximation
    (beta tau : ℝ) (j s : ℕ) (hs : 1 ≤ s) :
    T24GoodPair beta tau (j, s) ↔
      EventuallyPeriodicApproximation beta tau j s := by
  have hqNat : 1 ≤ decimalDenominatorNat j s :=
    decimalDenominatorNat_pos hs
  have hq : (0 : ℝ) < decimalDenominatorNat j s := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
  have hcast := decimalDenominatorNat_cast j s
  have hid (a : ℤ) :
      beta - (a : ℝ) / (decimalDenominatorNat j s : ℝ) =
        ((decimalDenominatorNat j s : ℝ) * beta - (a : ℝ)) /
          (decimalDenominatorNat j s : ℝ) := by
    field_simp
  unfold T24GoodPair EventuallyPeriodicApproximation
    decimalEventuallyPeriodicDenominator scaledIntegerError
  simp only
  rw [← hcast]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [hid, abs_div, abs_of_pos hq]
    exact (div_lt_div_iff_of_pos_right hq).2 ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [hid, abs_div, abs_of_pos hq] at ha
    exact (div_lt_div_iff_of_pos_right hq).1 ha

lemma JointGoodPair.left_t24GoodPair
    {M D K d h r : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} {js : ℕ × ℕ}
    (hgood : JointGoodPair chain k js) :
    T24GoodPair (chain.nodeCoefficient k) (nodeTau D k) js := by
  obtain ⟨a0, _a1, he0, _he1, _hbudget⟩ := hgood
  exact ⟨a0, he0⟩

lemma JointGoodPair.right_t24GoodPair
    {M D K d h r : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} {js : ℕ × ℕ}
    (hgood : JointGoodPair chain k js) :
    T24GoodPair (chain.nodeCoefficient (k + 1))
      (nodeTau D (k + 1)) js := by
  obtain ⟨_a0, a1, _he0, he1, _hbudget⟩ := hgood
  exact ⟨a1, he1⟩

lemma smoothNodeWeight_nonneg (H : ℕ) (beta : ℝ) (js : ℕ × ℕ) :
    0 ≤ smoothNodeWeight H beta js := by
  exact Theory.PiDigits.T27.fejerKernel_nonneg _ _

lemma commonPairWeight_nonneg
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) (js : ℕ × ℕ) :
    0 ≤ commonPairWeight chain k H0 H1 js := by
  exact mul_nonneg (smoothNodeWeight_nonneg _ _ _)
    (smoothNodeWeight_nonneg _ _ _)

lemma phase_successor_transport
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (u v : ℤ) (js : ℕ × ℕ) :
    Fourier.phase u
          ((pairDenominator js : ℝ) * chain.nodeCoefficient k) *
        Fourier.phase v
          ((pairDenominator js : ℝ) * chain.nodeCoefficient (k + 1)) =
      Fourier.phase
        (u + (GeometricResonanceChain.adjacentFactor chain k : ℤ) * v)
        ((pairDenominator js : ℝ) * chain.nodeCoefficient k) := by
  have hcoefficient :=
    GeometricResonanceChain.nodeCoefficient_succ chain k
  rw [hcoefficient]
  have hphase :
      Fourier.phase v
          ((pairDenominator js : ℝ) *
            ((GeometricResonanceChain.adjacentFactor chain k : ℝ) *
              chain.nodeCoefficient k)) =
        Fourier.phase
          ((GeometricResonanceChain.adjacentFactor chain k : ℤ) * v)
          ((pairDenominator js : ℝ) * chain.nodeCoefficient k) := by
    unfold Fourier.phase Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring
  rw [hphase, ← Theory.PiDigits.T27.phase_add]

/-- Exact product expansion, including both cutoffs, both triangular
coefficients, the common legal range, and successor-coefficient transport. -/
theorem mixedProductSum_eq_doubleFrequencySum
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) :
    (mixedProductSum chain k H0 H1 : ℂ) =
      mixedDoubleFrequencySum chain k H0 H1 := by
  classical
  have hpoint (js : ℕ × ℕ) :
      ((commonPairWeight chain k H0 H1 js : ℝ) : ℂ) =
        ∑ u ∈ Fourier.signedFrequenciesZero H0,
          ∑ v ∈ Fourier.signedFrequenciesZero H1,
            ((Fourier.triangularCoefficient H0 u *
                Fourier.triangularCoefficient H1 v : ℝ) : ℂ) *
              Fourier.phase
                (u +
                  (GeometricResonanceChain.adjacentFactor chain k : ℤ) * v)
                ((pairDenominator js : ℝ) * chain.nodeCoefficient k) := by
    unfold commonPairWeight smoothNodeWeight
    push_cast
    rw [Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerKernel_eq_aggregated,
      Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerKernel_eq_aggregated]
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [← phase_successor_transport chain k u v js]
    ring
  unfold mixedProductSum mixedDoubleFrequencySum
  push_cast
  simp_rw [hpoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro js hjs
  push_cast
  rfl

/-- The displayed mixed-sum hypothesis. Its left side is the exact boundary
loss, so this is an unproved analytic overlap premise rather than a hidden
claim about `pi`. -/
def MixedSumLowerBound
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) : Prop :=
  boundaryLoss chain k H0 H1 <
    (mixedDoubleFrequencySum chain k H0 H1).re

/-- A mixed-sum lower bound leaves positive smooth mass on a common pair that
satisfies both T24 predicates and T28's mixed error budget. -/
theorem exists_positive_commonPairWeight
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ)
    (hmix : MixedSumLowerBound chain k H0 H1) :
    ∃ js ∈ commonPairDomain chain k,
      JointGoodPair chain k js ∧
      0 < commonPairWeight chain k H0 H1 js := by
  classical
  have hexpansion :
      (mixedDoubleFrequencySum chain k H0 H1).re =
        mixedProductSum chain k H0 H1 := by
    rw [← mixedProductSum_eq_doubleFrequencySum]
    simp
  have hmixProduct :
      boundaryLoss chain k H0 H1 < mixedProductSum chain k H0 H1 := by
    change boundaryLoss chain k H0 H1 <
      (mixedDoubleFrequencySum chain k H0 H1).re at hmix
    rwa [hexpansion] at hmix
  let good : ℕ × ℕ → Prop := fun js => JointGoodPair chain k js
  by_contra hnone
  have hzero : ∀ js ∈ (commonPairDomain chain k).filter good,
      commonPairWeight chain k H0 H1 js = 0 := by
    intro js hjs
    have hmem := (mem_filter.mp hjs)
    have hnotpos : ¬ 0 < commonPairWeight chain k H0 H1 js := by
      intro hpos
      apply hnone
      exact ⟨js, hmem.1, hmem.2, hpos⟩
    exact le_antisymm (le_of_not_gt hnotpos)
      (commonPairWeight_nonneg chain k H0 H1 js)
  have hgoodSum :
      (∑ js ∈ (commonPairDomain chain k).filter good,
          commonPairWeight chain k H0 H1 js) = 0 := by
    exact sum_eq_zero fun js hjs => hzero js hjs
  have hsplit := sum_filter_add_sum_filter_not
    (commonPairDomain chain k) good
      (commonPairWeight chain k H0 H1)
  have heq : mixedProductSum chain k H0 H1 =
      boundaryLoss chain k H0 H1 := by
    unfold mixedProductSum boundaryLoss
    rw [← hsplit, hgoodSum, zero_add]
  exact (ne_of_lt hmixProduct) heq.symm

/-- The mixed-sum premise constructs equal-index T24 witnesses satisfying all
seven clauses of T28's adjacent compatibility predicate. -/
theorem mixedSumLowerBound_implies_adjacentPairCompatible
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ)
    (hmix : MixedSumLowerBound chain k H0 H1) :
    ∃ j s : ℕ, ∃ a0 a1 : ℤ,
      AdjacentPairCompatible chain k j s j s a0 a1 := by
  obtain ⟨js, hjs, hjoint, _hpositive⟩ :=
    exists_positive_commonPairWeight chain k H0 H1 hmix
  obtain ⟨a0, a1, he0, he1, hbudget⟩ := hjoint
  have hrange := mem_commonPairDomain_iff.mp hjs
  refine ⟨js.1, js.2, a0, a1, ?_⟩
  simp only [AdjacentPairCompatible]
  refine ⟨hrange.2.2.1, hrange.2.2.2.1,
    hrange.2.2.1, hrange.2.2.2.2, he0, he1, ?_⟩
  simpa [pairDenominator] using hbudget

/-- Uniform form of the unproved mixed-sum premise, including the explicit
T28 exponent-eight closing bounds for the pair extracted from the sum. -/
def UniformMixedSumSelection (Q8 J S H0 H1 : ℕ) : Prop :=
  ∀ {M D K d h r : ℕ}, 1 ≤ d → 1 ≤ h → 1 ≤ r →
    ∀ chain : GeometricResonanceChain
        (initialCoefficient h r) M D 1 K d {r},
      (∀ k : Fin (d + 1),
        CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
            (chain.nodeResidual k) ∨
          (¬ CycleApproximation (chain.nodeCoefficient k) (nodeTau D k)
              (chain.nodeResidual k) ∧
            PositivePreperiodApproximation
              (chain.nodeCoefficient k) (nodeTau D k)
                (chain.nodeResidual k))) →
      ∃ k : Fin d, MixedSumLowerBound chain k H0 H1 ∧
        ∀ j s : ℕ, ∀ a0 a1 : ℤ,
          AdjacentPairCompatible chain k j s j s a0 a1 →
            ExponentEightClosingBounds Q8 J S chain k j s j s a0

theorem uniformMixedSumSelection_implies_coherentAdjacentSelection
    (Q8 J S H0 H1 : ℕ)
    (hmix : UniformMixedSumSelection Q8 J S H0 H1) :
    CoherentAdjacentSelection Q8 J S := by
  intro M D K d h r hd hh hr chain hinverse
  obtain ⟨k, hbound, hclosing⟩ := hmix hd hh hr chain hinverse
  obtain ⟨j, s, a0, a1, hcompatible⟩ :=
    mixedSumLowerBound_implies_adjacentPairCompatible
      chain k H0 H1 hbound
  exact ⟨k, j, s, j, s, a0, a1, hcompatible,
    hclosing j s a0 a1 hcompatible⟩

/-- Conditional canonical A1. Both the displayed uniform mixed-sum selection
and exponent-eight irrationality lower bound remain hypotheses. -/
theorem exponentEight_and_uniformMixedSum_imply_canonicalA1
    (Q8 J S H0 H1 : ℕ)
    (hirr : ExponentEightLowerBound Q8)
    (hmix : UniformMixedSumSelection Q8 J S H0 H1) :
    CanonicalA1 := by
  exact exponentEight_and_coherentSelection_imply_canonicalA1 Q8 J S hirr
    (uniformMixedSumSelection_implies_coherentAdjacentSelection
      Q8 J S H0 H1 hmix)

end MixedProductBridge
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.MixedProductBridge.mem_commonPairDomain_iff
#print axioms DecimalFactorComplexity.MixedProductBridge.t24GoodPair_iff_eventuallyPeriodicApproximation
#print axioms DecimalFactorComplexity.MixedProductBridge.mixedProductSum_eq_goodMass_add_boundaryLoss
#print axioms DecimalFactorComplexity.MixedProductBridge.phase_successor_transport
#print axioms DecimalFactorComplexity.MixedProductBridge.mixedProductSum_eq_doubleFrequencySum
#print axioms DecimalFactorComplexity.MixedProductBridge.exists_positive_commonPairWeight
#print axioms DecimalFactorComplexity.MixedProductBridge.mixedSumLowerBound_implies_adjacentPairCompatible
#print axioms DecimalFactorComplexity.MixedProductBridge.uniformMixedSumSelection_implies_coherentAdjacentSelection
#print axioms DecimalFactorComplexity.MixedProductBridge.exponentEight_and_uniformMixedSum_imply_canonicalA1
