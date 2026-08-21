import TheoryLib.PiLacunaryNearReturnSparsity.T34MixedProductBridge
import TheoryLib.PiPositiveDecimalFactorEntropy.T8T8DyadicShellFejer

/-!
# T38: fixed-stratum Fejer spike reduction

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module formalizes a conditional sufficient estimate extracted from the
T36 proof sketch.  The fixed-stratum Fejer spike is a definition and remains
an explicit hypothesis below.  In particular, this file proves no such spike
for `Real.pi`, no unconditional adjacent compatibility, and no canonical-A1
claim.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate Real

namespace DecimalFactorComplexity
namespace FixedStratumFejerSpike

open IteratedLagResonance
open FiniteInverseDichotomy
open SharedResonanceChain
open AdjacentNodeCompatibility
open MixedProductBridge

abbrev phase := Theory.PiDigits.T27.phase
abbrev fejerKernel := Theory.PiDigits.T27.fejerKernel

/-- The minimum of the two residual lengths in T34's common domain. -/
def commonDepth
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) : ℕ :=
  min (chain.nodeResidual k) (chain.nodeResidual (k + 1))

/-- The pairs `(j, ell-j)` in the denominator stratum of total length `ell`. -/
def denominatorStratum (ell : ℕ) : Finset (ℕ × ℕ) :=
  (range ell).image fun j => (j, ell - j)

lemma mem_denominatorStratum_iff {ell : ℕ} {js : ℕ × ℕ} :
    js ∈ denominatorStratum ell ↔
      js.1 + js.2 = ell ∧ 1 ≤ js.2 := by
  constructor
  · rw [denominatorStratum, mem_image]
    rintro ⟨j, hj, rfl⟩
    simp only [mem_range] at hj
    constructor <;> omega
  · rintro ⟨hsum, hs⟩
    rw [denominatorStratum, mem_image]
    refine ⟨js.1, by simp only [mem_range]; omega, ?_⟩
    apply Prod.ext
    · rfl
    · omega

lemma denominatorStratum_card (ell : ℕ) :
    (denominatorStratum ell).card = ell := by
  unfold denominatorStratum
  rw [card_image_of_injective]
  · exact card_range ell
  · intro a b hab
    exact congrArg Prod.fst hab

/-- The union of all strata `ell < L`; the `ell=0` stratum is empty. -/
def stratifiedPairDomain (L : ℕ) : Finset (ℕ × ℕ) :=
  (range L).biUnion denominatorStratum

lemma mem_stratifiedPairDomain_iff {L : ℕ} {js : ℕ × ℕ} :
    js ∈ stratifiedPairDomain L ↔
      1 ≤ js.2 ∧ js.1 + js.2 < L := by
  simp only [stratifiedPairDomain, mem_biUnion, mem_range,
    mem_denominatorStratum_iff]
  constructor
  · rintro ⟨ell, hell, hsum, hs⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hlt⟩
    exact ⟨js.1 + js.2, hlt, rfl, hs⟩

theorem commonPairDomain_eq_stratifiedPairDomain
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) :
    commonPairDomain chain k =
      stratifiedPairDomain (commonDepth chain k) := by
  ext js
  rw [mem_commonPairDomain_iff, mem_stratifiedPairDomain_iff]
  simp only [commonDepth, lt_min_iff]
  omega

/-- The eventually-periodic denominator on a stratum is `10^ell - 10^j`. -/
lemma decimalDenominatorNat_eq_pow_sub_pow (j s : ℕ) :
    decimalDenominatorNat j s = 10 ^ (j + s) - 10 ^ j := by
  simp [decimalDenominatorNat, pow_add, Nat.mul_sub_left_distrib]

lemma pairDenominator_stratum {ell j : ℕ} (hj : j < ell) :
    pairDenominator (j, ell - j) = 10 ^ ell - 10 ^ j := by
  unfold pairDenominator
  rw [decimalDenominatorNat_eq_pow_sub_pow]
  simp only [Nat.add_sub_of_le hj.le]

lemma stratumDenominator_lt_pow {ell j : ℕ} (hj : j < ell) :
    10 ^ ell - 10 ^ j < 10 ^ ell := by
  have hjpow : 10 ^ j ≤ 10 ^ ell :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt hj)
  have hjpos : 0 < 10 ^ j := by positivity
  omega

lemma nine_mul_pow_pred_le_stratumDenominator
    {ell j : ℕ} (hell : 1 ≤ ell) (hj : j < ell) :
    9 * 10 ^ (ell - 1) ≤ 10 ^ ell - 10 ^ j := by
  have hjle : j ≤ ell - 1 := by omega
  have hjpow : 10 ^ j ≤ 10 ^ (ell - 1) :=
    Nat.pow_le_pow_right (by norm_num) hjle
  have hellEq : ell = ell - 1 + 1 := by omega
  rw [hellEq, pow_add]
  norm_num
  omega

lemma stratumDenominator_lt_of_lt
    {ell ell' j j' : ℕ}
    (_hell : 1 ≤ ell) (hj : j < ell) (hj' : j' < ell')
    (hlt : ell < ell') :
    10 ^ ell - 10 ^ j < 10 ^ ell' - 10 ^ j' := by
  have hp1 : 10 ^ ell - 10 ^ j < 10 ^ ell :=
    stratumDenominator_lt_pow hj
  have hindex : ell ≤ ell' - 1 := by omega
  have hp2 : 10 ^ ell ≤ 10 ^ (ell' - 1) :=
    Nat.pow_le_pow_right (by norm_num) hindex
  have hpos : 0 < 10 ^ (ell' - 1) := by positivity
  have hp3 : 10 ^ (ell' - 1) ≤ 9 * 10 ^ (ell' - 1) := by omega
  have hp4 : 9 * 10 ^ (ell' - 1) ≤ 10 ^ ell' - 10 ^ j' :=
    nine_mul_pow_pred_le_stratumDenominator (by omega) hj'
  omega

/-- Distinct legal positive-period pairs have distinct natural denominators. -/
theorem pairDenominator_injective_on_commonPairDomain
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) :
    Set.InjOn pairDenominator (commonPairDomain chain k : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hpMem := mem_commonPairDomain_iff.mp hp
  have hqMem := mem_commonPairDomain_iff.mp hq
  let ellp := p.1 + p.2
  let ellq := q.1 + q.2
  have hpPeriod : 1 ≤ p.2 := hpMem.2.2.1
  have hqPeriod : 1 ≤ q.2 := hqMem.2.2.1
  have hellp : 1 ≤ ellp := by simp only [ellp]; omega
  have hellq : 1 ≤ ellq := by simp only [ellq]; omega
  have hpj : p.1 < ellp := by simp only [ellp]; omega
  have hqj : q.1 < ellq := by simp only [ellq]; omega
  have hformulaP : pairDenominator p = 10 ^ ellp - 10 ^ p.1 := by
    simp only [pairDenominator, decimalDenominatorNat_eq_pow_sub_pow, ellp]
  have hformulaQ : pairDenominator q = 10 ^ ellq - 10 ^ q.1 := by
    simp only [pairDenominator, decimalDenominatorNat_eq_pow_sub_pow, ellq]
  have hell : ellp = ellq := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsep := stratumDenominator_lt_of_lt hellp hpj hqj hlt
      rw [← hformulaP, ← hformulaQ, heq] at hsep
      exact (lt_irrefl _ hsep)
    · have hsep := stratumDenominator_lt_of_lt hellq hqj hpj hgt
      rw [← hformulaQ, ← hformulaP, heq] at hsep
      exact (lt_irrefl _ hsep)
  have hpPowLe : 10 ^ p.1 ≤ 10 ^ ellp :=
    Nat.pow_le_pow_right (by norm_num) hpj.le
  have hqPowLe : 10 ^ q.1 ≤ 10 ^ ellp := by
    rw [hell]
    exact Nat.pow_le_pow_right (by norm_num) hqj.le
  have hpqPow : 10 ^ p.1 = 10 ^ q.1 := by
    have heqSub : 10 ^ ellp - 10 ^ p.1 =
        10 ^ ellq - 10 ^ q.1 := hformulaP.symm.trans (heq.trans hformulaQ)
    rw [hell] at heqSub
    have hpPowLe' : 10 ^ p.1 ≤ 10 ^ ellq := by
      rwa [← hell]
    exact (tsub_right_inj hpPowLe' (Nat.pow_le_pow_right
      (by norm_num) hqj.le)).mp heqSub
  have hpqFirst : p.1 = q.1 :=
    Nat.pow_right_injective (by norm_num : 1 < 10) hpqPow
  apply Prod.ext
  · exact hpqFirst
  · simp only [ellp, ellq] at hell
    omega

/-- Under `U > 2 H0`, the transported frequency `(u,v) ↦ u+Uv` has no
collisions on T34's two rectangular Fourier cutoffs. -/
theorem transportedFrequency_injective
    {H0 H1 U : ℕ} (hsep : 2 * H0 < U) :
    Set.InjOn
      (fun uv : ℤ × ℤ => uv.1 + (U : ℤ) * uv.2)
      (↑(Fourier.signedFrequenciesZero H0 ×ˢ
        Fourier.signedFrequenciesZero H1) : Set (ℤ × ℤ)) := by
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' heq
  have hu := mem_fourierCutoff_iff.mp (mem_product.mp huv).1
  have hu' := mem_fourierCutoff_iff.mp (mem_product.mp huv').1
  have htransport : (U : ℤ) * (v - v') = u' - u := by
    linear_combination heq
  have hright : (u' - u).natAbs ≤ 2 * H0 := by
    calc
      (u' - u).natAbs ≤ u'.natAbs + u.natAbs := Int.natAbs_sub_le _ _
      _ ≤ H0 + H0 := Nat.add_le_add hu' hu
      _ = 2 * H0 := by omega
  have hvEq : v = v' := by
    by_contra hvne
    have hvsub : v - v' ≠ 0 := sub_ne_zero.mpr hvne
    have hvabs : 1 ≤ (v - v').natAbs := by
      exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hvsub)
    have hlower : U ≤ ((U : ℤ) * (v - v')).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right U hvabs
    rw [htransport] at hlower
    exact (not_lt_of_ge hlower) (lt_of_le_of_lt hright hsep)
  have huEq : u = u' := by
    rw [hvEq] at heq
    exact add_right_cancel heq
  exact Prod.ext huEq hvEq

/-- The inverse-square Fejer bound expressed using distance to the nearest
integer.  The constant `4` is inherited from the global sine bound in T14. -/
theorem fejerKernel_le_of_circleDistance_ge
    (H : ℕ) {x delta : ℝ} (hdelta : 0 < delta)
    (hfar : delta ≤ circleDistance x) :
    fejerKernel H x ≤ 1 / (4 * (H + 1 : ℝ) * delta ^ 2) := by
  obtain ⟨z, hz, hzhalf⟩ :=
    DyadicShellFejer.exists_int_circleDistance_eq_abs_le_half x
  let t : ℝ := x - (z : ℝ)
  have hdeltaT : delta ≤ |t| := by simpa only [t, hz] using hfar
  have htpos : 0 < |t| := hdelta.trans_le hdeltaT
  have ht0 : t ≠ 0 := abs_pos.mp htpos
  have hkernel :=
    Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerKernel_le_inverse_square
      H ht0 (by simpa only [t] using hzhalf)
  have hshift : fejerKernel H t = fejerKernel H x := by
    have hp := WeightedFourierReduction.fejerKernel_int_shift H z t
    simpa only [t, sub_add_cancel] using hp.symm
  have hsquare : delta ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_abs t, sq_nonneg (|t| - delta)]
  have hdenDelta : 0 < 4 * (H + 1 : ℝ) * delta ^ 2 := by
    positivity
  have hdenT : 0 < 4 * (H + 1 : ℝ) * t ^ 2 := by
    positivity
  calc
    fejerKernel H x = fejerKernel H t := hshift.symm
    _ ≤ 1 / (4 * (H + 1 : ℝ) * t ^ 2) := hkernel
    _ ≤ 1 / (4 * (H + 1 : ℝ) * delta ^ 2) := by
      apply one_div_le_one_div_of_le hdenDelta
      nlinarith

lemma fejerKernel_zero (x : ℝ) : fejerKernel 0 x = 1 := by
  simp [fejerKernel, Theory.PiDigits.T27.fejerKernel,
    Theory.PiDigits.T27.dirichletKernel, Theory.PiDigits.T27.phase_zero]

lemma commonPairWeight_zero
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (js : ℕ × ℕ) :
    commonPairWeight chain k 0 0 js = 1 := by
  simp [commonPairWeight, smoothNodeWeight, fejerKernel_zero]

lemma commonPairWeight_le_height
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) (js : ℕ × ℕ) :
    commonPairWeight chain k H0 H1 js ≤
      (H0 + 1 : ℝ) * (H1 + 1 : ℝ) := by
  unfold commonPairWeight smoothNodeWeight
  apply mul_le_mul
  · exact Theory.PiDigits.T27.fejerKernel_le _ _
  · exact Theory.PiDigits.T27.fejerKernel_le _ _
  · exact Theory.PiDigits.T27.fejerKernel_nonneg _ _
  · positivity

/-- T36's denominator stratification gives a completely explicit boundary
loss bound.  This robust form retains the exact bad-pair filter on the left
and uses the full Fejer height at every displayed stratum index.  The identity
`pairDenominator_stratum` supplies `10^ell-10^j`.  This is the coarse height
bound, not T36's sharper optimized envelope; no boundary term is discarded. -/
theorem boundaryLoss_le_explicit_stratified_height
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (H0 H1 : ℕ) :
    boundaryLoss chain k H0 H1 ≤
      ∑ ell ∈ range (commonDepth chain k),
        ∑ _j ∈ range ell, (H0 + 1 : ℝ) * (H1 + 1 : ℝ) := by
  classical
  have hgoodNonneg : 0 ≤ commonGoodMass chain k H0 H1 := by
    unfold commonGoodMass
    exact sum_nonneg fun js _ => commonPairWeight_nonneg chain k H0 H1 js
  have hboundaryLe : boundaryLoss chain k H0 H1 ≤
      mixedProductSum chain k H0 H1 := by
    rw [mixedProductSum_eq_goodMass_add_boundaryLoss]
    linarith
  apply hboundaryLe.trans
  unfold mixedProductSum
  rw [commonPairDomain_eq_stratifiedPairDomain, stratifiedPairDomain]
  rw [sum_biUnion]
  · apply sum_le_sum
    intro ell hell
    calc
      (∑ js ∈ denominatorStratum ell,
          commonPairWeight chain k H0 H1 js) ≤
          ∑ _js ∈ denominatorStratum ell,
            (H0 + 1 : ℝ) * (H1 + 1 : ℝ) := by
              apply sum_le_sum
              intro js hjs
              exact commonPairWeight_le_height chain k H0 H1 js
      _ = ∑ _j ∈ range ell,
            (H0 + 1 : ℝ) * (H1 + 1 : ℝ) := by
              simp only [sum_const, nsmul_eq_mul, denominatorStratum_card,
                card_range]
  · intro ell hell ell' hell' hne
    change Disjoint (denominatorStratum ell) (denominatorStratum ell')
    rw [disjoint_left]
    intro js hjs hjs'
    have hs := mem_denominatorStratum_iff.mp hjs
    have hs' := mem_denominatorStratum_iff.mp hjs'
    exact hne (hs.1.symm.trans hs'.1)

/-- The nodewise error threshold appearing literally in T34's good-pair
predicate. -/
def nodeErrorThreshold (D k : ℕ) : ℝ :=
  inverseError (nodeTau D k)

/-- T36's fixed-stratum radius.  The three entries respectively enforce the
left T24 error, transported right T24 error, and mixed budget. -/
def stratumDelta
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) : ℝ :=
  min (nodeErrorThreshold D k)
    (min
      (nodeErrorThreshold D (k + 1) /
        (GeometricResonanceChain.adjacentFactor chain k : ℝ))
      (1 / (2 * (GeometricResonanceChain.adjacentFactor chain k : ℝ) *
        (10 : ℝ) ^ ell)))

/-- The exact integral Fejer order `ceil(delta⁻¹)` from T36. -/
def stratumOrder
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) : ℕ :=
  Nat.ceil ((stratumDelta chain k ell)⁻¹)

lemma nodeErrorThreshold_pos (D k : ℕ) (hD : 1 ≤ D) :
    0 < nodeErrorThreshold D k := by
  have hdenNat := densityDenominator_pos D k hD
  have hden : (1 : ℝ) ≤ densityDenominator D k := by exact_mod_cast hdenNat
  have htauLt : nodeTau D k < 1 := by
    rw [nodeTau_explicit]
    have hlocal : 1 / (8 * (densityDenominator D k : ℝ) ^ 2) <
        1 / (1 : ℝ) := by
      apply one_div_lt_one_div_of_lt (by norm_num)
      nlinarith [sq_nonneg ((densityDenominator D k : ℝ) - 1)]
    simpa using hlocal
  unfold nodeErrorThreshold inverseError
  exact div_pos (Real.arccos_pos.mpr htauLt) (by positivity)

lemma stratumDelta_pos
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) (hD : 1 ≤ D) :
    0 < stratumDelta chain k ell := by
  have hU := adjacentFactor_pos chain k
  have hUR : (0 : ℝ) < GeometricResonanceChain.adjacentFactor chain k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
  unfold stratumDelta
  exact lt_min (nodeErrorThreshold_pos D k hD)
    (lt_min (div_pos (nodeErrorThreshold_pos D (k + 1) hD) hUR) (by positivity))

lemma stratumOrder_pos
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) (hD : 1 ≤ D) :
    1 ≤ stratumOrder chain k ell := by
  have hdelta := stratumDelta_pos chain k ell hD
  unfold stratumOrder
  have hceil : 0 < Nat.ceil ((stratumDelta chain k ell)⁻¹) := by
    rw [Nat.ceil_pos]
    positivity
  omega

/-- **Fixed-Stratum Fejer Spike (FSFS).**  This is the sole unproved analytic
hypothesis.  It is stated at one legal stratum and one genuine T26/T34 node;
the phase therefore remains the fixed coefficient `C*pi`. -/
def FSFS
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) : Prop :=
  1 ≤ D ∧ 1 ≤ ell ∧ ell < commonDepth chain k ∧
    (ell : ℝ) /
        (4 * (stratumOrder chain k ell : ℝ) *
          (stratumDelta chain k ell) ^ 2) <
      ∑ j ∈ range ell,
        fejerKernel (stratumOrder chain k ell - 1)
          (chain.nodeCoefficient k *
            ((10 : ℝ) ^ ell - (10 : ℝ) ^ j))

/-- FSFS forces one denominator in its displayed stratum to lie within the
explicit radius of an integer. -/
theorem FSFS.exists_stratum_circleDistance_lt
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} (hspike : FSFS chain k ell) :
    ∃ j ∈ range ell,
      circleDistance
        (chain.nodeCoefficient k *
          ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) <
        stratumDelta chain k ell := by
  classical
  rcases hspike with ⟨hD, hellPos, hellDepth, hspike⟩
  let delta := stratumDelta chain k ell
  let R := stratumOrder chain k ell
  have hdelta : 0 < delta := stratumDelta_pos chain k ell hD
  have hR : 1 ≤ R := stratumOrder_pos chain k ell hD
  by_contra hnone
  push Not at hnone
  have hpoint : ∀ j ∈ range ell,
      fejerKernel (R - 1)
          (chain.nodeCoefficient k *
            ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) ≤
        1 / (4 * (R : ℝ) * delta ^ 2) := by
    intro j hj
    have hfar : delta ≤ circleDistance
        (chain.nodeCoefficient k *
          ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) :=
      hnone j hj
    have hbound := fejerKernel_le_of_circleDistance_ge (R - 1) hdelta hfar
    have hcast : (((R - 1 : ℕ) : ℝ) + 1) = (R : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hR
    simpa only [Nat.cast_add, Nat.cast_one, hcast] using hbound
  have hsum :
      (∑ j ∈ range ell,
        fejerKernel (R - 1)
          (chain.nodeCoefficient k *
            ((10 : ℝ) ^ ell - (10 : ℝ) ^ j))) ≤
        (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) := by
    calc
      (∑ j ∈ range ell,
          fejerKernel (R - 1)
            (chain.nodeCoefficient k *
              ((10 : ℝ) ^ ell - (10 : ℝ) ^ j))) ≤
          ∑ _j ∈ range ell, 1 / (4 * (R : ℝ) * delta ^ 2) := by
            exact sum_le_sum fun j hj => hpoint j hj
      _ = (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
  change (ell : ℝ) / (4 * (R : ℝ) * delta ^ 2) < _ at hspike
  exact (not_lt_of_ge hsum) hspike

/-- The close denominator supplied by FSFS is a T34 jointly good pair.  The
right integer is explicitly transported as `a1 = U*a0`. -/
theorem FSFS.exists_jointGoodPair
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} (hspike : FSFS chain k ell) :
    ∃ js ∈ commonPairDomain chain k, JointGoodPair chain k js := by
  classical
  have hdata := hspike
  rcases hdata with ⟨hD, hellPos, hellDepth, _hstrict⟩
  obtain ⟨j, hjRange, hnear⟩ := hspike.exists_stratum_circleDistance_lt
  have hj : j < ell := mem_range.mp hjRange
  let s := ell - j
  let U := GeometricResonanceChain.adjacentFactor chain k
  let beta0 := chain.nodeCoefficient k
  let delta := stratumDelta chain k ell
  have hs : 1 ≤ s := by simp only [s]; omega
  have hsum : j + s = ell := by simp only [s]; omega
  have hU : 1 ≤ U := adjacentFactor_pos chain k
  have hUR : (0 : ℝ) < U := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
  have hdelta : 0 < delta := stratumDelta_pos chain k ell hD
  have hpowNat : 10 ^ j ≤ 10 ^ ell :=
    Nat.pow_le_pow_right (by norm_num) hj.le
  have hqCast : (pairDenominator (j, s) : ℝ) =
      (10 : ℝ) ^ ell - (10 : ℝ) ^ j := by
    rw [pairDenominator_stratum hj, Nat.cast_sub hpowNat,
      Nat.cast_pow, Nat.cast_pow]
    norm_num
  have hnear' : circleDistance
      ((pairDenominator (j, s) : ℝ) * beta0) < delta := by
    simpa only [beta0, delta, hqCast, mul_comm] using hnear
  obtain ⟨a0, ha0⟩ :=
    WeightedFourierReduction.exists_int_abs_sub_lt_of_circleDistance_lt hnear'
  let a1 : ℤ := (U : ℤ) * a0
  have he0Delta : scaledIntegerError beta0 j s a0 < delta := by
    simpa only [scaledIntegerError, pairDenominator, beta0] using ha0
  have hdeltaLeft : delta ≤ nodeErrorThreshold D k := by
    exact min_le_left _ _
  have hdeltaRight : delta ≤ nodeErrorThreshold D (k + 1) / (U : ℝ) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaBudget : delta ≤ 1 / (2 * (U : ℝ) * (10 : ℝ) ^ ell) := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have he0 : scaledIntegerError beta0 j s a0 < inverseError (nodeTau D k) := by
    exact he0Delta.trans_le hdeltaLeft
  have heTransport :
      scaledIntegerError (chain.nodeCoefficient (k + 1)) j s a1 =
        (U : ℝ) * scaledIntegerError beta0 j s a0 := by
    unfold scaledIntegerError a1 beta0
    rw [GeometricResonanceChain.nodeCoefficient_succ]
    push_cast
    change
      |(pairDenominator (j, s) : ℝ) *
            ((U : ℝ) * chain.nodeCoefficient k) - (U : ℝ) * (a0 : ℝ)| =
        (U : ℝ) *
          |(pairDenominator (j, s) : ℝ) * chain.nodeCoefficient k -
            (a0 : ℝ)|
    rw [show
      (pairDenominator (j, s) : ℝ) *
            ((U : ℝ) * chain.nodeCoefficient k) - (U : ℝ) * (a0 : ℝ) =
          (U : ℝ) *
            ((pairDenominator (j, s) : ℝ) * chain.nodeCoefficient k -
              (a0 : ℝ)) by ring,
      abs_mul, abs_of_pos hUR]
  have he1 : scaledIntegerError (chain.nodeCoefficient (k + 1)) j s a1 <
      inverseError (nodeTau D (k + 1)) := by
    rw [heTransport]
    calc
      (U : ℝ) * scaledIntegerError beta0 j s a0 < (U : ℝ) * delta :=
        mul_lt_mul_of_pos_left he0Delta hUR
      _ ≤ nodeErrorThreshold D (k + 1) :=
        by simpa [mul_comm] using (le_div_iff₀ hUR).mp hdeltaRight
  have hqNatPos : 1 ≤ pairDenominator (j, s) :=
    decimalDenominatorNat_pos hs
  have hqPos : (0 : ℝ) < pairDenominator (j, s) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNatPos)
  have hqLtNat : pairDenominator (j, s) < 10 ^ ell := by
    rw [pairDenominator_stratum hj]
    exact stratumDenominator_lt_pow hj
  have hqLt : (pairDenominator (j, s) : ℝ) < (10 : ℝ) ^ ell := by
    exact_mod_cast hqLtNat
  have hqErrorLt :
      (pairDenominator (j, s) : ℝ) * scaledIntegerError beta0 j s a0 <
        (10 : ℝ) ^ ell * delta := by
    calc
      (pairDenominator (j, s) : ℝ) * scaledIntegerError beta0 j s a0 ≤
          (pairDenominator (j, s) : ℝ) * delta :=
        mul_le_mul_of_nonneg_left he0Delta.le hqPos.le
      _ < (10 : ℝ) ^ ell * delta :=
        mul_lt_mul_of_pos_right hqLt hdelta
  have hscaledBudget :
      2 * (U : ℝ) * (pairDenominator (j, s) : ℝ) *
          scaledIntegerError beta0 j s a0 < 1 := by
    have hstrict :
        2 * (U : ℝ) *
            ((pairDenominator (j, s) : ℝ) *
              scaledIntegerError beta0 j s a0) <
          2 * (U : ℝ) * ((10 : ℝ) ^ ell * delta) :=
      mul_lt_mul_of_pos_left hqErrorLt (by positivity)
    have hupper : 2 * (U : ℝ) * ((10 : ℝ) ^ ell * delta) ≤ 1 := by
      calc
        2 * (U : ℝ) * ((10 : ℝ) ^ ell * delta) =
            (2 * (U : ℝ) * (10 : ℝ) ^ ell) * delta := by ring
        _ ≤ (2 * (U : ℝ) * (10 : ℝ) ^ ell) *
            (1 / (2 * (U : ℝ) * (10 : ℝ) ^ ell)) :=
          mul_le_mul_of_nonneg_left hdeltaBudget (by positivity)
        _ = 1 := by field_simp
    nlinarith
  have hdomain : (j, s) ∈ commonPairDomain chain k := by
    apply mem_commonPairDomain_iff.mpr
    have hdepth := lt_min_iff.mp hellDepth
    exact ⟨by omega, by omega, hs, by omega, by omega⟩
  refine ⟨(j, s), hdomain, a0, a1, he0, he1, ?_⟩
  rw [heTransport]
  nlinarith [hscaledBudget]

/-- A jointly good legal pair at zero cutoffs is exactly enough for T34's
strict mixed-sum premise. -/
theorem jointGoodPair_implies_mixedSumLowerBound_zero
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d)
    (hjoint : ∃ js ∈ commonPairDomain chain k,
      JointGoodPair chain k js) :
    MixedSumLowerBound chain k 0 0 := by
  classical
  obtain ⟨js, hjs, hgood⟩ := hjoint
  have hmem : js ∈ (commonPairDomain chain k).filter
      (JointGoodPair chain k) := mem_filter.mpr ⟨hjs, hgood⟩
  have hmass : 0 < commonGoodMass chain k 0 0 := by
    unfold commonGoodMass
    have hle : commonPairWeight chain k 0 0 js ≤
        ∑ x ∈ (commonPairDomain chain k).filter (JointGoodPair chain k),
          commonPairWeight chain k 0 0 x :=
      single_le_sum
        (fun x _ => commonPairWeight_nonneg chain k 0 0 x) hmem
    rw [commonPairWeight_zero] at hle
    exact zero_lt_one.trans_le hle
  unfold MixedSumLowerBound
  rw [← mixedProductSum_eq_doubleFrequencySum]
  simp only [Complex.ofReal_re]
  rw [mixedProductSum_eq_goodMass_add_boundaryLoss]
  linarith

/-- FSFS implies T34's common-pair mixed-sum hypothesis, but FSFS itself
remains assumed. -/
theorem FSFS.implies_mixedSumLowerBound_zero
    {M D K d h r ell : ℕ}
    {chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r}}
    {k : Fin d} (hspike : FSFS chain k ell) :
    MixedSumLowerBound chain k 0 0 :=
  jointGoodPair_implies_mixedSumLowerBound_zero chain k
    hspike.exists_jointGoodPair

/-- The one-dimensional base-10 lacunary sum left after factoring the
The constant `10^ell` phase from a denominator stratum. -/
def lacunaryPhaseSum (beta : ℝ) (ell : ℕ) (u : ℤ) : ℂ :=
  ∑ j ∈ range ell, phase (-u) (beta * (10 : ℝ) ^ j)

/-- The fully displayed finite Fourier expression for a stratum Fejer sum.
The support is `|u| ≤ R-1` and the weight is exactly `1-|u|/R`. -/
def lacunaryExpansion (beta : ℝ) (ell R : ℕ) : ℂ :=
  ∑ u ∈ Fourier.signedFrequenciesZero (R - 1),
    (((1 - (u.natAbs : ℝ) / (R : ℝ) : ℝ)) : ℂ) *
      phase u (beta * (10 : ℝ) ^ ell) *
        lacunaryPhaseSum beta ell u

lemma phase_stratum_factorization
    (beta : ℝ) (ell j : ℕ) (u : ℤ) :
    phase u (beta * ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) =
      phase u (beta * (10 : ℝ) ^ ell) *
        phase (-u) (beta * (10 : ℝ) ^ j) := by
  unfold phase Theory.PiDigits.T27.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact one-dimensional expansion, with no asymptotic or cancellation
claim. -/
theorem stratumFejerSum_eq_lacunaryExpansion
    (beta : ℝ) (ell R : ℕ) (hR : 1 ≤ R) :
    ((∑ j ∈ range ell,
        fejerKernel (R - 1)
          (beta * ((10 : ℝ) ^ ell - (10 : ℝ) ^ j)) : ℝ) : ℂ) =
      lacunaryExpansion beta ell R := by
  classical
  have hcast : (((R - 1 : ℕ) : ℝ) + 1) = (R : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hR
  have hcoefficient (u : ℤ) :
      Fourier.triangularCoefficient (R - 1) u =
        1 - (u.natAbs : ℝ) / (R : ℝ) := by
    rw [triangularCoefficient_explicit]
    exact congrArg (fun x : ℝ => 1 - (u.natAbs : ℝ) / x) hcast
  push_cast
  simp_rw [Theory.PiDigits.BoundaryRobustFejerDichotomy.fejerKernel_eq_aggregated]
  rw [sum_comm]
  unfold lacunaryExpansion lacunaryPhaseSum
  apply sum_congr rfl
  intro u hu
  have hc :
      Theory.PiDigits.BoundaryRobustFejerDichotomy.triangularCoefficient
          (R - 1) u = 1 - (u.natAbs : ℝ) / (R : ℝ) :=
    hcoefficient u
  simp_rw [hc]
  simp_rw [phase_stratum_factorization]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-- FSFS written solely as its explicit one-dimensional signed-frequency
expansion.  This remains a predicate, not an assertion for `pi`. -/
def ExpandedFSFS
    {M D K d h r : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) (ell : ℕ) : Prop :=
  1 ≤ D ∧ 1 ≤ ell ∧ ell < commonDepth chain k ∧
    (ell : ℝ) /
        (4 * (stratumOrder chain k ell : ℝ) *
          (stratumDelta chain k ell) ^ 2) <
      (lacunaryExpansion (chain.nodeCoefficient k) ell
        (stratumOrder chain k ell)).re

/-- The named FSFS hypothesis is exactly, not merely implied by, the
displayed collection of one-dimensional base-10 lacunary sums. -/
theorem fsfs_iff_expandedFSFS
    {M D K d h r ell : ℕ}
    (chain : GeometricResonanceChain
      (initialCoefficient h r) M D 1 K d {r})
    (k : Fin d) :
    FSFS chain k ell ↔ ExpandedFSFS chain k ell := by
  constructor
  · rintro hfsfs
    rcases hfsfs with ⟨hD, hell, hdepth, hsum⟩
    refine ⟨hD, hell, hdepth, ?_⟩
    have hR := stratumOrder_pos chain k ell hD
    have hexpansion := stratumFejerSum_eq_lacunaryExpansion
      (chain.nodeCoefficient k) ell (stratumOrder chain k ell) hR
    have hre := congrArg Complex.re hexpansion
    simp only [Complex.ofReal_re] at hre
    rwa [← hre]
  · rintro hexpanded
    rcases hexpanded with ⟨hD, hell, hdepth, hsum⟩
    refine ⟨hD, hell, hdepth, ?_⟩
    have hR := stratumOrder_pos chain k ell hD
    have hexpansion := stratumFejerSum_eq_lacunaryExpansion
      (chain.nodeCoefficient k) ell (stratumOrder chain k ell) hR
    have hre := congrArg Complex.re hexpansion
    simp only [Complex.ofReal_re] at hre
    rwa [hre]

end FixedStratumFejerSpike
end DecimalFactorComplexity

#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.commonPairDomain_eq_stratifiedPairDomain
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.pairDenominator_injective_on_commonPairDomain
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.transportedFrequency_injective
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.fejerKernel_le_of_circleDistance_ge
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.boundaryLoss_le_explicit_stratified_height
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.FSFS.exists_stratum_circleDistance_lt
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.FSFS.exists_jointGoodPair
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.jointGoodPair_implies_mixedSumLowerBound_zero
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.FSFS.implies_mixedSumLowerBound_zero
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.stratumFejerSum_eq_lacunaryExpansion
#print axioms DecimalFactorComplexity.FixedStratumFejerSpike.fsfs_iff_expandedFSFS
