import TheoryLib.PiLongLagBlockCollisionDecay.T2T2UniformLongLagResidual
import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiPositiveDecimalFactorEntropy.T7T7FejerSpectralCriterion

/-!
# T8: a collision-independent spectral target for long residual pairs

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

The domain below depends only on the finite index ranges and T2's arithmetic
exclusion predicate. It does not use decimal-block equality, near-return
membership, `longResidualPairCount`, or any conclusion-equivalent clause.

The external assertion `mu(pi) < 8` remains the explicit T4 hypothesis
`IrrationalityMeasureBelow Real.pi 8`. No spectral estimate for pi is asserted.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T8

open DecimalFactorComplexity
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.LagDecomposition
open DecimalFactorComplexity.WeightedFourierReduction
open Theory.PiDigits.BoundaryRobustFejerDichotomy
open Theory.PiDigits.LongLagBlockCollisionDecay
open Theory.PiDigits.LongLagBlockCollisionDecay.T2
open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Theory.PiDigits.PositiveLowerBlockDensity.T25
open Theory.PiDigits.PositiveLowerBlockDensity.T26

/-- The exact decimal frequency scale. -/
def decimalFrequency (m : ℕ) : ℕ := 10 ^ m

/-- Half the decimal frequency. The Fejer kernel below has order one less than
this number, so its signed frequencies satisfy `|h| < halfFrequency m`. -/
def halfFrequency (m : ℕ) : ℕ := decimalFrequency m / 2

/-- A core records a positive long lag and its smaller starting index. -/
abbrev LongPairCore := Σ _lag : ℕ, ℕ

/-- An orientation and a `(lag,start)` core. `false` denotes `(start,start+lag)`
and `true` denotes the reverse ordered pair. -/
abbrev OrderedLongPair := Bool × LongPairCore

/-- First coordinate of the represented ordered pair. -/
def orderedFirst (q : OrderedLongPair) : ℕ :=
  if q.1 then q.2.2 + q.2.1 else q.2.2

/-- Second coordinate of the represented ordered pair. -/
def orderedSecond (q : OrderedLongPair) : ℕ :=
  if q.1 then q.2.2 else q.2.2 + q.2.1

/-- `Q(mu,c,Q0,m,N)`: both orientations of every long-lag pair which survives
T2's arithmetic exclusion. This definition is collision-independent: neither
block equality nor circle-nearness occurs in it. -/
def orderedLongPairDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset OrderedLongPair := by
  classical
  exact (Finset.univ : Finset Bool).product
    ((longResidualLags m N).sigma fun r =>
      (Finset.range (N - r)).filter fun n =>
        ¬ ArithmeticExcluded μ c Q0 m n r)

/-- Complete endpoint and exclusion audit for membership in `Q`. -/
theorem mem_orderedLongPairDomain_iff
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair} :
    q ∈ orderedLongPairDomain μ c Q0 m N ↔
      0 < q.2.1 ∧ m ≤ q.2.1 ∧ q.2.1 < N ∧
        q.2.2 < N - q.2.1 ∧
          ¬ ArithmeticExcluded μ c Q0 m q.2.2 q.2.1 := by
  classical
  change q ∈ (Finset.univ : Finset Bool).product
      ((longResidualLags m N).sigma fun r =>
        (Finset.range (N - r)).filter fun n =>
          ¬ ArithmeticExcluded μ c Q0 m n r) ↔ _
  constructor
  · intro hq
    have hparts := (Finset.mem_product).mp hq
    have hcore := (Finset.mem_sigma).mp hparts.2
    have hstart := (Finset.mem_filter).mp hcore.2
    have hlag := mem_longResidualLags_iff.mp hcore.1
    exact ⟨hlag.1, hlag.2.1, hlag.2.2,
      Finset.mem_range.mp hstart.1, hstart.2⟩
  · rintro ⟨hr0, hmr, hrN, hn, hnot⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_sigma.mpr ?_⟩
    exact ⟨mem_longResidualLags_iff.mpr ⟨hr0, hmr, hrN⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hnot⟩⟩

/-- The requested phase argument `(10^a-10^b)*pi`, with the ordered
coordinates represented by `q`. -/
def orderedPhaseArgument (q : OrderedLongPair) : ℝ :=
  ((10 : ℝ) ^ orderedFirst q - (10 : ℝ) ^ orderedSecond q) * Real.pi

/-- The signed-frequency exponential sum over the collision-independent
domain. -/
def signedSpectralSum
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) : ℂ :=
  ∑ q ∈ orderedLongPairDomain μ c Q0 m N,
    Theory.PiDigits.T27.phase h (orderedPhaseArgument q)

/-- The requested positive-frequency sum. -/
def spectralSum
    (μ c : ℝ) (Q0 m N h : ℕ) : ℂ :=
  signedSpectralSum μ c Q0 m N (h : ℤ)

/-- Literal exponential expansion of `S_h`; the second occurrence of `pi` is
the fixed number whose decimal orbit is being tested. -/
theorem spectralSum_eq_exp
    (μ c : ℝ) (Q0 m N h : ℕ) :
    spectralSum μ c Q0 m N h =
      ∑ q ∈ orderedLongPairDomain μ c Q0 m N,
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
            ((((10 : ℝ) ^ orderedFirst q -
              (10 : ℝ) ^ orderedSecond q) * Real.pi : ℝ) : ℂ)) := by
  rfl

/-- Signed frequencies have the same norm as their positive absolute
frequencies. -/
theorem norm_signedSpectralSum_eq_natAbs
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) :
    ‖signedSpectralSum μ c Q0 m N h‖ =
      ‖spectralSum μ c Q0 m N h.natAbs‖ := by
  classical
  by_cases hh : 0 ≤ h
  · unfold spectralSum
    rw [Int.natAbs_of_nonneg hh]
  · have hhneg : h < 0 := lt_of_not_ge hh
    have heq : h = -((h.natAbs : ℕ) : ℤ) :=
      Int.eq_neg_natAbs_of_nonpos hhneg.le
    have hconj :
        signedSpectralSum μ c Q0 m N (-((h.natAbs : ℕ) : ℤ)) =
          conj (signedSpectralSum μ c Q0 m N ((h.natAbs : ℕ) : ℤ)) := by
      unfold signedSpectralSum
      simp_rw [Theory.PiDigits.T27.phase_neg]
      rw [map_sum]
    rw [heq, hconj, Complex.norm_conj]
    simp [spectralSum]

/-- The zero mode is the cardinality of `Q`. -/
theorem signedSpectralSum_zero
    (μ c : ℝ) (Q0 m N : ℕ) :
    signedSpectralSum μ c Q0 m N 0 =
      (orderedLongPairDomain μ c Q0 m N).card := by
  simp [signedSpectralSum, Theory.PiDigits.T27.phase_zero]

/-- The unweighted positive-frequency energy, with the inclusive range
`1 <= h <= H_m = 10^m` exactly visible. -/
def positiveSpectralEnergy
    (μ c : ℝ) (Q0 m N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖spectralSum μ c Q0 m N h‖ ^ 2

/-- The uniform spectral hypothesis. One nonnegative `K` is chosen before all
positive `m,N`. It mentions only the collision-independent domain and its
exponential sums. -/
def UniformSpectralEnergyBound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
      positiveSpectralEnergy μ c Q0 m N ≤
        K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2

/-- Quantifier audit for the spectral hypothesis. -/
theorem uniformSpectralEnergyBound_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    UniformSpectralEnergyBound μ c Q0 ↔
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          positiveSpectralEnergy μ c Q0 m N ≤
            K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2 := by
  rfl

/-- T2's strict residual near returns, now selected from the independent
domain. This definition is used only in proofs, never in the spectral
hypothesis. The radius is exactly `10^(-m)` and the strict inequality preserves
the half-open decimal-cylinder boundary convention imported by T2. -/
def residualPairsInsideDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset OrderedLongPair :=
  (orderedLongPairDomain μ c Q0 m N).filter fun q =>
    circleDistance
      ((10 : ℝ) ^ q.2.2 * ((10 : ℝ) ^ q.2.1 - 1) * Real.pi) <
        ((10 : ℝ) ^ m)⁻¹

/-- Both orientations in `Q` reproduce exactly T2's ordered residual count. -/
theorem residualPairsInsideDomain_card
    (μ c : ℝ) (Q0 m N : ℕ) :
    (residualPairsInsideDomain μ c Q0 m N).card =
      longResidualPairCount μ c Q0 m N := by
  classical
  have hset : residualPairsInsideDomain μ c Q0 m N =
      (Finset.univ : Finset Bool).product
        ((longResidualLags m N).sigma fun r =>
          residualNearReturnStarts μ c Q0 m N r) := by
    ext q
    simp [residualPairsInsideDomain, orderedLongPairDomain,
      residualNearReturnStarts, nearReturnStarts]
    tauto
  rw [hset]
  calc
    ((Finset.univ : Finset Bool).product
        ((longResidualLags m N).sigma fun r =>
          residualNearReturnStarts μ c Q0 m N r)).card =
        (Finset.univ : Finset Bool).card *
          ((longResidualLags m N).sigma fun r =>
            residualNearReturnStarts μ c Q0 m N r).card :=
      Finset.card_product _ _
    _ = 2 * ∑ r ∈ longResidualLags m N,
          (residualNearReturnStarts μ c Q0 m N r).card := by
      rw [Finset.card_sigma]
      norm_num
    _ = longResidualPairCount μ c Q0 m N := by
      rfl

/-- Every member of `Q` represents two indices in `{0,...,N-1}`. -/
theorem ordered_coordinates_lt
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair}
    (hq : q ∈ orderedLongPairDomain μ c Q0 m N) :
    orderedFirst q < N ∧ orderedSecond q < N := by
  classical
  change q ∈ (Finset.univ : Finset Bool).product
    ((longResidualLags m N).sigma fun r =>
      (Finset.range (N - r)).filter fun n =>
        ¬ ArithmeticExcluded μ c Q0 m n r) at hq
  have hparts := (Finset.mem_product).mp hq
  have hcore := hparts.2
  have hcoreParts := (Finset.mem_sigma).mp hcore
  have hn := hcoreParts.2
  have hnParts := (Finset.mem_filter).mp hn
  have hnlt := Finset.mem_range.mp hnParts.1
  have hsum : q.2.2 + q.2.1 < N := by omega
  simp only [orderedFirst, orderedSecond]
  split <;> omega

/-- A coarse collision-independent cardinality bound. The factor two records
the two ordered orientations explicitly. -/
theorem orderedLongPairDomain_card_le_two_sq
    (μ c : ℝ) (Q0 m N : ℕ) :
    (orderedLongPairDomain μ c Q0 m N).card ≤ 2 * N ^ 2 := by
  classical
  unfold orderedLongPairDomain
  have hsum :
      (∑ r ∈ longResidualLags m N,
          ((Finset.range (N - r)).filter fun n =>
            ¬ ArithmeticExcluded μ c Q0 m n r).card) ≤
        ∑ _r ∈ longResidualLags m N, N := by
    apply Finset.sum_le_sum
    intro r _hr
    exact (Finset.card_filter_le _ _).trans
      ((Finset.card_range (N - r)).le.trans (Nat.sub_le N r))
  have hlags : (longResidualLags m N).card ≤ N := by
    calc
      (longResidualLags m N).card ≤ (Finset.range N).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_range]
        exact (mem_longResidualLags_iff.mp hr).2.2
      _ = N := Finset.card_range N
  calc
    ((Finset.univ : Finset Bool).product
        ((longResidualLags m N).sigma fun r =>
          (Finset.range (N - r)).filter fun n =>
            ¬ ArithmeticExcluded μ c Q0 m n r)).card =
        (Finset.univ : Finset Bool).card *
          ((longResidualLags m N).sigma fun r =>
            (Finset.range (N - r)).filter fun n =>
              ¬ ArithmeticExcluded μ c Q0 m n r).card :=
      Finset.card_product _ _
    _ = (Finset.univ : Finset Bool).card *
        (∑ r ∈ longResidualLags m N,
          ((Finset.range (N - r)).filter fun n =>
            ¬ ArithmeticExcluded μ c Q0 m n r).card) := by
      rw [Finset.card_sigma]
    _ =
        2 * (∑ r ∈ longResidualLags m N,
          ((Finset.range (N - r)).filter fun n =>
            ¬ ArithmeticExcluded μ c Q0 m n r).card) := by norm_num
    _ ≤ 2 * (∑ _r ∈ longResidualLags m N, N) :=
      Nat.mul_le_mul_left 2 hsum
    _ = 2 * ((longResidualLags m N).card * N) := by simp
    _ ≤ 2 * (N * N) := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right N hlags)
    _ = 2 * N ^ 2 := by ring

/-- The scaled order-`H_m/2-1` Fejer kernel used as the trigonometric
majorant. -/
def nearReturnMajorant (m : ℕ) (x : ℝ) : ℝ :=
  Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
    Theory.PiDigits.T27.fejerKernel (halfFrequency m - 1) x

/-- Every signed Fourier coefficient of the majorant, including the zero
coefficient. Outside `|h| < H_m/2` it is zero. -/
def majorantCoefficient (m : ℕ) (h : ℤ) : ℝ :=
  if h.natAbs < halfFrequency m then
    Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
      (1 - (h.natAbs : ℝ) / (halfFrequency m : ℝ))
  else 0

/-- The zero-frequency coefficient is exactly `pi^2/(2H_m)`. -/
theorem majorantCoefficient_zero (m : ℕ) (hm : 1 ≤ m) :
    majorantCoefficient m 0 =
      Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) := by
  have hhalf : 0 < halfFrequency m := by
    unfold halfFrequency decimalFrequency
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one]
    have hk : 0 < 10 ^ k := pow_pos (by norm_num) k
    omega
  simp [majorantCoefficient, hhalf]

/-- Exact finite Fourier expansion of the majorant. -/
theorem nearReturnMajorant_eq_trigonometricPolynomial
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (nearReturnMajorant m x : ℂ) =
      ∑ h ∈ fejerFrequencies (halfFrequency m),
        (majorantCoefficient m h : ℂ) * Theory.PiDigits.T27.phase h x := by
  have hhalf : 1 ≤ halfFrequency m := by
    unfold halfFrequency decimalFrequency
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one]
    have hk : 0 < 10 ^ k := pow_pos (by norm_num) k
    omega
  rw [nearReturnMajorant]
  push_cast
  rw [fejerKernel_eq_aggregated, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h.natAbs < halfFrequency m :=
    (mem_fejerFrequencies_iff hhalf).mp hh
  rw [triangularCoefficient_pred_eq_fejerWeight
    (halfFrequency m) h hhalf]
  simp only [majorantCoefficient, hh', ↓reduceIte, fejerWeight]
  push_cast
  ring

/-- Pointwise majorization at the strict decimal circle radius. Equality at
the circle boundary is deliberately not counted. -/
theorem strictCircleIndicator_le_majorant
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (if circleDistance x < ((10 : ℝ) ^ m)⁻¹ then (1 : ℝ) else 0) ≤
      nearReturnMajorant m x := by
  have hhalf : 1 ≤ halfFrequency m := by
    unfold halfFrequency decimalFrequency
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one]
    have hk : 0 < 10 ^ k := pow_pos (by norm_num) k
    omega
  have hdoubleNat : 2 * halfFrequency m = decimalFrequency m := by
    exact two_mul_half_ten_pow m hm
  have hdoubleReal : 2 * (halfFrequency m : ℝ) =
      (decimalFrequency m : ℝ) := by
    exact_mod_cast hdoubleNat
  have hfreqCast : (decimalFrequency m : ℝ) = (10 : ℝ) ^ m := by
    simp [decimalFrequency]
  have hhalfPos : (0 : ℝ) < halfFrequency m := by exact_mod_cast hhalf
  split_ifs with hx
  · have hx' : circleDistance x <
        (2 * (halfFrequency m : ℝ))⁻¹ := by
      rw [hdoubleReal, hfreqCast]
      exact hx
    have hk := fejerKernel_pred_lower_of_circleDistance_lt
      (halfFrequency m) hhalf x hx'
    have hscale : 0 ≤ Real.pi ^ 2 /
        (2 * (decimalFrequency m : ℝ)) := by positivity
    unfold nearReturnMajorant
    calc
      (1 : ℝ) =
          (Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ))) *
            (4 * (halfFrequency m : ℝ) / Real.pi ^ 2) := by
        rw [← hdoubleReal]
        field_simp [Real.pi_ne_zero, ne_of_gt hhalfPos]
        ring
      _ ≤ Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          Theory.PiDigits.T27.fejerKernel (halfFrequency m - 1) x :=
        mul_le_mul_of_nonneg_left hk hscale
  · unfold nearReturnMajorant
    exact mul_nonneg (by positivity)
      (Theory.PiDigits.T27.fejerKernel_nonneg _ _)

/-- A residual core is a strict near return for the represented ordered phase,
for either orientation. -/
theorem orderedPhaseArgument_near
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair}
    (hq : q ∈ residualPairsInsideDomain μ c Q0 m N) :
    circleDistance (orderedPhaseArgument q) < ((10 : ℝ) ^ m)⁻¹ := by
  classical
  have hnear := (Finset.mem_filter.mp hq).2
  rcases q with ⟨b, ⟨r, n⟩⟩
  change circleDistance
      ((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) <
        ((10 : ℝ) ^ m)⁻¹ at hnear
  have hfactor := pow_lag_factorization Real.pi n r
  cases b with
  | false =>
      have harg :
          ((10 : ℝ) ^ n - (10 : ℝ) ^ (n + r)) * Real.pi =
            -((10 : ℝ) ^ n * ((10 : ℝ) ^ r - 1) * Real.pi) := by
        rw [← hfactor]
        ring
      simp only [orderedPhaseArgument, orderedFirst, orderedSecond, Bool.false_eq_true,
        ↓reduceIte]
      rw [harg, circleDistance_neg]
      exact hnear
  | true =>
      simp only [orderedPhaseArgument, orderedFirst, orderedSecond, ↓reduceIte]
      rw [hfactor]
      exact hnear

/-- Exact double-frequency expansion of the Fejer sum over `Q`. -/
theorem sum_fejerKernel_eq_doubleSignedRe
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    (∑ q ∈ orderedLongPairDomain μ c Q0 m N,
        Theory.PiDigits.T27.fejerKernel (halfFrequency m - 1)
          (orderedPhaseArgument q)) =
      (∑ r ∈ Finset.range (halfFrequency m),
        ∑ s ∈ Finset.range (halfFrequency m),
          (signedSpectralSum μ c Q0 m N ((s : ℤ) - r)).re) /
        (halfFrequency m : ℝ) := by
  classical
  have hhalf : 1 ≤ halfFrequency m := by
    unfold halfFrequency decimalFrequency
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one]
    have hk : 0 < 10 ^ k := pow_pos (by norm_num) k
    omega
  have hpred : halfFrequency m - 1 + 1 = halfFrequency m :=
    Nat.sub_add_cancel hhalf
  have hpredCast : ((halfFrequency m - 1 : ℕ) : ℝ) + 1 =
      (halfFrequency m : ℝ) := by exact_mod_cast hpred
  have hnum :
      (∑ q ∈ orderedLongPairDomain μ c Q0 m N,
        (∑ r ∈ Finset.range (halfFrequency m),
          ∑ s ∈ Finset.range (halfFrequency m),
            Theory.PiDigits.T27.phase ((s : ℤ) - r)
              (orderedPhaseArgument q)).re) =
        ∑ r ∈ Finset.range (halfFrequency m),
          ∑ s ∈ Finset.range (halfFrequency m),
            (signedSpectralSum μ c Q0 m N ((s : ℤ) - r)).re := by
    simp only [signedSpectralSum]
    simp_rw [← Complex.reCLM_apply, map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.sum_comm]
  simp_rw [Theory.PiDigits.T27.fejerKernel_eq_doubleSum, hpred, hpredCast]
  rw [← Finset.sum_div]
  exact congrArg (fun z : ℝ => z / (halfFrequency m : ℝ)) hnum

/-- The Fejer sum over `Q` is controlled by its zero mode and the requested
inclusive positive-frequency range. -/
theorem sum_fejerKernel_le_zero_add_positive
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    (∑ q ∈ orderedLongPairDomain μ c Q0 m N,
        Theory.PiDigits.T27.fejerKernel (halfFrequency m - 1)
          (orderedPhaseArgument q)) ≤
      (orderedLongPairDomain μ c Q0 m N).card +
        2 * ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖spectralSum μ c Q0 m N h‖ := by
  classical
  let g : ℕ → ℝ := fun h => ‖spectralSum μ c Q0 m N h‖
  have hg : ∀ h, 0 ≤ g h := fun h => norm_nonneg _
  have hhalf : 1 ≤ halfFrequency m := by
    unfold halfFrequency decimalFrequency
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one]
    have hk : 0 < 10 ^ k := pow_pos (by norm_num) k
    omega
  have hhalfPos : (0 : ℝ) < halfFrequency m := by exact_mod_cast hhalf
  have hterm :
      (∑ r ∈ Finset.range (halfFrequency m),
        ∑ s ∈ Finset.range (halfFrequency m),
          (signedSpectralSum μ c Q0 m N ((s : ℤ) - r)).re) ≤
        ∑ r ∈ Finset.range (halfFrequency m),
          ∑ s ∈ Finset.range (halfFrequency m),
            g (Int.natAbs ((s : ℤ) - r)) := by
    apply Finset.sum_le_sum
    intro r _hr
    apply Finset.sum_le_sum
    intro s _hs
    calc
      (signedSpectralSum μ c Q0 m N ((s : ℤ) - r)).re ≤
          ‖signedSpectralSum μ c Q0 m N ((s : ℤ) - r)‖ :=
        Complex.re_le_norm _
      _ = g (Int.natAbs ((s : ℤ) - r)) := by
        rw [norm_signedSpectralSum_eq_natAbs]
  have hpairs := pairDifference_sum_le (halfFrequency m - 1) g hg
  have hpred : halfFrequency m - 1 + 1 = halfFrequency m :=
    Nat.sub_add_cancel hhalf
  have hpredCast : ((halfFrequency m - 1 : ℕ) : ℝ) + 1 =
      (halfFrequency m : ℝ) := by exact_mod_cast hpred
  have hsmall :
      (∑ h ∈ Finset.Icc 1 (halfFrequency m - 1), g h) ≤
        ∑ h ∈ Finset.Icc 1 (decimalFrequency m), g h := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      simp only [Finset.mem_Icc] at hh ⊢
      constructor
      · exact hh.1
      · have hhalfLe : halfFrequency m ≤ decimalFrequency m := by
          exact Nat.div_le_self (decimalFrequency m) 2
        omega
    · intro h _hh _hnot
      exact hg h
  have hzero : g 0 =
      (orderedLongPairDomain μ c Q0 m N).card := by
    unfold g spectralSum
    have hz := congrArg norm (signedSpectralSum_zero μ c Q0 m N)
    simpa using hz
  rw [sum_fejerKernel_eq_doubleSignedRe μ c Q0 m N hm]
  calc
    (∑ r ∈ Finset.range (halfFrequency m),
        ∑ s ∈ Finset.range (halfFrequency m),
          (signedSpectralSum μ c Q0 m N ((s : ℤ) - r)).re) /
        (halfFrequency m : ℝ) ≤
      (∑ r ∈ Finset.range (halfFrequency m),
        ∑ s ∈ Finset.range (halfFrequency m),
          g (Int.natAbs ((s : ℤ) - r))) /
        (halfFrequency m : ℝ) :=
      div_le_div_of_nonneg_right hterm hhalfPos.le
    _ ≤ ((halfFrequency m : ℝ) *
          (g 0 + 2 * ∑ h ∈ Finset.Icc 1 (halfFrequency m - 1), g h)) /
        (halfFrequency m : ℝ) := by
      apply div_le_div_of_nonneg_right
      · simpa only [hpred, hpredCast] using hpairs
      · exact hhalfPos.le
    _ = g 0 + 2 * ∑ h ∈ Finset.Icc 1 (halfFrequency m - 1), g h := by
      field_simp [ne_of_gt hhalfPos]
    _ ≤ g 0 + 2 * ∑ h ∈ Finset.Icc 1 (decimalFrequency m), g h := by
      gcongr
    _ = (orderedLongPairDomain μ c Q0 m N).card +
        2 * ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖spectralSum μ c Q0 m N h‖ := by
      rw [hzero]

/-- Explicit finite majorant bound for T2's residual count. The zero mode is
the first term; the second term contains only positive frequencies and uses
the exact coefficients bounded by their common scale. -/
theorem longResidualPairCount_le_majorant
    (μ c : ℝ) (Q0 m N : ℕ) (hm : 1 ≤ m) :
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
      Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
        (orderedLongPairDomain μ c Q0 m N).card +
      Real.pi ^ 2 / (decimalFrequency m : ℝ) *
        ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ‖spectralSum μ c Q0 m N h‖ := by
  classical
  let Q := orderedLongPairDomain μ c Q0 m N
  let R := residualPairsInsideDomain μ c Q0 m N
  have hcard : (longResidualPairCount μ c Q0 m N : ℝ) =
      ∑ q ∈ Q, if q ∈ R then (1 : ℝ) else 0 := by
    rw [← residualPairsInsideDomain_card μ c Q0 m N]
    have hsubset : residualPairsInsideDomain μ c Q0 m N ⊆
        orderedLongPairDomain μ c Q0 m N := Finset.filter_subset _ _
    simp [Q, R, Finset.inter_eq_right.mpr hsubset]
  have hindicator :
      (∑ q ∈ Q, if q ∈ R then (1 : ℝ) else 0) ≤
        ∑ q ∈ Q, nearReturnMajorant m (orderedPhaseArgument q) := by
    apply Finset.sum_le_sum
    intro q _hq
    split_ifs with hqR
    · have hnear := orderedPhaseArgument_near hqR
      have hmajor := strictCircleIndicator_le_majorant
        m hm (orderedPhaseArgument q)
      simpa [hnear] using hmajor
    · unfold nearReturnMajorant
      exact mul_nonneg (by positivity)
        (Theory.PiDigits.T27.fejerKernel_nonneg _ _)
  have hscale : 0 ≤ Real.pi ^ 2 /
      (2 * (decimalFrequency m : ℝ)) := by positivity
  have hkernel := sum_fejerKernel_le_zero_add_positive μ c Q0 m N hm
  rw [hcard]
  calc
    (∑ q ∈ Q, if q ∈ R then (1 : ℝ) else 0) ≤
        ∑ q ∈ Q, nearReturnMajorant m (orderedPhaseArgument q) := hindicator
    _ = Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
        ∑ q ∈ Q, Theory.PiDigits.T27.fejerKernel
          (halfFrequency m - 1) (orderedPhaseArgument q) := by
      simp only [nearReturnMajorant, Finset.mul_sum]
    _ ≤ Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
        ((orderedLongPairDomain μ c Q0 m N).card +
          2 * ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖spectralSum μ c Q0 m N h‖) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [Q] using hkernel
      · exact hscale
    _ = Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          (orderedLongPairDomain μ c Q0 m N).card +
        Real.pi ^ 2 / (decimalFrequency m : ℝ) *
          ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖spectralSum μ c Q0 m N h‖ := by ring

/-- Cauchy-Schwarz converts the squared-energy hypothesis into the linear
frequency sum needed by the majorant. -/
theorem positiveFrequencyNormSum_le_of_energy
    (μ c : ℝ) (Q0 m N : ℕ) (K : ℝ)
    (hN : 1 ≤ N) (hK : 0 ≤ K)
    (henergy : positiveSpectralEnergy μ c Q0 m N ≤
      K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2) :
    (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
        ‖spectralSum μ c Q0 m N h‖) ≤
      (K + 1) * (decimalFrequency m : ℝ) * N := by
  let A := ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖spectralSum μ c Q0 m N h‖
  have hfreqPosNat : 0 < decimalFrequency m := by
    unfold decimalFrequency
    positivity
  have hfreqPos : (0 : ℝ) < decimalFrequency m := by exact_mod_cast hfreqPosNat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ((Finset.Icc 1 (decimalFrequency m)).card : ℝ) =
      (decimalFrequency m : ℝ) := by
    norm_cast
    simp
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.Icc 1 (decimalFrequency m))
    (f := fun h => ‖spectralSum μ c Q0 m N h‖)
  have hsq : A ^ 2 ≤
      (decimalFrequency m : ℝ) * positiveSpectralEnergy μ c Q0 m N := by
    simpa only [A, hcard, positiveSpectralEnergy] using hCS
  have hsqEnergy : A ^ 2 ≤
      K * (decimalFrequency m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
    calc
      A ^ 2 ≤ (decimalFrequency m : ℝ) *
          positiveSpectralEnergy μ c Q0 m N := hsq
      _ ≤ (decimalFrequency m : ℝ) *
          (K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2) := by
        gcongr
      _ = K * (decimalFrequency m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by ring
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hKone : 0 ≤ K + 1 := by linarith
  have hcoef : K ≤ (K + 1) ^ 2 := by nlinarith [sq_nonneg K]
  have htargetSq : A ^ 2 ≤
      ((K + 1) * (decimalFrequency m : ℝ) * (N : ℝ)) ^ 2 := by
    calc
      A ^ 2 ≤ K * (decimalFrequency m : ℝ) ^ 2 * (N : ℝ) ^ 2 := hsqEnergy
      _ ≤ (K + 1) ^ 2 * (decimalFrequency m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
        gcongr
      _ = ((K + 1) * (decimalFrequency m : ℝ) * (N : ℝ)) ^ 2 := by ring
  have htargetNonneg : 0 ≤
      (K + 1) * (decimalFrequency m : ℝ) * (N : ℝ) := by positivity
  exact (sq_le_sq₀ hA htargetNonneg).mp htargetSq

/-- A pointwise spectral-energy estimate gives the required residual estimate,
with an explicit constant independent of `m,N,s`. -/
theorem longResidualPairCount_le_of_spectralEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (K : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hK : 0 ≤ K)
    (henergy : positiveSpectralEnergy μ c Q0 m N ≤
      K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2) :
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
      (Real.pi ^ 2 + 1) * (K + 1) *
        ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(m : ℝ))) := by
  have hmajor := longResidualPairCount_le_majorant μ c Q0 m N hm
  have hnorm := positiveFrequencyNormSum_le_of_energy
    μ c Q0 m N K hN hK henergy
  have hcardNat := orderedLongPairDomain_card_le_two_sq μ c Q0 m N
  have hcard : ((orderedLongPairDomain μ c Q0 m N).card : ℝ) ≤
      2 * (N : ℝ) ^ 2 := by exact_mod_cast hcardNat
  have hfreqPos : (0 : ℝ) < decimalFrequency m := by
    unfold decimalFrequency
    positivity
  have hdecay : (10 : ℝ) ^ (-(m : ℝ)) =
      ((decimalFrequency m : ℝ))⁻¹ := by
    unfold decimalFrequency
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast]
    exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10) (m : ℝ)
  have hKone : 1 ≤ K + 1 := by linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
        Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          (orderedLongPairDomain μ c Q0 m N).card +
        Real.pi ^ 2 / (decimalFrequency m : ℝ) *
          ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖spectralSum μ c Q0 m N h‖ := hmajor
    _ ≤ Real.pi ^ 2 / (2 * (decimalFrequency m : ℝ)) *
          (2 * (N : ℝ) ^ 2) +
        Real.pi ^ 2 / (decimalFrequency m : ℝ) *
          ((K + 1) * (decimalFrequency m : ℝ) * N) := by
      gcongr
    _ = Real.pi ^ 2 * ((N : ℝ) ^ 2 *
          ((decimalFrequency m : ℝ))⁻¹) +
        Real.pi ^ 2 * (K + 1) * N := by
      field_simp [ne_of_gt hfreqPos]
    _ ≤ (Real.pi ^ 2 + 1) * (K + 1) *
        ((N : ℝ) + (N : ℝ) ^ 2 *
          ((decimalFrequency m : ℝ))⁻¹) := by
      have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      have hNsq : 0 ≤ (N : ℝ) ^ 2 *
          ((decimalFrequency m : ℝ))⁻¹ := by positivity
      nlinarith [mul_nonneg hpi hNsq,
        mul_nonneg (show 0 ≤ Real.pi ^ 2 * (K + 1) by positivity) hNreal.le]
    _ = (Real.pi ^ 2 + 1) * (K + 1) *
        ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(m : ℝ))) := by rw [hdecay]

/-- The uniform spectral target plus T2's explicit arithmetic premise implies
the exact T2 residual predicate. -/
theorem uniformSpectralEnergyBound_implies_T2
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hspectral : UniformSpectralEnergyBound μ c Q0) :
    PiUniformLongLagResidualPairDecay μ c Q0 := by
  rcases hspectral with ⟨K, hK, henergy⟩
  refine ⟨hIrr, ?_⟩
  intro s hs0 hs1
  let C := (Real.pi ^ 2 + 1) * (K + 1)
  have hpiOne : 1 ≤ Real.pi ^ 2 + 1 := by nlinarith [sq_nonneg Real.pi]
  have hKOne : 1 ≤ K + 1 := by linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_le_mul hpiOne hKOne (by norm_num : 0 ≤ (1 : ℝ))
      (by nlinarith [sq_nonneg Real.pi] : 0 ≤ Real.pi ^ 2 + 1)]
  refine ⟨C, hC, ?_⟩
  intro m N hm hN
  have hpoint := longResidualPairCount_le_of_spectralEnergy
    μ c Q0 m N K hm hN hK (henergy m N hm hN)
  have hmReal : (0 : ℝ) ≤ m := by positivity
  have hexponent : -(m : ℝ) ≤ -s * (m : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) hmReal]
  have hpow : (10 : ℝ) ^ (-(m : ℝ)) ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  calc
    (longResidualPairCount μ c Q0 m N : ℝ) ≤
        C * ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-(m : ℝ))) := by simpa [C] using hpoint
    _ ≤ C * ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ))) := by
      gcongr

/-- Hence the collision-independent spectral hypothesis implies canonical C1.
This theorem is conditional and does not assert the hypothesis for pi. -/
theorem uniformSpectralEnergyBound_implies_C1
    {μ c : ℝ} {Q0 : ℕ}
    (hIrr : EffectiveIrrationality Real.pi μ c Q0)
    (hspectral : UniformSpectralEnergyBound μ c Q0) :
    PiLongLagBlockCollisionDecay := by
  exact piUniformLongLagResidualPairDecay_implies_C1
    (uniformSpectralEnergyBound_implies_T2 hIrr hspectral)

/-- Literal unbounded normalized positive-frequency energy. The order is
`forall K >= 0, exists positive m,N`; `Q0` is fixed before `K`. -/
def UnboundedNormalizedSpectralEnergy
    (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∀ K : ℝ, 0 ≤ K →
    ∃ m N : ℕ, 1 ≤ m ∧ 1 ≤ N ∧
      K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2 <
        positiveSpectralEnergy μ c Q0 m N

/-- Quantifier audit for spectral unboundedness. -/
theorem unboundedNormalizedSpectralEnergy_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    UnboundedNormalizedSpectralEnergy μ c Q0 ↔
      ∀ K : ℝ, 0 ≤ K →
        ∃ m N : ℕ, 1 ≤ m ∧ 1 ≤ N ∧
          K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2 <
            positiveSpectralEnergy μ c Q0 m N := by
  rfl

/-- Logical negation of the uniform spectral bound, in explicit unbounded
form. -/
theorem not_uniformSpectralEnergyBound_iff_unbounded
    (μ c : ℝ) (Q0 : ℕ) :
    ¬ UniformSpectralEnergyBound μ c Q0 ↔
      UnboundedNormalizedSpectralEnergy μ c Q0 := by
  classical
  constructor
  · intro hnot K hK
    have hfail : ¬ (∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        positiveSpectralEnergy μ c Q0 m N ≤
          K * (decimalFrequency m : ℝ) * (N : ℝ) ^ 2) := by
      intro hall
      exact hnot ⟨K, hK, hall⟩
    push Not at hfail
    obtain ⟨m, N, hm, hN, hlarge⟩ := hfail
    exact ⟨m, N, hm, hN, hlarge⟩
  · intro hunbounded hbound
    rcases hbound with ⟨K, hK, hall⟩
    obtain ⟨m, N, hm, hN, hlarge⟩ := hunbounded K hK
    exact (not_lt_of_ge (hall m N hm hN)) hlarge

/-- Under T4's explicit external premise, failure of C1 forces unbounded
normalized energy for the arithmetic parameters `(mu,c)=(8,1)`. This is a
contrapositive reduction, not an assertion that C1 fails or that the spectral
hypothesis holds for pi. -/
theorem published_mu_pi_lt_eight_and_not_C1_implies_unbounded_spectralEnergy
    (hSource : IrrationalityMeasureBelow Real.pi 8)
    (hnotC1 : ¬ PiLongLagBlockCollisionDecay) :
    ∃ Q0 : ℕ, EffectiveIrrationality Real.pi 8 1 Q0 ∧
      UnboundedNormalizedSpectralEnergy 8 1 Q0 := by
  obtain ⟨Q0, hIrr⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality hSource
  refine ⟨Q0, hIrr, ?_⟩
  apply (not_uniformSpectralEnergyBound_iff_unbounded 8 1 Q0).mp
  intro hspectral
  exact hnotC1 (uniformSpectralEnergyBound_implies_C1 hIrr hspectral)

end Theory.PiDigits.LongLagBlockCollisionDecay.T8

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.uniformSpectralEnergyBound_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.spectralSum_eq_exp
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.residualPairsInsideDomain_card
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.orderedLongPairDomain_card_le_two_sq
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.majorantCoefficient_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.nearReturnMajorant_eq_trigonometricPolynomial
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.strictCircleIndicator_le_majorant
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.longResidualPairCount_le_majorant
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.positiveFrequencyNormSum_le_of_energy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.longResidualPairCount_le_of_spectralEnergy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.uniformSpectralEnergyBound_implies_T2
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.uniformSpectralEnergyBound_implies_C1
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.unboundedNormalizedSpectralEnergy_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.not_uniformSpectralEnergyBound_iff_unbounded
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T8.published_mu_pi_lt_eight_and_not_C1_implies_unbounded_spectralEnergy
