import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting
import TheoryLib.PiLacunaryNearReturnSparsity.T25FiniteMultilevelEnvelope
import TheoryLib.PiLacunaryNearReturnSparsity.T64AggregateFejerCriterion

/-!
# T107: averaged triangular T64 defect

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module leaves the averaged fixed-pi analytic estimate as a premise.  It
proves only the finite counting step, the bridge to T14 coherent splitting,
and the resulting conditional implication to the open C2 hypothesis.  It
does not assert the analytic premise, C2, or canonical A1 for pi.
-/

noncomputable section

open Filter Finset Topology
open MeasureTheory ProbabilityTheory

namespace DecimalFactorComplexity.AveragedTriangularFejerT107

open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.FiniteMultilevelEnvelope
open DecimalFactorComplexity.CoherentSuccessorSplitting
open DecimalFactorComplexity.AggregateFejerCriterionT64

/-- The literal T64 levels in a depth-`m` row: exactly `1 ≤ ell < m`. -/
def literalLevels (m : ℕ) : Finset ℕ := Finset.Ico 1 m

/-- T64's complete parent-plus-successor boundary load at level `ell`. -/
def rowBoundaryLoad (ell P : ℕ) : ℝ :=
  (activeBoundaryCount piOrbit P (10 ^ (ell + 1))
      (fun j => piCylinderCode (ell + 1) j)
      (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
    (1 / 2 : ℝ) *
      (activeBoundaryCount piOrbit P (10 ^ ell)
        (fun j => piCylinderCode ell j)
        (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)

/-- The exact boundary budget in T64's row theorem. -/
def rowBoundaryBudget (ell P : ℕ) : ℝ :=
  (P : ℝ) / (40 * (10 ^ ell : ℕ))

/-- The exact collected-Fourier budget in T64's row theorem. -/
def rowFourierBudget (ell P : ℕ) : ℝ :=
  (P : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ))

/-- The maximum of the two normalized T64 analytic loads.  At a positive
cutoff it is at most one exactly when both literal T64 row estimates hold. -/
def rowAnalyticDefect (ell P : ℕ) : ℝ :=
  max (rowBoundaryLoad ell P / rowBoundaryBudget ell P)
    (‖rowFourierRemainder ell P‖ / rowFourierBudget ell P)

/-- T64's two analytic row premises, with every normalization displayed. -/
def LiteralT64GoodLevel (ell P : ℕ) : Prop :=
  (activeBoundaryCount piOrbit P (10 ^ (ell + 1))
        (fun j => piCylinderCode (ell + 1) j)
        (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
      (1 / 2 : ℝ) *
        (activeBoundaryCount piOrbit P (10 ^ ell)
          (fun j => piCylinderCode ell j)
          (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) ≤
      (P : ℝ) / (40 * (10 ^ ell : ℕ)) ∧
    ‖rowFourierRemainder ell P‖ ≤
      (P : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ))

/-- The good literal levels below `m` for one finite prefix. -/
def literalT64GoodLevels (m P : ℕ) : Finset ℕ := by
  classical
  exact (literalLevels m).filter fun ell => LiteralT64GoodLevel ell P

/-- The normalized defect is nonnegative. -/
theorem rowAnalyticDefect_nonneg (ell P : ℕ) :
    0 ≤ rowAnalyticDefect ell P := by
  unfold rowAnalyticDefect
  have hload : 0 ≤ rowBoundaryLoad ell P := by
    unfold rowBoundaryLoad
    positivity
  have hbudget : 0 ≤ rowBoundaryBudget ell P := by
    unfold rowBoundaryBudget
    positivity
  exact (div_nonneg hload hbudget).trans (le_max_left _ _)

/-- At a positive cutoff, the normalized maximum is an exact encoding of
T64's two separate row budgets. -/
theorem rowAnalyticDefect_le_one_iff
    (ell P : ℕ) (hP : 0 < P) :
    rowAnalyticDefect ell P ≤ 1 ↔ LiteralT64GoodLevel ell P := by
  have hboundaryBudget : 0 < rowBoundaryBudget ell P := by
    unfold rowBoundaryBudget
    positivity
  have hfourierBudget : 0 < rowFourierBudget ell P := by
    unfold rowFourierBudget
    positivity
  unfold rowAnalyticDefect LiteralT64GoodLevel rowBoundaryLoad
  rw [max_le_iff]
  constructor
  · rintro ⟨hboundary, hfourier⟩
    constructor
    · rw [div_le_iff₀ hboundaryBudget] at hboundary
      simpa [rowBoundaryBudget] using hboundary
    · rw [div_le_iff₀ hfourierBudget] at hfourier
      simpa [rowFourierBudget] using hfourier
  · rintro ⟨hboundary, hfourier⟩
    constructor
    · rw [div_le_iff₀ hboundaryBudget]
      simpa [rowBoundaryBudget] using hboundary
    · rw [div_le_iff₀ hfourierBudget]
      simpa [rowFourierBudget] using hfourier

/-- Finite Markov counting at threshold one.  The additive target `D` is
kept real-valued, so later use can retain the exact affine defect `d*m-B`. -/
theorem finite_markov_good_count
    {α : Type*} [DecidableEq α] (s : Finset α) (defect : α → ℝ) (D : ℝ)
    (hnonneg : ∀ a ∈ s, 0 ≤ defect a)
    (haverage : ∑ a ∈ s, defect a ≤ (s.card : ℝ) - D) :
    D ≤ ((s.filter fun a => defect a ≤ 1).card : ℝ) := by
  classical
  let good := s.filter fun a => defect a ≤ 1
  let bad := s.filter fun a => ¬ defect a ≤ 1
  have hbadPoint : ∀ a ∈ bad, (1 : ℝ) ≤ defect a := by
    intro a ha
    have ha' : a ∈ s ∧ ¬ defect a ≤ 1 := by
      simpa [bad] using ha
    exact (not_le.mp ha'.2).le
  have hbadToSum : (bad.card : ℝ) ≤ ∑ a ∈ s, defect a := by
    calc
      (bad.card : ℝ) = ∑ _a ∈ bad, (1 : ℝ) := by simp
      _ ≤ ∑ a ∈ bad, defect a := by
        exact Finset.sum_le_sum fun a ha => hbadPoint a ha
      _ ≤ ∑ a ∈ s, defect a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro a ha _haBad
          exact hnonneg a ha
  have hpartitionNat : good.card + bad.card = s.card := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := s) (p := fun a => defect a ≤ 1))
  have hpartitionReal : (good.card : ℝ) + (bad.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hpartitionNat
  have hgoal : D ≤ (good.card : ℝ) := by
    linarith
  simpa [good] using hgoal

/-- The conditional averaged multilevel hypothesis on one increasing family
of positive prefixes.  Every triangle entry `k ≥ k0`, `m ≥ m0`, `m ≤ k`
averages over exactly `1 ≤ ell < m`; the analytic estimate is not proved. -/
def AveragedTriangularT64DefectAt
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle) : Prop :=
  0 < d ∧ 0 ≤ B ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
    Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 nu) ∧
    ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
      ∑ ell ∈ literalLevels m, rowAnalyticDefect ell (N k) ≤
        ((literalLevels m).card : ℝ) - (d * (m : ℝ) - B)

/-- The averaged hypothesis with all prefix and triangular quantifiers
visible in the theorem type. -/
theorem averagedTriangularT64DefectAt_iff_quantifiers
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle) :
    AveragedTriangularT64DefectAt d B m0 k0 N nu ↔
      0 < d ∧ 0 ≤ B ∧ StrictMono N ∧ (∀ k, 0 < N k) ∧
      Tendsto (fun k => piDecimalEmpiricalMeasure (N k)) atTop (𝓝 nu) ∧
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        ∑ ell ∈ literalLevels m, rowAnalyticDefect ell (N k) ≤
          ((literalLevels m).card : ℝ) - (d * (m : ℝ) - B) :=
  Iff.rfl

/-- Quantitative extraction of at least `d*m-B` literal levels satisfying
both exact T64 row estimates. -/
theorem averaged_defect_extracts_literal_t64_good_levels
    (d B : ℝ) (m0 k0 k m : ℕ) (N : ℕ → ℕ)
    (hNpos : ∀ j, 0 < N j)
    (hk : k0 ≤ k) (hm : m0 ≤ m) (hmk : m ≤ k)
    (haverage :
      ∀ k' : ℕ, k0 ≤ k' → ∀ m' : ℕ, m0 ≤ m' → m' ≤ k' →
        ∑ ell ∈ literalLevels m', rowAnalyticDefect ell (N k') ≤
          ((literalLevels m').card : ℝ) - (d * (m' : ℝ) - B)) :
    d * (m : ℝ) - B ≤ (literalT64GoodLevels m (N k)).card := by
  classical
  have hmarkov := finite_markov_good_count
    (literalLevels m) (fun ell => rowAnalyticDefect ell (N k))
      (d * (m : ℝ) - B)
      (fun ell _hell => rowAnalyticDefect_nonneg ell (N k))
      (haverage k hk m hm hmk)
  have hfilter :
      (literalLevels m).filter (fun ell => rowAnalyticDefect ell (N k) ≤ 1) =
        (literalLevels m).filter (fun ell => LiteralT64GoodLevel ell (N k)) := by
    ext ell
    simp only [Finset.mem_filter]
    rw [rowAnalyticDefect_le_one_iff ell (N k) (hNpos k)]
  rw [hfilter] at hmarkov
  simpa [literalT64GoodLevels] using hmarkov

/-- Fully expanded extraction statement.  Its premise displays the averaged
boundary/Fourier normalization, and its conclusion displays the two separate
T64 row criteria on every counted level. -/
theorem explicit_averaged_defect_extracts_literal_t64_good_levels
    (d B : ℝ) (m0 k0 k m : ℕ) (N : ℕ → ℕ)
    (hNpos : ∀ j, 0 < N j)
    (hk : k0 ≤ k) (hm : m0 ≤ m) (hmk : m ≤ k)
    (haverage :
      ∀ k' : ℕ, k0 ≤ k' → ∀ m' : ℕ, m0 ≤ m' → m' ≤ k' →
        ∑ ell ∈ Finset.Ico 1 m',
          max
            (((activeBoundaryCount piOrbit (N k') (10 ^ (ell + 1))
                  (fun j => piCylinderCode (ell + 1) j)
                  (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
                (1 / 2 : ℝ) *
                  (activeBoundaryCount piOrbit (N k') (10 ^ ell)
                    (fun j => piCylinderCode ell j)
                    (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) /
              ((N k' : ℝ) / (40 * (10 ^ ell : ℕ))))
            (‖rowFourierRemainder ell (N k')‖ /
              ((N k' : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ)))) ≤
          ((Finset.Ico 1 m').card : ℝ) - (d * (m' : ℝ) - B)) :
    d * (m : ℝ) - B ≤
      ((Finset.Ico 1 m).filter fun ell =>
        (activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
              (fun j => piCylinderCode (ell + 1) j)
              (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
            (1 / 2 : ℝ) *
              (activeBoundaryCount piOrbit (N k) (10 ^ ell)
                (fun j => piCylinderCode ell j)
                (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) ≤
            (N k : ℝ) / (40 * (10 ^ ell : ℕ)) ∧
          ‖rowFourierRemainder ell (N k)‖ ≤
            (N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ))).card := by
  have h := averaged_defect_extracts_literal_t64_good_levels
    d B m0 k0 k m N hNpos hk hm hmk (by
      intro k' hk' m' hm' hmk'
      simpa [literalLevels, rowAnalyticDefect, rowBoundaryLoad,
        rowBoundaryBudget, rowFourierBudget] using
          haverage k' hk' m' hm' hmk')
  simpa [literalT64GoodLevels, literalLevels, LiteralT64GoodLevel] using h

/-- Every extracted T64-good literal level is one of T14's splitting levels,
with T64's fixed `mu = 3281/7281` and `eta = 1/100`. -/
theorem literalT64GoodLevels_subset_piSplittingLevels
    (m k : ℕ) (N : ℕ → ℕ) (hNpos : ∀ j, 0 < N j) (hmk : m ≤ k) :
    literalT64GoodLevels m (N k) ⊆
      piSplittingLevels m (N k) (3281 / 7281 : ℝ) (1 / 100) := by
  intro ell hell
  have hell' : ell ∈ literalLevels m ∧ LiteralT64GoodLevel ell (N k) := by
    simpa [literalT64GoodLevels] using hell
  have hrange : 1 ≤ ell ∧ ell < m := by
    simpa [literalLevels] using hell'.1
  have hrow := boundary_and_fourier_imply_literal_t14_row
    ell m k N hrange.1 hrange.2 hmk (hNpos k) hell'.2.1 hell'.2.2
  simp only [piSplittingLevels, Finset.mem_filter, Finset.mem_range]
  exact ⟨hrange.2, hrow.1⟩

/-- The averaged analytic premise gives T14 coherent splitting on the same
prefix family, with every structural premise and the additive defect retained. -/
theorem averaged_triangular_t64_implies_coherent_splitting_at
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hd : 0 < d) (hB : 0 ≤ B)
    (hNmono : StrictMono N) (hNpos : ∀ k, 0 < N k)
    (hnu : Tendsto (fun k => piDecimalEmpiricalMeasure (N k))
      atTop (𝓝 nu))
    (haverage :
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        ∑ ell ∈ literalLevels m, rowAnalyticDefect ell (N k) ≤
          ((literalLevels m).card : ℝ) - (d * (m : ℝ) - B)) :
    PiCoherentPositiveDensitySplittingAt
      (3281 / 7281 : ℝ) (1 / 100) d B m0 k0 N nu := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, hd, hB,
    hNmono, hNpos, hnu, ?_⟩
  intro k hk m hm hmk
  have hgood := averaged_defect_extracts_literal_t64_good_levels
    d B m0 k0 k m N hNpos hk hm hmk haverage
  have hsubset := literalT64GoodLevels_subset_piSplittingLevels
    m k N hNpos hmk
  have hcardNat := Finset.card_le_card hsubset
  have hcardReal : ((literalT64GoodLevels m (N k)).card : ℝ) ≤
      (piSplittingLevelCount m (N k)
        (3281 / 7281 : ℝ) (1 / 100) : ℝ) := by
    exact_mod_cast hcardNat
  exact hgood.trans hcardReal

/-- Packaged form of the coherent-splitting bridge. -/
theorem averagedTriangularT64DefectAt_implies_coherent_splitting_at
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (havg : AveragedTriangularT64DefectAt d B m0 k0 N nu) :
    PiCoherentPositiveDensitySplittingAt
      (3281 / 7281 : ℝ) (1 / 100) d B m0 k0 N nu := by
  rcases havg with ⟨hd, hB, hNmono, hNpos, hnu, haverage⟩
  exact averaged_triangular_t64_implies_coherent_splitting_at
    d B m0 k0 N nu hd hB hNmono hNpos hnu haverage

/-- Quantifier- and normalization-expanded coherent-splitting bridge. -/
theorem explicit_averaged_triangular_t64_implies_coherent_splitting_at
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hd : 0 < d) (hB : 0 ≤ B)
    (hNmono : StrictMono N) (hNpos : ∀ k, 0 < N k)
    (hnu : Tendsto (fun k => piDecimalEmpiricalMeasure (N k))
      atTop (𝓝 nu))
    (haverage :
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        ∑ ell ∈ Finset.Ico 1 m,
          max
            (((activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
                  (fun j => piCylinderCode (ell + 1) j)
                  (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
                (1 / 2 : ℝ) *
                  (activeBoundaryCount piOrbit (N k) (10 ^ ell)
                    (fun j => piCylinderCode ell j)
                    (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) /
              ((N k : ℝ) / (40 * (10 ^ ell : ℕ))))
            (‖rowFourierRemainder ell (N k)‖ /
              ((N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ)))) ≤
          ((Finset.Ico 1 m).card : ℝ) - (d * (m : ℝ) - B)) :
    PiCoherentPositiveDensitySplittingAt
      (3281 / 7281 : ℝ) (1 / 100) d B m0 k0 N nu := by
  apply averaged_triangular_t64_implies_coherent_splitting_at
    d B m0 k0 N nu hd hB hNmono hNpos hnu
  intro k hk m hm hmk
  simpa [literalLevels, rowAnalyticDefect, rowBoundaryLoad,
    rowBoundaryBudget, rowFourierBudget] using haverage k hk m hm hmk

/-- Conditional route to the agenda's open C2 hypothesis.  The full averaged
Fourier-and-boundary estimate remains an explicit premise of this theorem. -/
theorem explicit_averaged_triangular_t64_implies_piPolynomialSmallBallC2
    (d B : ℝ) (m0 k0 : ℕ) (N : ℕ → ℕ)
    (nu : ProbabilityMeasure UnitAddCircle)
    (hd : 0 < d) (hB : 0 ≤ B)
    (hNmono : StrictMono N) (hNpos : ∀ k, 0 < N k)
    (hnu : Tendsto (fun k => piDecimalEmpiricalMeasure (N k))
      atTop (𝓝 nu))
    (haverage :
      ∀ k : ℕ, k0 ≤ k → ∀ m : ℕ, m0 ≤ m → m ≤ k →
        ∑ ell ∈ Finset.Ico 1 m,
          max
            (((activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
                  (fun j => piCylinderCode (ell + 1) j)
                  (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
                (1 / 2 : ℝ) *
                  (activeBoundaryCount piOrbit (N k) (10 ^ ell)
                    (fun j => piCylinderCode ell j)
                    (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) /
              ((N k : ℝ) / (40 * (10 ^ ell : ℕ))))
            (‖rowFourierRemainder ell (N k)‖ /
              ((N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ)))) ≤
          ((Finset.Ico 1 m).card : ℝ) - (d * (m : ℝ) - B)) :
    PiPolynomialSmallBallC2 := by
  apply coherentPositiveDensitySplitting_implies_piPolynomialSmallBallC2
  exact ⟨(3281 / 7281 : ℝ), (1 / 100 : ℝ), d, B, m0, k0, N, nu,
    explicit_averaged_triangular_t64_implies_coherent_splitting_at
      d B m0 k0 N nu hd hB hNmono hNpos hnu haverage⟩

end DecimalFactorComplexity.AveragedTriangularFejerT107

#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.rowAnalyticDefect_le_one_iff
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.finite_markov_good_count
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.averaged_defect_extracts_literal_t64_good_levels
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.explicit_averaged_defect_extracts_literal_t64_good_levels
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.literalT64GoodLevels_subset_piSplittingLevels
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.averaged_triangular_t64_implies_coherent_splitting_at
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.explicit_averaged_triangular_t64_implies_coherent_splitting_at
#print axioms DecimalFactorComplexity.AveragedTriangularFejerT107.explicit_averaged_triangular_t64_implies_piPolynomialSmallBallC2
