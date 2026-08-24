import TheoryLib.PiQuantitativeBlockHitting.T123T123AggregatedJacksonFrontier

/-!
# Exact total signed mass of the aggregated Jackson coefficients

The order-`q` Jackson polynomial has total signed coefficient mass exactly
two.  Regrouping equal frequencies preserves that total.  This verifies the
closed mass identity used by the frequency-aggregated frontier, without
asserting positivity of every aggregated coefficient or any cancellation for
the decimal orbit of pi.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.AggregatedJacksonCoefficientMass

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier

/-- The total signed mass of the unaggregated order-`q` Jackson presentation
is exactly two. -/
lemma jacksonCoefficient_self_sum (q : ℕ) (hq : 0 < q) :
    (∑ i : JacksonIndex q, jacksonCoefficient q q i) = 2 := by
  classical
  rw [Fintype.sum_sum_type]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmain :
      (∑ x : Fin q × Fin q × Fin q × Fin q,
        jacksonCoefficient q q (Sum.inl x)) = 2 := by
    simp only [jacksonCoefficient, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hedgeSignSum : (∑ i : Bool × Fin q, edgeSign i) = 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [edgeSign]
  have hedge :
      (∑ x : (Bool × Fin q) × (Bool × Fin q),
        jacksonCoefficient q q (Sum.inr x)) = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [jacksonCoefficient]
    apply Finset.sum_eq_zero
    intro i hi
    calc
      (∑ j : Bool × Fin q,
          -(edgeSign i * edgeSign j) / (2 * (q : ℝ) ^ 2)) =
          (-edgeSign i) * (∑ j : Bool × Fin q, edgeSign j) /
            (2 * (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hedgeSignSum]; ring
  rw [hmain, hedge]
  norm_num

/-- Regrouping a finite coefficient family by frequency preserves its total
signed mass. -/
lemma sum_aggregatedCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℝ) (frequency : ι → ℤ) :
    ∑ h ∈ Finset.image frequency Finset.univ,
        aggregatedCoefficient coefficient frequency h =
      ∑ i, coefficient i := by
  classical
  apply Finset.sum_image'
  intro i hi
  unfold aggregatedCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- The exact total signed mass of the frequency-aggregated order-`q`
Jackson coefficients is two. -/
theorem aggregatedJacksonCoefficient_totalMass (q : ℕ) (hq : 0 < q) :
    (∑ h ∈ Finset.image (@jacksonFrequency q) Finset.univ,
      aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) h) = 2 := by
  rw [sum_aggregatedCoefficient]
  exact jacksonCoefficient_self_sum q hq

end Theory.PiDigits.AggregatedJacksonCoefficientMass

#print axioms Theory.PiDigits.AggregatedJacksonCoefficientMass.aggregatedJacksonCoefficient_totalMass
