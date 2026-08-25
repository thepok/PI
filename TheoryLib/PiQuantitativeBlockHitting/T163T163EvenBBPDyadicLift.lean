import TheoryLib.PiQuantitativeBlockHitting.T104T104BBPSeriesIdentity
import TheoryLib.PiQuantitativeBlockHitting.T115T115SampledBBPCellDefectPhase
import TheoryLib.PiQuantitativeBlockHitting.T44T44MachinTotalTwoAdicForcing

/-!
# T163: exact even-depth dyadic conductor and immediate BBP lift

At an even sampled depth `m`, the final combined BBP row has strictly smaller
two-adic valuation than every preceding row.  This gives the exact reduced
denominator exponent `27*m` for `10^m * bbpPartial (7*m)`.

The already verified positive BBP tail is smaller than the depth-`m-1`
dyadic-lift spacing.  Consequently the actual sampled BBP rational is the
unique point of its lift lattice immediately below `10^m * pi`.

This is exact arithmetic and Archimedean localization for the actual BBP
truncation.  It proves no cancellation, cylinder hit, normality, or V1 claim.
-/

noncomputable section

open scoped BigOperators

namespace Theory.PiDigits.T163EvenBBPDyadicLift

open Finset
open Theory.PiDigits.MachinTwoAdicForcing
open Theory.PiDigits.MachinTotalTwoAdicForcing
open Theory.PiDigits.T77SelectedPadicDefectShell
open Theory.PiDigits.T98BBPArchimedeanTerm
open Theory.PiDigits.T100BBPRealBridge
open Theory.PiDigits.T104BBPSeriesIdentity
open Theory.PiDigits.T115SampledBBPCellDefectPhase

/-- The inclusive BBP partial sum is the sum of its collapsed four-pole rows. -/
theorem bbpPartial_eq_sum_combined (K : ℕ) :
    bbpPartial K = ∑ j ∈ range (K + 1), bbpCombinedTerm j := by
  simp only [bbpPartial, polePartial, bbpCombinedTerm, sum_add_distrib]

private theorem combinedOddDenominator (j : ℕ) :
    Odd ((2 * j + 1) * (4 * j + 3) * (8 * j + 1) * (8 * j + 5)) := by
  have h1 : Odd (2 * j + 1) := ⟨j, by omega⟩
  have h2 : Odd (4 * j + 3) := ⟨2 * j + 1, by omega⟩
  have h3 : Odd (8 * j + 1) := ⟨4 * j, by omega⟩
  have h4 : Odd (8 * j + 5) := ⟨4 * j + 2, by omega⟩
  exact Odd.mul (Odd.mul (Odd.mul h1 h2) h3) h4

private theorem combinedNumerator_odd_of_even {j : ℕ} (hj : Even j) :
    Odd (120 * j ^ 2 + 151 * j + 47) := by
  rcases hj with ⟨r, rfl⟩
  refine ⟨240 * r ^ 2 + 151 * r + 23, ?_⟩
  ring

private theorem bbpCombinedTerm_ne_zero (j : ℕ) : bbpCombinedTerm j ≠ 0 :=
  ne_of_gt (bbpCombinedTerm_pos j)

private theorem padicValRat_two_combined_lower (j : ℕ) :
    -(4 * (j : ℤ)) ≤ padicValRat 2 (bbpCombinedTerm j) := by
  let A : ℕ := 120 * j ^ 2 + 151 * j + 47
  let O : ℕ := (2 * j + 1) * (4 * j + 3) * (8 * j + 1) * (8 * j + 5)
  have hA : (A : ℚ) ≠ 0 := by positivity
  have hO : (O : ℚ) ≠ 0 := by positivity
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have hOdd : Odd O := combinedOddDenominator j
  have hvalO : padicValRat 2 (O : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd hOdd
  have hval16 : padicValRat 2 (16 : ℚ) = 4 := by
    have htwo : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (by norm_num : 1 < (2 : ℕ))
    rw [show (16 : ℚ) = 2 ^ 4 by norm_num, padicValRat.pow (by norm_num)]
    rw [htwo]
    norm_num
  have heq : bbpCombinedTerm j = (A : ℚ) / ((O : ℚ) * 16 ^ j) := by
    rw [bbpCombinedTerm_eq]
    field_simp
    dsimp [A, O]
    push_cast
    ring
  have hvalA : padicValRat 2 (A : ℚ) = (padicValNat 2 A : ℤ) :=
    padicValRat.of_nat
  rw [heq]
  rw [padicValRat.div hA (mul_ne_zero hO (pow_ne_zero _ h16)),
    padicValRat.mul hO (pow_ne_zero _ h16), hvalO,
    padicValRat.pow h16, hval16, hvalA]
  simp only [zero_add]
  have hv : (0 : ℤ) ≤ (padicValNat 2 A : ℤ) := by positivity
  push_cast
  omega

private theorem padicValRat_two_combined_even {j : ℕ} (hj : Even j) :
    padicValRat 2 (bbpCombinedTerm j) = -(4 * (j : ℤ)) := by
  let A : ℕ := 120 * j ^ 2 + 151 * j + 47
  let O : ℕ := (2 * j + 1) * (4 * j + 3) * (8 * j + 1) * (8 * j + 5)
  have hA : (A : ℚ) ≠ 0 := by positivity
  have hO : (O : ℚ) ≠ 0 := by positivity
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have hvalA : padicValRat 2 (A : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (combinedNumerator_odd_of_even hj)
  have hvalO : padicValRat 2 (O : ℚ) = 0 :=
    padicValRat_two_natCast_eq_zero_of_odd (combinedOddDenominator j)
  have hval16 : padicValRat 2 (16 : ℚ) = 4 := by
    have htwo : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (by norm_num : 1 < (2 : ℕ))
    rw [show (16 : ℚ) = 2 ^ 4 by norm_num, padicValRat.pow (by norm_num)]
    rw [htwo]
    norm_num
  have heq : bbpCombinedTerm j = (A : ℚ) / ((O : ℚ) * 16 ^ j) := by
    rw [bbpCombinedTerm_eq]
    field_simp
    dsimp [A, O]
    push_cast
    ring
  rw [heq]
  rw [padicValRat.div hA (mul_ne_zero hO (pow_ne_zero _ h16)),
    padicValRat.mul hO (pow_ne_zero _ h16), hvalA, hvalO,
    padicValRat.pow h16, hval16]
  ring

private theorem padicValRat_two_sum_lower
    {S : Finset ℕ} (f : ℕ → ℚ) (c : ℤ)
    (hf : ∀ x ∈ S, c ≤ padicValRat 2 (f x)) :
    (∑ x ∈ S, f x) = 0 ∨ c ≤ padicValRat 2 (∑ x ∈ S, f x) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hxs ih =>
      rw [sum_insert hxs]
      have hx := hf x (mem_insert_self x S)
      have hs := ih (fun y hy => hf y (mem_insert_of_mem hy))
      by_cases hx0 : f x = 0
      · simpa [hx0] using hs
      by_cases hs0 : (∑ y ∈ S, f y) = 0
      · simp [hs0, hx0, hx]
      rcases hs with hs | hs
      · exact False.elim (hs0 hs)
      by_cases hsum0 : f x + ∑ y ∈ S, f y = 0
      · exact Or.inl hsum0
      · exact Or.inr (le_trans (le_min hx hs)
          (padicValRat.min_le_padicValRat_add hsum0))

/-- At even depth, the sampled rational has exact two-adic order `-27*m`. -/
theorem scaledBBPRat_two_val_even (m : ℕ) (hm : Even m) :
    padicValRat 2 (scaledBBPRat m) = -(27 * (m : ℤ)) := by
  have hlastEven : Even (7 * m) := Even.mul_left hm 7
  have hlast := padicValRat_two_combined_even hlastEven
  have hprefix := padicValRat_two_sum_lower bbpCombinedTerm
      (-(4 * (7 * m : ℕ) : ℤ) + 1)
      (S := range (7 * m)) (fun j hj => by
        have hjlt : j < 7 * m := mem_range.mp hj
        have hlow := padicValRat_two_combined_lower j
        push_cast at hlow ⊢
        omega)
  have hpartial : padicValRat 2 (bbpPartial (7 * m)) = -(28 * (m : ℤ)) := by
    rw [bbpPartial_eq_sum_combined, sum_range_succ]
    rcases hprefix with hz | hge
    · simp only [hz, zero_add, hlast]
      push_cast
      ring
    · by_cases hp0 : (∑ j ∈ range (7 * m), bbpCombinedTerm j) = 0
      · simp only [hp0, zero_add, hlast]
        push_cast
        ring
      · have hlast0 := bbpCombinedTerm_ne_zero (7 * m)
        have hlt : padicValRat 2 (bbpCombinedTerm (7 * m)) <
            padicValRat 2 (∑ j ∈ range (7 * m), bbpCombinedTerm j) := by
          rw [hlast]
          omega
        have hsum0 : bbpCombinedTerm (7 * m) +
            ∑ j ∈ range (7 * m), bbpCombinedTerm j ≠ 0 := by
          intro hz
          have heq := eq_neg_of_add_eq_zero_left hz
          have hv := congrArg (padicValRat 2) heq
          rw [padicValRat.neg] at hv
          omega
        rw [add_comm, padicValRat.add_eq_of_lt hsum0 hlast0 hp0 hlt, hlast]
        push_cast
        ring
  unfold scaledBBPRat
  have hpartial0 : bbpPartial (7 * m) ≠ 0 := by
    exact ne_of_gt (by
      rw [bbpPartial_eq_sum_combined, sum_range_succ]
      exact add_pos_of_nonneg_of_pos
        (sum_nonneg fun j _ => (bbpCombinedTerm_pos j).le)
        (bbpCombinedTerm_pos (7 * m)))
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) hpartial0,
    padicValRat.pow (by norm_num), padicValRat_two_ten, hpartial]
  ring

/-- At positive even depth, the reduced denominator contains exactly
`2^(27*m)` and the reduced numerator is odd. -/
theorem scaledBBPRat_even_two_primary (m : ℕ) (hm : Even m) (hmpos : 0 < m) :
    padicValNat 2 (scaledBBPRat m).den = 27 * m ∧
      Odd (scaledBBPRat m).num.natAbs := by
  let q := scaledBBPRat m
  have hval := scaledBBPRat_two_val_even m hm
  have hq0 : q ≠ 0 := by
    intro hz
    simp [q, hz] at hval
    omega
  have hnum0 : q.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    intro hn
    apply hq0
    rw [← q.num_div_den, hn]
    norm_num
  have hdenDiv : 2 ∣ q.den := by
    by_contra hnot
    have hvden : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd hnot
    rw [padicValRat_def, hvden] at hval
    have hvnum : (0 : ℤ) ≤ padicValInt 2 q.num := by
      unfold padicValInt
      positivity
    omega
  have hnumNot : ¬ 2 ∣ q.num.natAbs := by
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_right hdenDiv q.reduced).symm
  have hvnum : padicValInt 2 q.num = 0 := by
    simpa [padicValInt] using padicValNat.eq_zero_of_not_dvd hnumNot
  constructor
  · rw [padicValRat_def, hvnum] at hval
    norm_num at hval
    exact_mod_cast hval
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hnumNot

/-- The depth-`m-1` lift spacing at even depth, written directly from the
exact dyadic conductor. -/
def evenBBPLiftSpacing (m : ℕ) : ℚ :=
  (2 * (5 : ℚ) ^ (m - 1)) / (2 : ℚ) ^ (27 * m)

/-- The verified BBP tail is strictly smaller than the even-depth lift
spacing.  The lower inequality is strict because the BBP series has positive
terms beyond every finite prefix. -/
theorem scaledBBPRat_even_tail_lt_spacing (m : ℕ) (hm : 1 ≤ m) :
    (0 : ℝ) < (10 : ℝ) ^ m * Real.pi - (scaledBBPRat m : ℝ) ∧
      (10 : ℝ) ^ m * Real.pi - (scaledBBPRat m : ℝ) <
        (evenBBPLiftSpacing m : ℝ) := by
  have htail := T100BBPRealBridge.real_bbp_hasSum_tail_bounds
    bbpRealTerm_hasSum_pi (7 * m)
  have hpartial : (scaledBBPRat m : ℝ) =
      (10 : ℝ) ^ m * bbpRealPartial (7 * m) := by
    simp only [scaledBBPRat, bbpRealPartial, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat]
  have hstrictPartial : bbpRealPartial (7 * m) < Real.pi := by
    have hs := bbpRealPartial_succ (7 * m)
    have hpos : 0 < bbpRealTerm (7 * m + 1) := by
      simpa only [bbpRealTerm, Rat.cast_pos] using bbpCombinedTerm_pos (7 * m + 1)
    have hnext : bbpRealPartial (7 * m) < bbpRealPartial (7 * m + 1) := by
      linarith
    exact lt_of_lt_of_le hnext (real_bbp_hasSum_tail_bounds
      bbpRealTerm_hasSum_pi (7 * m + 1)).1
  have hpow10 : (0 : ℝ) < 10 ^ m := by positivity
  constructor
  · rw [hpartial]
    nlinarith
  · rw [hpartial]
    have hupper := htail.2.1
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hmajor : (10 : ℝ) ^ m * (4 / (15 * (16 : ℝ) ^ (7 * m))) <
        (evenBBPLiftSpacing m : ℝ) := by
      norm_num [evenBBPLiftSpacing, Rat.cast_div, Rat.cast_mul, Rat.cast_pow]
      rw [show (10 : ℝ) ^ m = 2 ^ m * 5 ^ m by
        rw [show (10 : ℝ) = 2 * 5 by norm_num, mul_pow],
        show (16 : ℝ) ^ (7 * m) = 2 ^ (28 * m) by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]; congr 1 <;> omega,
        show (5 : ℝ) ^ m = 5 ^ (m - 1) * 5 by
          simpa [hm1] using pow_succ (5 : ℝ) (m - 1)]
      have h2 : (0 : ℝ) < 2 ^ (27 * m) := by positivity
      have h5 : (0 : ℝ) < 5 ^ (m - 1) := by positivity
      field_simp
      ring_nf
      nlinarith [show (0 : ℝ) < 2 ^ (m * 28) by positivity]
    calc
      (10 : ℝ) ^ m * Real.pi - (10 : ℝ) ^ m * bbpRealPartial (7 * m) =
          (10 : ℝ) ^ m * (Real.pi - bbpRealPartial (7 * m)) := by ring
      _ ≤ (10 : ℝ) ^ m * (4 / (15 * (16 : ℝ) ^ (7 * m))) :=
        mul_le_mul_of_nonneg_left hupper hpow10.le
      _ < (evenBBPLiftSpacing m : ℝ) := hmajor

/-- The actual sampled BBP rational is the unique point of its spacing
lattice in the interval immediately below `10^m*pi`. -/
theorem scaledBBPRat_even_unique_immediate_lift
    (m : ℕ) (hm : Even m) (hmpos : 0 < m) (y : ℚ) (z : ℤ)
    (hy : y = scaledBBPRat m + z * evenBBPLiftSpacing m)
    (hylow : (10 : ℝ) ^ m * Real.pi - (evenBBPLiftSpacing m : ℝ) < (y : ℝ))
    (hyhigh : (y : ℝ) ≤ (10 : ℝ) ^ m * Real.pi) :
    y = scaledBBPRat m ∧
      padicValNat 2 (scaledBBPRat m).den = 27 * m ∧
      Odd (scaledBBPRat m).num.natAbs := by
  refine ⟨?_, scaledBBPRat_even_two_primary m hm hmpos⟩
  have hm1 : 1 ≤ m := hmpos
  have htail := scaledBBPRat_even_tail_lt_spacing m hm1
  have hspace : (0 : ℝ) < (evenBBPLiftSpacing m : ℝ) := by
    unfold evenBBPLiftSpacing
    positivity
  have hyR : (y : ℝ) = (scaledBBPRat m : ℝ) + (z : ℝ) *
      (evenBBPLiftSpacing m : ℝ) := by exact_mod_cast hy
  have hzLower : (z : ℝ) > -1 := by
    rw [hyR] at hylow
    nlinarith
  have hzUpper : (z : ℝ) < 1 := by
    rw [hyR] at hyhigh
    nlinarith
  have hz0 : z = 0 := by
    have hzLowerZ : (-1 : ℤ) < z := by exact_mod_cast hzLower
    have hzUpperZ : z < (1 : ℤ) := by exact_mod_cast hzUpper
    omega
  simpa [hz0] using hy

end Theory.PiDigits.T163EvenBBPDyadicLift

#print axioms Theory.PiDigits.T163EvenBBPDyadicLift.bbpPartial_eq_sum_combined
#print axioms Theory.PiDigits.T163EvenBBPDyadicLift.scaledBBPRat_two_val_even
#print axioms Theory.PiDigits.T163EvenBBPDyadicLift.scaledBBPRat_even_two_primary
#print axioms Theory.PiDigits.T163EvenBBPDyadicLift.scaledBBPRat_even_tail_lt_spacing
#print axioms Theory.PiDigits.T163EvenBBPDyadicLift.scaledBBPRat_even_unique_immediate_lift
