import TheoryLib.PiQuantitativeBlockHitting.T129T129BoundaryKernelNormalizedComparison

/-!
# T130: nonzero boundary-coefficient algebra

This file verifies the piecewise cubic coefficient calculation behind the
normalized comparison of the Jackson and boundary-matched kernels, and the
exact gain identity for their actual frequency-aggregated presentations.  The
remaining combinatorial bridge identifying the actual nonzero Fejer-square
frequency fibers with `cubicMultiplicity` is not asserted here.  It is a
finite algebraic statement and does not assert cancellation for the decimal
orbit of pi.
-/

noncomputable section

namespace Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra

open Theory.PiDigits.BoundaryKernelRatioAlgebra
open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.AggregatedJacksonFrontier
open Theory.PiDigits.BoundaryMatchedKernel

/-- A finite presentation of `F_q^2` on the existing Jackson index type.  It
uses the main quadruples and gives every edge-pair index coefficient zero. -/
def fejerSquarePresentationCoefficient (q : ℕ) : JacksonIndex q → ℝ
  | Sum.inl _ => 1 / (q : ℝ) ^ 2
  | Sum.inr _ => 0

/-- The actual main-quadruple multiplicity at an integer frequency. -/
def mainFrequencyMultiplicity (q : ℕ) (h : ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter fun x =>
    jacksonFrequency (Sum.inl x) = h).card

/-- Aggregating the finite presentation of `F_q^2` is exactly the cardinality
of the corresponding main-frequency fiber, divided by `q^2`. -/
lemma aggregatedFejerSquareCoefficient_eq_card (q : ℕ) (h : ℤ) :
    aggregatedCoefficient (fejerSquarePresentationCoefficient q)
        (@jacksonFrequency q) h =
      (mainFrequencyMultiplicity q h : ℝ) / (q : ℝ) ^ 2 := by
  classical
  unfold aggregatedCoefficient mainFrequencyMultiplicity
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [fejerSquarePresentationCoefficient]
  rw [show (∑ x : Fin q × Fin q × Fin q × Fin q,
      if jacksonFrequency (Sum.inl x) = h then 1 / (q : ℝ) ^ 2 else 0) =
      (((Finset.univ : Finset (Fin q × Fin q × Fin q × Fin q)).filter fun x =>
          jacksonFrequency (Sum.inl x) = h).card : ℝ) /
        (q : ℝ) ^ 2 by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring]
  simp

/-- Before aggregation, the boundary kernel differs from the Jackson kernel
by exactly `delta_q F_q^2`. -/
lemma boundaryCoefficient_eq_jackson_add
    (q : ℕ) (i : JacksonIndex q) :
    boundaryCoefficient q i = jacksonCoefficient q q i +
      (1 - 2 / (q : ℝ) ^ 2 - Real.cos (Real.pi / q)) *
        fejerSquarePresentationCoefficient q i := by
  rcases i with i | i
  · simp only [boundaryCoefficient, jacksonCoefficient,
      fejerSquarePresentationCoefficient]
    ring
  · simp only [boundaryCoefficient, jacksonCoefficient,
      fejerSquarePresentationCoefficient, mul_zero, add_zero]

/-- The same gain identity after collecting every repeated frequency. -/
theorem aggregatedBoundaryCoefficient_eq_jackson_add
    (q : ℕ) (h : ℤ) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q) h =
      aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) h +
        (1 - 2 / (q : ℝ) ^ 2 - Real.cos (Real.pi / q)) *
          aggregatedCoefficient (fejerSquarePresentationCoefficient q)
            (@jacksonFrequency q) h := by
  classical
  unfold aggregatedCoefficient
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [boundaryCoefficient_eq_jackson_add]

private def topEdgeIndex (q : ℕ) (hq : 0 < q) : JacksonIndex q :=
  Sum.inr ((false, ⟨q - 1, by omega⟩), (true, ⟨0, hq⟩))

private lemma topEdgeIndex_frequency (q : ℕ) (hq : 0 < q) :
    jacksonFrequency (topEdgeIndex q hq) = 2 * (q : ℤ) - 1 := by
  simp [topEdgeIndex, jacksonFrequency, edgeFrequency]
  omega

private lemma jacksonFrequency_eq_top_unique
    (q : ℕ) (hq : 0 < q) (i : JacksonIndex q)
    (hi : jacksonFrequency i = 2 * (q : ℤ) - 1) :
    i = topEdgeIndex q hq := by
  rcases i with ⟨⟨r, s, u, v⟩⟩ | ⟨⟨⟨bi, i⟩, ⟨bj, j⟩⟩⟩
  · simp only [jacksonFrequency] at hi
    have hr := r.isLt
    have hs := s.isLt
    have hu := u.isLt
    have hv := v.isLt
    omega
  · cases bi <;> cases bj
    · simp only [jacksonFrequency, edgeFrequency] at hi
      have hii := i.isLt
      have hjj := j.isLt
      push_cast at hi
      omega
    · simp only [jacksonFrequency, edgeFrequency] at hi
      have hii := i.isLt
      have hjj := j.isLt
      have hiLast : i.val = q - 1 := by omega
      have hjZero : j.val = 0 := by omega
      have hiEq : i = ⟨q - 1, by omega⟩ := Fin.ext hiLast
      have hjEq : j = ⟨0, hq⟩ := Fin.ext hjZero
      simp [hiEq, hjEq, topEdgeIndex]
    · simp only [jacksonFrequency, edgeFrequency] at hi
      have hii := i.isLt
      have hjj := j.isLt
      push_cast at hi
      omega
    · simp only [jacksonFrequency, edgeFrequency] at hi
      have hii := i.isLt
      have hjj := j.isLt
      push_cast at hi
      omega

/-- At the outer positive endpoint, the actual aggregated Jackson coefficient
is the single surviving edge-pair coefficient. -/
theorem aggregatedJacksonCoefficient_top (q : ℕ) (hq : 0 < q) :
    aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q)
        (2 * (q : ℤ) - 1) = 1 / (2 * (q : ℝ) ^ 2) := by
  classical
  unfold aggregatedCoefficient
  rw [Finset.sum_eq_single (topEdgeIndex q hq)]
  · simp [topEdgeIndex, jacksonCoefficient, edgeSign]
  · intro b hb hne
    exact (hne (jacksonFrequency_eq_top_unique q hq b
      (Finset.mem_filter.mp hb).2)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, topEdgeIndex_frequency q hq⟩)).elim

/-- The boundary-matched coefficient agrees with Jackson at the outer
positive endpoint, since `F_q^2` itself has no coefficient there. -/
theorem aggregatedBoundaryCoefficient_top (q : ℕ) (hq : 0 < q) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q)
        (2 * (q : ℤ) - 1) = 1 / (2 * (q : ℝ) ^ 2) := by
  classical
  unfold aggregatedCoefficient
  rw [Finset.sum_eq_single (topEdgeIndex q hq)]
  · simp [topEdgeIndex, boundaryCoefficient, edgeSign]
  · intro b hb hne
    exact (hne (jacksonFrequency_eq_top_unique q hq b
      (Finset.mem_filter.mp hb).2)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, topEdgeIndex_frequency q hq⟩)).elim

/-- The normalized improvement holds for the actual aggregated coefficient at
the outer endpoint of the support.  This endpoint needs no cubic fiber count:
only one edge pair survives. -/
theorem normalized_aggregatedBoundary_top_lt_jackson
    (q : ℕ) (hq : 1 < q) :
    aggregatedCoefficient (boundaryCoefficient q) (@jacksonFrequency q)
          (2 * (q : ℤ) - 1) /
        Theory.PiDigits.BoundaryMatchedKernel.boundaryZeroCoefficient q <
      aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q)
          (2 * (q : ℤ) - 1) /
        aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 := by
  rw [aggregatedBoundaryCoefficient_top q (by omega),
    aggregatedJacksonCoefficient_top q (by omega)]
  have hnum : 0 < 1 / (2 * (q : ℝ) ^ 2) := by positivity
  have hJzero : 0 <
      aggregatedCoefficient (jacksonCoefficient q q) (@jacksonFrequency q) 0 := by
    rw [Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_eq
      q (by omega)]
    positivity
  exact div_lt_div_of_pos_left hnum hJzero
    (Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_lt_boundaryZeroCoefficient
      q hq)

/-- The closed cubic candidate for the unnormalised multiplicity of frequency
`h` in the square of the order-`q` triangular Fejer coefficient family.  The
two pieces agree at `h=q`.  The combinatorial identification with the actual
fiber of `jacksonFrequency` is kept separate from the algebra below. -/
def cubicMultiplicity (q h : ℕ) : ℝ :=
  if h ≤ q then
    (4 * (q : ℝ) ^ 3 + 2 * q - 6 * q * (h : ℝ) ^ 2 +
      3 * (h : ℝ) ^ 3 - 3 * h) / 6
  else
    ((2 * q - h - 1 : ℝ) * (2 * q - h : ℝ) *
      (2 * q - h + 1 : ℝ)) / 6

/-- The coefficient `B_q(h)` of `F_q^2` on the nonnegative half-support. -/
def fejerSquareCoefficient (q h : ℕ) : ℝ :=
  cubicMultiplicity q h / (q : ℝ) ^ 2

/-- The neighbouring average `M_q(h)`. -/
def neighboringCoefficient (q h : ℕ) : ℝ :=
  (fejerSquareCoefficient q (h - 1) +
    fejerSquareCoefficient q (h + 1)) / 2

/-- The coefficient of `(cos(2*pi*t)-beta) F_q(t)^2` at positive frequency
`h`, in closed form. -/
def affineCoefficient (q h : ℕ) (beta : ℝ) : ℝ :=
  neighboringCoefficient q h - beta * fejerSquareCoefficient q h

lemma cubicMultiplicity_zero (q : ℕ) :
    cubicMultiplicity q 0 = (2 * (q : ℝ) ^ 3 + q) / 3 := by
  simp [cubicMultiplicity]
  ring

lemma cubicMultiplicity_one (q : ℕ) (hq : 1 ≤ q) :
    cubicMultiplicity q 1 = 2 * (q : ℝ) * ((q : ℝ) ^ 2 - 1) / 3 := by
  simp [cubicMultiplicity, hq]
  ring

lemma fejerSquareCoefficient_zero (q : ℕ) (hq : 0 < q) :
    fejerSquareCoefficient q 0 = (2 * (q : ℝ) ^ 2 + 1) / (3 * q) := by
  rw [fejerSquareCoefficient, cubicMultiplicity_zero]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

lemma fejerSquareCoefficient_one (q : ℕ) (hq : 1 ≤ q) :
    fejerSquareCoefficient q 1 = 2 * ((q : ℝ) ^ 2 - 1) / (3 * q) := by
  rw [fejerSquareCoefficient, cubicMultiplicity_one q hq]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp

private lemma crossDeterminant_first_piece
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhq : h ≤ q) :
    fejerSquareCoefficient q 0 * neighboringCoefficient q h -
        fejerSquareCoefficient q 1 * fejerSquareCoefficient q h =
      (h : ℝ) * ((h : ℝ) ^ 2 - 2 * q * h + 2 * (q : ℝ) ^ 2) /
        (2 * (q : ℝ) ^ 3) := by
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  have hhm1 : h - 1 ≤ q := by omega
  have hhp1_cases : h + 1 ≤ q ∨ h = q := by omega
  rw [fejerSquareCoefficient_zero q hq0,
    fejerSquareCoefficient_one q (Nat.one_le_iff_ne_zero.mpr hq0.ne')]
  rcases hhp1_cases with hhp1 | heq
  · simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
      if_pos hhq, if_pos hhm1, if_pos hhp1]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ h)]
    norm_num
    field_simp
    ring
  · subst h
    have hqm1 : q - 1 ≤ q := by omega
    have hqpn : ¬ q + 1 ≤ q := by omega
    simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
      if_pos (le_refl q), if_pos hqm1, if_neg hqpn]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
    field_simp
    ring

private lemma crossDeterminant_second_piece
    (q h : ℕ) (hq : 1 < q) (hhq : q < h) (hhsupp : h ≤ 2 * q - 1) :
    fejerSquareCoefficient q 0 * neighboringCoefficient q h -
        fejerSquareCoefficient q 1 * fejerSquareCoefficient q h =
      ((2 * q - h : ℕ) : ℝ) *
          ((h : ℝ) ^ 2 - 4 * q * h + 6 * (q : ℝ) ^ 2) /
        (6 * (q : ℝ) ^ 3) := by
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  have hhnot : ¬ h ≤ q := by omega
  have hhp1not : ¬ h + 1 ≤ q := by omega
  rw [fejerSquareCoefficient_zero q hq0,
    fejerSquareCoefficient_one q (Nat.one_le_iff_ne_zero.mpr hq0.ne')]
  by_cases hnear : h ≤ q + 1
  · have heq : h = q + 1 := by omega
    subst h
    have hqm1 : q + 1 - 1 ≤ q := by omega
    have hq1not : ¬ q + 1 ≤ q := by omega
    have hq2not : ¬ q + 1 + 1 ≤ q := by omega
    simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
      if_pos hqm1, if_neg hq1not, if_neg hq2not]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    rw [Nat.cast_sub (by omega : q + 1 ≤ 2 * q)]
    push_cast
    field_simp
    ring
  · have hhm1not : ¬ h - 1 ≤ q := by omega
    simp only [neighboringCoefficient, fejerSquareCoefficient, cubicMultiplicity,
      if_neg hhnot, if_neg hhm1not, if_neg hhp1not]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ h)]
    rw [Nat.cast_sub (by omega : h ≤ 2 * q)]
    norm_num
    field_simp
    ring

/-- Exact piecewise cross determinant controlling every normalized nonzero
coefficient in the useful support. -/
theorem crossDeterminant_eq
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    fejerSquareCoefficient q 0 * neighboringCoefficient q h -
        fejerSquareCoefficient q 1 * fejerSquareCoefficient q h =
      if h ≤ q then
        (h : ℝ) * ((h : ℝ) ^ 2 - 2 * q * h + 2 * (q : ℝ) ^ 2) /
          (2 * (q : ℝ) ^ 3)
      else
        ((2 * q - h : ℕ) : ℝ) *
            ((h : ℝ) ^ 2 - 4 * q * h + 6 * (q : ℝ) ^ 2) /
          (6 * (q : ℝ) ^ 3) := by
  split_ifs with hhq
  · exact crossDeterminant_first_piece q h hq hh0 hhq
  · exact crossDeterminant_second_piece q h hq (by omega) hhsupp

/-- The piecewise cross determinant is strictly positive at every positive
frequency in the support. -/
theorem crossDeterminant_pos
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    0 < fejerSquareCoefficient q 0 * neighboringCoefficient q h -
      fejerSquareCoefficient q 1 * fejerSquareCoefficient q h := by
  rw [crossDeterminant_eq q h hq hh0 hhsupp]
  split_ifs with hhq
  · have hqR : (0 : ℝ) < q := by positivity
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
    have hsquare : 0 <
        (h : ℝ) ^ 2 - 2 * q * h + 2 * (q : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((h : ℝ) - q)]
    exact div_pos (mul_pos hhR hsquare) (by positivity)
  · have hgap : 0 < 2 * q - h := by omega
    have hgapR : (0 : ℝ) < (2 * q - h : ℕ) := by exact_mod_cast hgap
    have hsquare : 0 <
        (h : ℝ) ^ 2 - 4 * q * h + 6 * (q : ℝ) ^ 2 := by
      have hqR : (0 : ℝ) < q := by positivity
      nlinarith [sq_nonneg ((h : ℝ) - 2 * q)]
    exact div_pos (mul_pos hgapR hsquare) (by positivity)

/-- The signed zero coefficient of the affine cosine--Fejer-squared family. -/
def affineZeroCoefficient (q : ℕ) (beta : ℝ) : ℝ :=
  fejerSquareCoefficient q 1 - beta * fejerSquareCoefficient q 0

/-- The old order-`q` Jackson parameter. -/
def jacksonBeta (q : ℕ) : ℝ := 1 - 2 / (q : ℝ) ^ 2

lemma affineZeroCoefficient_jackson (q : ℕ) (hq : 1 < q) :
    affineZeroCoefficient q (jacksonBeta q) =
      ((q : ℝ) ^ 2 + 2) / (3 * (q : ℝ) ^ 3) := by
  rw [affineZeroCoefficient, jacksonBeta,
    fejerSquareCoefficient_zero q (by omega),
    fejerSquareCoefficient_one q (by omega)]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma affineZeroCoefficient_boundary (q : ℕ) (hq : 1 < q) :
    affineZeroCoefficient q (Real.cos (Real.pi / q)) =
      Theory.PiDigits.BoundaryMatchedKernel.boundaryZeroCoefficient q := by
  rw [affineZeroCoefficient,
    fejerSquareCoefficient_zero q (by omega),
    fejerSquareCoefficient_one q (by omega),
    Theory.PiDigits.BoundaryKernelNormalizedComparison.boundaryZeroCoefficient_eq
      q (by omega)]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp

lemma boundaryBeta_lt_jacksonBeta (q : ℕ) (hq : 1 < q) :
    Real.cos (Real.pi / q) < jacksonBeta q := by
  have hzero :=
    Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_lt_boundaryZeroCoefficient
      q hq
  rw [Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_eq
      q (by omega),
    ← affineZeroCoefficient_jackson q hq,
    ← affineZeroCoefficient_boundary q hq] at hzero
  unfold affineZeroCoefficient at hzero
  have hB0 : 0 < fejerSquareCoefficient q 0 := by
    rw [fejerSquareCoefficient_zero q (by omega)]
    positivity
  nlinarith

/-- On the whole positive half-support, every boundary-matched nonzero
coefficient is strictly smaller after normalization by its own zero mode than
the corresponding Jackson coefficient. -/
theorem normalized_boundary_lt_jackson
    (q h : ℕ) (hq : 1 < q) (hh0 : 0 < h) (hhsupp : h ≤ 2 * q - 1) :
    affineCoefficient q h (Real.cos (Real.pi / q)) /
        affineZeroCoefficient q (Real.cos (Real.pi / q)) <
      affineCoefficient q h (jacksonBeta q) /
        affineZeroCoefficient q (jacksonBeta q) := by
  apply normalizedAffineCoefficient_strictMono
    (fejerSquareCoefficient q 0) (fejerSquareCoefficient q 1)
    (neighboringCoefficient q h) (fejerSquareCoefficient q h)
    (Real.cos (Real.pi / q)) (jacksonBeta q)
  · exact boundaryBeta_lt_jacksonBeta q hq
  · change 0 < affineZeroCoefficient q (Real.cos (Real.pi / q))
    rw [affineZeroCoefficient_boundary q hq]
    have hjpos : 0 <
        Theory.PiDigits.AggregatedJacksonFrontier.aggregatedCoefficient
          (Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonCoefficient q q)
          (@Theory.PiDigits.PiNaturalScaleResonanceObstruction.jacksonFrequency q) 0 := by
      rw [Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_eq
        q (by omega)]
      positivity
    exact hjpos.trans
      (Theory.PiDigits.BoundaryKernelNormalizedComparison.jacksonZeroCoefficient_lt_boundaryZeroCoefficient
        q hq)
  · change 0 < affineZeroCoefficient q (jacksonBeta q)
    rw [affineZeroCoefficient_jackson q hq]
    positivity
  · exact crossDeterminant_pos q h hq hh0 hhsupp

end Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra

#print axioms Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.crossDeterminant_eq
#print axioms Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.crossDeterminant_pos
#print axioms Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.aggregatedBoundaryCoefficient_eq_jackson_add
#print axioms Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.normalized_aggregatedBoundary_top_lt_jackson
#print axioms Theory.PiDigits.BoundaryNonzeroCoefficientAlgebra.normalized_boundary_lt_jackson
