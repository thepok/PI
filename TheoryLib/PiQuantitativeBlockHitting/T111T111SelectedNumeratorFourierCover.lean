import TheoryLib.PiPositiveDecimalFactorEntropy.T18T18FiniteCircleQuantization

/-!
# T111: finite signed-DFT occupancy and endpoint-safe circle cover

For an arbitrary finite real sample, the full discrete Fourier transform of
its `q`-mesh cell counts recovers each exact cell multiplicity. A strictly
one-sided lower bound on the signed nonzero-frequency sum therefore forces
that cell to be occupied. Full cell occupancy then gives a `1/q` cover in the
quotient metric on `UnitAddCircle`, including the zero/one endpoint.

These are generic finite certificates. They assert no BBP estimate, density,
normality, prescribed digit occurrence, or V1 statement for pi.
-/

namespace Theory.PiDigits.T111SelectedNumeratorFourierCover

open Finset
open scoped Metric

private theorem cellSum_ite {M q : ℕ} [NeZero q] (x : Fin M → ℝ)
    (a : ZMod q) (j : Fin M) :
    (∑ h : ZMod q,
        ZMod.stdAddChar (h *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
      ((if DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j = a
          then q else 0 : ℕ) : ℂ) := by
  rw [AddChar.sum_mulShift
    (b := DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a)
    (ZMod.isPrimitive_stdAddChar q)]
  have hcard : Fintype.card (ZMod q) = q := by simp
  rcases eq_or_ne
      (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j) a with he | he
  · simp [he, hcard]
  · simp [sub_eq_zero, he]

/-- The full cell-centered DFT is exactly the mesh size times the number of
sample points in the selected cell. -/
theorem fullDFTSum_eq_mul_orbitCellMultiplicity {M q : ℕ} [NeZero q]
    (x : Fin M → ℝ) (a : ZMod q) :
    (∑ h : ZMod q, ∑ j : Fin M,
        ZMod.stdAddChar (h *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
      ((q * DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMultiplicity x a : ℕ) :
        ℂ) := by
  classical
  have hm : DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMultiplicity x a =
      ((Finset.univ : Finset (Fin M)).filter
        (fun j =>
          DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j = a)).card := rfl
  have hnat : (∑ j : Fin M,
        (if DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j = a
          then q else 0 : ℕ)) =
      q * DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMultiplicity x a := by
    rw [hm, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hstep : (∑ j : Fin M, ∑ h : ZMod q,
        ZMod.stdAddChar (h *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
      (((∑ j : Fin M,
          (if DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j = a
            then q else 0 : ℕ)) : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => cellSum_ite x a j
  rw [Finset.sum_comm, hstep, hnat]

/-- If the real part of the signed nonzero-frequency DFT is strictly larger
than `-M`, then the selected cell is occupied. -/
theorem signedDFTTrough_implies_cell_hit {M q : ℕ} [NeZero q]
    (x : Fin M → ℝ) (a : ZMod q)
    (htrough : -(M : ℝ) <
      (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ j : Fin M,
        ZMod.stdAddChar (h *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))).re) :
    0 < DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMultiplicity x a := by
  classical
  rcases Nat.eq_zero_or_pos
      (DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMultiplicity x a) with h0 | hpos
  · exfalso
    have hsplit :
        (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ j : Fin M,
            ZMod.stdAddChar (h *
              (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) +
          (∑ j : Fin M, ZMod.stdAddChar ((0 : ZMod q) *
            (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
        ∑ h : ZMod q, ∑ j : Fin M,
          ZMod.stdAddChar (h *
            (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a)) :=
      Finset.sum_erase_add Finset.univ
        (fun h => ∑ j : Fin M, ZMod.stdAddChar (h *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a)))
        (Finset.mem_univ 0)
    have hzero : (∑ j : Fin M, ZMod.stdAddChar ((0 : ZMod q) *
          (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
        ((M : ℕ) : ℂ) := by
      simp
    have hfull : (∑ h : ZMod q, ∑ j : Fin M,
          ZMod.stdAddChar (h *
            (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
        (0 : ℂ) := by
      rw [fullDFTSum_eq_mul_orbitCellMultiplicity x a, h0]
      simp
    have hsum0 :
        (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ j : Fin M,
            ZMod.stdAddChar (h *
              (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) +
          (∑ j : Fin M, ZMod.stdAddChar ((0 : ZMod q) *
            (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
        (0 : ℂ) := hsplit.trans hfull
    have hneg :
        (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ j : Fin M,
            ZMod.stdAddChar (h *
              (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))) =
          (-(M : ℕ) : ℂ) := by
      rw [eq_neg_of_add_eq_zero_left hsum0, hzero]
    have hre :
        (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ∑ j : Fin M,
            ZMod.stdAddChar (h *
              (DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbit x q j - a))).re =
          -(M : ℝ) := by
      rw [hneg]
      simp
    rw [hre] at htrough
    linarith
  · exact hpos

private theorem abs_fract_sub_le_inv_of_cyclicCell_eq {q : ℕ} (hq : 0 < q)
    {u v : ℝ}
    (hcell : DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q u =
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q v) :
    |Int.fract v - Int.fract u| ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell at hcell
  have hF0 : (0 : ℤ) ≤ ⌊(q : ℝ) * Int.fract u⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hqR.le (Int.fract_nonneg u))
  have hFM : ⌊(q : ℝ) * Int.fract u⌋ < (q : ℤ) := by
    rw [Int.floor_lt]
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one u) hqR
  have hG0 : (0 : ℤ) ≤ ⌊(q : ℝ) * Int.fract v⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hqR.le (Int.fract_nonneg v))
  have hGM : ⌊(q : ℝ) * Int.fract v⌋ < (q : ℤ) := by
    rw [Int.floor_lt]
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one v) hqR
  have hF : ⌊(q : ℝ) * Int.fract u⌋ = ⌊(q : ℝ) * Int.fract v⌋ := by
    rw [ZMod.intCast_eq_intCast_iff'] at hcell
    rwa [Int.emod_eq_of_lt hF0 hFM, Int.emod_eq_of_lt hG0 hGM] at hcell
  have hulo : (((⌊(q : ℝ) * Int.fract u⌋ : ℤ) : ℝ)) ≤
      (q : ℝ) * Int.fract u := Int.floor_le _
  have huhi : (q : ℝ) * Int.fract u <
      (((⌊(q : ℝ) * Int.fract u⌋ : ℤ) : ℝ)) + 1 := Int.lt_floor_add_one _
  have hvlo : (((⌊(q : ℝ) * Int.fract v⌋ : ℤ) : ℝ)) ≤
      (q : ℝ) * Int.fract v := Int.floor_le _
  have hvhi : (q : ℝ) * Int.fract v <
      (((⌊(q : ℝ) * Int.fract v⌋ : ℤ) : ℝ)) + 1 := Int.lt_floor_add_one _
  rw [← hF] at hvlo hvhi
  have hub : (q : ℝ) * (Int.fract v - Int.fract u) ≤ 1 := by linarith
  have hqinv : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hqR)
  have hdub : Int.fract v - Int.fract u ≤ (q : ℝ)⁻¹ :=
    le_of_mul_le_mul_left (hub.trans_eq hqinv.symm) hqR
  have hdlb : -(q : ℝ)⁻¹ ≤ Int.fract v - Int.fract u := by
    have hneg : (q : ℝ) * -(Int.fract v - Int.fract u) ≤ 1 := by linarith
    have hbound := le_of_mul_le_mul_left (hneg.trans_eq hqinv.symm) hqR
    linarith
  rw [abs_le]
  exact ⟨hdlb, hdub⟩

/-- Equal cyclic mesh cells imply quotient-circle distance at most one mesh
width, without replacing the quotient metric by ordinary real distance. -/
theorem circleDist_le_inv_of_cyclicCell_eq {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (hcell : DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q x =
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q y) :
    dist ((x : ℝ) : UnitAddCircle) ((y : ℝ) : UnitAddCircle) ≤ (q : ℝ)⁻¹ := by
  have hd : |Int.fract y - Int.fract x| ≤ (q : ℝ)⁻¹ :=
    abs_fract_sub_le_inv_of_cyclicCell_eq hq hcell
  have hshift : x - y - (((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)) =
      Int.fract x - Int.fract y := by
    simp only [Int.fract]
    push_cast
    ring
  calc
    dist ((x : ℝ) : UnitAddCircle) ((y : ℝ) : UnitAddCircle) =
        ‖((x : ℝ) : UnitAddCircle) - ((y : ℝ) : UnitAddCircle)‖ := dist_eq_norm _ _
    _ = ‖(((x - y : ℝ)) : UnitAddCircle)‖ := by rw [AddCircle.coe_sub]
    _ = |(x - y : ℝ) - round (x - y)| := UnitAddCircle.norm_eq
    _ ≤ |(x - y : ℝ) - (((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ))| := round_le _ _
    _ = |Int.fract x - Int.fract y| := by rw [hshift]
    _ ≤ (q : ℝ)⁻¹ := by rwa [abs_sub_comm]

/-- Hitting every cyclic mesh cell gives a `1/q` cover of `UnitAddCircle`. -/
theorem all_cyclicCells_hit_implies_circleCover {M q : ℕ} (hq : 0 < q)
    (x : Fin M → ℝ)
    (hhit : ∀ a : ZMod q, ∃ j : Fin M,
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q (x j) = a)
    (y : UnitAddCircle) :
    ∃ j : Fin M,
      dist (((x j : ℝ) : UnitAddCircle)) y ≤ (q : ℝ)⁻¹ := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨j, hj⟩ :=
    hhit (DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q t)
  exact ⟨j, circleDist_le_inv_of_cyclicCell_eq hq hj⟩

end Theory.PiDigits.T111SelectedNumeratorFourierCover
