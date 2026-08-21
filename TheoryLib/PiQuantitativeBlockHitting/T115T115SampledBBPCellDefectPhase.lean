import TheoryLib.PiQuantitativeBlockHitting.T111T111SelectedNumeratorFourierCover
import TheoryLib.PiQuantitativeBlockHitting.T114T114SampledBBPGCDNormalizedSuccessor

/-!
# T115: exact sampled BBP cell-defect phase

This module factors a centered cyclic-cell character through the actual
reduced sampled BBP residue and its exact Euclidean floor defect.  It is a
pointwise algebraic identity only: no finite sum, occupancy, cancellation,
density, normality, or V1 conclusion is claimed.
-/

noncomputable section

namespace Theory.PiDigits.T115SampledBBPCellDefectPhase

/-- The synchronized reduced rational `10^N * bbpPartial (7*N)`. -/
def scaledBBPRat (N : ℕ) : ℚ :=
  (10 : ℚ) ^ N * Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)

/-- Its actual reduced numerator modulo its full reduced denominator. -/
def residueNum (N : ℕ) : ℤ :=
  (scaledBBPRat N).num % (scaledBBPRat N).den

/-- Its full positive reduced denominator. -/
def residueDen (N : ℕ) : ℕ :=
  (scaledBBPRat N).den

/-- The Euclidean cell quotient of `q * residueNum N` by `residueDen N`. -/
def cellQuotient (q N : ℕ) : ℤ :=
  ((q : ℤ) * residueNum N) / (residueDen N : ℤ)

/-- The corresponding Euclidean remainder. -/
def cellRemainder (q N : ℕ) : ℤ :=
  ((q : ℤ) * residueNum N) % (residueDen N : ℤ)

/-- The exact real floor defect `remainder / (q * denominator)`. -/
noncomputable def cellDefect (q N : ℕ) : ℝ :=
  (cellRemainder q N : ℝ) / ((q : ℝ) * (residueDen N : ℝ))

/-- Exact Euclidean identity `q*r = D*c + e`. -/
theorem mul_residue_eq_den_mul_cell_add_remainder (q N : ℕ) :
    (q : ℤ) * residueNum N =
      (residueDen N : ℤ) * cellQuotient q N + cellRemainder q N := by
  have h := Int.mul_ediv_add_emod ((q : ℤ) * residueNum N) (residueDen N : ℤ)
  simp only [cellQuotient, cellRemainder]
  linarith

/-- At the zero mesh, quotient, remainder, and normalized defect all vanish. -/
theorem zero_mesh_data (N : ℕ) :
    cellQuotient 0 N = 0 ∧ cellRemainder 0 N = 0 ∧ cellDefect 0 N = 0 := by
  have hzero : ((0 : ℕ) : ℤ) * residueNum N = 0 := by simp
  constructor
  · simp only [cellQuotient, hzero, Int.zero_ediv]
  · refine ⟨by simp only [cellRemainder, hzero, Int.zero_emod], ?_⟩
    have hr : cellRemainder (0 : ℕ) N = 0 := by
      simp only [cellRemainder, hzero, Int.zero_emod]
    simp only [cellDefect, hr, Int.cast_zero, Nat.cast_zero, zero_mul, div_zero]

private theorem residueDen_pos (N : ℕ) : 0 < residueDen N := Rat.den_pos _

private theorem stdAddChar_intCast_mul {q : ℕ} [NeZero q]
    (h : ZMod q) (m : ℤ) :
    ZMod.stdAddChar (h * (m : ZMod q)) =
      Complex.exp
        ((2 : ℂ) * Real.pi * Complex.I * ((h.val : ℤ) : ℂ) *
          (m : ℂ) / ((q : ℕ) : ℂ)) := by
  have hrep : h * (m : ZMod q) = (((h.val : ℤ) * m : ℤ) : ZMod q) := by
    calc
      h * (m : ZMod q) = (h.val : ZMod q) * (m : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
      _ = ((h.val : ℤ) : ZMod q) * (m : ZMod q) := by norm_cast
      _ = (((h.val : ℤ) * m : ℤ) : ZMod q) := by
        exact (map_mul (Int.castRingHom (ZMod q)) (h.val : ℤ) m).symm
  rw [hrep, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem stdAddChar_intCast_mul_eq_phase {q : ℕ} [NeZero q]
    (h : ZMod q) (m : ℤ) :
    ZMod.stdAddChar (h * (m : ZMod q)) =
      Theory.PiDigits.T27.phase (h.val : ℤ) ((m : ℝ) / (q : ℝ)) := by
  rw [stdAddChar_intCast_mul]
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  field_simp

private theorem freq_split_real {q : ℕ} [NeZero q] (N : ℕ) :
    (cellQuotient q N : ℝ) / (q : ℝ) =
      (residueNum N : ℝ) / (residueDen N : ℝ) - cellDefect q N := by
  have hEu := mul_residue_eq_den_mul_cell_add_remainder q N
  have hD : (0 : ℝ) < residueDen N := by exact_mod_cast residueDen_pos N
  have hQ : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hEuR :
      (q : ℝ) * (residueNum N : ℝ) =
        (residueDen N : ℝ) * (cellQuotient q N : ℝ) +
          (cellRemainder q N : ℝ) := by
    exact_mod_cast hEu
  unfold cellDefect
  field_simp [ne_of_gt hD, ne_of_gt hQ]
  nlinarith [hEuR]

private theorem phase_neg_argument (h : ℤ) (x : ℝ) :
    Theory.PiDigits.T27.phase h (-x) = Theory.PiDigits.T27.phase (-h) x := by
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  ring

/-- Exact centered cell character: target, residue phase, and negative defect phase. -/
theorem centered_sampledBBPCell_character_eq_residue_mul_defect
    {q : ℕ} [NeZero q] (N : ℕ) (a h : ZMod q) :
    ZMod.stdAddChar (h *
      (DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit N) - a)) =
      ZMod.stdAddChar (-(h * a)) *
        Theory.PiDigits.T27.phase (h.val : ℤ)
          ((residueNum N : ℝ) / (residueDen N : ℝ)) *
        Theory.PiDigits.T27.phase (-(h.val : ℤ)) (cellDefect q N) := by
  have hcell :
      DecimalFactorComplexity.MicroscopicFullEntropy.cyclicCell q
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit N) =
          (cellQuotient q N : ZMod q) := by
    rw [Theory.PiDigits.T113SampledBBPReducedCellRecurrence.cyclicCell_sampledBBPOrbit_eq_selectedCell]
    rfl
  rw [hcell]
  have hcenter :
      h * ((cellQuotient q N : ZMod q) - a) =
        -(h * a) + h * (cellQuotient q N : ZMod q) := by ring
  rw [hcenter, AddChar.map_add_eq_mul, stdAddChar_intCast_mul_eq_phase,
    freq_split_real, sub_eq_add_neg, Theory.PiDigits.T27.phase_add_real,
    phase_neg_argument]
  ring

end Theory.PiDigits.T115SampledBBPCellDefectPhase
