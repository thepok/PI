import TheoryLib.PiQuantitativeBlockHitting.T106T106BBPForcedOrbit

/-!
# T112: exact selected-residue representation of the sampled BBP orbit

At time `N`, all four statements use the single synchronized rational
`(10 : ℚ)^N * bbpPartial (7 * N)`.  They expose its actual reduced numerator
and denominator.  No cancellation, density, coverage, normality, or V1 claim
is made here.
-/

noncomputable section

namespace Theory.PiDigits.T112SampledBBPSelectedResidue

open Finset BigOperators

private theorem fract_ratCast_eq_num_emod_den (q : ℚ) :
    Int.fract (q : ℝ) =
      (((q.num % (q.den : ℤ) : ℤ) : ℝ)) / (q.den : ℝ) := by
  rw [Rat.cast_def, Int.fract_div_intCast_eq_div_intCast_mod]

theorem ratCast_circle_eq_num_emod_den (q : ℚ) :
    (((q : ℝ) : UnitAddCircle)) =
      ((((q.num % (q.den : ℤ) : ℤ) : ℝ) / (q.den : ℝ) : ℝ) : UnitAddCircle) := by
  calc
    (((q : ℝ) : UnitAddCircle)) =
        ((Int.fract (q : ℝ) : ℝ) : UnitAddCircle) :=
      (AddCircle.coe_fract (q : ℝ)).symm
    _ = ((((q.num % (q.den : ℤ) : ℤ) : ℝ) / (q.den : ℝ) : ℝ) :
        UnitAddCircle) := by rw [fract_ratCast_eq_num_emod_den]

private theorem scaled_bbpPartial_cast_eq (N : ℕ) :
    ((10 : ℝ) ^ N *
        ((Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N) : ℚ) : ℝ)) =
      (((10 : ℚ) ^ N *
          Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N) : ℚ) :
        ℝ) := by
  push_cast
  rfl

theorem sampledBBPOrbit_coe_eq_selectedResidue (N : ℕ) :
    let qN : ℚ := (10 : ℚ) ^ N *
      Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)
    ((Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit N : ℝ) : UnitAddCircle) =
      ((((qN.num % (qN.den : ℤ) : ℤ) : ℝ) / (qN.den : ℝ) : ℝ) : UnitAddCircle) := by
  intro qN
  change ((Int.fract ((10 : ℝ) ^ N *
      ((Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N) : ℚ) : ℝ)) :
      ℝ) : UnitAddCircle) = _
  rw [AddCircle.coe_fract, scaled_bbpPartial_cast_eq]
  exact ratCast_circle_eq_num_emod_den qN

theorem phase_sampledBBPOrbit_eq_selectedResidue (h : ℤ) (N : ℕ) :
    let qN : ℚ := (10 : ℚ) ^ N *
      Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)
    Theory.PiDigits.T27.phase h
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit N) =
      Theory.PiDigits.T27.phase h
        ((((qN.num % (qN.den : ℤ) : ℤ) : ℝ) / (qN.den : ℝ))) := by
  intro qN
  calc
    Theory.PiDigits.T27.phase h
        (Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit N) =
      Theory.PiDigits.T27.phase h (Int.fract ((10 : ℝ) ^ N *
          ((Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N) : ℚ) :
            ℝ))) := rfl
    _ = Theory.PiDigits.T27.phase h ((10 : ℝ) ^ N *
          ((Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N) : ℚ) :
            ℝ)) :=
        Theory.PiDigits.T29.phase_fract_eq_phase h _
    _ = Theory.PiDigits.T27.phase h ((qN : ℚ) : ℝ) := by
        rw [scaled_bbpPartial_cast_eq]
    _ = Theory.PiDigits.T27.phase h (Int.fract ((qN : ℚ) : ℝ)) :=
        (Theory.PiDigits.T29.phase_fract_eq_phase h _).symm
    _ = Theory.PiDigits.T27.phase h
          ((((qN.num % (qN.den : ℤ) : ℤ) : ℝ) / (qN.den : ℝ))) := by
        rw [fract_ratCast_eq_num_emod_den]

theorem exponentialSum_sampledBBP_eq_selectedResidue (M : ℕ) (h : ℤ) :
    Theory.PiDigits.T27.exponentialSum
        Theory.PiDigits.T106BBPForcedOrbit.sampledBBPOrbit M h =
      ∑ N ∈ Finset.range M,
        let qN : ℚ := (10 : ℚ) ^ N *
          Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N)
        Theory.PiDigits.T27.phase h
          ((((qN.num % (qN.den : ℤ) : ℤ) : ℝ) / (qN.den : ℝ))) := by
  apply sum_congr rfl
  intro N _
  exact phase_sampledBBPOrbit_eq_selectedResidue h N

end Theory.PiDigits.T112SampledBBPSelectedResidue
