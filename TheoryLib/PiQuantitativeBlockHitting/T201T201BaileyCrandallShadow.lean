import TheoryLib.PiQuantitativeBlockHitting.T200T200BaileyCrandallCoboundary
import TheoryLib.PiQuantitativeBlockHitting.T108T108BBPCircleDensityTransfer

/-!
# T201: corrected Bailey–Crandall circle shadow

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-04 (wave E3 rerun, one task per lemma), against the contracted
signatures of AllMath task pack t201; gate-checked per task; assembled by Codex
-/

noncomputable section
namespace Theory.PiDigits.T201BaileyCrandallShadow

open T200BaileyCrandallCoboundary

def y (n : ℕ) : ℝ := Int.fract (Y n)

def bcOrbit (n : ℕ) : UnitAddCircle :=
  ((y (n + 1) : ℝ) : UnitAddCircle)

def hexPiOrbit (n : ℕ) : UnitAddCircle :=
  (((16 : ℝ) ^ n * Real.pi : ℝ) : UnitAddCircle)

theorem Y_succ (n : ℕ) :
    Y (n + 1) = 16 * Y n + R n := by
  unfold Y
  rw [Finset.sum_range_succ]
  have hlast : (16 : ℝ) ^ (n + 1 - 1 - n) * R n = R n := by
    have h0 : n + 1 - 1 - n = 0 := by omega
    rw [h0, pow_zero, one_mul]
  rw [hlast, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hexp : n + 1 - 1 - k = (n - 1 - k) + 1 := by
    have hk' : k < n := Finset.mem_range.mp hk
    omega
  rw [hexp, pow_succ]
  ring

theorem corrected_circle_identity (n : ℕ) :
    bcOrbit n + ((tau (n + 1) : ℝ) : UnitAddCircle) = hexPiOrbit n := by
  have hY : Y (n + 1) + tau (n + 1) = (16 : ℝ) ^ n * Real.pi := by
    have h := Y_add_tau_eq_pow_mul_pi (n := n + 1) (by omega)
    rwa [Nat.add_sub_cancel] at h
  unfold bcOrbit hexPiOrbit y
  rw [AddCircle.coe_fract, ← AddCircle.coe_add, hY]

namespace HypothesisForms

theorem y_succ
    (hYSucc : ∀ m : ℕ, Y (m + 1) = 16 * Y m + R m)
    (n : ℕ) :
    y (n + 1) = Int.fract (16 * y n + R n) := by
  unfold y
  rw [hYSucc n]
  have hdecomp : Y n = ((⌊Y n⌋ : ℤ) : ℝ) + Int.fract (Y n) := by
    have h := Int.fract_add_floor (Y n)
    linarith [h]
  have hsplit : 16 * Y n + R n
      = (16 * Int.fract (Y n) + R n) + ((16 * ⌊Y n⌋ : ℤ) : ℝ) := by
    conv_lhs => rw [hdecomp]
    push_cast
    ring
  rw [hsplit, Int.fract_add_intCast]

theorem circleDist_bcOrbit_hexPiOrbit_le
    (hCorrected : ∀ m : ℕ,
      bcOrbit m + ((tau (m + 1) : ℝ) : UnitAddCircle) = hexPiOrbit m)
    (n : ℕ) :
    dist (bcOrbit n) (hexPiOrbit n) ≤ tau (n + 1) := by
  have hpos : 0 ≤ tau (n + 1) := le_of_lt (tau_pos (n + 1))
  have hdiff' : hexPiOrbit n - bcOrbit n = ((tau (n + 1) : ℝ) : UnitAddCircle) := by
    conv_lhs => rw [← hCorrected n]
    exact add_sub_cancel_left _ _
  calc dist (bcOrbit n) (hexPiOrbit n)
      = ‖hexPiOrbit n - bcOrbit n‖ := by rw [dist_comm, dist_eq_norm]
    _ = ‖((tau (n + 1) : ℝ) : UnitAddCircle)‖ := by rw [hdiff']
    _ ≤ ‖tau (n + 1)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |tau (n + 1)| := Real.norm_eq_abs _
    _ = tau (n + 1) := abs_of_nonneg hpos

theorem tendsto_circleDist_bc_hex_zero
    (hDist : ∀ n : ℕ,
      dist (bcOrbit n) (hexPiOrbit n) ≤ tau (n + 1)) :
    Filter.Tendsto
      (fun n : ℕ => dist (bcOrbit n) (hexPiOrbit n))
      Filter.atTop (nhds 0) := by
  have hSucc : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 1) Filter.tendsto_id
  have hTau : Filter.Tendsto (fun n : ℕ => tau (n + 1)) Filter.atTop (nhds 0) :=
    Theory.PiDigits.T200BaileyCrandallCoboundary.tendsto_tau_zero.comp hSucc
  exact squeeze_zero (fun n => dist_nonneg) hDist hTau

theorem circleDenseLate_bc_iff_hex
    (hTendsto : Filter.Tendsto
      (fun n : ℕ => dist (bcOrbit n) (hexPiOrbit n))
      Filter.atTop (nhds 0)) :
    (∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (bcOrbit n) q < r) ↔
      ∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (hexPiOrbit n) q < r :=
  Theory.PiDigits.T108BBPCircleDensityTransfer.circleDenseArbitrarilyLate_iff_of_tendsto_dist_zero
    hTendsto

end HypothesisForms

theorem y_succ (n : ℕ) :
    y (n + 1) = Int.fract (16 * y n + R n) :=
  HypothesisForms.y_succ Y_succ n

theorem circleDist_bcOrbit_hexPiOrbit_le (n : ℕ) :
    dist (bcOrbit n) (hexPiOrbit n) ≤ tau (n + 1) :=
  HypothesisForms.circleDist_bcOrbit_hexPiOrbit_le corrected_circle_identity n

theorem tendsto_circleDist_bc_hex_zero :
    Filter.Tendsto
      (fun n : ℕ => dist (bcOrbit n) (hexPiOrbit n))
      Filter.atTop (nhds 0) :=
  HypothesisForms.tendsto_circleDist_bc_hex_zero
    circleDist_bcOrbit_hexPiOrbit_le

theorem circleDenseLate_bc_iff_hex :
    (∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (bcOrbit n) q < r) ↔
      ∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧ dist (hexPiOrbit n) q < r :=
  HypothesisForms.circleDenseLate_bc_iff_hex
    tendsto_circleDist_bc_hex_zero

end Theory.PiDigits.T201BaileyCrandallShadow
