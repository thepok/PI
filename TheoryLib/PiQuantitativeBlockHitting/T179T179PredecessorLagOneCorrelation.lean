import TheoryLib.PiQuantitativeBlockHitting.T177T177PredecessorDigitDFT
import TheoryLib.PiQuantitativeBlockHitting.T20T20DigitChangeFourierDefect

/-!
# T179: exact lag-one predecessor-digit correlation

The nine nonzero digit-DFT sectors from T177 contain only frequencies
`h = 10 * ell + r`, hence no ten-adic ray compression or endpoint term.
This file rewrites each such sector as an exact correlation between the
actual predecessor decimal digit of the pi orbit and a suffix-centered
kernel retaining the literal T139 coefficients and target center.

This is an identity, not a cancellation estimate.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.PredecessorLagOneCorrelation

open Theory.PiDigits.PiNaturalScaleResonanceObstruction
open Theory.PiDigits.PrimitiveRayCoefficientGap
open Theory.PiDigits.PrimitiveRayBoundaryConsumer
open Theory.PiDigits.PositiveLeftExtensionTransport
open Theory.PiDigits.PredecessorDigitDFT
open Theory.PiDigits.LongLagBlockCollisionDecay.T16

abbrev phase := Theory.PiDigits.T27.phase
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- The literal decimal digit immediately preceding the suffix orbit point. -/
def predecessorDigit (n : ℕ) : ℕ := ⌊10 * piOrbit n⌋₊

/-- The suffix-centered kernel left after resolving predecessor character `r`. -/
def predecessorSuffixKernel (q r : ℕ) (t : ℝ) : ℂ :=
  10 * phase (r : ℤ) (t / 10) *
    ∑ ell ∈ range (2 * q),
      (positiveBoundaryCoefficient (10 * q) (10 * ell + r) : ℂ) *
        phase (ell : ℤ) t

/-- The predecessor digit is a genuine decimal digit. -/
theorem predecessorDigit_lt_ten (n : ℕ) : predecessorDigit n < 10 := by
  unfold predecessorDigit
  have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n).1
  rw [Nat.floor_lt (by positivity : 0 ≤ 10 * piOrbit n)]
  have hx := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n).2
  norm_num
  linarith

/-- Exact lag-one decimal decomposition of the actual pi orbit. -/
theorem piOrbit_eq_predecessor_add_suffix (n : ℕ) :
    piOrbit n = ((predecessorDigit n : ℝ) + piOrbit (n + 1)) / 10 := by
  have hx0 := (Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n).1
  have hs := Theory.PiDigits.DigitChangeFourierDefect.piOrbit_succ n
  change piOrbit (n + 1) = Int.fract (10 * piOrbit n) at hs
  rw [hs]
  unfold predecessorDigit
  rw [Int.fract, ← natCast_floor_eq_intCast_floor (by positivity : 0 ≤ 10 * piOrbit n)]
  ring

private lemma digit_character_orthogonality
    (d e : ℕ) (hd : d < 10) (he : e < 10) :
    (∑ r ∈ range 10,
      phase (-(r : ℤ)) ((d : ℝ) / 10) *
        phase (r : ℤ) ((e : ℝ) / 10)) =
      if d = e then 10 else 0 := by
  classical
  by_cases hde : d = e
  · subst e
    simp only [if_pos]
    have hone (r : ℕ) :
        phase (-(r : ℤ)) ((d : ℝ) / 10) *
            phase (r : ℤ) ((d : ℝ) / 10) = 1 := by
      unfold phase Theory.PiDigits.T27.phase
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 1
      push_cast
      ring
    simp_rw [hone]
    norm_num
  · simp only [if_neg hde]
    by_cases hle : d < e
    · let k := e - d
      have hk0 : 0 < k := by omega
      have hk10 : k < 10 := by omega
      have hterm (r : ℕ) :
          phase (-(r : ℤ)) ((d : ℝ) / 10) *
              phase (r : ℤ) ((e : ℝ) / 10) =
            phase (k : ℤ) ((r : ℝ) / 10) := by
        unfold phase Theory.PiDigits.T27.phase
        rw [← Complex.exp_add]
        apply congrArg Complex.exp
        dsimp [k]
        push_cast
        rw [Nat.cast_sub (Nat.le_of_lt hle)]
        ring
      simp_rw [hterm]
      simpa [Theory.PiDigits.T27.exponentialSum,
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid] using
        (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
          k 10 (by norm_num) hk0 hk10)
    · let k := d - e
      have hk0 : 0 < k := by omega
      have hk10 : k < 10 := by omega
      have hterm (r : ℕ) :
          phase (-(r : ℤ)) ((d : ℝ) / 10) *
              phase (r : ℤ) ((e : ℝ) / 10) =
            phase (-(k : ℤ)) ((r : ℝ) / 10) := by
        unfold phase Theory.PiDigits.T27.phase
        rw [← Complex.exp_add]
        apply congrArg Complex.exp
        dsimp [k]
        push_cast
        rw [Nat.cast_sub (by omega : e ≤ d)]
        ring
      simp_rw [hterm]
      have hpos :=
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid_exponentialSum_nat_eq_zero
          k 10 (by norm_num) hk0 hk10
      have hneg := Theory.PiDigits.SharperNaturalScaleResonance.exponentialSum_neg
        (Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid 10) 10 (k : ℤ)
      rw [hpos, map_zero] at hneg
      simpa [Theory.PiDigits.T27.exponentialSum,
        Theory.PiDigits.SharperNaturalScaleResonance.uniformGrid] using hneg

private lemma tenPrimitivePart_eq_self_of_mod_nonzero
    {h r : ℕ} (hr0 : 0 < r) (hr10 : r < 10) (hmod : h % 10 = r) :
    tenPrimitivePart h = h := by
  have hnot : ¬10 ∣ h := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hv : tenValuation h = 0 := by
    simpa using (tenValuation_pow_mul_of_not_dvd (ell := 0) (k := h)
      (by omega) hnot)
  have hred := ten_reduction h
  rw [hv] at hred
  simpa using hred

/-- Fine-frequency form of a nonzero predecessor-character sector. -/
def finePredecessorSector (q A N r : ℕ) : ℂ :=
  ∑ ell ∈ range (2 * q),
    ((10 * positiveBoundaryCoefficient (10 * q) (10 * ell + r) : ℝ) : ℂ) *
      phase (-((10 * ell + r : ℕ) : ℤ))
        (decimalCylinderCenter q A / 10) *
      exponentialSum piOrbit N ((10 * ell + r : ℕ) : ℤ)

private lemma phase_neg_frequency_digit_eq_mod (h d : ℕ) :
    phase (-(h : ℤ)) ((d : ℝ) / 10) =
      phase (-((h % 10 : ℕ) : ℤ)) ((d : ℝ) / 10) := by
  unfold phase Theory.PiDigits.T27.phase
  have hdecomp : (h : ℤ) = 10 * (h / 10 : ℕ) + (h % 10 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod h 10).symm
  rw [hdecomp]
  have hexp : 2 * (Real.pi : ℂ) * Complex.I *
          (-(10 * (h / 10 : ℕ) + (h % 10 : ℕ)) : ℤ) *
          ((((d : ℝ) / 10 : ℝ) : ℂ)) =
        (-((h / 10 : ℕ) * d : ℤ)) * (2 * (Real.pi : ℂ) * Complex.I) +
          2 * (Real.pi : ℂ) * Complex.I * (-((h % 10 : ℕ) : ℤ)) *
            ((((d : ℝ) / 10 : ℝ) : ℂ)) := by
    norm_num [Int.cast_neg]
    ring
  rw [hexp, Complex.exp_add]
  have hone :
      Complex.exp (-((h / 10 : ℕ) * d : ℤ) *
        (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I
      (-((h / 10 : ℕ) * d : ℤ)) using 1
    simp only [Int.cast_neg]
  rw [hone, one_mul]
  congr 1
  simp only [Int.cast_neg, Int.cast_natCast]

private lemma digit_character_phase_grid_sum
    (r h : ℕ) (hr10 : r < 10) (c : ℝ) :
    (∑ d ∈ range 10,
      phase (r : ℤ) ((d : ℝ) / 10) *
        phase (-(h : ℤ)) ((c + d) / 10)) =
      if h % 10 = r then 10 * phase (-(h : ℤ)) (c / 10) else 0 := by
  have hsplit (d : ℕ) :
      phase (-(h : ℤ)) ((c + d) / 10) =
        phase (-(h : ℤ)) (c / 10) *
          phase (-((h % 10 : ℕ) : ℤ)) ((d : ℝ) / 10) := by
    calc
      phase (-(h : ℤ)) ((c + d) / 10) =
          phase (-(h : ℤ)) (c / 10) *
            phase (-(h : ℤ)) ((d : ℝ) / 10) := by
        change Theory.PiDigits.T27.phase (-(h : ℤ)) ((c + d) / 10) = _
        rw [show (c + (d : ℝ)) / 10 = c / 10 + (d : ℝ) / 10 by ring,
          Theory.PiDigits.T27.phase_add_real]
      _ = _ := congrArg (fun z => phase (-(h : ℤ)) (c / 10) * z)
        (phase_neg_frequency_digit_eq_mod h d)
  simp_rw [hsplit]
  rw [show (∑ d ∈ range 10,
      phase (r : ℤ) ((d : ℝ) / 10) *
        (phase (-(h : ℤ)) (c / 10) *
          phase (-((h % 10 : ℕ) : ℤ)) ((d : ℝ) / 10))) =
      phase (-(h : ℤ)) (c / 10) *
        ∑ d ∈ range 10,
          phase (-((h % 10 : ℕ) : ℤ)) ((d : ℝ) / 10) *
            phase (r : ℤ) ((d : ℝ) / 10) by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro d hd
    ring]
  have horth := digit_character_orthogonality (h % 10) r
    (Nat.mod_lt _ (by norm_num)) hr10
  have htranspose :
      (∑ d ∈ range 10,
        phase (-((h % 10 : ℕ) : ℤ)) ((d : ℝ) / 10) *
          phase (r : ℤ) ((d : ℝ) / 10)) =
        ∑ d ∈ range 10,
          phase (-(d : ℤ)) (((h % 10 : ℕ) : ℝ) / 10) *
            phase (d : ℤ) ((r : ℝ) / 10) := by
    apply sum_congr rfl
    intro d hd
    unfold phase Theory.PiDigits.T27.phase
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Int.cast_neg, Int.cast_natCast]
    push_cast
    ring
  rw [htranspose, horth]
  by_cases heq : h % 10 = r
  · simp [heq, mul_comm]
  · simp [heq]

private theorem predecessorDigitSector_eq_filtered_frequency_sum
    (q A N r : ℕ) (hq : 0 < q) (hr0 : 0 < r) (hr10 : r < 10) :
    predecessorDigitSector q A N r =
      ∑ h ∈ positiveBoundarySupport (10 * q) with h % 10 = r,
        ((10 * positiveBoundaryCoefficient (10 * q) h : ℝ) : ℂ) *
          phase (-(h : ℤ)) (decimalCylinderCenter q A / 10) *
          exponentialSum piOrbit N (h : ℤ) := by
  classical
  unfold predecessorDigitSector
  simp_rw [primitiveBoundaryFourierSum_eq_support_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcenter (d : ℕ) :
      decimalCylinderCenter (10 * q) (A + d * q) =
        (decimalCylinderCenter q A + d) / 10 := by
    unfold decimalCylinderCenter
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp
    ring
  simp_rw [centeredBoundaryTerm, hcenter]
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro h hh
  by_cases hmod : h % 10 = r
  · simp only [hmod, if_true]
    have hprim := tenPrimitivePart_eq_self_of_mod_nonzero hr0 hr10 hmod
    rw [hprim]
    have hgrid := digit_character_phase_grid_sum r h hr10
      (decimalCylinderCenter q A)
    rw [hmod, if_pos rfl] at hgrid
    calc
      ∑ d ∈ range 10,
          phase (r : ℤ) ((d : ℝ) / 10) *
            (((positiveBoundaryCoefficient (10 * q) h : ℂ) *
                phase (-(h : ℤ))
                  ((decimalCylinderCenter q A + d) / 10)) *
              exponentialSum piOrbit N (h : ℤ)) =
          ((positiveBoundaryCoefficient (10 * q) h : ℂ) *
            exponentialSum piOrbit N (h : ℤ)) *
            (∑ d ∈ range 10,
              phase (r : ℤ) ((d : ℝ) / 10) *
                phase (-(h : ℤ))
                  ((decimalCylinderCenter q A + d) / 10)) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro d hd
            ring
      _ = _ := by rw [hgrid]; push_cast; ring
  · simp only [hmod, if_false]
    have hgrid := digit_character_phase_grid_sum r h hr10
      (decimalCylinderCenter q A)
    rw [if_neg hmod] at hgrid
    calc
      ∑ d ∈ range 10,
          phase (r : ℤ) ((d : ℝ) / 10) *
            (((positiveBoundaryCoefficient (10 * q) h : ℂ) *
                phase (-(h : ℤ))
                  ((decimalCylinderCenter q A + d) / 10)) *
              exponentialSum piOrbit N (tenPrimitivePart h : ℤ)) =
          ((positiveBoundaryCoefficient (10 * q) h : ℂ) *
            exponentialSum piOrbit N (tenPrimitivePart h : ℤ)) *
            (∑ d ∈ range 10,
              phase (r : ℤ) ((d : ℝ) / 10) *
                phase (-(h : ℤ))
                  ((decimalCylinderCenter q A + d) / 10)) := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro d hd
            ring
      _ = 0 := by rw [hgrid, mul_zero]

/-- Every nonzero digit-character sector is the exact consecutive residue
class `h = 10 * ell + r`; those frequencies are already ten-primitive. -/
theorem predecessorDigitSector_eq_finePredecessorSector
    (q A N r : ℕ) (hq : 0 < q) (hr0 : 0 < r) (hr10 : r < 10) :
    predecessorDigitSector q A N r = finePredecessorSector q A N r := by
  rw [predecessorDigitSector_eq_filtered_frequency_sum q A N r hq hr0 hr10]
  unfold finePredecessorSector
  apply Finset.sum_bij (fun h _ => h / 10)
  · intro h hh
    simp only [positiveBoundarySupport, Finset.mem_filter, Finset.mem_Icc] at hh
    simp only [Finset.mem_range]
    rcases hh with ⟨⟨hh1, hh2⟩, hmod⟩
    have hdecomp := Nat.mod_add_div h 10
    omega
  · intro a ha b hb hab
    simp only [positiveBoundarySupport, Finset.mem_filter, Finset.mem_Icc] at ha hb
    rcases ha with ⟨⟨ha1, ha2⟩, hamod⟩
    rcases hb with ⟨⟨hb1, hb2⟩, hbmod⟩
    have hadecomp := Nat.mod_add_div a 10
    have hbdecomp := Nat.mod_add_div b 10
    omega
  · intro ell hell
    refine ⟨10 * ell + r, ?_, by omega⟩
    · simp only [positiveBoundarySupport, Finset.mem_filter, Finset.mem_Icc]
      simp only [Finset.mem_range] at hell
      constructor
      · constructor <;> omega
      · omega
  · intro h hh
    simp only [positiveBoundarySupport, Finset.mem_filter, Finset.mem_Icc] at hh
    rcases hh with ⟨⟨hh1, hh2⟩, hmod⟩
    have hdecomp := Nat.mod_add_div h 10
    have heq : 10 * (h / 10) + r = h := by omega
    rw [heq]

private lemma phase_ten_mul_add_div_ten (ell r : ℕ) (t : ℝ) :
    phase ((10 * ell + r : ℕ) : ℤ) (t / 10) =
      phase (ell : ℤ) t * phase (r : ℤ) (t / 10) := by
  unfold phase Theory.PiDigits.T27.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_nat_at_nat (ell a : ℕ) :
    phase (ell : ℤ) (a : ℝ) = 1 := by
  unfold phase Theory.PiDigits.T27.phase
  convert Complex.exp_int_mul_two_pi_mul_I ((ell * a : ℕ) : ℤ) using 1
  push_cast
  ring

private lemma phase_add_real (h : ℤ) (x y : ℝ) :
    phase h (x + y) = phase h x * phase h y :=
  Theory.PiDigits.T27.phase_add_real h x y

private lemma phase_neg_frequency_eq_neg_argument (h : ℤ) (x : ℝ) :
    phase (-h) x = phase h (-x) := by
  unfold phase Theory.PiDigits.T27.phase
  congr 1
  push_cast
  ring

private lemma centered_fine_phase_eq_predecessor_suffix
    (ell r n : ℕ) (c : ℝ) :
    phase (-((10 * ell + r : ℕ) : ℤ)) (c / 10) *
        phase ((10 * ell + r : ℕ) : ℤ) (piOrbit n) =
      phase (r : ℤ) ((predecessorDigit n : ℝ) / 10) *
        (phase (r : ℤ) ((piOrbit (n + 1) - c) / 10) *
          phase (ell : ℤ) (piOrbit (n + 1) - c)) := by
  have horbit := piOrbit_eq_predecessor_add_suffix n
  calc
    phase (-((10 * ell + r : ℕ) : ℤ)) (c / 10) *
        phase ((10 * ell + r : ℕ) : ℤ) (piOrbit n) =
      phase ((10 * ell + r : ℕ) : ℤ) (piOrbit n - c / 10) := by
        rw [phase_neg_frequency_eq_neg_argument,
          ← phase_add_real]
        congr 1
        ring
    _ = phase ((10 * ell + r : ℕ) : ℤ)
        (((predecessorDigit n : ℝ) + piOrbit (n + 1) - c) / 10) := by
          congr 1
          rw [horbit]
          ring
    _ = phase (ell : ℤ)
          ((predecessorDigit n : ℝ) + piOrbit (n + 1) - c) *
        phase (r : ℤ)
          (((predecessorDigit n : ℝ) + piOrbit (n + 1) - c) / 10) :=
      phase_ten_mul_add_div_ten ell r _
    _ = _ := by
      rw [show (predecessorDigit n : ℝ) + piOrbit (n + 1) - c =
          (predecessorDigit n : ℝ) + (piOrbit (n + 1) - c) by ring]
      rw [phase_add_real,
        phase_nat_at_nat,
        one_mul]
      rw [show ((predecessorDigit n : ℝ) + (piOrbit (n + 1) - c)) / 10 =
          (predecessorDigit n : ℝ) / 10 +
            (piOrbit (n + 1) - c) / 10 by ring,
        phase_add_real]
      ring

/-- Exact lag-one formula: the complete nonzero child sector is an actual
predecessor-digit character correlated with the suffix-centered kernel. -/
theorem predecessorDigitSector_eq_lagOneCorrelation
    (q A N r : ℕ) (hq : 0 < q) (hr0 : 0 < r) (hr10 : r < 10) :
    predecessorDigitSector q A N r =
      ∑ n ∈ range N,
        phase (r : ℤ) ((predecessorDigit n : ℝ) / 10) *
          predecessorSuffixKernel q r
            (piOrbit (n + 1) - decimalCylinderCenter q A) := by
  rw [predecessorDigitSector_eq_finePredecessorSector q A N r hq hr0 hr10]
  unfold finePredecessorSector predecessorSuffixKernel
  unfold exponentialSum Theory.PiDigits.T27.exponentialSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro ell hell
  have hphase := centered_fine_phase_eq_predecessor_suffix ell r n
    (decimalCylinderCenter q A)
  rw [show ((10 * positiveBoundaryCoefficient (10 * q) (10 * ell + r) : ℝ) : ℂ) *
        phase (-((10 * ell + r : ℕ) : ℤ))
          (decimalCylinderCenter q A / 10) *
        phase ((10 * ell + r : ℕ) : ℤ) (piOrbit n) =
      ((10 * positiveBoundaryCoefficient (10 * q) (10 * ell + r) : ℝ) : ℂ) *
        (phase (-((10 * ell + r : ℕ) : ℤ))
          (decimalCylinderCenter q A / 10) *
        phase ((10 * ell + r : ℕ) : ℤ) (piOrbit n)) by ring,
      hphase]
  push_cast
  ring

#print axioms Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigit_lt_ten
#print axioms Theory.PiDigits.PredecessorLagOneCorrelation.piOrbit_eq_predecessor_add_suffix
#print axioms Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigitSector_eq_finePredecessorSector
#print axioms Theory.PiDigits.PredecessorLagOneCorrelation.predecessorDigitSector_eq_lagOneCorrelation

end Theory.PiDigits.PredecessorLagOneCorrelation
