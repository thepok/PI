import TheoryLib.PiQuantitativeBlockHitting.T17T17PowerTenDiophantineReduction
import TheoryLib.PiDigits.T18FiniteAlphabetSubsequentialCounting
import TheoryLib.PiDecimalFactorComplexity.T10PiWeightedFourierReduction

/-!
# T20: decimal digit changes force first-frequency Fourier defect

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file records an unconditional bridge from changes in the floor-based
decimal digits of pi to cancellation in its first circle-frequency sum.  It
does not supply a lower bound for the number of digit changes, and hence does
not prove decimal normality or even disjunctivity of pi.

The proof has three separate ingredients.  First, the Fourier defect is an
exact all-pairs cosine energy.  Second, the elementary path Poincare estimate
compares that defect with the energy of consecutive phases.  Third, two
unequal consecutive decimal digits force the corresponding orbit increment
to remain at least `1/100` from an integer.
-/

noncomputable section

open scoped ComplexConjugate
open Finset Set

namespace Theory.PiDigits.DigitChangeFourierDefect

abbrev phase := Theory.PiDigits.T27.phase
abbrev exponentialSum := Theory.PiDigits.T27.exponentialSum
abbrev piOrbit := Theory.PiDigits.T27.piFractionalOrbit

/-- The squared-energy cost along the consecutive edges of a finite path. -/
def pathEnergy (z : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N - 1), ‖z (i + 1) - z i‖ ^ 2

/-- Coordinatewise arithmetic mean of the first `N` complex values. -/
def complexMean (z : ℕ → ℂ) (N : ℕ) : ℂ :=
  ⟨(∑ i ∈ Finset.range N, (z i).re) / (N : ℝ),
    (∑ i ∈ Finset.range N, (z i).im) / (N : ℝ)⟩

/-- Squared distance between two points is at most twice the sum of their
squared distances from an arbitrary center. -/
lemma norm_sub_sq_le_two_centered (z w c : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * ‖z - c‖ ^ 2 + 2 * ‖w - c‖ ^ 2 := by
  have htri : ‖z - w‖ ≤ ‖z - c‖ + ‖w - c‖ := by
    calc
      ‖z - w‖ = ‖(z - c) + (c - w)‖ := by
        congr 1
        abel
      _ ≤ ‖z - c‖ + ‖c - w‖ := norm_add_le _ _
      _ = ‖z - c‖ + ‖w - c‖ := by
        congr 1
        exact norm_sub_rev c w
  nlinarith [norm_nonneg (z - w), norm_nonneg (z - c),
    norm_nonneg (w - c), sq_nonneg (‖z - c‖ - ‖w - c‖)]

/-- Shifting the indices of a nonnegative family drops at most the two path
endpoints. -/
lemma sum_shifted_range_sub_one_le (f : ℕ → ℝ) (N : ℕ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ Finset.range (N - 1), f (i + 1)) ≤
      ∑ i ∈ Finset.range N, f i := by
  classical
  let A := Finset.range (N - 1)
  let g : ℕ → ℕ := fun i ↦ i + 1
  have hg : Set.InjOn g A := by
    intro i hi j hj hij
    exact Nat.add_right_cancel hij
  have himage : A.image g ⊆ Finset.range N := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    simp only [A, Finset.mem_range] at hi ⊢
    change i + 1 < N
    omega
  calc
    (∑ i ∈ Finset.range (N - 1), f (i + 1)) =
        ∑ j ∈ A.image g, f j := by
          simpa only [A, g] using (Finset.sum_image hg).symm
    _ ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun i _hi _hnot ↦ hf i)

/-- The unshifted initial path indices are contained in the full prefix. -/
lemma sum_range_sub_one_le (f : ℕ → ℝ) (N : ℕ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ Finset.range (N - 1), f i) ≤
      ∑ i ∈ Finset.range N, f i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _hi _hnot
    exact hf i

/-- Elementary path Poincare inequality, with a deliberately simple sharp
enough constant.  Each centered vertex occurs in at most two edges. -/
theorem pathEnergy_le_four_centeredEnergy (z : ℕ → ℂ) (N : ℕ) (c : ℂ) :
    pathEnergy z N ≤
      4 * ∑ i ∈ Finset.range N, ‖z i - c‖ ^ 2 := by
  let f : ℕ → ℝ := fun i ↦ ‖z i - c‖ ^ 2
  have hf : ∀ i, 0 ≤ f i := fun i ↦ sq_nonneg _
  have hedges : pathEnergy z N ≤
      ∑ i ∈ Finset.range (N - 1), (2 * f i + 2 * f (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [f, add_comm] using
      norm_sub_sq_le_two_centered (z (i + 1)) (z i) c
  have hleft := sum_range_sub_one_le f N hf
  have hright := sum_shifted_range_sub_one_le f N hf
  calc
    pathEnergy z N ≤
        ∑ i ∈ Finset.range (N - 1), (2 * f i + 2 * f (i + 1)) := hedges
    _ = 2 * (∑ i ∈ Finset.range (N - 1), f i) +
        2 * (∑ i ∈ Finset.range (N - 1), f (i + 1)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * ∑ i ∈ Finset.range N, f i := by linarith

/-- The one-dimensional finite variance identity. -/
lemma mul_sum_sq_sub_average (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    (N : ℝ) *
        ∑ i ∈ Finset.range N,
          (f i - (∑ j ∈ Finset.range N, f j) / (N : ℝ)) ^ 2 =
      (N : ℝ) * (∑ i ∈ Finset.range N, (f i) ^ 2) -
        (∑ i ∈ Finset.range N, f i) ^ 2 := by
  let S : ℝ := ∑ j ∈ Finset.range N, f j
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hexpand :
      (∑ i ∈ Finset.range N, (f i - S / (N : ℝ)) ^ 2) =
        (∑ i ∈ Finset.range N, (f i) ^ 2) -
          2 * S * (S / (N : ℝ)) + (N : ℝ) * (S / (N : ℝ)) ^ 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [show (∑ j ∈ Finset.range N, f j) = S by rfl, hexpand]
  field_simp
  ring

/-- For unit complex values, `N` times the centered energy is exactly the
usual squared Fourier defect. -/
theorem mul_centeredEnergy_eq_defect (z : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hz : ∀ i < N, ‖z i‖ = 1) :
    (N : ℝ) * ∑ i ∈ Finset.range N, ‖z i - complexMean z N‖ ^ 2 =
      (N : ℝ) ^ 2 - ‖∑ i ∈ Finset.range N, z i‖ ^ 2 := by
  let R : ℝ := ∑ i ∈ Finset.range N, (z i).re
  let I : ℝ := ∑ i ∈ Finset.range N, (z i).im
  have hre := mul_sum_sq_sub_average (fun i ↦ (z i).re) N hN
  have him := mul_sum_sq_sub_average (fun i ↦ (z i).im) N hN
  have hunit :
      (∑ i ∈ Finset.range N, ((z i).re ^ 2 + (z i).im ^ 2)) = (N : ℝ) := by
    calc
      (∑ i ∈ Finset.range N, ((z i).re ^ 2 + (z i).im ^ 2)) =
          ∑ i ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show (z i).re ^ 2 + (z i).im ^ 2 = Complex.normSq (z i) by
              rw [Complex.normSq_apply]
              ring]
            rw [Complex.normSq_eq_norm_sq, hz i (Finset.mem_range.mp hi)]
            norm_num
      _ = (N : ℝ) := by simp
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp_rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  rw [Complex.re_sum, Complex.im_sum]
  simp only [complexMean]
  change (N : ℝ) *
      ∑ i ∈ Finset.range N,
        (((z i).re - R / (N : ℝ)) * ((z i).re - R / (N : ℝ)) +
          ((z i).im - I / (N : ℝ)) * ((z i).im - I / (N : ℝ))) =
    (N : ℝ) ^ 2 - (R * R + I * I)
  simp_rw [← pow_two]
  rw [Finset.sum_add_distrib, mul_add, hre, him]
  change
    (N : ℝ) * (∑ i ∈ Finset.range N, (z i).re ^ 2) - R ^ 2 +
        ((N : ℝ) * (∑ i ∈ Finset.range N, (z i).im ^ 2) - I ^ 2) =
      (N : ℝ) ^ 2 - (R ^ 2 + I ^ 2)
  calc
    (N : ℝ) * (∑ i ∈ Finset.range N, (z i).re ^ 2) - R ^ 2 +
          ((N : ℝ) * (∑ i ∈ Finset.range N, (z i).im ^ 2) - I ^ 2) =
        (N : ℝ) *
            ((∑ i ∈ Finset.range N, (z i).re ^ 2) +
              ∑ i ∈ Finset.range N, (z i).im ^ 2) - (R ^ 2 + I ^ 2) := by ring
    _ = (N : ℝ) * (N : ℝ) - (R ^ 2 + I ^ 2) := by
      rw [← Finset.sum_add_distrib, hunit]
    _ = (N : ℝ) ^ 2 - (R ^ 2 + I ^ 2) := by ring

/-- Unit-modulus path values have defect at least `N/4` times their
consecutive-edge energy. -/
theorem defect_ge_mul_pathEnergy (z : ℕ → ℂ) (N : ℕ)
    (hz : ∀ i < N, ‖z i‖ = 1) :
    (N : ℝ) / 4 * pathEnergy z N ≤
      (N : ℝ) ^ 2 - ‖∑ i ∈ Finset.range N, z i‖ ^ 2 := by
  cases N with
  | zero => simp [pathEnergy]
  | succ n =>
      have hN : 0 < n + 1 := Nat.succ_pos n
      have hp := pathEnergy_le_four_centeredEnergy z (n + 1)
        (complexMean z (n + 1))
      have hv := mul_centeredEnergy_eq_defect z (n + 1) hN hz
      calc
        ((n + 1 : ℕ) : ℝ) / 4 * pathEnergy z (n + 1) ≤
            ((n + 1 : ℕ) : ℝ) / 4 *
              (4 * ∑ i ∈ Finset.range (n + 1),
                ‖z i - complexMean z (n + 1)‖ ^ 2) := by
                  gcongr
        _ = ((n + 1 : ℕ) : ℝ) *
              ∑ i ∈ Finset.range (n + 1),
                ‖z i - complexMean z (n + 1)‖ ^ 2 := by ring
        _ = ((n + 1 : ℕ) : ℝ) ^ 2 -
              ‖∑ i ∈ Finset.range (n + 1), z i‖ ^ 2 := hv

/-- The real part of the circle phase is the corresponding cosine. -/
lemma phase_re_eq_cos (h : ℤ) (x : ℝ) :
    (phase h x).re = Real.cos (2 * Real.pi * (h : ℝ) * x) := by
  rw [show phase h x =
      Complex.exp (((2 * Real.pi * (h : ℝ) * x : ℝ) : ℂ) * Complex.I) by
    unfold phase Theory.PiDigits.T27.phase
    congr 1
    push_cast
    ring]
  exact Complex.exp_ofReal_mul_I_re _

/-- Exact all-pairs form of the Fourier defect.  The sum is over ordered
pairs, so every off-diagonal unordered pair occurs twice and each diagonal
term contributes zero. -/
theorem finiteCircle_defect_eq_pairCosineEnergy {N : ℕ}
    (x : Fin N → ℝ) (h : ℤ) :
    (N : ℝ) ^ 2 - ‖∑ i : Fin N, phase h (x i)‖ ^ 2 =
      ∑ ij : Fin N × Fin N,
        (1 - Real.cos (2 * Real.pi * (h : ℝ) * (x ij.2 - x ij.1))) := by
  classical
  have hpair :=
    DecimalFactorComplexity.WeightedFourierReduction.orderedPair_phase_identity x h
  have hre := congrArg Complex.re hpair
  simp only [Complex.re_sum, Complex.ofReal_re] at hre
  simp_rw [phase_re_eq_cos] at hre
  calc
    (N : ℝ) ^ 2 - ‖∑ i : Fin N, phase h (x i)‖ ^ 2 =
        (N : ℝ) ^ 2 -
          ∑ ij : Fin N × Fin N,
            Real.cos (2 * Real.pi * (h : ℝ) * (x ij.2 - x ij.1)) := by
              rw [hre]
    _ = ∑ ij : Fin N × Fin N,
          (1 - Real.cos (2 * Real.pi * (h : ℝ) * (x ij.2 - x ij.1))) := by
            rw [Finset.sum_sub_distrib]
            simp [Fintype.card_prod]
            ring

/-- Exact all-pairs energy identity for the fixed fractional pi orbit at the
first nonzero frequency. -/
theorem pi_defect_eq_pairCosineEnergy (N : ℕ) :
    (N : ℝ) ^ 2 - ‖exponentialSum piOrbit N 1‖ ^ 2 =
      ∑ ij : Fin N × Fin N,
        (1 - Real.cos
          (2 * Real.pi * (piOrbit ij.2.val - piOrbit ij.1.val))) := by
  have h := finiteCircle_defect_eq_pairCosineEnergy
    (x := fun i : Fin N ↦ piOrbit i.val) 1
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ phase 1 (piOrbit i)) N] at h
  simpa only [Theory.PiDigits.T27.exponentialSum, Int.cast_one, one_mul,
    mul_one] using h

/-- The first two floor-based decimal digits determine the integer part of
`100*x` exactly. -/
lemma floor_hundred_eq_of_first_two_digits {x : ℝ} (hx : x ∈ Set.Ico 0 1)
    (a b : Fin 10) (hzero : Real.digits x 10 0 = a)
    (hone : Real.digits x 10 1 = b) :
    ⌊(100 : ℝ) * x⌋₊ = 10 * a.val + b.val := by
  have hsum := Real.ofDigits_digits_sum_eq (b := 10) hx 2
  norm_num [Finset.sum_range_succ, Real.ofDigitsTerm, hzero, hone] at hsum
  have hreal : (⌊(100 : ℝ) * x⌋₊ : ℝ) =
      (10 * a.val + b.val : ℕ) := by
    calc
      (⌊(100 : ℝ) * x⌋₊ : ℝ) =
          100 * ((a.val : ℝ) * (1 / 10) + (b.val : ℝ) * (1 / 100)) := hsum.symm
      _ = (10 * a.val + b.val : ℕ) := by push_cast; ring
  exact_mod_cast hreal

/-- Half-open two-digit cylinder determined by the first two decimal digits. -/
lemma mem_two_digit_cylinder {x : ℝ} (hx : x ∈ Set.Ico 0 1)
    (a b : Fin 10) (hzero : Real.digits x 10 0 = a)
    (hone : Real.digits x 10 1 = b) :
    x ∈ Set.Ico
      ((10 * a.val + b.val : ℕ) / (100 : ℝ))
      (((10 * a.val + b.val + 1 : ℕ) : ℝ) / 100) := by
  have hfloor := floor_hundred_eq_of_first_two_digits hx a b hzero hone
  have hxnonneg : 0 ≤ (100 : ℝ) * x := mul_nonneg (by norm_num) hx.1
  have hlo : (⌊(100 : ℝ) * x⌋₊ : ℝ) ≤ 100 * x := Nat.floor_le hxnonneg
  have hhi : 100 * x < (⌊(100 : ℝ) * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hfloor] at hlo hhi
  push_cast at hlo hhi
  constructor <;> norm_num at * <;> linarith

/-- The two-digit cell arithmetic behind the separation constant.  Unequal
digits imply that `9*x-a` stays between `1/100` and `9/10` away from zero in
absolute value. -/
lemma decimal_increment_abs_bounds {x : ℝ} (a b : Fin 10)
    (hcell : x ∈ Set.Ico
      ((10 * a.val + b.val : ℕ) / (100 : ℝ))
      (((10 * a.val + b.val + 1 : ℕ) : ℝ) / 100))
    (hab : a ≠ b) :
    (1 / 100 : ℝ) ≤ |9 * x - a.val| ∧
      |9 * x - a.val| ≤ (9 / 10 : ℝ) := by
  have hav : a.val < 10 := a.isLt
  have hbv : b.val < 10 := b.isLt
  have hne : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
  have horder : a.val < b.val ∨ b.val < a.val := lt_or_gt_of_ne hne
  have hcell' := hcell
  norm_num at hcell'
  have hxlow : (a.val : ℝ) / 10 ≤ x := by
    have hb0 : (0 : ℝ) ≤ b.val := by positivity
    nlinarith [hcell'.1]
  have hxhigh : x < ((a.val : ℝ) + 1) / 10 := by
    have hb9 : (b.val : ℝ) ≤ 9 := by exact_mod_cast (Nat.le_of_lt_succ hbv)
    nlinarith [hcell'.2]
  have hwideLow : -(9 / 10 : ℝ) ≤ 9 * x - a.val := by
    have ha9 : (a.val : ℝ) ≤ 9 := by exact_mod_cast (Nat.le_of_lt_succ hav)
    nlinarith
  have hwideHigh : 9 * x - a.val ≤ (9 / 10 : ℝ) := by
    have ha0 : (0 : ℝ) ≤ a.val := by positivity
    nlinarith
  constructor
  · rcases horder with hlt | hgt
    · have hgapNat : 10 * a.val + 1 ≤ 9 * b.val := by omega
      have hgap : (10 : ℝ) * a.val + 1 ≤ 9 * b.val := by exact_mod_cast hgapNat
      rw [abs_of_nonneg]
      · nlinarith [hcell'.1]
      · nlinarith [hcell'.1]
    · have hgapNat : 9 * b.val + 10 ≤ 10 * a.val := by omega
      have hgap : (9 : ℝ) * b.val + 10 ≤ 10 * a.val := by exact_mod_cast hgapNat
      rw [abs_of_nonpos]
      · nlinarith [hcell'.2]
      · nlinarith [hcell'.2]
  · rw [abs_le]
    exact ⟨hwideLow, hwideHigh⟩

/-- Taking a base-ten step only depends on the fractional part. -/
lemma fract_ten_eq_fract_ten_fract (y : ℝ) :
    Int.fract (10 * y) = Int.fract (10 * Int.fract y) := by
  calc
    Int.fract (10 * y) =
        Int.fract (((10 * ⌊y⌋ : ℤ) : ℝ) + 10 * Int.fract y) := by
      congr 1
      push_cast
      nlinarith [Int.floor_add_fract y]
    _ = Int.fract (10 * Int.fract y) := Int.fract_intCast_add _ _

/-- Successive points of the fractional pi orbit are related by the base-ten
map. -/
lemma piOrbit_succ (j : ℕ) :
    piOrbit (j + 1) = Int.fract (10 * piOrbit j) := by
  unfold piOrbit Theory.PiDigits.T27.piFractionalOrbit
  rw [show (10 : ℝ) ^ (j + 1) * Real.pi =
      10 * ((10 : ℝ) ^ j * Real.pi) by
    rw [pow_succ]
    ring]
  exact fract_ten_eq_fract_ten_fract _

/-- On a two-digit cell, the base-ten fractional map subtracts its first
digit. -/
lemma fract_ten_eq_sub_first_digit {x : ℝ} (a b : Fin 10)
    (hcell : x ∈ Set.Ico
      ((10 * a.val + b.val : ℕ) / (100 : ℝ))
      (((10 * a.val + b.val + 1 : ℕ) : ℝ) / 100)) :
    Int.fract (10 * x) = 10 * x - a.val := by
  have hav : a.val < 10 := a.isLt
  have hbv : b.val < 10 := b.isLt
  have hcell' := hcell
  norm_num at hcell'
  have hxlow : (a.val : ℝ) ≤ 10 * x := by
    have hb0 : (0 : ℝ) ≤ b.val := by positivity
    nlinarith [hcell'.1]
  have hxhigh : 10 * x < (a.val : ℝ) + 1 := by
    have hb9 : (b.val : ℝ) ≤ 9 := by exact_mod_cast (Nat.le_of_lt_succ hbv)
    nlinarith [hcell'.2]
  have hxnonneg : 0 ≤ 10 * x := le_trans (by positivity) hxlow
  have hfloor : ⌊10 * x⌋₊ = a.val :=
    (Nat.floor_eq_iff hxnonneg).2 ⟨hxlow, hxhigh⟩
  rw [Int.fract, ← natCast_floor_eq_intCast_floor hxnonneg, hfloor]

/-- Every genuine adjacent digit change in pi gives a base-ten orbit
increment whose absolute representative lies in `[1/100, 9/10]`. -/
theorem piOrbit_succ_sub_abs_bounds (j : ℕ)
    (hchange : Theory.PiDigits.piDigit j ≠ Theory.PiDigits.piDigit (j + 1)) :
    (1 / 100 : ℝ) ≤ |piOrbit (j + 1) - piOrbit j| ∧
      |piOrbit (j + 1) - piOrbit j| ≤ (9 / 10 : ℝ) := by
  let a : Fin 10 := Theory.PiDigits.piDigit j
  let b : Fin 10 := Theory.PiDigits.piDigit (j + 1)
  let x : ℝ := piOrbit j
  have hx : x ∈ Set.Ico (0 : ℝ) 1 :=
    Theory.PiDigits.T27.piFractionalOrbit_mem_Ico j
  have hzero : Real.digits x 10 0 = a := by
    simpa only [x, a, Nat.add_zero] using
      Theory.PiDigits.PowerTenDiophantineReduction.piFractionalOrbit_digit j 0
  have hone : Real.digits x 10 1 = b := by
    simpa only [x, b] using
      Theory.PiDigits.PowerTenDiophantineReduction.piFractionalOrbit_digit j 1
  have hcell := mem_two_digit_cylinder hx a b hzero hone
  have hincrement : piOrbit (j + 1) - piOrbit j = 9 * x - a.val := by
    rw [piOrbit_succ, fract_ten_eq_sub_first_digit a b hcell]
    simp only [x]
    ring
  rw [hincrement]
  exact decimal_increment_abs_bounds a b hcell (by simpa only [a, b] using hchange)

/-- Chord length between two phases is the distance from one to the phase of
their increment. -/
lemma norm_phase_sub_phase_eq (x y : ℝ) :
    ‖phase 1 y - phase 1 x‖ = ‖1 - phase 1 (y - x)‖ := by
  have hy : phase 1 y = phase 1 x * phase 1 (y - x) := by
    rw [← Theory.PiDigits.T27.phase_add_real]
    congr 1
    ring
  rw [hy]
  calc
    ‖phase 1 x * phase 1 (y - x) - phase 1 x‖ =
        ‖phase 1 x * (phase 1 (y - x) - 1)‖ := by
          congr 1
          ring
    _ = ‖phase 1 (y - x) - 1‖ := by
      rw [norm_mul, Theory.PiDigits.T27.norm_phase, one_mul]
    _ = ‖1 - phase 1 (y - x)‖ := norm_sub_rev _ _

/-- A changed decimal edge has a uniform rational chord-length lower bound.
The exact trigonometric chord is slightly larger; `1/25` keeps the final
The constant rational. -/
theorem pi_changed_edge_norm_lower (j : ℕ)
    (hchange : Theory.PiDigits.piDigit j ≠ Theory.PiDigits.piDigit (j + 1)) :
    (1 / 25 : ℝ) ≤ ‖phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j)‖ := by
  obtain ⟨hlow, hhigh⟩ := piOrbit_succ_sub_abs_bounds j hchange
  have hsin := Theory.PiDigits.T27.abs_sin_pi_mul_lower
    (u := piOrbit (j + 1) - piOrbit j) (L := (1 / 50 : ℝ))
    (by norm_num) (by norm_num at hlow ⊢; exact hlow)
    (by norm_num at hhigh ⊢; linarith)
  rw [norm_phase_sub_phase_eq,
    Theory.PiDigits.T27.norm_one_sub_phase_one]
  norm_num at hsin ⊢
  linarith

/-- Squared form of `pi_changed_edge_norm_lower`. -/
theorem pi_changed_edge_sq_lower (j : ℕ)
    (hchange : Theory.PiDigits.piDigit j ≠ Theory.PiDigits.piDigit (j + 1)) :
    (1 / 625 : ℝ) ≤
      ‖phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j)‖ ^ 2 := by
  have h := pi_changed_edge_norm_lower j hchange
  have hn := norm_nonneg (phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j))
  norm_num at h ⊢
  nlinarith

/-- On the annulus of representatives relevant to a changed decimal edge,
the cosine is maximized at the nearest allowed endpoint `1/100`. -/
lemma cos_two_pi_le_cos_pi_div_fifty {u : ℝ}
    (hlow : (1 / 100 : ℝ) ≤ |u|)
    (hhigh : |u| ≤ (9 / 10 : ℝ)) :
    Real.cos (2 * Real.pi * u) ≤ Real.cos (Real.pi / 50) := by
  have hcosAbs : Real.cos (2 * Real.pi * u) =
      Real.cos (2 * Real.pi * |u|) := by
    calc
      Real.cos (2 * Real.pi * u) = Real.cos |2 * Real.pi * u| :=
        (Real.cos_abs _).symm
      _ = Real.cos (2 * Real.pi * |u|) := by
        rw [abs_mul, abs_of_pos Real.two_pi_pos]
  rw [hcosAbs]
  by_cases hhalf : |u| ≤ (1 / 2 : ℝ)
  · have hargLow : Real.pi / 50 ≤ 2 * Real.pi * |u| := by
      nlinarith [Real.pi_pos]
    have hargHigh : 2 * Real.pi * |u| ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hargHigh hargLow
  · have hhalf' : (1 / 2 : ℝ) < |u| := lt_of_not_ge hhalf
    have hargLow : Real.pi / 50 ≤ 2 * Real.pi * (1 - |u|) := by
      nlinarith [Real.pi_pos]
    have hargHigh : 2 * Real.pi * (1 - |u|) ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have hperiod : Real.cos (2 * Real.pi * |u|) =
        Real.cos (2 * Real.pi * (1 - |u|)) := by
      calc
        Real.cos (2 * Real.pi * |u|) =
            Real.cos (2 * Real.pi - 2 * Real.pi * |u|) :=
              (Real.cos_two_pi_sub _).symm
        _ = Real.cos (2 * Real.pi * (1 - |u|)) := by ring_nf
    rw [hperiod]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hargHigh hargLow

/-- Exact chord-square identity for two circle phases. -/
lemma norm_phase_sub_phase_sq_eq (x y : ℝ) :
    ‖phase 1 y - phase 1 x‖ ^ 2 =
      2 * (1 - Real.cos (2 * Real.pi * (y - x))) := by
  have hny : Complex.normSq (phase 1 y) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
    norm_num
  have hnx : Complex.normSq (phase 1 x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Theory.PiDigits.T27.norm_phase]
    norm_num
  have hprod : phase 1 y * conj (phase 1 x) = phase 1 (y - x) :=
    (DecimalFactorComplexity.WeightedFourierReduction.phase_real_sub 1 y x).symm
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, hny, hnx, hprod,
    phase_re_eq_cos]
  ring_nf

/-- Sharp changed-edge lower bound used in the final theorem. -/
theorem pi_changed_edge_sq_cosine_lower (j : ℕ)
    (hchange : Theory.PiDigits.piDigit j ≠ Theory.PiDigits.piDigit (j + 1)) :
    2 * (1 - Real.cos (Real.pi / 50)) ≤
      ‖phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j)‖ ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := piOrbit_succ_sub_abs_bounds j hchange
  rw [norm_phase_sub_phase_sq_eq]
  have hcos := cos_two_pi_le_cos_pi_div_fifty hlow hhigh
  linarith

/-- The prefix path energy receives at least `1/625` from every adjacent
digit change. -/
theorem pi_pathEnergy_ge_changeCount (N : ℕ) :
    (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 625 ≤
      pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := by
  classical
  let changes := Theory.PiDigits.T18.changePositions Theory.PiDigits.piDigit N
  let edge : ℕ → ℝ := fun j ↦
    ‖phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j)‖ ^ 2
  have hsubset : changes ⊆ Finset.range (N - 1) := by
    intro j hj
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.piDigit i ≠ Theory.PiDigits.piDigit (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').1
  have hlower : (∑ j ∈ changes, (1 / 625 : ℝ)) ≤
      ∑ j ∈ changes, edge j := by
    apply Finset.sum_le_sum
    intro j hj
    apply pi_changed_edge_sq_lower
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.piDigit i ≠ Theory.PiDigits.piDigit (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').2
  have hmono : (∑ j ∈ changes, edge j) ≤
      ∑ j ∈ Finset.range (N - 1), edge j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j _hj _hnot
    exact sq_nonneg _
  calc
    (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 625 =
        ∑ j ∈ changes, (1 / 625 : ℝ) := by
          simp only [Theory.PiDigits.T18.changeCount, changes,
            Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ j ∈ changes, edge j := hlower
    _ ≤ ∑ j ∈ Finset.range (N - 1), edge j := hmono
    _ = pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := rfl

/-- Sharp cosine version of the path-energy lower bound. -/
theorem pi_pathEnergy_ge_cosine_changeCount (N : ℕ) :
    2 * (1 - Real.cos (Real.pi / 50)) *
        (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) ≤
      pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := by
  classical
  let changes := Theory.PiDigits.T18.changePositions Theory.PiDigits.piDigit N
  let edge : ℕ → ℝ := fun j ↦
    ‖phase 1 (piOrbit (j + 1)) - phase 1 (piOrbit j)‖ ^ 2
  have hsubset : changes ⊆ Finset.range (N - 1) := by
    intro j hj
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.piDigit i ≠ Theory.PiDigits.piDigit (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').1
  have hlower :
      (∑ j ∈ changes, 2 * (1 - Real.cos (Real.pi / 50))) ≤
        ∑ j ∈ changes, edge j := by
    apply Finset.sum_le_sum
    intro j hj
    apply pi_changed_edge_sq_cosine_lower
    have hj' : j ∈
        (Finset.range (N - 1)).filter
          (fun i ↦ Theory.PiDigits.piDigit i ≠ Theory.PiDigits.piDigit (i + 1)) := by
      simpa only [changes, Theory.PiDigits.T18.changePositions] using hj
    exact (Finset.mem_filter.mp hj').2
  have hmono : (∑ j ∈ changes, edge j) ≤
      ∑ j ∈ Finset.range (N - 1), edge j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j _hj _hnot
    exact sq_nonneg _
  calc
    2 * (1 - Real.cos (Real.pi / 50)) *
          (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) =
        ∑ j ∈ changes, 2 * (1 - Real.cos (Real.pi / 50)) := by
          simp only [Theory.PiDigits.T18.changeCount, changes,
            Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ j ∈ changes, edge j := hlower
    _ ≤ ∑ j ∈ Finset.range (N - 1), edge j := hmono
    _ = pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := rfl

/-- Unconditional fixed-pi Fourier-defect bridge.  Every change among the
first `N` decimal digits forces a rational amount of first-frequency defect;
the factor `N` comes from the path Poincare inequality. -/
theorem pi_firstFrequency_defect_ge_digitChanges (N : ℕ) :
    (N : ℝ) *
        (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 2500 ≤
      (N : ℝ) ^ 2 - ‖exponentialSum piOrbit N 1‖ ^ 2 := by
  have hpath := pi_pathEnergy_ge_changeCount N
  have hdefect := defect_ge_mul_pathEnergy
    (fun j ↦ phase 1 (piOrbit j)) N
    (fun i hi ↦ Theory.PiDigits.T27.norm_phase 1 (piOrbit i))
  calc
    (N : ℝ) *
          (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 2500 =
        (N : ℝ) / 4 *
          ((Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) / 625) := by
            ring
    _ ≤ (N : ℝ) / 4 * pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := by
      gcongr
    _ ≤ (N : ℝ) ^ 2 -
        ‖∑ i ∈ Finset.range N, phase 1 (piOrbit i)‖ ^ 2 := hdefect
    _ = (N : ℝ) ^ 2 - ‖exponentialSum piOrbit N 1‖ ^ 2 := rfl

/-- Strongest exact form of the unconditional fixed-pi bridge proved here.
The constant is the squared chord corresponding to a circular separation of
`1/100`, followed by the factor `N/4` from path Poincare. -/
theorem pi_firstFrequency_defect_ge_cosine_digitChanges (N : ℕ) :
    (N : ℝ) / 2 * (1 - Real.cos (Real.pi / 50)) *
        (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) ≤
      (N : ℝ) ^ 2 - ‖exponentialSum piOrbit N 1‖ ^ 2 := by
  have hpath := pi_pathEnergy_ge_cosine_changeCount N
  have hdefect := defect_ge_mul_pathEnergy
    (fun j ↦ phase 1 (piOrbit j)) N
    (fun i hi ↦ Theory.PiDigits.T27.norm_phase 1 (piOrbit i))
  calc
    (N : ℝ) / 2 * (1 - Real.cos (Real.pi / 50)) *
          (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ) =
        (N : ℝ) / 4 *
          (2 * (1 - Real.cos (Real.pi / 50)) *
            (Theory.PiDigits.T18.changeCount Theory.PiDigits.piDigit N : ℝ)) := by
              ring
    _ ≤ (N : ℝ) / 4 * pathEnergy (fun j ↦ phase 1 (piOrbit j)) N := by
      gcongr
    _ ≤ (N : ℝ) ^ 2 -
        ‖∑ i ∈ Finset.range N, phase 1 (piOrbit i)‖ ^ 2 := hdefect
    _ = (N : ℝ) ^ 2 - ‖exponentialSum piOrbit N 1‖ ^ 2 := rfl

end Theory.PiDigits.DigitChangeFourierDefect
