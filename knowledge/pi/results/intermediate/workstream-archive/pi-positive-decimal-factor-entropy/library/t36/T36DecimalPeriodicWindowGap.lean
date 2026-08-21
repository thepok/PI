import TheoryLib.PiPositiveDecimalFactorEntropy.T31T31DominantPeriodicTransfer
import TheoryLib.PiPositiveDecimalFactorEntropy.T33T33FixedDecimalPeriodicBlocks

/-!
# T36: effective irrationality excludes long decimal periodic windows

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none recorded; the canonical question was formulated locally.

This file proves a conditional sibling theorem for an arbitrary real `x` supplied
with an explicit decimal expansion. It imports the kernel-checked T31 and T33
modules, but makes no unconditional assertion about the decimal expansion or
irrationality measure of pi and proves no instance of C1.

Decimal positions are zero-based. A window beginning at `a` with length `L`
occupies `[a, a + L)`. "Period `p`" means exact digit equality modulo `p`, not
minimal period. The equation `x = Real.ofDigits d` is an explicit expansion
witness, so both terminating-zero and repeating-nine boundary representations
are admitted; no uniqueness of decimal expansion is used.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace DecimalFactorComplexity.PeriodicWindowGap

open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.FixedDecimalPeriodicBlocks
open Theory.PiDigits.T20

abbrev Digit := Fin 10
abbrev Stream := ℕ → Digit

/-- The explicit convention connecting a real to a possibly boundary-ambiguous
decimal stream. -/
def Represents (x : ℝ) (d : Stream) : Prop :=
  x = Real.ofDigits d

/-- Exact digit periodicity on the zero-based half-open window `[a, a + L)`.
The supplied `p` is a period; it need not be the least period. -/
def ExactPeriodicWindow (d : Stream) (a p L : ℕ) : Prop :=
  0 < p ∧ ∀ i < L, d (a + i) = d (a + i % p)

/-- Complete the finite window to the eventually periodic stream having the
same prefix before `a` and repeating the first `p` window digits forever. -/
def periodicCompletion (d : Stream) (a p n : ℕ) : Digit :=
  if n < a then d n else d (a + (n - a) % p)

/-- The integer numerator of the associated eventually periodic rational. -/
def periodicNumerator (d : Stream) (a p : ℕ) : ℕ :=
  prefixLabel d a 0 * (10 ^ p - 1) + prefixLabel d p a

/-- The displayed, not necessarily reduced, denominator. -/
def periodicDenominator (a p : ℕ) : ℕ :=
  10 ^ a * (10 ^ p - 1)

/-- The associated rational, reduced internally by Lean's rational-number
implementation but constructed from the displayed numerator and denominator. -/
def associatedRational (d : Stream) (a p : ℕ) : ℚ :=
  Rat.divInt (periodicNumerator d a p : ℤ) (periodicDenominator a p : ℤ)

/-- A standard effective irrationality-exponent premise with constant one.
`Q0` is an onset for the denominator `q`, not for a decimal position. -/
def EffectiveIrrationality (x μ : ℝ) (Q0 : ℕ) : Prop :=
  1 < μ ∧ ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ z : ℤ,
    1 / (q : ℝ) ^ μ < |x - (z : ℝ) / q|

/-- The deliberately displayed natural-to-real rounding allowance in the
final weak inequality. -/
def roundingConstant : ℝ := 1

theorem represents_iff (x : ℝ) (d : Stream) :
    Represents x d ↔ x = Real.ofDigits d := by
  rfl

theorem effectiveIrrationality_iff_quantifiers (x μ : ℝ) (Q0 : ℕ) :
    EffectiveIrrationality x μ Q0 ↔
      1 < μ ∧ ∀ q : ℕ, Q0 ≤ q → 0 < q → ∀ z : ℤ,
        1 / (q : ℝ) ^ μ < |x - (z : ℝ) / q| := by
  rfl

theorem exactPeriodicWindow_iff_quantifiers (d : Stream) (a p L : ℕ) :
    ExactPeriodicWindow d a p L ↔
      0 < p ∧ ∀ i < L, d (a + i) = d (a + i % p) := by
  rfl

theorem periodicCompletion_of_lt (d : Stream) (a p n : ℕ) (hn : n < a) :
    periodicCompletion d a p n = d n := by
  simp [periodicCompletion, hn]

theorem periodicCompletion_add (d : Stream) (a p i : ℕ) :
    periodicCompletion d a p (a + i) = d (a + i % p) := by
  simp [periodicCompletion]

/-- The purely periodic tail used to evaluate the completion exactly. -/
def periodicTail (d : Stream) (a p i : ℕ) : Digit :=
  d (a + i % p)

theorem periodicTail_periodic (d : Stream) (a p i : ℕ) :
    periodicTail d a p (i + p) = periodicTail d a p i := by
  simp [periodicTail]

theorem periodicTail_first (d : Stream) (a p i : ℕ) (hi : i < p) :
    periodicTail d a p i = d (a + i) := by
  simp [periodicTail, Nat.mod_eq_of_lt hi]

theorem periodicDenominator_pos (a p : ℕ) (hp : 0 < p) :
    0 < periodicDenominator a p := by
  unfold periodicDenominator
  have hpow : 1 < 10 ^ p := one_lt_pow₀ (by norm_num) hp.ne'
  exact Nat.mul_pos (pow_pos (by norm_num) a) (Nat.sub_pos_of_lt hpow)

theorem periodicDenominator_cast (a p : ℕ) :
    (periodicDenominator a p : ℝ) =
      (10 : ℝ) ^ a * ((10 : ℝ) ^ p - 1) := by
  unfold periodicDenominator
  push_cast
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (10 : ℕ)))]
  norm_num

/-- Casting the associated rational to the reals recovers the displayed
numerator-over-denominator expression. -/
theorem associatedRational_cast (d : Stream) (a p : ℕ) :
    (associatedRational d a p : ℝ) =
      (periodicNumerator d a p : ℝ) / periodicDenominator a p := by
  unfold associatedRational
  rw [Rat.cast_divInt]
  push_cast
  rfl

/-- The reduced denominator of the associated rational divides the displayed
decimal denominator. -/
theorem associatedRational_den_dvd (d : Stream) (a p : ℕ) :
    (associatedRational d a p).den ∣ periodicDenominator a p := by
  rw [← Int.natCast_dvd_natCast]
  unfold associatedRational
  exact Rat.den_dvd _ _

/-- Exact evaluation of the purely periodic tail. -/
theorem periodicTail_ofDigits_eq (d : Stream) (a p : ℕ) (hp : 0 < p) :
    Real.ofDigits (periodicTail d a p) =
      (prefixLabel d p a : ℝ) / ((10 : ℝ) ^ p - 1) := by
  have hshift : (fun i => periodicTail d a p (i + p)) = periodicTail d a p := by
    funext i
    exact periodicTail_periodic d a p i
  have hsum :
      (∑ i ∈ Finset.range p, Real.ofDigitsTerm (periodicTail d a p) i) =
        (prefixLabel d p a : ℝ) / (10 : ℝ) ^ p := by
    rw [← prefixSum_eq_label_div d p a]
    apply Finset.sum_congr rfl
    intro i hi
    have hip : i < p := Finset.mem_range.mp hi
    simp only [Real.ofDigitsTerm]
    rw [periodicTail_first d a p i hip]
  have hsplit := Real.ofDigits_eq_sum_add_ofDigits (periodicTail d a p) p
  rw [hshift, hsum] at hsplit
  have hpowpos : (0 : ℝ) < (10 : ℝ) ^ p := by positivity
  have hden : (10 : ℝ) ^ p - 1 ≠ 0 := by
    have : (1 : ℝ) < (10 : ℝ) ^ p := one_lt_pow₀ (by norm_num) hp.ne'
    linarith
  rw [eq_div_iff hden]
  rw [inv_eq_one_div] at hsplit
  norm_num at hsplit
  field_simp [hpowpos.ne'] at hsplit ⊢
  linarith

/-- Exact numerator and denominator of the associated rational. The theorem
uses the displayed denominator itself, hence explicitly witnesses a denominator
dividing `10^a * (10^p - 1)`. -/
theorem periodicCompletion_ofDigits_eq_rational
    (d : Stream) (a p : ℕ) (hp : 0 < p) :
    Real.ofDigits (periodicCompletion d a p) =
      (periodicNumerator d a p : ℝ) / periodicDenominator a p := by
  have hprefix :
      (∑ i ∈ Finset.range a,
          Real.ofDigitsTerm (periodicCompletion d a p) i) =
        (prefixLabel d a 0 : ℝ) / (10 : ℝ) ^ a := by
    rw [← prefixSum_eq_label_div d a 0]
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i < a := Finset.mem_range.mp hi
    simp only [Real.ofDigitsTerm]
    rw [periodicCompletion_of_lt d a p i hia]
    simp
  have htail :
      (fun i => periodicCompletion d a p (i + a)) = periodicTail d a p := by
    funext i
    rw [Nat.add_comm]
    exact periodicCompletion_add d a p i
  rw [Real.ofDigits_eq_sum_add_ofDigits (periodicCompletion d a p) a,
    hprefix, htail, periodicTail_ofDigits_eq d a p hp,
    periodicDenominator_cast]
  unfold periodicNumerator
  have hpowNat : 1 ≤ 10 ^ p := one_le_pow₀ (by norm_num)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hpowNat, Nat.cast_one]
  push_cast
  have hpowA : (10 : ℝ) ^ a ≠ 0 := by positivity
  have hpowP : (10 : ℝ) ^ p - 1 ≠ 0 := by
    have : (1 : ℝ) < (10 : ℝ) ^ p := one_lt_pow₀ (by norm_num) hp.ne'
    linarith
  field_simp

/-- Exact identification of the completion with the actual rational value. -/
theorem periodicCompletion_ofDigits_eq_associatedRational
    (d : Stream) (a p : ℕ) (hp : 0 < p) :
    Real.ofDigits (periodicCompletion d a p) = associatedRational d a p := by
  rw [associatedRational_cast]
  exact periodicCompletion_ofDigits_eq_rational d a p hp

/-- Exact window equality gives agreement with the rational completion through
the first `a + L` digits. -/
theorem periodicCompletion_agrees_through_window
    (d : Stream) (a p L : ℕ) (hw : ExactPeriodicWindow d a p L) :
    ∀ n < a + L, d n = periodicCompletion d a p n := by
  intro n hn
  by_cases hna : n < a
  · rw [periodicCompletion_of_lt d a p n hna]
  · have han : a ≤ n := Nat.le_of_not_gt hna
    let i := n - a
    have hiL : i < L := by
      dsimp [i]
      omega
    have hi := hw.2 i hiL
    have hn_eq : n = a + i := by
      dsimp [i]
      omega
    rw [hn_eq, periodicCompletion_add]
    exact hi

/-- The decimal-boundary-safe approximation estimate. Closed endpoint equality
is allowed, including for a repeating-nine representation. -/
theorem periodic_window_approximation
    (x : ℝ) (d : Stream) (a p L : ℕ)
    (hx : Represents x d) (hw : ExactPeriodicWindow d a p L) :
    |x - (periodicNumerator d a p : ℝ) / periodicDenominator a p| ≤
      ((10 : ℝ) ^ (a + L))⁻¹ := by
  rw [hx, ← periodicCompletion_ofDigits_eq_rational d a p hw.1]
  exact Real.abs_ofDigits_sub_ofDigits_le
    (periodicCompletion_agrees_through_window d a p L hw)

/-- The same boundary-safe error bound stated directly for the associated
rational rather than its displayed numerator-over-denominator presentation. -/
theorem periodic_window_associatedRational_approximation
    (x : ℝ) (d : Stream) (a p L : ℕ)
    (hx : Represents x d) (hw : ExactPeriodicWindow d a p L) :
    |x - (associatedRational d a p : ℝ)| ≤
      ((10 : ℝ) ^ (a + L))⁻¹ := by
  rw [associatedRational_cast]
  exact periodic_window_approximation x d a p L hx hw

/-- The displayed denominator is strictly below `10^(a+p)`. -/
theorem periodicDenominator_lt_ten_pow_add (a p : ℕ) :
    periodicDenominator a p < 10 ^ (a + p) := by
  unfold periodicDenominator
  rw [pow_add]
  have hsub : 10 ^ p - 1 < 10 ^ p := Nat.sub_lt (by positivity) (by norm_num)
  exact Nat.mul_lt_mul_of_pos_left hsub (by positivity)

/-- Generic periodic-window gap theorem. Every parameter, onset, decimal
convention, denominator, approximation error, and the rounding constant is
visible in the statement. -/
theorem effectiveIrrationality_periodic_window_gap
    (x μ : ℝ) (Q0 a p L : ℕ) (d : Stream)
    (hx : Represents x d)
    (hIrr : EffectiveIrrationality x μ Q0)
    (hw : ExactPeriodicWindow d a p L)
    (hOnset : Q0 ≤ periodicDenominator a p) :
    (L : ℝ) ≤ (μ - 1) * a + μ * p + roundingConstant := by
  let q := periodicDenominator a p
  let z : ℤ := periodicNumerator d a p
  have hqposNat : 0 < q := periodicDenominator_pos a p hw.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hqLtNat : q < 10 ^ (a + p) :=
    periodicDenominator_lt_ten_pow_add a p
  have hqLt : (q : ℝ) < (10 : ℝ) ^ (a + p) := by exact_mod_cast hqLtNat
  have hlower := hIrr.2 q hOnset hqposNat z
  have hupper := periodic_window_approximation x d a p L hx hw
  have hz : (z : ℝ) = periodicNumerator d a p := by simp [z]
  rw [hz] at hlower
  have hirrUpper : 1 / (q : ℝ) ^ μ < ((10 : ℝ) ^ (a + L))⁻¹ :=
    hlower.trans_le hupper
  have hmuPos : 0 < μ := lt_trans zero_lt_one hIrr.1
  have hqPower :
      ((10 : ℝ) ^ (a + p)) ^ (-μ) < (q : ℝ) ^ (-μ) := by
    exact (Real.rpow_lt_rpow_iff_of_neg (by positivity) hqpos (neg_neg_of_pos hmuPos)).2 hqLt
  have hqNeg : (q : ℝ) ^ (-μ) = 1 / (q : ℝ) ^ μ := by
    rw [Real.rpow_neg hqpos.le]
    simp [one_div]
  have hpower :
      ((10 : ℝ) ^ (a + p)) ^ (-μ) < ((10 : ℝ) ^ (a + L))⁻¹ := by
    rw [hqNeg] at hqPower
    exact hqPower.trans hirrUpper
  have hexponents :
      -μ * ((a + p : ℕ) : ℝ) < -((a + L : ℕ) : ℝ) := by
    rw [← Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 10)]
    convert hpower using 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      ring
    · rw [← Real.rpow_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
  unfold roundingConstant
  push_cast at hexponents ⊢
  linarith

/-- One inspectable generic certificate displaying the associated rational,
denominator divisibility, approximation error, and rounded window bound. -/
theorem decimal_periodic_window_certificate
    (x μ : ℝ) (Q0 a p L : ℕ) (d : Stream)
    (hx : Represents x d)
    (hIrr : EffectiveIrrationality x μ Q0)
    (hw : ExactPeriodicWindow d a p L)
    (hOnset : Q0 ≤ periodicDenominator a p) :
    periodicDenominator a p ∣ 10 ^ a * (10 ^ p - 1) ∧
      (associatedRational d a p).den ∣ periodicDenominator a p ∧
      Real.ofDigits (periodicCompletion d a p) =
        associatedRational d a p ∧
      |x - (associatedRational d a p : ℝ)| ≤
        ((10 : ℝ) ^ (a + L))⁻¹ ∧
      (L : ℝ) ≤ (μ - 1) * a + μ * p + roundingConstant := by
  exact ⟨dvd_refl _, associatedRational_den_dvd d a p,
    periodicCompletion_ofDigits_eq_associatedRational d a p hw.1,
    periodic_window_associatedRational_approximation x d a p L hx hw,
    effectiveIrrationality_periodic_window_gap x μ Q0 a p L d hx hIrr hw hOnset⟩

/-! ## T33 specialization -/

/-- T33's rational model has digit period `period s`, including at decimal
boundaries because `decimalDigit` is mathlib's fixed floor-based convention. -/
theorem t33_modelDecimalDigit_periodic (s j : ℕ) :
    decimalDigit (modelSeed s) (j + period s) =
      decimalDigit (modelSeed s) j := by
  have hseed : 0 ≤ modelSeed s := by
    unfold modelSeed ScaleDependentDecimalOrbit.seed
    positivity
  calc
    decimalDigit (modelSeed s) (j + period s) =
        decimalDigit (baseTenOrbit (modelSeed s) (j + period s)) 0 := by
      symm
      simpa using decimalDigit_baseTenOrbit
        (modelSeed s) hseed (j + period s) 0
    _ = decimalDigit (baseTenOrbit (modelSeed s) j) 0 := by
      rw [periodicModel_periodic s j]
    _ = decimalDigit (modelSeed s) j := by
      simpa using decimalDigit_baseTenOrbit (modelSeed s) hseed j 0

theorem t33_modelWindowTail_periodic (s : ℕ) :
    Function.Periodic
      (fun i => decimalDigit (modelSeed s) (boundary s + i)) (period s) := by
  intro i
  simpa only [Nat.add_assoc] using
    t33_modelDecimalDigit_periodic s (boundary s + i)

/-- Whenever one complete T33 period fits in its copied block, the whole block
is an exact period-`period s` window in the generic zero-based convention. -/
theorem t33_exactPeriodicWindow_of_period_le (s : ℕ)
    (hfit : period s ≤ blockLength s) :
    ExactPeriodicWindow fixedDigitStream (boundary s) (period s) (blockLength s) := by
  refine ⟨by simp [period, ScaleDependentDecimalOrbit.period], ?_⟩
  intro i hi
  have hmod : i % period s < blockLength s :=
    (Nat.mod_lt i (by simp [period, ScaleDependentDecimalOrbit.period])).trans_le hfit
  rw [fixedDigitStream_block_digit s i hi,
    fixedDigitStream_block_digit s (i % period s) hmod]
  exact (t33_modelWindowTail_periodic s).map_mod_nat i |>.symm

/-- The T33 block occupies asymptotically all of its sample. -/
theorem t33_blockLength_div_sampleSize_tendsto_one :
    Tendsto (fun s => (blockLength s : ℝ) / sampleSize s) atTop (𝓝 1) := by
  have hMpos (s : ℕ) : (0 : ℝ) < sampleSize s := by
    exact_mod_cast (show 0 < sampleSize s by
      simp [sampleSize, ScaleDependentDecimalOrbit.sampleSize])
  convert
    (tendsto_const_nhds.sub boundary_div_sampleSize_tendsto_zero :
      Tendsto (fun s : ℕ =>
        (1 : ℝ) - (boundary s : ℝ) / sampleSize s) atTop (𝓝 (1 - 0))) using 1
  · funext s
    rw [blockLength, Nat.cast_sub (boundary_lt_sampleSize s).le]
    field_simp [hMpos s |>.ne']
  · norm_num

/-- Eventually the exact model period fits inside T33's copied block. -/
theorem t33_period_le_blockLength_eventually :
    ∀ᶠ s in atTop, period s ≤ blockLength s := by
  have hMpos (s : ℕ) : (0 : ℝ) < sampleSize s := by
    exact_mod_cast (show 0 < sampleSize s by
      simp [sampleSize, ScaleDependentDecimalOrbit.sampleSize])
  have hlt : ∀ᶠ s in atTop,
      (period s : ℝ) / sampleSize s < (blockLength s : ℝ) / sampleSize s :=
    Filter.Tendsto.eventually_lt period_div_sampleSize_tendsto_zero
      t33_blockLength_div_sampleSize_tendsto_one zero_lt_one
  filter_upwards [hlt] with s hs
  have : (period s : ℝ) < blockLength s :=
    (div_lt_div_iff_of_pos_right (hMpos s)).mp hs
  exact_mod_cast this.le

/-- The T33 displayed denominator eventually passes every fixed effective
irrationality onset. -/
theorem t33_periodicDenominator_eventually_ge (Q0 : ℕ) :
    ∀ᶠ s in atTop, Q0 ≤ periodicDenominator (boundary s) (period s) := by
  have hpTop := period_tendsto_atTop.eventually_gt_atTop (Q0 : ℝ)
  filter_upwards [hpTop] with s hs
  have hQp : Q0 ≤ period s := by exact_mod_cast hs.le
  have hp : 0 < period s := by simp [period, ScaleDependentDecimalOrbit.period]
  have hpPow : period s < 10 ^ period s :=
    Nat.lt_pow_self (by norm_num)
  have hpSub : period s ≤ 10 ^ period s - 1 := by omega
  calc
    Q0 ≤ period s := hQp
    _ ≤ 10 ^ period s - 1 := hpSub
    _ ≤ periodicDenominator (boundary s) (period s) := by
      unfold periodicDenominator
      exact Nat.le_mul_of_pos_left _ (by positivity)

/-- Fully displayed T33 specialization of the generic certificate. All
parameters remain the recursive T33 quantities rather than hidden witnesses. -/
theorem t33_decimal_periodic_window_certificate
    (μ : ℝ) (Q0 s : ℕ)
    (hIrr : EffectiveIrrationality fixedSeed μ Q0)
    (hfit : period s ≤ blockLength s)
    (hOnset : Q0 ≤ periodicDenominator (boundary s) (period s)) :
    periodicDenominator (boundary s) (period s) ∣
        10 ^ boundary s * (10 ^ period s - 1) ∧
      (associatedRational fixedDigitStream (boundary s) (period s)).den ∣
        periodicDenominator (boundary s) (period s) ∧
      Real.ofDigits
          (periodicCompletion fixedDigitStream (boundary s) (period s)) =
        associatedRational fixedDigitStream (boundary s) (period s) ∧
      |fixedSeed -
          (associatedRational fixedDigitStream (boundary s) (period s) : ℝ)| ≤
        ((10 : ℝ) ^ (boundary s + blockLength s))⁻¹ ∧
      (blockLength s : ℝ) ≤
        (μ - 1) * boundary s + μ * period s + roundingConstant := by
  exact decimal_periodic_window_certificate
    fixedSeed μ Q0 (boundary s) (period s) (blockLength s) fixedDigitStream
    rfl hIrr (t33_exactPeriodicWindow_of_period_le s hfit) hOnset

/-- T33's block/sample/period growth eventually exceeds the generic finite-μ
upper bound, with the same displayed rounding constant `1`. -/
theorem t33_parameters_eventually_exceed_fixed_bound (μ : ℝ) :
    ∀ᶠ s in atTop,
      (μ - 1) * (boundary s : ℝ) + μ * (period s : ℝ) + roundingConstant <
        (blockLength s : ℝ) := by
  have hMpos (s : ℕ) : (0 : ℝ) < sampleSize s := by
    exact_mod_cast (show 0 < sampleSize s by
      simp [sampleSize, ScaleDependentDecimalOrbit.sampleSize])
  have hone : Tendsto (fun s : ℕ => roundingConstant / sampleSize s)
      atTop (𝓝 0) := by
    have hbound : ∀ᶠ s in atTop,
        0 ≤ roundingConstant / sampleSize s ∧
          roundingConstant / sampleSize s ≤ (period s : ℝ) / sampleSize s :=
      Filter.Eventually.of_forall fun s => by
        have hp : 1 ≤ period s := by
          exact one_le_pow₀ (by norm_num)
        constructor
        · unfold roundingConstant
          positivity
        · unfold roundingConstant
          exact div_le_div_of_nonneg_right (by exact_mod_cast hp) (hMpos s).le
    exact squeeze_zero' (hbound.mono fun _ h => h.1)
      (hbound.mono fun _ h => h.2) period_div_sampleSize_tendsto_zero
  have hright : Tendsto (fun s : ℕ =>
      ((μ - 1) * (boundary s : ℝ) + μ * (period s : ℝ) + roundingConstant) /
        sampleSize s) atTop (𝓝 0) := by
    have hterms :=
      ((boundary_div_sampleSize_tendsto_zero.const_mul (μ - 1)).add
        (period_div_sampleSize_tendsto_zero.const_mul μ)).add hone
    convert hterms using 1
    funext s
    field_simp [hMpos s |>.ne']
    ring
  have hlt := Filter.Tendsto.eventually_lt hright
    t33_blockLength_div_sampleSize_tendsto_one zero_lt_one
  filter_upwards [hlt] with s hs
  exact (div_lt_div_iff_of_pos_right (hMpos s)).mp hs

/-- Hence the T33 fixed seed cannot satisfy this finite effective
irrationality hypothesis for any fixed exponent and onset. This is a statement
about T33's non-pi sibling seed only. -/
theorem t33_fixedSeed_not_effectiveIrrationality (μ : ℝ) (Q0 : ℕ) :
    ¬ EffectiveIrrationality fixedSeed μ Q0 := by
  intro hIrr
  have hfalse : ∀ᶠ (s : ℕ) in atTop, False := by
    filter_upwards [t33_period_le_blockLength_eventually,
      t33_periodicDenominator_eventually_ge Q0,
      t33_parameters_eventually_exceed_fixed_bound μ] with s hfit hOnset hlarge
    have hbound := (t33_decimal_periodic_window_certificate μ Q0 s
      hIrr hfit hOnset).2.2.2.2
    exact (not_le_of_gt hlarge) hbound
  exact hfalse.exists.elim fun _ h => h

/-! ## Explicit nonclaims -/

structure ScopeStatus where
  appliesToT33FixedSeed : Bool
  provesPiIrrationalityEstimate : Bool
  amplifiesT10 : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  appliesToT33FixedSeed := true
  provesPiIrrationalityEstimate := false
  amplifiesT10 := false
  provesC1 := false
  disprovesC1 := false

/-- Excluding the exact periodic-window mechanism neither amplifies T10 nor
proves C1; no irrationality estimate for pi is asserted in this file. -/
theorem explicit_pi_T10_C1_nonclaims :
    scopeStatus.appliesToT33FixedSeed = true ∧
      scopeStatus.provesPiIrrationalityEstimate = false ∧
      scopeStatus.amplifiesT10 = false ∧
      scopeStatus.provesC1 = false ∧ scopeStatus.disprovesC1 = false := by
  norm_num [scopeStatus]

end DecimalFactorComplexity.PeriodicWindowGap

#print axioms DecimalFactorComplexity.PeriodicWindowGap.associatedRational_den_dvd
#print axioms DecimalFactorComplexity.PeriodicWindowGap.periodicCompletion_ofDigits_eq_associatedRational
#print axioms DecimalFactorComplexity.PeriodicWindowGap.periodic_window_associatedRational_approximation
#print axioms DecimalFactorComplexity.PeriodicWindowGap.effectiveIrrationality_periodic_window_gap
#print axioms DecimalFactorComplexity.PeriodicWindowGap.decimal_periodic_window_certificate
#print axioms DecimalFactorComplexity.PeriodicWindowGap.t33_exactPeriodicWindow_of_period_le
#print axioms DecimalFactorComplexity.PeriodicWindowGap.t33_decimal_periodic_window_certificate
#print axioms DecimalFactorComplexity.PeriodicWindowGap.t33_parameters_eventually_exceed_fixed_bound
#print axioms DecimalFactorComplexity.PeriodicWindowGap.t33_fixedSeed_not_effectiveIrrationality
#print axioms DecimalFactorComplexity.PeriodicWindowGap.explicit_pi_T10_C1_nonclaims
