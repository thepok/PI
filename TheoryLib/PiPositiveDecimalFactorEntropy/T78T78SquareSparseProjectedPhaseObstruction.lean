import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
import TheoryLib.PiPositiveDecimalFactorEntropy.T57T57MovingWordCoreObstruction
import TheoryLib.PiPositiveDecimalFactorEntropy.T72T72ProjectedPeriodicity

/-!
# T78: square-sparse obstruction to uniform projected-phase depth

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none; the canonical question was formulated locally.

This is a sibling construction. It makes no assertion about pi and neither
proves nor disproves C6 or C1.
-/

noncomputable section

open Filter Finset Set Topology

namespace DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorEntropy.T57MovingWordCoreObstruction
open DecimalFactorEntropy.T65RationalCoreCertificate
open DecimalFactorEntropy.T72ProjectedPeriodicity
open DecimalFactorEntropy.T72ProjectedPeriodicity.T48
open DecimalFactorEntropy.T48EndpointCarryKMP
open DecimalFactorComplexity
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.FactorComplexity
open Theory.PiDigits.T20
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The inclusive depth attached to length `m`. -/
def radius (m : ℕ) : ℕ := 2 ^ m

/-- The square spacing, deliberately much larger than every relevant block. -/
def spacing (m : ℕ) : ℕ := 10 * (radius m + m + 1)

/-- The one-based endpoint of square block number `t`; block numbers start at one. -/
def blockEnd (m t : ℕ) : ℕ := spacing m * t ^ 2

/-- The requested square-sparse real. -/
def squareReal (m : ℕ) : ℝ :=
  ∑' t : {t : ℕ // 1 ≤ t}, (10 : ℝ) ^ (-(blockEnd m t.val : ℤ))

/-- Zero-based position of the `t`th isolated digit. -/
def blockPosition (m : ℕ) (t : {t : ℕ // 1 ≤ t}) : ℕ :=
  blockEnd m t.val - 1

/-- A one exactly at zero-based decimal position `D_m t² - 1`, for `t ≥ 1`. -/
def squareDigits (m n : ℕ) : Fin 10 := by
  classical
  exact if n ∈ Set.range (blockPosition m) then 1 else 0

/-- T57's omitted word, now indexed by the square-series parameter. -/
abbrev omittedWordAt (m : ℕ) : List (Fin 10) := omittedWord m

@[simp] theorem radius_eq (m : ℕ) : radius m = 2 ^ m := rfl

@[simp] theorem spacing_eq (m : ℕ) :
    spacing m = 10 * (2 ^ m + m + 1) := rfl

@[simp] theorem omittedWordAt_length (m : ℕ) : (omittedWordAt m).length = m := by
  exact omittedWord_length m

theorem spacing_pos (m : ℕ) : 0 < spacing m := by
  simp [spacing]

theorem blockEnd_strictMono (m : ℕ) : StrictMono (blockEnd m) := by
  intro a b hab
  dsimp [blockEnd]
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hab (by omega)) (spacing_pos m)

theorem blockEnd_injective (m : ℕ) : Function.Injective (blockEnd m) :=
  (blockEnd_strictMono m).injective

theorem blockEnd_pos (m t : ℕ) (ht : 1 ≤ t) : 0 < blockEnd m t := by
  exact Nat.mul_pos (spacing_pos m) (Nat.pow_pos ht)

theorem blockPosition_succ (m : ℕ) (t : {t : ℕ // 1 ≤ t}) :
    blockPosition m t + 1 = blockEnd m t.val := by
  rw [blockPosition]
  exact Nat.sub_add_cancel (blockEnd_pos m t.val t.property)

theorem blockPosition_injective (m : ℕ) : Function.Injective (blockPosition m) := by
  intro s t h
  apply Subtype.ext
  apply blockEnd_injective m
  rw [← blockPosition_succ m s, ← blockPosition_succ m t, h]

theorem squareDigits_at_blockEnd (m t : ℕ) (ht : 1 ≤ t) :
    squareDigits m (blockEnd m t - 1) = 1 := by
  rw [squareDigits, if_pos]
  exact ⟨⟨t, ht⟩, rfl⟩

theorem squareDigits_eq_zero_of_not_blockEnd (m n : ℕ)
    (h : ∀ t : ℕ, 1 ≤ t → n + 1 ≠ blockEnd m t) :
    squareDigits m n = 0 := by
  rw [squareDigits, if_neg]
  rintro ⟨t, rfl⟩
  exact h t.val t.property (blockPosition_succ m t)

@[simp] theorem squareDigits_blockPosition
    (m : ℕ) (t : {t : ℕ // 1 ≤ t}) :
    squareDigits m (blockPosition m t) = 1 := by
  simp [squareDigits]

theorem ofDigitsTerm_squareDigits_blockPosition
    (m : ℕ) (t : {t : ℕ // 1 ≤ t}) :
    Real.ofDigitsTerm (squareDigits m) (blockPosition m t) =
      (10 : ℝ) ^ (-(blockEnd m t.val : ℤ)) := by
  rw [Real.ofDigitsTerm, squareDigits_blockPosition]
  simp only [Fin.val_one, Nat.cast_one, one_mul]
  rw [blockPosition_succ]
  simp [zpow_neg, zpow_natCast]

theorem ofDigitsTerm_squareDigits_eq_zero_of_not_mem
    (m n : ℕ) (hn : n ∉ Set.range (blockPosition m)) :
    Real.ofDigitsTerm (squareDigits m) n = 0 := by
  simp [Real.ofDigitsTerm, squareDigits, hn]

/-- The selected sparse decimal stream evaluates to the requested square sum.
This also fixes the zero-based/one-based endpoint convention exactly. -/
theorem squareReal_eq_ofDigits (m : ℕ) :
    squareReal m = Real.ofDigits (squareDigits m) := by
  let S : Set ℕ := Set.range (blockPosition m)
  let Sc : Set ℕ := {n | n ∉ S}
  let f : ℕ → ℝ := Real.ofDigitsTerm (squareDigits m)
  have hf : Summable f := Real.summable_ofDigitsTerm
  have hcompl' : (∑' n : Sc, f n.val) = 0 := by
    calc
      (∑' n : Sc, f n.val) = ∑' _n : Sc, (0 : ℝ) := by
        apply tsum_congr
        intro n
        exact ofDigitsTerm_squareDigits_eq_zero_of_not_mem m n.val n.property
      _ = 0 := tsum_zero
  have hsub : (∑' n : S, f n.val) = ∑' n : ℕ, f n := by
    have hsplit := hf.tsum_subtype_add_tsum_subtype_compl S
    have hSc : Sᶜ = Sc := by ext n; simp [Sc]
    rw [hSc] at hsplit
    rw [hcompl', add_zero] at hsplit
    exact hsplit
  let e := Equiv.ofInjective (blockPosition m) (blockPosition_injective m)
  have hequiv := e.tsum_eq (fun n : S => f n.val)
  change (∑' t : {t : ℕ // 1 ≤ t},
      (10 : ℝ) ^ (-(blockEnd m t.val : ℤ))) = ∑' n : ℕ, f n
  rw [← hsub, ← hequiv]
  apply tsum_congr
  intro t
  simpa [e, S, f] using (ofDigitsTerm_squareDigits_blockPosition m t).symm

/-- Number of zero digits strictly between consecutive isolated ones. -/
def zeroGap (m N : ℕ) : ℕ :=
  blockEnd m (N + 1) - blockEnd m N - 1

theorem blockEnd_succ (m N : ℕ) :
    blockEnd m (N + 1) = blockEnd m N + spacing m * (2 * N + 1) := by
  simp only [blockEnd]
  ring

theorem zeroGap_eq (m N : ℕ) :
    zeroGap m N = spacing m * (2 * N + 1) - 1 := by
  rw [zeroGap, blockEnd_succ]
  omega

theorem squareDigits_shift_eq_zero_before_gap
    (m N i : ℕ) (hN : 1 ≤ N) (hi : i < zeroGap m N) :
    squareDigits m (i + blockEnd m N) = 0 := by
  apply squareDigits_eq_zero_of_not_blockEnd
  intro t ht heq
  by_cases htN : t ≤ N
  · have hend : blockEnd m t ≤ blockEnd m N :=
      (blockEnd_strictMono m).monotone htN
    omega
  · have hNt : N + 1 ≤ t := by omega
    have hnext : blockEnd m (N + 1) ≤ blockEnd m t :=
      (blockEnd_strictMono m).monotone hNt
    rw [zeroGap_eq] at hi
    rw [blockEnd_succ] at hnext
    omega

theorem shiftedSquareDigits_ofDigits_pos (m N : ℕ) (hN : 1 ≤ N) :
    0 < Real.ofDigits (fun i => squareDigits m (i + blockEnd m N)) := by
  let k := zeroGap m N
  let d : ℕ → Fin 10 := fun i => squareDigits m (i + blockEnd m N)
  have hnext : d k = 1 := by
    dsimp [d, k]
    have heq : zeroGap m N + blockEnd m N = blockEnd m (N + 1) - 1 := by
      rw [zeroGap_eq, blockEnd_succ]
      have hd : 0 < spacing m * (2 * N + 1) :=
        Nat.mul_pos (spacing_pos m) (by omega)
      omega
    rw [heq]
    exact squareDigits_at_blockEnd m (N + 1) (by omega)
  have hterm : 0 < Real.ofDigitsTerm d k := by
    rw [Real.ofDigitsTerm, hnext]
    simp
  have hle : Real.ofDigitsTerm d k ≤ Real.ofDigits d := by
    exact Real.summable_ofDigitsTerm.le_tsum k (fun _ _ => Real.ofDigitsTerm_nonneg)
  exact hterm.trans_le hle

theorem shiftedSquareDigits_ofDigits_le_gap
    (m N : ℕ) (hN : 1 ≤ N) :
    Real.ofDigits (fun i => squareDigits m (i + blockEnd m N)) ≤
      ((10 : ℝ) ^ zeroGap m N)⁻¹ := by
  let d : ℕ → Fin 10 := fun i => squareDigits m (i + blockEnd m N)
  rw [Real.ofDigits_eq_sum_add_ofDigits d (zeroGap m N)]
  have hsum : (∑ i ∈ Finset.range (zeroGap m N), Real.ofDigitsTerm d i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hzero : d i = 0 := squareDigits_shift_eq_zero_before_gap m N i hN
      (Finset.mem_range.mp hi)
    simp [Real.ofDigitsTerm, hzero]
  rw [hsum, zero_add]
  exact mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)

theorem zeroGap_ge (m N : ℕ) : N ≤ zeroGap m N := by
  rw [zeroGap_eq]
  have hs : 10 ≤ spacing m := by simp [spacing]
  apply Nat.le_sub_of_add_le
  calc
    N + 1 ≤ 10 * (2 * N + 1) := by omega
    _ ≤ spacing m * (2 * N + 1) := Nat.mul_le_mul_right _ hs

theorem denominator_lt_ten_pow_zeroGap (m B : ℕ) :
    B < 10 ^ zeroGap m (B + 1) := by
  have hNG : B + 1 ≤ zeroGap m (B + 1) := zeroGap_ge m (B + 1)
  calc
    B < B + 1 := by omega
    _ < 2 ^ (B + 1) := (B + 1).lt_two_pow_self
    _ ≤ 10 ^ (B + 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ 10 ^ zeroGap m (B + 1) := Nat.pow_le_pow_right (by omega) hNG

theorem pow_mul_squareReal_eq_prefix_add_tail (m N : ℕ) :
    (10 : ℝ) ^ blockEnd m N * squareReal m =
      (prefixLabel (squareDigits m) (blockEnd m N) 0 : ℕ) +
        Real.ofDigits (fun i => squareDigits m (i + blockEnd m N)) := by
  rw [squareReal_eq_ofDigits,
    Real.ofDigits_eq_sum_add_ofDigits (squareDigits m) (blockEnd m N)]
  have hprefix := prefixSum_eq_label_div (squareDigits m) (blockEnd m N) 0
  simp only [zero_add] at hprefix
  rw [hprefix]
  have hp : (10 : ℝ) ^ blockEnd m N ≠ 0 := by positivity
  field_simp
  ring

/-- The square-spaced decimal real is irrational. The proof uses the exact
integer obtained by clearing the denominator at the `N`th block endpoint and
the strictly positive next-block tail, which is eventually smaller than one
over that denominator. -/
theorem squareReal_irrational (m : ℕ) : Irrational (squareReal m) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  let B : ℕ := b.natAbs
  let N : ℕ := B + 1
  let K : ℕ := blockEnd m N
  let P : ℕ := prefixLabel (squareDigits m) K 0
  let y : ℝ := Real.ofDigits (fun i => squareDigits m (i + K))
  have hN : 1 ≤ N := by simp [N]
  have hypos : 0 < y := by
    simpa [y, K] using shiftedSquareDigits_ofDigits_pos m N hN
  have hyle : y ≤ ((10 : ℝ) ^ zeroGap m N)⁻¹ := by
    simpa [y, K] using shiftedSquareDigits_ofDigits_le_gap m N hN
  have hBpowNat : B < 10 ^ zeroGap m N := by
    simpa [N] using denominator_lt_ten_pow_zeroGap m B
  have hBpow : (B : ℝ) < (10 : ℝ) ^ zeroGap m N := by
    exact_mod_cast hBpowNat
  have hBylt : (B : ℝ) * y < 1 := by
    calc
      (B : ℝ) * y ≤ (B : ℝ) * ((10 : ℝ) ^ zeroGap m N)⁻¹ :=
        mul_le_mul_of_nonneg_left hyle (by positivity)
      _ < 1 := by
        rw [← div_eq_mul_inv]
        exact (div_lt_one (by positivity)).2 hBpow
  have heq := pow_mul_squareReal_eq_prefix_add_tail m N
  change (10 : ℝ) ^ K * squareReal m = (P : ℕ) + y at heq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcleared : (10 : ℝ) ^ K * (a : ℝ) =
      (b : ℝ) * (P : ℝ) + (b : ℝ) * y := by
    rw [hab] at heq
    field_simp [hbR] at heq
    nlinarith
  let z : ℤ := (10 ^ K : ℕ) * a - b * (P : ℤ)
  have hz : (z : ℝ) = (b : ℝ) * y := by
    dsimp [z]
    push_cast
    nlinarith
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    have : (b : ℝ) * y ≠ 0 := mul_ne_zero hbR hypos.ne'
    exact this hz.symm
  have hzabs : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hnat : 1 ≤ z.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz0)
    calc
      (1 : ℝ) ≤ (z.natAbs : ℕ) := by exact_mod_cast hnat
      _ = |(z : ℝ)| := by simp
  have habs : |(z : ℝ)| = (B : ℝ) * y := by
    rw [hz, abs_mul, abs_of_pos hypos]
    simp [B]
  rw [habs] at hzabs
  linarith

/-- A safe width containing all digits of the finite decimal block `16^j`. -/
def blockWidth (j : ℕ) : ℕ := 2 * j + 2

/-- The explicit zero-based interval reserved for the `t`th copy of `16^j`. -/
def InBlockInterval (m j t n : ℕ) : Prop :=
  blockEnd m t - blockWidth j ≤ n ∧ n < blockEnd m t

/-- The selected terminating, zero-tailed expansion of `16^j x_m`. -/
def scaledExpansion (m j n : ℕ) : Fin 10 := by
  classical
  exact if h : ∃ t : ℕ, 1 ≤ t ∧ InBlockInterval m j t n then
    imageExpansion j (reciprocalPoint (blockEnd m (Classical.choose h) - 1)) n
  else 0

theorem blockWidth_le_spacing {m j : ℕ} (hj : j ≤ radius m) :
    blockWidth j ≤ spacing m := by
  simp only [blockWidth, spacing]
  omega

theorem blockWidth_le_blockEnd {m j t : ℕ} (hj : j ≤ radius m) (ht : 1 ≤ t) :
    blockWidth j ≤ blockEnd m t := by
  calc
    blockWidth j ≤ spacing m := blockWidth_le_spacing hj
    _ ≤ spacing m * t ^ 2 := by
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos ht)
    _ = blockEnd m t := rfl

theorem blockEnd_add_spacing_le {m s t : ℕ} (hst : s < t) :
    blockEnd m s + spacing m ≤ blockEnd m t := by
  simp only [blockEnd]
  have hsquares : s ^ 2 + 1 ≤ t ^ 2 := by
    have := Nat.pow_lt_pow_left hst (by omega : 2 ≠ 0)
    omega
  calc
    spacing m * s ^ 2 + spacing m = spacing m * (s ^ 2 + 1) := by ring
    _ ≤ spacing m * t ^ 2 := Nat.mul_le_mul_left _ hsquares

/-- Reserved block intervals are pairwise disjoint throughout the inclusive
range `j ≤ R_m`; this is the carry-free spacing statement. -/
theorem blockIntervals_disjoint {m j s t n : ℕ} (hj : j ≤ radius m)
    (hs : InBlockInterval m j s n) (ht : InBlockInterval m j t n) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hsep := blockEnd_add_spacing_le (m := m) hst
    have hw := blockWidth_le_spacing hj
    have hleft : blockEnd m s ≤ blockEnd m t - blockWidth j := by
      apply Nat.le_sub_of_add_le
      exact (Nat.add_le_add_left hw _).trans hsep
    exact (not_lt_of_ge (hleft.trans ht.1)) hs.2
  · have hsep := blockEnd_add_spacing_le (m := m) hts
    have hw := blockWidth_le_spacing hj
    have hleft : blockEnd m t ≤ blockEnd m s - blockWidth j := by
      apply Nat.le_sub_of_add_le
      exact (Nat.add_le_add_left hw _).trans hsep
    exact (not_lt_of_ge (hleft.trans hs.1)) ht.2

theorem scaledExpansion_eq_singleBlock
    {m j t n : ℕ} (hj : j ≤ radius m) (ht : 1 ≤ t)
    (hn : InBlockInterval m j t n) :
    scaledExpansion m j n =
      imageExpansion j (reciprocalPoint (blockEnd m t - 1)) n := by
  classical
  rw [scaledExpansion]
  split
  next h =>
    have hu := (Classical.choose_spec h).2
    have hut : Classical.choose h = t := blockIntervals_disjoint hj hu hn
    rw [hut]
  next h => exact (h ⟨t, ht, hn⟩).elim

theorem scaledExpansion_eq_zero_of_no_interval
    {m j n : ℕ} (hn : ∀ t : ℕ, 1 ≤ t → ¬ InBlockInterval m j t n) :
    scaledExpansion m j n = 0 := by
  rw [scaledExpansion, dif_neg]
  push Not
  exact hn

theorem singleBlock_eq_zero_before
    {m j t n : ℕ} (hj : j ≤ radius m) (ht : 1 ≤ t)
    (hn : n < blockEnd m t - blockWidth j) :
    imageExpansion j (reciprocalPoint (blockEnd m t - 1)) n = 0 := by
  have hwidth := blockWidth_le_blockEnd hj ht
  have hdeep : (n + 1) + 2 * j + 1 ≤ blockEnd m t - 1 := by
    simp only [blockWidth] at hn hwidth ⊢
    omega
  have hp := imagePrefix_reciprocal_eq_zero_of_deep
    (n + 1) j (blockEnd m t - 1) hdeep
  have hdigit := congrFun hp (⟨n, by omega⟩ : Fin (n + 1))
  exact hdigit

theorem singleBlock_eq_zero_after
    {m j t n : ℕ} (ht : 1 ≤ t) (hn : blockEnd m t ≤ n) :
    imageExpansion j (reciprocalPoint (blockEnd m t - 1)) n = 0 := by
  apply imageExpansion_reciprocal_zero_tail
  have hend := blockEnd_pos m t ht
  omega

theorem sixteen_pow_lt_ten_pow_blockEnd
    {m j t : ℕ} (hj : j ≤ radius m) (ht : 1 ≤ t) :
    (16 : ℝ) ^ j < (10 : ℝ) ^ blockEnd m t := by
  have hnat := sixteen_pow_le_ten_pow_two_mul j
  have hexp : 2 * j < blockEnd m t := by
    have hw := blockWidth_le_blockEnd hj ht
    simp only [blockWidth] at hw
    omega
  calc
    (16 : ℝ) ^ j ≤ (10 : ℝ) ^ (2 * j) := by exact_mod_cast hnat
    _ < (10 : ℝ) ^ blockEnd m t := by
      rw [pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)]
      exact_mod_cast hexp

/-- One reserved copy evaluates exactly to `16^j / 10^(D_m t²)`, using the
terminating floor-based expansion selected by T57. -/
theorem singleBlock_ofDigits
    {m j t : ℕ} (hj : j ≤ radius m) (ht : 1 ≤ t) :
    Real.ofDigits (imageExpansion j (reciprocalPoint (blockEnd m t - 1))) =
      (16 : ℝ) ^ j / (10 : ℝ) ^ blockEnd m t := by
  rw [imageExpansion, Real.ofDigits_digits (by norm_num)]
  · rw [unitCoordinate_circleMul_reciprocalPoint]
    have hpos : 0 ≤ (16 : ℝ) ^ j / (10 : ℝ) ^ blockEnd m t := by positivity
    have hlt : (16 : ℝ) ^ j / (10 : ℝ) ^ blockEnd m t < 1 := by
      rw [div_lt_one (by positivity)]
      exact sixteen_pow_lt_ten_pow_blockEnd hj ht
    rw [show blockEnd m t - 1 + 1 = blockEnd m t by
      exact Nat.sub_add_cancel (blockEnd_pos m t ht)]
    exact Int.fract_eq_self.mpr ⟨hpos, hlt⟩
  · exact ⟨unitCoordinate_nonneg _, unitCoordinate_lt_one _⟩

/-- The contribution of one reserved block at one global digit position. -/
def reservedTerm (m j : ℕ) (t : {t : ℕ // 1 ≤ t}) (n : ℕ) : ℝ := by
  classical
  exact if InBlockInterval m j t.val n then
      Real.ofDigitsTerm
        (imageExpansion j (reciprocalPoint (blockEnd m t.val - 1))) n
    else 0

theorem reservedTerm_eq_singleTerm
    {m j : ℕ} (hj : j ≤ radius m) (t : {t : ℕ // 1 ≤ t}) (n : ℕ) :
    reservedTerm m j t n =
      Real.ofDigitsTerm
        (imageExpansion j (reciprocalPoint (blockEnd m t.val - 1))) n := by
  rw [reservedTerm]
  split
  · rfl
  next hn =>
    have hout : n < blockEnd m t.val - blockWidth j ∨ blockEnd m t.val ≤ n := by
      unfold InBlockInterval at hn
      omega
    rcases hout with hbefore | hafter
    · rw [Real.ofDigitsTerm, singleBlock_eq_zero_before hj t.property hbefore]
      simp [Real.ofDigitsTerm]
    · rw [Real.ofDigitsTerm, singleBlock_eq_zero_after t.property hafter]
      simp [Real.ofDigitsTerm]

theorem reservedTerm_summable
    {m j : ℕ} (hj : j ≤ radius m) (t : {t : ℕ // 1 ≤ t}) :
    Summable (reservedTerm m j t) := by
  apply (Real.summable_ofDigitsTerm : Summable
    (Real.ofDigitsTerm
      (imageExpansion j (reciprocalPoint (blockEnd m t.val - 1))))).congr
  intro n
  exact (reservedTerm_eq_singleTerm hj t n).symm

theorem reservedTerm_tsum
    {m j : ℕ} (hj : j ≤ radius m) (t : {t : ℕ // 1 ≤ t}) :
    (∑' n : ℕ, reservedTerm m j t n) =
      (16 : ℝ) ^ j / (10 : ℝ) ^ blockEnd m t.val := by
  apply (tsum_congr (fun n => reservedTerm_eq_singleTerm hj t n)).trans
  exact singleBlock_ofDigits hj t.property

theorem summable_squareTerms (m : ℕ) :
    Summable (fun t : {t : ℕ // 1 ≤ t} =>
      (10 : ℝ) ^ (-(blockEnd m t.val : ℤ))) := by
  have hgeom : Summable (fun n : ℕ => (10 : ℝ) ^ (-(n : ℤ))) := by
    simpa [zpow_neg, zpow_natCast] using
      (summable_geometric_of_lt_one (by positivity : 0 ≤ (10 : ℝ)⁻¹) (by norm_num))
  exact hgeom.comp_injective
    (fun s t h => Subtype.ext ((blockEnd_injective m) h))

theorem summable_reservedTerms
    {m j : ℕ} (hj : j ≤ radius m) :
    Summable (Function.uncurry (reservedTerm m j)) := by
  rw [summable_prod_of_nonneg (fun p => by
    dsimp only [Function.uncurry, reservedTerm]
    split
    · exact Real.ofDigitsTerm_nonneg
    · exact le_rfl)]
  refine ⟨fun t => reservedTerm_summable hj t, ?_⟩
  have hs := (summable_squareTerms m).mul_left ((16 : ℝ) ^ j)
  apply hs.congr
  intro t
  change (16 : ℝ) ^ j * (10 : ℝ) ^ (-(blockEnd m t.val : ℤ)) =
    ∑' n : ℕ, reservedTerm m j t n
  rw [reservedTerm_tsum hj t]
  simp [div_eq_mul_inv, zpow_neg, zpow_natCast]

theorem scaledTerm_eq_tsum_reserved
    {m j n : ℕ} (hj : j ≤ radius m) :
    Real.ofDigitsTerm (scaledExpansion m j) n =
      ∑' t : {t : ℕ // 1 ≤ t}, reservedTerm m j t n := by
  classical
  by_cases h : ∃ t : ℕ, 1 ≤ t ∧ InBlockInterval m j t n
  · let t : {t : ℕ // 1 ≤ t} := ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    have ht : InBlockInterval m j t.val n := (Classical.choose_spec h).2
    rw [tsum_eq_single t]
    · rw [reservedTerm, if_pos ht]
      unfold Real.ofDigitsTerm
      rw [scaledExpansion_eq_singleBlock hj t.property ht]
    · intro s hst
      rw [reservedTerm, if_neg]
      intro hs
      exact hst (Subtype.ext (blockIntervals_disjoint hj hs ht))
  · have hdigit : scaledExpansion m j n = 0 := by
      apply scaledExpansion_eq_zero_of_no_interval
      intro t ht hinterval
      exact h ⟨t, ht, hinterval⟩
    rw [Real.ofDigitsTerm, hdigit]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul]
    have hall : ∀ t : {t : ℕ // 1 ≤ t}, reservedTerm m j t n = 0 := by
      intro t
      rw [reservedTerm, if_neg]
      exact fun ht => h ⟨t.val, t.property, ht⟩
    simp only [hall, tsum_zero]

/-- The explicit carry-free expansion evaluates to `16^j x_m`. -/
theorem scaledExpansion_ofDigits
    {m j : ℕ} (hj : j ≤ radius m) :
    Real.ofDigits (scaledExpansion m j) = (16 : ℝ) ^ j * squareReal m := by
  rw [Real.ofDigits]
  calc
    (∑' n : ℕ, Real.ofDigitsTerm (scaledExpansion m j) n) =
        ∑' n : ℕ, ∑' t : {t : ℕ // 1 ≤ t}, reservedTerm m j t n := by
          apply tsum_congr
          intro n
          exact scaledTerm_eq_tsum_reserved hj
    _ = ∑' t : {t : ℕ // 1 ≤ t}, ∑' n : ℕ, reservedTerm m j t n :=
      (summable_reservedTerms hj).tsum_comm
    _ = ∑' t : {t : ℕ // 1 ≤ t},
        ((16 : ℝ) ^ j * (10 : ℝ) ^ (-(blockEnd m t.val : ℤ))) := by
          apply tsum_congr
          intro t
          rw [reservedTerm_tsum hj t]
          simp [div_eq_mul_inv, zpow_neg, zpow_natCast]
    _ = (16 : ℝ) ^ j * squareReal m := by
      rw [squareReal, (summable_squareTerms m).tsum_mul_left]

theorem circleMul_powTen_reciprocalPoint
    {E start : ℕ} (hstart : start < E) :
    circleMul (10 ^ start) (reciprocalPoint (E - 1)) =
      reciprocalPoint (E - start - 1) := by
  have hE : E - 1 + 1 = E := by omega
  have hEs : E - start - 1 + 1 = E - start := by omega
  change (10 ^ start) •
      ((((1 : ℝ) / (10 : ℝ) ^ (E - 1 + 1) : ℝ) : UnitAddCircle)) =
    (((1 : ℝ) / (10 : ℝ) ^ (E - start - 1 + 1) : ℝ) : UnitAddCircle)
  rw [hE, hEs, ← AddCircle.coe_nsmul]
  simp only [nsmul_eq_mul]
  congr 1
  push_cast
  have hdecomp : E = (E - start) + start := by omega
  rw [hdecomp, pow_add]
  field_simp
  congr 1
  omega

theorem imageExpansion_shift_reciprocalPoint
    {j E start : ℕ} (hstart : start < E) :
    ∀ i : ℕ,
      imageExpansion j (reciprocalPoint (E - 1)) (start + i) =
        imageExpansion j (reciprocalPoint (E - start - 1)) i := by
  intro i
  have hshift := congrFun
    (imageExpansion_streamShift j start (reciprocalPoint (E - 1))) i
  rw [circleMul_powTen_reciprocalPoint hstart] at hshift
  simpa [streamShift, Nat.add_comm] using hshift

/-- A length-`m` window meets a reserved copy. -/
def WindowMeetsBlock (m j start t : ℕ) : Prop :=
  ∃ i : Fin m, InBlockInterval m j t (start + i.val)

theorem m_add_blockWidth_le_spacing
    {m j : ℕ} (hj : j ≤ radius m) :
    m + blockWidth j ≤ spacing m := by
  simp only [blockWidth, spacing]
  omega

theorem window_meets_unique
    {m j start s t : ℕ} (hj : j ≤ radius m)
    (hs : WindowMeetsBlock m j start s)
    (ht : WindowMeetsBlock m j start t) : s = t := by
  rcases hs with ⟨i, hi⟩
  rcases ht with ⟨k, hk⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hsep := blockEnd_add_spacing_le (m := m) hst
    have hmw := m_add_blockWidth_le_spacing hj
    have hfar : blockEnd m s + m ≤ blockEnd m t - blockWidth j := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_assoc] using (Nat.add_le_add_left hmw (blockEnd m s)).trans hsep
    have hki : start + i.val < blockEnd m s := hi.2
    have htk : blockEnd m t - blockWidth j ≤ start + k.val := hk.1
    omega
  · have hsep := blockEnd_add_spacing_le (m := m) hts
    have hmw := m_add_blockWidth_le_spacing hj
    have hfar : blockEnd m t + m ≤ blockEnd m s - blockWidth j := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_assoc] using (Nat.add_le_add_left hmw (blockEnd m t)).trans hsep
    have hkk : start + k.val < blockEnd m t := hk.2
    have hsi : blockEnd m s - blockWidth j ≤ start + i.val := hi.1
    omega

theorem scaledExpansion_window_eq_singleBlock
    {m j start t : ℕ} (hj : j ≤ radius m)
    (ht : 1 ≤ t) (hmeet : WindowMeetsBlock m j start t) :
    ∀ i : Fin m,
      scaledExpansion m j (start + i.val) =
        imageExpansion j (reciprocalPoint (blockEnd m t - 1)) (start + i.val) := by
  intro i
  by_cases hi : ∃ u : ℕ, 1 ≤ u ∧ InBlockInterval m j u (start + i.val)
  · obtain ⟨u, hu, hui⟩ := hi
    have hut : u = t := window_meets_unique hj ⟨i, hui⟩ hmeet
    subst u
    exact scaledExpansion_eq_singleBlock hj ht hui
  · have hscaled : scaledExpansion m j (start + i.val) = 0 := by
      apply scaledExpansion_eq_zero_of_no_interval
      intro u hu hui
      exact hi ⟨u, hu, hui⟩
    rw [hscaled]
    have hout : start + i.val < blockEnd m t - blockWidth j ∨
        blockEnd m t ≤ start + i.val := by
      by_contra hinside
      push Not at hinside
      exact hi ⟨t, ht, hinside⟩
    rcases hout with hbefore | hafter
    · exact (singleBlock_eq_zero_before hj ht hbefore).symm
    · exact (singleBlock_eq_zero_after ht hafter).symm

/-- Every length-`m` factor of every inclusive scaled expansion is one of
T57's explicitly counted prefixes. A factor either is all zero or meets one
and only one reserved copy. -/
theorem windowVector_mem_observedPrefixes
    {m j start : ℕ} (hm : 2 ≤ m) (hj : j ≤ radius m) :
    (fun i : Fin m => scaledExpansion m j (start + i.val)) ∈
      observedPrefixes m (radius m) := by
  by_cases hmeet : ∃ t : ℕ, 1 ≤ t ∧ WindowMeetsBlock m j start t
  · let t : ℕ := Classical.choose hmeet
    have ht : 1 ≤ t := (Classical.choose_spec hmeet).1
    have htm := (Classical.choose_spec hmeet).2
    rcases htm with ⟨i, hi⟩
    have hstart : start < blockEnd m t :=
      lt_of_le_of_lt (Nat.le_add_right start i.val) hi.2
    let k := blockEnd m t - start - 1
    have hkEnd : k + 1 = blockEnd m t - start := by dsimp [k]; omega
    have hklt : k < m + 2 * j + 2 := by
      dsimp [k, t] at hstart hi ⊢
      simp only [InBlockInterval, blockWidth] at hi
      have hir := i.isLt
      omega
    have hvec : (fun r : Fin m => scaledExpansion m j (start + r.val)) =
        imagePrefix m j (reciprocalPoint k) := by
      funext r
      rw [scaledExpansion_window_eq_singleBlock hj ht ⟨i, hi⟩ r]
      exact imageExpansion_shift_reciprocalPoint hstart r.val
    rw [hvec]
    exact imagePrefix_mem_observedPrefixes m (radius m) j hj
      (reciprocalPoint k) (Set.mem_insert_of_mem 0 (Set.mem_range_self k))
  · let k := m + 2 * j + 1
    have hzero : (fun i : Fin m => scaledExpansion m j (start + i.val)) =
        fun _ => 0 := by
      funext i
      apply scaledExpansion_eq_zero_of_no_interval
      intro t ht hi
      exact hmeet ⟨t, ht, ⟨i, hi⟩⟩
    have hprefix : imagePrefix m j (reciprocalPoint k) = fun _ => 0 := by
      apply imagePrefix_reciprocal_eq_zero_of_deep
      simp [k]
    rw [hzero, ← hprefix]
    exact imagePrefix_mem_observedPrefixes m (radius m) j hj
      (reciprocalPoint k) (Set.mem_insert_of_mem 0 (Set.mem_range_self k))

theorem factor_zero_or_meets_unique_block
    {m j start : ℕ} (hj : j ≤ radius m) :
    (fun i : Fin m => scaledExpansion m j (start + i.val)) = (fun _ => 0) ∨
      ∃! t : ℕ, 1 ≤ t ∧ WindowMeetsBlock m j start t := by
  by_cases h : ∃ t : ℕ, 1 ≤ t ∧ WindowMeetsBlock m j start t
  · right
    obtain ⟨t, ht, hmeet⟩ := h
    refine ⟨t, ⟨ht, hmeet⟩, ?_⟩
    intro s hs
    exact window_meets_unique hj hs.2 hmeet
  · left
    funext i
    apply scaledExpansion_eq_zero_of_no_interval
    intro t ht hi
    exact h ⟨t, ht, ⟨i, hi⟩⟩

theorem scaledExpansion_avoids_omittedWord
    {m j : ℕ} (hm : 2 ≤ m) (hj : j ≤ radius m) :
    AvoidsWord (omittedWordAt m) (scaledExpansion m j) := by
  intro start hocc
  apply omittedVector_not_mem m hm
  have hmem := windowVector_mem_observedPrefixes hm hj (start := start)
  have heq : (fun i : Fin m => scaledExpansion m j (start + i.val)) =
      omittedVector m := by
    funext i
    have hi : i.val < (omittedWordAt m).length := by simp
    have hdigit := hocc ⟨i.val, hi⟩
    simpa [omittedWordAt, omittedWord, List.get_eq_getElem] using hdigit
  rwa [heq] at hmem

/-- The circle point represented by the requested square sum. -/
def squarePoint (m : ℕ) : UnitAddCircle := (squareReal m : UnitAddCircle)

theorem scaledExpansion_circleValue
    {m j : ℕ} (hj : j ≤ radius m) :
    circleValue (scaledExpansion m j) = circleMul (16 ^ j) (squarePoint m) := by
  rw [circleValue, scaledExpansion_ofDigits hj]
  change (((16 : ℝ) ^ j * squareReal m : ℝ) : UnitAddCircle) =
    (16 ^ j) • ((squareReal m : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_nsmul]
  congr 1
  push_cast
  simp [nsmul_eq_mul]

/-- The requested irrational point belongs to the endpoint-safe core at the
full exponential depth. Shifts use T44's existential endpoint convention. -/
theorem squarePoint_mem_Core
    {m : ℕ} (hm : 2 ≤ m) :
    squarePoint m ∈ Core (omittedWordAt m) (radius m) := by
  intro n j hj
  let a : DecimalStream := streamShift n (scaledExpansion m j)
  refine ⟨a, avoidsWord_streamShift (omittedWordAt m) (scaledExpansion m j) n
    (scaledExpansion_avoids_omittedWord hm hj), ?_⟩
  rw [circleValue_streamShift, scaledExpansion_circleValue hj]
  exact circleMul_commute (10 ^ n) (16 ^ j) (squarePoint m)

/-- Irrationality also excludes rational representatives on the circle; adding
an integer cannot turn an irrational real into a rational one. -/
theorem squarePoint_not_rational (m : ℕ) :
    ¬ IsRationalCirclePoint (squarePoint m) := by
  rintro ⟨q, hq⟩
  have hzero : (((squareReal m - (q : ℝ) : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    change squarePoint m - (((q : ℝ) : UnitAddCircle)) = 0
    rw [hq]
    simp
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero
  have hzreal : (z : ℝ) = squareReal m - (q : ℝ) := by
    simpa [zsmul_eq_mul] using hz
  apply squareReal_irrational m
  refine ⟨q + (z : ℚ), ?_⟩
  push_cast
  linarith

/-- T72's exact certificate fails at every inclusive depth `r ≤ 2^m`. -/
theorem projectedPhase_fails_at_every_depth
    {m : ℕ} (hm : 2 ≤ m) (r : ℕ) (hr : r ≤ radius m) :
    ¬ Graph.GlobalPrimitivePhaseCriterion
      (carryKMPGraph (omittedWordAt m) (by
        intro hnil
        have hlen := congrArg List.length hnil
        simp at hlen
        omega) r)
      coordinateZeroProjection := by
  intro hgraph
  have hwne : omittedWordAt m ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  have hrat := endpointComplete_globalProjectedPhase_implies_rationalCore
    (omittedWordAt m) hwne r hgraph
  apply squarePoint_not_rational m
  exact hrat (squarePoint m)
    (core_antitone_radius (omittedWordAt m) hr (squarePoint_mem_Core hm))

/-- The exact T57 count retained by the square construction: the indexing
family has the displayed cardinality, while distinct observed factors may
collide and therefore satisfy an upper bound. -/
theorem exact_factor_index_count (m : ℕ) (hm : 2 ≤ m) :
    let R := radius m
    Fintype.card (PrefixIndex m R) = (R + 1) * (m + R + 2) ∧
      (observedPrefixes m R).card ≤ (R + 1) * (m + R + 2) ∧
      (R + 1) * (m + R + 2) < 10 ^ m ∧
      (omittedWordAt m).length = m := by
  dsimp only
  have hcard := prefixIndex_card m (radius m)
  rw [inclusive_prefix_count_closed_form] at hcard
  have hobs := observedPrefixes_card_le_prefix_count m (radius m)
  rw [inclusive_prefix_count_closed_form] at hobs
  have hlt := inclusive_prefix_count_lt_ten_pow m hm
  rw [inclusive_prefix_count_closed_form] at hlt
  simpa only [radius] using
    And.intro hcard (And.intro hobs (And.intro hlt (omittedWordAt_length m)))

/-- Expanded counterexample quantifiers: after any nonnegative affine bound is
fixed, one exact length-`m` omitted word defeats every projected certificate
at every depth allowed by that bound. -/
theorem not_uniformLinearProjectedPhaseHypothesis_quantifiers :
    ∀ L C : ℝ, 0 ≤ L →
      ∃ m : ℕ, ∃ hm : 2 ≤ m, ∃ hw : omittedWordAt m ≠ [],
        ∀ r : ℕ, (r : ℝ) ≤ L * ((omittedWordAt m).length : ℝ) + C →
          ¬ Graph.GlobalPrimitivePhaseCriterion
            (carryKMPGraph (omittedWordAt m) hw r) coordinateZeroProjection := by
  intro L C hL
  obtain ⟨m, hm, hbound⟩ := exists_two_pow_dominates_affine L C hL
  have hw : omittedWordAt m ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  refine ⟨m, hm, hw, ?_⟩
  intro r hr
  have hrRreal : (r : ℝ) ≤ (radius m : ℕ) := by
    calc
      (r : ℝ) ≤ L * ((omittedWordAt m).length : ℝ) + C := hr
      _ = L * (m : ℝ) + C := by rw [omittedWordAt_length]
      _ ≤ (radius m : ℕ) := by simpa [radius] using hbound
  have hrR : r ≤ radius m := by exact_mod_cast hrRreal
  exact projectedPhase_fails_at_every_depth hm r hrR

/-- Literal negation of T72's exact existential affine-uniform hypothesis. -/
theorem not_uniformLinearProjectedPhaseHypothesis :
    ¬ UniformLinearProjectedPhaseHypothesis := by
  rintro ⟨L, C, hL, hgraph⟩
  obtain ⟨m, hm, hw, hfail⟩ :=
    not_uniformLinearProjectedPhaseHypothesis_quantifiers L C hL
  obtain ⟨r, hr, hcert⟩ := hgraph (omittedWordAt m) hw
  exact hfail r hr hcert

theorem radius_strictMono : StrictMono radius := by
  intro m n hmn
  simp only [radius]
  exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 hmn

theorem spacing_strictMono : StrictMono spacing := by
  intro m n hmn
  have hr := radius_strictMono hmn
  simp only [spacing]
  omega

theorem blockEnd_strictMono_parameter
    {m n : ℕ} (hmn : m < n) (t : {t : ℕ // 1 ≤ t}) :
    blockEnd m t.val < blockEnd n t.val := by
  simp only [blockEnd]
  exact Nat.mul_lt_mul_of_pos_right (spacing_strictMono hmn) (Nat.pow_pos t.property)

/-- The real witnesses genuinely vary with `m`: increasing `m` moves every
square block farther right and strictly decreases the positive series. -/
theorem squareReal_strictAnti {m n : ℕ} (hmn : m < n) :
    squareReal n < squareReal m := by
  rw [squareReal, squareReal]
  have hterm (t : {t : ℕ // 1 ≤ t}) :
      (10 : ℝ) ^ (-(blockEnd n t.val : ℤ)) <
        (10 : ℝ) ^ (-(blockEnd m t.val : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by
      rw [pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)]
      exact_mod_cast blockEnd_strictMono_parameter hmn t)
  let t : {t : ℕ // 1 ≤ t} := ⟨1, by omega⟩
  exact Summable.tsum_lt_tsum (i := t) (fun s => (hterm s).le) (hterm t)
    (summable_squareTerms n) (summable_squareTerms m)

theorem omittedWordAt_ne_of_ne {m n : ℕ} (hmn : m ≠ n) :
    omittedWordAt m ≠ omittedWordAt n := by
  intro h
  have hlen := congrArg List.length h
  apply hmn
  simpa using hlen

/-- Both components of the witness family are pairwise distinct. -/
theorem witnesses_vary_with_m {m n : ℕ} (hmn : m ≠ n) :
    omittedWordAt m ≠ omittedWordAt n ∧ squareReal m ≠ squareReal n := by
  refine ⟨omittedWordAt_ne_of_ne hmn, ?_⟩
  intro heq
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (ne_of_lt (squareReal_strictAnti hlt)) heq.symm
  · exact (ne_of_lt (squareReal_strictAnti hgt)) heq

theorem omittedWordAt_nonempty {m : ℕ} (hm : 2 ≤ m) : omittedWordAt m ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp at hlen
  omega

/-- One acceptance-facing theorem exposing the complete construction at a
fixed `m`: exact parameters and sum, block positions, disjoint carry-free
copies, terminating endpoint convention, factor count and omission, exact word
length, irrationality, Core membership, and every failed depth. -/
theorem squareSparse_obstruction_certificate (m : ℕ) (hm : 2 ≤ m) :
    let R := radius m
    let D := spacing m
    R = 2 ^ m ∧
      D = 10 * (R + m + 1) ∧
      squareReal m =
        ∑' t : {t : ℕ // 1 ≤ t}, (10 : ℝ) ^ (-(D * t.val ^ 2 : ℕ) : ℤ) ∧
      (∀ j : ℕ, j ≤ R →
        Real.ofDigits (scaledExpansion m j) = (16 : ℝ) ^ j * squareReal m ∧
        (∀ t : ℕ, 1 ≤ t →
          (∀ n : ℕ, InBlockInterval m j t n →
            scaledExpansion m j n =
              imageExpansion j (reciprocalPoint (D * t ^ 2 - 1)) n) ∧
          (∀ n : ℕ, D * t ^ 2 ≤ n →
            imageExpansion j (reciprocalPoint (D * t ^ 2 - 1)) n = 0)) ∧
        (∀ s t n : ℕ, InBlockInterval m j s n →
          InBlockInterval m j t n → s = t) ∧
        (∀ start : ℕ,
          (fun i : Fin m => scaledExpansion m j (start + i.val)) = (fun _ => 0) ∨
            ∃! t : ℕ, 1 ≤ t ∧ WindowMeetsBlock m j start t) ∧
        ∀ start : ℕ,
          (fun i : Fin m => scaledExpansion m j (start + i.val)) ∈
            observedPrefixes m R) ∧
      Fintype.card (PrefixIndex m R) = (R + 1) * (m + R + 2) ∧
      (observedPrefixes m R).card ≤ (R + 1) * (m + R + 2) ∧
      (R + 1) * (m + R + 2) < 10 ^ m ∧
      (omittedWordAt m).length = m ∧
      Irrational (squareReal m) ∧
      squarePoint m ∈ Core (omittedWordAt m) R ∧
      ∀ r : ℕ, r ≤ R →
        ¬ Graph.GlobalPrimitivePhaseCriterion
          (carryKMPGraph (omittedWordAt m) (omittedWordAt_nonempty hm) r)
          coordinateZeroProjection := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · intro j hj
    refine ⟨scaledExpansion_ofDigits hj, ?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨?_, ?_⟩
      · intro n hn
        exact scaledExpansion_eq_singleBlock hj ht hn
      · intro n hn
        exact singleBlock_eq_zero_after ht hn
    · intro s t n hs ht
      exact blockIntervals_disjoint hj hs ht
    · intro start
      exact factor_zero_or_meets_unique_block hj
    · intro start
      exact windowVector_mem_observedPrefixes hm hj
  · obtain ⟨hcard, hobs, hlt, hlen⟩ := exact_factor_index_count m hm
    refine ⟨hcard, hobs, hlt, hlen, squareReal_irrational m,
      squarePoint_mem_Core hm, ?_⟩
    intro r hr
    exact projectedPhase_fails_at_every_depth hm r hr

structure ScopeStatus where
  witnessesDependOnM : Bool
  refutesT72UniformLinearProjectedPhase : Bool
  provesC6 : Bool
  disprovesC6 : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  concernsPi : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  witnessesDependOnM := true
  refutesT72UniformLinearProjectedPhase := true
  provesC6 := false
  disprovesC6 := false
  provesC1 := false
  disprovesC1 := false
  concernsPi := false

/-- Formal scope marker: the varying sibling witnesses refute only T72's
universal sufficient certificate. They prove or disprove nothing about C6,
C1, or pi. -/
theorem exact_scope :
    scopeStatus.witnessesDependOnM = true ∧
      scopeStatus.refutesT72UniformLinearProjectedPhase = true ∧
      scopeStatus.provesC6 = false ∧
      scopeStatus.disprovesC6 = false ∧
      scopeStatus.provesC1 = false ∧
      scopeStatus.disprovesC1 = false ∧
      scopeStatus.concernsPi = false := by
  norm_num [scopeStatus]

end DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction

#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.squareReal_eq_ofDigits
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.squareReal_irrational
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.blockIntervals_disjoint
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.scaledExpansion_ofDigits
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.factor_zero_or_meets_unique_block
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.windowVector_mem_observedPrefixes
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.squarePoint_mem_Core
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.projectedPhase_fails_at_every_depth
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.exact_factor_index_count
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.not_uniformLinearProjectedPhaseHypothesis_quantifiers
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.not_uniformLinearProjectedPhaseHypothesis
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.witnesses_vary_with_m
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.squareSparse_obstruction_certificate
#print axioms DecimalFactorEntropy.T78SquareSparseProjectedPhaseObstruction.exact_scope
