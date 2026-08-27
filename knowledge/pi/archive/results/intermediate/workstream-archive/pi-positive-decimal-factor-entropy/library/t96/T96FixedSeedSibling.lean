import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore

/-!
# T96: an explicit fixed-seed sibling theorem

The only accumulated research module imported here is kernel-checked T44.
T57 and T78 are comparisons in the prose companion, not proof dependencies.
-/

noncomputable section

open Filter Finset Set Topology

namespace DecimalFactorEntropy.T96FixedSeedSiblingExplicit

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorComplexity.NormalOrbitNearReturns

/-- One-based position of sparse digit number `q`, with `q = 0` corresponding
to the summand `10^(-4)`. -/
def sparseEnd (q : ℕ) : ℕ := 4 ^ (q + 1)

/-- Zero-based position of sparse digit number `q`. -/
def sparsePosition (q : ℕ) : ℕ := sparseEnd q - 1

/-- Decimal stream having a one exactly at positions `4^(q+1)-1`. -/
def xStarDigits (n : ℕ) : Fin 10 := by
  classical
  exact if n ∈ Set.range sparsePosition then 1 else 0

/-- The explicit real `x_*`, defined by its decimal expansion. -/
def xStar : ℝ := Real.ofDigits xStarDigits

/-- The corresponding point of the circle. -/
def xStarPoint : UnitAddCircle := (xStar : UnitAddCircle)

/-- Closure of the forward decimal orbit of the explicit seed. -/
def xStarOrbitClosure : Set UnitAddCircle :=
  closure (Set.range fun n : ℕ => circleMul (10 ^ n) xStarPoint)

theorem sparseEnd_strictMono : StrictMono sparseEnd := by
  intro a b hab
  simp only [sparseEnd]
  exact Nat.pow_lt_pow_right (by omega : 1 < 4) (by omega)

theorem sparsePosition_succ (q : ℕ) :
    sparsePosition q + 1 = sparseEnd q := by
  rw [sparsePosition]
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by simp [sparseEnd]))

theorem sparsePosition_injective : Function.Injective sparsePosition := by
  intro a b hab
  apply sparseEnd_strictMono.injective
  rw [← sparsePosition_succ a, ← sparsePosition_succ b, hab]

@[simp] theorem xStarDigits_sparsePosition (q : ℕ) :
    xStarDigits (sparsePosition q) = 1 := by
  simp [xStarDigits]

theorem xStarDigits_eq_zero_of_not_mem (n : ℕ)
    (hn : n ∉ Set.range sparsePosition) : xStarDigits n = 0 := by
  simp [xStarDigits, hn]

theorem ofDigitsTerm_xStarDigits_sparsePosition (q : ℕ) :
    Real.ofDigitsTerm xStarDigits (sparsePosition q) =
      (10 : ℝ) ^ (-(sparseEnd q : ℤ)) := by
  rw [Real.ofDigitsTerm, xStarDigits_sparsePosition]
  simp only [Fin.val_one, Nat.cast_one, one_mul]
  rw [sparsePosition_succ]
  simp [zpow_neg, zpow_natCast]

theorem ofDigitsTerm_xStarDigits_eq_zero_of_not_mem (n : ℕ)
    (hn : n ∉ Set.range sparsePosition) :
    Real.ofDigitsTerm xStarDigits n = 0 := by
  simp [Real.ofDigitsTerm, xStarDigits, hn]

/-- Exact identification with the series in the agenda statement:
`q = 0` here is the statement's `q = 1`. -/
theorem xStar_eq_series :
    xStar = ∑' q : ℕ, (10 : ℝ) ^ (-(4 ^ (q + 1) : ℕ) : ℤ) := by
  let S : Set ℕ := Set.range sparsePosition
  let Sc : Set ℕ := {n | n ∉ S}
  let f : ℕ → ℝ := Real.ofDigitsTerm xStarDigits
  have hf : Summable f := Real.summable_ofDigitsTerm
  have hcompl : (∑' n : Sc, f n.val) = 0 := by
    calc
      (∑' n : Sc, f n.val) = ∑' _n : Sc, (0 : ℝ) := by
        apply tsum_congr
        intro n
        exact ofDigitsTerm_xStarDigits_eq_zero_of_not_mem n.val n.property
      _ = 0 := tsum_zero
  have hsub : (∑' n : S, f n.val) = ∑' n : ℕ, f n := by
    have hsplit := hf.tsum_subtype_add_tsum_subtype_compl S
    have hSc : Sᶜ = Sc := by ext n; simp [Sc]
    rw [hSc, hcompl, add_zero] at hsplit
    exact hsplit
  let e := Equiv.ofInjective sparsePosition sparsePosition_injective
  have hequiv := e.tsum_eq (fun n : S => f n.val)
  rw [xStar, Real.ofDigits]
  rw [← hsub, ← hequiv]
  apply tsum_congr
  intro q
  simpa [e, S, f, sparseEnd] using
    ofDigitsTerm_xStarDigits_sparsePosition q

/-- Number of zero digits strictly between sparse digits `q` and `q+1`. -/
def zeroGap (q : ℕ) : ℕ := sparseEnd (q + 1) - sparseEnd q - 1

theorem sparseEnd_succ (q : ℕ) : sparseEnd (q + 1) = 4 * sparseEnd q := by
  simp only [sparseEnd]
  rw [show q + 1 + 1 = (q + 1) + 1 by omega, pow_succ,
    show q + 1 = q + 1 by rfl, pow_succ]
  ring

theorem zeroGap_eq (q : ℕ) : zeroGap q = 3 * sparseEnd q - 1 := by
  rw [zeroGap, sparseEnd_succ]
  have hpos : 0 < sparseEnd q := by simp [sparseEnd]
  omega

theorem xStarDigits_shift_eq_zero_before_gap
    (q i : ℕ) (hi : i < zeroGap q) :
    xStarDigits (i + sparseEnd q) = 0 := by
  apply xStarDigits_eq_zero_of_not_mem
  rintro ⟨t, ht⟩
  by_cases htq : t ≤ q
  · have hend : sparseEnd t ≤ sparseEnd q := sparseEnd_strictMono.monotone htq
    rw [sparsePosition] at ht
    have hpos : 0 < sparseEnd t := by simp [sparseEnd]
    omega
  · have hqt : q + 1 ≤ t := by omega
    have hnext : sparseEnd (q + 1) ≤ sparseEnd t :=
      sparseEnd_strictMono.monotone hqt
    change i < sparseEnd (q + 1) - sparseEnd q - 1 at hi
    rw [sparsePosition] at ht
    have hpos : 0 < sparseEnd t := by simp [sparseEnd]
    omega

theorem shifted_xStarDigits_ofDigits_pos (q : ℕ) :
    0 < Real.ofDigits (fun i => xStarDigits (i + sparseEnd q)) := by
  let k := zeroGap q
  let d : ℕ → Fin 10 := fun i => xStarDigits (i + sparseEnd q)
  have hnext : d k = 1 := by
    dsimp [d, k]
    have heq : zeroGap q + sparseEnd q = sparseEnd (q + 1) - 1 := by
      rw [zeroGap_eq, sparseEnd_succ]
      have hpos : 0 < sparseEnd q := by simp [sparseEnd]
      omega
    rw [heq]
    exact xStarDigits_sparsePosition (q + 1)
  have hterm : 0 < Real.ofDigitsTerm d k := by
    rw [Real.ofDigitsTerm, hnext]
    simp
  have hle : Real.ofDigitsTerm d k ≤ Real.ofDigits d :=
    Real.summable_ofDigitsTerm.le_tsum k (fun _ _ => Real.ofDigitsTerm_nonneg)
  exact hterm.trans_le hle

theorem shifted_xStarDigits_ofDigits_le_gap (q : ℕ) :
    Real.ofDigits (fun i => xStarDigits (i + sparseEnd q)) ≤
      ((10 : ℝ) ^ zeroGap q)⁻¹ := by
  let d : ℕ → Fin 10 := fun i => xStarDigits (i + sparseEnd q)
  rw [Real.ofDigits_eq_sum_add_ofDigits d (zeroGap q)]
  have hsum :
      (∑ i ∈ Finset.range (zeroGap q), Real.ofDigitsTerm d i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hzero : d i = 0 :=
      xStarDigits_shift_eq_zero_before_gap q i (Finset.mem_range.mp hi)
    simp [Real.ofDigitsTerm, hzero]
  rw [hsum, zero_add]
  exact mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)

theorem zeroGap_ge (q : ℕ) : q ≤ zeroGap q := by
  rw [zeroGap_eq, sparseEnd]
  have hpow : q + 1 ≤ 4 ^ (q + 1) := by
    calc
      q + 1 ≤ 2 ^ (q + 1) := (q + 1).lt_two_pow_self.le
      _ ≤ 4 ^ (q + 1) := Nat.pow_le_pow_left (by omega) _
  omega

theorem denominator_lt_ten_pow_zeroGap (B : ℕ) :
    B < 10 ^ zeroGap (B + 1) := by
  have hgap : B + 1 ≤ zeroGap (B + 1) := zeroGap_ge (B + 1)
  calc
    B < B + 1 := by omega
    _ < 2 ^ (B + 1) := (B + 1).lt_two_pow_self
    _ ≤ 10 ^ (B + 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ 10 ^ zeroGap (B + 1) := Nat.pow_le_pow_right (by omega) hgap

theorem pow_mul_xStar_eq_prefix_add_tail (q : ℕ) :
    (10 : ℝ) ^ sparseEnd q * xStar =
      (prefixLabel xStarDigits (sparseEnd q) 0 : ℕ) +
        Real.ofDigits (fun i => xStarDigits (i + sparseEnd q)) := by
  rw [xStar, Real.ofDigits_eq_sum_add_ofDigits xStarDigits (sparseEnd q)]
  have hprefix := prefixSum_eq_label_div xStarDigits (sparseEnd q) 0
  simp only [zero_add] at hprefix
  rw [hprefix]
  have hp : (10 : ℝ) ^ sparseEnd q ≠ 0 := by positivity
  field_simp
  ring

/-- The explicit fixed seed is irrational. -/
theorem xStar_irrational : Irrational xStar := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  let B : ℕ := b.natAbs
  let q : ℕ := B + 1
  let E : ℕ := sparseEnd q
  let P : ℕ := prefixLabel xStarDigits E 0
  let y : ℝ := Real.ofDigits (fun i => xStarDigits (i + E))
  have hypos : 0 < y := by
    simpa [y, E] using shifted_xStarDigits_ofDigits_pos q
  have hyle : y ≤ ((10 : ℝ) ^ zeroGap q)⁻¹ := by
    simpa [y, E] using shifted_xStarDigits_ofDigits_le_gap q
  have hBpowNat : B < 10 ^ zeroGap q := by
    simpa [q] using denominator_lt_ten_pow_zeroGap B
  have hBpow : (B : ℝ) < (10 : ℝ) ^ zeroGap q := by
    exact_mod_cast hBpowNat
  have hBylt : (B : ℝ) * y < 1 := by
    calc
      (B : ℝ) * y ≤ (B : ℝ) * ((10 : ℝ) ^ zeroGap q)⁻¹ :=
        mul_le_mul_of_nonneg_left hyle (by positivity)
      _ < 1 := by
        rw [← div_eq_mul_inv]
        exact (div_lt_one (by positivity)).2 hBpow
  have heq := pow_mul_xStar_eq_prefix_add_tail q
  change (10 : ℝ) ^ E * xStar = (P : ℕ) + y at heq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcleared : (10 : ℝ) ^ E * (a : ℝ) =
      (b : ℝ) * (P : ℝ) + (b : ℝ) * y := by
    rw [hab] at heq
    field_simp [hbR] at heq
    nlinarith
  let z : ℤ := (10 ^ E : ℕ) * a - b * (P : ℤ)
  have hz : (z : ℝ) = (b : ℝ) * y := by
    dsimp [z]
    push_cast
    nlinarith
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    exact (mul_ne_zero hbR hypos.ne') hz.symm
  have hzabs : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hnat : 1 ≤ z.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz0)
    calc
      (1 : ℝ) ≤ (z.natAbs : ℕ) := by exact_mod_cast hnat
      _ = |(z : ℝ)| := by simp
  have habs : |(z : ℝ)| = (B : ℝ) * y := by
    rw [hz, abs_mul, abs_of_pos hypos]
    simp [B]
  rw [habs] at hzabs
  linarith

theorem xStar_ne_pi : xStar ≠ Real.pi := by
  intro h
  have hxle : xStar ≤ 1 := Real.ofDigits_le_one xStarDigits
  rw [h] at hxle
  linarith [Real.pi_gt_three]

/-- A safe fixed width for the decimal representation of `16^j`. -/
def blockWidth (j : ℕ) : ℕ := 2 * j + 1

theorem sixteen_pow_le_ten_pow_two_mul (j : ℕ) :
    16 ^ j ≤ 10 ^ (2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      exact Nat.mul_le_mul ih (by norm_num)

theorem sixteen_pow_lt_ten_pow_blockWidth (j : ℕ) :
    16 ^ j < 10 ^ blockWidth j := by
  calc
    16 ^ j ≤ 10 ^ (2 * j) := sixteen_pow_le_ten_pow_two_mul j
    _ < 10 ^ (2 * j + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    _ = 10 ^ blockWidth j := by rw [blockWidth]

/-- Canonical terminating decimal expansion of `16^j / 10^blockWidth(j)`. -/
def blockExpansion (j : ℕ) : DecimalStream :=
  Real.digits ((16 : ℝ) ^ j / (10 : ℝ) ^ blockWidth j) 10

theorem blockExpansion_ofDigits (j : ℕ) :
    Real.ofDigits (blockExpansion j) =
      (16 : ℝ) ^ j / (10 : ℝ) ^ blockWidth j := by
  rw [blockExpansion, Real.ofDigits_digits (by norm_num)]
  · constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      exact_mod_cast sixteen_pow_lt_ten_pow_blockWidth j

theorem blockExpansion_zero_tail (j n : ℕ) (hn : blockWidth j ≤ n) :
    blockExpansion j n = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply Fin.ext
  simp only [blockExpansion, Real.digits, Fin.val_ofNat]
  have heq :
      ((16 : ℝ) ^ j / (10 : ℝ) ^ blockWidth j) *
          (10 : ℝ) ^ (blockWidth j + t + 1) =
        ((16 ^ j) * 10 ^ (t + 1) : ℕ) := by
    rw [show blockWidth j + t + 1 = blockWidth j + (t + 1) by omega,
      pow_add]
    push_cast
    field_simp
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [heq, Nat.floor_natCast]
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨(16 ^ j) * 10 ^ t, ?_⟩
  rw [pow_succ]
  ring

theorem exists_splitIndex (s : ℕ) :
    ∃ q : ℕ, s ≤ 3 * 4 ^ (q + 1) := by
  refine ⟨s, ?_⟩
  have hs : s ≤ 2 ^ s := s.lt_two_pow_self.le
  have hpow : 2 ^ s ≤ 4 ^ (s + 1) := by
    calc
      2 ^ s ≤ 4 ^ s := Nat.pow_le_pow_left (by omega) _
      _ ≤ 4 ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos : 0 < 4 ^ (s + 1) := by positivity
  omega

/-- Least tail split index; `splitEnd s` is a power of four and leaves at
least `s` positions across the next factor-four gap. -/
def splitIndex (s : ℕ) : ℕ := Nat.find (exists_splitIndex s)

def splitEnd (s : ℕ) : ℕ := 4 ^ (splitIndex s + 1)

theorem splitIndex_spec (s : ℕ) : s ≤ 3 * splitEnd s := by
  exact Nat.find_spec (exists_splitIndex s)

theorem splitEnd_le_two_mul (s : ℕ) (hs : 4 ≤ s) : splitEnd s ≤ 2 * s := by
  cases hq : splitIndex s with
  | zero =>
      simp [splitEnd, hq]
      omega
  | succ q =>
      have hq_lt : q < splitIndex s := by omega
      have hminimal : ¬s ≤ 3 * 4 ^ (q + 1) := by
        exact Nat.find_min (exists_splitIndex s) hq_lt
      have hlt : 3 * 4 ^ (q + 1) < s := by omega
      rw [splitEnd, hq, show q + 1 + 1 = (q + 1) + 1 by omega, pow_succ]
      nlinarith

theorem blockWidth_add_le_three_splitEnd (m j : ℕ) :
    blockWidth j + m ≤ 3 * splitEnd (blockWidth j + m) :=
  splitIndex_spec _

theorem splitEnd_le_two_width_add (m j : ℕ) (hm : 5 ≤ m) :
    splitEnd (blockWidth j + m) ≤ 2 * (blockWidth j + m) := by
  apply splitEnd_le_two_mul
  simp [blockWidth]
  omega

/-- Terminating width-`E` decimal expansion of `p / 10^E`. -/
def terminatingExpansion (p E : ℕ) : DecimalStream :=
  Real.digits ((p : ℝ) / (10 : ℝ) ^ E) 10

theorem terminatingExpansion_ofDigits {p E : ℕ} (hp : p < 10 ^ E) :
    Real.ofDigits (terminatingExpansion p E) =
      (p : ℝ) / (10 : ℝ) ^ E := by
  rw [terminatingExpansion, Real.ofDigits_digits (by norm_num)]
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    exact_mod_cast hp

theorem terminatingExpansion_zero_tail {p E n : ℕ}
    (hp : p < 10 ^ E) (hn : E ≤ n) :
    terminatingExpansion p E n = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply Fin.ext
  simp only [terminatingExpansion, Real.digits, Fin.val_ofNat]
  have heq :
      ((p : ℝ) / (10 : ℝ) ^ E) * (10 : ℝ) ^ (E + t + 1) =
        (p * 10 ^ (t + 1) : ℕ) := by
    rw [show E + t + 1 = E + (t + 1) by omega, pow_add]
    push_cast
    field_simp
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [heq, Nat.floor_natCast]
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨p * 10 ^ t, ?_⟩
  rw [pow_succ]
  ring

def prefixEnd (m j : ℕ) : ℕ := splitEnd (blockWidth j + m)

def prefixLastIndex (m j : ℕ) : ℕ := splitIndex (blockWidth j + m)

theorem prefixEnd_eq_sparseEnd (m j : ℕ) :
    prefixEnd m j = sparseEnd (prefixLastIndex m j) := rfl

/-- Numerator of the finite part of `16^j x_*` over denominator
`10^prefixEnd(m,j)`. -/
def finiteNumerator (m j : ℕ) : ℕ :=
  16 ^ j * ∑ q ∈ Finset.range (prefixLastIndex m j + 1),
    10 ^ (prefixEnd m j - sparseEnd q)

def prefixResidue (m j : ℕ) : ℕ :=
  finiteNumerator m j % 10 ^ prefixEnd m j

def prefixExpansion (m j : ℕ) : DecimalStream :=
  terminatingExpansion (prefixResidue m j) (prefixEnd m j)

theorem prefixResidue_lt (m j : ℕ) :
    prefixResidue m j < 10 ^ prefixEnd m j := by
  apply Nat.mod_lt
  positivity

theorem prefixExpansion_ofDigits (m j : ℕ) :
    Real.ofDigits (prefixExpansion m j) =
      (prefixResidue m j : ℝ) / (10 : ℝ) ^ prefixEnd m j := by
  exact terminatingExpansion_ofDigits (prefixResidue_lt m j)

theorem prefixExpansion_zero_tail (m j n : ℕ) (hn : prefixEnd m j ≤ n) :
    prefixExpansion m j n = 0 :=
  terminatingExpansion_zero_tail (prefixResidue_lt m j) hn

/-- The support interval of the copy of `16^j` ending at sparse position
`sparseEnd q`, after the finite prefix split. -/
def InTailBlock (m j q n : ℕ) : Prop :=
  prefixLastIndex m j < q ∧
    sparseEnd q - blockWidth j ≤ n ∧ n < sparseEnd q

theorem sparseEnd_prefixLastIndex (m j : ℕ) :
    sparseEnd (prefixLastIndex m j) = prefixEnd m j := by rfl

theorem firstTailEnd (m j : ℕ) :
    sparseEnd (prefixLastIndex m j + 1) = 4 * prefixEnd m j := by
  rw [sparseEnd_succ, sparseEnd_prefixLastIndex]

theorem tail_start_after_prefix
    {m j q : ℕ} (hq : prefixLastIndex m j < q) :
    prefixEnd m j + m ≤ sparseEnd q - blockWidth j := by
  have hqfirst : prefixLastIndex m j + 1 ≤ q := by omega
  have hend : sparseEnd (prefixLastIndex m j + 1) ≤ sparseEnd q :=
    sparseEnd_strictMono.monotone hqfirst
  have hsplit := blockWidth_add_le_three_splitEnd m j
  change blockWidth j + m ≤ 3 * prefixEnd m j at hsplit
  rw [firstTailEnd] at hend
  apply Nat.le_sub_of_add_le
  omega

theorem tail_blocks_window_separated
    {m j q r : ℕ} (hqr : q < r) (hq : prefixLastIndex m j < q) :
    sparseEnd q + m ≤ sparseEnd r - blockWidth j := by
  have hnext : sparseEnd (q + 1) ≤ sparseEnd r :=
    sparseEnd_strictMono.monotone (by omega)
  have hendpos : prefixEnd m j ≤ sparseEnd q := by
    have := sparseEnd_strictMono.monotone (show prefixLastIndex m j ≤ q by omega)
    simpa [sparseEnd_prefixLastIndex] using this
  have hsplit := blockWidth_add_le_three_splitEnd m j
  change blockWidth j + m ≤ 3 * prefixEnd m j at hsplit
  have hwm : blockWidth j + m ≤ 3 * sparseEnd q := by
    nlinarith
  rw [sparseEnd_succ] at hnext
  apply Nat.le_sub_of_add_le
  omega

theorem tail_blocks_disjoint
    {m j q r n : ℕ} (hq : InTailBlock m j q n)
    (hr : InTailBlock m j r n) : q = r := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hqr | hrq
  · have hsep := tail_blocks_window_separated (m := m) (j := j) hqr hq.1
    have hend : sparseEnd q ≤ n :=
      (Nat.le_add_right (sparseEnd q) m).trans (hsep.trans hr.2.1)
    exact (not_lt_of_ge hend) hq.2.2
  · have hsep := tail_blocks_window_separated (m := m) (j := j) hrq hr.1
    have hend : sparseEnd r ≤ n :=
      (Nat.le_add_right (sparseEnd r) m).trans (hsep.trans hq.2.1)
    exact (not_lt_of_ge hend) hr.2.2

/-- Explicit carry-free expansion of `16^j x_*`: a finite residue prefix,
followed by disjoint copies of the fixed-width decimal block for `16^j`. -/
def scaledExpansion (m j n : ℕ) : Fin 10 := by
  classical
  exact if n < prefixEnd m j then prefixExpansion m j n
    else if h : ∃ q : ℕ, InTailBlock m j q n then
      blockExpansion j
        (n - (sparseEnd (Classical.choose h) - blockWidth j))
    else 0

theorem scaledExpansion_eq_prefix {m j n : ℕ} (hn : n < prefixEnd m j) :
    scaledExpansion m j n = prefixExpansion m j n := by
  simp [scaledExpansion, hn]

theorem scaledExpansion_eq_tail
    {m j q n : ℕ} (hq : InTailBlock m j q n) :
    scaledExpansion m j n =
      blockExpansion j (n - (sparseEnd q - blockWidth j)) := by
  classical
  rw [scaledExpansion, if_neg]
  · split
    next h =>
      have hchoose : Classical.choose h = q :=
        tail_blocks_disjoint (Classical.choose_spec h) hq
      rw [hchoose]
    next h => exact (h ⟨q, hq⟩).elim
  · have hstart := tail_start_after_prefix hq.1
    have hle : prefixEnd m j ≤ n := by
      exact (Nat.le_add_right (prefixEnd m j) m).trans
        (hstart.trans hq.2.1)
    omega

theorem scaledExpansion_eq_zero_of_outside
    {m j n : ℕ} (hn : prefixEnd m j ≤ n)
    (hout : ∀ q : ℕ, ¬InTailBlock m j q n) :
    scaledExpansion m j n = 0 := by
  rw [scaledExpansion, if_neg (by omega), dif_neg]
  push Not
  exact hout

/-- Prefix a decimal stream by `k` zeros. -/
def shiftExpansion (k : ℕ) (a : DecimalStream) : DecimalStream :=
  fun n => if k ≤ n then a (n - k) else 0

theorem shiftExpansion_before {k n : ℕ} {a : DecimalStream} (hn : n < k) :
    shiftExpansion k a n = 0 := by simp [shiftExpansion, hn]

theorem shiftExpansion_after (k i : ℕ) (a : DecimalStream) :
    shiftExpansion k a (i + k) = a i := by
  simp [shiftExpansion, Nat.add_sub_cancel_left, Nat.add_comm]

theorem ofDigits_shiftExpansion (k : ℕ) (a : DecimalStream) :
    Real.ofDigits (shiftExpansion k a) =
      ((10 : ℝ) ^ k)⁻¹ * Real.ofDigits a := by
  rw [Real.ofDigits_eq_sum_add_ofDigits (shiftExpansion k a) k]
  have hsum :
      (∑ i ∈ Finset.range k, Real.ofDigitsTerm (shiftExpansion k a) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hz := shiftExpansion_before (a := a) (Finset.mem_range.mp hi)
    simp [Real.ofDigitsTerm, hz]
  rw [hsum, zero_add]
  congr 1
  apply congrArg Real.ofDigits
  funext i
  simpa [Nat.add_comm] using shiftExpansion_after k i a

abbrev TailIndex (m j : ℕ) := {q : ℕ // prefixLastIndex m j < q}

theorem blockWidth_le_tailEnd {m j q : ℕ}
    (hq : prefixLastIndex m j < q) : blockWidth j ≤ sparseEnd q := by
  have hstart := tail_start_after_prefix (m := m) (j := j) hq
  have hE : 0 < prefixEnd m j := by simp [prefixEnd, splitEnd]
  omega

/-- One shifted copy of the decimal block for `16^j`. -/
def tailBlockExpansion (m j : ℕ) (q : TailIndex m j) : DecimalStream :=
  shiftExpansion (sparseEnd q.val - blockWidth j) (blockExpansion j)

theorem tailBlockExpansion_ofDigits (m j : ℕ) (q : TailIndex m j) :
    Real.ofDigits (tailBlockExpansion m j q) =
      (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val := by
  rw [tailBlockExpansion, ofDigits_shiftExpansion, blockExpansion_ofDigits]
  have hw : blockWidth j ≤ sparseEnd q.val := blockWidth_le_tailEnd q.property
  have hadd : sparseEnd q.val - blockWidth j + blockWidth j = sparseEnd q.val :=
    Nat.sub_add_cancel hw
  have hinv : ((10 : ℝ) ^ sparseEnd q.val)⁻¹ =
      ((10 : ℝ) ^ (sparseEnd q.val - blockWidth j))⁻¹ *
        ((10 : ℝ) ^ blockWidth j)⁻¹ := by
    rw [← hadd, pow_add]
    field_simp
    congr 1
    omega
  rw [div_eq_mul_inv, div_eq_mul_inv, hinv]
  ring

theorem tailBlockExpansion_eq_block
    {m j : ℕ} (q : TailIndex m j) {n : ℕ}
    (hn : sparseEnd q.val - blockWidth j ≤ n) :
    tailBlockExpansion m j q n =
      blockExpansion j (n - (sparseEnd q.val - blockWidth j)) := by
  simp [tailBlockExpansion, shiftExpansion, hn]

theorem tailBlockExpansion_eq_zero_after
    {m j : ℕ} (q : TailIndex m j) {n : ℕ}
    (hn : sparseEnd q.val ≤ n) : tailBlockExpansion m j q n = 0 := by
  rw [tailBlockExpansion_eq_block q (by
    have hw := blockWidth_le_tailEnd q.property
    omega)]
  apply blockExpansion_zero_tail
  have hw := blockWidth_le_tailEnd q.property
  omega

theorem tailBlockExpansion_eq_zero_before
    {m j : ℕ} (q : TailIndex m j) {n : ℕ}
    (hn : n < sparseEnd q.val - blockWidth j) :
    tailBlockExpansion m j q n = 0 :=
  shiftExpansion_before hn

theorem summable_sparseTerms :
    Summable (fun q : ℕ => (10 : ℝ) ^ (-(sparseEnd q : ℤ))) := by
  have hgeom : Summable (fun n : ℕ => (10 : ℝ) ^ (-(n : ℤ))) := by
    simpa [zpow_neg, zpow_natCast] using
      (summable_geometric_of_lt_one (by positivity : 0 ≤ (10 : ℝ)⁻¹)
        (by norm_num))
  exact hgeom.comp_injective sparseEnd_strictMono.injective

def tailReservedTerm (m j : ℕ) (q : TailIndex m j) (n : ℕ) : ℝ :=
  Real.ofDigitsTerm (tailBlockExpansion m j q) n

theorem tailReservedTerm_nonneg (m j : ℕ) (q : TailIndex m j) (n : ℕ) :
    0 ≤ tailReservedTerm m j q n := Real.ofDigitsTerm_nonneg

theorem summable_tailReservedTerm (m j : ℕ) (q : TailIndex m j) :
    Summable (tailReservedTerm m j q) := Real.summable_ofDigitsTerm

theorem tailReservedTerm_tsum (m j : ℕ) (q : TailIndex m j) :
    (∑' n : ℕ, tailReservedTerm m j q n) =
      (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val :=
  tailBlockExpansion_ofDigits m j q

theorem summable_tailReservedTerms (m j : ℕ) :
    Summable (Function.uncurry (tailReservedTerm m j)) := by
  change Summable (fun p : TailIndex m j × ℕ =>
    tailReservedTerm m j p.1 p.2)
  rw [summable_prod_of_nonneg (fun p => tailReservedTerm_nonneg m j p.1 p.2)]
  refine ⟨fun q => summable_tailReservedTerm m j q, ?_⟩
  have hs : Summable (fun q : TailIndex m j =>
      (10 : ℝ) ^ (-(sparseEnd q.val : ℤ))) :=
    summable_sparseTerms.subtype _
  have hmul := hs.mul_left ((16 : ℝ) ^ j)
  apply hmul.congr
  intro q
  rw [tailReservedTerm_tsum]
  simp [div_eq_mul_inv, zpow_neg, zpow_natCast]

theorem reservedTerm_eq_zero_before
    {m j : ℕ} (q : TailIndex m j) {n : ℕ}
    (hn : n < sparseEnd q.val - blockWidth j) :
    tailReservedTerm m j q n = 0 := by
  simp [tailReservedTerm, Real.ofDigitsTerm,
    tailBlockExpansion_eq_zero_before q hn]

theorem reservedTerm_eq_zero_after
    {m j : ℕ} (q : TailIndex m j) {n : ℕ}
    (hn : sparseEnd q.val ≤ n) : tailReservedTerm m j q n = 0 := by
  simp [tailReservedTerm, Real.ofDigitsTerm,
    tailBlockExpansion_eq_zero_after q hn]

theorem scaledTerm_eq_prefix_add_tsum_tail (m j n : ℕ) :
    Real.ofDigitsTerm (scaledExpansion m j) n =
      Real.ofDigitsTerm (prefixExpansion m j) n +
        ∑' q : TailIndex m j, tailReservedTerm m j q n := by
  classical
  by_cases hnpre : n < prefixEnd m j
  · rw [Real.ofDigitsTerm, scaledExpansion_eq_prefix hnpre]
    have hall : ∀ q : TailIndex m j, tailReservedTerm m j q n = 0 := by
      intro q
      apply reservedTerm_eq_zero_before
      have hstart := tail_start_after_prefix (m := m) (j := j) q.property
      omega
    simp [hall, Real.ofDigitsTerm]
  · have hprefix : prefixExpansion m j n = 0 :=
      prefixExpansion_zero_tail m j n (by omega)
    by_cases hblock : ∃ q : ℕ, InTailBlock m j q n
    · let q : TailIndex m j :=
        ⟨Classical.choose hblock, (Classical.choose_spec hblock).1⟩
      have hq : InTailBlock m j q.val n := Classical.choose_spec hblock
      rw [tsum_eq_single q]
      · have hscaled := scaledExpansion_eq_tail hq
        have htail := tailBlockExpansion_eq_block q hq.2.1
        simp only [tailReservedTerm, Real.ofDigitsTerm, hprefix,
          Fin.val_zero, Nat.cast_zero, zero_mul, zero_add]
        rw [hscaled, htail]
      · intro r hrq
        rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hrq) with hrlt | hqLt
        · apply reservedTerm_eq_zero_after
          have hsep := tail_blocks_window_separated
            (m := m) (j := j) hrlt r.property
          have hnstart := hq.2.1
          exact (Nat.le_add_right (sparseEnd r.val) m).trans
            (hsep.trans hnstart)
        · apply reservedTerm_eq_zero_before
          have hsep := tail_blocks_window_separated
            (m := m) (j := j) hqLt q.property
          exact lt_of_lt_of_le hq.2.2
            ((Nat.le_add_right (sparseEnd q.val) m).trans hsep)
    · have hscaled : scaledExpansion m j n = 0 := by
        apply scaledExpansion_eq_zero_of_outside (by omega)
        intro q hq
        exact hblock ⟨q, hq⟩
      have hall : ∀ q : TailIndex m j, tailReservedTerm m j q n = 0 := by
        intro q
        by_cases hbefore : n < sparseEnd q.val - blockWidth j
        · exact reservedTerm_eq_zero_before q hbefore
        · apply reservedTerm_eq_zero_after
          by_contra hnafter
          push Not at hnafter
          exact hblock ⟨q.val, q.property, by omega, hnafter⟩
      simp [hscaled, hprefix, hall, Real.ofDigitsTerm]

/-- Exact real value of the explicit scaled decimal stream. -/
theorem scaledExpansion_ofDigits (m j : ℕ) :
    Real.ofDigits (scaledExpansion m j) =
      (prefixResidue m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
        ∑' q : TailIndex m j,
          (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val := by
  have hprod := summable_tailReservedTerms m j
  have htailN : Summable (fun n : ℕ =>
      ∑' q : TailIndex m j, tailReservedTerm m j q n) :=
    hprod.prod_symm.prod
  rw [Real.ofDigits]
  calc
    (∑' n : ℕ, Real.ofDigitsTerm (scaledExpansion m j) n) =
        ∑' n : ℕ, (Real.ofDigitsTerm (prefixExpansion m j) n +
          ∑' q : TailIndex m j, tailReservedTerm m j q n) := by
            apply tsum_congr
            intro n
            exact scaledTerm_eq_prefix_add_tsum_tail m j n
    _ = (∑' n : ℕ, Real.ofDigitsTerm (prefixExpansion m j) n) +
          ∑' n : ℕ, ∑' q : TailIndex m j,
            tailReservedTerm m j q n :=
      Real.summable_ofDigitsTerm.tsum_add htailN
    _ = Real.ofDigits (prefixExpansion m j) +
          ∑' q : TailIndex m j, ∑' n : ℕ,
            tailReservedTerm m j q n := by
      rw [Real.ofDigits, hprod.tsum_comm]
    _ = (prefixResidue m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
          ∑' q : TailIndex m j,
            (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val := by
      rw [prefixExpansion_ofDigits]
      congr 1
      apply tsum_congr
      intro q
      exact tailReservedTerm_tsum m j q

/-- Reindex naturals as precisely the sparse terms after the finite split. -/
def tailIndexEquiv (m j : ℕ) : ℕ ≃ TailIndex m j where
  toFun k := ⟨prefixLastIndex m j + 1 + k, by omega⟩
  invFun q := q.val - (prefixLastIndex m j + 1)
  left_inv k := by simp
  right_inv q := by
    apply Subtype.ext
    change prefixLastIndex m j + 1 +
      (q.val - (prefixLastIndex m j + 1)) = q.val
    omega

theorem tail_tsum_reindex (m j : ℕ) :
    (∑' q : TailIndex m j,
        (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val) =
      ∑' k : ℕ, (16 : ℝ) ^ j /
        (10 : ℝ) ^ sparseEnd (k + (prefixLastIndex m j + 1)) := by
  have h := (tailIndexEquiv m j).tsum_eq
    (fun q : TailIndex m j =>
      (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val)
  rw [← h]
  apply tsum_congr
  intro k
  simp [tailIndexEquiv, Nat.add_comm, Nat.add_left_comm]

theorem sparseEnd_le_prefixEnd {m j q : ℕ}
    (hq : q < prefixLastIndex m j + 1) :
    sparseEnd q ≤ prefixEnd m j := by
  rw [← sparseEnd_prefixLastIndex]
  exact sparseEnd_strictMono.monotone (by omega)

theorem decimal_pow_sub_div {E a : ℕ} (ha : a ≤ E) :
    ((10 ^ (E - a) : ℕ) : ℝ) / (10 : ℝ) ^ E =
      (10 : ℝ) ^ (-(a : ℤ)) := by
  have hdecomp : E - a + a = E := Nat.sub_add_cancel ha
  rw [zpow_neg, zpow_natCast, ← hdecomp, pow_add]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  congr 1
  omega

theorem finiteNumerator_div (m j : ℕ) :
    (finiteNumerator m j : ℝ) / (10 : ℝ) ^ prefixEnd m j =
      (16 : ℝ) ^ j *
        ∑ q ∈ Finset.range (prefixLastIndex m j + 1),
          (10 : ℝ) ^ (-(sparseEnd q : ℤ)) := by
  rw [finiteNumerator]
  push_cast
  rw [mul_div_assoc]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    decimal_pow_sub_div
      (sparseEnd_le_prefixEnd (Finset.mem_range.mp hq))

theorem sixteen_mul_xStar_split (m j : ℕ) :
    (16 : ℝ) ^ j * xStar =
      (finiteNumerator m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
        ∑' q : TailIndex m j,
          (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val := by
  let Q := prefixLastIndex m j + 1
  let f : ℕ → ℝ := fun q => (10 : ℝ) ^ (-(sparseEnd q : ℤ))
  have hsplit := summable_sparseTerms.sum_add_tsum_nat_add Q
  have htail : Summable (fun k : ℕ => f (k + Q)) :=
    summable_sparseTerms.comp_injective (fun _ _ h => by omega)
  have hmul :
      (16 : ℝ) ^ j * (∑' k : ℕ, f (k + Q)) =
        ∑' k : ℕ, (16 : ℝ) ^ j * f (k + Q) :=
    (htail.tsum_mul_left ((16 : ℝ) ^ j)).symm
  calc
    (16 : ℝ) ^ j * xStar = (16 : ℝ) ^ j * ∑' q : ℕ, f q := by
      rw [xStar_eq_series]
      rfl
    _ = (16 : ℝ) ^ j *
        ((∑ q ∈ Finset.range Q, f q) + ∑' k : ℕ, f (k + Q)) := by
      rw [hsplit]
    _ = (16 : ℝ) ^ j * (∑ q ∈ Finset.range Q, f q) +
        ∑' k : ℕ, (16 : ℝ) ^ j * f (k + Q) := by
      rw [mul_add, hmul]
    _ = (finiteNumerator m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
        ∑' k : ℕ, (16 : ℝ) ^ j /
          (10 : ℝ) ^ sparseEnd (k + Q) := by
      rw [finiteNumerator_div]
      congr 1
      apply tsum_congr
      intro k
      simp [f, div_eq_mul_inv, zpow_neg, zpow_natCast]
    _ = (finiteNumerator m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
        ∑' q : TailIndex m j,
          (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val := by
      rw [tail_tsum_reindex]

theorem prefixResidue_circle_eq_finiteNumerator (m j : ℕ) :
    (((prefixResidue m j : ℝ) / (10 : ℝ) ^ prefixEnd m j : ℝ) :
      UnitAddCircle) =
    (((finiteNumerator m j : ℝ) / (10 : ℝ) ^ prefixEnd m j : ℝ) :
      UnitAddCircle) := by
  let M : ℕ := 10 ^ prefixEnd m j
  let A : ℕ := finiteNumerator m j
  have hM : M ≠ 0 := by simp [M]
  have hdiv := Nat.mod_add_div A M
  have hreal : (A : ℝ) / (M : ℝ) =
      ((A % M : ℕ) : ℝ) / (M : ℝ) + ((A / M : ℕ) : ℝ) := by
    field_simp
    exact_mod_cast hdiv.symm
  have hcircle := congrArg (fun r : ℝ => (r : UnitAddCircle)) hreal
  change (((A : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) =
    (((((A % M : ℕ) : ℝ) / (M : ℝ) + ((A / M : ℕ) : ℝ) : ℝ)) :
      UnitAddCircle) at hcircle
  rw [AddCircle.coe_add, real_nat_circle_eq_zero, add_zero] at hcircle
  simpa [M, A, prefixResidue] using hcircle.symm

/-- The carry-free stream has exactly the circle value `16^j x_*`. -/
theorem scaledExpansion_circleValue (m j : ℕ) :
    circleValue (scaledExpansion m j) =
      circleMul (16 ^ j) xStarPoint := by
  rw [circleValue, scaledExpansion_ofDigits, xStarPoint]
  have hsplit := sixteen_mul_xStar_split m j
  have hp := prefixResidue_circle_eq_finiteNumerator m j
  have hcoe :
      ((((prefixResidue m j : ℝ) / (10 : ℝ) ^ prefixEnd m j +
          ∑' q : TailIndex m j,
            (16 : ℝ) ^ j / (10 : ℝ) ^ sparseEnd q.val : ℝ)) :
        UnitAddCircle) =
      (((16 : ℝ) ^ j * xStar : ℝ) : UnitAddCircle) := by
    rw [hsplit, AddCircle.coe_add, AddCircle.coe_add, hp]
  rw [hcoe]
  change ((((16 : ℝ) ^ j * xStar : ℝ)) : UnitAddCircle) =
    (16 ^ j) • ((xStar : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_nsmul]
  congr 1
  push_cast
  simp [nsmul_eq_mul]

/-- Length-`m` factor beginning at `start`. -/
def windowVector (m : ℕ) (a : DecimalStream) (start : ℕ) : Fin m → Fin 10 :=
  fun i => a (start + i.val)

/-- A single copy of the `16^j` block, with `m` leading zeros. -/
def modelExpansion (m j : ℕ) : DecimalStream :=
  shiftExpansion m (blockExpansion j)

def modelWindow (m j start : ℕ) : Fin m → Fin 10 :=
  windowVector m (modelExpansion m j) start

/-- The finite index family overcounting every factor at all inclusive levels
`0 ≤ j ≤ R`.  The first summand indexes finite-prefix starts and the second
indexes every relative window around one isolated tail block. -/
abbrev FactorIndex (m R : ℕ) :=
  Σ j : Fin (R + 1),
    Fin (prefixEnd m j.val + (m + blockWidth j.val))

def indexedFactor (m R : ℕ) (p : FactorIndex m R) : Fin m → Fin 10 :=
  if h : p.2.val < prefixEnd m p.1.val then
    windowVector m (scaledExpansion m p.1.val) p.2.val
  else
    modelWindow m p.1.val (p.2.val - prefixEnd m p.1.val)

def observedFactors (m R : ℕ) : Finset (Fin m → Fin 10) :=
  Finset.univ.image (indexedFactor m R)

theorem factorIndex_card (m R : ℕ) :
    Fintype.card (FactorIndex m R) =
      ∑ j ∈ Finset.range (R + 1),
        (prefixEnd m j + (m + blockWidth j)) := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  simpa using (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => prefixEnd m j + (m + blockWidth j)) (R + 1))

theorem observedFactors_card_le_index_count (m R : ℕ) :
    (observedFactors m R).card ≤
      ∑ j ∈ Finset.range (R + 1),
        (prefixEnd m j + (m + blockWidth j)) := by
  calc
    (observedFactors m R).card ≤
        (Finset.univ : Finset (FactorIndex m R)).card := Finset.card_image_le
    _ = Fintype.card (FactorIndex m R) := Finset.card_univ
    _ = _ := factorIndex_card m R

theorem factorIndex_count_le_three_sum (m R : ℕ) (hm : 5 ≤ m) :
    (∑ j ∈ Finset.range (R + 1),
        (prefixEnd m j + (m + blockWidth j))) ≤
      3 * ∑ j ∈ Finset.range (R + 1), (blockWidth j + m) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hE := splitEnd_le_two_width_add m j hm
  change prefixEnd m j ≤ 2 * (blockWidth j + m) at hE
  omega

theorem width_sum_closed_form (m R : ℕ) :
    (∑ j ∈ Finset.range (R + 1), (blockWidth j + m)) =
      (R + 1) * (R + m + 1) := by
  simp only [blockWidth]
  calc
    (∑ j ∈ Finset.range (R + 1), (2 * j + 1 + m)) =
        (∑ j ∈ Finset.range (R + 1), j) * 2 + (R + 1) * (m + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      simp only [Finset.sum_const_nat, Finset.card_range]
      ring
    _ = (R + 1) * R + (R + 1) * (m + 1) := by
      rw [Finset.sum_range_id_mul_two]
      simp
    _ = (R + 1) * (R + m + 1) := by ring

theorem observedFactors_card_le_forty (m : ℕ) (hm : 5 ≤ m) :
    (observedFactors m (2 ^ m)).card ≤ 40 * 4 ^ m := by
  let R := 2 ^ m
  have hcount := observedFactors_card_le_index_count m R
  have hthree := factorIndex_count_le_three_sum m R hm
  rw [width_sum_closed_form] at hthree
  have hmR : m + 1 ≤ R := by
    dsimp [R]
    have hm2 : m < 2 ^ m := m.lt_two_pow_self
    omega
  have hRpos : 0 < R := by simp [R]
  have hbound : 3 * ((R + 1) * (R + m + 1)) ≤ 12 * R ^ 2 := by
    nlinarith
  have hpow : R ^ 2 = 4 ^ m := by
    dsimp [R]
    rw [show 4 = 2 ^ 2 by norm_num]
    simp only [← pow_mul]
    congr 1
    omega
  calc
    (observedFactors m R).card ≤
        ∑ j ∈ Finset.range (R + 1),
          (prefixEnd m j + (m + blockWidth j)) := hcount
    _ ≤ 3 * ((R + 1) * (R + m + 1)) := hthree
    _ ≤ 12 * R ^ 2 := hbound
    _ ≤ 40 * 4 ^ m := by rw [hpow]; omega

theorem forty_four_pow_lt_ten_pow (m : ℕ) (hm : 5 ≤ m) :
    40 * 4 ^ m < 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ, pow_succ]
      nlinarith [show 0 < 4 ^ m by positivity]

def WindowMeetsTail (m j start q : ℕ) : Prop :=
  ∃ i : Fin m, InTailBlock m j q (start + i.val)

theorem window_meets_tail_unique
    {m j start q r : ℕ} (hq : WindowMeetsTail m j start q)
    (hr : WindowMeetsTail m j start r) : q = r := by
  rcases hq with ⟨i, hi⟩
  rcases hr with ⟨k, hk⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hqr | hrq
  · have hsep := tail_blocks_window_separated (m := m) (j := j) hqr hi.1
    have hkstart : sparseEnd q + m ≤ start + k.val := hsep.trans hk.2.1
    have hstartEnd : start < sparseEnd q :=
      lt_of_le_of_lt (Nat.le_add_right start i.val) hi.2.2
    have hlt : start + k.val < sparseEnd q + m :=
      (Nat.add_lt_add_left k.isLt start).trans
        (Nat.add_lt_add_right hstartEnd m)
    exact (not_lt_of_ge hkstart) hlt
  · have hsep := tail_blocks_window_separated (m := m) (j := j) hrq hk.1
    have histart : sparseEnd r + m ≤ start + i.val := hsep.trans hi.2.1
    have hstartEnd : start < sparseEnd r :=
      lt_of_le_of_lt (Nat.le_add_right start k.val) hk.2.2
    have hlt : start + i.val < sparseEnd r + m :=
      (Nat.add_lt_add_left i.isLt start).trans
        (Nat.add_lt_add_right hstartEnd m)
    exact (not_lt_of_ge histart) hlt

theorem scaledExpansion_zero_outside_met_block
    {m j start q n : ℕ} (hmeet : WindowMeetsTail m j start q)
    (hstartn : start ≤ n) (hnwindow : n < start + m)
    (hnpre : prefixEnd m j ≤ n)
    (hnout : ¬InTailBlock m j q n) : scaledExpansion m j n = 0 := by
  apply scaledExpansion_eq_zero_of_outside hnpre
  intro r hr
  have hqr : q = r :=
    window_meets_tail_unique hmeet ⟨⟨n - start, by omega⟩, by
      simpa [Nat.add_sub_of_le hstartn] using hr⟩
  exact hnout (hqr ▸ hr)

theorem window_eq_model_of_meets
    {m j start q : ℕ} (hstart : prefixEnd m j ≤ start)
    (hmeet : WindowMeetsTail m j start q) :
    ∃ offset : ℕ, offset < m + blockWidth j ∧
      windowVector m (scaledExpansion m j) start = modelWindow m j offset := by
  rcases hmeet with ⟨i, hi⟩
  let B := sparseEnd q - blockWidth j
  let offset := start + m - B
  have hB : B ≤ start + m := by
    change B ≤ start + m
    have hBi := hi.2.1
    change B ≤ start + i.val at hBi
    have hir := i.isLt
    omega
  have hw : blockWidth j ≤ sparseEnd q := blockWidth_le_tailEnd hi.1
  have hBadd : B + blockWidth j = sparseEnd q := by
    dsimp [B]
    exact Nat.sub_add_cancel hw
  have hoffset : offset < m + blockWidth j := by
    dsimp [offset]
    have hstartEnd : start < sparseEnd q :=
      lt_of_le_of_lt (Nat.le_add_right start i.val) hi.2.2
    omega
  refine ⟨offset, hoffset, ?_⟩
  funext r
  let n := start + r.val
  change scaledExpansion m j n = modelExpansion m j (offset + r.val)
  have hnpre : prefixEnd m j ≤ n := hstart.trans (Nat.le_add_right start r.val)
  have hstartn : start ≤ n := Nat.le_add_right start r.val
  have hnwindow : n < start + m := by
    dsimp [n]
    omega
  by_cases hnB : n < B
  · have hglobal : scaledExpansion m j n = 0 := by
      apply scaledExpansion_zero_outside_met_block ⟨i, hi⟩ hstartn hnwindow hnpre
      intro hinside
      exact (not_lt_of_ge hinside.2.1) hnB
    have hmodel : modelExpansion m j (offset + r.val) = 0 := by
      apply shiftExpansion_before
      dsimp [offset, n] at hnB ⊢
      omega
    exact hglobal.trans hmodel.symm
  · have hBn : B ≤ n := by omega
    have hmodel : modelExpansion m j (offset + r.val) =
        blockExpansion j (n - B) := by
      rw [modelExpansion, shiftExpansion]
      have hmle : m ≤ offset + r.val := by
        dsimp [offset, n] at hBn ⊢
        omega
      rw [if_pos hmle]
      congr 1
      dsimp [offset, n]
      omega
    by_cases hnend : n < sparseEnd q
    · have hinside : InTailBlock m j q n := ⟨hi.1, hBn, hnend⟩
      have hglobal := scaledExpansion_eq_tail hinside
      exact hglobal.trans hmodel.symm
    · have hglobal : scaledExpansion m j n = 0 := by
        apply scaledExpansion_zero_outside_met_block ⟨i, hi⟩ hstartn hnwindow hnpre
        intro hinside
        exact hnend hinside.2.2
      have hblock : blockExpansion j (n - B) = 0 := by
        apply blockExpansion_zero_tail
        dsimp [B] at hBn ⊢
        omega
      exact hglobal.trans (hmodel.trans hblock).symm

theorem windowVector_mem_observedFactors
    {m R j start : ℕ} (hj : j ≤ R) :
    windowVector m (scaledExpansion m j) start ∈ observedFactors m R := by
  classical
  apply Finset.mem_image.mpr
  let jf : Fin (R + 1) := ⟨j, by omega⟩
  by_cases hprefix : start < prefixEnd m j
  · let k : Fin (prefixEnd m j + (m + blockWidth j)) :=
      ⟨start, lt_of_lt_of_le hprefix (Nat.le_add_right _ _)⟩
    refine ⟨⟨jf, k⟩, Finset.mem_univ _, ?_⟩
    simp [indexedFactor, jf, k, hprefix]
  · by_cases hmeet : ∃ q : ℕ, WindowMeetsTail m j start q
    · obtain ⟨q, hq⟩ := hmeet
      obtain ⟨offset, hoffset, heq⟩ :=
        window_eq_model_of_meets (by omega) hq
      let k : Fin (prefixEnd m j + (m + blockWidth j)) :=
        ⟨prefixEnd m j + offset, by omega⟩
      refine ⟨⟨jf, k⟩, Finset.mem_univ _, ?_⟩
      simp [indexedFactor, jf, k, Nat.not_lt.mpr (Nat.le_add_right _ _)]
      simpa [k] using heq.symm
    · let k : Fin (prefixEnd m j + (m + blockWidth j)) :=
        ⟨prefixEnd m j, by simp [blockWidth]⟩
      refine ⟨⟨jf, k⟩, Finset.mem_univ _, ?_⟩
      have hscaledzero : windowVector m (scaledExpansion m j) start = fun _ => 0 := by
        funext i
        apply scaledExpansion_eq_zero_of_outside (by omega)
        intro q hq
        exact hmeet ⟨q, ⟨i, hq⟩⟩
      have hmodelzero : modelWindow m j 0 = fun _ => 0 := by
        funext i
        simp [modelWindow, windowVector, modelExpansion,
          shiftExpansion, i.isLt]
      simp [indexedFactor, jf, k, Nat.not_lt.mpr (Nat.le_refl _)]
      exact (hscaledzero.trans hmodelzero.symm).symm

theorem observedFactors_card_lt_all_words (m : ℕ) (hm : 5 ≤ m) :
    (observedFactors m (2 ^ m)).card < Fintype.card (Fin m → Fin 10) := by
  calc
    (observedFactors m (2 ^ m)).card ≤ 40 * 4 ^ m :=
      observedFactors_card_le_forty m hm
    _ < 10 ^ m := forty_four_pow_lt_ten_pow m hm
    _ = Fintype.card (Fin m → Fin 10) := by simp

/-- A word omitted simultaneously from all scaled streams through depth
`2^m`; the fallback branch is irrelevant to the theorem's `m ≥ 5` range. -/
noncomputable def omittedVector (m : ℕ) : Fin m → Fin 10 :=
  if hm : 5 ≤ m then
    Classical.choose (show ∃ u : Fin m → Fin 10,
        u ∉ observedFactors m (2 ^ m) by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin m → Fin 10)) ⊆
          observedFactors m (2 ^ m) := fun u _ => hall u
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ] at hle
      exact (Nat.not_le_of_lt (observedFactors_card_lt_all_words m hm)) hle)
  else fun _ => 0

noncomputable def omittedWord (m : ℕ) : List (Fin 10) :=
  List.ofFn (omittedVector m)

@[simp] theorem omittedWord_length (m : ℕ) : (omittedWord m).length = m := by
  simp [omittedWord]

theorem omittedVector_not_mem (m : ℕ) (hm : 5 ≤ m) :
    omittedVector m ∉ observedFactors m (2 ^ m) := by
  rw [omittedVector, dif_pos hm]
  exact Classical.choose_spec (show ∃ u : Fin m → Fin 10,
      u ∉ observedFactors m (2 ^ m) by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin m → Fin 10)) ⊆
        observedFactors m (2 ^ m) := fun u _ => hall u
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    exact (Nat.not_le_of_lt (observedFactors_card_lt_all_words m hm)) hle)

theorem scaledExpansion_avoids_omittedWord
    {m j : ℕ} (hm : 5 ≤ m) (hj : j ≤ 2 ^ m) :
    AvoidsWord (omittedWord m) (scaledExpansion m j) := by
  intro start hocc
  apply omittedVector_not_mem m hm
  have hmem := windowVector_mem_observedFactors (m := m) hj (start := start)
  have heq : windowVector m (scaledExpansion m j) start = omittedVector m := by
    funext i
    have hi : i.val < (omittedWord m).length := by simp
    have hdigit := hocc ⟨i.val, hi⟩
    simpa [windowVector, omittedWord, List.get_eq_getElem] using hdigit
  rwa [heq] at hmem

/-- The explicit seed itself belongs to the endpoint-safe T44 core. -/
theorem xStarPoint_mem_Core (m : ℕ) (hm : 5 ≤ m) :
    xStarPoint ∈ Core (omittedWord m) (2 ^ m) := by
  intro n j hj
  refine ⟨streamShift n (scaledExpansion m j),
    avoidsWord_streamShift (omittedWord m) (scaledExpansion m j) n
      (scaledExpansion_avoids_omittedWord hm hj), ?_⟩
  rw [circleValue_streamShift, scaledExpansion_circleValue]
  exact circleMul_commute (10 ^ n) (16 ^ j) xStarPoint

theorem xStar_decimal_iterate_mem_Core
    (m n : ℕ) (hm : 5 ≤ m) :
    circleMul (10 ^ n) xStarPoint ∈ Core (omittedWord m) (2 ^ m) := by
  induction n with
  | zero => simpa [circleMul] using xStarPoint_mem_Core m hm
  | succ n ih =>
      have hnext := core_forward_timesTen_invariant (omittedWord m) (2 ^ m) ih
      change circleMul 10 (circleMul (10 ^ n) xStarPoint) ∈
        Core (omittedWord m) (2 ^ m) at hnext
      simpa [circleMul_comp, pow_succ, Nat.mul_comm] using hnext

theorem xStarOrbitClosure_subset_Core (m : ℕ) (hm : 5 ≤ m) :
    xStarOrbitClosure ⊆ Core (omittedWord m) (2 ^ m) := by
  apply closure_minimal
  · rintro _ ⟨n, rfl⟩
    exact xStar_decimal_iterate_mem_Core m n hm
  · exact core_isClosed (omittedWord m) (2 ^ m)

/-- Acceptance-facing sibling theorem.  The seed is fixed before `m`; the
selected exact-length word may vary with `m`; the radius is exactly `2^m`. -/
theorem fixed_seed_sibling_theorem :
    ∀ m : ℕ, 5 ≤ m →
      ∃ w : List (Fin 10), w.length = m ∧
        xStarOrbitClosure ⊆ Core w (2 ^ m) := by
  intro m hm
  exact ⟨omittedWord m, omittedWord_length m,
    xStarOrbitClosure_subset_Core m hm⟩

abbrev PositiveIndex := {q : ℕ // 1 ≤ q}

def positiveIndexEquiv : ℕ ≃ PositiveIndex where
  toFun q := ⟨q + 1, by omega⟩
  invFun q := q.val - 1
  left_inv q := by simp
  right_inv q := by
    apply Subtype.ext
    change q.val - 1 + 1 = q.val
    omega

/-- Literal one-based form of the real in the agenda statement. -/
theorem xStar_eq_series_one_based :
    xStar = ∑' q : PositiveIndex,
      (10 : ℝ) ^ (-(4 ^ q.val : ℕ) : ℤ) := by
  rw [xStar_eq_series]
  have h := positiveIndexEquiv.tsum_eq
    (fun q : PositiveIndex => (10 : ℝ) ^ (-(4 ^ q.val : ℕ) : ℤ))
  simpa [positiveIndexEquiv] using h

/-- One theorem exposing all statement-referee data: the literal fixed series,
irrationality, non-pi scope, exact radius and word length, finite factor bound,
all-window coverage, exact scaled values, avoidance, and orbit-closure Core
containment. -/
theorem fixed_seed_sibling_certificate :
    xStar = ∑' q : PositiveIndex,
        (10 : ℝ) ^ (-(4 ^ q.val : ℕ) : ℤ) ∧
      Irrational xStar ∧ xStar ≠ Real.pi ∧
      ∀ m : ℕ, 5 ≤ m →
        let R := 2 ^ m
        ∃ w : List (Fin 10),
          w.length = m ∧
          (observedFactors m R).card ≤ 40 * 4 ^ m ∧
          40 * 4 ^ m < 10 ^ m ∧
          (∀ j : ℕ, j ≤ R → ∀ start : ℕ,
            windowVector m (scaledExpansion m j) start ∈ observedFactors m R) ∧
          (∀ j : ℕ, j ≤ R →
            circleValue (scaledExpansion m j) = circleMul (16 ^ j) xStarPoint ∧
            AvoidsWord w (scaledExpansion m j)) ∧
          xStarOrbitClosure ⊆ Core w R := by
  refine ⟨xStar_eq_series_one_based, xStar_irrational, xStar_ne_pi, ?_⟩
  intro m hm
  dsimp only
  refine ⟨omittedWord m, omittedWord_length m,
    observedFactors_card_le_forty m hm, forty_four_pow_lt_ten_pow m hm,
    ?_, ?_, xStarOrbitClosure_subset_Core m hm⟩
  · intro j hj start
    exact windowVector_mem_observedFactors hj
  · intro j hj
    exact ⟨scaledExpansion_circleValue m j,
      scaledExpansion_avoids_omittedWord hm hj⟩

end DecimalFactorEntropy.T96FixedSeedSiblingExplicit

#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStar_eq_series
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStar_irrational
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStar_ne_pi
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.blockExpansion_ofDigits
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.splitEnd_le_two_width_add
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.prefixExpansion_ofDigits
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.tail_start_after_prefix
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.scaledExpansion_eq_tail
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.ofDigits_shiftExpansion
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.tailBlockExpansion_ofDigits
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.scaledTerm_eq_prefix_add_tsum_tail
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.scaledExpansion_ofDigits
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.finiteNumerator_div
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.scaledExpansion_circleValue
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.observedFactors_card_le_forty
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.forty_four_pow_lt_ten_pow
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.windowVector_mem_observedFactors
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.omittedWord_length
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStarPoint_mem_Core
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStarOrbitClosure_subset_Core
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.fixed_seed_sibling_theorem
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.xStar_eq_series_one_based
#print axioms DecimalFactorEntropy.T96FixedSeedSiblingExplicit.fixed_seed_sibling_certificate
