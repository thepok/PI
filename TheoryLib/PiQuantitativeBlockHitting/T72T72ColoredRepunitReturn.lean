import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.PiDigits.T21PiDigitsV1V3Relationship

/-!
# T72: colored repunit returns are exactly decimal disjunctivity

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For `P > 0`, the colors are the real grid points
`k / (10^P - 1)` with `0 <= k < 10^P - 1`.  A colored return means that the
base-ten fractional-part orbit comes arbitrarily close to every such point,
after every prescribed starting time.  The distance below is ordinary real
absolute value, not circle distance; in particular, a return to color zero
cannot be witnessed by an orbit point close to one.

This module proves that colored returns are equivalent to T20's base-ten
orbit density, and hence to canonical V1 for pi.  It does not prove either
side.  The reverse implication uses the explicit interior color
`(10 * a + 5) / (10^(m+1) - 1)` for the length-`m` cylinder with index `a`.
This keeps both the leading-zero cylinder and the all-nine cylinder strictly
away from their endpoints.
-/

noncomputable section

namespace Theory.PiDigits.T72ColoredRepunitReturn

/-- The length-`P` decimal repunit. -/
def repunit (P : ℕ) : ℕ :=
  10 ^ P - 1

theorem repunit_pos {P : ℕ} (hP : 0 < P) : 0 < repunit P := by
  unfold repunit
  exact Nat.sub_pos_of_lt (one_lt_pow₀ (by norm_num) hP.ne')

/-- The real point carrying residue color `k` at period `P`. -/
def repunitGridPoint (P : ℕ) (k : Fin (repunit P)) : ℝ :=
  (k.val : ℝ) / (repunit P : ℝ)

theorem repunitGridPoint_mem_Ico {P : ℕ} (hP : 0 < P)
    (k : Fin (repunit P)) :
    repunitGridPoint P k ∈ Set.Ico (0 : ℝ) 1 := by
  have hq : 0 < (repunit P : ℝ) := by
    exact_mod_cast repunit_pos hP
  constructor
  · exact div_nonneg (by positivity) hq.le
  · exact (div_lt_one hq).2 (by exact_mod_cast k.isLt)

/-- Every repunit color is approached arbitrarily accurately and arbitrarily
late by the real fractional-part orbit. -/
def ColoredRepunitReturns (x : ℝ) : Prop :=
  ∀ P : ℕ, 0 < P → ∀ k : Fin (repunit P), ∀ N : ℕ, ∀ ε : ℝ,
    0 < ε → ∃ n : ℕ, N ≤ n ∧
      |Theory.PiDigits.T20.baseTenOrbit x n - repunitGridPoint P k| < ε

/-- The first `m` floor-based decimal digits of a point. -/
def decimalPrefix (y : ℝ) (m : ℕ) : List (Fin 10) :=
  List.ofFn fun i : Fin m ↦ Theory.PiDigits.T20.decimalDigit y i.val

@[simp] theorem decimalPrefix_length (y : ℝ) (m : ℕ) :
    (decimalPrefix y m).length = m := by
  simp [decimalPrefix]

/-- Matching the first `m` digits gives the standard real, rather than
circle, distance bound.  This is the endpoint-safe ingredient at color zero.
-/
theorem abs_baseTenOrbit_sub_le_of_prefixMatch
    {x y : ℝ} (hx : 0 ≤ x) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    {n m : ℕ}
    (hmatch : ∀ i : Fin m,
      Theory.PiDigits.T20.decimalDigit x (n + i.val) =
        Theory.PiDigits.T20.decimalDigit y i.val) :
    |Theory.PiDigits.T20.baseTenOrbit x n - y| ≤ ((10 : ℝ) ^ m)⁻¹ := by
  have hprefix : ∀ i < m,
      Real.digits (Theory.PiDigits.T20.baseTenOrbit x n) 10 i =
        Real.digits y 10 i := by
    intro i hi
    change Theory.PiDigits.T20.decimalDigit
        (Theory.PiDigits.T20.baseTenOrbit x n) i =
      Theory.PiDigits.T20.decimalDigit y i
    exact (Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx n i).trans
      (hmatch ⟨i, hi⟩)
  have hclose := Real.abs_ofDigits_sub_ofDigits_le hprefix
  rw [Real.ofDigits_digits (by norm_num)
      (Theory.PiDigits.T20.baseTenOrbit_mem_Ico x n),
    Real.ofDigits_digits (by norm_num) hy] at hclose
  simpa [inv_pow] using hclose

/-- Decimal disjunctivity supplies all colored returns.  T21 is used here to
make every finite prefix occur after the prescribed threshold `N`. -/
theorem everyFiniteDecimalWord_implies_coloredRepunitReturns
    {x : ℝ} (hx : 0 ≤ x)
    (hwords : Theory.PiDigits.T20.EveryFiniteDecimalWord x) :
    ColoredRepunitReturns x := by
  have hgeneric : Theory.PiDigits.T21.EveryFiniteWordOccurs
      (Theory.PiDigits.T20.decimalDigit x) := by
    intro s
    obtain ⟨n, hn⟩ := hwords s
    exact ⟨n, hn⟩
  have hlate : Theory.PiDigits.T21.EveryFiniteWordOccursArbitrarilyLate
      (Theory.PiDigits.T20.decimalDigit x) :=
    (Theory.PiDigits.T21.everyFiniteWordOccurs_iff_arbitrarilyLate
      (Theory.PiDigits.T20.decimalDigit x)).mp hgeneric
  intro P hP k N ε hε
  let y : ℝ := repunitGridPoint P k
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := repunitGridPoint_mem_Ico hP k
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
    (by norm_num : (10 : ℝ)⁻¹ < 1)
  let s : List (Fin 10) := decimalPrefix y m
  obtain ⟨n, hnN, hn⟩ := hlate s N
  refine ⟨n, hnN, ?_⟩
  have hmatch : ∀ i : Fin m,
      Theory.PiDigits.T20.decimalDigit x (n + i.val) =
        Theory.PiDigits.T20.decimalDigit y i.val := by
    intro i
    have hi : i.val < s.length := by
      simpa only [s, decimalPrefix_length] using i.isLt
    simpa only [s, decimalPrefix, List.getElem_ofFn] using hn i.val hi
  exact (abs_baseTenOrbit_sub_le_of_prefixMatch hx hy hmatch).trans_lt
    (by simpa [inv_pow] using hm)

/-- A canonical color chosen strictly inside the decimal cylinder of `w`.
The trailing digit five makes the construction simultaneously safe for
leading-zero words and for the all-nine word. -/
def wordInteriorColor (w : List (Fin 10)) :
    Fin (repunit (w.length + 1)) := by
  refine ⟨10 * Theory.PiDigits.T20.wordValue w + 5, ?_⟩
  have hvalue := Theory.PiDigits.T20.wordValue_lt_pow_length w
  unfold repunit
  rw [pow_succ]
  omega

/-- The chosen repunit-grid point lies strictly inside the half-open cylinder
of `w`, including when `w` is all zeroes or all nines. -/
theorem wordInteriorGridPoint_mem_wordCylinder (w : List (Fin 10)) :
    repunitGridPoint (w.length + 1) (wordInteriorColor w) ∈
      Set.Ioo
        ((Theory.PiDigits.T20.wordValue w : ℝ) /
          (10 : ℝ) ^ w.length)
        (((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ w.length) := by
  let a : ℝ := Theory.PiDigits.T20.wordValue w
  let Q : ℝ := (10 : ℝ) ^ w.length
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ (by norm_num)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have haQ : a < Q := by
    dsimp [a, Q]
    exact_mod_cast Theory.PiDigits.T20.wordValue_lt_pow_length w
  have hdenNat : 0 < repunit (w.length + 1) := repunit_pos (by omega)
  have hden : 0 < (repunit (w.length + 1) : ℝ) := by
    exact_mod_cast hdenNat
  have hdenEq : (repunit (w.length + 1) : ℝ) = 10 * Q - 1 := by
    dsimp [repunit, Q]
    rw [pow_succ]
    norm_num
    ring
  have hcolorEq : ((wordInteriorColor w).val : ℝ) = 10 * a + 5 := by
    simp [wordInteriorColor, a]
  rw [repunitGridPoint, hdenEq, hcolorEq]
  simp only [Set.mem_Ioo, Nat.cast_add, Nat.cast_one]
  change a / Q < (10 * a + 5) / (10 * Q - 1) ∧
    (10 * a + 5) / (10 * Q - 1) < (a + 1) / Q
  constructor
  · rw [div_lt_div_iff₀ hQ (by linarith : 0 < 10 * Q - 1)]
    nlinarith
  · rw [div_lt_div_iff₀ (by linarith : 0 < 10 * Q - 1) hQ]
    nlinarith

/-- Colored returns hit every decimal cylinder.  The proof uses a positive
margin on both sides of the explicit interior color, so no decimal endpoint
convention is hidden in the argument. -/
theorem coloredRepunitReturns_implies_everyFiniteDecimalWord
    {x : ℝ} (hx : 0 ≤ x) (hreturns : ColoredRepunitReturns x) :
    Theory.PiDigits.T20.EveryFiniteDecimalWord x := by
  intro w
  let y : ℝ :=
    repunitGridPoint (w.length + 1) (wordInteriorColor w)
  let left : ℝ :=
    (Theory.PiDigits.T20.wordValue w : ℝ) / (10 : ℝ) ^ w.length
  let right : ℝ :=
    ((Theory.PiDigits.T20.wordValue w + 1 : ℕ) : ℝ) /
      (10 : ℝ) ^ w.length
  have hy : y ∈ Set.Ioo left right := by
    simpa only [y, left, right] using wordInteriorGridPoint_mem_wordCylinder w
  let ε : ℝ := min (y - left) (right - y)
  have hε : 0 < ε := by
    exact lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)
  obtain ⟨n, -, hn⟩ :=
    hreturns (w.length + 1) (by omega) (wordInteriorColor w) 0 ε hε
  have hmem : Theory.PiDigits.T20.baseTenOrbit x n ∈ Set.Ico left right := by
    rw [abs_lt] at hn
    dsimp [ε] at hn
    constructor <;> linarith [min_le_left (y - left) (right - y),
      min_le_right (y - left) (right - y)]
  refine ⟨n, ?_⟩
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder w
    (Theory.PiDigits.T20.baseTenOrbit x n) (by
      simpa only [left, right] using hmem)
  intro i hi
  exact (Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx n i).symm.trans
    (hdigits i hi)

/-- Exact generic equivalence between decimal disjunctivity and arbitrarily
late approximation of every repunit color. -/
theorem everyFiniteDecimalWord_iff_coloredRepunitReturns
    (x : ℝ) (hx : 0 ≤ x) :
    Theory.PiDigits.T20.EveryFiniteDecimalWord x ↔
      ColoredRepunitReturns x :=
  ⟨everyFiniteDecimalWord_implies_coloredRepunitReturns hx,
    coloredRepunitReturns_implies_everyFiniteDecimalWord hx⟩

/-- T20's metric orbit-density statement is exactly the colored-return
criterion.  This is an equivalence only; neither side is asserted for pi. -/
theorem baseTenOrbitDense_iff_coloredRepunitReturns
    (x : ℝ) (hx : 0 ≤ x) :
    Theory.PiDigits.T20.BaseTenOrbitDense x ↔ ColoredRepunitReturns x := by
  constructor
  · intro hdense
    exact everyFiniteDecimalWord_implies_coloredRepunitReturns hx
      ((Theory.PiDigits.T20.everyFiniteDecimalWord_iff_baseTenOrbitDense
        x hx).mpr hdense)
  · intro hreturns
    exact (Theory.PiDigits.T20.everyFiniteDecimalWord_iff_baseTenOrbitDense
      x hx).mp
        (coloredRepunitReturns_implies_everyFiniteDecimalWord hx hreturns)

/-- Canonical V1 for pi is exactly the statement that its decimal orbit
approximates every residue color `k/(10^P-1)`, to every precision and after
every threshold.  The theorem leaves this common proposition open. -/
theorem canonicalV1_iff_coloredRepunitReturns :
    Theory.PiDigits.V1 ↔ ColoredRepunitReturns Real.pi := by
  exact Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense.trans
    (baseTenOrbitDense_iff_coloredRepunitReturns Real.pi Real.pi_pos.le)

end Theory.PiDigits.T72ColoredRepunitReturn

#print axioms Theory.PiDigits.T72ColoredRepunitReturn.repunit_pos
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.repunitGridPoint_mem_Ico
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.decimalPrefix_length
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.abs_baseTenOrbit_sub_le_of_prefixMatch
#print axioms
  Theory.PiDigits.T72ColoredRepunitReturn.everyFiniteDecimalWord_implies_coloredRepunitReturns
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.wordInteriorGridPoint_mem_wordCylinder
#print axioms
  Theory.PiDigits.T72ColoredRepunitReturn.coloredRepunitReturns_implies_everyFiniteDecimalWord
#print axioms
  Theory.PiDigits.T72ColoredRepunitReturn.everyFiniteDecimalWord_iff_coloredRepunitReturns
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.baseTenOrbitDense_iff_coloredRepunitReturns
#print axioms Theory.PiDigits.T72ColoredRepunitReturn.canonicalV1_iff_coloredRepunitReturns
