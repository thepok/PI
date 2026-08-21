import TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# T16: deterministic decimal boundary-word obstruction

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

This file imports T14's Fejer estimates and formalizes only the deterministic
decimal translation of its boundary branch.  Every final theorem is a
necessary consequence of a missing word or of `not C1`; there is no converse.
No estimate for either pi-specific branch is supplied, so this file neither
proves nor refutes C1.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.DecimalBoundaryWordObstruction

open Theory.PiDigits.BoundaryRobustFejerDichotomy
open Theory.PiDigits.QuantitativeBlockHitting

/-- The unique little-endian numeral padded to `ell` digits, displayed in the
usual most-significant-digit-first order and coerced to decimal digits. -/
def fixedWord (ell b : ℕ) : List (Fin 10) :=
  (Nat.digitsAppend 10 ell b).reverse.map (Fin.ofNat 10)

/-- The T20 numerical value agrees with `Nat.ofDigits` on reversed values. -/
theorem wordValue_eq_ofDigits (w : List (Fin 10)) :
    Theory.PiDigits.T20.wordValue w =
      Nat.ofDigits 10 (w.map Fin.val).reverse := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      rw [Theory.PiDigits.T20.wordValue, List.map_cons, List.reverse_cons,
        Nat.ofDigits_append, ih]
      simp
      ring

theorem fixedWord_length {ell b : ℕ} (hb : b < 10 ^ ell) :
    (fixedWord ell b).length = ell := by
  simp [fixedWord, Nat.length_digitsAppend (by norm_num : 1 < 10) ell hb]

theorem fixedWord_map_val {ell b : ℕ} (hb : b < 10 ^ ell) :
    (fixedWord ell b).map Fin.val = (Nat.digitsAppend 10 ell b).reverse := by
  unfold fixedWord
  rw [List.map_map]
  calc
    List.map (Fin.val ∘ Fin.ofNat 10) (Nat.digitsAppend 10 ell b).reverse =
        List.map id (Nat.digitsAppend 10 ell b).reverse := by
      apply List.map_congr_left
      intro d hd
      rw [List.mem_reverse] at hd
      have hdlt := Nat.lt_of_mem_digitsAppend
        (by norm_num : 1 < 10) ell d hd
      exact Nat.mod_eq_of_lt hdlt
    _ = (Nat.digitsAppend 10 ell b).reverse := by simp

theorem fixedWord_value {ell b : ℕ} (hb : b < 10 ^ ell) :
    Theory.PiDigits.T20.wordValue (fixedWord ell b) = b := by
  rw [wordValue_eq_ofDigits, fixedWord_map_val hb, List.reverse_reverse]
  exact (Nat.setInvOn_digitsAppend_ofDigits (by norm_num : 1 < 10) ell).2 hb

theorem wordValue_append (u v : List (Fin 10)) :
    Theory.PiDigits.T20.wordValue (u ++ v) =
      Theory.PiDigits.T20.wordValue u * 10 ^ v.length +
        Theory.PiDigits.T20.wordValue v := by
  induction u with
  | nil => simp [Theory.PiDigits.T20.wordValue]
  | cons d u ih =>
      simp only [List.cons_append, Theory.PiDigits.T20.wordValue, List.length_append,
        List.length_cons, ih]
      rw [pow_add]
      ring

theorem wordValue_replicate_zero (r : ℕ) :
    Theory.PiDigits.T20.wordValue (List.replicate r (0 : Fin 10)) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [List.replicate_succ, Theory.PiDigits.T20.wordValue, ih]

theorem wordValue_replicate_nine (r : ℕ) :
    Theory.PiDigits.T20.wordValue (List.replicate r (9 : Fin 10)) =
      10 ^ r - 1 := by
  induction r with
  | zero => simp [T20.wordValue]
  | succ r ih =>
      rw [List.replicate_succ, Theory.PiDigits.T20.wordValue,
        List.length_replicate, ih,
        pow_succ']
      omega

theorem wordValue_injective_of_length {u v : List (Fin 10)}
    (hlen : u.length = v.length)
    (hvalue : Theory.PiDigits.T20.wordValue u =
      Theory.PiDigits.T20.wordValue v) :
    u = v := by
  rw [wordValue_eq_ofDigits, wordValue_eq_ofDigits] at hvalue
  have hraw : (u.map Fin.val).reverse = (v.map Fin.val).reverse := by
    apply Nat.ofDigits_inj_of_len_eq (by norm_num : 1 < (10 : ℕ))
    · simp [hlen]
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · exact hvalue
  have hmapped : u.map Fin.val = v.map Fin.val := by
    simpa using congrArg List.reverse hraw
  exact (List.map_injective_iff.mpr Fin.val_injective) hmapped

theorem fixedWord_eq_of_length_value {ell b : ℕ} (hb : b < 10 ^ ell)
    (w : List (Fin 10)) (hlen : w.length = ell)
    (hvalue : Theory.PiDigits.T20.wordValue w = b) :
    fixedWord ell b = w := by
  apply wordValue_injective_of_length
  · rw [fixedWord_length hb, hlen]
  · rw [fixedWord_value hb, hvalue]

theorem fixedWord_mul_pow_eq_append_zero {ell r b : ℕ}
    (hb : b < 10 ^ ell) :
    fixedWord (ell + r) (b * 10 ^ r) =
      fixedWord ell b ++ List.replicate r (0 : Fin 10) := by
  have hs : 0 < 10 ^ r := by positivity
  have hbound : b * 10 ^ r < 10 ^ (ell + r) := by
    rw [pow_add]
    exact (Nat.mul_lt_mul_right hs).mpr hb
  apply fixedWord_eq_of_length_value hbound
  · simp [fixedWord_length hb]
  · rw [wordValue_append, fixedWord_value hb, wordValue_replicate_zero]
    simp

theorem fixedWord_mul_pow_add_pred_eq_append_nine {ell r b : ℕ}
    (hb : b < 10 ^ ell) :
    fixedWord (ell + r) (b * 10 ^ r + (10 ^ r - 1)) =
      fixedWord ell b ++ List.replicate r (9 : Fin 10) := by
  have hs : 0 < 10 ^ r := by positivity
  have hsucc : b + 1 ≤ 10 ^ ell := Nat.succ_le_iff.mpr hb
  have hbound : b * 10 ^ r + (10 ^ r - 1) < 10 ^ (ell + r) := by
    rw [pow_add]
    calc
      b * 10 ^ r + (10 ^ r - 1) < b * 10 ^ r + 10 ^ r :=
        Nat.add_lt_add_left (Nat.sub_lt hs (by omega)) _
      _ = (b + 1) * 10 ^ r := by rw [Nat.add_mul, one_mul]
      _ ≤ 10 ^ ell * 10 ^ r := Nat.mul_le_mul_right _ hsucc
  apply fixedWord_eq_of_length_value hbound
  · simp [fixedWord_length hb]
  · rw [wordValue_append, fixedWord_value hb, wordValue_replicate_nine]
    simp

theorem fixedWord_zero_eq_replicate_zero (ell : ℕ) :
    fixedWord ell 0 = List.replicate ell (0 : Fin 10) := by
  apply fixedWord_eq_of_length_value (by positivity : 0 < 10 ^ ell)
  · simp
  · rw [wordValue_replicate_zero]

theorem fixedWord_pow_sub_one_eq_replicate_nine (ell : ℕ) :
    fixedWord ell (10 ^ ell - 1) = List.replicate ell (9 : Fin 10) := by
  have hp : 0 < 10 ^ ell := by positivity
  apply fixedWord_eq_of_length_value (Nat.sub_lt hp (by omega))
  · simp
  · rw [wordValue_replicate_nine]

/-- Canonical predecessor fine-cylinder label. -/
def predecessorLabel (q s a : ℕ) : ℕ := (a * s + q * s - 1) % (q * s)

/-- Fine cylinder immediately to the right of the left coarse boundary. -/
def leftInteriorLabel (s a : ℕ) : ℕ := a * s

/-- Fine cylinder immediately to the left of the right coarse boundary. -/
def rightInteriorLabel (s a : ℕ) : ℕ := (a + 1) * s - 1

/-- Canonical successor fine-cylinder label. -/
def successorLabel (q s a : ℕ) : ℕ := ((a + 1) * s) % (q * s)

theorem boundaryLabels_canonical {q s a : ℕ} (hq : 0 < q) (hs : 0 < s)
    (ha : a < q) :
    predecessorLabel q s a < q * s ∧
      leftInteriorLabel s a < q * s ∧
      rightInteriorLabel s a < q * s ∧
      successorLabel q s a < q * s := by
  have hqs : 0 < q * s := Nat.mul_pos hq hs
  have has : a * s < q * s := (Nat.mul_lt_mul_right hs).mpr ha
  have hasucc : (a + 1) * s ≤ q * s :=
    Nat.mul_le_mul_right s (Nat.succ_le_iff.mpr ha)
  refine ⟨Nat.mod_lt _ hqs, has, ?_, Nat.mod_lt _ hqs⟩
  unfold rightInteriorLabel
  omega

/-- All ordinary borrow/carry formulas and both circular wraparounds. -/
theorem boundaryLabels_complete_carry_audit {q s a : ℕ}
    (hq : 0 < q) (hs : 0 < s) (ha : a < q) :
    (a = 0 → predecessorLabel q s a = q * s - 1) ∧
    (0 < a → predecessorLabel q s a = (a - 1) * s + (s - 1)) ∧
    leftInteriorLabel s a = a * s ∧
    rightInteriorLabel s a = a * s + (s - 1) ∧
    (a + 1 < q → successorLabel q s a = (a + 1) * s) ∧
    (a + 1 = q → successorLabel q s a = 0) := by
  have hqs : 0 < q * s := Nat.mul_pos hq hs
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro ha0
    subst a
    unfold predecessorLabel
    simp only [zero_mul, zero_add]
    exact Nat.mod_eq_of_lt (Nat.sub_lt hqs (by omega))
  · intro ha0
    unfold predecessorLabel
    have has0 : 0 < a * s := Nat.mul_pos ha0 hs
    have haslt : a * s < q * s := (Nat.mul_lt_mul_right hs).mpr ha
    have hrearrange : a * s + q * s - 1 = q * s + (a * s - 1) := by
      omega
    have hsublt : a * s - 1 < q * s := (Nat.sub_le _ _).trans_lt haslt
    rw [hrearrange]
    simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.zero_mod, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt hsublt]
    calc
      a * s - 1 = ((a - 1) + 1) * s - 1 := by
        rw [Nat.sub_add_cancel ha0]
      _ = (a - 1) * s + s - 1 := by rw [Nat.add_mul, one_mul]
      _ = (a - 1) * s + (s - 1) := by omega
  · unfold rightInteriorLabel
    rw [Nat.add_mul, one_mul]
    omega
  · intro hasucc
    unfold successorLabel
    exact Nat.mod_eq_of_lt ((Nat.mul_lt_mul_right hs).mpr hasucc)
  · intro hasucc
    unfold successorLabel
    rw [hasucc, Nat.mod_self]

/-- The predecessor, two interiors, and successor are four distinct canonical
labels whenever both decimal scales have at least two cells. -/
theorem boundaryLabels_pairwise_distinct {q s a : ℕ}
    (hq : 2 ≤ q) (hs : 2 ≤ s) (ha : a < q) :
    predecessorLabel q s a ≠ leftInteriorLabel s a ∧
    predecessorLabel q s a ≠ rightInteriorLabel s a ∧
    predecessorLabel q s a ≠ successorLabel q s a ∧
    leftInteriorLabel s a ≠ rightInteriorLabel s a ∧
    leftInteriorLabel s a ≠ successorLabel q s a ∧
    rightInteriorLabel s a ≠ successorLabel q s a := by
  have hq0 : 0 < q := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨hPzero, hPpos, _hL, hR, hSordinary, hSwrap⟩ :=
    boundaryLabels_complete_carry_audit hq0 hs0 ha
  have hPdirect : 0 < a → predecessorLabel q s a = a * s - 1 := by
    intro ha0
    rw [hPpos ha0]
    calc
      (a - 1) * s + (s - 1) = ((a - 1) + 1) * s - 1 := by
        rw [Nat.add_mul, one_mul]
        omega
      _ = a * s - 1 := by rw [Nat.sub_add_cancel ha0]
  have hRdirect : rightInteriorLabel s a = a * s + s - 1 := by
    rw [hR]
    omega
  by_cases ha0 : a = 0
  · subst a
    have hS : successorLabel q s 0 = s := by
      simpa using hSordinary (by omega)
    have hsQ : s < q * s := by
      simpa only [one_mul] using
        (Nat.mul_lt_mul_right hs0).mpr (by omega : 1 < q)
    have hsPred : s ≤ q * s - 1 := by omega
    have hQpos : 0 < q * s := Nat.mul_pos hq0 hs0
    have hprod : 4 ≤ q * s := by
      have := Nat.mul_le_mul hq hs
      norm_num at this ⊢
      exact this
    have htwoS : s + s ≤ q * s := by
      have := Nat.mul_le_mul_right s hq
      simpa [two_mul] using this
    have hsPredStrict : s < q * s - 1 := by omega
    have hP0 : predecessorLabel q s 0 = q * s - 1 := hPzero rfl
    rw [hP0, hS]
    simp only [leftInteriorLabel, rightInteriorLabel, zero_mul, zero_add,
      one_mul]
    omega
  by_cases hawrap : a + 1 = q
  · have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
    have hP := hPdirect ha0'
    have hS := hSwrap hawrap
    have haS : 2 ≤ a * s := by
      have hmul : 1 * 2 ≤ a * s := Nat.mul_le_mul (by omega) hs
      simpa using hmul
    have haSQ : a * s < q * s := (Nat.mul_lt_mul_right hs0).mpr ha
    rw [hP, hRdirect, hS]
    unfold leftInteriorLabel
    have hright : a * s + s = q * s := by
      calc
        a * s + s = (a + 1) * s := by rw [Nat.add_mul, one_mul]
        _ = q * s := by rw [hawrap]
    omega
  · have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
    have hP := hPdirect ha0'
    have hS : successorLabel q s a = a * s + s := by
      rw [hSordinary (by omega), Nat.add_mul, one_mul]
    rw [hP, hRdirect, hS]
    unfold leftInteriorLabel
    have haS : 0 < a * s := Nat.mul_pos ha0' hs0
    omega

/-- The four labels are exactly the padded predecessor, two padded interior
words, and padded successor, including the zero/one wraparound words. -/
theorem boundaryWords_complete_carry_audit {k r a : ℕ}
    (hk : 0 < k) (hr : 0 < r) (ha : a < 10 ^ k) :
    let q : ℕ := 10 ^ k
    let s : ℕ := 10 ^ r
    let Q : ℕ := 10 ^ (k + r)
    fixedWord (k + r) (leftInteriorLabel s a) =
        fixedWord k a ++ List.replicate r (0 : Fin 10) ∧
    fixedWord (k + r) (rightInteriorLabel s a) =
        fixedWord k a ++ List.replicate r (9 : Fin 10) ∧
    (0 < a → fixedWord (k + r) (predecessorLabel q s a) =
        fixedWord k (a - 1) ++ List.replicate r (9 : Fin 10)) ∧
    (a = 0 → fixedWord (k + r) (predecessorLabel q s a) =
        List.replicate (k + r) (9 : Fin 10)) ∧
    (a + 1 < q → fixedWord (k + r) (successorLabel q s a) =
        fixedWord k (a + 1) ++ List.replicate r (0 : Fin 10)) ∧
    (a + 1 = q → fixedWord (k + r) (successorLabel q s a) =
        List.replicate (k + r) (0 : Fin 10)) ∧
    q * s = Q := by
  dsimp only
  have hq : 0 < 10 ^ k := by positivity
  have hs : 0 < 10 ^ r := by positivity
  obtain ⟨hPzero, hPpos, _hL, hR, hSordinary, hSwrap⟩ :=
    boundaryLabels_complete_carry_audit hq hs ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold leftInteriorLabel
    exact fixedWord_mul_pow_eq_append_zero ha
  · rw [hR]
    exact fixedWord_mul_pow_add_pred_eq_append_nine ha
  · intro ha0
    rw [hPpos ha0]
    apply fixedWord_mul_pow_add_pred_eq_append_nine
    exact (Nat.sub_le a 1).trans_lt ha
  · intro ha0
    rw [hPzero ha0]
    simpa only [pow_add] using fixedWord_pow_sub_one_eq_replicate_nine (k + r)
  · intro hasucc
    rw [hSordinary hasucc]
    exact fixedWord_mul_pow_eq_append_zero hasucc
  · intro hasucc
    rw [hSwrap hasucc]
    exact fixedWord_zero_eq_replicate_zero (k + r)
  · exact (pow_add 10 k r).symm

/-- Strict circular distance is witnessed by one integer translate. -/
theorem circularDistance_lt_iff_exists_int (x y rho : ℝ) :
    circularDistance x y < rho ↔ ∃ z : ℤ, |x - y - z| < rho := by
  constructor
  · intro h
    obtain ⟨v, ⟨z, rfl⟩, hv⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty fun z : ℤ => |x - y - z|) h
    exact ⟨z, hv⟩
  · rintro ⟨z, hz⟩
    exact (circularDistance_le_abs_sub_int x y z).trans_lt hz

/-- A canonical representative is not a `Q`-adic grid endpoint. -/
def AvoidsGridEndpoints (Q : ℕ) (x : ℝ) : Prop :=
  ∀ j < Q, x ≠ (j : ℝ) / Q

/-- No canonical point of the pi orbit is an exact decimal-grid endpoint. -/
theorem piFractionalOrbit_avoids_grid_endpoints (n Q : ℕ) (hQ : 0 < Q) :
    AvoidsGridEndpoints Q (Theory.PiDigits.T27.piFractionalOrbit n) := by
  intro j hj hhit
  let y : ℝ := (10 : ℝ) ^ n * Real.pi
  let z : ℤ := ⌊y⌋
  let A : ℤ := (Q : ℤ) * z + j
  let D : ℤ := (Q : ℤ) * (10 ^ n : ℤ)
  have hQreal : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hpowreal : (10 : ℝ) ^ n ≠ 0 := by positivity
  have hfract : Int.fract y = (j : ℝ) / Q := by
    simpa [Theory.PiDigits.T27.piFractionalOrbit, y] using hhit
  have hy : y = (z : ℝ) + (j : ℝ) / Q := by
    rw [Int.fract] at hfract
    dsimp only [z]
    linarith
  have hD : D ≠ 0 := by
    dsimp only [D]
    exact mul_ne_zero (by exact_mod_cast hQ.ne') (by positivity)
  apply (irrational_pi.ne_rational A D)
  dsimp only [A, D]
  push_cast
  dsimp only [y] at hy
  field_simp
  field_simp at hy
  nlinarith

theorem circularDistance_one_lt_iff_zero_lt (x rho : ℝ) :
    circularDistance x 1 < rho ↔ circularDistance x 0 < rho := by
  rw [circularDistance_lt_iff_exists_int,
    circularDistance_lt_iff_exists_int]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z + 1, ?_⟩
    convert hz using 1 <;> push_cast <;> ring
  · rintro ⟨z, hz⟩
    refine ⟨z - 1, ?_⟩
    convert hz using 1 <;> push_cast <;> ring

theorem circular_zero_boundary_iff_adjacent_cells
    {Q : ℕ} {x : ℝ} (hQ : 0 < Q)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hendpoint : AvoidsGridEndpoints Q x) :
    circularDistance x 0 < 1 / Q ↔
      inCylinder Q (Q - 1) x ∨ inCylinder Q 0 x := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hrpos : (0 : ℝ) < 1 / Q := div_pos zero_lt_one hQR
  have hrle : (1 : ℝ) / Q ≤ 1 := (div_le_one hQR).2 hQone
  have hpredlt : Q - 1 < Q := Nat.sub_lt hQ (by omega)
  have hleft : (((Q - 1 : ℕ) : ℝ) / Q) = 1 - 1 / Q := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    field_simp
  constructor
  · rw [circularDistance_lt_iff_exists_int]
    rintro ⟨z, hz⟩
    rw [sub_zero, abs_lt] at hz
    have hzloR : (-1 : ℝ) < (z : ℝ) := by linarith [hx.1]
    have hzhiR : (z : ℝ) < 2 := by linarith [hx.2]
    have hzlo : (-1 : ℤ) < z := by exact_mod_cast hzloR
    have hzhi : z < (2 : ℤ) := by exact_mod_cast hzhiR
    have hzcase : z = 0 ∨ z = 1 := by omega
    rcases hzcase with rfl | rfl
    · right
      unfold inCylinder cylinderLeft cylinderRight
      constructor
      · simpa using hx.1
      · simpa using hz.2
    · left
      unfold inCylinder cylinderLeft cylinderRight
      rw [show Q - 1 + 1 = Q by omega, hleft]
      constructor
      · norm_num at hz
        rw [one_div]
        linarith [hz.1]
      · simpa only [Nat.cast_ofNat, div_self hQR.ne'] using hx.2
  · intro hcell
    rw [circularDistance_lt_iff_exists_int]
    rcases hcell with hleftCell | hrightCell
    · refine ⟨1, ?_⟩
      unfold inCylinder cylinderLeft cylinderRight at hleftCell
      rw [show Q - 1 + 1 = Q by omega, hleft] at hleftCell
      have hne := hendpoint (Q - 1) hpredlt
      have hstrict : 1 - 1 / (Q : ℝ) < x :=
        lt_of_le_of_ne hleftCell.1 (by simpa [hleft] using hne.symm)
      rw [abs_lt]
      push_cast
      rw [one_div] at hstrict ⊢
      have hxone : x < 1 := by
        simpa only [div_self hQR.ne'] using hleftCell.2
      constructor <;> linarith
    · refine ⟨0, ?_⟩
      unfold inCylinder cylinderLeft cylinderRight at hrightCell
      rw [abs_lt]
      push_cast
      norm_num at hrightCell ⊢
      constructor
      · exact lt_of_lt_of_le (neg_lt_zero.mpr (inv_pos.mpr hQR)) hrightCell.1
      · exact hrightCell.2

theorem circular_interior_boundary_iff_adjacent_cells
    {Q m : ℕ} {x : ℝ} (hQ : 0 < Q) (hm0 : 0 < m) (hmQ : m < Q)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hendpoint : AvoidsGridEndpoints Q x) :
    circularDistance x ((m : ℝ) / Q) < 1 / Q ↔
      inCylinder Q (m - 1) x ∨ inCylinder Q m x := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrpos : (0 : ℝ) < 1 / Q := div_pos zero_lt_one hQR
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hmLower : (1 : ℝ) / Q ≤ (m : ℝ) / Q :=
    (div_le_div_iff_of_pos_right hQR).2 hmone
  have hmsucc : m + 1 ≤ Q := Nat.succ_le_iff.mpr hmQ
  have hmUpper : (m : ℝ) / Q + 1 / Q ≤ 1 := by
    calc
      (m : ℝ) / Q + 1 / Q = ((m + 1 : ℕ) : ℝ) / Q := by
        push_cast
        ring
      _ ≤ 1 := (div_le_one hQR).2 (by exact_mod_cast hmsucc)
  have hleft : (((m - 1 : ℕ) : ℝ) / Q) = (m : ℝ) / Q - 1 / Q := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    ring
  have hright : (((m + 1 : ℕ) : ℝ) / Q) = (m : ℝ) / Q + 1 / Q := by
    push_cast
    ring
  constructor
  · rw [circularDistance_lt_iff_exists_int]
    rintro ⟨z, hz⟩
    rw [abs_lt] at hz
    have hzltR : (z : ℝ) < 1 := by linarith [hx.2]
    have hzgtR : (-1 : ℝ) < (z : ℝ) := by linarith [hx.1]
    have hzlt : z < (1 : ℤ) := by exact_mod_cast hzltR
    have hzgt : (-1 : ℤ) < z := by exact_mod_cast hzgtR
    have hz0 : z = 0 := by omega
    subst z
    norm_num at hz
    have hzlower : (m : ℝ) / Q - 1 / Q < x := by
      rw [one_div]
      linarith [hz.1]
    have hzupper : x < (m : ℝ) / Q + 1 / Q := by
      rw [one_div]
      linarith [hz.2]
    by_cases hxm : x < (m : ℝ) / Q
    · left
      unfold inCylinder cylinderLeft cylinderRight
      rw [show m - 1 + 1 = m by omega, hleft]
      exact ⟨hzlower.le, hxm⟩
    · right
      unfold inCylinder cylinderLeft cylinderRight
      rw [hright]
      exact ⟨le_of_not_gt hxm, hzupper⟩
  · intro hcell
    rw [circularDistance_lt_iff_exists_int]
    refine ⟨0, ?_⟩
    rw [abs_lt]
    push_cast
    rcases hcell with hleftCell | hrightCell
    · unfold inCylinder cylinderLeft cylinderRight at hleftCell
      rw [show m - 1 + 1 = m by omega, hleft] at hleftCell
      have hne := hendpoint (m - 1) (by omega)
      have hstrict : (m : ℝ) / Q - 1 / Q < x :=
        lt_of_le_of_ne hleftCell.1 (by simpa [hleft] using hne.symm)
      constructor <;> linarith [hleftCell.2]
    · unfold inCylinder cylinderLeft cylinderRight at hrightCell
      rw [hright] at hrightCell
      constructor <;> linarith [hrightCell.1, hrightCell.2]

/-- Exact classification of a strict `1/Q` circular neighborhood of a grid
point.  The endpoint hypothesis is necessary because the cells are half-open. -/
theorem circular_grid_boundary_iff_adjacent_cells
    {Q m : ℕ} {x : ℝ} (hQ : 0 < Q) (hm : m ≤ Q)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hendpoint : AvoidsGridEndpoints Q x) :
    circularDistance x ((m : ℝ) / Q) < 1 / Q ↔
      inCylinder Q ((m + Q - 1) % Q) x ∨ inCylinder Q (m % Q) x := by
  by_cases hm0 : m = 0
  · subst m
    have hpred : (Q - 1) % Q = Q - 1 :=
      Nat.mod_eq_of_lt (Nat.sub_lt hQ (by omega))
    simpa [hpred] using
      circular_zero_boundary_iff_adjacent_cells hQ hx hendpoint
  by_cases hmQ : m = Q
  · subst m
    have hpred : (Q + Q - 1) % Q = Q - 1 := by
      have hrearrange : Q + Q - 1 = Q + (Q - 1) := by omega
      rw [hrearrange, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (Nat.sub_lt hQ (by omega))]
    rw [show ((Q : ℝ) / Q) = 1 by field_simp,
      circularDistance_one_lt_iff_zero_lt, hpred, Nat.mod_self]
    exact circular_zero_boundary_iff_adjacent_cells hQ hx hendpoint
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmlt : m < Q := lt_of_le_of_ne hm hmQ
  have hpred : (m + Q - 1) % Q = m - 1 := by
    have hrearrange : m + Q - 1 = Q + (m - 1) := by omega
    rw [hrearrange, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  rw [hpred, Nat.mod_eq_of_lt hmlt]
  exact circular_interior_boundary_iff_adjacent_cells
    hQ hmpos hmlt hx hendpoint

/-- At decimal scales, the two strict coarse-boundary neighborhoods are
exactly the predecessor/interior/interior/successor fine cylinders. -/
theorem pi_twoBoundary_iff_four_fine_cylinders
    {k r a n : ℕ} (hk : 0 < k) (hr : 0 < r) (ha : a < 10 ^ k) :
    let q : ℕ := 10 ^ k
    let s : ℕ := 10 ^ r
    let Q : ℕ := 10 ^ (k + r)
    circularDistance (Theory.PiDigits.T27.piFractionalOrbit n)
          (cylinderLeft q a) < 1 / (Q : ℝ) ∨
        circularDistance (Theory.PiDigits.T27.piFractionalOrbit n)
          (cylinderRight q a) < 1 / (Q : ℝ) ↔
      inCylinder Q (predecessorLabel q s a)
          (Theory.PiDigits.T27.piFractionalOrbit n) ∨
      inCylinder Q (leftInteriorLabel s a)
          (Theory.PiDigits.T27.piFractionalOrbit n) ∨
      inCylinder Q (rightInteriorLabel s a)
          (Theory.PiDigits.T27.piFractionalOrbit n) ∨
      inCylinder Q (successorLabel q s a)
          (Theory.PiDigits.T27.piFractionalOrbit n) := by
  dsimp only
  let x := Theory.PiDigits.T27.piFractionalOrbit n
  have hq : 0 < 10 ^ k := by positivity
  have hs : 0 < 10 ^ r := by positivity
  have hQ : 0 < 10 ^ (k + r) := by positivity
  have hQeq : 10 ^ k * 10 ^ r = 10 ^ (k + r) := (pow_add 10 k r).symm
  have hx : x ∈ Set.Ico (0 : ℝ) 1 :=
    Theory.PiDigits.T27.piFractionalOrbit_mem_Ico n
  have hend : AvoidsGridEndpoints (10 ^ (k + r)) x :=
    piFractionalOrbit_avoids_grid_endpoints n _ hQ
  have hmL : a * 10 ^ r ≤ 10 ^ (k + r) := by
    rw [← hQeq]
    exact Nat.mul_le_mul_right _ ha.le
  have hcenterL : (((a * 10 ^ r : ℕ) : ℝ) / (10 ^ (k + r) : ℕ)) =
      (a : ℝ) / (10 ^ k : ℕ) := by
    rw [← hQeq]
    push_cast
    field_simp
  have hP : (a * 10 ^ r + 10 ^ (k + r) - 1) % 10 ^ (k + r) =
      predecessorLabel (10 ^ k) (10 ^ r) a := by
    rw [← hQeq]
    rfl
  have hL : (a * 10 ^ r) % 10 ^ (k + r) = leftInteriorLabel (10 ^ r) a := by
    unfold leftInteriorLabel
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le
      ((Nat.mul_lt_mul_right hs).mpr ha) (by rw [hQeq]))
  have hleftiff := circular_grid_boundary_iff_adjacent_cells
    (Q := 10 ^ (k + r)) (m := a * 10 ^ r) (x := x) hQ hmL hx hend
  rw [hcenterL, hP, hL] at hleftiff
  have hmR : (a + 1) * 10 ^ r ≤ 10 ^ (k + r) := by
    rw [← hQeq]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr ha)
  have hmRpos : 0 < (a + 1) * 10 ^ r := Nat.mul_pos (by omega) hs
  have hcenterR : ((((a + 1) * 10 ^ r : ℕ) : ℝ) /
      (10 ^ (k + r) : ℕ)) = ((a + 1 : ℕ) : ℝ) / (10 ^ k : ℕ) := by
    rw [← hQeq]
    push_cast
    field_simp
  have hR : ((a + 1) * 10 ^ r + 10 ^ (k + r) - 1) % 10 ^ (k + r) =
      rightInteriorLabel (10 ^ r) a := by
    have hsub : (a + 1) * 10 ^ r - 1 < 10 ^ (k + r) := by omega
    have hrearrange : (a + 1) * 10 ^ r + 10 ^ (k + r) - 1 =
        10 ^ (k + r) + ((a + 1) * 10 ^ r - 1) := by omega
    rw [hrearrange, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hsub]
    rfl
  have hS : ((a + 1) * 10 ^ r) % 10 ^ (k + r) =
      successorLabel (10 ^ k) (10 ^ r) a := by
    rw [← hQeq]
    rfl
  have hrightiff := circular_grid_boundary_iff_adjacent_cells
    (Q := 10 ^ (k + r)) (m := (a + 1) * 10 ^ r) (x := x)
    hQ hmR hx hend
  rw [hcenterR, hR, hS] at hrightiff
  dsimp only [x] at hleftiff hrightiff ⊢
  unfold cylinderLeft cylinderRight
  constructor
  · rintro (hleftNear | hrightNear)
    · rcases hleftiff.mp hleftNear with hPmem | hLmem
      · exact Or.inl hPmem
      · exact Or.inr (Or.inl hLmem)
    · rcases hrightiff.mp hrightNear with hRmem | hSmem
      · exact Or.inr (Or.inr (Or.inl hRmem))
      · exact Or.inr (Or.inr (Or.inr hSmem))
  · rintro (hPmem | hLmem | hRmem | hSmem)
    · exact Or.inl (hleftiff.mpr (Or.inl hPmem))
    · exact Or.inl (hleftiff.mpr (Or.inr hLmem))
    · exact Or.inr (hrightiff.mpr (Or.inl hRmem))
    · exact Or.inr (hrightiff.mpr (Or.inr hSmem))

theorem inCylinder_label_unique {Q b c : ℕ} {x : ℝ} (hQ : 0 < Q)
    (hb : inCylinder Q b x) (hc : inCylinder Q c x) : b = c := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  unfold inCylinder cylinderLeft cylinderRight at hb hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbc | hcb
  · have hsucc : b + 1 ≤ c := Nat.succ_le_iff.mpr hbc
    have hdiv : (((b + 1 : ℕ) : ℝ) / Q) ≤ (c : ℝ) / Q :=
      (div_le_div_iff_of_pos_right hQR).2 (by exact_mod_cast hsucc)
    linarith [hb.2, hc.1]
  · have hsucc : c + 1 ≤ b := Nat.succ_le_iff.mpr hcb
    have hdiv : (((c + 1 : ℕ) : ℝ) / Q) ≤ (b : ℝ) / Q :=
      (div_le_div_iff_of_pos_right hQR).2 (by exact_mod_cast hsucc)
    linarith [hc.2, hb.1]

noncomputable def fourCylinderUnionCount
    (x : ℕ → ℝ) (N Q b₁ b₂ b₃ b₄ : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n =>
    inCylinder Q b₁ (x n) ∨ inCylinder Q b₂ (x n) ∨
      inCylinder Q b₃ (x n) ∨ inCylinder Q b₄ (x n)).card

theorem card_four_distinct_cylinders
    (x : ℕ → ℝ) (N Q b₁ b₂ b₃ b₄ : ℕ) (hQ : 0 < Q)
    (h₁₂ : b₁ ≠ b₂) (h₁₃ : b₁ ≠ b₃) (h₁₄ : b₁ ≠ b₄)
    (h₂₃ : b₂ ≠ b₃) (h₂₄ : b₂ ≠ b₄) (h₃₄ : b₃ ≠ b₄) :
    fourCylinderUnionCount x N Q b₁ b₂ b₃ b₄ =
      cylinderCount x N Q b₁ + cylinderCount x N Q b₂ +
        cylinderCount x N Q b₃ + cylinderCount x N Q b₄ := by
  classical
  unfold fourCylinderUnionCount
  let A := (range N).filter fun n => inCylinder Q b₁ (x n)
  let B := (range N).filter fun n => inCylinder Q b₂ (x n)
  let C := (range N).filter fun n => inCylinder Q b₃ (x n)
  let D := (range N).filter fun n => inCylinder Q b₄ (x n)
  have hAD : Disjoint A (B ∪ (C ∪ D)) := by
    rw [Finset.disjoint_left]
    intro n hnA hnU
    simp only [A, Finset.mem_filter] at hnA
    simp only [Finset.mem_union, B, C, D, Finset.mem_filter] at hnU
    rcases hnU with hnB | hnC | hnD
    · exact h₁₂ (inCylinder_label_unique hQ hnA.2 hnB.2)
    · exact h₁₃ (inCylinder_label_unique hQ hnA.2 hnC.2)
    · exact h₁₄ (inCylinder_label_unique hQ hnA.2 hnD.2)
  have hBD : Disjoint B (C ∪ D) := by
    rw [Finset.disjoint_left]
    intro n hnB hnU
    simp only [B, Finset.mem_filter] at hnB
    simp only [Finset.mem_union, C, D, Finset.mem_filter] at hnU
    rcases hnU with hnC | hnD
    · exact h₂₃ (inCylinder_label_unique hQ hnB.2 hnC.2)
    · exact h₂₄ (inCylinder_label_unique hQ hnB.2 hnD.2)
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro n hnC hnD
    simp only [C, D, Finset.mem_filter] at hnC hnD
    exact h₃₄ (inCylinder_label_unique hQ hnC.2 hnD.2)
  rw [Finset.filter_or, Finset.filter_or, Finset.filter_or]
  change (A ∪ (B ∪ (C ∪ D))).card = _
  rw [Finset.card_union_of_disjoint hAD,
    Finset.card_union_of_disjoint hBD,
    Finset.card_union_of_disjoint hCD]
  unfold A B C D cylinderCount
  omega

/-- T14's indexed boundary count is exactly the sum of the four neighboring
fine-cylinder counts; multiplicities are retained. -/
theorem pi_twoBoundaryCount_eq_four_fine_counts
    {N k r a : ℕ} (hk : 0 < k) (hr : 0 < r) (ha : a < 10 ^ k) :
    twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) a
        (1 / ((10 ^ (k + r) : ℕ) : ℝ)) =
      cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ (k + r))
          (predecessorLabel (10 ^ k) (10 ^ r) a) +
      cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ (k + r))
          (leftInteriorLabel (10 ^ r) a) +
      cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ (k + r))
          (rightInteriorLabel (10 ^ r) a) +
      cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ (k + r))
          (successorLabel (10 ^ k) (10 ^ r) a) := by
  classical
  have hpoint := pi_twoBoundary_iff_four_fine_cylinders
    (k := k) (r := r) (a := a) (n := 0) hk hr ha
  have hcount :
      twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) a
          (1 / ((10 ^ (k + r) : ℕ) : ℝ)) =
        fourCylinderUnionCount Theory.PiDigits.T27.piFractionalOrbit N
          (10 ^ (k + r))
          (predecessorLabel (10 ^ k) (10 ^ r) a)
          (leftInteriorLabel (10 ^ r) a)
          (rightInteriorLabel (10 ^ r) a)
          (successorLabel (10 ^ k) (10 ^ r) a) := by
    unfold twoBoundaryCount fourCylinderUnionCount
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hnear⟩
      exact ⟨hn, (pi_twoBoundary_iff_four_fine_cylinders
        (k := k) (r := r) (a := a) (n := n) hk hr ha).mp hnear⟩
    · rintro ⟨hn, hmem⟩
      exact ⟨hn, (pi_twoBoundary_iff_four_fine_cylinders
        (k := k) (r := r) (a := a) (n := n) hk hr ha).mpr hmem⟩
  rw [hcount]
  have hq2 : 2 ≤ 10 ^ k := by
    exact (by
      have hten : 10 ≤ 10 ^ k := by
        simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hk
      omega)
  have hs2 : 2 ≤ 10 ^ r := by
    exact (by
      have hten : 10 ≤ 10 ^ r := by
        simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hr
      omega)
  obtain ⟨hPL, hPR, hPS, hLR, hLS, hRS⟩ :=
    boundaryLabels_pairwise_distinct hq2 hs2 ha
  exact card_four_distinct_cylinders Theory.PiDigits.T27.piFractionalOrbit N
    (10 ^ (k + r))
    (predecessorLabel (10 ^ k) (10 ^ r) a)
    (leftInteriorLabel (10 ^ r) a)
    (rightInteriorLabel (10 ^ r) a)
    (successorLabel (10 ^ k) (10 ^ r) a)
    (by positivity) hPL hPR hPS hLR hLS hRS

theorem leftInterior_mem_coarseCylinder {q s a : ℕ} {x : ℝ}
    (hq : 0 < q) (hs : 0 < s)
    (hmem : inCylinder (q * s) (leftInteriorLabel s a) x) :
    inCylinder q a x := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqsR : (0 : ℝ) < q * s := by positivity
  have hsone : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold inCylinder cylinderLeft cylinderRight at hmem ⊢
  unfold leftInteriorLabel at hmem
  have hleft : (((a * s : ℕ) : ℝ) / (q * s : ℕ)) = (a : ℝ) / q := by
    push_cast
    field_simp
  rw [hleft] at hmem
  have hright : ((((a * s + 1 : ℕ) : ℝ) / (q * s : ℕ))) ≤
      ((a + 1 : ℕ) : ℝ) / q := by
    push_cast
    apply (div_le_div_iff₀ hqsR hqR).2
    nlinarith
  exact ⟨hmem.1, hmem.2.trans_le hright⟩

theorem rightInterior_mem_coarseCylinder {q s a : ℕ} {x : ℝ}
    (hq : 0 < q) (hs : 0 < s)
    (hmem : inCylinder (q * s) (rightInteriorLabel s a) x) :
    inCylinder q a x := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqsR : (0 : ℝ) < q * s := by positivity
  have hsone : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hprod : 0 < (a + 1) * s := Nat.mul_pos (by omega) hs
  unfold inCylinder cylinderLeft cylinderRight at hmem ⊢
  unfold rightInteriorLabel at hmem
  have hleft : (a : ℝ) / q ≤
      ((((a + 1) * s - 1 : ℕ) : ℝ) / (q * s : ℕ)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ (a + 1) * s), Nat.cast_one]
    push_cast
    apply (div_le_div_iff₀ hqR hqsR).2
    nlinarith
  have hsucc : (a + 1) * s - 1 + 1 = (a + 1) * s := by omega
  have hright :
      ((((a + 1) * s - 1 + 1 : ℕ) : ℝ) / (q * s : ℕ)) =
        ((a + 1 : ℕ) : ℝ) / q := by
    rw [hsucc]
    push_cast
    field_simp
  rw [hright] at hmem
  exact ⟨hleft.trans hmem.1, hmem.2⟩

/-- Absence of the coarse cylinder removes exactly its two interior words from
the four-cylinder boundary decomposition. -/
theorem missing_coarseCylinder_removes_two_interiors
    {N q s a : ℕ} (hq : 0 < q) (hs : 0 < s)
    (hempty : cylinderCount Theory.PiDigits.T27.piFractionalOrbit N q a = 0) :
    cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (q * s)
        (leftInteriorLabel s a) = 0 ∧
      cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (q * s)
        (rightInteriorLabel s a) = 0 := by
  classical
  have hnone : ∀ n < N,
      ¬inCylinder q a (Theory.PiDigits.T27.piFractionalOrbit n) := by
    intro n hn hmem
    have hmember : n ∈ ((range N).filter fun j =>
        inCylinder q a (Theory.PiDigits.T27.piFractionalOrbit j)) := by
      simp [hn, hmem]
    unfold cylinderCount at hempty
    rw [Finset.card_eq_zero.mp hempty] at hmember
    simp at hmember
  constructor
  · unfold cylinderCount
    rw [Finset.card_filter_eq_zero_iff]
    intro n hn hmem
    exact hnone n (Finset.mem_range.mp hn)
      (leftInterior_mem_coarseCylinder hq hs hmem)
  · unfold cylinderCount
    rw [Finset.card_filter_eq_zero_iff]
    intro n hn hmem
    exact hnone n (Finset.mem_range.mp hn)
      (rightInterior_mem_coarseCylinder hq hs hmem)

/-- Indexed occurrences of a concrete finite word in the pi digit stream. -/
noncomputable def piWordOccurrenceCount (v : List (Fin 10)) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n =>
    ∀ i : ℕ, ∀ hi : i < v.length,
      Theory.PiDigits.piDigit (n + i) = v.get ⟨i, hi⟩).card

theorem pi_fixedWord_digits_of_mem_cylinder
    {ell b n : ℕ} (hb : b < 10 ^ ell)
    (hmem : inCylinder (10 ^ ell) b
      (Theory.PiDigits.T27.piFractionalOrbit n)) :
    ∀ i : ℕ, ∀ hi : i < (fixedWord ell b).length,
      Theory.PiDigits.piDigit (n + i) = (fixedWord ell b).get ⟨i, hi⟩ := by
  have hinterval : Theory.PiDigits.T27.piFractionalOrbit n ∈
      Set.Ico
        ((Theory.PiDigits.T20.wordValue (fixedWord ell b) : ℝ) /
          (10 : ℝ) ^ (fixedWord ell b).length)
        (((Theory.PiDigits.T20.wordValue (fixedWord ell b) + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ (fixedWord ell b).length) := by
    simpa only [inCylinder, cylinderLeft, cylinderRight, fixedWord_length hb,
      fixedWord_value hb, Nat.cast_pow, Nat.cast_ofNat] using hmem
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    (fixedWord ell b) (Theory.PiDigits.T27.piFractionalOrbit n) hinterval
  intro i hi
  have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
    Real.pi Real.pi_pos.le n i
  exact (Theory.PiDigits.T20.decimalDigit_pi (n + i)).symm.trans
    (hshift.symm.trans (hdigits i hi))

theorem cylinderCount_le_fixedWord_occurrences
    {N ell b : ℕ} (hb : b < 10 ^ ell) :
    cylinderCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ ell) b ≤
      piWordOccurrenceCount (fixedWord ell b) N := by
  classical
  unfold cylinderCount piWordOccurrenceCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, pi_fixedWord_digits_of_mem_cylinder hb hn.2⟩

theorem natCeil_eighth_le_max {N q p s : ℕ} (hq : 0 < q)
    (h : (N : ℝ) / (4 * (q : ℝ)) ≤ ((p + s : ℕ) : ℝ)) :
    Nat.ceil ((N : ℝ) / (8 * (q : ℝ))) ≤ max p s := by
  rw [Nat.ceil_le]
  have h4q : (0 : ℝ) < 4 * q := by positivity
  have h8q : (0 : ℝ) < 8 * q := by positivity
  apply (div_le_iff₀ h8q).2
  have hN : (N : ℝ) ≤ (4 * (q : ℝ)) * ((p + s : ℕ) : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ h4q).1 h
  have hps : ((p + s : ℕ) : ℝ) ≤ 2 * ((max p s : ℕ) : ℝ) := by
    exact_mod_cast
      (show p + s ≤ 2 * max p s by
        simpa [two_mul] using
          add_le_add (le_max_left p s) (le_max_right p s))
  calc
    (N : ℝ) ≤ (4 * q) * ((p + s : ℕ) : ℝ) := hN
    _ ≤ (4 * q) * (2 * ((max p s : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hps h4q.le
    _ = ((max p s : ℕ) : ℝ) * (8 * q) := by ring

theorem natCeil_natCast_div_natCast (N d : ℕ) (hd : 0 < d) :
    Nat.ceil ((N : ℝ) / (d : ℝ)) = N ⌈/⌉ d := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.ceil_le, ceilDiv_le_iff_le_mul hd,
    div_le_iff₀ (by exact_mod_cast hd)]
  norm_cast
  simp [mul_comm]

theorem natCeil_eighth_eq_rounded_division (N q : ℕ) (hq : 0 < q) :
    Nat.ceil ((N : ℝ) / (8 * (q : ℝ))) =
      (N + 8 * q - 1) / (8 * q) := by
  simpa [Nat.ceilDiv_eq_add_pred_div, Nat.cast_mul] using
    natCeil_natCast_div_natCast N (8 * q) (by omega)

/-- After the two interior words are deleted, T14's boundary branch forces
one of the two surviving adjacent words at the exact ceiling count. -/
theorem boundary_branch_forces_adjacent_word
    {N k r a : ℕ} (hk : 0 < k) (hr : 0 < r) (ha : a < 10 ^ k)
    (hempty : cylinderCount Theory.PiDigits.T27.piFractionalOrbit N
      (10 ^ k) a = 0)
    (hboundary : (N : ℝ) / (4 * (10 ^ k : ℕ)) ≤
      twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N (10 ^ k) a
        (1 / ((10 ^ (k + r) : ℕ) : ℝ))) :
    Nat.ceil ((N : ℝ) / (8 * (10 ^ k : ℕ))) ≤
      max
        (piWordOccurrenceCount
          (fixedWord (k + r) (predecessorLabel (10 ^ k) (10 ^ r) a)) N)
        (piWordOccurrenceCount
          (fixedWord (k + r) (successorLabel (10 ^ k) (10 ^ r) a)) N) := by
  let q : ℕ := 10 ^ k
  let s : ℕ := 10 ^ r
  let Q : ℕ := 10 ^ (k + r)
  let P : ℕ := predecessorLabel q s a
  let L : ℕ := leftInteriorLabel s a
  let R : ℕ := rightInteriorLabel s a
  let S : ℕ := successorLabel q s a
  have hq : 0 < q := by dsimp [q]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hQeq : q * s = Q := by
    dsimp [q, s, Q]
    exact (pow_add 10 k r).symm
  have hcount := pi_twoBoundaryCount_eq_four_fine_counts
    (N := N) (k := k) (r := r) (a := a) hk hr ha
  have hinteriors := missing_coarseCylinder_removes_two_interiors
    hq hs hempty
  have hLzero : cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q L = 0 := by
    simpa only [L, q, s, Q, hQeq] using hinteriors.1
  have hRzero : cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q R = 0 := by
    simpa only [R, q, s, Q, hQeq] using hinteriors.2
  have hcount' :
      twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit N q a
          (1 / (Q : ℝ)) =
        cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q P +
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q L +
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q R +
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q S := by
    simpa only [q, s, Q, P, L, R, S] using hcount
  have hPS : (N : ℝ) / (4 * (q : ℝ)) ≤
      ((cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q P +
        cylinderCount Theory.PiDigits.T27.piFractionalOrbit N Q S : ℕ) : ℝ) := by
    rw [hcount'] at hboundary
    rw [hLzero, hRzero] at hboundary
    norm_num at hboundary ⊢
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using hboundary
  have hceil := natCeil_eighth_le_max hq hPS
  obtain ⟨hPbound, _hLbound, _hRbound, hSbound⟩ :=
    boundaryLabels_canonical hq hs ha
  have hPboundQ : P < 10 ^ (k + r) := by
    dsimp only [P, Q] at hPbound ⊢
    rwa [hQeq] at hPbound
  have hSboundQ : S < 10 ^ (k + r) := by
    dsimp only [S, Q] at hSbound ⊢
    rwa [hQeq] at hSbound
  have hPocc := cylinderCount_le_fixedWord_occurrences
    (N := N) hPboundQ
  have hSocc := cylinderCount_le_fixedWord_occurrences
    (N := N) hSboundQ
  dsimp only [q, s, Q, P, S] at hceil hPocc hSocc ⊢
  exact hceil.trans (max_le_max hPocc hSocc)

/-- The decimal width `10^-(k+r)` satisfies T14's hypotheses exactly when
`M+1` reaches the stated full cutoff. -/
theorem decimal_width_t14_hypotheses
    {k r M : ℕ} (hk : 0 < k) (hr : 0 < r)
    (hcut : 2 * 10 ^ (2 * k + r) ≤ M + 1) :
    0 < (1 / ((10 ^ (k + r) : ℕ) : ℝ)) ∧
    (1 / ((10 ^ (k + r) : ℕ) : ℝ)) ≤
      1 / (2 * ((10 ^ k : ℕ) : ℝ)) ∧
    2 * ((10 ^ k : ℕ) : ℝ) ≤
      (M + 1 : ℝ) * (1 / ((10 ^ (k + r) : ℕ) : ℝ)) := by
  have hqR : (0 : ℝ) < (10 ^ k : ℕ) := by positivity
  have hQR : (0 : ℝ) < (10 ^ (k + r) : ℕ) := by positivity
  have hs2 : 2 ≤ 10 ^ r := by
    have hten : 10 ≤ 10 ^ r := by
      simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hr
    omega
  refine ⟨div_pos zero_lt_one hQR, ?_, ?_⟩
  · apply (div_le_div_iff₀ hQR (by positivity : (0 : ℝ) < 2 * (10 ^ k : ℕ))).2
    push_cast
    have hnat : 2 * 10 ^ k ≤ 10 ^ (k + r) := by
      rw [pow_add]
      simpa [mul_comm] using Nat.mul_le_mul_left (10 ^ k) hs2
    norm_num
    exact_mod_cast hnat
  · rw [mul_one_div]
    apply (le_div_iff₀ hQR).2
    have hexp : 10 ^ k * 10 ^ (k + r) = 10 ^ (2 * k + r) := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    have hnat : 2 * (10 ^ k * 10 ^ (k + r)) ≤ M + 1 := by
      rw [hexp]
      exact hcut
    have hnat' : (2 * 10 ^ k) * 10 ^ (k + r) ≤ M + 1 := by
      simpa [mul_assoc] using hnat
    exact_mod_cast hnat'

/-- Direct specialization of T14's contrapositive at the exact deadline
`D=C*k*10^k`, exactly `D-k+1` starts, and decimal boundary width
`10^-(k+r)`. -/
theorem pi_fullContainment_at_decimal_width_exact_deadline
    (C k r M : ℕ) (hC : 1 ≤ C) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hcut : 2 * 10 ^ (2 * k + r) ≤ M + 1)
    (hboundary : ∀ w : DecimalWord k,
      (twoBoundaryCount Theory.PiDigits.T27.piFractionalOrbit
        (C * k * 10 ^ k - k + 1) (10 ^ k)
        (Theory.PiDigits.T20.wordValue (List.ofFn w))
        (1 / ((10 ^ (k + r) : ℕ) : ℝ)) : ℝ) <
          (C * k * 10 ^ k - k + 1 : ℕ) / (4 * (10 ^ k : ℕ)))
    (hfourier : aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
      (C * k * 10 ^ k - k + 1) (10 ^ k) M <
        (C * k * 10 ^ k - k + 1 : ℕ) / (2 * (10 ^ k : ℕ))) :
    CoversAllLengthKWordsBy Theory.PiDigits.piDigit k (C * k * 10 ^ k) := by
  obtain ⟨hδ, hδq, hMδ⟩ := decimal_width_t14_hypotheses
    hk hr hcut
  exact pi_fullContainment_at_exact_deadline_of_smallness
    C k M (1 / ((10 ^ (k + r) : ℕ) : ℝ)) hC hk
    hδ hδq hMδ hboundary hfourier

/-- Literal `not C1` forces, at unbounded exact full-containment deadlines,
either a surviving adjacent decimal word with the exact ceiling count or
T14's imported aggregated Fourier branch. -/
theorem not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance
    (hnotC1 : ¬ C1) :
    ∀ C K r : ℕ, 1 ≤ C → 1 ≤ K → 1 ≤ r →
      ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧
        ∃ w : DecimalWord k,
          let q : ℕ := 10 ^ k
          let D : ℕ := C * k * q
          let N : ℕ := D - k + 1
          let a : ℕ := Theory.PiDigits.T20.wordValue (List.ofFn w)
          a < q ∧
          (¬ ∃ n : ℕ, n + k ≤ D ∧
            ∀ j : Fin k, Theory.PiDigits.piDigit (n + j) = w j) ∧
          cylinderCount Theory.PiDigits.T27.piFractionalOrbit N q a = 0 ∧
          ∀ M : ℕ, 2 * 10 ^ (2 * k + r) ≤ M + 1 →
            (Nat.ceil ((N : ℝ) / (8 * (q : ℝ))) ≤
                max
                  (piWordOccurrenceCount
                    (fixedWord (k + r) (predecessorLabel q (10 ^ r) a)) N)
                  (piWordOccurrenceCount
                    (fixedWord (k + r) (successorLabel q (10 ^ r) a)) N) ∨
              (N : ℝ) / (2 * q) ≤
                aggregatedFourierSum Theory.PiDigits.T27.piFractionalOrbit
                  N q M) := by
  intro C K r hC hK hr
  obtain ⟨k, hKk, hk, w, hrest⟩ :=
    not_C1_implies_unbounded_boundary_or_aggregated_resonance
      hnotC1 C K hC hK
  refine ⟨k, hKk, hk, w, ?_⟩
  dsimp only at hrest ⊢
  rcases hrest with ⟨ha, hmissing, hempty, hall⟩
  refine ⟨ha, hmissing, hempty, ?_⟩
  intro M hcut
  obtain ⟨hδ, hδq, hMδ⟩ := decimal_width_t14_hypotheses hk hr hcut
  rcases hall (1 / ((10 ^ (k + r) : ℕ) : ℝ)) M hδ hδq hMδ with
    hboundary | hfourier
  · left
    exact boundary_branch_forces_adjacent_word hk hr ha hempty hboundary
  · exact Or.inr hfourier

#print axioms boundaryLabels_complete_carry_audit
#print axioms boundaryWords_complete_carry_audit
#print axioms piFractionalOrbit_avoids_grid_endpoints
#print axioms circular_grid_boundary_iff_adjacent_cells
#print axioms pi_twoBoundary_iff_four_fine_cylinders
#print axioms pi_twoBoundaryCount_eq_four_fine_counts
#print axioms missing_coarseCylinder_removes_two_interiors
#print axioms natCeil_eighth_eq_rounded_division
#print axioms boundary_branch_forces_adjacent_word
#print axioms decimal_width_t14_hypotheses
#print axioms pi_fullContainment_at_decimal_width_exact_deadline
#print axioms not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance

end Theory.PiDigits.DecimalBoundaryWordObstruction
