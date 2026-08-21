import TheoryLib.PiDigits.T7Statements
import Mathlib.Analysis.Real.OfDigits

/-!
# Decimal disjunctivity and the base-ten fractional-part orbit

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file proves an equivalence only.  In particular, it proves neither that
the base-ten fractional-part orbit of `Real.pi` is dense nor T7's canonical
V1 proposition.  It also proves nothing about T7's sibling proposition V3.
-/

namespace Theory.PiDigits.T20

/-- The generic floor-based decimal digit stream used by T7. -/
noncomputable def decimalDigit (x : ℝ) (n : ℕ) : Fin 10 :=
  Real.digits x 10 n

/-- Every finite decimal word occurs contiguously in the floor-based stream. -/
def EveryFiniteDecimalWord (x : ℝ) : Prop :=
  ∀ s : List (Fin 10), ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
    decimalDigit x (n + i) = s.get ⟨i, hi⟩

/-- The base-ten fractional-part orbit.  `Int.fract` is mathlib's generic
fractional-part operation, specialized here to `ℝ`. -/
noncomputable def baseTenOrbit (x : ℝ) (k : ℕ) : ℝ :=
  Int.fract ((10 : ℝ) ^ k * x)

/-- Explicit metric density of the orbit in the closed unit interval. -/
def BaseTenOrbitDense (x : ℝ) : Prop :=
  ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, |baseTenOrbit x k - y| < ε

lemma decimalDigit_pi (n : ℕ) :
    decimalDigit Real.pi n = Theory.PiDigits.piDigit n := by
  rfl

lemma baseTenOrbit_mem_Ico (x : ℝ) (k : ℕ) :
    baseTenOrbit x k ∈ Set.Ico (0 : ℝ) 1 := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Multiplying by `10^k` and taking fractional part shifts the floor-based
digit stream by `k` places. -/
lemma decimalDigit_baseTenOrbit (x : ℝ) (hx : 0 ≤ x) (k i : ℕ) :
    decimalDigit (baseTenOrbit x k) i = decimalDigit x (k + i) := by
  apply Fin.ext
  simp only [decimalDigit, Real.digits, Fin.val_ofNat, baseTenOrbit]
  push_cast
  let y : ℝ := (10 : ℝ) ^ k * x
  let q : ℕ := ⌊y⌋₊ * 10 ^ (i + 1)
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hfract : Int.fract y = y - (⌊y⌋₊ : ℝ) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hy]
  have hreal :
      Int.fract ((10 : ℝ) ^ k * x) * (10 : ℝ) ^ (i + 1) =
        x * (10 : ℝ) ^ (k + i + 1) - q := by
    rw [show (10 : ℝ) ^ k * x = y by rfl, hfract]
    dsimp [q, y]
    push_cast
    rw [show k + i + 1 = k + (i + 1) by omega, pow_add]
    ring
  have hqfloor : q ≤ ⌊x * (10 : ℝ) ^ (k + i + 1)⌋₊ := by
    apply Nat.le_floor
    rw [show (q : ℝ) = (⌊y⌋₊ : ℝ) * (10 : ℝ) ^ (i + 1) by
      dsimp [q]
      norm_cast]
    calc
      (⌊y⌋₊ : ℝ) * (10 : ℝ) ^ (i + 1) ≤
          y * (10 : ℝ) ^ (i + 1) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le hy) (by positivity)
      _ = x * (10 : ℝ) ^ (k + i + 1) := by
        dsimp [y]
        rw [show k + i + 1 = k + (i + 1) by omega, pow_add]
        ring
  have hfloor :
      ⌊Int.fract ((10 : ℝ) ^ k * x) * (10 : ℝ) ^ (i + 1)⌋₊ =
        ⌊x * (10 : ℝ) ^ (k + i + 1)⌋₊ - q := by
    rw [hreal]
    exact Nat.floor_sub_natCast _ _
  rw [hfloor]
  have hqmod : q ≡ 0 [MOD 10] := by
    apply Dvd.dvd.modEq_zero_nat
    refine ⟨⌊y⌋₊ * 10 ^ i, ?_⟩
    dsimp [q]
    simp [pow_succ]
    ring
  have hmod :
      ⌊x * (10 : ℝ) ^ (k + i + 1)⌋₊ - q ≡
        ⌊x * (10 : ℝ) ^ (k + i + 1)⌋₊ [MOD 10] := by
    simpa using Nat.ModEq.sub hqfloor (Nat.zero_le _) Nat.ModEq.rfl hqmod
  exact hmod

/-- A word interpreted as the left endpoint of its decimal cylinder. -/
def wordValue : List (Fin 10) → ℕ
  | [] => 0
  | d :: s => d.val * 10 ^ s.length + wordValue s

lemma wordValue_lt_pow_length (s : List (Fin 10)) :
    wordValue s < 10 ^ s.length := by
  induction s with
  | nil => simp [wordValue]
  | cons d s ih =>
      simp only [wordValue, List.length_cons, pow_succ']
      have hd : d.val < 10 := d.isLt
      calc
        d.val * 10 ^ s.length + wordValue s <
            d.val * 10 ^ s.length + 10 ^ s.length := Nat.add_lt_add_left ih _
        _ = (d.val + 1) * 10 ^ s.length := by simp [Nat.add_mul]
        _ ≤ 10 * 10 ^ s.length := Nat.mul_le_mul_right _ hd

/-- Membership in a decimal cylinder fixes precisely the corresponding
initial floor-based digits. -/
lemma decimalDigit_eq_of_mem_wordCylinder (s : List (Fin 10)) (z : ℝ)
    (hz : z ∈ Set.Ico
      ((wordValue s : ℝ) / (10 : ℝ) ^ s.length)
      (((wordValue s + 1 : ℕ) : ℝ) / (10 : ℝ) ^ s.length)) :
    ∀ i : ℕ, ∀ hi : i < s.length,
      decimalDigit z i = s.get ⟨i, hi⟩ := by
  induction s generalizing z with
  | nil => simp
  | cons d s ih =>
      have hq : 0 < (10 : ℝ) ^ s.length := by positivity
      have hv0 : 0 ≤ (wordValue s : ℝ) := by positivity
      have hvlt : (wordValue s : ℝ) < (10 : ℝ) ^ s.length := by
        exact_mod_cast wordValue_lt_pow_length s
      have hv1 : ((wordValue s + 1 : ℕ) : ℝ) ≤ (10 : ℝ) ^ s.length := by
        exact_mod_cast wordValue_lt_pow_length s
      simp only [wordValue, List.length_cons, pow_succ'] at hz
      push_cast at hz
      have hden : 0 < (10 : ℝ) * 10 ^ s.length := by positivity
      have hloMul :
          (d.val : ℝ) * 10 ^ s.length + wordValue s ≤
            z * ((10 : ℝ) * 10 ^ s.length) := by
        exact (div_le_iff₀ hden).mp hz.1
      have hhiMul :
          z * ((10 : ℝ) * 10 ^ s.length) <
            (d.val : ℝ) * 10 ^ s.length + wordValue s + 1 := by
        exact (lt_div_iff₀ hden).mp hz.2
      have hdle : (d.val : ℝ) ≤ 10 * z := by
        apply le_of_mul_le_mul_right _ hq
        exact calc
          (d.val : ℝ) * 10 ^ s.length ≤
              (d.val : ℝ) * 10 ^ s.length + wordValue s :=
            le_add_of_nonneg_right hv0
          _ ≤ z * ((10 : ℝ) * 10 ^ s.length) := hloMul
          _ = (10 * z) * 10 ^ s.length := by ring
      have hdzlt : 10 * z < (d.val : ℝ) + 1 := by
        apply lt_of_mul_lt_mul_right _ hq.le
        exact calc
          (10 * z) * 10 ^ s.length =
              z * ((10 : ℝ) * 10 ^ s.length) := by ring
          _ < (d.val : ℝ) * 10 ^ s.length + wordValue s + 1 := hhiMul
          _ ≤ ((d.val : ℝ) + 1) * 10 ^ s.length := by
            calc
              (d.val : ℝ) * 10 ^ s.length + wordValue s + 1 =
                  (d.val : ℝ) * 10 ^ s.length + (wordValue s + 1) := by ring
              _ ≤ (d.val : ℝ) * 10 ^ s.length + 10 ^ s.length := by
                push_cast at hv1
                gcongr
              _ = ((d.val : ℝ) + 1) * 10 ^ s.length := by ring
      have hz0 : 0 ≤ z := by
        have hd0 : 0 ≤ (d.val : ℝ) := by positivity
        nlinarith
      have htenz0 : 0 ≤ 10 * z := by positivity
      have hfloor : ⌊10 * z⌋₊ = d.val := by
        exact (Nat.floor_eq_iff htenz0).2 ⟨hdle, hdzlt⟩
      have hfract : Int.fract (10 * z) = 10 * z - d.val := by
        rw [Int.fract, ← natCast_floor_eq_intCast_floor htenz0, hfloor]
      have htail : Int.fract (10 * z) ∈ Set.Ico
          ((wordValue s : ℝ) / (10 : ℝ) ^ s.length)
          (((wordValue s + 1 : ℕ) : ℝ) / (10 : ℝ) ^ s.length) := by
        rw [hfract]
        constructor
        · apply (div_le_iff₀ hq).2
          calc
            (wordValue s : ℝ) ≤
                z * ((10 : ℝ) * 10 ^ s.length) -
                  (d.val : ℝ) * 10 ^ s.length := by linarith
            _ = (10 * z - d.val) * 10 ^ s.length := by ring
        · apply (lt_div_iff₀ hq).2
          calc
            (10 * z - d.val) * 10 ^ s.length =
                z * ((10 : ℝ) * 10 ^ s.length) -
                  (d.val : ℝ) * 10 ^ s.length := by ring
            _ < (wordValue s + 1 : ℕ) := by
              push_cast
              linarith
      intro i hi
      cases i with
      | zero =>
          have hget : (d :: s).get ⟨0, hi⟩ = d := by
            simp only [List.get_eq_getElem, List.getElem_cons_zero]
          rw [hget]
          apply Fin.ext
          simp only [decimalDigit, Real.digits, Fin.val_ofNat]
          norm_num only [Nat.zero_add, pow_one, Nat.cast_ofNat]
          rw [mul_comm, hfloor, Nat.mod_eq_of_lt d.isLt]
      | succ j =>
          have hj : j < s.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          have htailDigit := ih (Int.fract (10 * z)) htail j hj
          have hshift := decimalDigit_baseTenOrbit z hz0 1 j
          have hshift' :
              decimalDigit (Int.fract (10 * z)) j = decimalDigit z (1 + j) := by
            simpa [baseTenOrbit, pow_one] using hshift
          simpa [Nat.add_comm] using hshift'.symm.trans htailDigit

/-- Occurrence of every finite decimal word implies metric density of the
base-ten fractional-part orbit in `[0,1]`. -/
theorem everyFiniteDecimalWord_implies_baseTenOrbitDense
    (x : ℝ) (hx : 0 ≤ x) (hwords : EveryFiniteDecimalWord x) :
    BaseTenOrbitDense x := by
  intro y hy ε hε
  obtain ⟨a, -, ha⟩ := (Real.ofDigits_SurjOn (b := 10) (by norm_num)) hy
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
    (by norm_num : (10 : ℝ)⁻¹ < 1)
  let s : List (Fin 10) := List.ofFn fun i : Fin m => a i
  obtain ⟨k, hk⟩ := hwords s
  have hprefix : ∀ i < m,
      Real.digits (baseTenOrbit x k) 10 i = a i := by
    intro i hi
    have hocc : decimalDigit x (k + i) = a i := by
      simpa [s] using hk i (by simpa [s] using hi)
    exact (decimalDigit_baseTenOrbit x hx k i).trans hocc
  have hclose := Real.abs_ofDigits_sub_ofDigits_le hprefix
  rw [Real.ofDigits_digits (by norm_num) (baseTenOrbit_mem_Ico x k), ha] at hclose
  refine ⟨k, hclose.trans_lt ?_⟩
  simpa [inv_pow] using hm

/-- Metric density of the base-ten fractional-part orbit in `[0,1]` implies
occurrence of every finite decimal word. -/
theorem baseTenOrbitDense_implies_everyFiniteDecimalWord
    (x : ℝ) (hx : 0 ≤ x) (hdense : BaseTenOrbitDense x) :
    EveryFiniteDecimalWord x := by
  intro s
  let left : ℝ := (wordValue s : ℝ) / (10 : ℝ) ^ s.length
  let right : ℝ := ((wordValue s + 1 : ℕ) : ℝ) / (10 : ℝ) ^ s.length
  have hpow : 0 < (10 : ℝ) ^ s.length := by positivity
  have hvlt : (wordValue s : ℝ) < (10 : ℝ) ^ s.length := by
    exact_mod_cast wordValue_lt_pow_length s
  have hv1 : ((wordValue s + 1 : ℕ) : ℝ) ≤ (10 : ℝ) ^ s.length := by
    exact_mod_cast wordValue_lt_pow_length s
  have hleft0 : 0 ≤ left := by
    dsimp [left]
    positivity
  have hright1 : right ≤ 1 := by
    dsimp [right]
    exact (div_le_one hpow).2 hv1
  have hlr : left < right := by
    dsimp [left, right]
    apply (div_lt_div_iff_of_pos_right hpow).2
    push_cast
    norm_num
  let center : ℝ := (left + right) / 2
  let radius : ℝ := (right - left) / 2
  have hcenter : center ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [center]
    constructor <;> linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  obtain ⟨k, hk⟩ := hdense center hcenter radius hradius
  have hmem : baseTenOrbit x k ∈ Set.Ico left right := by
    rw [abs_lt] at hk
    dsimp [center, radius] at hk
    constructor <;> linarith
  have hdigits := decimalDigit_eq_of_mem_wordCylinder s (baseTenOrbit x k) (by
    simpa [left, right] using hmem)
  refine ⟨k, ?_⟩
  intro i hi
  exact (decimalDigit_baseTenOrbit x hx k i).symm.trans (hdigits i hi)

/-- Generic equivalence between decimal disjunctivity and orbit density. -/
theorem everyFiniteDecimalWord_iff_baseTenOrbitDense (x : ℝ) (hx : 0 ≤ x) :
    EveryFiniteDecimalWord x ↔ BaseTenOrbitDense x :=
  ⟨everyFiniteDecimalWord_implies_baseTenOrbitDense x hx,
    baseTenOrbitDense_implies_everyFiniteDecimalWord x hx⟩

/-- Exact T7 specialization.  This theorem identifies the two open
propositions; it does not prove either proposition. -/
theorem v1_iff_pi_baseTenOrbitDense :
    Theory.PiDigits.V1 ↔
      ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
        ∃ k : ℕ, |Int.fract ((10 : ℝ) ^ k * Real.pi) - y| < ε := by
  change Theory.PiDigits.V1 ↔ BaseTenOrbitDense Real.pi
  rw [← everyFiniteDecimalWord_iff_baseTenOrbitDense Real.pi Real.pi_pos.le]
  constructor
  · intro h s
    obtain ⟨n, hn⟩ := h s
    exact ⟨n, fun i hi => (decimalDigit_pi (n + i)).trans (hn i hi)⟩
  · intro h s
    obtain ⟨n, hn⟩ := h s
    exact ⟨n, fun i hi => (decimalDigit_pi (n + i)).symm.trans (hn i hi)⟩

end Theory.PiDigits.T20

#print axioms Theory.PiDigits.T20.everyFiniteDecimalWord_implies_baseTenOrbitDense
#print axioms Theory.PiDigits.T20.baseTenOrbitDense_implies_everyFiniteDecimalWord
#print axioms Theory.PiDigits.T20.everyFiniteDecimalWord_iff_baseTenOrbitDense
#print axioms Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense
