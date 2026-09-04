import TheoryLib.PiDigits.T20BaseTenOrbitDensity
import TheoryLib.PiQuantitativeBlockHitting.T126T126ZeroWindowCell

/-!
# T207: zero/nine cylinders, endpoint recurrence, and the P3 offset bridge

produced for AllMath task pack t207; task
`pi-t207-endpoint-01-zero-cylinder` by the free model Muse Spark 1.3 through
the modelbench pipeline on 2026-09-04 (wave E3, one task per lemma); tasks
`pi-t207-endpoint-02-nine-cylinder` through
`pi-t207-endpoint-06-p3-one-based-offset` by Claude Opus 5 as a Pi Lab
subagent on 2026-09-04; each task compiled and axiom-checked; assembled by
Claude Opus 5
-/

noncomputable section
namespace Theory.PiDigits.T207EndpointRecurrence

def piOrbit (n : ℕ) : ℝ :=
  Theory.PiDigits.T20.baseTenOrbit Real.pi n

def PiCW0 : Prop :=
  ∀ L : ℕ, ∃ n : ℕ,
    ∀ i : Fin L, Theory.PiDigits.piDigit (n + i.val) = 0

def PiCW9 : Prop :=
  ∀ L : ℕ, ∃ n : ℕ,
    ∀ i : Fin L, Theory.PiDigits.piDigit (n + i.val) = 9

def PiEND : Prop := PiCW0 ∨ PiCW9

def PiP3OneBased : Prop :=
  ∀ L : ℕ, ∃ j : ℕ, 1 ≤ j ∧
    ∀ i : Fin L,
      Theory.PiDigits.piDigit ((j - 1) + i.val) = 0

/-! ### The zero cylinder

Task `pi-t207-endpoint-01-zero-cylinder`. -/

/-- The all-zero decimal word of length `L`. -/
def zeroWord (L : ℕ) : List (Fin 10) := List.replicate L 0

theorem zeroWord_length (L : ℕ) : (zeroWord L).length = L := by
  simp [zeroWord]

theorem wordValue_zeroWord (L : ℕ) :
    Theory.PiDigits.T20.wordValue (zeroWord L) = 0 := by
  induction L with
  | zero => rfl
  | succ k ih =>
    have hcons : zeroWord (k + 1) = (0 : Fin 10) :: zeroWord k := rfl
    rw [hcons]
    simp [Theory.PiDigits.T20.wordValue, ih]

theorem get_zeroWord (L : ℕ) (i : ℕ) (hi : i < (zeroWord L).length) :
    (zeroWord L).get ⟨i, hi⟩ = 0 := by
  rw [List.get_eq_getElem]
  show ((List.replicate L (0 : Fin 10)))[i] = 0
  have hiL : i < L := by
    have h := hi
    rwa [zeroWord_length] at h
  exact List.getElem_replicate (by rwa [List.length_replicate])

/-- The orbit of pi never lands exactly on a decimal-grid endpoint `10 ^ (-L)`,
since that would force pi to be rational. -/
theorem piOrbit_ne_invPow (n L : ℕ) :
    piOrbit n ≠ ((10 : ℝ) ^ L)⁻¹ := by
  intro heq
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hfrac : Int.fract ((10 : ℝ) ^ n * Real.pi) = ((10 : ℝ) ^ L)⁻¹ := heq
  have hdecomp : (10 : ℝ) ^ n * Real.pi
      = (⌊(10 : ℝ) ^ n * Real.pi⌋ : ℝ) + ((10 : ℝ) ^ L)⁻¹ := by
    have h := Int.floor_add_fract ((10 : ℝ) ^ n * Real.pi)
    rw [hfrac] at h
    exact h.symm
  have h10ne : (10 : ℝ) ^ n ≠ 0 := ne_of_gt h10n
  have hpi : Real.pi
      = ((⌊(10 : ℝ) ^ n * Real.pi⌋ : ℝ) + ((10 : ℝ) ^ L)⁻¹) / (10 : ℝ) ^ n := by
    rw [eq_div_iff h10ne, mul_comm Real.pi ((10 : ℝ) ^ n)]
    exact hdecomp
  have hq : (((((⌊(10 : ℝ) ^ n * Real.pi⌋ : ℤ) : ℚ) + ((10 : ℚ) ^ L)⁻¹)
      / (10 : ℚ) ^ n : ℚ) : ℝ) = Real.pi := by
    push_cast
    exact hpi.symm
  exact irrational_pi ⟨_, hq⟩

theorem zeroBlock_iff_piOrbit_lt (n L : ℕ) :
    (∀ i : Fin L,
      Theory.PiDigits.piDigit (n + i.val) = 0) ↔
      piOrbit n < ((10 : ℝ) ^ L)⁻¹ := by
  constructor
  · intro hzero
    have hzero' : ∀ i : Fin L,
        (Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val)).val = 0 := by
      intro i
      have h : Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val) = 0 := by
        rw [Theory.PiDigits.T20.decimalDigit_pi]
        exact hzero i
      simp [h]
    have hle :=
      Theory.PiQuantitativeBlockHitting.T126.baseTenOrbit_le_invPow_of_zero_window
        Real.pi_pos.le (n := n) (k := L) hzero'
    have hne := piOrbit_ne_invPow n L
    show Theory.PiDigits.T20.baseTenOrbit Real.pi n < ((10 : ℝ) ^ L)⁻¹
    exact lt_of_le_of_ne hle hne
  · intro hlt
    have hmem : Theory.PiDigits.T20.baseTenOrbit Real.pi n ∈ Set.Ico
        ((Theory.PiDigits.T20.wordValue (zeroWord L) : ℝ) /
          (10 : ℝ) ^ (zeroWord L).length)
        (((Theory.PiDigits.T20.wordValue (zeroWord L) + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ (zeroWord L).length) := by
      rw [wordValue_zeroWord, zeroWord_length]
      simp only [Nat.cast_zero, Nat.cast_one, zero_add, zero_div,
        one_div]
      refine Set.mem_Ico.mpr ⟨?_, ?_⟩
      · exact (Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi n).1
      · exact hlt
    have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
      (zeroWord L) _ hmem
    intro i
    have hi : i.val < (zeroWord L).length := by
      rw [zeroWord_length]
      exact i.isLt
    have hget := hdigits i.val hi
    have hzero_get : (zeroWord L).get ⟨i.val, hi⟩ = 0 :=
      get_zeroWord L i.val hi
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit
      Real.pi Real.pi_pos.le n i.val
    calc Theory.PiDigits.piDigit (n + i.val)
        = Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val) :=
          (Theory.PiDigits.T20.decimalDigit_pi _).symm
      _ = Theory.PiDigits.T20.decimalDigit
            (Theory.PiDigits.T20.baseTenOrbit Real.pi n) i.val := hshift.symm
      _ = (zeroWord L).get ⟨i.val, hi⟩ := hget
      _ = 0 := hzero_get

/-! ### The nine cylinder

Task `pi-t207-endpoint-02-nine-cylinder`. -/

/-- The all-nine decimal word of length `L`. -/
def nineWord (L : ℕ) : List (Fin 10) := List.replicate L 9

theorem nineWord_length (L : ℕ) : (nineWord L).length = L := by
  simp [nineWord]

theorem get_nineWord (L : ℕ) (i : ℕ) (hi : i < (nineWord L).length) :
    (nineWord L).get ⟨i, hi⟩ = 9 := by
  rw [List.get_eq_getElem]
  simp [nineWord]

theorem wordValue_nineWord_succ (L : ℕ) :
    Theory.PiDigits.T20.wordValue (nineWord L) + 1 = 10 ^ L := by
  induction L with
  | zero => rfl
  | succ k ih =>
    have h9 : (9 : Fin 10).val = 9 := rfl
    have hcons : Theory.PiDigits.T20.wordValue (nineWord (k + 1))
        = (9 : Fin 10).val * 10 ^ (nineWord k).length
          + Theory.PiDigits.T20.wordValue (nineWord k) := rfl
    rw [hcons, nineWord_length, h9]
    calc 9 * 10 ^ k + Theory.PiDigits.T20.wordValue (nineWord k) + 1
        = 9 * 10 ^ k + (Theory.PiDigits.T20.wordValue (nineWord k) + 1) := by
          ring
      _ = 9 * 10 ^ k + 10 ^ k := by rw [ih]
      _ = 10 ^ (k + 1) := by ring

theorem decimalDigit_zero_val (z : ℝ) :
    (Theory.PiDigits.T20.decimalDigit z 0).val = ⌊(10 : ℝ) * z⌋₊ % 10 := by
  rw [mul_comm]
  simp [Theory.PiDigits.T20.decimalDigit, Real.digits]

/-- A prefix of nines forces the point into the top mesh cell. -/
theorem nine_prefix_lower :
    ∀ (L : ℕ) (z : ℝ), 0 ≤ z → z < 1 →
      (∀ i : ℕ, i < L → (Theory.PiDigits.T20.decimalDigit z i).val = 9) →
      1 - ((10 : ℝ) ^ L)⁻¹ ≤ z := by
  intro L
  induction L with
  | zero =>
    intro z hz0 _ _
    simpa using hz0
  | succ L ih =>
    intro z hz0 hz1 h
    have hz10 : (0 : ℝ) ≤ 10 * z := by linarith
    have hd0 : ⌊(10 : ℝ) * z⌋₊ % 10 = 9 := by
      rw [← decimalDigit_zero_val z]
      exact h 0 (Nat.succ_pos L)
    have hlt : ⌊(10 : ℝ) * z⌋₊ < 10 := by
      have : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
      refine (Nat.floor_lt hz10).mpr ?_
      rw [this]
      linarith
    have hfl : ⌊(10 : ℝ) * z⌋₊ = 9 := by omega
    have hfract : Int.fract ((10 : ℝ) * z) = 10 * z - 9 := by
      rw [Int.fract, ← natCast_floor_eq_intCast_floor hz10, hfl]
      norm_num
    have hshift : ∀ i : ℕ,
        Theory.PiDigits.T20.decimalDigit (Int.fract ((10 : ℝ) * z)) i
          = Theory.PiDigits.T20.decimalDigit z (1 + i) := by
      intro i
      have hb := Theory.PiDigits.T20.decimalDigit_baseTenOrbit z hz0 1 i
      simpa [Theory.PiDigits.T20.baseTenOrbit, pow_one] using hb
    have hw := ih (Int.fract ((10 : ℝ) * z)) (Int.fract_nonneg _)
      (Int.fract_lt_one _) (by
        intro i hi
        rw [hshift i]
        exact h (1 + i) (by omega))
    rw [hfract] at hw
    have hpow : ((10 : ℝ) ^ (L + 1))⁻¹ = ((10 : ℝ) ^ L)⁻¹ / 10 := by
      rw [pow_succ, mul_inv]
      ring
    rw [hpow]
    linarith

theorem nineBlock_iff_piOrbit_ge (n L : ℕ) :
    (∀ i : Fin L,
      Theory.PiDigits.piDigit (n + i.val) = 9) ↔
      1 - ((10 : ℝ) ^ L)⁻¹ ≤ piOrbit n := by
  have hpow : (0 : ℝ) < (10 : ℝ) ^ L := by positivity
  have hlo : (0 : ℝ) ≤ piOrbit n :=
    (Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi n).1
  have hhi : piOrbit n < 1 :=
    (Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi n).2
  constructor
  · intro hnine
    refine nine_prefix_lower L (piOrbit n) hlo hhi ?_
    intro i hi
    have h1 : Theory.PiDigits.T20.decimalDigit (piOrbit n) i
        = Theory.PiDigits.T20.decimalDigit Real.pi (n + i) :=
      Theory.PiDigits.T20.decimalDigit_baseTenOrbit Real.pi Real.pi_pos.le n i
    have h2 : Theory.PiDigits.piDigit (n + i) = 9 := hnine ⟨i, hi⟩
    rw [h1, Theory.PiDigits.T20.decimalDigit_pi, h2]
    rfl
  · intro hge
    have hvR : (Theory.PiDigits.T20.wordValue (nineWord L) : ℝ)
        = (10 : ℝ) ^ L - 1 := by
      have hN := wordValue_nineWord_succ L
      have hR : ((Theory.PiDigits.T20.wordValue (nineWord L) + 1 : ℕ) : ℝ)
          = ((10 ^ L : ℕ) : ℝ) := by exact_mod_cast hN
      push_cast at hR
      linarith
    have hmem : piOrbit n ∈ Set.Ico
        ((Theory.PiDigits.T20.wordValue (nineWord L) : ℝ) /
          (10 : ℝ) ^ (nineWord L).length)
        (((Theory.PiDigits.T20.wordValue (nineWord L) + 1 : ℕ) : ℝ) /
          (10 : ℝ) ^ (nineWord L).length) := by
      rw [nineWord_length]
      refine Set.mem_Ico.mpr ⟨?_, ?_⟩
      · rw [hvR]
        have hid : ((10 : ℝ) ^ L - 1) / (10 : ℝ) ^ L
            = 1 - ((10 : ℝ) ^ L)⁻¹ := by
          field_simp
        rw [hid]
        exact hge
      · push_cast
        rw [hvR]
        have hid : ((10 : ℝ) ^ L - 1 + 1) / (10 : ℝ) ^ L = 1 := by
          field_simp
          ring
        rw [hid]
        exact hhi
    have hdig := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
      (nineWord L) (piOrbit n) hmem
    intro i
    have hi : i.val < (nineWord L).length := by
      rw [nineWord_length]; exact i.isLt
    calc Theory.PiDigits.piDigit (n + i.val)
        = Theory.PiDigits.T20.decimalDigit Real.pi (n + i.val) :=
          (Theory.PiDigits.T20.decimalDigit_pi _).symm
      _ = Theory.PiDigits.T20.decimalDigit (piOrbit n) i.val :=
          (Theory.PiDigits.T20.decimalDigit_baseTenOrbit Real.pi
            Real.pi_pos.le n i.val).symm
      _ = (nineWord L).get ⟨i.val, hi⟩ := hdig i.val hi
      _ = 9 := get_nineWord L i.val hi

/-! ### Endpoint recurrence

Tasks `pi-t207-endpoint-03-cw0-recurrence` and
`pi-t207-endpoint-04-cw9-recurrence`; their `exists_invPow_lt` helpers are
byte-identical and appear once. -/

/-- Archimedean choice of a decimal resolution finer than `ε`. -/
theorem exists_invPow_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, ((10 : ℝ) ^ L)⁻¹ < ε := by
  obtain ⟨L, hL⟩ :=
    exists_pow_lt_of_lt_one hε (show (1 / 10 : ℝ) < 1 by norm_num)
  refine ⟨L, ?_⟩
  rwa [one_div, inv_pow] at hL

theorem PiCW0_iff_recurrent_at_zero
    (hZero : ∀ n L : ℕ,
      (∀ i : Fin L, Theory.PiDigits.piDigit (n + i.val) = 0) ↔
        piOrbit n < ((10 : ℝ) ^ L)⁻¹) :
    PiCW0 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ piOrbit n < ε := by
  constructor
  · intro h ε hε N
    obtain ⟨L, hL⟩ := exists_invPow_lt hε
    obtain ⟨n, hn⟩ := h (N + L)
    refine ⟨n + N, Nat.le_add_left N n, ?_⟩
    have hblock : ∀ i : Fin L,
        Theory.PiDigits.piDigit ((n + N) + i.val) = 0 := by
      intro i
      have hmem : N + i.val < N + L := by omega
      have := hn ⟨N + i.val, hmem⟩
      simpa [← Nat.add_assoc] using this
    exact lt_trans ((hZero (n + N) L).mp hblock) hL
  · intro h L
    obtain ⟨n, _, hlt⟩ := h ((10 : ℝ) ^ L)⁻¹ (by positivity) 0
    exact ⟨n, (hZero n L).mpr hlt⟩

theorem PiCW9_iff_recurrent_at_one
    (hNine : ∀ n L : ℕ,
      (∀ i : Fin L, Theory.PiDigits.piDigit (n + i.val) = 9) ↔
        1 - ((10 : ℝ) ^ L)⁻¹ ≤ piOrbit n) :
    PiCW9 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ 1 - ε < piOrbit n := by
  constructor
  · intro h ε hε N
    obtain ⟨L, hL⟩ := exists_invPow_lt hε
    obtain ⟨n, hn⟩ := h (N + L)
    refine ⟨n + N, Nat.le_add_left N n, ?_⟩
    have hblock : ∀ i : Fin L,
        Theory.PiDigits.piDigit ((n + N) + i.val) = 9 := by
      intro i
      have hmem : N + i.val < N + L := by omega
      have := hn ⟨N + i.val, hmem⟩
      simpa [← Nat.add_assoc] using this
    have hge := (hNine (n + N) L).mp hblock
    linarith
  · intro h L
    obtain ⟨n, _, hlt⟩ := h ((10 : ℝ) ^ L)⁻¹ (by positivity) 0
    exact ⟨n, (hNine n L).mpr hlt.le⟩

/-! ### The END dictionary

Task `pi-t207-endpoint-05-end-dictionary`. -/

theorem PiEND_iff_endpoint_recurrence
    (hCW0 : PiCW0 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ piOrbit n < ε)
    (hCW9 : PiCW9 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ 1 - ε < piOrbit n) :
    PiEND ↔
      (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ piOrbit n < ε) ∨
      (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ 1 - ε < piOrbit n) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (hCW0.mp h)
    · exact Or.inr (hCW9.mp h)
  · rintro (h | h)
    · exact Or.inl (hCW0.mpr h)
    · exact Or.inr (hCW9.mpr h)

/-! ### The one-based P3 offset

Task `pi-t207-endpoint-06-p3-one-based-offset`. -/

theorem PiP3OneBased_iff_PiCW0 :
    PiP3OneBased ↔ PiCW0 := by
  constructor
  · intro h L
    obtain ⟨j, _hj, hblock⟩ := h L
    exact ⟨j - 1, hblock⟩
  · intro h L
    obtain ⟨n, hblock⟩ := h L
    refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
    simpa using hblock

/-! ### Discharged forms

Tasks 03, 04 and 05 keep their exact prerequisite contracts as hypotheses; the
siblings above supply them unconditionally. -/

theorem PiCW0_iff_recurrent_at_zero_discharged :
    PiCW0 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ piOrbit n < ε :=
  PiCW0_iff_recurrent_at_zero zeroBlock_iff_piOrbit_lt

theorem PiCW9_iff_recurrent_at_one_discharged :
    PiCW9 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ 1 - ε < piOrbit n :=
  PiCW9_iff_recurrent_at_one nineBlock_iff_piOrbit_ge

theorem PiEND_iff_endpoint_recurrence_discharged :
    PiEND ↔
      (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ piOrbit n < ε) ∨
      (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ 1 - ε < piOrbit n) :=
  PiEND_iff_endpoint_recurrence PiCW0_iff_recurrent_at_zero_discharged
    PiCW9_iff_recurrent_at_one_discharged

end Theory.PiDigits.T207EndpointRecurrence

end
