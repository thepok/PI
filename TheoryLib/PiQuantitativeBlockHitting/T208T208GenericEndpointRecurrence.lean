import Mathlib

/-!
# T208: generic endpoint recurrence

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t208; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

namespace Theory.PiDigits.T208GenericEndpointRecurrence

noncomputable section
def frac (x : ℝ) : ℝ := x - ⌊x⌋
def digit (b n : ℕ) (x : ℝ) : ℕ :=
  ⌊(b : ℝ) * frac ((b : ℝ) ^ n * x)⌋₊
def ZeroRun (b n ℓ : ℕ) (x : ℝ) : Prop :=
  ∀ i < ℓ, digit b (n + i) x = 0
def MaxRun (b n ℓ : ℕ) (x : ℝ) : Prop :=
  ∀ i < ℓ, digit b (n + i) x = b - 1
def ApproachesZero (b : ℕ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∀ N, ∃ n ≥ N, frac ((b : ℝ) ^ n * x) < ε
def ApproachesOne (b : ℕ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∀ N, ∃ n ≥ N, 1 - ε < frac ((b : ℝ) ^ n * x)

/-! ### The zero and maximal cylinder identities

Tasks `pi-t208-endpoint-01-zero-run-iff` and `pi-t208-endpoint-02-max-run-iff`.
The shared scalar helpers are byte-identical in the two artifacts and appear
once; task 02's `frac_def` and `cast_pred` extend the common layer. -/

section
variable {b n ℓ : ℕ} {x : ℝ}

lemma frac_def (y : ℝ) : frac y = y - ⌊y⌋ := rfl

lemma frac_eq_fract (y : ℝ) : frac y = Int.fract y := rfl

lemma frac_nonneg' (y : ℝ) : 0 ≤ frac y := Int.fract_nonneg y

lemma frac_lt_one' (y : ℝ) : frac y < 1 := Int.fract_lt_one y

lemma cast_pos_of_two_le (hb : 2 ≤ b) : (0 : ℝ) < (b : ℝ) := by
  have : 0 < b := lt_of_lt_of_le (by norm_num) hb
  exact_mod_cast this

lemma one_le_cast_of_two_le (hb : 2 ≤ b) : (1 : ℝ) ≤ (b : ℝ) := by
  have : 1 ≤ b := le_trans (by norm_num) hb
  exact_mod_cast this

lemma one_le_pow_cast (hb : 2 ≤ b) (m : ℕ) : (1 : ℝ) ≤ (b : ℝ) ^ m :=
  one_le_pow₀ (one_le_cast_of_two_le hb)

lemma pow_cast_pos (hb : 2 ≤ b) (m : ℕ) : (0 : ℝ) < (b : ℝ) ^ m :=
  pow_pos (cast_pos_of_two_le hb) m

lemma cast_pred (hb : 2 ≤ b) : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
  have h1 : 1 ≤ b := le_trans (by norm_num) hb
  push_cast [h1]
  ring
lemma frac_succ (c m : ℕ) (y : ℝ) :
    frac ((c : ℝ) ^ (m + 1) * y) = frac ((c : ℝ) * frac ((c : ℝ) ^ m * y)) := by
  simp only [frac_eq_fract]
  have h1 : ((⌊(c : ℝ) ^ m * y⌋ : ℤ) : ℝ) + Int.fract ((c : ℝ) ^ m * y)
      = (c : ℝ) ^ m * y := Int.floor_add_fract _
  have key : ((c : ℝ) ^ (m + 1) * y)
      = (((c : ℤ) * ⌊(c : ℝ) ^ m * y⌋ : ℤ) : ℝ)
        + (c : ℝ) * Int.fract ((c : ℝ) ^ m * y) := by
    push_cast
    linear_combination (-(c : ℝ)) * h1
  rw [key, Int.fract_intCast_add]
lemma frac_succ_eq_of_lt_one (c m : ℕ) (y : ℝ)
    (h : (c : ℝ) * frac ((c : ℝ) ^ m * y) < 1) (hc : (0 : ℝ) ≤ (c : ℝ)) :
    frac ((c : ℝ) ^ (m + 1) * y) = (c : ℝ) * frac ((c : ℝ) ^ m * y) := by
  rw [frac_succ]
  rw [frac_eq_fract]
  exact Int.fract_eq_self.2 ⟨mul_nonneg hc (frac_nonneg' _), h⟩

lemma digit_eq_zero_iff (c m : ℕ) (y : ℝ) :
    digit c m y = 0 ↔ (c : ℝ) * frac ((c : ℝ) ^ m * y) < 1 := by
  simpa [digit] using (Nat.floor_eq_zero (α := ℝ) (r := (c : ℝ) * frac ((c : ℝ) ^ m * y)))

lemma zeroRun_of_lt (hb : 2 ≤ b) :
    ∀ (L m : ℕ), frac ((b : ℝ) ^ m * x) < 1 / (b : ℝ) ^ L → ZeroRun b m L x := by
  intro L
  induction L with
  | zero => intro m _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ L ih =>
      intro m h
      have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
      have hp : (0 : ℝ) < (b : ℝ) ^ L := pow_cast_pos hb L
      have hbt : (b : ℝ) * frac ((b : ℝ) ^ m * x) < 1 / (b : ℝ) ^ L := by
        rw [pow_succ] at h
        calc (b : ℝ) * frac ((b : ℝ) ^ m * x)
            < (b : ℝ) * (1 / ((b : ℝ) ^ L * (b : ℝ))) := by
              exact mul_lt_mul_of_pos_left h hb0
          _ = 1 / (b : ℝ) ^ L := by field_simp
      have hlt1 : (b : ℝ) * frac ((b : ℝ) ^ m * x) < 1 :=
        lt_of_lt_of_le hbt (by
          rw [div_le_one hp]
          exact one_le_pow_cast hb L)
      have hd : digit b m x = 0 := (digit_eq_zero_iff b m x).2 hlt1
      have hstep : frac ((b : ℝ) ^ (m + 1) * x) = (b : ℝ) * frac ((b : ℝ) ^ m * x) :=
        frac_succ_eq_of_lt_one b m x hlt1 (le_of_lt hb0)
      have hrec : ZeroRun b (m + 1) L x := by
        apply ih
        rw [hstep]
        exact hbt
      intro i hi
      cases i with
      | zero => simpa using hd
      | succ j =>
          have hj : j < L := Nat.lt_of_succ_lt_succ hi
          have := hrec j hj
          have he : m + (j + 1) = m + 1 + j := by omega
          rw [he]
          exact this

lemma lt_of_zeroRun (hb : 2 ≤ b) :
    ∀ (L m : ℕ), ZeroRun b m L x → frac ((b : ℝ) ^ m * x) < 1 / (b : ℝ) ^ L := by
  intro L
  induction L with
  | zero => intro m _; simp only [pow_zero, div_one]; exact frac_lt_one' ((b : ℝ) ^ m * x)
  | succ L ih =>
      intro m h
      have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
      have hp : (0 : ℝ) < (b : ℝ) ^ L := pow_cast_pos hb L
      have hd : digit b m x = 0 := by simpa using h 0 (Nat.succ_pos L)
      have hlt1 : (b : ℝ) * frac ((b : ℝ) ^ m * x) < 1 :=
        (digit_eq_zero_iff b m x).1 hd
      have hstep : frac ((b : ℝ) ^ (m + 1) * x) = (b : ℝ) * frac ((b : ℝ) ^ m * x) :=
        frac_succ_eq_of_lt_one b m x hlt1 (le_of_lt hb0)
      have hrec : ZeroRun b (m + 1) L x := by
        intro j hj
        have := h (j + 1) (Nat.succ_lt_succ hj)
        have he : m + (j + 1) = m + 1 + j := by omega
        rw [he] at this
        exact this
      have hbt : (b : ℝ) * frac ((b : ℝ) ^ m * x) < 1 / (b : ℝ) ^ L := by
        rw [← hstep]; exact ih (m + 1) hrec
      have h3 : ((b : ℝ) * frac ((b : ℝ) ^ m * x)) * (b : ℝ) ^ L < 1 :=
        (lt_div_iff₀ hp).1 hbt
      rw [pow_succ, lt_div_iff₀ (by positivity)]
      have he : frac ((b : ℝ) ^ m * x) * ((b : ℝ) ^ L * (b : ℝ))
          = ((b : ℝ) * frac ((b : ℝ) ^ m * x)) * (b : ℝ) ^ L := by ring
      rw [he]
      exact h3

lemma zeroRun_iff (hb : 2 ≤ b) :
    ZeroRun b n ℓ x ↔ frac ((b : ℝ) ^ n * x) < 1 / (b : ℝ) ^ ℓ :=
  ⟨fun h => lt_of_zeroRun hb ℓ n h, fun h => zeroRun_of_lt hb ℓ n h⟩

lemma mul_frac_lt (hb : 2 ≤ b) (m : ℕ) (y : ℝ) :
    (b : ℝ) * frac ((b : ℝ) ^ m * y) < (b : ℝ) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
  have := mul_lt_mul_of_pos_left (frac_lt_one' ((b : ℝ) ^ m * y)) hb0
  simpa using this

lemma digit_eq_max_iff (hb : 2 ≤ b) (m : ℕ) (y : ℝ) :
    digit b m y = b - 1 ↔ (b : ℝ) - 1 ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
  have hnn : (0 : ℝ) ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y) :=
    mul_nonneg (le_of_lt hb0) (frac_nonneg' _)
  have hup : (b : ℝ) * frac ((b : ℝ) ^ m * y) < (b : ℝ) := mul_frac_lt hb m y
  constructor
  · intro h
    have := ((Nat.floor_eq_iff hnn).1 h).1
    rw [cast_pred hb] at this
    exact this
  · intro h
    refine (Nat.floor_eq_iff hnn).2 ⟨?_, ?_⟩
    · rw [cast_pred hb]; exact h
    · rw [cast_pred hb]; simpa using hup

lemma frac_succ_max (hb : 2 ≤ b) (m : ℕ) (y : ℝ)
    (h : (b : ℝ) - 1 ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y)) :
    frac ((b : ℝ) ^ (m + 1) * y)
      = (b : ℝ) * frac ((b : ℝ) ^ m * y) - ((b : ℝ) - 1) := by
  have hup : (b : ℝ) * frac ((b : ℝ) ^ m * y) < (b : ℝ) := mul_frac_lt hb m y
  have hfl : ⌊(b : ℝ) * frac ((b : ℝ) ^ m * y)⌋ = (b : ℤ) - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; exact h
    · push_cast; linarith
  rw [frac_succ, frac_def, hfl]
  push_cast
  ring

lemma maxRun_of_le (hb : 2 ≤ b) :
    ∀ (L m : ℕ), 1 - 1 / (b : ℝ) ^ L ≤ frac ((b : ℝ) ^ m * x) → MaxRun b m L x := by
  have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  intro L
  induction L with
  | zero => intro m _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ L ih =>
      intro m h
      have hp : (0 : ℝ) < (b : ℝ) ^ L := pow_cast_pos hb L
      have hcalc : (1 - 1 / (b : ℝ) ^ (L + 1)) * (b : ℝ)
          = (b : ℝ) - 1 / (b : ℝ) ^ L := by
        field_simp
        ring
      have hA : (b : ℝ) - 1 / (b : ℝ) ^ L ≤ (b : ℝ) * frac ((b : ℝ) ^ m * x) := by
        have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hb0)
        rw [hcalc] at h2
        linarith [h2]
      have hone : 1 / (b : ℝ) ^ L ≤ 1 := by
        rw [div_le_one hp]; exact one_le_pow_cast hb L
      have hd : digit b m x = b - 1 := by
        refine (digit_eq_max_iff hb m x).2 ?_
        linarith
      have hstep : frac ((b : ℝ) ^ (m + 1) * x)
          = (b : ℝ) * frac ((b : ℝ) ^ m * x) - ((b : ℝ) - 1) :=
        frac_succ_max hb m x (by linarith)
      have hrec : MaxRun b (m + 1) L x := by
        apply ih
        rw [hstep]
        linarith
      intro i hi
      cases i with
      | zero => simpa using hd
      | succ j =>
          have hj : j < L := Nat.lt_of_succ_lt_succ hi
          have hval := hrec j hj
          have he : m + (j + 1) = m + 1 + j := by omega
          rw [he]
          exact hval

lemma le_of_maxRun (hb : 2 ≤ b) :
    ∀ (L m : ℕ), MaxRun b m L x → 1 - 1 / (b : ℝ) ^ L ≤ frac ((b : ℝ) ^ m * x) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := cast_pos_of_two_le hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  intro L
  induction L with
  | zero =>
      intro m _
      simp only [pow_zero, div_one, sub_self]
      exact frac_nonneg' _
  | succ L ih =>
      intro m h
      have hp : (0 : ℝ) < (b : ℝ) ^ L := pow_cast_pos hb L
      have hd : digit b m x = b - 1 := by simpa using h 0 (Nat.succ_pos L)
      have hA : (b : ℝ) - 1 ≤ (b : ℝ) * frac ((b : ℝ) ^ m * x) :=
        (digit_eq_max_iff hb m x).1 hd
      have hstep : frac ((b : ℝ) ^ (m + 1) * x)
          = (b : ℝ) * frac ((b : ℝ) ^ m * x) - ((b : ℝ) - 1) :=
        frac_succ_max hb m x hA
      have hrec : MaxRun b (m + 1) L x := by
        intro j hj
        have hval := h (j + 1) (Nat.succ_lt_succ hj)
        have he : m + (j + 1) = m + 1 + j := by omega
        rw [he] at hval
        exact hval
      have hIH := ih (m + 1) hrec
      rw [hstep] at hIH
      have hcalc : (1 - 1 / (b : ℝ) ^ (L + 1)) * (b : ℝ)
          = (b : ℝ) - 1 / (b : ℝ) ^ L := by
        field_simp
        ring
      have hmul : (1 - 1 / (b : ℝ) ^ (L + 1)) * (b : ℝ)
          ≤ frac ((b : ℝ) ^ m * x) * (b : ℝ) := by
        rw [hcalc]
        linarith [hIH]
      exact le_of_mul_le_mul_right hmul hb0

lemma maxRun_iff (hb : 2 ≤ b) :
    MaxRun b n ℓ x ↔ 1 - 1 / (b : ℝ) ^ ℓ ≤ frac ((b : ℝ) ^ n * x) :=
  ⟨fun h => le_of_maxRun hb ℓ n h, fun h => maxRun_of_le hb ℓ n h⟩

end

/-! ### Arbitrarily long runs and endpoint recurrence

Tasks `pi-t208-endpoint-03-arbitrarily-long-zero`,
`pi-t208-endpoint-04-arbitrarily-long-max`, and
`pi-t208-endpoint-05-endpoint-recurrence`.  Their primed scalar helpers are
byte-identical across tasks 03 and 04 and appear once. -/

section
variable {b : ℕ} {x : ℝ}

lemma cast_pos_of_two_le' (hb : 2 ≤ b) : (0 : ℝ) < (b : ℝ) := by
  have : 0 < b := lt_of_lt_of_le (by norm_num) hb
  exact_mod_cast this

lemma one_lt_cast_of_two_le (hb : 2 ≤ b) : (1 : ℝ) < (b : ℝ) := by
  have : 1 < b := lt_of_lt_of_le (by norm_num) hb
  exact_mod_cast this

lemma pow_cast_pos' (hb : 2 ≤ b) (m : ℕ) : (0 : ℝ) < (b : ℝ) ^ m :=
  pow_pos (cast_pos_of_two_le' hb) m

lemma zeroRun_shift (c m L j : ℕ) (y : ℝ) (h : ZeroRun c m L y) :
    ZeroRun c (m + j) (L - j) y := by
  intro i hi
  have hji : j + i < L := by omega
  have hv := h (j + i) hji
  have he : m + (j + i) = m + j + i := by omega
  rwa [he] at hv

lemma exists_inv_pow_lt (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 / (b : ℝ) ^ M < ε := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (1 / ε) (one_lt_cast_of_two_le hb)
  refine ⟨M, ?_⟩
  have hpM : (0 : ℝ) < (b : ℝ) ^ M := pow_cast_pos' hb M
  have h1 : (1 : ℝ) < (b : ℝ) ^ M * ε := (div_lt_iff₀ hε).1 hM
  rw [div_lt_iff₀ hpM, mul_comm]
  exact h1

lemma inv_pow_antitone (hb : 2 ≤ b) {M K : ℕ} (hMK : M ≤ K) :
    1 / (b : ℝ) ^ K ≤ 1 / (b : ℝ) ^ M := by
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := le_of_lt (one_lt_cast_of_two_le hb)
  exact one_div_le_one_div_of_le (pow_cast_pos' hb M) (pow_le_pow_right₀ hb1 hMK)

theorem arbitrarily_long_zero_iff
    (hZero : ∀ n ℓ : ℕ,
      ZeroRun b n ℓ x ↔ frac ((b : ℝ) ^ n * x) < 1 / (b : ℝ) ^ ℓ)
    (hb : 2 ≤ b) :
    (∀ ℓ, ∃ n, ZeroRun b n ℓ x) ↔ ApproachesZero b x := by
  constructor
  · intro h ε hε N
    obtain ⟨M, hM⟩ := exists_inv_pow_lt hb hε
    obtain ⟨n, hn⟩ := h (N + M)
    refine ⟨max n N, le_max_right _ _, ?_⟩
    have hj : max n N - n ≤ N := by omega
    have hshift : ZeroRun b (n + (max n N - n)) (N + M - (max n N - n)) x :=
      zeroRun_shift b n (N + M) (max n N - n) x hn
    have he : n + (max n N - n) = max n N := by omega
    rw [he] at hshift
    have hlt := (hZero (max n N) (N + M - (max n N - n))).1 hshift
    have hge : M ≤ N + M - (max n N - n) := by omega
    exact lt_of_lt_of_le hlt (le_trans (inv_pow_antitone hb hge) (le_of_lt hM))
  · intro h ℓ
    obtain ⟨n, _, hn⟩ := h (1 / (b : ℝ) ^ ℓ) (by positivity) 0
    exact ⟨n, (hZero n ℓ).2 hn⟩

lemma maxRun_shift (c m L j : ℕ) (y : ℝ) (h : MaxRun c m L y) :
    MaxRun c (m + j) (L - j) y := by
  intro i hi
  have hji : j + i < L := by omega
  have hv := h (j + i) hji
  have he : m + (j + i) = m + j + i := by omega
  rwa [he] at hv
theorem arbitrarily_long_max_iff
    (hMax : ∀ n ℓ : ℕ,
      MaxRun b n ℓ x ↔ 1 - 1 / (b : ℝ) ^ ℓ ≤ frac ((b : ℝ) ^ n * x))
    (hb : 2 ≤ b) :
    (∀ ℓ, ∃ n, MaxRun b n ℓ x) ↔ ApproachesOne b x := by
  constructor
  · intro h ε hε N
    obtain ⟨M, hM⟩ := exists_inv_pow_lt hb hε
    obtain ⟨n, hn⟩ := h (N + M)
    refine ⟨max n N, le_max_right _ _, ?_⟩
    have hshift : MaxRun b (n + (max n N - n)) (N + M - (max n N - n)) x :=
      maxRun_shift b n (N + M) (max n N - n) x hn
    have he : n + (max n N - n) = max n N := by omega
    rw [he] at hshift
    have hle := (hMax (max n N) (N + M - (max n N - n))).1 hshift
    have hge : M ≤ N + M - (max n N - n) := by omega
    have hsmall : 1 / (b : ℝ) ^ (N + M - (max n N - n)) < ε :=
      lt_of_le_of_lt (inv_pow_antitone hb hge) hM
    linarith
  · intro h ℓ
    obtain ⟨n, _, hn⟩ := h (1 / (b : ℝ) ^ ℓ) (by positivity) 0
    exact ⟨n, (hMax n ℓ).2 (le_of_lt hn)⟩

theorem endpoint_recurrence_iff
    (hZero : (∀ ℓ, ∃ n, ZeroRun b n ℓ x) ↔ ApproachesZero b x)
    (hMax : (∀ ℓ, ∃ n, MaxRun b n ℓ x) ↔ ApproachesOne b x)
    (hb : 2 ≤ b) :
    ((∀ ℓ, ∃ n, ZeroRun b n ℓ x) ∨ (∀ ℓ, ∃ n, MaxRun b n ℓ x)) ↔
      ApproachesZero b x ∨ ApproachesOne b x :=
  or_congr hZero hMax

/-! ### Discharged forms

Tasks 03, 04 and 05 keep their exact prerequisite contracts as hypotheses; the
siblings above supply them unconditionally. -/

theorem arbitrarily_long_zero_iff_discharged (hb : 2 ≤ b) :
    (∀ ℓ, ∃ n, ZeroRun b n ℓ x) ↔ ApproachesZero b x :=
  arbitrarily_long_zero_iff
    (fun n ℓ => zeroRun_iff (b := b) (n := n) (ℓ := ℓ) (x := x) hb) hb

theorem arbitrarily_long_max_iff_discharged (hb : 2 ≤ b) :
    (∀ ℓ, ∃ n, MaxRun b n ℓ x) ↔ ApproachesOne b x :=
  arbitrarily_long_max_iff
    (fun n ℓ => maxRun_iff (b := b) (n := n) (ℓ := ℓ) (x := x) hb) hb

theorem endpoint_recurrence_iff_discharged (hb : 2 ≤ b) :
    ((∀ ℓ, ∃ n, ZeroRun b n ℓ x) ∨ (∀ ℓ, ∃ n, MaxRun b n ℓ x)) ↔
      ApproachesZero b x ∨ ApproachesOne b x :=
  endpoint_recurrence_iff (arbitrarily_long_zero_iff_discharged hb)
    (arbitrarily_long_max_iff_discharged hb) hb

end

end
end Theory.PiDigits.T208GenericEndpointRecurrence
