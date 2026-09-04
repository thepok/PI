import TheoryLib.PiQuantitativeBlockHitting.T198T198MachinBracketPack

/-!
# T213: quantified Machin SOH classification

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t213; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

namespace Theory.PiDigits.T213MachinSOHClassification

noncomputable section

def SOHAt (k m n D R Delta : ℕ) : Prop :=
  10 ^ k * R + 10 ^ (n + k) * Delta < D

def SOH37 (D : ℕ → ℕ) (R : ℕ → ℕ → ℕ) (Delta : ℕ → ℕ) : Prop :=
  ∀ k > 0, ∀ M > 0, ∃ m ≥ M, ∃ n,
    SOHAt k m n (D m) (R m n) (Delta m)

def MC0 (L U : ℕ → ℝ) : Prop :=
  ∀ ell : ℕ, 1 ≤ ell → ∃ m n : ℕ, ∃ z : ℤ,
    (z : ℝ) / (10 : ℝ) ^ n ≤ L m ∧
      L m < U m ∧
      U m < (z : ℝ) / (10 : ℝ) ^ n +
        1 / (10 : ℝ) ^ (n + ell)

def frac (x : ℝ) : ℝ := x - ⌊x⌋

def DataCorrect
    (L U : ℕ → ℝ) (D : ℕ → ℕ)
    (R : ℕ → ℕ → ℕ) (Delta : ℕ → ℕ) : Prop :=
  ∀ m n, 0 < D m ∧
    ((R m n : ℝ) / (D m : ℝ)) =
      frac ((10 : ℝ) ^ n * L m) ∧
    ((Delta m : ℝ) / (D m : ℝ)) = U m - L m

def machinL (m : ℕ) : ℝ :=
  Theory.PiDigits.HuttonRationalShadow.huttonLower m

def machinU (m : ℕ) : ℝ :=
  ((8 * Theory.PiDigits.MachinGridStability.arctanPartialRat 3 (2 * m + 1) +
      4 * Theory.PiDigits.MachinGridStability.arctanPartialRat 7 (2 * m + 1) : ℚ) : ℝ)

def PiCW0 : Prop :=
  ∀ ell : ℕ, 1 ≤ ell → ∃ n : ℕ,
    ∀ i : Fin ell, Theory.PiDigits.piDigit (n + i.val) = 0

def MachinDataCorrect
    (D : ℕ → ℕ) (R : ℕ → ℕ → ℕ) (Delta : ℕ → ℕ) : Prop :=
  DataCorrect machinL machinU D R Delta

/-- Negative powers of ten are antitone in the exponent. -/
lemma one_div_pow_ten_anti {a b : ℕ} (hab : a ≤ b) :
    (1 : ℝ) / 10 ^ b ≤ 1 / 10 ^ a := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hab

/-- Any positive real eventually dominates a negative power of ten. -/
lemma exists_one_div_pow_ten_lt {e : ℝ} (he : 0 < e) :
    ∃ j : ℕ, (1 : ℝ) / 10 ^ j < e := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / e) (by norm_num : (1 : ℝ) < 10)
  refine ⟨j, ?_⟩
  rw [div_lt_iff₀ he] at hj
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- Beyond a finite initial segment one can pick a cylinder length that no
already-positive bracket width can survive. -/
lemma exists_late_ell (L U : ℕ → ℝ) (k M : ℕ) :
    ∃ ell : ℕ, k ≤ ell ∧
      ∀ j, j < M → L j < U j → (1 : ℝ) / 10 ^ ell < U j - L j := by
  induction M with
  | zero => exact ⟨k, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ M ih =>
      obtain ⟨ell, hkl, hell⟩ := ih
      by_cases hM : L M < U M
      · obtain ⟨p, hp⟩ := exists_one_div_pow_ten_lt (show (0 : ℝ) < U M - L M by linarith)
        refine ⟨max ell p, le_trans hkl (le_max_left _ _), ?_⟩
        intro j hj hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact lt_of_le_of_lt (one_div_pow_ten_anti (le_max_left ell p)) (hell j h hlt)
        · subst h
          exact lt_of_le_of_lt (one_div_pow_ten_anti (le_max_right ell p)) hp
      · refine ⟨ell, hkl, ?_⟩
        intro j hj hlt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact hell j h hlt
        · exact absurd (h ▸ hlt) hM

/-- A decimal cylinder of length `k` around the bracket forces the integer SOH
inequality at the same indices. -/
lemma cylinder_to_sohAt
    {L U : ℕ → ℝ} {D : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    {k m n : ℕ} (hD : 0 < D m)
    (hR : ((R m n : ℝ) / (D m : ℝ)) = frac ((10 : ℝ) ^ n * L m))
    (hDelta : ((Delta m : ℝ) / (D m : ℝ)) = U m - L m)
    {z : ℤ} (h1 : (z : ℝ) / (10 : ℝ) ^ n ≤ L m)
    (h2 : U m < (z : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + k)) :
    SOHAt k m n (D m) (R m n) (Delta m) := by
  have hDr : (0 : ℝ) < (D m : ℝ) := by exact_mod_cast hD
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have h10k : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hnk : (10 : ℝ) ^ (n + k) = (10 : ℝ) ^ n * (10 : ℝ) ^ k := pow_add 10 n k
  have hzle : (z : ℝ) ≤ (10 : ℝ) ^ n * L m := by
    rw [div_le_iff₀ h10n] at h1
    linarith
  have hzfloorR : (z : ℝ) ≤ ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.le_floor.2 hzle
  have hfl : ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) ≤ (10 : ℝ) ^ n * L m := Int.floor_le _
  have hdd : (z : ℝ) / (10 : ℝ) ^ n ≤
      ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n := by
    gcongr
  have h2' : U m <
      ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + k) := by
    linarith
  have hRe : (R m n : ℝ) =
      (D m : ℝ) * ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) := by
    have hfr : frac ((10 : ℝ) ^ n * L m) =
        (10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) := rfl
    rw [← hfr, ← hR]
    field_simp
  have hDe : (Delta m : ℝ) = (D m : ℝ) * (U m - L m) := by
    rw [← hDelta]
    field_simp
  have hmul :
      U m * ((10 : ℝ) ^ n * (10 : ℝ) ^ k) <
        (((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n +
          1 / (10 : ℝ) ^ (n + k)) * ((10 : ℝ) ^ n * (10 : ℝ) ^ k) :=
    mul_lt_mul_of_pos_right h2' (by positivity)
  have hrhs :
      (((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n +
          1 / (10 : ℝ) ^ (n + k)) * ((10 : ℝ) ^ n * (10 : ℝ) ^ k) =
        (10 : ℝ) ^ k * ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) + 1 := by
    rw [hnk]
    field_simp
  rw [hrhs] at hmul
  have hreal :
      (10 : ℝ) ^ k * (R m n : ℝ) + (10 : ℝ) ^ (n + k) * (Delta m : ℝ) < (D m : ℝ) := by
    have hEq :
        (10 : ℝ) ^ k * (R m n : ℝ) + (10 : ℝ) ^ (n + k) * (Delta m : ℝ) =
          (D m : ℝ) *
            ((10 : ℝ) ^ n * (10 : ℝ) ^ k * U m -
              (10 : ℝ) ^ k * ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) := by
      rw [hRe, hDe, hnk]
      ring
    rw [hEq]
    calc
      (D m : ℝ) *
          ((10 : ℝ) ^ n * (10 : ℝ) ^ k * U m -
            (10 : ℝ) ^ k * ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ))
          < (D m : ℝ) * 1 := by
            apply mul_lt_mul_of_pos_left _ hDr
            linarith
      _ = (D m : ℝ) := mul_one _
  show 10 ^ k * R m n + 10 ^ (n + k) * Delta m < D m
  exact_mod_cast hreal

/-- Strict positive bracket widths push MC0 witnesses beyond every index. -/
lemma mc0_to_soh37
    {L U : ℕ → ℝ} {D : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    (hdata : DataCorrect L U D R Delta) (hMC : MC0 L U) :
    SOH37 D R Delta := by
  intro k hk M _
  obtain ⟨ell, hkl, hell⟩ := exists_late_ell L U k M
  obtain ⟨m, n, z, h1, h2, h3⟩ := hMC ell (by omega)
  have hmM : M ≤ m := by
    rcases Nat.lt_or_ge m M with hlt | hge
    · exfalso
      have hw := hell m hlt h2
      have hle : (1 : ℝ) / 10 ^ (n + ell) ≤ 1 / 10 ^ ell :=
        one_div_pow_ten_anti (Nat.le_add_left ell n)
      linarith
    · exact hge
  obtain ⟨hD, hR, hDelta⟩ := hdata m n
  refine ⟨m, hmM, n, cylinder_to_sohAt hD hR hDelta h1 ?_⟩
  have hle : (1 : ℝ) / 10 ^ (n + ell) ≤ 1 / 10 ^ (n + k) :=
    one_div_pow_ten_anti (by omega)
  linarith

/-- The integer SOH inequality yields one decimal cylinder containing the
whole bracket. -/
lemma sohAt_to_cylinder
    {L U : ℕ → ℝ} {D : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    {k m n : ℕ} (hD : 0 < D m)
    (hR : ((R m n : ℝ) / (D m : ℝ)) = frac ((10 : ℝ) ^ n * L m))
    (hDelta : ((Delta m : ℝ) / (D m : ℝ)) = U m - L m)
    (h : SOHAt k m n (D m) (R m n) (Delta m)) :
    ∃ z : ℤ, (z : ℝ) / (10 : ℝ) ^ n ≤ L m ∧
      U m < (z : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + k) := by
  have hDr : (0 : ℝ) < (D m : ℝ) := by exact_mod_cast hD
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have h10k : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hnk : (10 : ℝ) ^ (n + k) = (10 : ℝ) ^ n * (10 : ℝ) ^ k := pow_add 10 n k
  have hfloor : ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) ≤ (10 : ℝ) ^ n * L m :=
    Int.floor_le _
  have hRe : (R m n : ℝ) =
      (D m : ℝ) * ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) := by
    have hfr : frac ((10 : ℝ) ^ n * L m) =
        (10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) := rfl
    rw [← hfr, ← hR]
    field_simp
  have hDe : (Delta m : ℝ) = (D m : ℝ) * (U m - L m) := by
    rw [← hDelta]
    field_simp
  have hcast :
      (10 : ℝ) ^ k * (R m n : ℝ) + (10 : ℝ) ^ (n + k) * (Delta m : ℝ) < (D m : ℝ) := by
    have hnat : 10 ^ k * R m n + 10 ^ (n + k) * Delta m < D m := h
    exact_mod_cast hnat
  have hX :
      (10 : ℝ) ^ k * ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
        (10 : ℝ) ^ (n + k) * (U m - L m) < 1 := by
    have h2 :
        (D m : ℝ) *
            ((10 : ℝ) ^ k *
                ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
              (10 : ℝ) ^ (n + k) * (U m - L m)) <
          (D m : ℝ) * 1 := by
      rw [mul_one]
      calc
        (D m : ℝ) *
            ((10 : ℝ) ^ k *
                ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
              (10 : ℝ) ^ (n + k) * (U m - L m))
            = (10 : ℝ) ^ k * (R m n : ℝ) +
              (10 : ℝ) ^ (n + k) * (Delta m : ℝ) := by
              rw [hRe, hDe]; ring
        _ < (D m : ℝ) := hcast
    exact lt_of_mul_lt_mul_left (by linarith) hDr.le
  refine ⟨⌊(10 : ℝ) ^ n * L m⌋, ?_, ?_⟩
  · rw [div_le_iff₀ h10n]
    linarith
  · have hgoal :
        ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / (10 : ℝ) ^ n + 1 / (10 : ℝ) ^ (n + k) =
          ((10 : ℝ) ^ k * ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) + 1) / (10 : ℝ) ^ (n + k) := by
      rw [hnk]
      field_simp
    rw [hgoal, lt_div_iff₀ (by positivity)]
    rw [hnk] at hX ⊢
    linarith

section
variable {D Δ : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {L U : ℕ → ℝ} {k m n : ℕ}

lemma sohAt_implies_bracketCylinder
    (hD : 0 < D m) (hR : ((R m n : ℝ) / D m) = frac (10 ^ n * L m))
    (hΔ : (Δ m : ℝ) / D m = U m - L m)
    (h : SOHAt k m n (D m) (R m n) (Δ m)) :
    ∃ z : ℤ, (z : ℝ) / 10 ^ n ≤ L m ∧
      U m < (z : ℝ) / 10 ^ n + 1 / 10 ^ (n + k) := by
  have hDr : (0 : ℝ) < (D m : ℝ) := by exact_mod_cast hD
  have h10n : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have h10k : (0 : ℝ) < (10 : ℝ) ^ k := by positivity
  have hnk : (10 : ℝ) ^ (n + k) = (10 : ℝ) ^ n * (10 : ℝ) ^ k := pow_add 10 n k
  have hfloor : ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) ≤ (10 : ℝ) ^ n * L m :=
    Int.floor_le _
  have hRe : (R m n : ℝ) =
      (D m : ℝ) * ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) := by
    have hfr : frac ((10 : ℝ) ^ n * L m) =
        (10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) := rfl
    rw [← hfr, ← hR]
    field_simp
  have hDe : (Δ m : ℝ) = (D m : ℝ) * (U m - L m) := by
    rw [← hΔ]
    field_simp
  have hcast :
      (10 : ℝ) ^ k * (R m n : ℝ) + (10 : ℝ) ^ (n + k) * (Δ m : ℝ) < (D m : ℝ) := by
    have hnat : 10 ^ k * R m n + 10 ^ (n + k) * Δ m < D m := h
    exact_mod_cast hnat
  have hX :
      (10 : ℝ) ^ k * ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
        (10 : ℝ) ^ (n + k) * (U m - L m) < 1 := by
    have h2 :
        (D m : ℝ) *
            ((10 : ℝ) ^ k *
                ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
              (10 : ℝ) ^ (n + k) * (U m - L m)) <
          (D m : ℝ) * 1 := by
      rw [mul_one]
      calc
        (D m : ℝ) *
            ((10 : ℝ) ^ k *
                ((10 : ℝ) ^ n * L m - ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ)) +
              (10 : ℝ) ^ (n + k) * (U m - L m))
            = (10 : ℝ) ^ k * (R m n : ℝ) +
              (10 : ℝ) ^ (n + k) * (Δ m : ℝ) := by
              rw [hRe, hDe]; ring
        _ < (D m : ℝ) := hcast
    exact lt_of_mul_lt_mul_left (by linarith) hDr.le
  refine ⟨⌊(10 : ℝ) ^ n * L m⌋, ?_, ?_⟩
  · rw [div_le_iff₀ h10n]
    linarith
  · have hgoal :
        ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) / 10 ^ n + 1 / 10 ^ (n + k) =
          ((10 : ℝ) ^ k * ((⌊(10 : ℝ) ^ n * L m⌋ : ℤ) : ℝ) + 1) / (10 : ℝ) ^ (n + k) := by
      rw [hnk]
      field_simp
    rw [hgoal, lt_div_iff₀ (by positivity)]
    rw [hnk] at hX ⊢
    linarith
end

lemma interior_bracket_implies_eventual_sohAt
    {L U : ℕ → ℝ} {D : ℕ → ℕ}
    {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    (hdata : DataCorrect L U D R Delta) :
    MC0 L U → SOH37 D R Delta :=
  fun hMC => mc0_to_soh37 hdata hMC

/-- General classification: with strictly positive bracket widths and exact
integer data, SOH37 and MC0 are equivalent. -/
theorem soh37_iff_mc0
    {L U : ℕ → ℝ} {D : ℕ → ℕ}
    {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    (hInterior : ∀ m, L m < U m)
    (hdata : DataCorrect L U D R Delta) :
    SOH37 D R Delta ↔ MC0 L U := by
  constructor
  · intro hS ell hell
    obtain ⟨m, _, n, hsoh⟩ := hS ell (by omega) 1 (by omega)
    obtain ⟨hD, hR, hDelta⟩ := hdata m n
    obtain ⟨z, hz1, hz2⟩ := sohAt_to_cylinder hD hR hDelta hsoh
    exact ⟨m, n, z, hz1, hInterior m, hz2⟩
  · intro hMC
    exact mc0_to_soh37 hdata hMC

/-- The T198 Machin 3/7 endpoints strictly bracket pi, hence each other. -/
lemma machin_interior (m : ℕ) : machinL m < machinU m := by
  have hb := Theory.PiDigits.T198MachinBracketPack.machin37_strict_bracket_and_width m
  exact lt_trans hb.1 hb.2.1

/-- T198's Machin MC0 bridge, in the pinned local API. -/
lemma machinMC0_iff_piCW0_local : MC0 machinL machinU ↔ PiCW0 :=
  Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0

/-- Discharged form: `machin_interior` supplies the bracket-positivity
hypothesis of `soh37_iff_mc0` at the Machin endpoints. -/
theorem soh37_iff_mc0_machin
    {D : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    (hdata : MachinDataCorrect D R Delta) :
    SOH37 D R Delta ↔ MC0 machinL machinU :=
  soh37_iff_mc0 machin_interior hdata

theorem soh37_iff_piCW0
    {D : ℕ → ℕ} {R : ℕ → ℕ → ℕ} {Delta : ℕ → ℕ}
    (hdata : MachinDataCorrect D R Delta) :
    SOH37 D R Delta ↔ PiCW0 :=
  (soh37_iff_mc0 machin_interior hdata).trans machinMC0_iff_piCW0_local

end

end Theory.PiDigits.T213MachinSOHClassification
