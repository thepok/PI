import TheoryLib.PiQuantitativeBlockHitting.T208T208GenericEndpointRecurrence
import Mathlib

/-!
# T209: canonical cylinders and endpoint deletion

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t209; each task compiled and
axiom-checked; assembled by Claude Opus 5

Every task embedded T208's starter definitions verbatim because T208 was not
yet promoted.  Those embedded copies are byte-identical to the promoted
`TheoryLib/PiQuantitativeBlockHitting/T208T208GenericEndpointRecurrence.lean`
definitions, so they are dropped here in favour of the import.
-/

universe u

namespace Theory.PiDigits.T209EndpointCylinderBridge

noncomputable section
def wordValue (b : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun z d => b * z + d) 0
def cylinder (b : ℕ) (w : List ℕ) : Set ℝ :=
  Set.Ico ((wordValue b w : ℝ) / b ^ w.length)
    (((wordValue b w : ℝ) + 1) / b ^ w.length)
def closedCylinder (b : ℕ) (w : List ℕ) : Set ℝ :=
  Set.Icc ((wordValue b w : ℝ) / b ^ w.length)
    (((wordValue b w : ℝ) + 1) / b ^ w.length)
def radixEndpoints (b : ℕ) : Set ℝ :=
  {x | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) / b ^ n}

/-! ### Half-open versus closed cylinders

Tasks `pi-t209-cylinder-01-subset-closed` and
`pi-t209-cylinder-02-endpoint-difference`. -/

section
variable {b : ℕ} {w : List ℕ}

lemma cylinder_subset_closed : cylinder b w ⊆ closedCylinder b w :=
  Set.Ico_subset_Icc_self

lemma closed_diff_cylinder_subset :
    closedCylinder b w \ cylinder b w ⊆ radixEndpoints b := by
  rintro y ⟨hy, hny⟩
  rw [closedCylinder, Set.mem_Icc] at hy
  rw [cylinder, Set.mem_Ico, not_and_or] at hny
  have hend : y = ((wordValue b w : ℝ) + 1) / (b : ℝ) ^ w.length := by
    rcases hny with h | h
    · exact absurd hy.1 h
    · exact le_antisymm hy.2 (not_lt.1 h)
  refine ⟨(wordValue b w : ℤ) + 1, w.length, ?_⟩
  rw [hend]
  push_cast
  ring

end

/-! ### Countability of the radix endpoints

Task `pi-t209-cylinder-03-endpoints-countable`. -/

section
variable {b : ℕ}

lemma radixEndpoints_countable (hb : 2 ≤ b) : (radixEndpoints b).Countable := by
  have hsub : radixEndpoints b
      ⊆ Set.range (fun p : ℤ × ℕ => (p.1 : ℝ) / (b : ℝ) ^ p.2) := by
    rintro y ⟨k, m, rfl⟩
    exact ⟨(k, m), rfl⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

end

/-! ### Occurrence as orbit membership

Task `pi-t209-cylinder-04-occurrence-orbit`. -/

section
variable {b n : ℕ} {w : List ℕ} {x : ℝ}

lemma wordValue_foldl (c : ℕ) : ∀ (v : List ℕ) (z : ℕ),
    v.foldl (fun z d => c * z + d) z = z * c ^ v.length + wordValue c v := by
  intro v
  induction v with
  | nil => intro z; simp [wordValue]
  | cons e rest ih =>
      intro z
      have hw : wordValue c (e :: rest) = e * c ^ rest.length + wordValue c rest := by
        rw [wordValue, List.foldl_cons, ih (c * 0 + e)]
        simp
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (c * z + e), hw, pow_succ]
      ring

lemma wordValue_cons (c d : ℕ) (v : List ℕ) :
    wordValue c (d :: v) = d * c ^ v.length + wordValue c v := by
  rw [wordValue, List.foldl_cons, wordValue_foldl c v (c * 0 + d)]
  simp

lemma wordValue_lt (hb : 2 ≤ b) :
    ∀ (v : List ℕ), (∀ d ∈ v, d < b) → wordValue b v < b ^ v.length := by
  intro v
  induction v with
  | nil => intro _; simp [wordValue]
  | cons e rest ih =>
      intro hall
      have he : e < b := hall e (List.mem_cons_self)
      have hrest : ∀ d ∈ rest, d < b := fun d hd => hall d (List.mem_cons_of_mem _ hd)
      have hIH := ih hrest
      rw [wordValue_cons, List.length_cons, pow_succ]
      have h1 : e * b ^ rest.length + wordValue b rest < (e + 1) * b ^ rest.length := by
        have : (e + 1) * b ^ rest.length = e * b ^ rest.length + b ^ rest.length := by ring
        omega
      have h2 : (e + 1) * b ^ rest.length ≤ b ^ rest.length * b := by
        rw [mul_comm (b ^ rest.length) b]
        exact Nat.mul_le_mul_right _ he
      omega

open Theory.PiDigits.T208GenericEndpointRecurrence in
lemma frac_eq_fract (y : ℝ) : frac y = Int.fract y := rfl

open Theory.PiDigits.T208GenericEndpointRecurrence in
lemma frac_def (y : ℝ) : frac y = y - ⌊y⌋ := rfl

open Theory.PiDigits.T208GenericEndpointRecurrence in
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

open Theory.PiDigits.T208GenericEndpointRecurrence in
lemma digit_eq_iff (hb : 2 ≤ b) (m : ℕ) (y : ℝ) (e : ℕ) :
    digit b m y = e ↔
      ((e : ℝ) ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y) ∧
        (b : ℝ) * frac ((b : ℝ) ^ m * y) < (e : ℝ) + 1) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := lt_of_lt_of_le (by norm_num) hb
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y) :=
    mul_nonneg (le_of_lt hb0) (by rw [frac_eq_fract]; exact Int.fract_nonneg _)
  rw [digit, Nat.floor_eq_iff hnn]

open Theory.PiDigits.T208GenericEndpointRecurrence in
lemma frac_succ_sub (hb : 2 ≤ b) (m : ℕ) (y : ℝ) (e : ℕ)
    (h1 : (e : ℝ) ≤ (b : ℝ) * frac ((b : ℝ) ^ m * y))
    (h2 : (b : ℝ) * frac ((b : ℝ) ^ m * y) < (e : ℝ) + 1) :
    frac ((b : ℝ) ^ (m + 1) * y) = (b : ℝ) * frac ((b : ℝ) ^ m * y) - (e : ℝ) := by
  have hfl : ⌊(b : ℝ) * frac ((b : ℝ) ^ m * y)⌋ = (e : ℤ) := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; exact h1
    · push_cast; exact h2
  rw [frac_succ, frac_def, hfl]
  push_cast
  ring

open Theory.PiDigits.T208GenericEndpointRecurrence in
lemma occurrence_aux (hb : 2 ≤ b) :
    ∀ (v : List ℕ), (∀ d ∈ v, d < b) → ∀ (m : ℕ),
      ((∀ j, ∀ hj : j < v.length, digit b (m + j) x = v.get ⟨j, hj⟩) ↔
        frac ((b : ℝ) ^ m * x) ∈ cylinder b v) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := lt_of_lt_of_le (by norm_num) hb
    exact_mod_cast this
  intro v
  induction v with
  | nil =>
      intro _ m
      have hcyl : cylinder b ([] : List ℕ) = Set.Ico (0 : ℝ) 1 := by
        rw [cylinder]
        norm_num [wordValue]
      rw [hcyl, Set.mem_Ico]
      constructor
      · intro _
        refine ⟨?_, ?_⟩
        · rw [frac_eq_fract]; exact Int.fract_nonneg _
        · rw [frac_eq_fract]; exact Int.fract_lt_one _
      · intro _ j hj
        exact absurd hj (Nat.not_lt_zero j)
  | cons e rest ih =>
      intro hall m
      have he : e < b := hall e (List.mem_cons_self)
      have hrest : ∀ d ∈ rest, d < b := fun d hd => hall d (List.mem_cons_of_mem _ hd)
      have hP : (0 : ℝ) < (b : ℝ) ^ rest.length := pow_pos hb0 _
      have hPb : (0 : ℝ) < (b : ℝ) ^ rest.length * (b : ℝ) := mul_pos hP hb0
      have hVlt : wordValue b rest < b ^ rest.length := wordValue_lt hb rest hrest
      have hV : (wordValue b rest : ℝ) + 1 ≤ (b : ℝ) ^ rest.length := by
        have h' : wordValue b rest + 1 ≤ b ^ rest.length := hVlt
        exact_mod_cast h'
      have hV0 : (0 : ℝ) ≤ (wordValue b rest : ℝ) := Nat.cast_nonneg _
      have hnum : ((wordValue b (e :: rest) : ℕ) : ℝ)
          = (e : ℝ) * (b : ℝ) ^ rest.length + (wordValue b rest : ℝ) := by
        rw [wordValue_cons]; push_cast; ring
      have hden : ((b : ℝ) ^ (e :: rest).length) = (b : ℝ) ^ rest.length * (b : ℝ) := by
        rw [List.length_cons, pow_succ]
      have hcyl : cylinder b (e :: rest)
          = Set.Ico
              (((e : ℝ) * (b : ℝ) ^ rest.length + (wordValue b rest : ℝ))
                / ((b : ℝ) ^ rest.length * (b : ℝ)))
              (((e : ℝ) * (b : ℝ) ^ rest.length + (wordValue b rest : ℝ) + 1)
                / ((b : ℝ) ^ rest.length * (b : ℝ))) := by
        rw [cylinder, hnum, hden]
      have hIH : (∀ j, ∀ hj : j < rest.length,
            digit b (m + 1 + j) x = rest.get ⟨j, hj⟩) ↔
          ((wordValue b rest : ℝ) / (b : ℝ) ^ rest.length ≤ frac ((b : ℝ) ^ (m + 1) * x) ∧
            frac ((b : ℝ) ^ (m + 1) * x)
              < ((wordValue b rest : ℝ) + 1) / (b : ℝ) ^ rest.length) := by
        rw [ih hrest (m + 1), cylinder, Set.mem_Ico]
      rw [hcyl, Set.mem_Ico, div_le_iff₀ hPb, lt_div_iff₀ hPb]
      constructor
      · intro h
        have hhead : digit b m x = e := by
          have h0 := h 0 (Nat.succ_pos _)
          simpa using h0
        obtain ⟨hd1, hd2⟩ := (digit_eq_iff hb m x e).1 hhead
        have hfs : frac ((b : ℝ) ^ (m + 1) * x)
            = (b : ℝ) * frac ((b : ℝ) ^ m * x) - (e : ℝ) := frac_succ_sub hb m x e hd1 hd2
        have htail : ∀ j, ∀ hj : j < rest.length,
            digit b (m + 1 + j) x = rest.get ⟨j, hj⟩ := by
          intro j hj
          have hj' : j + 1 < (e :: rest).length := by
            rw [List.length_cons]; omega
          have hv := h (j + 1) hj'
          rw [show m + (j + 1) = m + 1 + j from by omega] at hv
          simpa using hv
        obtain ⟨hi1, hi2⟩ := hIH.1 htail
        rw [hfs, div_le_iff₀ hP] at hi1
        rw [hfs, lt_div_iff₀ hP] at hi2
        constructor
        · linarith
        · linarith
      · rintro ⟨hm1, hm2⟩
        have hd1 : (e : ℝ) ≤ (b : ℝ) * frac ((b : ℝ) ^ m * x) := by
          have hstep : (e : ℝ) * (b : ℝ) ^ rest.length
              ≤ ((b : ℝ) * frac ((b : ℝ) ^ m * x)) * (b : ℝ) ^ rest.length := by
            nlinarith [hm1, hV0]
          exact le_of_mul_le_mul_right hstep hP
        have hd2 : (b : ℝ) * frac ((b : ℝ) ^ m * x) < (e : ℝ) + 1 := by
          have hstep : ((b : ℝ) * frac ((b : ℝ) ^ m * x)) * (b : ℝ) ^ rest.length
              < ((e : ℝ) + 1) * (b : ℝ) ^ rest.length := by
            nlinarith [hm2, hV]
          exact lt_of_mul_lt_mul_right hstep (le_of_lt hP)
        have hhead : digit b m x = e := (digit_eq_iff hb m x e).2 ⟨hd1, hd2⟩
        have hfs : frac ((b : ℝ) ^ (m + 1) * x)
            = (b : ℝ) * frac ((b : ℝ) ^ m * x) - (e : ℝ) := frac_succ_sub hb m x e hd1 hd2
        have htail : ∀ j, ∀ hj : j < rest.length,
            digit b (m + 1 + j) x = rest.get ⟨j, hj⟩ := by
          apply hIH.2
          rw [hfs]
          constructor
          · rw [div_le_iff₀ hP]; nlinarith [hm1]
          · rw [lt_div_iff₀ hP]; nlinarith [hm2]
        intro j hj
        cases j with
        | zero => simpa using hhead
        | succ k =>
            have hk : k < rest.length := by
              rw [List.length_cons] at hj; omega
            have hv := htail k hk
            rw [show m + 1 + k = m + (k + 1) from by omega] at hv
            simpa using hv

lemma occurrence_iff_orbit_mem (hb : 2 ≤ b) (hw : ∀ d ∈ w, d < b) :
    (∀ i : Fin w.length,
      Theory.PiDigits.T208GenericEndpointRecurrence.digit b (n + i) x = w.get i) ↔
      Theory.PiDigits.T208GenericEndpointRecurrence.frac ((b : ℝ) ^ n * x) ∈ cylinder b w := by
  rw [← occurrence_aux hb w hw n]
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h i
    exact h i.val i.isLt

end

/-! ### Finite-prefix invariance of arbitrarily late occurrences

Task `pi-t209-cylinder-05-finite-prefix`. -/

section
variable {α : Type u} {a a' : ℕ → α} {N : ℕ} {w : List α}

lemma occurrence_transfer {β : Type u} {c c' : ℕ → β} {K : ℕ} {v : List β}
    (h : ∀ n ≥ K, c n = c' n)
    (hyp : ∀ M, ∃ n ≥ M, ∀ i : Fin v.length, c (n + i) = v.get i) :
    ∀ M, ∃ n ≥ M, ∀ i : Fin v.length, c' (n + i) = v.get i := by
  intro M
  obtain ⟨n, hn, hw⟩ := hyp (max M K)
  have hnK : K ≤ n := le_trans (le_max_right M K) hn
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  intro i
  rw [← h (n + i) (by omega)]
  exact hw i

lemma finite_prefix_preserves_infinite_occurrence
    (h : ∀ n ≥ N, a n = a' n) :
    (∀ M, ∃ n ≥ M, ∀ i : Fin w.length, a (n + i) = w.get i) ↔
    (∀ M, ∃ n ≥ M, ∀ i : Fin w.length, a' (n + i) = w.get i) :=
  ⟨fun hyp => occurrence_transfer h hyp,
   fun hyp => occurrence_transfer (fun n hn => (h n hn).symm) hyp⟩

end

end
end Theory.PiDigits.T209EndpointCylinderBridge
