import TheoryLib.PiQuantitativeBlockHitting.T200T200BaileyCrandallCoboundary
import TheoryLib.PiQuantitativeBlockHitting.T108T108BBPCircleDensityTransfer
import TheoryLib.PiQuantitativeBlockHitting.T201T201BaileyCrandallShadow
import Mathlib.Data.Real.Basic

/-!
# T205: power-base disjunctivity and the P5 dictionary

produced for AllMath task pack t205; tasks
`pi-t205-power-base-01-digit-bounds`, `-02-digit-grouping`,
`-04-sixteen-iff-two` and `-06-p5-iff-two` by the free model Muse Spark 1.3
through the modelbench pipeline on 2026-09-04 (wave E3, one task per lemma);
tasks `pi-t205-power-base-03-disjunctive-power-iff` and
`-05-p5-iff-sixteen` by Claude Opus 5 as a Pi Lab subagent on 2026-09-04;
each task compiled and axiom-checked; assembled by Claude Opus 5

Every task embedded T201's three starter definitions verbatim because T201 was
launched in the same wave.  Those embedded copies are byte-identical to the
promoted `TheoryLib/PiQuantitativeBlockHitting/T201T201BaileyCrandallShadow.lean`
definitions, so they are dropped here in favour of the import.
-/

noncomputable section
open scoped BigOperators

namespace Theory.PiDigits.T205PowerBaseDisjunctivity

def baseDigit (b : ℕ) (x : ℝ) (n : ℕ) : ℤ :=
  Int.floor ((b : ℝ) ^ (n + 1) * Int.fract x) -
    (b : ℤ) * Int.floor ((b : ℝ) ^ n * Int.fract x)

def ValidWord (b : ℕ) (w : List ℤ) : Prop :=
  ∀ i : Fin w.length,
    0 ≤ w.get i ∧ w.get i < (b : ℤ)

def OccursAt (b : ℕ) (x : ℝ) (w : List ℤ) (n : ℕ) : Prop :=
  ∀ i : Fin w.length, baseDigit b x (n + i.val) = w.get i

def DigitDisjunctive (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℤ, ValidWord b w → ∃ n : ℕ, OccursAt b x w n

def P5 : Prop :=
  ∀ (u v : ℚ) (N : ℕ), 0 ≤ u → u < v → v ≤ 1 →
    ∃ n : ℕ, N ≤ n ∧
      (u : ℝ) < Theory.PiDigits.T201BaileyCrandallShadow.y n ∧
      Theory.PiDigits.T201BaileyCrandallShadow.y n < (v : ℝ)

/-! ### Digit bounds

Task `pi-t205-power-base-01-digit-bounds`. -/

theorem baseDigit_bounds {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (n : ℕ) :
    0 ≤ baseDigit b x n ∧ baseDigit b x n < (b : ℤ) := by
  unfold baseDigit
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  set t : ℝ := (b : ℝ) ^ n * Int.fract x with ht_def
  have ht0 : 0 ≤ t := mul_nonneg (pow_nonneg hbpos.le n) hf0
  have hdecomp : ((⌊t⌋ : ℤ) : ℝ) + Int.fract t = t := Int.floor_add_fract t
  have hr0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hr1 : Int.fract t < 1 := Int.fract_lt_one t
  have hpow_succ : (b : ℝ) ^ (n + 1) * Int.fract x = (b : ℝ) * t := by
    rw [ht_def, pow_succ]
    ring
  have hcast : ((((b : ℤ) * ⌊t⌋ : ℤ)) : ℝ) = (b : ℝ) * (((⌊t⌋ : ℤ)) : ℝ) := by
    push_cast
    ring
  have hmul : (b : ℝ) * t = ((((b : ℤ) * ⌊t⌋ : ℤ)) : ℝ) + (b : ℝ) * Int.fract t := by
    have h1 : (b : ℝ) * t = (b : ℝ) * ((((⌊t⌋ : ℤ)) : ℝ) + Int.fract t) := by
      congr 1
      exact (Int.floor_add_fract t).symm
    rw [h1, mul_add, hcast]
  have hfloor : ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋
      = (b : ℤ) * ⌊t⌋ + ⌊(b : ℝ) * Int.fract t⌋ := by
    rw [hpow_succ, hmul, Int.floor_intCast_add]
  have hBr0 : 0 ≤ (b : ℝ) * Int.fract t := mul_nonneg hbpos.le hr0
  have hBr1 : (b : ℝ) * Int.fract t < ((((b : ℤ))) : ℝ) := by
    have hlt : (b : ℝ) * Int.fract t < (b : ℝ) * 1 :=
      mul_lt_mul_of_pos_left hr1 hbpos
    rw [mul_one] at hlt
    have hcc : ((((b : ℤ))) : ℝ) = (b : ℝ) := by simp
    rw [hcc]
    exact hlt
  have h0 : 0 ≤ ⌊(b : ℝ) * Int.fract t⌋ := Int.floor_nonneg.mpr hBr0
  have h1 : ⌊(b : ℝ) * Int.fract t⌋ < (b : ℤ) := Int.floor_lt.mpr hBr1
  rw [hfloor]
  constructor
  · have e : (b : ℤ) * ⌊t⌋ + ⌊(b : ℝ) * Int.fract t⌋ - (b : ℤ) * ⌊t⌋
        = ⌊(b : ℝ) * Int.fract t⌋ := by abel
    rw [e]
    exact h0
  · have e : (b : ℤ) * ⌊t⌋ + ⌊(b : ℝ) * Int.fract t⌋ - (b : ℤ) * ⌊t⌋
        = ⌊(b : ℝ) * Int.fract t⌋ := by abel
    rw [e]
    exact h1


/-! ### Digit grouping

Task `pi-t205-power-base-02-digit-grouping`. -/

theorem telescope_aux (c : ℤ) (f : ℕ → ℤ) (k m : ℕ) :
    ∑ j ∈ Finset.range k, (f (m + j + 1) - c * f (m + j)) * c ^ (k - 1 - j) =
      f (m + k) - c ^ k * f m := by
  induction k generalizing m with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hlast : k + 1 - 1 - k = 0 := by omega
    rw [hlast, pow_zero, mul_one]
    have hexp : ∀ j ∈ Finset.range k, (k + 1 - 1 - j : ℕ) = (k - 1 - j) + 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      omega
    have hterm : ∀ j ∈ Finset.range k,
        (f (m + j + 1) - c * f (m + j)) * c ^ (k + 1 - 1 - j) =
          ((f (m + j + 1) - c * f (m + j)) * c ^ (k - 1 - j)) * c := by
      intro j hj
      rw [hexp j hj, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ih m]
    have hpow : c ^ (k + 1) = c ^ k * c := pow_succ c k
    have hm : m + (k + 1) = (m + k) + 1 := by omega
    rw [hm, hpow]
    ring

theorem baseDigit_power_group
    {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k)
    (x : ℝ) (n : ℕ) :
    baseDigit (b ^ k) x n =
      ∑ j ∈ Finset.range k,
        baseDigit b x (k * n + j) * (b : ℤ) ^ (k - 1 - j) := by
  have _hb : 2 ≤ b := hb
  have _hk : 0 < k := hk
  have hBreal : (((b ^ k : ℕ)) : ℝ) = (b : ℝ) ^ k := by
    push_cast
    ring
  have hBint : (((b ^ k : ℕ)) : ℤ) = (b : ℤ) ^ k := by
    push_cast
    ring
  have hpow1 : ((((b ^ k : ℕ)) : ℝ)) ^ (n + 1) = (b : ℝ) ^ (k * n + k) := by
    rw [hBreal, ← pow_mul, Nat.mul_add, Nat.mul_one]
  have hpow0 : ((((b ^ k : ℕ)) : ℝ)) ^ n = (b : ℝ) ^ (k * n) := by
    rw [hBreal, ← pow_mul]
  have hLHS : baseDigit (b ^ k) x n =
      Int.floor ((b : ℝ) ^ (k * n + k) * Int.fract x) -
        (b : ℤ) ^ k * Int.floor ((b : ℝ) ^ (k * n) * Int.fract x) := by
    unfold baseDigit
    rw [hpow1, hpow0, hBint]
  have hRHS : (∑ j ∈ Finset.range k,
        baseDigit b x (k * n + j) * (b : ℤ) ^ (k - 1 - j)) =
      ∑ j ∈ Finset.range k,
        ((Int.floor ((b : ℝ) ^ (k * n + j + 1) * Int.fract x) -
          (b : ℤ) * Int.floor ((b : ℝ) ^ (k * n + j) * Int.fract x)) *
          (b : ℤ) ^ (k - 1 - j)) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold baseDigit
    rfl
  rw [hRHS, hLHS]
  exact (telescope_aux (b : ℤ)
    (fun m => Int.floor ((b : ℝ) ^ m * Int.fract x)) k (k * n)).symm


/-! ### The base-power disjunctivity equivalence

Task `pi-t205-power-base-03-disjunctive-power-iff`. -/

/-! ### Helper layer: base-`b` blocks of length `k` -/

/-- The integer value of `k` base-`b` digits, most significant digit first. -/
def gval (b : ℕ) (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, f j * (b : ℤ) ^ (k - 1 - j)

/-- Prepending a digit to a digit stream. -/
def consFun (q : ℤ) (g : ℕ → ℤ) : ℕ → ℤ :=
  fun j => if j = 0 then q else g (j - 1)

/-- A finite word extended by zeros to a total digit stream. -/
def padWord (w : List ℤ) (t : ℕ) : ℤ :=
  if h : t < w.length then w.get ⟨t, h⟩ else 0

theorem padWord_lt (w : List ℤ) (t : ℕ) (h : t < w.length) :
    padWord w t = w.get ⟨t, h⟩ := dif_pos h

theorem padWord_ge (w : List ℤ) (t : ℕ) (h : ¬ t < w.length) :
    padWord w t = 0 := dif_neg h

theorem consFun_zero (q : ℤ) (g : ℕ → ℤ) : consFun q g 0 = q := by
  simp [consFun]

theorem consFun_succ (q : ℤ) (g : ℕ → ℤ) (j : ℕ) : consFun q g (j + 1) = g j := by
  simp [consFun]

theorem consFun_shift (q : ℤ) (g : ℕ → ℤ) :
    (fun j => consFun q g (j + 1)) = g := by
  funext j
  exact consFun_succ q g j

theorem gval_zero (b : ℕ) (f : ℕ → ℤ) : gval b f 0 = 0 := by
  simp [gval]

theorem gval_congr (b : ℕ) (f g : ℕ → ℤ) (k : ℕ)
    (h : ∀ j : ℕ, j < k → f j = g j) : gval b f k = gval b g k := by
  unfold gval
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem gval_succ (b : ℕ) (f : ℕ → ℤ) (k : ℕ) :
    gval b f (k + 1) = f 0 * (b : ℤ) ^ k + gval b (fun j => f (j + 1)) k := by
  unfold gval
  rw [Finset.sum_range_succ']
  have h : ∑ j ∈ Finset.range k, f (j + 1) * (b : ℤ) ^ (k + 1 - 1 - (j + 1))
      = ∑ j ∈ Finset.range k, f (j + 1) * (b : ℤ) ^ (k - 1 - j) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 2
    omega
  rw [h]
  have hk0 : k + 1 - 1 - 0 = k := by omega
  rw [hk0]
  ring

theorem gval_mem (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k : ℕ) (f : ℕ → ℤ), (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < (b : ℤ)) →
      0 ≤ gval b f k ∧ gval b f k < (b : ℤ) ^ k := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by
    have hb0 : 0 < b := by omega
    exact_mod_cast hb0
  intro k
  induction k with
  | zero =>
    intro f _
    rw [gval_zero]
    refine ⟨le_refl 0, ?_⟩
    simpa using zero_lt_one
  | succ k ih =>
    intro f hf
    have hbk : (0 : ℤ) < (b : ℤ) ^ k := pow_pos hbpos k
    have htail := ih (fun j => f (j + 1)) (fun j hj => hf (j + 1) (by omega))
    have h0 := hf 0 (Nat.succ_pos k)
    rw [gval_succ]
    have hmul : 0 ≤ f 0 * (b : ℤ) ^ k := mul_nonneg h0.1 hbk.le
    refine ⟨by linarith [htail.1], ?_⟩
    have h1 : f 0 * (b : ℤ) ^ k ≤ ((b : ℤ) - 1) * (b : ℤ) ^ k := by
      refine mul_le_mul_of_nonneg_right ?_ hbk.le
      linarith [h0.2]
    have h2 : ((b : ℤ) - 1) * (b : ℤ) ^ k + (b : ℤ) ^ k = (b : ℤ) ^ (k + 1) := by
      rw [pow_succ]; ring
    linarith [htail.2]

theorem gval_inj (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k : ℕ) (f g : ℕ → ℤ),
      (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < (b : ℤ)) →
      (∀ j : ℕ, j < k → 0 ≤ g j ∧ g j < (b : ℤ)) →
      gval b f k = gval b g k → ∀ j : ℕ, j < k → f j = g j := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by
    have hb0 : 0 < b := by omega
    exact_mod_cast hb0
  intro k
  induction k with
  | zero =>
    intro f g _ _ _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro f g hf hg heq j hj
    have hbk : (0 : ℤ) < (b : ℤ) ^ k := pow_pos hbpos k
    have hFt := gval_mem b hb k (fun i => f (i + 1))
      (fun i hi => hf (i + 1) (by omega))
    have hGt := gval_mem b hb k (fun i => g (i + 1))
      (fun i hi => hg (i + 1) (by omega))
    rw [gval_succ, gval_succ] at heq
    have h0 : f 0 = g 0 := by
      rcases lt_trichotomy (f 0) (g 0) with h | h | h
      · exfalso
        have hle : (f 0 + 1) * (b : ℤ) ^ k ≤ g 0 * (b : ℤ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) hbk.le
        linarith [hFt.1, hFt.2, hGt.1, hGt.2]
      · exact h
      · exfalso
        have hle : (g 0 + 1) * (b : ℤ) ^ k ≤ f 0 * (b : ℤ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) hbk.le
        linarith [hFt.1, hFt.2, hGt.1, hGt.2]
    have htails : gval b (fun i => f (i + 1)) k = gval b (fun i => g (i + 1)) k := by
      rw [h0] at heq
      linarith
    cases j with
    | zero => exact h0
    | succ j' =>
      exact ih (fun i => f (i + 1)) (fun i => g (i + 1))
        (fun i hi => hf (i + 1) (by omega)) (fun i hi => hg (i + 1) (by omega))
        htails j' (by omega)

theorem gval_expand (b : ℕ) (hb : 2 ≤ b) :
    ∀ (k : ℕ) (v : ℤ), 0 ≤ v → v < (b : ℤ) ^ k →
      ∃ f : ℕ → ℤ,
        (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < (b : ℤ)) ∧ gval b f k = v := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by
    have hb0 : 0 < b := by omega
    exact_mod_cast hb0
  intro k
  induction k with
  | zero =>
    intro v hv0 hv1
    refine ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    rw [gval_zero]
    have hv : v < 1 := by simpa using hv1
    omega
  | succ k ih =>
    intro v hv0 hv1
    have hbk : (0 : ℤ) < (b : ℤ) ^ k := pow_pos hbpos k
    obtain ⟨g, hg1, hg2⟩ := ih (v % (b : ℤ) ^ k)
      (Int.emod_nonneg v (ne_of_gt hbk)) (Int.emod_lt_of_pos v hbk)
    refine ⟨consFun (v / (b : ℤ) ^ k) g, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        rw [consFun_zero]
        refine ⟨Int.ediv_nonneg hv0 hbk.le, ?_⟩
        rw [Int.ediv_lt_iff_lt_mul hbk]
        calc v < (b : ℤ) ^ (k + 1) := hv1
          _ = (b : ℤ) * (b : ℤ) ^ k := by rw [pow_succ]; ring
      | succ j' =>
        rw [consFun_succ]
        exact hg1 j' (by omega)
    · rw [gval_succ, consFun_zero, consFun_shift, hg2]
      have hmod := Int.mul_ediv_add_emod v ((b : ℤ) ^ k)
      linarith

theorem div_mod_pack (k i j : ℕ) (hk : 0 < k) (hj : j < k) :
    (k * i + j) / k = i ∧ (k * i + j) % k = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem exists_aligned (k n M : ℕ) (hk : 0 < k) :
    ∃ t N : ℕ, t < k ∧ n + t * (k * M + 1) = k * N := by
  rcases Nat.eq_zero_or_pos (n % k) with h0 | hpos
  · refine ⟨0, n / k, hk, ?_⟩
    rw [Nat.zero_mul, Nat.add_zero]
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)).symm
  · have hdk : n % k < k := Nat.mod_lt _ hk
    have hn : k * (n / k) + n % k = n := Nat.div_add_mod n k
    set e := k - n % k with he
    have hek : e < k := by omega
    have hde : n % k + e = k := by omega
    refine ⟨e, e * M + n / k + 1, hek, ?_⟩
    have h1 : n + e * (k * M + 1)
        = (k * (n / k) + n % k) + e * (k * M + 1) := by rw [hn]
    rw [h1]
    calc (k * (n / k) + n % k) + e * (k * M + 1)
        = k * (e * M) + k * (n / k) + (n % k + e) := by ring
      _ = k * (e * M) + k * (n / k) + k := by rw [hde]
      _ = k * (e * M + n / k + 1) := by ring

theorem validWord_ofFn {m : ℕ} (b : ℕ) (g : Fin m → ℤ)
    (h : ∀ i : Fin m, 0 ≤ g i ∧ g i < (b : ℤ)) : ValidWord b (List.ofFn g) := by
  intro i
  have hi : i.val < m := by
    have hlt := i.isLt
    simpa using hlt
  have hget : (List.ofFn g).get i = g ⟨i.val, hi⟩ := by
    simp [List.get_eq_getElem]
  rw [hget]
  exact h _

theorem occursAt_ofFn {m : ℕ} (b : ℕ) (x : ℝ) (g : Fin m → ℤ) (n : ℕ)
    (h : OccursAt b x (List.ofFn g) n) (p : ℕ) (hp : p < m) :
    baseDigit b x (n + p) = g ⟨p, hp⟩ := by
  have hp' : p < (List.ofFn g).length := by simpa using hp
  refine (h ⟨p, hp'⟩).trans ?_
  simp [List.get_eq_getElem]

/-! ### The contracted theorem -/

theorem digitDisjunctive_power_iff
    (hBounds : ∀ {b : ℕ}, 2 ≤ b → ∀ x : ℝ, ∀ n : ℕ,
      0 ≤ baseDigit b x n ∧ baseDigit b x n < (b : ℤ))
    (hGroup : ∀ {b k : ℕ}, 2 ≤ b → 0 < k → ∀ x : ℝ, ∀ n : ℕ,
      baseDigit (b ^ k) x n =
        ∑ j ∈ Finset.range k,
          baseDigit b x (k * n + j) * (b : ℤ) ^ (k - 1 - j))
    {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (x : ℝ) :
    DigitDisjunctive (b ^ k) x ↔ DigitDisjunctive b x := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by
    have hb0 : 0 < b := by omega
    exact_mod_cast hb0
  have hbk : (0 : ℤ) < (b : ℤ) ^ k := pow_pos hbpos k
  have hcast : ((b ^ k : ℕ) : ℤ) = (b : ℤ) ^ k := by push_cast; ring
  have hgr : ∀ n : ℕ, baseDigit (b ^ k) x n
      = gval b (fun j => baseDigit b x (k * n + j)) k := fun n => hGroup hb hk x n
  constructor
  · intro hD w hw
    have hpad : ∀ t : ℕ, 0 ≤ padWord w t ∧ padWord w t < (b : ℤ) := by
      intro t
      by_cases h : t < w.length
      · rw [padWord_lt w t h]; exact hw ⟨t, h⟩
      · rw [padWord_ge w t h]; exact ⟨le_refl 0, hbpos⟩
    obtain ⟨n, hn⟩ := hD
      (List.ofFn (fun i : Fin w.length =>
        gval b (fun j => padWord w (k * i.val + j)) k))
      (validWord_ofFn (b ^ k) _ (fun i => by
        rw [hcast]
        exact gval_mem b hb k (fun j => padWord w (k * i.val + j))
          (fun j _ => hpad _)))
    refine ⟨k * n, ?_⟩
    intro i
    have hi : i.val < w.length := i.isLt
    have hik : i.val / k < w.length := lt_of_le_of_lt (Nat.div_le_self _ _) hi
    have hjk : i.val % k < k := Nat.mod_lt _ hk
    have hocc := occursAt_ofFn (b ^ k) x _ n hn (i.val / k) hik
    have hEq : gval b (fun j => baseDigit b x (k * (n + i.val / k) + j)) k
        = gval b (fun j => padWord w (k * (i.val / k) + j)) k := by
      rw [← hgr (n + i.val / k)]
      exact hocc
    have hkey := gval_inj b hb k _ _
      (fun j _ => hBounds hb x (k * (n + i.val / k) + j))
      (fun j _ => hpad (k * (i.val / k) + j)) hEq (i.val % k) hjk
    have hdm : k * (i.val / k) + i.val % k = i.val := Nat.div_add_mod i.val k
    have harith : k * (n + i.val / k) + i.val % k = k * n + i.val := by
      rw [Nat.mul_add, Nat.add_assoc, hdm]
    rw [harith, hdm] at hkey
    rw [hkey]
    exact padWord_lt w i.val hi
  · intro hD W hW
    have hexp : ∀ i : ℕ, ∃ f : ℕ → ℤ,
        (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < (b : ℤ)) ∧ gval b f k = padWord W i := by
      intro i
      by_cases h : i < W.length
      · rw [padWord_lt W i h]
        have hb1 := hW ⟨i, h⟩
        refine gval_expand b hb k _ hb1.1 ?_
        have hlt := hb1.2
        rwa [hcast] at hlt
      · rw [padWord_ge W i h]
        exact gval_expand b hb k 0 le_rfl hbk
    choose F hF1 hF2 using hexp
    obtain ⟨n, hn⟩ := hD
      (List.ofFn (fun p : Fin (k * (k * W.length + 1)) =>
        F (p.val % (k * W.length + 1) / k) (p.val % (k * W.length + 1) % k)))
      (validWord_ofFn b _ (fun p => hF1 _ _ (Nat.mod_lt _ hk)))
    obtain ⟨t, N, htk, hNeq⟩ := exists_aligned k n W.length hk
    have hshift : ∀ s : ℕ, s < k * W.length →
        baseDigit b x (k * N + s) = F (s / k) (s % k) := by
      intro s hs
      have hsP : s < k * W.length + 1 := by omega
      have hp : t * (k * W.length + 1) + s < k * (k * W.length + 1) := by
        calc t * (k * W.length + 1) + s
            < t * (k * W.length + 1) + (k * W.length + 1) := by omega
          _ = (t + 1) * (k * W.length + 1) := by ring
          _ ≤ k * (k * W.length + 1) := Nat.mul_le_mul htk le_rfl
      have hocc := occursAt_ofFn b x _ n hn (t * (k * W.length + 1) + s) hp
      have hmod : (t * (k * W.length + 1) + s) % (k * W.length + 1) = s := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsP]
      rw [hmod] at hocc
      have hidx : k * N + s = n + (t * (k * W.length + 1) + s) := by
        rw [← hNeq]; ring
      rw [hidx]
      exact hocc
    refine ⟨N, ?_⟩
    intro i
    have hi : i.val < W.length := i.isLt
    have hkey : ∀ j : ℕ, j < k →
        baseDigit b x (k * (N + i.val) + j) = F i.val j := by
      intro j hj
      have hs : k * i.val + j < k * W.length := by
        calc k * i.val + j < k * i.val + k := by omega
          _ = k * (i.val + 1) := by ring
          _ ≤ k * W.length := Nat.mul_le_mul le_rfl hi
      have hidx : k * (N + i.val) + j = k * N + (k * i.val + j) := by ring
      rw [hidx, hshift (k * i.val + j) hs]
      obtain ⟨hd, hm⟩ := div_mod_pack k i.val j hk hj
      rw [hd, hm]
    calc baseDigit (b ^ k) x (N + i.val)
        = gval b (fun j => baseDigit b x (k * (N + i.val) + j)) k := hgr (N + i.val)
      _ = gval b (F i.val) k := gval_congr b _ _ k (fun j hj => hkey j hj)
      _ = padWord W i.val := hF2 i.val
      _ = W.get i := padWord_lt W i.val hi


/-! ### `D16 ↔ D2`

Task `pi-t205-power-base-04-sixteen-iff-two`. -/

theorem digitDisjunctive_sixteen_iff_two
    (hPower : ∀ {b k : ℕ}, 2 ≤ b → 0 < k → ∀ x : ℝ,
      DigitDisjunctive (b ^ k) x ↔ DigitDisjunctive b x) :
    DigitDisjunctive 16 Real.pi ↔ DigitDisjunctive 2 Real.pi := by
  have h := hPower (b := 2) (k := 4) (by norm_num) (by norm_num) Real.pi
  have e : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [e] at h
  exact h

/-! ### `P5 ↔ D16`

Task `pi-t205-power-base-05-p5-iff-sixteen`.  Its hexadecimal helper layer
declares `validWord_ofFn` and `occursAt_ofFn` specialized to base sixteen,
which clash by name with the base-`b` helpers of task 03 above, so that task is
kept verbatim inside this sub-namespace.  Its `padWord`, `padWord_lt` and
`padWord_ge` are byte-identical to task 03's and resolve to the enclosing
namespace, so they are not repeated. -/

namespace HexLayer

/-! ### Circle helpers -/

theorem dist_coe_le_abs (a b : ℝ) :
    dist ((a : UnitAddCircle)) ((b : UnitAddCircle)) ≤ |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem dist_coe_eq_abs (a b : ℝ) :
    dist ((a : UnitAddCircle)) ((b : UnitAddCircle))
      = |a - b - ((round (a - b) : ℤ) : ℝ)| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq (p := (1 : ℝ))]
  norm_num

/-! ### Hexadecimal block values -/

/-- The integer value of `k` hexadecimal digits, most significant digit first. -/
def hval (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, f j * (16 : ℤ) ^ (k - 1 - j)

theorem hval_zero (f : ℕ → ℤ) : hval f 0 = 0 := by
  simp [hval]

theorem hval_congr (f g : ℕ → ℤ) (k : ℕ) (h : ∀ j : ℕ, j < k → f j = g j) :
    hval f k = hval g k := by
  unfold hval
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem hval_succ (f : ℕ → ℤ) (k : ℕ) :
    hval f (k + 1) = f 0 * (16 : ℤ) ^ k + hval (fun j => f (j + 1)) k := by
  unfold hval
  rw [Finset.sum_range_succ']
  have h : ∑ j ∈ Finset.range k, f (j + 1) * (16 : ℤ) ^ (k + 1 - 1 - (j + 1))
      = ∑ j ∈ Finset.range k, f (j + 1) * (16 : ℤ) ^ (k - 1 - j) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 2
    omega
  rw [h]
  have hk0 : k + 1 - 1 - 0 = k := by omega
  rw [hk0]
  ring

theorem hval_mem : ∀ (k : ℕ) (f : ℕ → ℤ),
    (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < 16) →
      0 ≤ hval f k ∧ hval f k < (16 : ℤ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro f _
    rw [hval_zero]
    exact ⟨le_refl 0, by norm_num⟩
  | succ k ih =>
    intro f hf
    have hbk : (0 : ℤ) < (16 : ℤ) ^ k := by positivity
    have htail := ih (fun j => f (j + 1)) (fun j hj => hf (j + 1) (by omega))
    have h0 := hf 0 (Nat.succ_pos k)
    rw [hval_succ]
    have hmul : 0 ≤ f 0 * (16 : ℤ) ^ k := mul_nonneg h0.1 hbk.le
    refine ⟨by linarith [htail.1], ?_⟩
    have h1 : f 0 * (16 : ℤ) ^ k ≤ ((16 : ℤ) - 1) * (16 : ℤ) ^ k := by
      refine mul_le_mul_of_nonneg_right ?_ hbk.le
      linarith [h0.2]
    have h2 : ((16 : ℤ) - 1) * (16 : ℤ) ^ k + (16 : ℤ) ^ k = (16 : ℤ) ^ (k + 1) := by
      rw [pow_succ]; ring
    linarith [htail.2]

theorem hval_inj : ∀ (k : ℕ) (f g : ℕ → ℤ),
    (∀ j : ℕ, j < k → 0 ≤ f j ∧ f j < 16) →
    (∀ j : ℕ, j < k → 0 ≤ g j ∧ g j < 16) →
    hval f k = hval g k → ∀ j : ℕ, j < k → f j = g j := by
  intro k
  induction k with
  | zero =>
    intro f g _ _ _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro f g hf hg heq j hj
    have hbk : (0 : ℤ) < (16 : ℤ) ^ k := by positivity
    have hFt := hval_mem k (fun i => f (i + 1)) (fun i hi => hf (i + 1) (by omega))
    have hGt := hval_mem k (fun i => g (i + 1)) (fun i hi => hg (i + 1) (by omega))
    rw [hval_succ, hval_succ] at heq
    have h0 : f 0 = g 0 := by
      rcases lt_trichotomy (f 0) (g 0) with h | h | h
      · exfalso
        have hle : (f 0 + 1) * (16 : ℤ) ^ k ≤ g 0 * (16 : ℤ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) hbk.le
        linarith [hFt.1, hFt.2, hGt.1, hGt.2]
      · exact h
      · exfalso
        have hle : (g 0 + 1) * (16 : ℤ) ^ k ≤ f 0 * (16 : ℤ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) hbk.le
        linarith [hFt.1, hFt.2, hGt.1, hGt.2]
    have htails : hval (fun i => f (i + 1)) k = hval (fun i => g (i + 1)) k := by
      rw [h0] at heq
      linarith
    cases j with
    | zero => exact h0
    | succ j' =>
      exact ih (fun i => f (i + 1)) (fun i => g (i + 1))
        (fun i hi => hf (i + 1) (by omega)) (fun i hi => hg (i + 1) (by omega))
        htails j' (by omega)

theorem validWord_ofFn {m : ℕ} (g : Fin m → ℤ)
    (h : ∀ i : Fin m, 0 ≤ g i ∧ g i < 16) : ValidWord 16 (List.ofFn g) := by
  intro i
  have hi : i.val < m := by
    have hlt := i.isLt
    simpa using hlt
  have hget : (List.ofFn g).get i = g ⟨i.val, hi⟩ := by
    simp [List.get_eq_getElem]
  rw [hget]
  have := h ⟨i.val, hi⟩
  constructor
  · exact this.1
  · have h16 : (((16 : ℕ) : ℤ)) = (16 : ℤ) := by norm_num
    rw [h16]
    exact this.2

theorem occursAt_ofFn {m : ℕ} (x : ℝ) (g : Fin m → ℤ) (n : ℕ)
    (h : OccursAt 16 x (List.ofFn g) n) (p : ℕ) (hp : p < m) :
    baseDigit 16 x (n + p) = g ⟨p, hp⟩ := by
  have hp' : p < (List.ofFn g).length := by simpa using hp
  refine (h ⟨p, hp'⟩).trans ?_
  simp [List.get_eq_getElem]

/-! ### The hexadecimal orbit -/

/-- The hexadecimal fractional-part orbit. -/
def orb (x : ℝ) (n : ℕ) : ℝ := Int.fract ((16 : ℝ) ^ n * Int.fract x)

theorem orb_nonneg (x : ℝ) (n : ℕ) : 0 ≤ orb x n := Int.fract_nonneg _

theorem orb_lt_one (x : ℝ) (n : ℕ) : orb x n < 1 := Int.fract_lt_one _

theorem orb_eq_fract (x : ℝ) (n : ℕ) :
    orb x n = Int.fract ((16 : ℝ) ^ n * x) := by
  have hfx : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  have hrw : (16 : ℝ) ^ n * Int.fract x
      = (16 : ℝ) ^ n * x - (((16 ^ n * ⌊x⌋ : ℤ)) : ℝ) := by
    rw [hfx]
    push_cast
    ring
  rw [orb, hrw, Int.fract_sub_intCast]

theorem baseDigit16_eq (x : ℝ) (n : ℕ) :
    baseDigit 16 x n
      = ⌊(16 : ℝ) ^ (n + 1) * Int.fract x⌋ - 16 * ⌊(16 : ℝ) ^ n * Int.fract x⌋ := by
  unfold baseDigit
  norm_num

theorem sixteen_split (x : ℝ) (n : ℕ) :
    (16 : ℝ) ^ (n + 1) * Int.fract x
      = (((16 * ⌊(16 : ℝ) ^ n * Int.fract x⌋ : ℤ)) : ℝ)
        + (16 : ℝ) * Int.fract ((16 : ℝ) ^ n * Int.fract x) := by
  have h := Int.floor_add_fract ((16 : ℝ) ^ n * Int.fract x)
  have hfr : (16 : ℝ) ^ (n + 1) * Int.fract x
      = (16 : ℝ) * ((16 : ℝ) ^ n * Int.fract x) := by
    rw [pow_succ]; ring
  rw [hfr]
  push_cast
  linarith [h]

theorem baseDigit_eq_floor (x : ℝ) (n : ℕ) :
    baseDigit 16 x n = ⌊(16 : ℝ) * orb x n⌋ := by
  rw [baseDigit16_eq, sixteen_split, Int.floor_intCast_add, orb]
  ring

theorem orb_succ (x : ℝ) (n : ℕ) :
    orb x (n + 1) = Int.fract ((16 : ℝ) * orb x n) := by
  rw [orb, orb, sixteen_split, Int.fract_intCast_add]

theorem baseDigit_bounds16 (x : ℝ) (n : ℕ) :
    0 ≤ baseDigit 16 x n ∧ baseDigit 16 x n < 16 := by
  rw [baseDigit_eq_floor]
  constructor
  · refine Int.floor_nonneg.mpr ?_
    have := orb_nonneg x n
    linarith
  · refine Int.floor_lt.mpr ?_
    have := orb_lt_one x n
    push_cast
    linarith

theorem floor_block (x : ℝ) : ∀ (L n : ℕ),
    ⌊(16 : ℝ) ^ L * orb x n⌋ = hval (fun j => baseDigit 16 x (n + j)) L := by
  intro L
  induction L with
  | zero =>
    intro n
    rw [hval_zero, pow_zero, one_mul]
    exact Int.floor_eq_zero_iff.mpr ⟨orb_nonneg x n, orb_lt_one x n⟩
  | succ L ih =>
    intro n
    have hstep : (16 : ℝ) * orb x n
        = ((baseDigit 16 x n : ℤ) : ℝ) + orb x (n + 1) := by
      rw [baseDigit_eq_floor, orb_succ]
      exact (Int.floor_add_fract ((16 : ℝ) * orb x n)).symm
    have hexp : (16 : ℝ) ^ (L + 1) * orb x n
        = ((((16 : ℤ) ^ L * baseDigit 16 x n : ℤ)) : ℝ)
          + (16 : ℝ) ^ L * orb x (n + 1) := by
      calc (16 : ℝ) ^ (L + 1) * orb x n
          = (16 : ℝ) ^ L * ((16 : ℝ) * orb x n) := by ring
        _ = (16 : ℝ) ^ L * (((baseDigit 16 x n : ℤ) : ℝ) + orb x (n + 1)) := by
            rw [hstep]
        _ = ((((16 : ℤ) ^ L * baseDigit 16 x n : ℤ)) : ℝ)
              + (16 : ℝ) ^ L * orb x (n + 1) := by push_cast; ring
    rw [hexp, Int.floor_intCast_add, ih (n + 1), hval_succ]
    have hshift : hval (fun j => baseDigit 16 x (n + 1 + j)) L
        = hval (fun j => baseDigit 16 x (n + (j + 1))) L := by
      refine hval_congr _ _ L ?_
      intro j _
      congr 1
      omega
    rw [hshift]
    have hn0 : n + 0 = n := by omega
    rw [hn0]
    ring

/-! ### The contracted theorem -/

theorem P5_iff_digitDisjunctive_sixteen
    (hShadow :
      (∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
          ∃ n : ℕ, N ≤ n ∧
            dist (Theory.PiDigits.T201BaileyCrandallShadow.bcOrbit n) q < r) ↔
        ∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
          ∃ n : ℕ, N ≤ n ∧
            dist (Theory.PiDigits.T201BaileyCrandallShadow.hexPiOrbit n) q < r) :
    P5 ↔ DigitDisjunctive 16 Real.pi := by
  have hHex : ∀ n : ℕ, Theory.PiDigits.T201BaileyCrandallShadow.hexPiOrbit n
      = ((orb Real.pi n : ℝ) : UnitAddCircle) := by
    intro n
    rw [orb_eq_fract, AddCircle.coe_fract]
    rfl
  have hP5 : P5 ↔ (∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
      ∃ n : ℕ, N ≤ n ∧
        dist (Theory.PiDigits.T201BaileyCrandallShadow.bcOrbit n) q < r) := by
    constructor
    · intro hp5 q N r hr
      obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = q :=
        ⟨q.out, Quotient.out_eq q⟩
      have haq : ((Int.fract t : ℝ) : UnitAddCircle) = q := by
        rw [AddCircle.coe_fract]; exact ht
      have ha0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
      have ha1 : Int.fract t < 1 := Int.fract_lt_one t
      have hlo_le : max 0 (Int.fract t - r / 2) ≤ Int.fract t :=
        max_le ha0 (by linarith)
      have ha_hi : Int.fract t < min 1 (Int.fract t + r / 2) :=
        lt_min ha1 (by linarith)
      obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn
        (show max 0 (Int.fract t - r / 2) < min 1 (Int.fract t + r / 2) by linarith)
      obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn hv1
      have hlo0 : (0 : ℝ) ≤ max 0 (Int.fract t - r / 2) := le_max_left _ _
      have hu0 : (0 : ℚ) ≤ u := by
        have : (0 : ℝ) < (u : ℝ) := lt_of_le_of_lt hlo0 hu1
        exact_mod_cast this.le
      have huv : u < v := by exact_mod_cast hu2
      have hv1' : v ≤ (1 : ℚ) := by
        have : (v : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hv2 (min_le_left _ _))
        exact_mod_cast this
      obtain ⟨n, hnN, hny1, hny2⟩ := hp5 u v (N + 1) hu0 huv hv1'
      refine ⟨n - 1, by omega, ?_⟩
      have hbc : Theory.PiDigits.T201BaileyCrandallShadow.bcOrbit (n - 1)
          = ((Theory.PiDigits.T201BaileyCrandallShadow.y (n - 1 + 1) : ℝ) :
            UnitAddCircle) := rfl
      rw [hbc, show n - 1 + 1 = n by omega, ← haq]
      refine lt_of_le_of_lt (dist_coe_le_abs _ _) ?_
      have h1 : max 0 (Int.fract t - r / 2)
          < Theory.PiDigits.T201BaileyCrandallShadow.y n := lt_trans hu1 hny1
      have h2 : Theory.PiDigits.T201BaileyCrandallShadow.y n
          < min 1 (Int.fract t + r / 2) := lt_trans hny2 hv2
      have hlor : Int.fract t - r / 2 ≤ max 0 (Int.fract t - r / 2) := le_max_right _ _
      have hhir : min 1 (Int.fract t + r / 2) ≤ Int.fract t + r / 2 := min_le_right _ _
      rw [abs_lt]
      constructor <;> linarith
    · intro hA u v N hu0 huv hv1
      have hu0' : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0
      have huv' : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
      have hv1' : (v : ℝ) ≤ 1 := by exact_mod_cast hv1
      set a : ℝ := ((u : ℝ) + (v : ℝ)) / 2 with hadef
      have hau : (u : ℝ) < a := by rw [hadef]; linarith
      have hav : a < (v : ℝ) := by rw [hadef]; linarith
      have ha0 : 0 < a := lt_of_le_of_lt hu0' hau
      have ha1 : a < 1 := lt_of_lt_of_le hav hv1'
      set r : ℝ := min (((v : ℝ) - (u : ℝ)) / 4) (min (a / 2) ((1 - a) / 2)) with hrdef
      have hr : 0 < r := by
        rw [hrdef]
        exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
      have hr1 : r ≤ ((v : ℝ) - (u : ℝ)) / 4 := by rw [hrdef]; exact min_le_left _ _
      have hr2 : r ≤ a / 2 := by
        rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hr3 : r ≤ (1 - a) / 2 := by
        rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
      obtain ⟨n, hnN, hdist⟩ := hA ((a : ℝ) : UnitAddCircle) N r hr
      have hbc : Theory.PiDigits.T201BaileyCrandallShadow.bcOrbit n
          = ((Theory.PiDigits.T201BaileyCrandallShadow.y (n + 1) : ℝ) :
            UnitAddCircle) := rfl
      rw [hbc, dist_coe_eq_abs] at hdist
      set b : ℝ := Theory.PiDigits.T201BaileyCrandallShadow.y (n + 1) with hbdef
      have hb0 : 0 ≤ b := by rw [hbdef]; exact Int.fract_nonneg _
      have hb1 : b < 1 := by rw [hbdef]; exact Int.fract_lt_one _
      set m : ℤ := round (b - a) with hmdef
      have hm0 : m = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmR : ((m : ℝ)) ≤ -1 := by
            have : m ≤ -1 := by omega
            exact_mod_cast this
          have hup := (abs_lt.mp hdist).2
          linarith
        · have hmR : (1 : ℝ) ≤ ((m : ℝ)) := by
            have : 1 ≤ m := by omega
            exact_mod_cast this
          have hlow := (abs_lt.mp hdist).1
          linarith
      rw [hm0] at hdist
      have habs : |b - a| < r := by
        have : ((0 : ℤ) : ℝ) = 0 := by norm_num
        rw [this, sub_zero] at hdist
        exact hdist
      have hlt := abs_lt.mp habs
      exact ⟨n + 1, by omega, by linarith [hlt.1, hlt.2], by linarith [hlt.1, hlt.2]⟩
  have hD16 : DigitDisjunctive 16 Real.pi ↔
      (∀ q : UnitAddCircle, ∀ N : ℕ, ∀ r : ℝ, 0 < r →
        ∃ n : ℕ, N ≤ n ∧
          dist (Theory.PiDigits.T201BaileyCrandallShadow.hexPiOrbit n) q < r) := by
    constructor
    · intro hD q N r hr
      obtain ⟨t, ht⟩ : ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = q :=
        ⟨q.out, Quotient.out_eq q⟩
      have haq : ((Int.fract t : ℝ) : UnitAddCircle) = q := by
        rw [AddCircle.coe_fract]; exact ht
      obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hr (show (16 : ℝ)⁻¹ < 1 by norm_num)
      rw [inv_pow] at hL
      set a : ℝ := Int.fract t with hadef
      have hfa : Int.fract a = a := by rw [hadef]; exact Int.fract_fract t
      obtain ⟨n, hn⟩ := hD
        (List.ofFn (fun j : Fin (N + L) =>
          if j.val < N then 0 else baseDigit 16 a (j.val - N)))
        (validWord_ofFn _ (fun j => by
          by_cases h : j.val < N
          · rw [if_pos h]; norm_num
          · rw [if_neg h]; exact baseDigit_bounds16 a (j.val - N)))
      refine ⟨n + N, Nat.le_add_left N n, ?_⟩
      have hmatch : ∀ i : ℕ, i < L →
          baseDigit 16 Real.pi (n + N + i) = baseDigit 16 a i := by
        intro i hi
        have hp : N + i < N + L := by omega
        have hocc := occursAt_ofFn Real.pi _ n hn (N + i) hp
        rw [show n + (N + i) = n + N + i by omega] at hocc
        rw [hocc]
        have hgo : (if (N + i) < N then (0 : ℤ) else baseDigit 16 a ((N + i) - N))
            = baseDigit 16 a i := by
          rw [if_neg (by omega)]
          congr 1
          omega
        exact hgo
      have horb0 : orb a 0 = a := by
        rw [orb, pow_zero, one_mul, hfa, hfa]
      have hcong : hval (fun j => baseDigit 16 Real.pi (n + N + j)) L
          = hval (fun j => baseDigit 16 a (0 + j)) L := by
        refine hval_congr _ _ L ?_
        intro j hj
        rw [show 0 + j = j by omega]
        exact hmatch j hj
      have hfloor_eq : ⌊(16 : ℝ) ^ L * orb Real.pi (n + N)⌋ = ⌊(16 : ℝ) ^ L * a⌋ := by
        rw [floor_block Real.pi L (n + N), hcong, ← floor_block a L 0, horb0]
      have hpow : (0 : ℝ) < (16 : ℝ) ^ L := by positivity
      have hX := Int.floor_le ((16 : ℝ) ^ L * orb Real.pi (n + N))
      have hX' := Int.lt_floor_add_one ((16 : ℝ) ^ L * orb Real.pi (n + N))
      have hY := Int.floor_le ((16 : ℝ) ^ L * a)
      have hY' := Int.lt_floor_add_one ((16 : ℝ) ^ L * a)
      rw [hfloor_eq] at hX hX'
      have hone : 1 < r * (16 : ℝ) ^ L := by
        have h := mul_lt_mul_of_pos_right hL hpow
        rwa [inv_mul_cancel₀ (ne_of_gt hpow)] at h
      have hup : orb Real.pi (n + N) - a < r := by
        have hlt1 : (16 : ℝ) ^ L * (orb Real.pi (n + N) - a) < (16 : ℝ) ^ L * r := by
          nlinarith
        exact lt_of_mul_lt_mul_left hlt1 hpow.le
      have hdn : a - orb Real.pi (n + N) < r := by
        have hlt2 : (16 : ℝ) ^ L * (a - orb Real.pi (n + N)) < (16 : ℝ) ^ L * r := by
          nlinarith
        exact lt_of_mul_lt_mul_left hlt2 hpow.le
      rw [hHex (n + N), ← haq]
      refine lt_of_le_of_lt (dist_coe_le_abs _ _) ?_
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    · intro hdense w hw
      have hpadb : ∀ j : ℕ, 0 ≤ padWord w j ∧ padWord w j < 16 := by
        intro j
        by_cases h : j < w.length
        · rw [padWord_lt w j h]
          have hj := hw ⟨j, h⟩
          have h16 : ((16 : ℕ) : ℤ) = 16 := by norm_num
          rw [h16] at hj
          exact hj
        · rw [padWord_ge w j h]; norm_num
      have hv := hval_mem w.length (padWord w) (fun j _ => hpadb j)
      have hpow : (0 : ℝ) < (16 : ℝ) ^ w.length := by positivity
      have hvR0 : (0 : ℝ) ≤ ((hval (padWord w) w.length : ℤ) : ℝ) := by
        exact_mod_cast hv.1
      have hvR1 : ((hval (padWord w) w.length : ℤ) : ℝ) + 1 ≤ (16 : ℝ) ^ w.length := by
        have h1 : hval (padWord w) w.length + 1 ≤ (16 : ℤ) ^ w.length := hv.2
        exact_mod_cast h1
      set a : ℝ := (((hval (padWord w) w.length : ℤ) : ℝ) + 1 / 2)
        / (16 : ℝ) ^ w.length with hadef
      set r : ℝ := (1 / 4) * ((16 : ℝ) ^ w.length)⁻¹ with hrdef
      have hr : 0 < r := by rw [hrdef]; positivity
      have hainv : a * (16 : ℝ) ^ w.length
          = ((hval (padWord w) w.length : ℤ) : ℝ) + 1 / 2 := by
        rw [hadef]
        field_simp
      have hrinv : r * (16 : ℝ) ^ w.length = 1 / 4 := by
        rw [hrdef]
        field_simp
      have ha_lb : 2 * r ≤ a := by
        have h1 : (2 * r) * (16 : ℝ) ^ w.length ≤ a * (16 : ℝ) ^ w.length := by
          rw [hainv]
          nlinarith [hrinv, hvR0]
        exact le_of_mul_le_mul_right h1 hpow
      have ha_ub : a ≤ 1 - 2 * r := by
        have h1 : a * (16 : ℝ) ^ w.length ≤ (1 - 2 * r) * (16 : ℝ) ^ w.length := by
          rw [hainv]
          nlinarith [hrinv, hvR1]
        exact le_of_mul_le_mul_right h1 hpow
      obtain ⟨n, _, hdist⟩ := hdense ((a : ℝ) : UnitAddCircle) 0 r hr
      rw [hHex n, dist_coe_eq_abs] at hdist
      have hb0 : 0 ≤ orb Real.pi n := orb_nonneg _ _
      have hb1 : orb Real.pi n < 1 := orb_lt_one _ _
      set m : ℤ := round (orb Real.pi n - a) with hmdef
      have hm0 : m = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmR : ((m : ℝ)) ≤ -1 := by
            have : m ≤ -1 := by omega
            exact_mod_cast this
          have hup := (abs_lt.mp hdist).2
          linarith
        · have hmR : (1 : ℝ) ≤ ((m : ℝ)) := by
            have : 1 ≤ m := by omega
            exact_mod_cast this
          have hlow := (abs_lt.mp hdist).1
          linarith
      rw [hm0] at hdist
      have habs : |orb Real.pi n - a| < r := by
        have hz : ((0 : ℤ) : ℝ) = 0 := by norm_num
        rw [hz, sub_zero] at hdist
        exact hdist
      have hlt := abs_lt.mp habs
      have hfl : ⌊(16 : ℝ) ^ w.length * orb Real.pi n⌋ = hval (padWord w) w.length := by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        · have h1 : ((hval (padWord w) w.length : ℤ) : ℝ) + 1 / 4
              ≤ (16 : ℝ) ^ w.length * orb Real.pi n := by
            nlinarith [hlt.1, hainv, hrinv]
          linarith
        · have h1 : (16 : ℝ) ^ w.length * orb Real.pi n
              ≤ ((hval (padWord w) w.length : ℤ) : ℝ) + 3 / 4 := by
            nlinarith [hlt.2, hainv, hrinv]
          push_cast
          linarith
      refine ⟨n, ?_⟩
      intro i
      have hi : i.val < w.length := i.isLt
      have heq : hval (fun j => baseDigit 16 Real.pi (n + j)) w.length
          = hval (padWord w) w.length := by
        rw [← floor_block Real.pi w.length n, hfl]
      have hkey := hval_inj w.length _ _
        (fun j _ => baseDigit_bounds16 Real.pi (n + j))
        (fun j _ => hpadb j) heq i.val hi
      rw [hkey]
      exact padWord_lt w i.val hi
  exact hP5.trans (hShadow.trans hD16.symm)


end HexLayer

/-! ### `P5 ↔ D2`

Task `pi-t205-power-base-06-p5-iff-two`. -/

theorem P5_iff_digitDisjunctive_two
    (hP5Hex : P5 ↔ DigitDisjunctive 16 Real.pi)
    (hHexTwo : DigitDisjunctive 16 Real.pi ↔ DigitDisjunctive 2 Real.pi) :
    P5 ↔ DigitDisjunctive 2 Real.pi :=
  hP5Hex.trans hHexTwo


/-! ### Discharged forms

Tasks 03, 04, 05 and 06 keep their exact prerequisite contracts as hypotheses;
the siblings above and promoted T201 supply them unconditionally. -/

theorem digitDisjunctive_power_iff_discharged
    {b k : ℕ} (hb : 2 ≤ b) (hk : 0 < k) (x : ℝ) :
    DigitDisjunctive (b ^ k) x ↔ DigitDisjunctive b x :=
  digitDisjunctive_power_iff
    (fun {_} hb' x' n' => baseDigit_bounds hb' x' n')
    (fun {_ _} hb' hk' x' n' => baseDigit_power_group hb' hk' x' n') hb hk x

theorem digitDisjunctive_sixteen_iff_two_discharged :
    DigitDisjunctive 16 Real.pi ↔ DigitDisjunctive 2 Real.pi :=
  digitDisjunctive_sixteen_iff_two
    (fun {_ _} hb' hk' x' => digitDisjunctive_power_iff_discharged hb' hk' x')

theorem P5_iff_digitDisjunctive_sixteen_discharged :
    P5 ↔ DigitDisjunctive 16 Real.pi :=
  HexLayer.P5_iff_digitDisjunctive_sixteen
    Theory.PiDigits.T201BaileyCrandallShadow.circleDenseLate_bc_iff_hex

theorem P5_iff_digitDisjunctive_two_discharged :
    P5 ↔ DigitDisjunctive 2 Real.pi :=
  P5_iff_digitDisjunctive_two P5_iff_digitDisjunctive_sixteen_discharged
    digitDisjunctive_sixteen_iff_two_discharged

end Theory.PiDigits.T205PowerBaseDisjunctivity

end
