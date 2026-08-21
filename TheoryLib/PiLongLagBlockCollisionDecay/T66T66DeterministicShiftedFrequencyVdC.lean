import TheoryLib.PiLongLagBlockCollisionDecay.T63T63ExactFiniteFourthMoment

/-!
# T66: deterministic shifted-frequency van der Corput core

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves only a conditional residual-A12 primitive-sector implication.
It does not prove its shifted-correlation premise at `Real.pi`, the full T29
predicate, C2, C3, C1, or the canonical collision estimate.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T66

open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T49
open Theory.PiDigits.LongLagBlockCollisionDecay.T56
open Theory.PiDigits.LongLagBlockCollisionDecay.T59
open Theory.PiDigits.LongLagBlockCollisionDecay.T63

/-- The literal dyadic endpoint `N_t = 4 * 2^t + 1`. -/
def N (t : ℕ) : ℕ := 4 * 2 ^ t + 1

/-- The literal integer cutoff `H_t = ceil(sqrt(N_t))`. -/
def H (t : ℕ) : ℕ := Nat.ceil (Real.sqrt (N t : ℝ))

/-- The exact shifted integer frequency
`h * (10^r - 1) * 10^k`. -/
def shiftedFrequency (h r k : ℕ) : ℕ :=
  h * (10 ^ r - 1) * 10 ^ k

/-- The exact fixed-pi shifted character at the displayed frequency. -/
def shiftedCharacter (h r k : ℕ) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      (shiftedFrequency h r k : ℂ) * (Real.pi : ℂ))

/-- The exact half-open shifted sum over `k < N_t-r`. -/
def shiftedSum (t h r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N t - r), shiftedCharacter h r k

/-- The exact triangularly weighted shifted energy. -/
def triangularEnergy (t h : ℕ) : ℝ :=
  (H t : ℝ) * N t +
    2 * ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) * (shiftedSum t h r).re

/-- One nonnegative constant controls every literal dyadic scale and every
inclusive frequency `1 <= h <= 10`. This proposition is not asserted at pi. -/
def FixedPiShiftedCorrelation (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
    triangularEnergy t h ≤ K * (H t : ℝ) * N t

/-- The square-free part of the exact T63 polynomial, summed over the ten
literal frequencies. -/
def firstMoment (t : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (N t)

/-- The fourth moment at the literal endpoint. -/
def fourthMoment (t : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (N t) ^ 2

/-- The complete T63 lower-order polynomial, with no term discarded. -/
def T63Polynomial (t : ℕ) : ℝ :=
  fourthMoment t - 4 * (N t - 1) * firstMoment t +
    20 * (N t : ℝ) ^ 2 - 30 * N t

/-- The literal T29 width at this one-block scale. -/
def literalWidth (t : ℕ) : ℝ :=
  Real.sqrt ((N t : ℝ) ^ 2 - 1)

/-- The selected-plus-defect primitive contribution, retaining both signed
orientations, the ten frequencies, and the literal width. -/
def selectedDefectContribution (Q0 t : ℕ) : ℝ :=
  (2 : ℝ) * (
    (∑ p ∈ selectedRecordDomain t,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
          (blockDifferenceValue p : ℝ))) / literalWidth t) +
    (∑ p ∈ unmatchedDefect Q0 t,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
          (blockDifferenceValue p : ℝ))) / literalWidth t))

theorem N_literal (t : ℕ) : N t = 4 * 2 ^ t + 1 := by
  rfl

theorem H_literal (t : ℕ) : H t = Nat.ceil (Real.sqrt (N t : ℝ)) := by
  rfl

theorem shiftedSum_literal (t h r : ℕ) :
    shiftedSum t h r =
      ∑ k ∈ Finset.range (N t - r),
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            (h * (10 ^ r - 1) * 10 ^ k : ℕ) * (Real.pi : ℂ)) := by
  rfl

theorem triangularEnergy_literal (t h : ℕ) :
    triangularEnergy t h =
      (H t : ℝ) * N t +
        2 * ∑ r ∈ Finset.Ico 1 (H t),
          ((H t - r : ℕ) : ℝ) *
            (∑ k ∈ Finset.range (N t - r),
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I *
                  (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                    (Real.pi : ℂ))).re := by
  rfl

/-- Exact correlation identity with T63's orbit points. -/
theorem shiftedCharacter_eq_orbitCorrelation (h r k : ℕ) :
    shiftedCharacter h r k =
      u (k + r) ^ h * conj (u k ^ h) := by
  rw [u_pow_eq_phase, u_pow_eq_phase,
    phase_mul_conj_phase_eq_sub_real]
  unfold shiftedCharacter shiftedFrequency Theory.PiDigits.T27.phase
  congr 1
  have hr : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
  rw [pow_add]
  push_cast [Nat.cast_sub hr]
  ring

/-- Zero-extended moving window used only to prove the deterministic
van der Corput inequality. -/
def movingWindow (h N H n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    if k ≤ n ∧ n < k + H then u k ^ h else 0

theorem sum_movingWindow
    {N0 H0 : ℕ} (hN : 0 < N0) (hH : 0 < H0) (h : ℕ) :
    (∑ n ∈ Finset.range (N0 + H0 - 1), movingWindow h N0 H0 n) =
      (H0 : ℂ) * T h N0 := by
  classical
  unfold movingWindow T
  rw [Finset.sum_comm]
  calc
    (∑ k ∈ Finset.range N0,
        ∑ n ∈ Finset.range (N0 + H0 - 1),
          if k ≤ n ∧ n < k + H0 then u k ^ h else 0) =
        ∑ k ∈ Finset.range N0, (H0 : ℂ) * u k ^ h := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < N0 := Finset.mem_range.mp hk
      have htop : k + H0 ≤ N0 + H0 - 1 := by omega
      have hfilter :
          (Finset.range (N0 + H0 - 1)).filter
              (fun n => k ≤ n ∧ n < k + H0) =
            Finset.Ico k (k + H0) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      rw [Nat.add_sub_cancel_left]
    _ = (H0 : ℂ) * ∑ k ∈ Finset.range N0, u k ^ h := by
      rw [Finset.mul_sum]

theorem normSq_finset_sum
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) =
      ∑ x ∈ s, ∑ y ∈ s, (f x * conj (f y)).re := by
  rw [Complex.normSq_apply]
  rw [Complex.re_sum, Complex.im_sum]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  simp [Complex.mul_re]

theorem triangular_gap_reindex
    (N0 H0 : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range N0, ∑ l ∈ Finset.range k,
      ((H0 - (k - l) : ℕ) : ℝ) * f k l) =
      ∑ r ∈ Finset.Ico 1 H0, ((H0 - r : ℕ) : ℝ) *
        ∑ q ∈ Finset.range (N0 - r), f (q + r) q := by
  classical
  let A : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.range N0).sigma fun k =>
      (Finset.range k).filter fun l => k - l < H0
  let B : Finset (Sigma fun _ : ℕ => ℕ) :=
    (Finset.Ico 1 H0).sigma fun r => Finset.range (N0 - r)
  have hleft :
      (∑ k ∈ Finset.range N0, ∑ l ∈ Finset.range k,
        ((H0 - (k - l) : ℕ) : ℝ) * f k l) =
        ∑ a ∈ A, ((H0 - (a.1 - a.2) : ℕ) : ℝ) * f a.1 a.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hgap : k - l < H0
    · simp [hgap]
    · have hzero : H0 - (k - l) = 0 := Nat.sub_eq_zero_of_le (by omega)
      simp [hgap, hzero]
  have hright :
      (∑ r ∈ Finset.Ico 1 H0, ((H0 - r : ℕ) : ℝ) *
        ∑ q ∈ Finset.range (N0 - r), f (q + r) q) =
        ∑ b ∈ B, ((H0 - b.1 : ℕ) : ℝ) * f (b.2 + b.1) b.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  rw [hleft, hright]
  refine Finset.sum_bij'
      (fun a _ => ⟨a.1 - a.2, a.2⟩)
      (fun b _ => ⟨b.2 + b.1, b.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rcases a with ⟨k, l⟩
    simp only [A, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at ha
    simp only [B, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range]
    have hback : l + (k - l) = k := Nat.add_sub_of_le (Nat.le_of_lt ha.2.1)
    omega
  · intro b hb
    rcases b with ⟨r, q⟩
    simp only [B, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hb
    simp only [A, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
    omega
  · intro a ha
    rcases a with ⟨k, l⟩
    simp only [A, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at ha
    apply Sigma.ext
    · have hback : l + (k - l) = k := Nat.add_sub_of_le (Nat.le_of_lt ha.2.1)
      omega
    · simp
  · intro b hb
    rcases b with ⟨r, q⟩
    simp only [B, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hb
    apply Sigma.ext
    · simp
    · simp
  · intro a ha
    rcases a with ⟨k, l⟩
    simp only [A, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at ha
    have hback : l + (k - l) = k := Nat.add_sub_of_le (Nat.le_of_lt ha.2.1)
    rw [hback]

theorem movingWindow_pair_sum
    {N0 H0 k l : ℕ} (hk : k < N0) (hl : l < N0) (h : ℕ) :
    (∑ n ∈ Finset.range (N0 + H0 - 1),
      ((if k ≤ n ∧ n < k + H0 then u k ^ h else 0) *
        conj (if l ≤ n ∧ n < l + H0 then u l ^ h else 0)).re) =
      ((H0 - (if l ≤ k then k - l else l - k) : ℕ) : ℝ) *
        (u k ^ h * conj (u l ^ h)).re := by
  classical
  let c : ℝ := (u k ^ h * conj (u l ^ h)).re
  have hterm (n : ℕ) :
      ((if k ≤ n ∧ n < k + H0 then u k ^ h else 0) *
        conj (if l ≤ n ∧ n < l + H0 then u l ^ h else 0)).re =
      if (k ≤ n ∧ n < k + H0) ∧ (l ≤ n ∧ n < l + H0) then c else 0 := by
    by_cases hk' : k ≤ n ∧ n < k + H0 <;>
      by_cases hl' : l ≤ n ∧ n < l + H0 <;>
      simp [hk', hl', c]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  by_cases hlk : l ≤ k
  · have htop : l + H0 ≤ N0 + H0 - 1 := by omega
    have hfilter :
        (Finset.range (N0 + H0 - 1)).filter
            (fun n => (k ≤ n ∧ n < k + H0) ∧
              (l ≤ n ∧ n < l + H0)) =
          Finset.Ico k (l + H0) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, if_pos hlk]
    congr 1
    norm_cast
    omega
  · have hkl : k < l := lt_of_not_ge hlk
    have htop : k + H0 ≤ N0 + H0 - 1 := by omega
    have hfilter :
        (Finset.range (N0 + H0 - 1)).filter
            (fun n => (k ≤ n ∧ n < k + H0) ∧
              (l ≤ n ∧ n < l + H0)) =
          Finset.Ico l (k + H0) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, if_neg hlk]
    congr 1
    norm_cast
    omega

theorem symmetric_double_sum
    (N0 : ℕ) (f : ℕ → ℕ → ℝ) (hsymm : ∀ k l, f k l = f l k) :
    (∑ k ∈ Finset.range N0, ∑ l ∈ Finset.range N0, f k l) =
      (∑ k ∈ Finset.range N0, f k k) +
        2 * ∑ k ∈ Finset.range N0, ∑ l ∈ Finset.range k, f k l := by
  induction N0 with
  | zero => simp
  | succ N0 ih =>
      simp only [Finset.sum_range_succ]
      have hcross : (∑ k ∈ Finset.range N0, f k N0) =
          ∑ k ∈ Finset.range N0, f N0 k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hsymm k N0
      rw [Finset.sum_add_distrib]
      rw [ih, hcross]
      ring

/-- Expansion of the zero-extended moving-window square. This is the exact
finite identity producing `H-r`, `k < N-r`, and no boundary remainder. -/
theorem sum_normSq_movingWindow_eq_triangularEnergy (t h : ℕ) :
    (∑ n ∈ Finset.range (N t + H t - 1),
      Complex.normSq (movingWindow h (N t) (H t) n)) =
        triangularEnergy t h := by
  classical
  unfold triangularEnergy shiftedSum
  simp_rw [shiftedCharacter_eq_orbitCorrelation]
  unfold movingWindow
  simp_rw [normSq_finset_sum]
  let g : ℕ → ℕ → ℝ := fun k l => (u k ^ h * conj (u l ^ h)).re
  let f : ℕ → ℕ → ℝ := fun k l =>
    ((H t - (if l ≤ k then k - l else l - k) : ℕ) : ℝ) * g k l
  have htriple :
      (∑ n ∈ Finset.range (N t + H t - 1),
        ∑ k ∈ Finset.range (N t),
          ∑ l ∈ Finset.range (N t),
            ((if k ≤ n ∧ n < k + H t then u k ^ h else 0) *
              conj (if l ≤ n ∧ n < l + H t then u l ^ h else 0)).re) =
        ∑ k ∈ Finset.range (N t), ∑ l ∈ Finset.range (N t), f k l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    simpa only [f, g] using movingWindow_pair_sum
      (Finset.mem_range.mp hk) (Finset.mem_range.mp hl) h
  rw [htriple]
  have hsymm : ∀ k l, f k l = f l k := by
    intro k l
    unfold f g
    have hre : (u k ^ h * conj (u l ^ h)).re =
        (u l ^ h * conj (u k ^ h)).re := by
      rw [show u l ^ h * conj (u k ^ h) =
          conj (u k ^ h * conj (u l ^ h)) by
        simp only [map_mul, starRingEnd_self_apply]
        ring]
      exact (Complex.conj_re _).symm
    rw [hre]
    by_cases hlk : l ≤ k
    · by_cases hkl : k ≤ l
      · have : k = l := Nat.le_antisymm hkl hlk
        subst l
        simp
      · simp only [if_pos hlk, if_neg hkl]
    · have hkl : k ≤ l := Nat.le_of_lt (lt_of_not_ge hlk)
      simp only [if_neg hlk, if_pos hkl]
  rw [symmetric_double_sum (N t) f hsymm]
  have hdiag : (∑ k ∈ Finset.range (N t), f k k) =
      (H t : ℝ) * N t := by
    calc
      (∑ k ∈ Finset.range (N t), f k k) =
          ∑ k ∈ Finset.range (N t), (H t : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold f g
        simp only [le_refl, ↓reduceIte, Nat.sub_self, Nat.sub_zero]
        rw [Complex.mul_conj, normSq_u_pow]
        norm_num
      _ = (H t : ℝ) * N t := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [hdiag]
  have hlower :
      (∑ k ∈ Finset.range (N t), ∑ l ∈ Finset.range k, f k l) =
        ∑ r ∈ Finset.Ico 1 (H t), ((H t - r : ℕ) : ℝ) *
          ∑ q ∈ Finset.range (N t - r), g (q + r) q := by
    calc
      (∑ k ∈ Finset.range (N t), ∑ l ∈ Finset.range k, f k l) =
          ∑ k ∈ Finset.range (N t), ∑ l ∈ Finset.range k,
            ((H t - (k - l) : ℕ) : ℝ) * g k l := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        unfold f
        simp only [if_pos (Nat.le_of_lt (Finset.mem_range.mp hl))]
      _ = ∑ r ∈ Finset.Ico 1 (H t), ((H t - r : ℕ) : ℝ) *
          ∑ q ∈ Finset.range (N t - r), g (q + r) q :=
        triangular_gap_reindex (N t) (H t) g
  rw [hlower]
  simp only [g]
  simp_rw [Complex.re_sum]

/-- Independent finite van der Corput core. The theorem displays the cutoff,
the triangular energy, and the exact endpoint multiplier. -/
theorem finite_van_der_corput (t h : ℕ) :
    (H t : ℝ) ^ 2 * X h (N t) ≤
      ((N t + H t - 1 : ℕ) : ℝ) * triangularEnergy t h := by
  have hNpos : 0 < N t := by unfold N; positivity
  have hHpos : 0 < H t := by
    unfold H
    rw [Nat.ceil_pos]
    positivity
  have hsum := sum_movingWindow hNpos hHpos h
  let L := Finset.range (N t + H t - 1)
  let a : ℕ → ℝ := fun n => ‖movingWindow h (N t) (H t) n‖
  have hnorm : (H t : ℝ) * ‖T h (N t)‖ ≤ ∑ n ∈ L, a n := by
    calc
      (H t : ℝ) * ‖T h (N t)‖ = ‖(H t : ℂ) * T h (N t)‖ := by
        rw [norm_mul]
        norm_num
      _ = ‖∑ n ∈ L, movingWindow h (N t) (H t) n‖ := by
        rw [hsum]
      _ ≤ ∑ n ∈ L, ‖movingWindow h (N t) (H t) n‖ :=
        norm_sum_le _ _
      _ = ∑ n ∈ L, a n := rfl
  have hleft0 : 0 ≤ (H t : ℝ) * ‖T h (N t)‖ := by positivity
  have hnormSq := mul_self_le_mul_self hleft0 hnorm
  have hCS := sq_sum_le_card_mul_sum_sq (s := L) (f := a)
  have henergy : (∑ n ∈ L, a n ^ 2) = triangularEnergy t h := by
    change (∑ n ∈ Finset.range (N t + H t - 1),
      ‖movingWindow h (N t) (H t) n‖ ^ 2) = triangularEnergy t h
    simp_rw [← Complex.normSq_eq_norm_sq]
    exact sum_normSq_movingWindow_eq_triangularEnergy t h
  calc
    (H t : ℝ) ^ 2 * X h (N t) =
        ((H t : ℝ) * ‖T h (N t)‖) ^ 2 := by
      unfold X
      rw [Complex.normSq_eq_norm_sq]
      ring
    _ ≤ (∑ n ∈ L, a n) ^ 2 := by
      simpa [pow_two] using hnormSq
    _ ≤ (L.card : ℝ) * ∑ n ∈ L, a n ^ 2 := hCS
    _ = ((N t + H t - 1 : ℕ) : ℝ) * triangularEnergy t h := by
      rw [henergy]
      simp [L]

theorem five_le_N (t : ℕ) : 5 ≤ N t := by
  unfold N
  have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  omega

theorem sqrt_N_le_H (t : ℕ) :
    Real.sqrt (N t : ℝ) ≤ (H t : ℝ) := by
  exact Nat.le_ceil _

theorem H_lt_sqrt_N_add_one (t : ℕ) :
    (H t : ℝ) < Real.sqrt (N t : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

theorem H_pos (t : ℕ) : 0 < H t := by
  have hNnat : 0 < N t := lt_of_lt_of_le (by omega) (five_le_N t)
  have hN : (0 : ℝ) < N t := by exact_mod_cast hNnat
  have hsqrt : 0 < Real.sqrt (N t : ℝ) := Real.sqrt_pos.2 hN
  have hle := sqrt_N_le_H t
  exact_mod_cast (lt_of_lt_of_le hsqrt hle)

theorem endpointMultiplier_le (t : ℕ) :
    ((N t + H t - 1 : ℕ) : ℝ) ≤
      (3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ) := by
  have hN5 : (5 : ℝ) ≤ N t := by exact_mod_cast five_le_N t
  have hN0 : (0 : ℝ) ≤ N t := by positivity
  have hs0 : 0 ≤ Real.sqrt (N t : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) :=
    Real.sq_sqrt hN0
  have hsHalf : Real.sqrt (N t : ℝ) ≤ (N t : ℝ) / 2 := by
    nlinarith
  have hceil := H_lt_sqrt_N_add_one t
  have hHs := sqrt_N_le_H t
  have hN1 : 1 ≤ N t := le_trans (by omega) (five_le_N t)
  have hsub : 1 ≤ N t + H t := le_trans hN1 (Nat.le_add_right _ _)
  have hcast : (((N t + H t - 1 : ℕ) : ℝ)) =
      (N t : ℝ) + H t - 1 := by
    rw [Nat.cast_sub hsub]
    push_cast
    rfl
  rw [hcast]
  nlinarith [mul_le_mul_of_nonneg_right hHs hs0]

/-- The chosen ceiling cutoff gives the displayed one-frequency constant. -/
theorem X_sq_le_of_shiftedCorrelation
    {K : ℝ} (hK : 0 ≤ K) (t h : ℕ)
    (_hh : h ∈ Finset.Icc 1 10)
    (hcorr : triangularEnergy t h ≤ K * (H t : ℝ) * N t) :
    X h (N t) ^ 2 ≤ (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3 := by
  have hHpos : (0 : ℝ) < H t := by exact_mod_cast H_pos t
  have hN0 : (0 : ℝ) ≤ N t := by positivity
  have hs0 : 0 ≤ Real.sqrt (N t : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (N t : ℝ)) ^ 2 = (N t : ℝ) :=
    Real.sq_sqrt hN0
  have hE0 : 0 ≤ triangularEnergy t h := by
    have hv := finite_van_der_corput t h
    have hX : 0 ≤ X h (N t) := Complex.normSq_nonneg _
    have hmult : (0 : ℝ) < (N t + H t - 1 : ℕ) := by
      exact_mod_cast (show 0 < N t + H t - 1 by
        have := five_le_N t
        omega)
    nlinarith [sq_nonneg (H t : ℝ)]
  have hcoeff : (0 : ℝ) ≤ (N t + H t - 1 : ℕ) := by positivity
  have hvdc := finite_van_der_corput t h
  have hmult := endpointMultiplier_le t
  have hchain :
      (H t : ℝ) ^ 2 * X h (N t) ≤
        (3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ) *
          (K * (H t : ℝ) * N t) := by
    calc
      (H t : ℝ) ^ 2 * X h (N t) ≤
          ((N t + H t - 1 : ℕ) : ℝ) * triangularEnergy t h := hvdc
      _ ≤ ((N t + H t - 1 : ℕ) : ℝ) *
          (K * (H t : ℝ) * N t) := by gcongr
      _ ≤ ((3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ)) *
          (K * (H t : ℝ) * N t) := by
        gcongr
  have hXbound : X h (N t) ≤
      (3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ) := by
    have hscaled : (H t : ℝ) ^ 2 * X h (N t) ≤
        (H t : ℝ) ^ 2 *
          ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) := by
      calc
      (H t : ℝ) ^ 2 * X h (N t) ≤
          (3 / 2 : ℝ) * (H t : ℝ) * Real.sqrt (N t : ℝ) *
            (K * (H t : ℝ) * N t) := hchain
      _ = (H t : ℝ) ^ 2 *
          ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) := by ring
    exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hHpos)
  have hX0 : 0 ≤ X h (N t) := Complex.normSq_nonneg _
  have hright0 : 0 ≤
      (3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ) := by positivity
  have hsq := mul_self_le_mul_self hX0 hXbound
  calc
    X h (N t) ^ 2 ≤
        ((3 / 2 : ℝ) * K * (N t : ℝ) * Real.sqrt (N t : ℝ)) ^ 2 := by
      simpa [pow_two] using hsq
    _ = (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 2 *
        (Real.sqrt (N t : ℝ)) ^ 2 := by ring
    _ = (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3 := by rw [hs2]; ring

/-- Exact `N_t^3` fourth-moment consequence, with all ten frequencies and
The constant `45/2` visible in the theorem type. -/
theorem fourthMoment_le_of_shiftedCorrelation
    {K : ℝ} (hCorr : FixedPiShiftedCorrelation K) (t : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1) ^ 2) ≤
      (45 / 2 : ℝ) * K ^ 2 * (4 * 2 ^ t + 1 : ℕ) ^ 3 := by
  rcases hCorr with ⟨hK, hCorr⟩
  change (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (N t) ^ 2) ≤
    (45 / 2 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3
  calc
    (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (N t) ^ 2) ≤
        ∑ h ∈ Finset.Icc (1 : ℕ) 10,
          (9 / 4 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro h hh
      exact X_sq_le_of_shiftedCorrelation hK t h hh (hCorr t h hh)
    _ = (45 / 2 : ℝ) * K ^ 2 * (N t : ℝ) ^ 3 := by
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num
      ring

/-- T63's kernel-checked recombination rewritten with the complete summed
polynomial and literal width. -/
theorem selectedDefectContribution_eq_T63Polynomial (Q0 t : ℕ) :
    selectedDefectContribution Q0 t =
      ((∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1) ^ 2) -
        4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1)) +
        20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
        30 * (4 * 2 ^ t + 1 : ℕ)) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1) := by
  unfold selectedDefectContribution literalWidth N
  rw [complete_selected_defect_recombination Q0 t]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul]
  push_cast
  ring

/-- Conditional primitive-sector implication only. Every cutoff, shift,
frequency, triangular weight, constant, dyadic scale, T63 polynomial term,
width, and specialized T29 target remains literal in the hypotheses or
conclusion. -/
theorem fixedPi_shiftedCorrelation_implies_primitiveBudget
    {K : ℝ}
    (hK : 0 ≤ K)
    (hCorr : ∀ t h : ℕ, h ∈ Finset.Icc 1 10 →
      ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) +
        2 * ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
            (∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I *
                  (h * (10 ^ r - 1) * 10 ^ k : ℕ) *
                    (Real.pi : ℂ))).re) ≤
        K * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ))
    (Q0 t : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (2 : ℝ) * (
      (∑ p ∈ selectedRecordDomain t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1)) +
      (∑ p ∈ unmatchedDefect Q0 t,
        (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          Real.cos (2 * Real.pi ^ 2 * (h : ℝ) *
            (blockDifferenceValue p : ℝ))) /
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
      10 * ((225 / 8 : ℝ) * K ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s) ) := by
  have hFixed : FixedPiShiftedCorrelation K := by
    refine ⟨hK, ?_⟩
    intro j h hh
    specialize hCorr j h hh
    simpa only [triangularEnergy, shiftedSum, shiftedCharacter,
      shiftedFrequency, H, N] using hCorr
  have hF := fourthMoment_le_of_shiftedCorrelation hFixed t
  have hN5 : (5 : ℝ) ≤ (4 * 2 ^ t + 1 : ℕ) := by
    exact_mod_cast five_le_N t
  have hN0 : (0 : ℝ) ≤ (4 * 2 ^ t + 1 : ℕ) := by positivity
  have hS0 : 0 ≤
      ∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1) := by
    apply Finset.sum_nonneg
    intro h hh
    exact Complex.normSq_nonneg _
  let n : ℝ := (4 * 2 ^ t + 1 : ℕ)
  let w : ℝ := Real.sqrt (n ^ 2 - 1)
  let B : ℝ := (45 / 2 : ℝ) * K ^ 2
  let A : ℝ := (225 / 8 : ℝ) * K ^ 2 + 5
  let target : ℝ := n + n ^ 2 * (10 : ℝ) ^ (-s)
  have hn5 : (5 : ℝ) ≤ n := hN5
  have hn0 : 0 ≤ n := hN0
  have hB0 : 0 ≤ B := by unfold B; positivity
  have hA0 : 0 ≤ A := by unfold A; positivity
  have hrad : 0 ≤ n ^ 2 - 1 := by nlinarith
  have hw0 : 0 ≤ w := by unfold w; exact Real.sqrt_nonneg _
  have hwpos : 0 < w := by
    unfold w
    exact Real.sqrt_pos.2 (by nlinarith)
  have hwLower : (4 / 5 : ℝ) * n ≤ w := by
    have hnm1 : 0 ≤ n - 1 := by nlinarith
    have hnm1w : n - 1 ≤ w := by
      unfold w
      apply (Real.le_sqrt hnm1 hrad).2
      nlinarith
    nlinarith
  have hpow : (1 / 10 : ℝ) ≤ (10 : ℝ) ^ (-s) := by
    have hexp : (-1 : ℝ) ≤ -s := by linarith
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10) hexp
    rw [Real.rpow_neg_one] at hp
    norm_num at hp ⊢
    exact hp
  have htarget : n ^ 2 / 10 ≤ target := by
    unfold target
    have hsq0 : 0 ≤ n ^ 2 := sq_nonneg n
    calc
      n ^ 2 / 10 = n ^ 2 * (1 / 10 : ℝ) := by ring
      _ ≤ n ^ 2 * (10 : ℝ) ^ (-s) := by gcongr
      _ ≤ n + n ^ 2 * (10 : ℝ) ^ (-s) := by linarith
  have hpoly :
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          X h (4 * 2 ^ t + 1) ^ 2) -
          4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
            (∑ h ∈ Finset.Icc (1 : ℕ) 10,
              X h (4 * 2 ^ t + 1)) +
          20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
          30 * (4 * 2 ^ t + 1 : ℕ) ≤
        (B + 4) * n ^ 3 := by
    have hF' : (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) ≤ B * n ^ 3 := by
      simpa only [B, n] using hF
    change (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) -
        4 * (n - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1)) +
        20 * n ^ 2 - 30 * n ≤ (B + 4) * n ^ 3
    have hcoef : (0 : ℝ) ≤ 4 * (n - 1) := by nlinarith
    nlinarith [mul_nonneg hcoef hS0]
  change selectedDefectContribution Q0 t ≤
    10 * ((225 / 8 : ℝ) * K ^ 2 + 5) *
      ((4 * 2 ^ t + 1 : ℕ) +
        (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s))
  rw [selectedDefectContribution_eq_T63Polynomial Q0 t]
  apply (div_le_iff₀ hwpos).2
  calc
    (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        X h (4 * 2 ^ t + 1) ^ 2) -
        4 * ((4 * 2 ^ t + 1 : ℕ) - 1) *
          (∑ h ∈ Finset.Icc (1 : ℕ) 10, X h (4 * 2 ^ t + 1)) +
        20 * (4 * 2 ^ t + 1 : ℕ) ^ 2 -
        30 * (4 * 2 ^ t + 1 : ℕ) ≤ (B + 4) * n ^ 3 := hpoly
    _ = 10 * A * (n ^ 2 / 10) * ((4 / 5 : ℝ) * n) := by
      unfold A B
      ring
    _ ≤ 10 * A * target * w := by gcongr
    _ = (10 * ((225 / 8 : ℝ) * K ^ 2 + 5) *
        ((4 * 2 ^ t + 1 : ℕ) +
          (4 * 2 ^ t + 1 : ℕ) ^ 2 * (10 : ℝ) ^ (-s))) *
          Real.sqrt (((4 * 2 ^ t + 1 : ℕ) : ℝ) ^ 2 - 1) := by
      rfl

end Theory.PiDigits.LongLagBlockCollisionDecay.T66

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.shiftedCharacter_eq_orbitCorrelation
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.sum_movingWindow
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.normSq_finset_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.triangular_gap_reindex
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.movingWindow_pair_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.symmetric_double_sum
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.sum_normSq_movingWindow_eq_triangularEnergy
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.finite_van_der_corput
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.endpointMultiplier_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.X_sq_le_of_shiftedCorrelation
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.fourthMoment_le_of_shiftedCorrelation
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.selectedDefectContribution_eq_T63Polynomial
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T66.fixedPi_shiftedCorrelation_implies_primitiveBudget
