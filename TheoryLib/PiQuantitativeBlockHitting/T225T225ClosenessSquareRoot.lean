import Mathlib

/-!
# T225: elementary square-root perturbation

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t225; each task compiled and
axiom-checked; assembled by Claude Opus 5

All five tasks share one byte-identical starter; tasks `-03` and `-05`
embedded the earlier lemmas verbatim, so each lemma appears once here.
-/

noncomputable section

namespace Theory.PiDigits.T225ClosenessSquareRoot

def BAκ (κ x : ℝ) : Prop :=
  0 < κ ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)|

def decimalCylinder (N A : ℕ) : Set ℝ :=
  Set.Ico
    ((A : ℝ) / (10 : ℝ) ^ N)
    (((A + 1 : ℕ) : ℝ) / (10 : ℝ) ^ N)

def SameDecimalCylinder (N : ℕ) (x y : ℝ) : Prop :=
  ∃ A : ℕ, A < 10 ^ N ∧
    x ∈ decimalCylinder N A ∧ y ∈ decimalCylinder N A

/-! ### Perturbation and cutoff

Tasks `pi-t225-closeness-01-perturbation-lower-bound`,
`-02-square-root-cutoff-implies-half-error` and
`-03-closeness-square-root-guarantee`. -/

lemma perturbation_lower_bound
    {κ x y δ : ℝ} {p : ℤ} {q : ℕ}
    (hBA : BAκ κ x) (hq : 0 < q)
    (hxy : |x - y| ≤ δ) :
    κ / (q : ℝ) ^ 2 - δ ≤
      |y - (p : ℝ) / (q : ℝ)| := by
  have hx : κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)| := hBA.2 p q hq
  have htri : |x - (p : ℝ) / (q : ℝ)| ≤ |x - y| + |y - (p : ℝ) / (q : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (x - (p : ℝ) / (q : ℝ)) (y - (p : ℝ) / (q : ℝ))
    have h2 : |(x - (p : ℝ) / (q : ℝ)) - (y - (p : ℝ) / (q : ℝ))| = |x - y| := by
      ring_nf
    linarith [abs_sub_abs_le_abs_sub (x - (p : ℝ) / (q : ℝ)) (y - (p : ℝ) / (q : ℝ)), h2]
  linarith

lemma squareRoot_cutoff_implies_half_error
    {κ δ : ℝ} {q : ℕ}
    (hκ : 0 < κ) (hδ : 0 < δ) (hq : 0 < q)
    (hcut : (q : ℝ) ≤ Real.sqrt (κ / (2 * δ))) :
    δ ≤ κ / (2 * (q : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have harg : (0 : ℝ) ≤ κ / (2 * δ) := by positivity
  have hsq : (q : ℝ) ^ 2 ≤ κ / (2 * δ) := by
    have h : (q : ℝ) ^ 2 ≤ (Real.sqrt (κ / (2 * δ))) ^ 2 := by nlinarith [hqR.le, hcut]
    rwa [Real.sq_sqrt harg] at h
  have h2 : (q : ℝ) ^ 2 * (2 * δ) ≤ κ := by
    calc (q : ℝ) ^ 2 * (2 * δ) ≤ (κ / (2 * δ)) * (2 * δ) := by
          apply mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = κ := by field_simp
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (q : ℝ) ^ 2)]
  nlinarith [h2]

theorem closeness_squareRoot_guarantee
    {κ x y δ : ℝ} {p : ℤ} {q : ℕ}
    (hBA : BAκ κ x) (hδ : 0 < δ)
    (hxy : |x - y| ≤ δ) (hq : 0 < q)
    (hcut : (q : ℝ) ≤ Real.sqrt (κ / (2 * δ))) :
    κ / (2 * (q : ℝ) ^ 2) ≤
      |y - (p : ℝ) / (q : ℝ)| := by
  have h1 : κ / (q : ℝ) ^ 2 - δ ≤ |y - (p : ℝ) / (q : ℝ)| :=
    perturbation_lower_bound hBA hq hxy
  have h2 : δ ≤ κ / (2 * (q : ℝ) ^ 2) :=
    squareRoot_cutoff_implies_half_error hBA.1 hδ hq hcut
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hhalf : κ / (q : ℝ) ^ 2 - κ / (2 * (q : ℝ) ^ 2) = κ / (2 * (q : ℝ) ^ 2) := by
    field_simp
    ring
  linarith

/-! ### Decimal-prefix specialization

Tasks `pi-t225-closeness-04-same-decimal-cylinder-distance` and
`-05-decimal-prefix-square-root-guarantee`. -/

lemma sameDecimalCylinder_distance
    {N : ℕ} {x y : ℝ}
    (h : SameDecimalCylinder N x y) :
    |x - y| < 1 / (10 : ℝ) ^ N := by
  obtain ⟨A, _hA, hx, hy⟩ := h
  simp only [decimalCylinder, Set.mem_Ico, Nat.cast_add, Nat.cast_one] at hx hy
  have hpow : (0 : ℝ) < (10 : ℝ) ^ N := by positivity
  have hsplit : ((A : ℝ) + 1) / (10 : ℝ) ^ N = (A : ℝ) / (10 : ℝ) ^ N + 1 / (10 : ℝ) ^ N := by
    field_simp
  rw [abs_sub_lt_iff]
  constructor <;> [linarith [hx.1, hx.2, hy.1, hy.2]; linarith [hx.1, hx.2, hy.1, hy.2]]

theorem decimalPrefix_squareRoot_guarantee
    {κ x y : ℝ} {N : ℕ} {p : ℤ} {q : ℕ}
    (hBA : BAκ κ x)
    (hprefix : SameDecimalCylinder N x y)
    (hq : 0 < q)
    (hcut :
      (q : ℝ) ≤ Real.sqrt (κ * (10 : ℝ) ^ N / 2)) :
    κ / (2 * (q : ℝ) ^ 2) ≤
      |y - (p : ℝ) / (q : ℝ)| := by
  have hpow : (0 : ℝ) < (10 : ℝ) ^ N := by positivity
  set δ : ℝ := 1 / (10 : ℝ) ^ N with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hxy : |x - y| ≤ δ := le_of_lt (sameDecimalCylinder_distance hprefix)
  have harg : κ / (2 * δ) = κ * (10 : ℝ) ^ N / 2 := by
    rw [hδdef]; field_simp
  have hcut' : (q : ℝ) ≤ Real.sqrt (κ / (2 * δ)) := by rw [harg]; exact hcut
  have h1 : κ / (q : ℝ) ^ 2 - δ ≤ |y - (p : ℝ) / (q : ℝ)| :=
    perturbation_lower_bound hBA hq hxy
  have h2 : δ ≤ κ / (2 * (q : ℝ) ^ 2) :=
    squareRoot_cutoff_implies_half_error hBA.1 hδ hq hcut'
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hhalf : κ / (q : ℝ) ^ 2 - κ / (2 * (q : ℝ) ^ 2) = κ / (2 * (q : ℝ) ^ 2) := by
    field_simp
    ring
  linarith

end Theory.PiDigits.T225ClosenessSquareRoot
