import Mathlib

/-!
# T226: continued-fraction cylinder perturbation

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t226; each task compiled and
axiom-checked; assembled by Claude Opus 5

All six tasks share one byte-identical starter; task `-06` embedded tasks
`-02`..`-05` verbatim, so each lemma appears once here.
-/

noncomputable section

namespace Theory.PiDigits.T226ContinuedFractionCylinderDistance

def BAκ (κ x : ℝ) : Prop :=
  0 < κ ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    κ / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / (q : ℝ)|

def rationalPoint (p : ℤ) (q : ℕ) : ℝ :=
  (p : ℝ) / (q : ℝ)

def secondaryEndpoint
    (pPrev p : ℤ) (qPrev q : ℕ) : ℝ :=
  rationalPoint (pPrev + p) (qPrev + q)

def cfCylinder
    (pPrev p : ℤ) (qPrev q : ℕ) : Set ℝ :=
  Set.Ioo
    (min (rationalPoint p q)
      (secondaryEndpoint pPrev p qPrev q))
    (max (rationalPoint p q)
      (secondaryEndpoint pPrev p qPrev q))

def cfCylinderMargin
    (x : ℝ) (pPrev p : ℤ) (qPrev q : ℕ) : ℝ :=
  min
    |x - rationalPoint p q|
    |x - secondaryEndpoint pPrev p qPrev q|

def CFCylinderData
    (κ x : ℝ) (pPrev p : ℤ) (qPrev q : ℕ) : Prop :=
  BAκ κ x ∧
  0 < qPrev ∧ 0 < q ∧ qPrev ≤ q ∧
  Int.natAbs (p * (qPrev : ℤ) - pPrev * (q : ℤ)) = 1 ∧
  x ∈ cfCylinder pPrev p qPrev q

def CFPrefixCodingInput
    (SameCFPrefix : ℕ → ℝ → ℝ → Prop)
    (IsDepthCylinder :
      ℕ → ℝ → ℤ → ℤ → ℕ → ℕ → Prop) : Prop :=
  ∀ {n : ℕ} {x y : ℝ} {pPrev p : ℤ} {qPrev q : ℕ},
    IsDepthCylinder n x pPrev p qPrev q →
    Irrational y →
    y ∈ cfCylinder pPrev p qPrev q →
    SameCFPrefix n x y

/-! ### Secondary denominator

Task `pi-t226-cf-cylinder-01-secondary-denominator-le-two-mul`. -/

lemma secondary_denominator_le_two_mul
    {qPrev q : ℕ} (hprev : qPrev ≤ q) :
    qPrev + q ≤ 2 * q := by
  omega

/-! ### Endpoint distances, margin, and the conditional prefix transfer

Tasks `pi-t226-cf-cylinder-02-primary-endpoint-distance`,
`-03-secondary-endpoint-distance`, `-04-cf-cylinder-margin-lower`,
`-05-perturbation-preserves-cf-cylinder` and
`-06-perturbation-preserves-cf-prefix`.  The continued-fraction coding
implication `CFPrefixCodingInput` stays an explicit hypothesis. -/

lemma primary_endpoint_distance
    {κ x : ℝ} {pPrev p : ℤ} {qPrev q : ℕ}
    (h : CFCylinderData κ x pPrev p qPrev q) :
    κ / (q : ℝ) ^ 2 ≤ |x - rationalPoint p q| := by
  obtain ⟨hBA, _, hq, _, _, _⟩ := h
  exact hBA.2 p q hq

lemma secondary_endpoint_distance
    {κ x : ℝ} {pPrev p : ℤ} {qPrev q : ℕ}
    (h : CFCylinderData κ x pPrev p qPrev q) :
    κ / (4 * (q : ℝ) ^ 2) ≤
      |x - secondaryEndpoint pPrev p qPrev q| := by
  obtain ⟨hBA, hqPrev, hq, hle, _, _⟩ := h
  have hsum : 0 < qPrev + q := by omega
  have hkey : κ / ((qPrev + q : ℕ) : ℝ) ^ 2 ≤
      |x - secondaryEndpoint pPrev p qPrev q| :=
    hBA.2 (pPrev + p) (qPrev + q) hsum
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsumR : (0 : ℝ) < ((qPrev + q : ℕ) : ℝ) := by exact_mod_cast hsum
  have hbound : ((qPrev + q : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    have : (qPrev + q : ℕ) ≤ 2 * q := by omega
    exact_mod_cast this
  have hmono : κ / (4 * (q : ℝ) ^ 2) ≤ κ / ((qPrev + q : ℕ) : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left hBA.1.le (by positivity)
    nlinarith [hsumR, hqR]
  linarith

lemma cfCylinderMargin_lower
    {κ x : ℝ} {pPrev p : ℤ} {qPrev q : ℕ}
    (h : CFCylinderData κ x pPrev p qPrev q) :
    κ / (4 * (q : ℝ) ^ 2) ≤
      cfCylinderMargin x pPrev p qPrev q := by
  have hq : 0 < q := h.2.2.1
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hκ : 0 < κ := h.1.1
  have h1 : κ / (q : ℝ) ^ 2 ≤ |x - rationalPoint p q| :=
    primary_endpoint_distance h
  have h2 : κ / (4 * (q : ℝ) ^ 2) ≤
      |x - secondaryEndpoint pPrev p qPrev q| :=
    secondary_endpoint_distance h
  have h1' : κ / (4 * (q : ℝ) ^ 2) ≤ κ / (q : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left hκ.le (by positivity)
    nlinarith
  rw [cfCylinderMargin, le_min_iff]
  exact ⟨le_trans h1' h1, h2⟩

lemma perturbation_preserves_cfCylinder
    {κ x y δ : ℝ} {pPrev p : ℤ} {qPrev q : ℕ}
    (h : CFCylinderData κ x pPrev p qPrev q)
    (hδ : 0 < δ) (hxy : |x - y| ≤ δ)
    (hsmall : δ < κ / (4 * (q : ℝ) ^ 2)) :
    y ∈ cfCylinder pPrev p qPrev q := by
  have hmargin : κ / (4 * (q : ℝ) ^ 2) ≤
      cfCylinderMargin x pPrev p qPrev q := cfCylinderMargin_lower h
  have hxmem : x ∈ cfCylinder pPrev p qPrev q := h.2.2.2.2.2
  rw [cfCylinder, Set.mem_Ioo] at hxmem
  set a : ℝ := rationalPoint p q with ha
  set b : ℝ := secondaryEndpoint pPrev p qPrev q with hb
  have hda : δ < |x - a| := by
    have : cfCylinderMargin x pPrev p qPrev q ≤ |x - a| := min_le_left _ _
    linarith
  have hdb : δ < |x - b| := by
    have : cfCylinderMargin x pPrev p qPrev q ≤ |x - b| := min_le_right _ _
    linarith
  have hdmin : δ < |x - min a b| := by
    rcases min_choice a b with hc | hc <;> rw [hc] <;> assumption
  have hdmax : δ < |x - max a b| := by
    rcases max_choice a b with hc | hc <;> rw [hc] <;> assumption
  have h1 : δ < x - min a b := by
    rw [abs_of_pos (by linarith [hxmem.1] : (0:ℝ) < x - min a b)] at hdmin
    exact hdmin
  have h2 : δ < max a b - x := by
    have hneg : x - max a b < 0 := by linarith [hxmem.2]
    rw [abs_of_neg hneg] at hdmax
    linarith
  have hyx : |x - y| ≤ δ := hxy
  rw [abs_le] at hyx
  rw [cfCylinder, Set.mem_Ioo]
  constructor
  · linarith [hyx.1, hyx.2]
  · linarith [hyx.1, hyx.2]

theorem perturbation_preserves_cfPrefix
    {SameCFPrefix : ℕ → ℝ → ℝ → Prop}
    {IsDepthCylinder :
      ℕ → ℝ → ℤ → ℤ → ℕ → ℕ → Prop}
    (hCoding : CFPrefixCodingInput SameCFPrefix IsDepthCylinder)
    {n : ℕ} {κ x y δ : ℝ}
    {pPrev p : ℤ} {qPrev q : ℕ}
    (hdepth : IsDepthCylinder n x pPrev p qPrev q)
    (hdata : CFCylinderData κ x pPrev p qPrev q)
    (hy : Irrational y)
    (hδ : 0 < δ) (hxy : |x - y| ≤ δ)
    (hsmall : δ < κ / (4 * (q : ℝ) ^ 2)) :
    SameCFPrefix n x y :=
  hCoding hdepth hy
    (perturbation_preserves_cfCylinder hdata hδ hxy hsmall)

end Theory.PiDigits.T226ContinuedFractionCylinderDistance
