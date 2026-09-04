import TheoryLib.PiQuantitativeBlockHitting.T221T221FourierComposition
import Mathlib

/-!
# T222: primitive ray criterion

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t222; each task compiled and
axiom-checked; assembled by Claude Opus 5

Tasks 02 and 03 of the pack are not included: they were not proved.
-/

noncomputable section

namespace Theory.PiDigits.T222PrimitiveRayCriterion

open Filter MeasureTheory Topology
open scoped BigOperators

noncomputable def trigPolynomial
    (S : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ S,
    a m * Complex.exp ((2 * Real.pi * m * x : ℝ) * Complex.I)

def CoefficientSupported (S : Finset ℤ) (a : ℤ → ℂ) : Prop :=
  ∀ m, m ∉ S → a m = 0

def Primitive (b : ℕ) (h : ℤ) : Prop :=
  h ≠ 0 ∧ ¬ (b : ℤ) ∣ h

noncomputable def raySupport
    (b : ℕ) (S : Finset ℤ) (h : ℤ) : Finset ℤ := by
  classical
  exact S.filter fun m => ∃ k : ℕ, m = (b : ℤ) ^ k * h

noncomputable def RaySum
    (b : ℕ) (S : Finset ℤ) (a : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑ m ∈ raySupport b S h, a m

def L1Coboundary (b : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, IntegrableOn g (Set.Ico 0 1) ∧
    ∀ᵐ x ∂Measure.restrict volume (Set.Ico 0 1),
      f x = g x -
        g (Theory.PiDigits.T221FourierComposition.Tb b ((b : ℝ) * x))

def PolynomialCoboundary
    (b : ℕ) (S : Finset ℤ) (a : ℤ → ℂ) : Prop :=
  ∃ (G : Finset ℤ) (c : ℤ → ℂ),
    CoefficientSupported G c ∧
      ∀ x : ℝ,
        trigPolynomial S a x = trigPolynomial G c x -
          trigPolynomial G c
            (Theory.PiDigits.T221FourierComposition.Tb b ((b : ℝ) * x))

def FourierCompositionInput (b : ℕ) : Prop :=
  ∀ {g : ℝ → ℂ} {m : ℤ}, IntegrableOn g (Set.Ico 0 1) →
    Theory.PiDigits.T221FourierComposition.coeff
        (fun x => g (Theory.PiDigits.T221FourierComposition.Tb b
          ((b : ℝ) * x))) m =
      if (b : ℤ) ∣ m then
        Theory.PiDigits.T221FourierComposition.coeff g (m / (b : ℤ))
      else 0

def RiemannLebesgueInput (b : ℕ) : Prop :=
  ∀ g : ℝ → ℂ, IntegrableOn g (Set.Ico 0 1) →
    ∀ h : ℤ, Primitive b h →
      Tendsto (fun k : ℕ =>
        Theory.PiDigits.T221FourierComposition.coeff g
          ((b : ℤ) ^ k * h)) atTop (𝓝 0)

lemma exists_ray_decomp {b : ℕ} (hb : 2 ≤ b) :
    ∀ (n : ℕ) (m : ℤ), m.natAbs = n → m ≠ 0 →
      ∃ p : ℕ × ℤ, Primitive b p.2 ∧ m = (b : ℤ) ^ p.1 * p.2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hn hm0
    by_cases hd : (b : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hd
      have hm'0 : m' ≠ 0 := by
        rintro rfl
        exact hm0 (by ring)
      have h1 : 0 < m'.natAbs := Int.natAbs_pos.mpr hm'0
      have h2 : ((b : ℤ) * m').natAbs = b * m'.natAbs := by
        simp [Int.natAbs_mul]
      have hlt : m'.natAbs < n := by
        rw [← hn, h2]
        nlinarith [h1]
      obtain ⟨p, hprim, heq⟩ := ih m'.natAbs hlt m' rfl hm'0
      exact ⟨(p.1 + 1, p.2), hprim, by rw [heq]; ring⟩
    · exact ⟨(0, m), ⟨hm0, hd⟩, by ring⟩

lemma ray_pow_eq {b : ℕ} (hb : 2 ≤ b) {k1 k2 : ℕ} {h1 h2 : ℤ}
    (hp1 : Primitive b h1) (hle : k1 ≤ k2)
    (heq : (b : ℤ) ^ k1 * h1 = (b : ℤ) ^ k2 * h2) : k1 = k2 := by
  by_contra hne
  have hlt : k1 < k2 := lt_of_le_of_ne hle hne
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hpow : ((b : ℤ) ^ k1) ≠ 0 := pow_ne_zero _ hb0
  have hsplit : h1 = (b : ℤ) ^ (k2 - k1) * h2 := by
    refine mul_left_cancel₀ hpow ?_
    rw [heq, ← mul_assoc, ← pow_add]
    congr 2
    omega
  refine hp1.2 ?_
  obtain ⟨t, ht⟩ : ∃ t : ℕ, k2 - k1 = t + 1 := ⟨k2 - k1 - 1, by omega⟩
  refine ⟨(b : ℤ) ^ t * h2, ?_⟩
  rw [hsplit, ht]
  ring

lemma ray_decomp_unique {b : ℕ} (hb : 2 ≤ b) {k1 k2 : ℕ} {h1 h2 : ℤ}
    (hp1 : Primitive b h1) (hp2 : Primitive b h2)
    (heq : (b : ℤ) ^ k1 * h1 = (b : ℤ) ^ k2 * h2) : k1 = k2 ∧ h1 = h2 := by
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hk : k1 = k2 := by
    rcases le_total k1 k2 with hle | hle
    · exact ray_pow_eq hb hp1 hle heq
    · exact (ray_pow_eq hb hp2 hle heq.symm).symm
  subst hk
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero _ hb0) heq⟩

lemma finiteSupport_rayDecomposition
    {b : ℕ} (hb : 2 ≤ b) (S : Finset ℤ) :
    ∀ m ∈ S, m ≠ 0 →
      ∃! p : ℕ × ℤ,
        Primitive b p.2 ∧ m = (b : ℤ) ^ p.1 * p.2 := by
  have _S : Finset ℤ := S
  intro m _hmS hm0
  obtain ⟨p, hp, hpe⟩ := exists_ray_decomp hb m.natAbs m rfl hm0
  refine ⟨p, ⟨hp, hpe⟩, ?_⟩
  rintro ⟨k, h⟩ ⟨hq, hqe⟩
  have heq : (b : ℤ) ^ k * h = (b : ℤ) ^ p.1 * p.2 := by
    rw [← hqe, ← hpe]
  obtain ⟨hk, hh⟩ := ray_decomp_unique hb hq hp heq
  simp only [Prod.ext_iff]
  exact ⟨hk, hh⟩

end Theory.PiDigits.T222PrimitiveRayCriterion
