import TheoryLib.PiQuantitativeBlockHitting.T114T114SampledBBPGCDNormalizedSuccessor
import TheoryLib.PiQuantitativeBlockHitting.T115T115SampledBBPCellDefectPhase

/-!
# T116: prime support of the exact sampled-BBP normalization gcd

For arbitrary reduced integer/natural pairs `(A,D)` and `(C,E)`, this file
restricts the prime support of the cross-normalization gcd attached to
`U = 10*A*E + C*D` and `V = D*E`.  Its specialization uses the actual reduced
rational pairs from the synchronized sampled-BBP orbit.

This is only a support lemma.  It proves no gcd-size or valuation bound and no
cancellation, occupancy, density, or V1 conclusion.
-/

namespace Theory.PiDigits.T116SampledBBPGCDPrimeSupport

private theorem not_dvd_of_coprime {p : ℕ} (hp : p.Prime) {x y : ℕ}
    (hc : Nat.Coprime x y) (hx : p ∣ x) (hy : p ∣ y) : False := by
  have h := Nat.dvd_gcd hx hy
  rw [hc] at h
  exact hp.not_dvd_one h

private theorem prime_dvd_tri_natAbs {p : ℕ} (hp : p.Prime) (a b c : ℤ)
    (h : (p : ℤ) ∣ a * b * c) :
    p ∣ a.natAbs ∨ p ∣ b.natAbs ∨ p ∣ c.natAbs := by
  have hn : p ∣ a.natAbs * (b.natAbs * c.natAbs) := by
    have hx : p ∣ (a * b * c).natAbs := Int.natAbs_dvd_natAbs.mpr h
    rwa [Int.natAbs_mul, Int.natAbs_mul, mul_assoc] at hx
  rcases hp.dvd_mul.mp hn with h1 | h23
  · exact Or.inl h1
  · rcases hp.dvd_mul.mp h23 with h2 | h3
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)

/-- A prime dividing the cross-normalization gcd of two reduced pairs must
divide the first denominator, and either the second denominator or base ten.
The generic natural denominators may be zero; positivity is used only in the
actual rational specialization through the `Rat` structure. -/
theorem prime_dvd_crossNormalizationGCD_support :
    ∀ (p : ℕ), p.Prime → ∀ (A C : ℤ) (D E : ℕ), Nat.Coprime A.natAbs D →
      Nat.Coprime C.natAbs E →
      p ∣ Int.gcd (10 * A * (E : ℤ) + C * (D : ℤ)) ((D * E : ℕ) : ℤ) →
      p ∣ D ∧ (p ∣ E ∨ p ∣ 10) := by
  intro p hp A C D E hAC hCE hg
  have hgZ : (p : ℤ) ∣
      ((Int.gcd (10 * A * (E : ℤ) + C * (D : ℤ)) ((D * E : ℕ) : ℤ) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hg
  have hUz : (p : ℤ) ∣ 10 * A * (E : ℤ) + C * (D : ℤ) :=
    hgZ.trans (Int.gcd_dvd_left _ _)
  have hDE : p ∣ D * E :=
    Int.natCast_dvd_natCast.mp (hgZ.trans (Int.gcd_dvd_right _ _))
  rcases hp.dvd_mul.mp hDE with hD | hE
  · refine ⟨hD, ?_⟩
    have hnotA : ¬ (p ∣ A.natAbs) := fun hA =>
      not_dvd_of_coprime hp hAC hA hD
    have hCD : (p : ℤ) ∣ C * (D : ℤ) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hD) _
    have h10AE : (p : ℤ) ∣ 10 * A * (E : ℤ) := by
      have h := dvd_sub hUz hCD
      convert h using 1
      ring
    rcases prime_dvd_tri_natAbs hp 10 A (E : ℤ) h10AE with h1 | h2 | h3
    · exact Or.inr (by simpa using h1)
    · exact absurd h2 hnotA
    · exact Or.inl (by simpa using h3)
  · refine ⟨?_, Or.inl hE⟩
    have hnotC : ¬ (p ∣ C.natAbs) := fun hC =>
      not_dvd_of_coprime hp hCE hC hE
    have h10AE : (p : ℤ) ∣ 10 * A * (E : ℤ) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hE) _
    have hCD : (p : ℤ) ∣ C * (D : ℤ) := by
      have h := dvd_sub hUz h10AE
      convert h using 1
      ring
    have hCDnat : p ∣ C.natAbs * D := by
      have hx : p ∣ (C * (D : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr hCD
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at hx
    rcases hp.dvd_mul.mp hCDnat with h1 | h2
    · exact absurd h1 hnotC
    · exact h2

/-- Specialization to the actual reduced sampled-BBP value and forcing pairs. -/
theorem prime_dvd_sampledBBPNormalizationGCD_support :
    ∀ (N p : ℕ), p.Prime →
      (let Q : ℚ := (10 : ℚ) ^ N *
        Theory.PiDigits.T77SelectedPadicDefectShell.bbpPartial (7 * N);
       let F : ℚ := Theory.PiDigits.T106BBPForcedOrbit.sampledBBPForcingRat N;
       let U : ℤ := 10 * Q.num * (F.den : ℤ) + F.num * (Q.den : ℤ);
       let V : ℕ := Q.den * F.den;
       p ∣ Int.gcd U (V : ℤ) → p ∣ Q.den ∧ (p ∣ F.den ∨ p ∣ 10)) := by
  intro N p hp Q F U V hg
  exact prime_dvd_crossNormalizationGCD_support p hp Q.num F.num Q.den F.den
    Q.reduced F.reduced hg

end Theory.PiDigits.T116SampledBBPGCDPrimeSupport
