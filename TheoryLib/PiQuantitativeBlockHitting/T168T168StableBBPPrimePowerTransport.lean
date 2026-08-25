import TheoryLib.PiQuantitativeBlockHitting.T158T158ExactBBPFiveAdicPulses

/-!
# T168: stable BBP prime-power transport

The literal seven new BBP rows have an explicit odd denominator support.
Away from that support and from the decimal primes, an old prime-primary
denominator component of the actual reduced sampled BBP rational persists
unchanged.  Its pole-removed rational coordinate evolves by multiplication
by ten modulo the full old prime power.

The transport conclusion is equality-aware because `padicValRat` assigns a
finite value to zero.  No distribution, cancellation, or V1 consequence is
asserted.
-/

noncomputable section

open scoped BigOperators

namespace Theory.PiDigits.T168StableBBPPrimePowerTransport

open Finset
open Theory.PiDigits.MachinPrimeSurvival
open Theory.PiDigits.T77SelectedPadicDefectShell
open Theory.PiDigits.T98BBPArchimedeanTerm
open Theory.PiDigits.T106BBPForcedOrbit
open Theory.PiDigits.T115SampledBBPCellDefectPhase
open Theory.PiDigits.T157ExactBBPFiveAdicShell
open Theory.PiDigits.T158ExactBBPFiveAdicPulses

/-- Odd denominator of one collapsed four-pole BBP row. -/
def bbpRowOddDenominator (j : ℕ) : ℕ :=
  (2 * j + 1) * (4 * j + 3) * (8 * j + 1) * (8 * j + 5)

/-- Product of the seven odd row denominators introduced between sampled
depths `m` and `m+1`. -/
def sampledBBPInnovationOddSupport (m : ℕ) : ℕ :=
  ∏ j ∈ range 7, bbpRowOddDenominator (7 * m + j + 1)

private lemma rowOddDenominator_dvd_innovationSupport
    (m j : ℕ) (hj : j < 7) :
    bbpRowOddDenominator (7 * m + j + 1) ∣
      sampledBBPInnovationOddSupport m := by
  unfold sampledBBPInnovationOddSupport
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)

private lemma padicValRat_bbpCombinedTerm_nonneg_of_not_dvd_row
    (p j : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10)
    (hrow : ¬p ∣ bbpRowOddDenominator j) :
    0 ≤ padicValRat p (bbpCombinedTerm j) := by
  letI : Fact p.Prime := ⟨hp⟩
  let A : ℕ := 120 * j ^ 2 + 151 * j + 47
  let O : ℕ := bbpRowOddDenominator j
  have hAnat : A ≠ 0 := by
    dsimp [A]
    omega
  have hA : (A : ℚ) ≠ 0 := by exact_mod_cast hAnat
  have hOnat : O ≠ 0 := by
    dsimp [O, bbpRowOddDenominator]
    positivity
  have hO : (O : ℚ) ≠ 0 := by exact_mod_cast hOnat
  have h16nat : ¬p ∣ 16 := by
    intro hp16
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 4) (by simpa using hp16)
    exact hp10 (dvd_trans hp2 (by norm_num : 2 ∣ 10))
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have hvalO : padicValRat p (O : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hrow
  have hval16 : padicValRat p (16 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd h16nat
  have hvalA : padicValRat p (A : ℚ) = (padicValNat p A : ℤ) :=
    padicValRat.of_nat
  have heq : bbpCombinedTerm j = (A : ℚ) / ((O : ℚ) * 16 ^ j) := by
    rw [bbpCombinedTerm_eq]
    dsimp [A, O, bbpRowOddDenominator]
    push_cast
    rfl
  rw [heq, padicValRat.div hA (mul_ne_zero hO (pow_ne_zero _ h16)),
    padicValRat.mul hO (pow_ne_zero _ h16), hvalO,
    padicValRat.pow h16, hval16, hvalA]
  simp

/-- The literal seven-row forcing is `p`-integral at every prime outside its
exact odd innovation-denominator support and the decimal primes. -/
theorem sampledBBPForcingRat_padicVal_nonneg_of_not_dvd_innovationSupport
    (m p : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10)
    (hsupport : ¬p ∣ sampledBBPInnovationOddSupport m) :
    0 ≤ padicValRat p (sampledBBPForcingRat m) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsum0 :
      (∑ j ∈ range 7, bbpCombinedTerm (7 * m + j + 1)) ≠ 0 := by
    exact ne_of_gt (Finset.sum_pos
      (fun j _ ↦ bbpCombinedTerm_pos (7 * m + j + 1))
      ⟨0, Finset.mem_range.mpr (by omega)⟩)
  have hsum : 0 ≤ padicValRat p
      (∑ j ∈ range 7, bbpCombinedTerm (7 * m + j + 1)) := by
    apply padicValRat_sum_nonneg hp _ _
    · intro j hj
      apply padicValRat_bbpCombinedTerm_nonneg_of_not_dvd_row p _ hp hp10
      intro hrow
      exact hsupport (dvd_trans hrow
        (rowOddDenominator_dvd_innovationSupport m j (mem_range.mp hj)))
    · exact hsum0
  rw [sampledBBPForcingRat_eq_sevenTerms,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hsum0,
    padicValRat.pow (by norm_num)]
  have hten : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp10
  rw [hten]
  simpa using hsum

/-- One literal innovation step preserves the exact negative `p`-valuation
of the actual reduced sampled BBP rational. -/
theorem scaledBBPRat_padicVal_persists_one_step
    (m p e : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10) (he : 0 < e)
    (hsupport : ¬p ∣ sampledBBPInnovationOddSupport m)
    (hval : padicValRat p (scaledBBPRat m) = -(e : ℤ)) :
    padicValRat p (scaledBBPRat (m + 1)) = -(e : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hforcing :=
    sampledBBPForcingRat_padicVal_nonneg_of_not_dvd_innovationSupport
      m p hp hp10 hsupport
  have hten : padicValRat p (10 : ℚ) = 0 :=
    padicValRat_natCast_eq_zero_of_not_dvd hp10
  have htenQ : padicValRat p (10 * scaledBBPRat m) = -(e : ℤ) := by
    rw [padicValRat.mul (by norm_num) (scaledBBPRat_ne_zero m), hten, hval]
    simp
  have hrec : scaledBBPRat (m + 1) =
      10 * scaledBBPRat m + sampledBBPForcingRat m := by
    rw [sampledBBPForcingRat_eq_scaledBBPRat_sub]
    ring
  have hsum0 : 10 * scaledBBPRat m + sampledBBPForcingRat m ≠ 0 := by
    rw [← hrec]
    exact scaledBBPRat_ne_zero (m + 1)
  rw [hrec]
  rw [padicValRat.add_eq_of_lt hsum0
    (mul_ne_zero (by norm_num) (scaledBBPRat_ne_zero m))
    (ne_of_gt (sampledBBPForcingRat_pos m))]
  · exact htenQ
  · rw [htenQ]
    omega

/-- Across a block whose literal innovation supports avoid `p`, the exact old
prime-primary denominator exponent persists at every sampled depth. -/
theorem scaledBBPRat_padicVal_persists_block
    (m R p e : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10) (he : 0 < e)
    (hstable : ∀ ν < R,
      ¬p ∣ sampledBBPInnovationOddSupport (m + ν))
    (hval : padicValRat p (scaledBBPRat m) = -(e : ℤ)) :
    ∀ j ≤ R, padicValRat p (scaledBBPRat (m + j)) = -(e : ℤ) := by
  intro j hj
  induction j with
  | zero => simpa using hval
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      simpa [Nat.add_assoc] using
        scaledBBPRat_padicVal_persists_one_step
          (m + j) p e hp hp10 he (hstable j hjR) hprev

/-- Equality-aware congruence modulo the full prime power `p^e`.  The equality
branch is essential at lag zero because `padicValRat 0` is finite. -/
def PrimePowerCongruent (p e : ℕ) (x y : ℚ) : Prop :=
  x = y ∨ (e : ℤ) ≤ padicValRat p (x - y)

private lemma PrimePowerCongruent.refl (p e : ℕ) (x : ℚ) :
    PrimePowerCongruent p e x x := Or.inl rfl

private lemma PrimePowerCongruent.add
    {p e : ℕ} (hp : p.Prime) {x y z w : ℚ}
    (hxy : PrimePowerCongruent p e x y)
    (hzw : PrimePowerCongruent p e z w) :
    PrimePowerCongruent p e (x + z) (y + w) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold PrimePowerCongruent at hxy hzw ⊢
  rcases hxy with hxy | hxy
  · rcases hzw with hzw | hzw
    · left; linarith
    · right
      have heq : x + z - (y + w) = z - w := by rw [hxy]; ring
      rw [heq]
      exact hzw
  rcases hzw with hzw | hzw
  · right
    have heq : x + z - (y + w) = x - y := by rw [hzw]; ring
    rw [heq]
    exact hxy
  by_cases hzero : x + z - (y + w) = 0
  · left; linarith
  · right
    have heq : x + z - (y + w) = (x - y) + (z - w) := by ring
    have hdiff : (x - y) + (z - w) ≠ 0 := by
      rwa [← heq]
    rw [heq]
    exact le_trans (le_min hxy hzw) (padicValRat.min_le_padicValRat_add hdiff)

private lemma PrimePowerCongruent.mul_ten
    {p e : ℕ} (hp : p.Prime) (hp10 : ¬p ∣ 10) {x y : ℚ}
    (hxy : PrimePowerCongruent p e x y) :
    PrimePowerCongruent p e (10 * x) (10 * y) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hxy with rfl | hxy
  · exact Or.inl rfl
  · by_cases hdiff : x - y = 0
    · left; linarith
    · right
      rw [show 10 * x - 10 * y = 10 * (x - y) by ring,
        padicValRat.mul (by norm_num) hdiff]
      have hten : padicValRat p (10 : ℚ) = 0 :=
        padicValRat_natCast_eq_zero_of_not_dvd hp10
      rw [hten]
      simpa using hxy

private lemma forcing_primePowerCongruent_zero
    (m p e : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10)
    (hsupport : ¬p ∣ sampledBBPInnovationOddSupport m) :
    PrimePowerCongruent p e
      ((p : ℚ) ^ e * sampledBBPForcingRat m) 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  right
  have hforcing :=
    sampledBBPForcingRat_padicVal_nonneg_of_not_dvd_innovationSupport
      m p hp hp10 hsupport
  rw [sub_zero, padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    (ne_of_gt (sampledBBPForcingRat_pos m)),
    padicValRat.pow (by exact_mod_cast hp.ne_zero), padicValRat.self hp.one_lt]
  omega

/-- Correct finite-block form of BC's prime-power transport.  Lag zero uses
the equality branch; positive lags obtain the full `p^e` congruence from the
literal seven-row innovations. -/
theorem scaledBBPRat_primePower_transport
    (m R p e : ℕ) (hp : p.Prime) (hp10 : ¬p ∣ 10)
    (hstable : ∀ ν < R,
      ¬p ∣ sampledBBPInnovationOddSupport (m + ν)) :
    ∀ j ≤ R,
      PrimePowerCongruent p e
        ((p : ℚ) ^ e * scaledBBPRat (m + j))
        ((10 : ℚ) ^ j * ((p : ℚ) ^ e * scaledBBPRat m)) := by
  intro j hj
  induction j with
  | zero =>
      simpa using (PrimePowerCongruent.refl p e
        ((p : ℚ) ^ e * scaledBBPRat m))
  | succ j ih =>
      have hjR : j < R := by omega
      have hprev := ih (by omega)
      have hten := PrimePowerCongruent.mul_ten hp hp10 hprev
      have hforce := forcing_primePowerCongruent_zero
        (m + j) p e hp hp10 (hstable j hjR)
      have hadd := PrimePowerCongruent.add hp hten hforce
      have hrec : scaledBBPRat (m + j + 1) =
          10 * scaledBBPRat (m + j) + sampledBBPForcingRat (m + j) := by
        rw [sampledBBPForcingRat_eq_scaledBBPRat_sub]
        ring
      convert hadd using 1
      · rw [show m + (j + 1) = m + j + 1 by omega, hrec]
        ring
      · rw [pow_succ]
        ring

#print axioms sampledBBPForcingRat_padicVal_nonneg_of_not_dvd_innovationSupport
#print axioms scaledBBPRat_padicVal_persists_one_step
#print axioms scaledBBPRat_padicVal_persists_block
#print axioms scaledBBPRat_primePower_transport

end Theory.PiDigits.T168StableBBPPrimePowerTransport
