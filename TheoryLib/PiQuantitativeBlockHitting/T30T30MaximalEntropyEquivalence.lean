import TheoryLib.PiDigits.T32FactorEntropyObstruction

/-!
# T30: maximal factor entropy is equivalent to canonical V1

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

For an arbitrary decimal stream, the full factor entropy `log 10` is attained
exactly when every finite decimal block occurs.  The forward implication uses
T32: one omitted nonempty word forces a strict entropy deficit.  The reverse
implication computes the entropy from exact maximal factor complexity.

The final theorem identifies this generic statement with T7's exact canonical
`V1` proposition for the decimal digit stream of pi.  No theorem in this file
proves the maximal-entropy premise for pi, so the equivalence is not an
unconditional proof of V1.
-/

noncomputable section

open Filter

namespace Theory.PiDigits.MaximalEntropyEquivalence

open DecimalFactorComplexity
open Theory.PiDigits.T32

/-- A decimal stream has at most `10^n` distinct factors of length `n`. -/
lemma canonicalFactorComplexity_le_pow_ten
    (s : Stream (Fin 10)) (n : ℕ) :
    canonicalFactorComplexity s n ≤ 10 ^ n := by
  have hcard := Nat.card_le_card_of_injective
    (fun v : Factor s n ↦ v.1) Subtype.val_injective
  simpa [Nat.card_fun, Nat.card_fin] using hcard

/-- Every normalized logarithmic factor-complexity term is at most the full
decimal entropy `log 10`. -/
lemma factorEntropyTerm_le_logTen (s : Stream (Fin 10)) (n : ℕ) :
    factorEntropyTerm s n ≤ Real.log 10 := by
  have hpositive : 0 < (canonicalFactorComplexity s (n + 1) : ℝ) := by
    exact_mod_cast one_le_canonicalFactorComplexity s (n + 1)
  have hupper :
      (canonicalFactorComplexity s (n + 1) : ℝ) ≤
        ((10 ^ (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast canonicalFactorComplexity_le_pow_ten s (n + 1)
  have hlog := Real.log_le_log hpositive hupper
  rw [factorEntropyTerm]
  apply (div_le_iff₀ (by positivity)).2
  rw [Nat.cast_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  simpa [mul_comm] using hlog

/-- The factor entropy of every decimal stream is bounded above by `log 10`. -/
theorem factorEntropy_le_logTen (s : Stream (Fin 10)) :
    factorEntropy s ≤ Real.log 10 := by
  let ceiling : ℕ → ℝ := fun _ ↦ Real.log 10
  have heventual : factorEntropyTerm s ≤ᶠ[atTop] ceiling :=
    Filter.Eventually.of_forall (factorEntropyTerm_le_logTen s)
  have hnonneg : ∀ n, 0 ≤ factorEntropyTerm s n := by
    intro n
    exact div_nonneg
      (Real.log_natCast_nonneg (canonicalFactorComplexity s (n + 1)))
      (by positivity)
  have hcobounded :
      atTop.IsCoboundedUnder (· ≤ ·) (factorEntropyTerm s) :=
    Filter.isCoboundedUnder_le_of_le atTop hnonneg
  have hceiling : Tendsto ceiling atTop (nhds (Real.log 10)) := by
    exact tendsto_const_nhds
  calc
    factorEntropy s = limsup (factorEntropyTerm s) atTop := rfl
    _ ≤ limsup ceiling atTop :=
      limsup_le_limsup heventual hcobounded hceiling.isBoundedUnder_le
    _ = Real.log 10 := hceiling.limsup_eq

/-- Decimal disjunctivity gives exact maximal factor complexity at every
length and hence factor entropy `log 10`. -/
theorem factorEntropy_eq_logTen_of_disjunctive
    (s : Stream (Fin 10)) (hdisj : Disjunctive s) :
    factorEntropy s = Real.log 10 := by
  have hcomplexity : ∀ n : ℕ,
      canonicalFactorComplexity s n = 10 ^ n :=
    (decimal_disjunctive_iff_canonical_factorComplexity s).mp hdisj
  have hterm : factorEntropyTerm s = fun _ ↦ Real.log 10 := by
    funext n
    simp only [factorEntropyTerm, hcomplexity, Nat.cast_pow, Real.log_pow]
    norm_num
    field_simp
  rw [factorEntropy, hterm]
  exact tendsto_const_nhds.limsup_eq

/-- Conversely, maximal decimal factor entropy rules out every omitted
nonempty word by T32's strict entropy-deficit theorem. -/
theorem factorEntropy_eq_logTen_implies_disjunctive
    (s : Stream (Fin 10))
    (hentropy : factorEntropy s = Real.log 10) :
    Disjunctive s := by
  classical
  by_contra hnot
  rw [Disjunctive] at hnot
  push Not at hnot
  obtain ⟨k, w, homit⟩ := hnot
  have hk : 0 < k := by
    by_contra hk
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    apply homit
    refine ⟨0, ?_⟩
    intro j
    exact Fin.elim0 j
  have hdeficit : factorEntropy s < Real.log 10 :=
    (factorEntropy_le_of_omits s hk w homit).trans_lt
      (omittedBlock_entropyBound_lt_logTen hk)
  rw [hentropy] at hdeficit
  exact (lt_irrefl _ hdeficit)

/-- Exact generic characterization: a decimal stream has maximal factor
entropy if and only if every finite function-valued block occurs. -/
theorem factorEntropy_eq_logTen_iff_disjunctive (s : Stream (Fin 10)) :
    factorEntropy s = Real.log 10 ↔ Disjunctive s :=
  ⟨factorEntropy_eq_logTen_implies_disjunctive s,
    factorEntropy_eq_logTen_of_disjunctive s⟩

/-- T7's list-valued canonical V1 is exactly function-valued decimal
disjunctivity for `piDigit`, including the empty word and leading-zero words. -/
theorem canonicalV1_iff_piDisjunctive :
    Theory.PiDigits.V1 ↔ Disjunctive Theory.PiDigits.piDigit := by
  constructor
  · intro hV1 n w
    obtain ⟨i, hi⟩ := hV1 (List.ofFn w)
    refine ⟨i, ?_⟩
    intro j
    have hdigit := hi j.val (by simp)
    simpa using hdigit.symm
  · intro hdisj u
    obtain ⟨i, hi⟩ := hdisj u.length (listBlock u)
    refine ⟨i, ?_⟩
    intro j hj
    have hletter := hi ⟨j, hj⟩
    simpa [listBlock] using hletter.symm

/-- Canonical V1 is equivalently exact maximal factor complexity `10^n` at
every natural length. -/
theorem canonicalV1_iff_pi_maximalFactorComplexity :
    Theory.PiDigits.V1 ↔
      ∀ n : ℕ,
        canonicalFactorComplexity Theory.PiDigits.piDigit n = 10 ^ n := by
  rw [canonicalV1_iff_piDisjunctive,
    decimal_disjunctive_iff_canonical_factorComplexity]

/-- **Exact maximal-entropy bridge for canonical V1.** The decimal digit
stream of pi has factor entropy `log 10` if and only if every finite decimal
word occurs contiguously.  This equivalence proves neither side. -/
theorem pi_factorEntropy_eq_logTen_iff_canonicalV1 :
    factorEntropy Theory.PiDigits.piDigit = Real.log 10 ↔
      Theory.PiDigits.V1 := by
  rw [factorEntropy_eq_logTen_iff_disjunctive]
  exact canonicalV1_iff_piDisjunctive.symm

end Theory.PiDigits.MaximalEntropyEquivalence

#print axioms Theory.PiDigits.MaximalEntropyEquivalence.canonicalFactorComplexity_le_pow_ten
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.factorEntropyTerm_le_logTen
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.factorEntropy_le_logTen
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.factorEntropy_eq_logTen_of_disjunctive
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.factorEntropy_eq_logTen_implies_disjunctive
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.factorEntropy_eq_logTen_iff_disjunctive
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.canonicalV1_iff_piDisjunctive
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.canonicalV1_iff_pi_maximalFactorComplexity
#print axioms Theory.PiDigits.MaximalEntropyEquivalence.pi_factorEntropy_eq_logTen_iff_canonicalV1
