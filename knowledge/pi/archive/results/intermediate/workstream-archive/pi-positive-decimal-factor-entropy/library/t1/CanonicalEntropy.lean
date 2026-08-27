import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Subadditive
import TheoryLib.PiDigits.T11PiDigitFactorComplexity
import TheoryLib.PiDigits.T32FactorEntropyObstruction

/-!
# Canonical decimal factor entropy

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file proves an interface for arbitrary one-sided decimal streams and then
specializes it to the existing floor-based decimal digit stream for pi. It
does not prove positive entropy or disjunctivity for pi.

Normalized conventions: positions are zero-based after the decimal point;
factors are contiguous and may start anywhere; one fixed real `η > 0` and one
integer `N ≥ 1` must work for every `n ≥ N`; `10 ^ (η * n)` is real `rpow`.
The full-entropy endpoint is recorded explicitly as the stronger sibling A6,
not as the positive-entropy question A1. Empty words are included in the final
finite-word quantifier. Aligned blocks, finite prefixes, frequencies, and the
integer digit `3` are not substituted for the canonical factor language.
-/

noncomputable section

open Filter Set Topology

namespace DecimalFactorEntropy

open DecimalFactorComplexity

/-- Restrict a block of length `n + m` to its first `n` symbols. -/
def takeBlock {α : Type*} (n m : ℕ) (w : Block α (n + m)) : Block α n :=
  fun j => w ⟨j, by omega⟩

/-- Restrict a block of length `n + m` to its final `m` symbols. -/
def dropBlock {α : Type*} (n m : ℕ) (w : Block α (n + m)) : Block α m :=
  fun j => w ⟨n + j, by omega⟩

/-- Split an occurring factor into its initial and final factors. -/
def splitFactor {α : Type*} [Fintype α] [DecidableEq α]
    (s : Stream α) (n m : ℕ) : Factor s (n + m) → Factor s n × Factor s m :=
  fun w =>
    (⟨takeBlock n m w.1, by
      obtain ⟨i, hi⟩ := w.2
      exact ⟨i, fun j => hi ⟨j, by omega⟩⟩⟩,
    ⟨dropBlock n m w.1, by
      obtain ⟨i, hi⟩ := w.2
      exact ⟨i + n, fun j => by
        simpa [dropBlock, Nat.add_assoc] using hi ⟨n + j, by omega⟩⟩⟩)

/-- Prefix-suffix splitting loses no information. -/
theorem splitFactor_injective {α : Type*} [Fintype α] [DecidableEq α]
    (s : Stream α) (n m : ℕ) : Function.Injective (splitFactor s n m) := by
  intro a b hab
  apply Subtype.ext
  funext q
  by_cases hq : q.val < n
  · have hleft := congrArg (fun p => p.1.1) hab
    exact congrFun hleft ⟨q, hq⟩
  · have hright := congrArg (fun p => p.2.1) hab
    change dropBlock n m a.1 = dropBlock n m b.1 at hright
    have hindex : q.val - n < m := by omega
    have := congrFun hright ⟨q.val - n, hindex⟩
    simpa [dropBlock, Nat.add_sub_of_le (Nat.le_of_not_gt hq)] using this

/-- Exact factor counts are submultiplicative. -/
theorem canonicalFactorComplexity_submultiplicative
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Stream α) (n m : ℕ) :
    canonicalFactorComplexity s (n + m) ≤
      canonicalFactorComplexity s n * canonicalFactorComplexity s m := by
  have hcard := Nat.card_le_card_of_injective (splitFactor s n m)
    (splitFactor_injective s n m)
  rw [Nat.card_prod] at hcard
  simpa only [canonicalFactorComplexity] using hcard

/-- Every factor count is positive because the factor at position zero exists. -/
theorem canonicalFactorComplexity_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Stream α) (n : ℕ) : 0 < canonicalFactorComplexity s n := by
  letI : Nonempty (Factor s n) := ⟨factorAt s n 0⟩
  exact Nat.card_pos

/-- Logarithms turn factor-count submultiplicativity into subadditivity. -/
theorem factorLogCount_subadditive
    {α : Type*} [Fintype α] [DecidableEq α] (s : Stream α) :
    Subadditive (fun n => Real.log (canonicalFactorComplexity s n : ℝ)) := by
  intro n m
  have hn : (0 : ℝ) < canonicalFactorComplexity s n := by
    exact_mod_cast canonicalFactorComplexity_pos s n
  have hm : (0 : ℝ) < canonicalFactorComplexity s m := by
    exact_mod_cast canonicalFactorComplexity_pos s m
  have hnm : (0 : ℝ) < canonicalFactorComplexity s (n + m) := by
    exact_mod_cast canonicalFactorComplexity_pos s (n + m)
  have hcount : (canonicalFactorComplexity s (n + m) : ℝ) ≤
      (canonicalFactorComplexity s n : ℝ) * canonicalFactorComplexity s m := by
    exact_mod_cast canonicalFactorComplexity_submultiplicative s n m
  calc
    Real.log (canonicalFactorComplexity s (n + m) : ℝ) ≤
        Real.log ((canonicalFactorComplexity s n : ℝ) *
          canonicalFactorComplexity s m) :=
      Real.strictMonoOn_log.monotoneOn (mem_Ioi.mpr hnm)
        (mem_Ioi.mpr (mul_pos hn hm)) hcount
    _ = Real.log (canonicalFactorComplexity s n : ℝ) +
        Real.log (canonicalFactorComplexity s m : ℝ) :=
      Real.log_mul hn.ne' hm.ne'

/-- The normalized base-ten logarithmic factor count. -/
def entropyRatio (s : Stream (Fin 10)) (n : ℕ) : ℝ :=
  Real.log (canonicalFactorComplexity s n : ℝ) / ((n : ℝ) * Real.log 10)

/-- Base-ten factor entropy, represented by Fekete's subadditive limit. -/
def entropyBaseTen (s : Stream (Fin 10)) : ℝ :=
  (factorLogCount_subadditive s).lim / Real.log 10

theorem factorLogRatio_bddBelow (s : Stream (Fin 10)) :
    BddBelow (range (fun n : ℕ =>
      Real.log (canonicalFactorComplexity s n : ℝ) / (n : ℝ))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast canonicalFactorComplexity_pos s n))
    (Nat.cast_nonneg n)

/-- Fekete's lemma supplies the canonical entropy limit over all lengths. -/
theorem entropyRatio_tendsto (s : Stream (Fin 10)) :
    Tendsto (entropyRatio s) atTop (𝓝 (entropyBaseTen s)) := by
  have ht := (factorLogCount_subadditive s).tendsto_lim
    (factorLogRatio_bddBelow s)
  have hdiv := ht.div_const (Real.log 10)
  simpa only [entropyRatio, entropyBaseTen, div_div] using hdiv

/-- The canonical quantifiers: one fixed positive exponent works at every
sufficiently large length. The exponent is a real `rpow` exponent. -/
def EventuallyExponentialFactorGrowth (s : Stream (Fin 10)) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (10 : ℝ) ^ (η * (n : ℝ)) ≤ (canonicalFactorComplexity s n : ℝ)

/-- Positive base-ten entropy is equivalent to the canonical exponential
quantifiers. -/
theorem positive_entropy_iff_eventually_exponential (s : Stream (Fin 10)) :
    0 < entropyBaseTen s ↔ EventuallyExponentialFactorGrowth s := by
  constructor
  · intro hentropy
    let η := entropyBaseTen s / 2
    have hη : 0 < η := by dsimp [η]; linarith
    have hηlt : η < entropyBaseTen s := by dsimp [η]; linarith
    have hevent : ∀ᶠ n in atTop, η < entropyRatio s n :=
      (entropyRatio_tendsto s).eventually (Ioi_mem_nhds hηlt)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
    refine ⟨η, hη, max 1 N₀, le_max_left _ _, ?_⟩
    intro n hn
    have hnN₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
    have hnpos : 0 < n := by omega
    have hratio := hN₀ n hnN₀
    rw [entropyRatio] at hratio
    have hden : 0 < (n : ℝ) * Real.log 10 :=
      mul_pos (by exact_mod_cast hnpos) (Real.log_pos (by norm_num))
    have hlog : (η * (n : ℝ)) * Real.log 10 ≤
        Real.log (canonicalFactorComplexity s n : ℝ) := by
      have h := (lt_div_iff₀ hden).mp hratio
      nlinarith
    have hp : (0 : ℝ) < canonicalFactorComplexity s n := by
      exact_mod_cast canonicalFactorComplexity_pos s n
    exact (Real.rpow_le_iff_le_log (by norm_num) hp).2 hlog
  · rintro ⟨η, hη, N, hN, hgrowth⟩
    have hevent : ∀ᶠ n in atTop, η ≤ entropyRatio s n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnpos : 0 < n := by omega
      have hp : (0 : ℝ) < canonicalFactorComplexity s n := by
        exact_mod_cast canonicalFactorComplexity_pos s n
      have hlog :=
        (Real.rpow_le_iff_le_log (by norm_num) hp).mp (hgrowth n hn)
      have hden : 0 < (n : ℝ) * Real.log 10 :=
        mul_pos (by exact_mod_cast hnpos) (Real.log_pos (by norm_num))
      rw [entropyRatio]
      apply (le_div_iff₀ hden).2
      nlinarith
    have hle : η ≤ entropyBaseTen s :=
      ge_of_tendsto (entropyRatio_tendsto s) hevent
    exact hη.trans_le hle

/-- The explicit superlinear factor-complexity quantifiers. -/
def SuperlinearFactorComplexity (s : Stream (Fin 10)) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    C * (n : ℝ) < (canonicalFactorComplexity s n : ℝ)

/-- Positive factor entropy is strictly stronger than superlinear factor
complexity. -/
theorem positive_entropy_implies_superlinear (s : Stream (Fin 10))
    (hentropy : 0 < entropyBaseTen s) : SuperlinearFactorComplexity s := by
  obtain ⟨η, hη, N₀, hN₀, hgrowth⟩ :=
    (positive_entropy_iff_eventually_exponential s).mp hentropy
  intro C _hC
  let b := η * Real.log 10
  have hb : 0 < b := mul_pos hη (Real.log_pos (by norm_num))
  have ht : Tendsto
      (fun n : ℕ => Real.exp (b * (n : ℝ)) / (n : ℝ) ^ (1 : ℝ))
      atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop 1 b hb).comp
      tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      C < Real.exp (b * (n : ℝ)) / (n : ℝ) ^ (1 : ℝ) :=
    ht.eventually (eventually_gt_atTop C)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hevent
  refine ⟨max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega) hn₀)
  have hquot := hN₁ n hn₁
  rw [Real.rpow_one] at hquot
  have hexp : C * (n : ℝ) < Real.exp (b * (n : ℝ)) :=
    (lt_div_iff₀ hnpos).mp hquot
  have heq : Real.exp (b * (n : ℝ)) =
      (10 : ℝ) ^ (η * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [b]
    ring
  calc
    C * (n : ℝ) < Real.exp (b * (n : ℝ)) := hexp
    _ = (10 : ℝ) ^ (η * (n : ℝ)) := heq
    _ ≤ (canonicalFactorComplexity s n : ℝ) := hgrowth n hn₀

/-- Fekete's infimum inequality at each positive length. -/
theorem entropyBaseTen_le_ratio (s : Stream (Fin 10))
    {n : ℕ} (hn : 0 < n) : entropyBaseTen s ≤ entropyRatio s n := by
  have hlim := (factorLogCount_subadditive s).lim_le_div
    (factorLogRatio_bddBelow s) hn.ne'
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [entropyBaseTen, entropyRatio]
  calc
    (factorLogCount_subadditive s).lim / Real.log 10 ≤
        (Real.log (canonicalFactorComplexity s n : ℝ) / (n : ℝ)) /
          Real.log 10 := div_le_div_of_nonneg_right hlim hlog.le
    _ = Real.log (canonicalFactorComplexity s n : ℝ) /
        ((n : ℝ) * Real.log 10) := by field_simp

/-- Omitting one nonempty word gives the exact finite-word entropy threshold. -/
theorem entropyBaseTen_le_of_omits (s : Stream (Fin 10))
    {m : ℕ} (hm : 0 < m) (w : Block (Fin 10) m) (homit : ¬ Occurs s w) :
    entropyBaseTen s ≤
      Real.log (10 ^ m - 1 : ℕ) / ((m : ℝ) * Real.log 10) := by
  have hcount : canonicalFactorComplexity s m ≤ 10 ^ m - 1 := by
    simpa using
      Theory.PiDigits.T32.factorComplexity_mul_le_pow_of_omits
        s hm w homit 1 (by omega)
  have hA : (0 : ℝ) < (10 ^ m - 1 : ℕ) := by
    have hten : 10 ≤ 10 ^ m := by
      simpa using pow_le_pow_right' (by norm_num : 1 ≤ (10 : ℕ)) hm
    exact_mod_cast (by omega : 0 < 10 ^ m - 1)
  have hp : (0 : ℝ) < canonicalFactorComplexity s m := by
    exact_mod_cast canonicalFactorComplexity_pos s m
  have hlog : Real.log (canonicalFactorComplexity s m : ℝ) ≤
      Real.log (10 ^ m - 1 : ℕ) := by
    apply Real.strictMonoOn_log.monotoneOn (mem_Ioi.mpr hp) (mem_Ioi.mpr hA)
    exact_mod_cast hcount
  have hden : 0 < (m : ℝ) * Real.log 10 :=
    mul_pos (by exact_mod_cast hm) (Real.log_pos (by norm_num))
  exact (entropyBaseTen_le_ratio s hm).trans
    ((div_le_div_iff_of_pos_right hden).2 hlog)

/-- Every forbidden-word threshold is strictly below full decimal entropy. -/
theorem omittedBlock_threshold_lt_one {m : ℕ} (hm : 0 < m) :
    Real.log (10 ^ m - 1 : ℕ) / ((m : ℝ) * Real.log 10) < 1 := by
  have hraw := Theory.PiDigits.T32.omittedBlock_entropyBound_lt_logTen hm
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  calc
    Real.log (10 ^ m - 1 : ℕ) / ((m : ℝ) * Real.log 10) =
        (Real.log (10 ^ m - 1 : ℕ) / (m : ℝ)) / Real.log 10 := by
      field_simp
    _ < 1 := (div_lt_one hlog).2 hraw

/-- An entropy lower bound strictly above the length-`m` forbidden-word
threshold certifies occurrence of every length-`m` word. -/
theorem every_length_m_block_occurs_of_threshold_lt_entropy
    (s : Stream (Fin 10)) {m : ℕ} (hm : 0 < m)
    (hthreshold :
      Real.log (10 ^ m - 1 : ℕ) / ((m : ℝ) * Real.log 10) <
        entropyBaseTen s) :
    ∀ w : Block (Fin 10) m, Occurs s w := by
  intro w
  by_contra homit
  exact (not_le_of_gt hthreshold) (entropyBaseTen_le_of_omits s hm w homit)

/-- A decimal stream has full entropy exactly when every finite block occurs. -/
theorem entropyBaseTen_eq_one_iff_disjunctive (s : Stream (Fin 10)) :
    entropyBaseTen s = 1 ↔ Disjunctive s := by
  constructor
  · intro hentropy
    by_contra hnot
    simp only [Disjunctive, not_forall] at hnot
    obtain ⟨m, w, homit⟩ := hnot
    have hm : 0 < m := by
      by_contra hz
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hz
      subst m
      apply homit
      exact ⟨0, fun j => Fin.elim0 j⟩
    have hle := entropyBaseTen_le_of_omits s hm w homit
    have hlt := omittedBlock_threshold_lt_one hm
    linarith
  · intro hdisj
    have hratio : ∀ n : ℕ, 0 < n → entropyRatio s n = 1 := by
      intro n hn
      have hcount :=
        (decimal_disjunctive_iff_canonical_factorComplexity s).mp hdisj n
      rw [entropyRatio, hcount, Nat.cast_pow, Real.log_pow]
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hlog : Real.log (10 : ℝ) ≠ 0 :=
        (Real.log_pos (by norm_num)).ne'
      field_simp
      norm_num
    have hevent : entropyRatio s =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hratio n (by omega)
    have hone : Tendsto (entropyRatio s) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds.congr' hevent.symm
    exact tendsto_nhds_unique (entropyRatio_tendsto s) hone

/-- The entropy of the existing floor-based decimal digit stream for pi. -/
def piEntropyBaseTen : ℝ := entropyBaseTen Theory.PiDigits.piDigit

/-- Pi's exact factor counts inherit submultiplicativity. -/
theorem piFactorComplexity_submultiplicative (n m : ℕ) :
    Theory.PiDigits.FactorComplexity.piFactorComplexity (n + m) ≤
      Theory.PiDigits.FactorComplexity.piFactorComplexity n *
        Theory.PiDigits.FactorComplexity.piFactorComplexity m := by
  simpa [Theory.PiDigits.FactorComplexity.piFactorComplexity] using
    canonicalFactorComplexity_submultiplicative
      Theory.PiDigits.piDigit n m

/-- The canonical exponential formulation for pi, with every quantifier
visible in the theorem type. This is an equivalence, not a proof of either
side. -/
theorem pi_positive_entropy_iff_canonical_exponential_quantifiers :
    0 < piEntropyBaseTen ↔
      ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (10 : ℝ) ^ (η * (n : ℝ)) ≤
          (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) := by
  simpa [piEntropyBaseTen, EventuallyExponentialFactorGrowth,
    Theory.PiDigits.FactorComplexity.piFactorComplexity] using
      positive_entropy_iff_eventually_exponential Theory.PiDigits.piDigit

/-- Positive entropy for pi would imply the explicit superlinear complexity
quantifiers. The positive-entropy premise remains open. -/
theorem pi_positive_entropy_implies_superlinear
    (hentropy : 0 < piEntropyBaseTen) :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) <
        (Theory.PiDigits.FactorComplexity.piFactorComplexity n : ℝ) := by
  simpa [piEntropyBaseTen, SuperlinearFactorComplexity,
    Theory.PiDigits.FactorComplexity.piFactorComplexity] using
      positive_entropy_implies_superlinear Theory.PiDigits.piDigit hentropy

/-- A certified pi entropy bound above the exact length-`m` threshold would
certify all decimal words of that length. -/
theorem pi_every_length_m_block_occurs_of_threshold_lt_entropy
    {m : ℕ} (hm : 0 < m)
    (hthreshold :
      Real.log (10 ^ m - 1 : ℕ) / ((m : ℝ) * Real.log 10) <
        piEntropyBaseTen) :
    ∀ w : Block (Fin 10) m, Occurs Theory.PiDigits.piDigit w := by
  exact every_length_m_block_occurs_of_threshold_lt_entropy
    Theory.PiDigits.piDigit hm hthreshold

/-- Full factor entropy for pi is equivalent to the canonical finite-word
question. Neither side is assumed or proved. -/
theorem pi_entropy_eq_one_iff_every_finite_decimal_word_occurs :
    piEntropyBaseTen = 1 ↔ Theory.PiDigits.V1 := by
  rw [piEntropyBaseTen, entropyBaseTen_eq_one_iff_disjunctive]
  constructor
  · intro hdisj u
    let w : Block (Fin 10) u.length := fun j => u.get j
    obtain ⟨i, hi⟩ := hdisj u.length w
    refine ⟨i, fun j hj => ?_⟩
    exact (hi ⟨j, hj⟩).symm
  · intro hV1 n w
    obtain ⟨i, hi⟩ := hV1 (List.ofFn w)
    refine ⟨i, fun j => ?_⟩
    have hj := hi j.val (by simp)
    simpa using hj.symm

/-- The same full-entropy endpoint with the canonical finite-word quantifiers
expanded in the theorem type. Neither open side is assumed. -/
theorem pi_entropy_eq_one_iff_canonical_word_quantifiers :
    piEntropyBaseTen = 1 ↔
      ∀ u : List (Fin 10), ∃ i : ℕ, ∀ j : ℕ, ∀ hj : j < u.length,
        Theory.PiDigits.piDigit (i + j) = u.get ⟨j, hj⟩ := by
  simpa only [Theory.PiDigits.V1] using
    pi_entropy_eq_one_iff_every_finite_decimal_word_occurs

end DecimalFactorEntropy

#print axioms DecimalFactorEntropy.canonicalFactorComplexity_submultiplicative
#print axioms DecimalFactorEntropy.entropyRatio_tendsto
#print axioms DecimalFactorEntropy.positive_entropy_iff_eventually_exponential
#print axioms DecimalFactorEntropy.positive_entropy_implies_superlinear
#print axioms DecimalFactorEntropy.entropyBaseTen_le_of_omits
#print axioms DecimalFactorEntropy.every_length_m_block_occurs_of_threshold_lt_entropy
#print axioms DecimalFactorEntropy.entropyBaseTen_eq_one_iff_disjunctive
#print axioms DecimalFactorEntropy.piFactorComplexity_submultiplicative
#print axioms DecimalFactorEntropy.pi_positive_entropy_iff_canonical_exponential_quantifiers
#print axioms DecimalFactorEntropy.pi_positive_entropy_implies_superlinear
#print axioms DecimalFactorEntropy.pi_every_length_m_block_occurs_of_threshold_lt_entropy
#print axioms DecimalFactorEntropy.pi_entropy_eq_one_iff_canonical_word_quantifiers
