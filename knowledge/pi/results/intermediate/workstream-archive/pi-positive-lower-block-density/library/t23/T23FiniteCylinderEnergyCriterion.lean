import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T14T14PrefixAutomatonCertificates
import TheoryLib.PiPositiveLowerBlockDensity.T15T15FinitePrefixIntrinsicEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T16T16MatrixPowerEntropy
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# Conditional full-dimensional cylinder energy criterion

Canonical question: `problems/local/pi-positive-lower-block-density.txt`
SHA-256: `11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`

This module proves only a conditional implication. The full-dimensional
cylinder-energy hypothesis defined below is unproved for pi. In particular,
the module contains no unconditional energy estimate and no unconditional
claim that pi has positive lower block density.
-/

noncomputable section

open Filter Finset Set Topology

namespace Theory.PiDigits.PositiveLowerBlockDensity.T23

open Theory.PiDigits.PositiveLowerBlockDensity
open Theory.PiDigits.PositiveLowerBlockDensity.T9
open Theory.PiDigits.PositiveLowerBlockDensity.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T13
open Theory.PiDigits.PositiveLowerBlockDensity.T15
open DecimalFactorComplexity.FiniteCylinderEnergy

/-- The normalized collision energy of all length-`m` decimal words at the
first `N` starts. Thus each summand is literally `(A_pi(w,N) / N)^2`. -/
def E_pi (m N : ℕ) : ℝ :=
  ∑ w : Fin m → Fin 10,
    (blockFrequency Theory.PiDigits.piDigit (List.ofFn w) N) ^ 2

/-- The explicit conditional hypothesis. The constants `C` and `N0` may
depend on `s`, while the estimate is uniform in every later `N` and every
positive word length `m`. This hypothesis is currently unproved for pi. -/
def PiFullDimensionalCylinderEnergyDecay : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
        E_pi m N ≤ C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ))

/-- Quantifier audit for the conditional energy hypothesis. -/
theorem piFullDimensionalCylinderEnergyDecay_iff_quantifiers :
    PiFullDimensionalCylinderEnergyDecay ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ C : ℝ, 1 ≤ C ∧ ∃ N0 : ℕ,
          ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ, 1 ≤ m →
            E_pi m N ≤
              C * ((10 : ℝ) ^ (-s * (m : ℝ)) + 1 / (N : ℝ)) := by
  rfl

/-- Fully-contained probabilities are exactly T1 block frequencies at the
corresponding number `N + 1 - m` of retained starts. -/
theorem fullyContainedWordProbability_eq_blockFrequency
    (s : ℕ → Fin 10) {N m : ℕ} (_hmN : m ≤ N) (w : Fin m → Fin 10) :
    fullyContainedWordProbability s N m w =
      blockFrequency s (List.ofFn w) (N + 1 - m) := by
  simp only [fullyContainedWordProbability, fullyContainedWordCount,
    blockFrequency, blockCount]
  congr 2
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i
    simpa [prefixWord] using congrFun h (Fin.cast (by simp) i)
  · intro h
    funext i
    simpa [prefixWord] using h (Fin.cast (by simp) i)

/-- Consequently the squared fully-contained probabilities are exactly the
normalized energy at the retained number of starts. -/
theorem sum_sq_fullyContainedWordProbability_eq_E_pi
    {N m : ℕ} (hmN : m ≤ N) :
    (∑ w : Fin m → Fin 10,
        (fullyContainedWordProbability Theory.PiDigits.piDigit N m w) ^ 2) =
      E_pi m (N + 1 - m) := by
  simp_rw [fullyContainedWordProbability_eq_blockFrequency
    Theory.PiDigits.piDigit hmN]
  rfl

/-- Finite Cauchy--Schwarz with contaminated support. If at most mass `q`
lies outside `good`, then the full collision energy is at least the square of
the retained mass divided by the cardinality of `good` (in multiplication
form, so no positivity side condition on the cardinality is hidden). -/
theorem contaminatedSupport_collision_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (good : Finset ι) (q : ℝ)
    (hp : ∑ i, p i = 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbad : ∑ i ∈ goodᶜ, p i ≤ q) :
    (1 - q) ^ 2 ≤
      (good.card : ℝ) * ∑ i, (p i) ^ 2 := by
  have hpartition := good.sum_add_sum_compl p
  have hgoodMass : 1 - q ≤ ∑ i ∈ good, p i := by
    rw [hp] at hpartition
    linarith
  have hgoodMassNonneg : 0 ≤ ∑ i ∈ good, p i := by
    linarith
  have hretained : (1 - q) ^ 2 ≤ (∑ i ∈ good, p i) ^ 2 := by
    nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := good) (f := p)
  have hsumSq : (∑ i ∈ good, p i ^ 2) ≤ ∑ i, p i ^ 2 := by
    rw [← good.sum_add_sum_compl (fun i => p i ^ 2)]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _hi => sq_nonneg (p i))
  calc
    (1 - q) ^ 2 ≤ (∑ i ∈ good, p i) ^ 2 := hretained
    _ ≤ (good.card : ℝ) * ∑ i ∈ good, p i ^ 2 := hcs
    _ ≤ (good.card : ℝ) * ∑ i, p i ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsumSq (by positivity)

/-- The accepted arbitrary-offset contamination estimate combined with finite
Cauchy--Schwarz. If occurrences of `v` contaminate at most half the retained
mass, the collision energy has the displayed forbidden-support lower bound. -/
theorem contaminatedForbiddenSupport_collision_lower_bound
    {ell N m : ℕ} (hell : 0 < ell) (hm : 0 < m) (hroom : 2 * m ≤ N)
    (v : Fin ell → Fin 10)
    (hrare : 2 * (m + 1) *
        blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 4 ≤
      (forbiddenWordCount v m : ℝ) * E_pi m (N + 1 - m) := by
  let p : (Fin m → Fin 10) → ℝ :=
    fullyContainedWordProbability Theory.PiDigits.piDigit N m
  let good := forbiddenWords v m
  have hmN : m ≤ N := by omega
  have hp : ∑ w, p w = 1 := by
    exact sum_fullyContainedWordProbability Theory.PiDigits.piDigit hmN
  have hbad : ∑ w ∈ goodᶜ, p w ≤ (1 : ℝ) / 2 := by
    exact (forbiddenExceptionalMass_le Theory.PiDigits.piDigit hell hm hroom v).trans
      hrare
  have hcs := contaminatedSupport_collision_lower_bound p good ((1 : ℝ) / 2)
    hp (by norm_num) (by norm_num) hbad
  rw [show (1 - (1 : ℝ) / 2) ^ 2 = (1 : ℝ) / 4 by norm_num] at hcs
  rw [show (good.card : ℝ) = (forbiddenWordCount v m : ℝ) by
    simp [good, forbiddenWords_card]] at hcs
  rw [sum_sq_fullyContainedWordProbability_eq_E_pi hmN] at hcs
  exact hcs

/-- Iterating T13 submultiplicativity at the accepted two-block scale gives
an explicit finite forbidden-language growth bound. -/
theorem forbiddenWordCount_twoBlock_mul_le_pow
    {ell : ℕ} (v : Fin ell → Fin 10) (j : ℕ) :
    forbiddenWordCount v ((2 * ell) * j) ≤ forbiddenQ v ^ j := by
  induction j with
  | zero =>
      have h := Nat.card_le_card_of_injective
        (fun w : ForbiddenLanguage v 0 => w.1) Subtype.val_injective
      simpa [forbiddenWordCount] using h
  | succ j ih =>
      calc
        forbiddenWordCount v ((2 * ell) * (j + 1)) =
            forbiddenWordCount v ((2 * ell) * j + 2 * ell) := by
              congr 1
        _ ≤ forbiddenWordCount v ((2 * ell) * j) *
            forbiddenWordCount v (2 * ell) :=
          forbiddenWordCount_submultiplicative v _ _
        _ ≤ forbiddenQ v ^ j * forbiddenQ v := by
          exact Nat.mul_le_mul ih (by simp [forbiddenWordCount, forbiddenQ])
        _ = forbiddenQ v ^ (j + 1) := by rw [pow_succ]

/-- A concrete exponent strictly between the two-block forbidden-language
growth exponent and the full decimal exponent `1`. -/
def forbiddenDecayExponent {ell : ℕ} (v : Fin ell → Fin 10) : ℝ :=
  (Real.log (forbiddenQ v : ℝ) +
      ((2 * ell : ℕ) : ℝ) * Real.log 10) /
    (2 * (((2 * ell : ℕ) : ℝ) * Real.log 10))

theorem forbiddenDecayExponent_pos_lt_one
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    0 < forbiddenDecayExponent v ∧ forbiddenDecayExponent v < 1 := by
  have hd : (0 : ℝ) < ((2 * ell : ℕ) : ℝ) := by positivity
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hden : 0 < 2 * (((2 * ell : ℕ) : ℝ) * Real.log 10) := by positivity
  have hQnat : 0 < forbiddenQ v := forbiddenQ_pos v hell
  have hQone : (1 : ℝ) ≤ forbiddenQ v := by exact_mod_cast hQnat
  have hlogQ : 0 ≤ Real.log (forbiddenQ v : ℝ) := Real.log_nonneg hQone
  have hrate := forbiddenQ_rate_lt_log_ten v hell
  have hgap : Real.log (forbiddenQ v : ℝ) <
      ((2 * ell : ℕ) : ℝ) * Real.log 10 := by
    rw [div_lt_iff₀ hd] at hrate
    simpa [mul_comm] using hrate
  constructor
  · unfold forbiddenDecayExponent
    exact div_pos (by positivity) hden
  · unfold forbiddenDecayExponent
    rw [div_lt_one hden]
    linarith

/-- The geometric base obtained by dividing forbidden-language growth by the
chosen decimal decay is strictly below one. -/
theorem forbiddenDecayBase_nonneg_lt_one
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10) :
    0 ≤ (forbiddenQ v : ℝ) /
          (10 : ℝ) ^ (forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) ∧
      (forbiddenQ v : ℝ) /
          (10 : ℝ) ^ (forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) < 1 := by
  let d : ℝ := ((2 * ell : ℕ) : ℝ)
  let D : ℝ := d * Real.log 10
  have hd : 0 < d := by dsimp [d]; positivity
  have hlogTen : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hD : 0 < D := mul_pos hd hlogTen
  have hQnat : 0 < forbiddenQ v := forbiddenQ_pos v hell
  have hQpos : (0 : ℝ) < forbiddenQ v := by exact_mod_cast hQnat
  have hQone : (1 : ℝ) ≤ forbiddenQ v := by exact_mod_cast hQnat
  have hlogQ : 0 ≤ Real.log (forbiddenQ v : ℝ) := Real.log_nonneg hQone
  have hrate := forbiddenQ_rate_lt_log_ten v hell
  have hlogGap : Real.log (forbiddenQ v : ℝ) < D := by
    have hd' : (0 : ℝ) < ((2 * ell : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hd'] at hrate
    simpa [D, d, mul_comm] using hrate
  have hsD : forbiddenDecayExponent v * D =
      (Real.log (forbiddenQ v : ℝ) + D) / 2 := by
    unfold forbiddenDecayExponent
    dsimp [D, d]
    field_simp
  have hmid : Real.log (forbiddenQ v : ℝ) <
      forbiddenDecayExponent v * D := by
    rw [hsD]
    linarith
  have hpow : (forbiddenQ v : ℝ) <
      (10 : ℝ) ^ (forbiddenDecayExponent v * d) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
    rw [← Real.exp_log hQpos, Real.exp_lt_exp]
    simpa [D, mul_assoc, mul_left_comm, mul_comm] using hmid
  have hpowPos : 0 < (10 : ℝ) ^ (forbiddenDecayExponent v * d) :=
    Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · simpa [d] using div_nonneg hQpos.le hpowPos.le
  · simpa [d] using (div_lt_one hpowPos).2 hpow

/-- At a sufficiently large two-block multiple, the forbidden-language part
of the hypothesized energy upper bound is smaller than `1/16`. -/
theorem exists_twoBlockScale_forbidden_energy_small
    {ell : ℕ} (hell : 0 < ell) (v : Fin ell → Fin 10)
    (C : ℝ) (_hC : 0 < C) :
    ∃ j : ℕ, 1 ≤ j ∧
      C * (forbiddenQ v : ℝ) ^ j *
          (10 : ℝ) ^
            (-forbiddenDecayExponent v * (((2 * ell) * j : ℕ) : ℝ)) <
        (1 : ℝ) / 16 := by
  let a : ℝ := (forbiddenQ v : ℝ) /
    (10 : ℝ) ^ (forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ))
  have ha := forbiddenDecayBase_nonneg_lt_one hell v
  have ha0 : 0 ≤ a := by simpa [a] using ha.1
  have ha1 : a < 1 := by simpa [a] using ha.2
  have ht : Tendsto (fun j : ℕ => C * a ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul C
  have hevent : ∀ᶠ j : ℕ in atTop, C * a ^ j < (1 : ℝ) / 16 :=
    ht.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨j, hjSmall, hjOne⟩ :=
    (hevent.and (eventually_ge_atTop 1)).exists
  refine ⟨j, hjOne, ?_⟩
  have hten : (0 : ℝ) ≤ 10 := by norm_num
  have hexp :
      -forbiddenDecayExponent v * (((2 * ell) * j : ℕ) : ℝ) =
        (-forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) * (j : ℝ) := by
    push_cast
    ring
  have hneg :
      -forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ) =
        -(forbiddenDecayExponent v * ((2 * ell : ℕ) : ℝ)) := by ring
  have heq :
      (forbiddenQ v : ℝ) ^ j *
          (10 : ℝ) ^
            (-forbiddenDecayExponent v * (((2 * ell) * j : ℕ) : ℝ)) =
        a ^ j := by
    rw [hexp, Real.rpow_mul hten, Real.rpow_natCast]
    rw [hneg, Real.rpow_neg hten]
    dsimp [a]
    rw [div_pow, div_eq_mul_inv, ← inv_pow, ← mul_pow]
  rw [mul_assoc, heq]
  exact hjSmall

/-- Slow-scale cutoff selection. Zero lower frequency lets the prefix cutoff
grow past an arbitrary exponential requirement while keeping contamination
small. The final conjunct is the explicit comparison making the `1/N` term
negligible at the retained sample size `N + 1 - m`. -/
theorem zeroLiminf_exists_slowCutoff_inverse_negligible
    {ell : ℕ} (v : Fin ell → Fin 10)
    (hzero : liminf
      (blockFrequency Theory.PiDigits.piDigit (List.ofFn v)) atTop = 0)
    (C : ℝ) (hC : 0 < C) (N0 m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ,
      2 * m ≤ N ∧
      N0 ≤ N + 1 - m ∧
      2 * (m + 1) *
          blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤
        (1 : ℝ) / 2 ∧
      C * (forbiddenWordCount v m : ℝ) *
          (1 / ((N + 1 - m : ℕ) : ℝ)) <
        (1 : ℝ) / 16 := by
  obtain ⟨B : ℕ, hB⟩ := exists_nat_gt
    (16 * C * (forbiddenWordCount v m : ℝ) +
      ((N0 + 3 * m + 1 : ℕ) : ℝ))
  let eps : ℝ := 1 / (4 * ((m + 1 : ℕ) : ℝ))
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨N, hBN, hfreq⟩ :=
    arbitrarilyLate_blockFrequency_le (List.ofFn v) hzero B heps
  have hbase : N0 + 3 * m + 1 < B := by
    have hnonneg : 0 ≤ 16 * C * (forbiddenWordCount v m : ℝ) := by positivity
    have hreal : ((N0 + 3 * m + 1 : ℕ) : ℝ) < (B : ℝ) := by linarith
    exact_mod_cast hreal
  have hroom : 2 * m ≤ N := by omega
  have hmN : m ≤ N + 1 := by omega
  have hretained : N0 ≤ N + 1 - m := by omega
  have hrare : 2 * (m + 1) *
      blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤
        (1 : ℝ) / 2 := by
    have hfactor : (0 : ℝ) ≤ 2 * (m + 1) := by positivity
    calc
      2 * (m + 1) *
          blockFrequency Theory.PiDigits.piDigit (List.ofFn v) N ≤
        2 * (m + 1) * eps :=
          mul_le_mul_of_nonneg_left hfreq hfactor
      _ = (1 : ℝ) / 2 := by
        dsimp [eps]
        push_cast
        field_simp
        norm_num
  have hMposNat : 0 < N + 1 - m := by omega
  have hMpos : (0 : ℝ) < (N + 1 - m : ℕ) := by exact_mod_cast hMposNat
  have hMcast : ((N + 1 - m : ℕ) : ℝ) = (N : ℝ) + 1 - m := by
    rw [Nat.cast_sub hmN]
    norm_num
  have hlarge : 16 * C * (forbiddenWordCount v m : ℝ) <
      ((N + 1 - m : ℕ) : ℝ) := by
    have hBNreal : (B : ℝ) ≤ N := by exact_mod_cast hBN
    push_cast at hB
    rw [hMcast]
    linarith
  have hinverse : C * (forbiddenWordCount v m : ℝ) *
      (1 / ((N + 1 - m : ℕ) : ℝ)) < (1 : ℝ) / 16 := by
    rw [one_div]
    rw [← div_eq_mul_inv]
    rw [div_lt_iff₀ hMpos]
    nlinarith
  exact ⟨N, hroom, hretained, hrare, hinverse⟩

/-- The conditional full-dimensional collision-energy decay implies T1's
unchanged canonical positive-lower-block-density predicate. The proof is by
literal negation of that predicate and uses the accepted forbidden-language
growth and finite-prefix contamination bounds. -/
theorem piFullDimensionalCylinderEnergyDecay_implies_piPositiveLowerBlockDensity
    (hEnergy : PiFullDimensionalCylinderEnergyDecay) :
    PiPositiveLowerBlockDensity := by
  by_contra hnot
  obtain ⟨ell, hell, v, hzero⟩ := not_C1_exists_zero_liminf hnot
  let s := forbiddenDecayExponent v
  have hs : 0 < s ∧ s < 1 := by
    simpa [s] using forbiddenDecayExponent_pos_lt_one hell v
  obtain ⟨C, hC, N0, hupper⟩ := hEnergy s hs.1 hs.2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨j, hj, hsmall⟩ :=
    exists_twoBlockScale_forbidden_energy_small hell v C hCpos
  let m := (2 * ell) * j
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N, hroom, hN0, hrare, hinverse⟩ :=
    zeroLiminf_exists_slowCutoff_inverse_negligible
      v hzero C hCpos N0 m hm
  have hlower := contaminatedForbiddenSupport_collision_lower_bound
    hell hm hroom v hrare
  have hupperE := hupper (N + 1 - m) hN0 m hm
  have hcountNat := forbiddenWordCount_twoBlock_mul_le_pow v j
  have hcount : (forbiddenWordCount v m : ℝ) ≤
      (forbiddenQ v : ℝ) ^ j := by
    dsimp [m]
    exact_mod_cast hcountNat
  have hdecayNonneg : 0 ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hfirst : C * (forbiddenWordCount v m : ℝ) *
      (10 : ℝ) ^ (-s * (m : ℝ)) < (1 : ℝ) / 16 := by
    apply lt_of_le_of_lt _ hsmall
    have hmul := mul_le_mul_of_nonneg_left hcount hCpos.le
    exact mul_le_mul_of_nonneg_right hmul hdecayNonneg
  have henergySmall : (forbiddenWordCount v m : ℝ) * E_pi m (N + 1 - m) <
      (1 : ℝ) / 4 := by
    calc
      (forbiddenWordCount v m : ℝ) * E_pi m (N + 1 - m) ≤
          (forbiddenWordCount v m : ℝ) *
            (C * ((10 : ℝ) ^ (-s * (m : ℝ)) +
              1 / ((N + 1 - m : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hupperE (by positivity)
      _ = C * (forbiddenWordCount v m : ℝ) *
              (10 : ℝ) ^ (-s * (m : ℝ)) +
            C * (forbiddenWordCount v m : ℝ) *
              (1 / ((N + 1 - m : ℕ) : ℝ)) := by ring
      _ < (1 : ℝ) / 16 + (1 : ℝ) / 16 := add_lt_add hfirst hinverse
      _ < (1 : ℝ) / 4 := by norm_num
  exact (not_lt_of_ge hlower) henergySmall

/-- The unnormalized sum of all T1 word-count squares is exactly the accepted
finite decimal-cylinder collision count. -/
theorem sum_sq_blockCount_eq_piCylinderCollisionEnergy (m N : ℕ) :
    (∑ w : Fin m → Fin 10,
        blockCount Theory.PiDigits.piDigit (List.ofFn w) N ^ 2) =
      piCylinderCollisionEnergy m N := by
  classical
  let code : Fin N → (Fin m → Fin 10) := fun i j =>
    Theory.PiDigits.piDigit (i.val + j.val)
  let S := DecimalFactorComplexity.collisionPairs
    DecimalFactorComplexity.piDecimalStream m N
  have hpartition : S.card =
      ∑ w : Fin m → Fin 10,
        (S.filter fun ij => code ij.1 = w).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin m → Fin 10)))
      (f := fun ij => code ij.1) (by simp)
  rw [piCylinderCollisionEnergy_eq_E_pi]
  change (∑ w : Fin m → Fin 10,
      blockCount Theory.PiDigits.piDigit (List.ofFn w) N ^ 2) =
    DecimalFactorComplexity.collisionEnergy
      DecimalFactorComplexity.piDecimalStream m N
  rw [DecimalFactorComplexity.collisionEnergy_eq_collisionPairCount]
  change (∑ w : Fin m → Fin 10,
      blockCount Theory.PiDigits.piDigit (List.ofFn w) N ^ 2) = S.card
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [pow_two]
  unfold blockCount
  rw [← Finset.card_product]
  apply congrArg Finset.card
  ext ij
  simp only [Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, S,
    DecimalFactorComplexity.mem_collisionPairs_iff]
  constructor
  · rintro ⟨hi, hj⟩
    have hicode : code ij.1 = w := by
      funext k
      simpa [code] using hi (Fin.cast (by simp) k)
    have hjcode : code ij.2 = w := by
      funext k
      simpa [code] using hj (Fin.cast (by simp) k)
    have hfactor : DecimalFactorComplexity.factorAt
        DecimalFactorComplexity.piDecimalStream m ij.1 =
        DecimalFactorComplexity.factorAt
          DecimalFactorComplexity.piDecimalStream m ij.2 := by
      apply Subtype.ext
      funext k
      have hk := congrFun (hicode.trans hjcode.symm) k
      simpa [code, DecimalFactorComplexity.factorAt,
        DecimalFactorComplexity.blockAt,
        DecimalFactorComplexity.piDecimalStream,
        Theory.PiDigits.T20.decimalDigit_pi] using hk
    exact ⟨hfactor, hicode⟩
  · rintro ⟨hfactor, hicode⟩
    have hcodeeq : code ij.1 = code ij.2 := by
      funext k
      have hk := congrFun (congrArg Subtype.val hfactor) k
      simpa [code, DecimalFactorComplexity.factorAt,
        DecimalFactorComplexity.blockAt,
        DecimalFactorComplexity.piDecimalStream,
        Theory.PiDigits.T20.decimalDigit_pi] using hk
    have hjcode : code ij.2 = w := hcodeeq.symm.trans hicode
    constructor
    · intro k
      simpa [code] using congrFun hicode (Fin.cast (by simp) k)
    · intro k
      simpa [code] using congrFun hjcode (Fin.cast (by simp) k)

/-- T23's explicit word-sum energy is the normalized accepted finite-cylinder
energy. This theorem is an interface theorem, not a new statistic. -/
theorem E_pi_eq_normalizedPiCylinderCollisionEnergy (m N : ℕ) :
    E_pi m N = normalizedPiCylinderCollisionEnergy m N := by
  unfold E_pi normalizedPiCylinderCollisionEnergy
  rw [← sum_sq_blockCount_eq_piCylinderCollisionEnergy]
  push_cast
  simp only [blockFrequency, div_pow]
  rw [Finset.sum_div]

end Theory.PiDigits.PositiveLowerBlockDensity.T23

#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.piFullDimensionalCylinderEnergyDecay_iff_quantifiers
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.fullyContainedWordProbability_eq_blockFrequency
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.contaminatedSupport_collision_lower_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.contaminatedForbiddenSupport_collision_lower_bound
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.forbiddenWordCount_twoBlock_mul_le_pow
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.zeroLiminf_exists_slowCutoff_inverse_negligible
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.sum_sq_blockCount_eq_piCylinderCollisionEnergy
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.E_pi_eq_normalizedPiCylinderCollisionEnergy
#print axioms Theory.PiDigits.PositiveLowerBlockDensity.T23.piFullDimensionalCylinderEnergyDecay_implies_piPositiveLowerBlockDensity
