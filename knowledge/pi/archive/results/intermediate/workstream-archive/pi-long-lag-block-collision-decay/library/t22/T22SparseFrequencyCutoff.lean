import TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T12T12ScaleMatchedSpectralFrontier
import Mathlib.Data.Nat.MaxPowDiv

/-!
# T22: exact sparse integer-frequency cutoff for T8

Canonical question: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file only reindexes T8's finite sums and restates T12's predicate. It
proves no spectral estimate, no maximal theorem at `Real.pi`, and no instance
of the canonical collision-decay conjecture.
-/

noncomputable section

open Finset
open scoped BigOperators ComplexConjugate

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T22

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- The positive frequency attached to a `(lag,start)` core. -/
def positiveDecimalFrequency (p : LongPairCore) : ℕ :=
  10 ^ (p.2 + p.1) - 10 ^ p.2

/-- The signed frequency attached to an ordered T8 record. -/
def signedDecimalFrequency (q : OrderedLongPair) : ℤ :=
  if q.1 then (positiveDecimalFrequency q.2 : ℤ)
  else -(positiveDecimalFrequency q.2 : ℤ)

/-- The largest orbit exponent used by a core. -/
def frequencyEndpoint (p : LongPairCore) : ℕ := p.2 + p.1

/-- T8 admissibility without the finite orbit cutoff `N`. -/
def AdmissibleOrderedFrequency
    (μ c : ℝ) (Q0 m : ℕ) (q : OrderedLongPair) : Prop :=
  0 < q.2.1 ∧ m ≤ q.2.1 ∧
    ¬ ArithmeticExcluded μ c Q0 m q.2.2 q.2.1

theorem positiveDecimalFrequency_eq_mul (p : LongPairCore) :
    positiveDecimalFrequency p = 10 ^ p.2 * (10 ^ p.1 - 1) := by
  simp [positiveDecimalFrequency, pow_add, Nat.mul_sub_left_distrib]

theorem ten_not_dvd_pow_sub_one {r : ℕ} (hr : 0 < r) :
    ¬ 10 ∣ 10 ^ r - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hpow : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
  have heq : 10 ^ (r + 1) - 1 = 10 * (10 ^ r - 1) + 9 := by
    rw [pow_succ]
    omega
  rw [heq, Nat.add_mod]
  norm_num

theorem positiveDecimalFrequency_ne_zero
    {p : LongPairCore} (hp : 0 < p.1) :
    positiveDecimalFrequency p ≠ 0 := by
  rw [positiveDecimalFrequency_eq_mul]
  apply Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
  have hpow : 1 < 10 ^ p.1 := one_lt_pow₀ (by norm_num) hp.ne'
  omega

theorem padicValNat_positiveDecimalFrequency
    {p : LongPairCore} (hp : 0 < p.1) :
    padicValNat 10 (positiveDecimalFrequency p) = p.2 := by
  rw [positiveDecimalFrequency_eq_mul]
  rw [padicValNat_base_pow_mul (by norm_num : 1 < 10)]
  · have hval : padicValNat 10 (10 ^ p.1 - 1) = 0 := by
      have hn : 10 ^ p.1 - 1 ≠ 0 := by
        have hpow : 1 < 10 ^ p.1 := one_lt_pow₀ (by norm_num) hp.ne'
        omega
      have hnot := ten_not_dvd_pow_sub_one hp
      have hiff := Nat.pow_dvd_iff_le_padicValNat
        (p := 10) (k := 1) (n := 10 ^ p.1 - 1) (by norm_num) hn
      simp only [pow_one] at hiff
      omega
    omega
  · have hpow : 1 < 10 ^ p.1 := one_lt_pow₀ (by norm_num) hp.ne'
    omega

theorem positiveDecimalFrequency_injective_of_positiveLag
    {p₁ p₂ : LongPairCore} (hp₁ : 0 < p₁.1) (hp₂ : 0 < p₂.1)
    (hfrequency : positiveDecimalFrequency p₁ = positiveDecimalFrequency p₂) :
    p₁ = p₂ := by
  rcases p₁ with ⟨r₁, n₁⟩
  rcases p₂ with ⟨r₂, n₂⟩
  have hn : n₁ = n₂ := by
    have hval := congrArg (padicValNat 10) hfrequency
    rw [padicValNat_positiveDecimalFrequency hp₁,
      padicValNat_positiveDecimalFrequency hp₂] at hval
    exact hval
  subst n₂
  rw [positiveDecimalFrequency_eq_mul,
    positiveDecimalFrequency_eq_mul] at hfrequency
  simp only at hfrequency
  have hsub : 10 ^ r₁ - 1 = 10 ^ r₂ - 1 :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) n₁) hfrequency
  have hpows : 10 ^ r₁ = 10 ^ r₂ := by
    calc
      10 ^ r₁ = (10 ^ r₁ - 1) + 1 :=
        (Nat.sub_add_cancel (one_le_pow₀ (by norm_num))).symm
      _ = (10 ^ r₂ - 1) + 1 := by rw [hsub]
      _ = 10 ^ r₂ := Nat.sub_add_cancel (one_le_pow₀ (by norm_num))
  have hr : r₁ = r₂ := Nat.pow_right_injective (by norm_num) hpows
  subst r₂
  rfl

theorem signedDecimalFrequency_injective_of_positiveLag
    {q₁ q₂ : OrderedLongPair}
    (hq₁ : 0 < q₁.2.1) (hq₂ : 0 < q₂.2.1)
    (hfrequency : signedDecimalFrequency q₁ = signedDecimalFrequency q₂) :
    q₁ = q₂ := by
  rcases q₁ with ⟨b₁, p₁⟩
  rcases q₂ with ⟨b₂, p₂⟩
  have hp₁ne := positiveDecimalFrequency_ne_zero hq₁
  have hp₂ne := positiveDecimalFrequency_ne_zero hq₂
  cases b₁ <;> cases b₂
  · simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte] at hfrequency
    have hpositive : positiveDecimalFrequency p₁ = positiveDecimalFrequency p₂ := by
      exact_mod_cast neg_injective hfrequency
    congr 1
    exact positiveDecimalFrequency_injective_of_positiveLag hq₁ hq₂ hpositive
  · simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte] at hfrequency
    have hp₁pos : (0 : ℤ) < positiveDecimalFrequency p₁ := by exact_mod_cast Nat.pos_of_ne_zero hp₁ne
    have hp₂pos : (0 : ℤ) < positiveDecimalFrequency p₂ := by exact_mod_cast Nat.pos_of_ne_zero hp₂ne
    omega
  · simp only [signedDecimalFrequency, Bool.false_eq_true, ↓reduceIte] at hfrequency
    have hp₁pos : (0 : ℤ) < positiveDecimalFrequency p₁ := by exact_mod_cast Nat.pos_of_ne_zero hp₁ne
    have hp₂pos : (0 : ℤ) < positiveDecimalFrequency p₂ := by exact_mod_cast Nat.pos_of_ne_zero hp₂ne
    omega
  · simp only [signedDecimalFrequency, ↓reduceIte] at hfrequency
    have hpositive : positiveDecimalFrequency p₁ = positiveDecimalFrequency p₂ := by
      exact_mod_cast hfrequency
    congr 1
    exact positiveDecimalFrequency_injective_of_positiveLag hq₁ hq₂ hpositive

theorem signedDecimalFrequency_injective_of_admissible
    {μ c : ℝ} {Q0 m : ℕ} {q₁ q₂ : OrderedLongPair}
    (hq₁ : AdmissibleOrderedFrequency μ c Q0 m q₁)
    (hq₂ : AdmissibleOrderedFrequency μ c Q0 m q₂)
    (hfrequency : signedDecimalFrequency q₁ = signedDecimalFrequency q₂) :
    q₁ = q₂ :=
  signedDecimalFrequency_injective_of_positiveLag hq₁.1 hq₂.1 hfrequency

/-- Reverse the order of the two represented orbit exponents. -/
def reverseOrientation (q : OrderedLongPair) : OrderedLongPair :=
  (!q.1, q.2)

theorem admissible_reverseOrientation_iff
    (μ c : ℝ) (Q0 m : ℕ) (q : OrderedLongPair) :
    AdmissibleOrderedFrequency μ c Q0 m (reverseOrientation q) ↔
      AdmissibleOrderedFrequency μ c Q0 m q := by
  rfl

theorem signedDecimalFrequency_reverseOrientation (q : OrderedLongPair) :
    signedDecimalFrequency (reverseOrientation q) = -signedDecimalFrequency q := by
  rcases q with ⟨b, p⟩
  cases b <;> simp [reverseOrientation, signedDecimalFrequency]

/-- The coefficient multiplicity at signed integer frequency `k`. It is
independent of the finite cutoff `N`; uniqueness of decimal differences makes
every surviving coefficient either zero or one. -/
def coefficientMultiplicity
    (μ c : ℝ) (Q0 m : ℕ) (k : ℤ) : ℕ := by
  classical
  exact if ∃ q : OrderedLongPair,
      AdmissibleOrderedFrequency μ c Q0 m q ∧ signedDecimalFrequency q = k
    then 1 else 0

theorem coefficientMultiplicity_eq_one_iff
    (μ c : ℝ) (Q0 m : ℕ) (k : ℤ) :
    coefficientMultiplicity μ c Q0 m k = 1 ↔
      ∃ q : OrderedLongPair,
        AdmissibleOrderedFrequency μ c Q0 m q ∧ signedDecimalFrequency q = k := by
  classical
  unfold coefficientMultiplicity
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun hone => by norm_num at hone, fun hex => (h hex).elim⟩

theorem positiveDecimalFrequency_int_eq (n r : ℕ) :
    (positiveDecimalFrequency ⟨r, n⟩ : ℤ) =
      (10 : ℤ) ^ (n + r) - (10 : ℤ) ^ n := by
  have hpow : 10 ^ n ≤ 10 ^ (n + r) :=
    pow_le_pow_right' (by norm_num) (by omega)
  rw [show positiveDecimalFrequency ⟨r, n⟩ = 10 ^ (n + r) - 10 ^ n by rfl]
  push_cast [hpow]
  rfl

/-- The two literal decimal-difference coefficients have multiplicity one
exactly under the lag and arithmetic-survival conditions. -/
theorem coefficientMultiplicity_decimal_orientations
    (μ c : ℝ) (Q0 m n r : ℕ) (hr : 0 < r) :
    (coefficientMultiplicity μ c Q0 m
        ((10 : ℤ) ^ (n + r) - (10 : ℤ) ^ n) = 1 ↔
      m ≤ r ∧ ¬ ArithmeticExcluded μ c Q0 m n r) ∧
    (coefficientMultiplicity μ c Q0 m
        ((10 : ℤ) ^ n - (10 : ℤ) ^ (n + r)) = 1 ↔
      m ≤ r ∧ ¬ ArithmeticExcluded μ c Q0 m n r) := by
  have hk : (10 : ℤ) ^ (n + r) - (10 : ℤ) ^ n =
      (positiveDecimalFrequency ⟨r, n⟩ : ℤ) :=
    (positiveDecimalFrequency_int_eq n r).symm
  have hkneg : (10 : ℤ) ^ n - (10 : ℤ) ^ (n + r) =
      -(positiveDecimalFrequency ⟨r, n⟩ : ℤ) := by
    rw [positiveDecimalFrequency_int_eq]
    ring
  have hpositive : coefficientMultiplicity μ c Q0 m
      (positiveDecimalFrequency ⟨r, n⟩ : ℤ) = 1 ↔
        m ≤ r ∧ ¬ ArithmeticExcluded μ c Q0 m n r := by
    rw [coefficientMultiplicity_eq_one_iff]
    constructor
    · rintro ⟨q, hq, hfrequency⟩
      have htarget : signedDecimalFrequency q =
          signedDecimalFrequency (true, ⟨r, n⟩) := by
        simpa [signedDecimalFrequency] using hfrequency
      have hqeq := signedDecimalFrequency_injective_of_positiveLag
        hq.1 hr htarget
      subst q
      exact ⟨hq.2.1, hq.2.2⟩
    · rintro ⟨hmr, hnot⟩
      exact ⟨(true, ⟨r, n⟩), ⟨hr, hmr, hnot⟩, by
        simp [signedDecimalFrequency]⟩
  constructor
  · rw [hk]
    exact hpositive
  · rw [hkneg, coefficientMultiplicity_eq_one_iff]
    constructor
    · rintro ⟨q, hq, hfrequency⟩
      have htarget : signedDecimalFrequency q =
          signedDecimalFrequency (false, ⟨r, n⟩) := by
        simpa [signedDecimalFrequency] using hfrequency
      have hqeq := signedDecimalFrequency_injective_of_positiveLag
        hq.1 hr htarget
      subst q
      exact ⟨hq.2.1, hq.2.2⟩
    · rintro ⟨hmr, hnot⟩
      exact ⟨(false, ⟨r, n⟩), ⟨hr, hmr, hnot⟩, by
        simp [signedDecimalFrequency]⟩

theorem coefficientMultiplicity_neg
    (μ c : ℝ) (Q0 m : ℕ) (k : ℤ) :
    coefficientMultiplicity μ c Q0 m (-k) =
      coefficientMultiplicity μ c Q0 m k := by
  classical
  let P : ℤ → Prop := fun z => ∃ q : OrderedLongPair,
    AdmissibleOrderedFrequency μ c Q0 m q ∧ signedDecimalFrequency q = z
  have hsymm : P (-k) ↔ P k := by
    constructor
    · rintro ⟨q, hq, hfrequency⟩
      refine ⟨reverseOrientation q,
        (admissible_reverseOrientation_iff μ c Q0 m q).2 hq, ?_⟩
      rw [signedDecimalFrequency_reverseOrientation, hfrequency]
      simp
    · rintro ⟨q, hq, hfrequency⟩
      refine ⟨reverseOrientation q,
        (admissible_reverseOrientation_iff μ c Q0 m q).2 hq, ?_⟩
      rw [signedDecimalFrequency_reverseOrientation, hfrequency]
  unfold coefficientMultiplicity
  change (if P (-k) then 1 else 0) = if P k then 1 else 0
  rw [hsymm]

/-- T8's domain is exactly the `N`-cutoff of the `N`-independent admissible
ordered frequencies. -/
theorem mem_orderedLongPairDomain_iff_admissible_endpoint
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair} :
    q ∈ orderedLongPairDomain μ c Q0 m N ↔
      AdmissibleOrderedFrequency μ c Q0 m q ∧ frequencyEndpoint q.2 < N := by
  rw [mem_orderedLongPairDomain_iff]
  constructor
  · rintro ⟨hr0, hmr, hrN, hn, hnot⟩
    exact ⟨⟨hr0, hmr, hnot⟩, by simp only [frequencyEndpoint]; omega⟩
  · rintro ⟨⟨hr0, hmr, hnot⟩, hend⟩
    simp only [frequencyEndpoint] at hend
    exact ⟨hr0, hmr, by omega, by omega, hnot⟩

/-- Both ordered orientations occur together and carry opposite frequencies. -/
theorem both_orientations_exact
    (μ c : ℝ) (Q0 m N : ℕ) (p : LongPairCore) :
    ((false, p) ∈ orderedLongPairDomain μ c Q0 m N ↔
        0 < p.1 ∧ m ≤ p.1 ∧ frequencyEndpoint p < N ∧
          ¬ ArithmeticExcluded μ c Q0 m p.2 p.1) ∧
    ((true, p) ∈ orderedLongPairDomain μ c Q0 m N ↔
        0 < p.1 ∧ m ≤ p.1 ∧ frequencyEndpoint p < N ∧
          ¬ ArithmeticExcluded μ c Q0 m p.2 p.1) ∧
    signedDecimalFrequency (false, p) = -(positiveDecimalFrequency p : ℤ) ∧
    signedDecimalFrequency (true, p) = (positiveDecimalFrequency p : ℤ) := by
  constructor
  · rw [mem_orderedLongPairDomain_iff_admissible_endpoint]
    simp only [AdmissibleOrderedFrequency]
    tauto
  constructor
  · rw [mem_orderedLongPairDomain_iff_admissible_endpoint]
    simp only [AdmissibleOrderedFrequency]
    tauto
  · simp [signedDecimalFrequency]

/-- The finite symmetric sparse set of signed integer frequencies selected by
orbit exponents below `N`. -/
def sparseFrequencyCutoff
    (μ c : ℝ) (Q0 m N : ℕ) : Finset ℤ :=
  (orderedLongPairDomain μ c Q0 m N).image signedDecimalFrequency

theorem mem_sparseFrequencyCutoff_iff
    {μ c : ℝ} {Q0 m N : ℕ} {k : ℤ} :
    k ∈ sparseFrequencyCutoff μ c Q0 m N ↔
      ∃ q : OrderedLongPair,
        AdmissibleOrderedFrequency μ c Q0 m q ∧
          frequencyEndpoint q.2 < N ∧ signedDecimalFrequency q = k := by
  classical
  simp only [sparseFrequencyCutoff, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq
    exact ⟨q, hq'.1, hq'.2, rfl⟩
  · rintro ⟨q, hq, hend, rfl⟩
    exact ⟨q, mem_orderedLongPairDomain_iff_admissible_endpoint.mpr ⟨hq, hend⟩, rfl⟩

theorem sparseFrequencyCutoff_symmetric
    (μ c : ℝ) (Q0 m N : ℕ) (k : ℤ) :
    -k ∈ sparseFrequencyCutoff μ c Q0 m N ↔
      k ∈ sparseFrequencyCutoff μ c Q0 m N := by
  rw [mem_sparseFrequencyCutoff_iff, mem_sparseFrequencyCutoff_iff]
  constructor
  · rintro ⟨q, hq, hend, hfrequency⟩
    refine ⟨reverseOrientation q,
      (admissible_reverseOrientation_iff μ c Q0 m q).2 hq, hend, ?_⟩
    rw [signedDecimalFrequency_reverseOrientation, hfrequency]
    simp
  · rintro ⟨q, hq, hend, hfrequency⟩
    refine ⟨reverseOrientation q,
      (admissible_reverseOrientation_iff μ c Q0 m q).2 hq, hend, ?_⟩
    rw [signedDecimalFrequency_reverseOrientation, hfrequency]

theorem sparseFrequencyCutoff_mono
    (μ c : ℝ) (Q0 m N : ℕ) :
    sparseFrequencyCutoff μ c Q0 m N ⊆
      sparseFrequencyCutoff μ c Q0 m (N + 1) := by
  intro k hk
  rw [mem_sparseFrequencyCutoff_iff] at hk ⊢
  rcases hk with ⟨q, hq, hend, rfl⟩
  exact ⟨q, hq, by omega, rfl⟩

/-- Exact separation of the new `N`-layer: no older frequency can reappear
because admissible decimal differences have unique ordered records. -/
theorem mem_cutoff_succ_not_cutoff_iff_endpoint
    {μ c : ℝ} {Q0 m N : ℕ} {k : ℤ} :
    k ∈ sparseFrequencyCutoff μ c Q0 m (N + 1) ∧
        k ∉ sparseFrequencyCutoff μ c Q0 m N ↔
      ∃ q : OrderedLongPair,
        AdmissibleOrderedFrequency μ c Q0 m q ∧
          frequencyEndpoint q.2 = N ∧ signedDecimalFrequency q = k := by
  classical
  constructor
  · rintro ⟨hnext, hnot⟩
    rw [mem_sparseFrequencyCutoff_iff] at hnext
    rcases hnext with ⟨q, hq, hend, hfrequency⟩
    refine ⟨q, hq, ?_, hfrequency⟩
    by_contra hne
    have hlt : frequencyEndpoint q.2 < N := by omega
    apply hnot
    rw [mem_sparseFrequencyCutoff_iff]
    exact ⟨q, hq, hlt, hfrequency⟩
  · rintro ⟨q, hq, hend, hfrequency⟩
    constructor
    · rw [mem_sparseFrequencyCutoff_iff]
      exact ⟨q, hq, by omega, hfrequency⟩
    · intro hold
      rw [mem_sparseFrequencyCutoff_iff] at hold
      rcases hold with ⟨q', hq', hend', hfrequency'⟩
      have hqq' := signedDecimalFrequency_injective_of_admissible
        hq' hq (hfrequency'.trans hfrequency.symm)
      subst q'
      omega

/-- For the required positive block lengths, the first cutoff `N=1` is
empty, including all arithmetic-exclusion and orientation conventions. -/
theorem sparseFrequencyCutoff_one_eq_empty
    (μ c : ℝ) (Q0 m : ℕ) (hm : 1 ≤ m) :
    sparseFrequencyCutoff μ c Q0 m 1 = ∅ := by
  ext k
  constructor
  · intro hk
    rw [mem_sparseFrequencyCutoff_iff] at hk
    rcases hk with ⟨q, hq, hend, _⟩
    rcases q with ⟨b, ⟨r, n⟩⟩
    have hmr : m ≤ r := hq.2.1
    change n + r < 1 at hend
    omega
  · intro hk
    simp at hk

theorem orderedPhaseArgument_eq_signedFrequency_mul
    {q : OrderedLongPair} (hlag : 0 < q.2.1) :
    orderedPhaseArgument q = (signedDecimalFrequency q : ℝ) * Real.pi := by
  rcases q with ⟨b, ⟨r, n⟩⟩
  have hpow : 10 ^ n ≤ 10 ^ (n + r) :=
    pow_le_pow_right' (by norm_num) (by omega)
  cases b
  · simp only [orderedPhaseArgument, orderedFirst, orderedSecond,
      Bool.false_eq_true, ↓reduceIte, signedDecimalFrequency]
    rw [show positiveDecimalFrequency ⟨r, n⟩ = 10 ^ (n + r) - 10 ^ n by rfl]
    push_cast [hpow]
    ring
  · simp only [orderedPhaseArgument, orderedFirst, orderedSecond,
      ↓reduceIte, signedDecimalFrequency]
    rw [show positiveDecimalFrequency ⟨r, n⟩ = 10 ^ (n + r) - 10 ^ n by rfl]
    push_cast [hpow]
    rfl

theorem coefficientMultiplicity_eq_one_of_mem_cutoff
    {μ c : ℝ} {Q0 m N : ℕ} {k : ℤ}
    (hk : k ∈ sparseFrequencyCutoff μ c Q0 m N) :
    coefficientMultiplicity μ c Q0 m k = 1 := by
  rw [coefficientMultiplicity_eq_one_iff]
  rw [mem_sparseFrequencyCutoff_iff] at hk
  rcases hk with ⟨q, hq, _, hfrequency⟩
  exact ⟨q, hq, hfrequency⟩

/-- The Fourier polynomial with the orbit point left variable. The finite set
is the exact `N`-cutoff, while its coefficient multiplicities do not mention
`N`. -/
def cutoffFourierSum
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) (α : ℝ) : ℂ :=
  ∑ k ∈ sparseFrequencyCutoff μ c Q0 m N,
    (coefficientMultiplicity μ c Q0 m k : ℂ) *
      Theory.PiDigits.T27.phase h ((k : ℝ) * α)

/-- The same variable-point sum before collecting equal integer frequencies. -/
def orderedAlphaSum
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) (α : ℝ) : ℂ :=
  ∑ q ∈ orderedLongPairDomain μ c Q0 m N,
    Theory.PiDigits.T27.phase h ((signedDecimalFrequency q : ℝ) * α)

theorem orderedAlphaSum_eq_cutoffFourierSum
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) (α : ℝ) :
    orderedAlphaSum μ c Q0 m N h α =
      cutoffFourierSum μ c Q0 m N h α := by
  classical
  unfold orderedAlphaSum cutoffFourierSum
  apply Finset.sum_bij (fun q _hq => signedDecimalFrequency q)
  · intro q hq
    exact Finset.mem_image_of_mem signedDecimalFrequency hq
  · intro q₁ hq₁ q₂ hq₂ heq
    apply signedDecimalFrequency_injective_of_admissible
    · exact (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq₁).1
    · exact (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq₂).1
    · exact heq
  · intro k hk
    rw [sparseFrequencyCutoff, Finset.mem_image] at hk
    rcases hk with ⟨q, hq, hfrequency⟩
    exact ⟨q, hq, hfrequency⟩
  · intro q hq
    rw [coefficientMultiplicity_eq_one_of_mem_cutoff
      (Finset.mem_image_of_mem signedDecimalFrequency hq)]
    simp

/-- Every signed T8 sum is exactly the sparse cutoff polynomial evaluated at
the fixed orbit point `alpha = pi`. -/
theorem signedSpectralSum_eq_cutoffFourierSum_pi
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) :
    signedSpectralSum μ c Q0 m N h =
      cutoffFourierSum μ c Q0 m N h Real.pi := by
  rw [← orderedAlphaSum_eq_cutoffFourierSum]
  unfold signedSpectralSum orderedAlphaSum
  apply Finset.sum_congr rfl
  intro q hq
  rw [orderedPhaseArgument_eq_signedFrequency_mul
    (mem_orderedLongPairDomain_iff_admissible_endpoint.mp hq).1.1]

/-- Literal identity for every T8 positive-frequency sum `S_h(m,N)`. -/
theorem spectralSum_eq_cutoffFourierSum_pi
    (μ c : ℝ) (Q0 m N h : ℕ) :
    spectralSum μ c Q0 m N h =
      cutoffFourierSum μ c Q0 m N (h : ℤ) Real.pi := by
  exact signedSpectralSum_eq_cutoffFourierSum_pi μ c Q0 m N (h : ℤ)

/-- T12's L1 frontier written entirely with the exact sparse cutoff. This is
a predicate, not an assertion that the displayed estimate holds. -/
def CutoffScaleMatchedL1Bound (μ c : ℝ) (Q0 : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖cutoffFourierSum μ c Q0 m N (h : ℤ) Real.pi‖) ≤
          B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N

/-- Full parameter and quantifier audit of the cutoff formulation. -/
theorem cutoffScaleMatchedL1Bound_iff_quantifiers
    (μ c : ℝ) (Q0 : ℕ) :
    CutoffScaleMatchedL1Bound μ c Q0 ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
                ‖cutoffFourierSum μ c Q0 m N (h : ℤ) Real.pi‖) ≤
              B * (decimalFrequency m : ℝ) * scaleMatchedTarget s m N := by
  rfl

/-- Exact equivalence with T12's original scale-matched L1 predicate. -/
theorem cutoffScaleMatchedL1Bound_iff_T12
    (μ c : ℝ) (Q0 : ℕ) :
    CutoffScaleMatchedL1Bound μ c Q0 ↔ ScaleMatchedL1Bound μ c Q0 := by
  constructor
  · intro hcutoff s hs0 hs1
    obtain ⟨B, hB, hbound⟩ := hcutoff s hs0 hs1
    refine ⟨B, hB, ?_⟩
    intro m N hm hN
    simpa only [spectralSum_eq_cutoffFourierSum_pi] using hbound m N hm hN
  · intro hT12 s hs0 hs1
    obtain ⟨B, hB, hbound⟩ := hT12 s hs0 hs1
    refine ⟨B, hB, ?_⟩
    intro m N hm hN
    simpa only [spectralSum_eq_cutoffFourierSum_pi] using hbound m N hm hN

end Theory.PiDigits.LongLagBlockCollisionDecay.T22

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.coefficientMultiplicity_eq_one_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.coefficientMultiplicity_decimal_orientations
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.coefficientMultiplicity_neg
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.mem_orderedLongPairDomain_iff_admissible_endpoint
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.both_orientations_exact
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.mem_sparseFrequencyCutoff_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.sparseFrequencyCutoff_symmetric
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.mem_cutoff_succ_not_cutoff_iff_endpoint
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.sparseFrequencyCutoff_one_eq_empty
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.spectralSum_eq_cutoffFourierSum_pi
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.cutoffScaleMatchedL1Bound_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T22.cutoffScaleMatchedL1Bound_iff_T12
