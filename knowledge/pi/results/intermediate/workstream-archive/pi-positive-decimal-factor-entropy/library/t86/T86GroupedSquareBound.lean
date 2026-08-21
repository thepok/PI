import TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit
import TheoryLib.PiPositiveDecimalFactorEntropy.T58T58TriangularFejerAudit
import TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic

/-!
# T86: kernel-checked grouped square bound for the T61 short residual

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

This file formalizes only the deterministic finite grouping suggested by the
unverified T85 note.  It imports the checked T56, T58, and T61 interfaces and
does not use T83, T84, or T85 as premises.  It proves no estimate at `Real.pi`
and no instance of C7, C2, C1, or positive decimal factor entropy.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DecimalFactorComplexity.T86GroupedSquareBound

open DecimalFactorComplexity.T56LagSectorAudit
open DecimalFactorComplexity.T58TriangularFejerAudit
open DecimalFactorComplexity.T61VaalerAnalytic
open Theory.PiDigits.LongLagBlockCollisionDecay.T16

/-- A T61 positive-frequency residual tuple, ordered as `(h,(r,j))`. -/
abbrev ResidualTuple := ℕ × (ℕ × ℕ)

/-- The exact product of T58's strict positive-frequency range and T61's
masked upper-triangular short residual rectangle. -/
def residualTupleDomain (μ c : ℝ) (Q0 n : ℕ) : Finset ResidualTuple :=
  positiveFejerFrequencies n ×ˢ residualShortRectangle μ c Q0 n

/-- The positive integer frequency attached to `(h,r,j)`. -/
def tupleFrequency (a : ResidualTuple) : ℕ :=
  phi a.1 a.2.2 a.2.1

/-- T61's literal signed Vaaler coefficient on a tuple. -/
def tupleWeight (n : ℕ) (a : ResidualTuple) : ℝ :=
  vaalerCoefficient (shortBandwidth n) a.1

/-- Exact finite fiber above a positive integer frequency. -/
def frequencyFiber (μ c : ℝ) (Q0 n q : ℕ) : Finset ResidualTuple :=
  (residualTupleDomain μ c Q0 n).filter fun a => tupleFrequency a = q

/-- Exact finite positive-frequency support at scale `n`. -/
def frequencySupport (μ c : ℝ) (Q0 n : ℕ) : Finset ℕ :=
  (residualTupleDomain μ c Q0 n).image tupleFrequency

/-- The normalized grouped coefficient.  The factor is exactly `2/L_n`,
including T61's outer factor two. -/
def groupedCoefficient (μ c : ℝ) (Q0 n q : ℕ) : ℝ :=
  (2 : ℝ) / (T61VaalerAnalytic.sampleLength n : ℝ) *
    ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a

/-- T85's notation `B_n(q)`, exposed transparently for downstream use. -/
abbrev B_n (μ c : ℝ) (Q0 n q : ℕ) : ℝ :=
  groupedCoefficient μ c Q0 n q

/-- Finite union of all supports at scales `0 ≤ n ≤ N`. -/
def cumulativeFrequencySupport (μ c : ℝ) (Q0 N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).biUnion fun n => frequencySupport μ c Q0 n

/-- One-scale grouped square energy. -/
def oneScaleEnergy (μ c : ℝ) (Q0 n : ℕ) : ℝ :=
  ∑ q ∈ frequencySupport μ c Q0 n,
    |groupedCoefficient μ c Q0 n q| ^ 2

/-- T86's cumulative grouped square, with every coefficient extended by zero
off its finite support. -/
def groupedSquare (μ c : ℝ) (Q0 N : ℕ) : ℝ :=
  ∑ q ∈ cumulativeFrequencySupport μ c Q0 N,
    |∑ n ∈ Finset.range (N + 1), groupedCoefficient μ c Q0 n q| ^ 2

/-- T85's notation `D_N`, with its finite-support convention explicit in
`groupedSquare`. -/
abbrev D_N (μ c : ℝ) (Q0 N : ℕ) : ℝ := groupedSquare μ c Q0 N

/-- The exact positive-frequency tuple sum, retaining T61's outer factor two.
The T61 zero mode is a separate term and is not present here. -/
def residualTupleCosineSum (μ c : ℝ) (Q0 n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ a ∈ residualTupleDomain μ c Q0 n,
    tupleWeight n a * Real.cos (2 * Real.pi * (tupleFrequency a : ℝ) * x)

/-- A fixed-frequency tuple is coded by its lag and start residue modulo the
scale index.  The frequency equation makes this code injective. -/
def fiberCode (n : ℕ) (a : ResidualTuple) : ℕ × ℕ :=
  (a.2.1, a.2.2 % n)

/-- Literal audit of every multiplier, lag, start, and residual-mask endpoint.
The explicit `r < L_n` follows from the nonempty strict start range. -/
theorem mem_residualTupleDomain_iff
    {μ c : ℝ} {Q0 n : ℕ} {a : ResidualTuple} :
    a ∈ residualTupleDomain μ c Q0 n ↔
      1 ≤ a.1 ∧ a.1 < shortBandwidth n ∧
      0 < a.2.1 ∧ a.2.1 < n ∧
      a.2.1 < T61VaalerAnalytic.sampleLength n ∧
      a.2.2 < T61VaalerAnalytic.sampleLength n - a.2.1 ∧
      ¬ Theory.PiDigits.PositiveLowerBlockDensity.T25.ArithmeticExcluded
        μ c Q0 n a.2.2 a.2.1 := by
  rw [residualTupleDomain, Finset.mem_product]
  rw [mem_positiveFejerFrequencies_iff, mem_residualShortRectangle_iff]
  constructor
  · rintro ⟨⟨hh0, hhH⟩, hr0, hrn, hj, hmask⟩
    have hsub : 0 < T61VaalerAnalytic.sampleLength n - a.2.1 :=
      (Nat.zero_le a.2.2).trans_lt hj
    exact ⟨hh0, hhH, hr0, hrn, Nat.sub_pos_iff_lt.mp hsub, hj, hmask⟩
  · rintro ⟨hh0, hhH, hr0, hrn, _hrL, hj, hmask⟩
    exact ⟨⟨hh0, hhH⟩, hr0, hrn, hj, hmask⟩

/-- The tuple frequency is exactly T58's positive structured frequency. -/
theorem tupleFrequency_eq (h r j : ℕ) :
    tupleFrequency (h, (r, j)) = h * 10 ^ j * (10 ^ r - 1) := by
  rfl

/-- The tuple weight is T61's literal signed coefficient, not an absolute or
triangular replacement. -/
theorem tupleWeight_explicit (n : ℕ) (a : ResidualTuple) :
    tupleWeight n a =
      (shortBandwidth n : ℝ)⁻¹ *
        (Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) / Real.pi +
          2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
            Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))) := by
  exact vaalerCoefficient_explicit _ _

/-- Membership in the exact finite frequency support is witnessed by a T61
residual tuple with that frequency. -/
theorem mem_frequencySupport_iff
    {μ c : ℝ} {Q0 n q : ℕ} :
    q ∈ frequencySupport μ c Q0 n ↔
      ∃ a ∈ residualTupleDomain μ c Q0 n, tupleFrequency a = q := by
  simp [frequencySupport]

/-- All supported frequencies are strictly positive; the T61 zero Fourier
mode is consequently absent from every grouped coefficient square. -/
theorem frequencySupport_positive
    {μ c : ℝ} {Q0 n q : ℕ} (hq : q ∈ frequencySupport μ c Q0 n) :
    0 < q := by
  obtain ⟨a, ha, rfl⟩ := mem_frequencySupport_iff.mp hq
  have hrange := mem_residualTupleDomain_iff.mp ha
  change 0 < a.1 * 10 ^ a.2.2 * (10 ^ a.2.1 - 1)
  have hrep : 0 < 10 ^ a.2.1 - 1 := by
    have hone : 1 < 10 ^ a.2.1 :=
      Nat.one_lt_pow (Nat.ne_of_gt hrange.2.2.1) (by norm_num)
    omega
  exact Nat.mul_pos (Nat.mul_pos hrange.1 (pow_pos (by norm_num) _)) hrep

/-- Literal zero-mode convention: frequency zero is not in the grouped
positive-frequency support. -/
theorem zero_not_mem_frequencySupport (μ c : ℝ) (Q0 n : ℕ) :
    0 ∉ frequencySupport μ c Q0 n := by
  intro hzero
  exact (Nat.not_lt_zero 0) (frequencySupport_positive hzero)

/-- Finite-support convention: the grouped coefficient is zero away from its
scale support. -/
theorem groupedCoefficient_eq_zero_of_not_mem
    {μ c : ℝ} {Q0 n q : ℕ} (hq : q ∉ frequencySupport μ c Q0 n) :
    groupedCoefficient μ c Q0 n q = 0 := by
  have hfiber : frequencyFiber μ c Q0 n q = ∅ := by
    rw [frequencyFiber, Finset.filter_eq_empty_iff]
    intro a ha hfrequency
    exact hq (mem_frequencySupport_iff.mpr ⟨a, ha, hfrequency⟩)
  simp [groupedCoefficient, hfiber]

/-- At scale zero both the positive frequency range and every grouped
coefficient are empty, so `B_0(q)=0` literally. -/
theorem groupedCoefficient_zero_scale (μ c : ℝ) (Q0 q : ℕ) :
    groupedCoefficient μ c Q0 0 q = 0 := by
  have hsupport : q ∉ frequencySupport μ c Q0 0 := by
    intro hq
    have hpos := frequencySupport_positive hq
    obtain ⟨a, ha, _⟩ := mem_frequencySupport_iff.mp hq
    have hrange := mem_residualTupleDomain_iff.mp ha
    norm_num [shortBandwidth, bandwidth] at hrange
  exact groupedCoefficient_eq_zero_of_not_mem hsupport

/-- Consequently the grouped coefficient at Fourier frequency zero vanishes
at every scale; T61's separate constant term is not folded into `B_n`. -/
theorem B_n_zero_frequency (μ c : ℝ) (Q0 n : ℕ) :
    B_n μ c Q0 n 0 = 0 :=
  groupedCoefficient_eq_zero_of_not_mem
    (zero_not_mem_frequencySupport μ c Q0 n)

/-- Named expansion of the exact normalized grouped coefficient. -/
theorem B_n_eq_exact_fiber (μ c : ℝ) (Q0 n q : ℕ) :
    B_n μ c Q0 n q =
      (2 : ℝ) / (T61VaalerAnalytic.sampleLength n : ℝ) *
        ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a := by
  rfl

/-- Named expansion of `D_N`, including the finite union support and the
literal scale range `0 ≤ n ≤ N`. -/
theorem D_N_eq_finite_grouped_square (μ c : ℝ) (Q0 N : ℕ) :
    D_N μ c Q0 N =
      ∑ q ∈ cumulativeFrequencySupport μ c Q0 N,
        |∑ n ∈ Finset.range (N + 1), B_n μ c Q0 n q| ^ 2 := by
  rfl

/-- Flattening T61's nested lag/start convention gives exactly its masked
residual rectangle; no rectangular enlargement is introduced. -/
theorem sum_residualShortRectangle_eq_nested
    (μ c : ℝ) (Q0 n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ residualShortRectangle μ c Q0 n, f p.1 p.2) =
      ∑ r ∈ Theory.PiDigits.PositiveLowerBlockDensity.T26.shortResidualLags
          n (T61VaalerAnalytic.sampleLength n),
        ∑ j ∈ residualStartDomain μ c Q0 n r, f r j := by
  classical
  exact Finset.sum_finset_product' _ _ _ (by
    intro p
    rcases p with ⟨r, j⟩
    constructor
    · intro hp
      have hp' := mem_residualShortRectangle_iff.mp hp
      have hLpos : 0 < T61VaalerAnalytic.sampleLength n - r :=
        (Nat.zero_le j).trans_lt hp'.2.2.1
      have hrL : r < T61VaalerAnalytic.sampleLength n :=
        Nat.sub_pos_iff_lt.mp hLpos
      have hr :
          r ∈ Theory.PiDigits.PositiveLowerBlockDensity.T26.shortResidualLags
            n (T61VaalerAnalytic.sampleLength n) :=
        Theory.PiDigits.PositiveLowerBlockDensity.T26.mem_shortResidualLags_iff.mpr
          ⟨hp'.1, hp'.2.1, hrL⟩
      have hj : j ∈ residualStartDomain μ c Q0 n r := by
        unfold residualStartDomain
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hp'.2.2.1, hp'.2.2.2⟩
      exact ⟨hr, hj⟩
    · rintro ⟨hr, hj⟩
      have hr' :=
        Theory.PiDigits.PositiveLowerBlockDensity.T26.mem_shortResidualLags_iff.mp hr
      unfold residualStartDomain at hj
      exact mem_residualShortRectangle_iff.mpr
        ⟨hr'.1, hr'.2.1, Finset.mem_range.mp (Finset.mem_filter.mp hj).1,
          (Finset.mem_filter.mp hj).2⟩)

/-- The tuple convention is exactly T61's signed nested residual sum when the
phase variable is `Real.pi`; this is bookkeeping, not a fixed-pi estimate. -/
theorem residualTupleCosineSum_pi_eq_T61
    (μ c : ℝ) (Q0 n : ℕ) :
    residualTupleCosineSum μ c Q0 n Real.pi =
      signedStructuredDenominatorSum μ c Q0 n := by
  classical
  unfold residualTupleCosineSum signedStructuredDenominatorSum
  rw [residualTupleDomain, Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [← sum_residualShortRectangle_eq_nested μ c Q0 n]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change vaalerCoefficient (shortBandwidth n) h *
      Real.cos (2 * Real.pi * (phi h p.2 p.1 : ℝ) * Real.pi) = _
  rw [phi_eq_frequency_mul_structuredDenominator]
  push_cast
  ring_nf

/-- Exact finite frequency grouping with the normalization `2/L_n`.  All
duplicate frequencies are summed inside `groupedCoefficient`; no injectivity
of `tupleFrequency` is assumed. -/
theorem normalized_frequency_grouping
    (μ c : ℝ) (Q0 n : ℕ) (x : ℝ) :
    residualTupleCosineSum μ c Q0 n x /
        (T61VaalerAnalytic.sampleLength n : ℝ) =
      ∑ q ∈ frequencySupport μ c Q0 n,
        groupedCoefficient μ c Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * x) := by
  classical
  let S := residualTupleDomain μ c Q0 n
  let Q := frequencySupport μ c Q0 n
  let phase : ℕ → ℝ := fun q => Real.cos (2 * Real.pi * (q : ℝ) * x)
  have hmaps : ∀ a ∈ S, tupleFrequency a ∈ Q := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hgroup :
      (∑ q ∈ Q, ∑ a ∈ S with tupleFrequency a = q,
          tupleWeight n a * phase (tupleFrequency a)) =
        ∑ a ∈ S, tupleWeight n a * phase (tupleFrequency a) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  symm
  calc
    (∑ q ∈ frequencySupport μ c Q0 n,
        groupedCoefficient μ c Q0 n q *
          Real.cos (2 * Real.pi * (q : ℝ) * x)) =
        (2 / (T61VaalerAnalytic.sampleLength n : ℝ)) *
          ∑ q ∈ Q, (∑ a ∈ S with tupleFrequency a = q, tupleWeight n a) *
            phase q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [S, phase, groupedCoefficient, frequencyFiber]
      ring
    _ = (2 / (T61VaalerAnalytic.sampleLength n : ℝ)) *
          ∑ q ∈ Q, ∑ a ∈ S with tupleFrequency a = q,
            tupleWeight n a * phase (tupleFrequency a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = (2 / (T61VaalerAnalytic.sampleLength n : ℝ)) *
          ∑ a ∈ S, tupleWeight n a * phase (tupleFrequency a) := by
      rw [hgroup]
    _ = residualTupleCosineSum μ c Q0 n x /
          (T61VaalerAnalytic.sampleLength n : ℝ) := by
      simp only [residualTupleCosineSum, S, phase]
      ring

/-- Exact T85 frequency-fiber estimate.  At a fixed lag, congruent starts
modulo `n` would force the smaller multiplier to be at least `10^n`; hence
there are at most `n` starts for each of the at most `n-1` short lags. -/
theorem frequencyFiber_card_le
    (μ c : ℝ) (Q0 n q : ℕ) (hn : 1 ≤ n) :
    (frequencyFiber μ c Q0 n q).card ≤ n * (n - 1) := by
  classical
  let target : Finset (ℕ × ℕ) := Finset.Ico 1 n ×ˢ Finset.range n
  have hmaps : ∀ a ∈ frequencyFiber μ c Q0 n q, fiberCode n a ∈ target := by
    intro a ha
    have hadomain := (Finset.mem_filter.mp ha).1
    have harange := mem_residualTupleDomain_iff.mp hadomain
    simp only [target, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨harange.2.2.1, harange.2.2.2.1⟩, Nat.mod_lt _ (by omega)⟩
  have hinj : Set.InjOn (fiberCode n) (frequencyFiber μ c Q0 n q) := by
    intro a ha b hb hcode
    have hadomain := (Finset.mem_filter.mp ha).1
    have hbdomain := (Finset.mem_filter.mp hb).1
    have hafrequency := (Finset.mem_filter.mp ha).2
    have hbfrequency := (Finset.mem_filter.mp hb).2
    have harange := mem_residualTupleDomain_iff.mp hadomain
    have hbrange := mem_residualTupleDomain_iff.mp hbdomain
    have hfrequency : tupleFrequency a = tupleFrequency b :=
      hafrequency.trans hbfrequency.symm
    change (a.2.1, a.2.2 % n) = (b.2.1, b.2.2 % n) at hcode
    have hlag : a.2.1 = b.2.1 := (Prod.mk.inj hcode).1
    have hmod : a.2.2 % n = b.2.2 % n := (Prod.mk.inj hcode).2
    have start_not_lt : ¬a.2.2 < b.2.2 := by
      intro hstart
      have hmodeq : a.2.2 ≡ b.2.2 [MOD n] := hmod
      have hdvd : n ∣ b.2.2 - a.2.2 :=
        (Nat.modEq_iff_dvd' hstart.le).mp hmodeq
      have hdiffpos : 0 < b.2.2 - a.2.2 := Nat.sub_pos_iff_lt.mpr hstart
      have hnle : n ≤ b.2.2 - a.2.2 := Nat.le_of_dvd hdiffpos hdvd
      have hpowle : 10 ^ n ≤ 10 ^ (b.2.2 - a.2.2) :=
        Nat.pow_le_pow_right (by omega) hnle
      have hrep : 0 < 10 ^ a.2.1 - 1 := by
        have hone : 1 < 10 ^ a.2.1 :=
          Nat.one_lt_pow (Nat.ne_of_gt harange.2.2.1) (by norm_num)
        omega
      have hmultiplier :
          a.1 = b.1 * 10 ^ (b.2.2 - a.2.2) := by
        have hf := hfrequency
        change a.1 * 10 ^ a.2.2 * (10 ^ a.2.1 - 1) =
          b.1 * 10 ^ b.2.2 * (10 ^ b.2.1 - 1) at hf
        rw [← hlag, show b.2.2 = a.2.2 + (b.2.2 - a.2.2) by omega,
          pow_add] at hf
        have hcancel :
            (10 ^ a.2.2 * (10 ^ a.2.1 - 1)) * a.1 =
              (10 ^ a.2.2 * (10 ^ a.2.1 - 1)) *
                (b.1 * 10 ^ (b.2.2 - a.2.2)) := by
          convert hf using 1 <;> ring
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.mul_pos (pow_pos (by norm_num) _) hrep) hcancel
      have hpowlemult : 10 ^ (b.2.2 - a.2.2) ≤ a.1 := by
        rw [hmultiplier]
        simpa using Nat.mul_le_mul_right (10 ^ (b.2.2 - a.2.2)) hbrange.1
      have hband : shortBandwidth n ≤ 10 ^ n := by
        exact Nat.div_le_self _ _
      omega
    have start_not_gt : ¬b.2.2 < a.2.2 := by
      intro hstart
      have hmodeq : b.2.2 ≡ a.2.2 [MOD n] := hmod.symm
      have hdvd : n ∣ a.2.2 - b.2.2 :=
        (Nat.modEq_iff_dvd' hstart.le).mp hmodeq
      have hdiffpos : 0 < a.2.2 - b.2.2 := Nat.sub_pos_iff_lt.mpr hstart
      have hnle : n ≤ a.2.2 - b.2.2 := Nat.le_of_dvd hdiffpos hdvd
      have hpowle : 10 ^ n ≤ 10 ^ (a.2.2 - b.2.2) :=
        Nat.pow_le_pow_right (by omega) hnle
      have hrep : 0 < 10 ^ b.2.1 - 1 := by
        have hone : 1 < 10 ^ b.2.1 :=
          Nat.one_lt_pow (Nat.ne_of_gt hbrange.2.2.1) (by norm_num)
        omega
      have hmultiplier :
          b.1 = a.1 * 10 ^ (a.2.2 - b.2.2) := by
        have hf := hfrequency.symm
        change b.1 * 10 ^ b.2.2 * (10 ^ b.2.1 - 1) =
          a.1 * 10 ^ a.2.2 * (10 ^ a.2.1 - 1) at hf
        rw [hlag, show a.2.2 = b.2.2 + (a.2.2 - b.2.2) by omega,
          pow_add] at hf
        have hcancel :
            (10 ^ b.2.2 * (10 ^ b.2.1 - 1)) * b.1 =
              (10 ^ b.2.2 * (10 ^ b.2.1 - 1)) *
                (a.1 * 10 ^ (a.2.2 - b.2.2)) := by
          convert hf using 1 <;> ring
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.mul_pos (pow_pos (by norm_num) _) hrep) hcancel
      have hpowlemult : 10 ^ (a.2.2 - b.2.2) ≤ b.1 := by
        rw [hmultiplier]
        simpa using Nat.mul_le_mul_right (10 ^ (a.2.2 - b.2.2)) harange.1
      have hband : shortBandwidth n ≤ 10 ^ n := by
        exact Nat.div_le_self _ _
      omega
    have hstart : a.2.2 = b.2.2 := by omega
    have hmultiplier : a.1 = b.1 := by
      have hf := hfrequency
      change a.1 * 10 ^ a.2.2 * (10 ^ a.2.1 - 1) =
        b.1 * 10 ^ b.2.2 * (10 ^ b.2.1 - 1) at hf
      rw [← hlag, ← hstart] at hf
      have hrep : 0 < 10 ^ a.2.1 - 1 := by
        have hone : 1 < 10 ^ a.2.1 :=
          Nat.one_lt_pow (Nat.ne_of_gt harange.2.2.1) (by norm_num)
        omega
      have hfactor : 0 < 10 ^ a.2.2 * (10 ^ a.2.1 - 1) :=
        Nat.mul_pos (pow_pos (by norm_num) _) hrep
      apply Nat.eq_of_mul_eq_mul_right hfactor
      simpa [mul_assoc] using hf
    exact Prod.ext hmultiplier (Prod.ext hlag hstart)
  calc
    (frequencyFiber μ c Q0 n q).card ≤ target.card :=
      Finset.card_le_card_of_injOn (fiberCode n) hmaps hinj
    _ = n * (n - 1) := by
      simp only [target, Finset.card_product, Nat.card_Ico, Finset.card_range]
      ring

/-- Uniform envelope for T61's literal signed coefficient on every legal
positive multiplier. -/
theorem abs_tupleWeight_lt_three_div
    {μ c : ℝ} {Q0 n : ℕ} {a : ResidualTuple}
    (ha : a ∈ residualTupleDomain μ c Q0 n) :
    |tupleWeight n a| < 3 / (shortBandwidth n : ℝ) := by
  have hrange := mem_residualTupleDomain_iff.mp ha
  have hHposNat : 0 < shortBandwidth n := by omega
  have hHpos : (0 : ℝ) < shortBandwidth n := by exact_mod_cast hHposNat
  have hhpos : (0 : ℝ) < a.1 := by exact_mod_cast hrange.1
  have hhH : (a.1 : ℝ) < shortBandwidth n := by exact_mod_cast hrange.2.1
  have hy0 : 0 < (a.1 : ℝ) / (shortBandwidth n : ℝ) := div_pos hhpos hHpos
  have hy1 : (a.1 : ℝ) / (shortBandwidth n : ℝ) < 1 :=
    (div_lt_one hHpos).mpr hhH
  have hsine :
      |Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) / Real.pi| < 1 := by
    calc
      |Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) / Real.pi| =
          |Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| /
            Real.pi := by rw [abs_div, abs_of_pos Real.pi_pos]
      _ ≤ 1 / Real.pi := by
        gcongr
        exact Real.abs_sin_le_one _
      _ < 1 := (div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hcosine :
      |2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
          Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| ≤ 2 := by
    calc
      |2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
          Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| =
          2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
            |Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (sub_nonneg.mpr hy1.le)]
      _ ≤ 2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) := by
        have hfactor :
            0 ≤ 2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) :=
          mul_nonneg (by norm_num) (sub_nonneg.mpr hy1.le)
        simpa using mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one
            (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))) hfactor
      _ ≤ 2 := by nlinarith
  rw [tupleWeight_explicit, abs_mul, abs_of_pos (inv_pos.mpr hHpos)]
  have hshape :
      |Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) / Real.pi +
          2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
            Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| < 3 :=
    (abs_add_le _ _).trans_lt (by linarith)
  calc
    (shortBandwidth n : ℝ)⁻¹ *
          |Real.sin (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ)) * Real.pi⁻¹ +
            2 * (1 - (a.1 : ℝ) / (shortBandwidth n : ℝ)) *
              Real.cos (Real.pi * (a.1 : ℝ) / (shortBandwidth n : ℝ))| <
        (shortBandwidth n : ℝ)⁻¹ * 3 := by
      apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hHpos)
      simpa [div_eq_mul_inv] using hshape
    _ = 3 / (shortBandwidth n : ℝ) := by ring

/-- Exact tuple-count envelope: `H_n-1` positive multipliers, at most `n-1`
positive short lags, and at most `L_n` starts per lag. -/
theorem residualTupleDomain_card_le (μ c : ℝ) (Q0 n : ℕ) :
    (residualTupleDomain μ c Q0 n).card ≤
      (shortBandwidth n - 1) * (n - 1) *
        T61VaalerAnalytic.sampleLength n := by
  classical
  let P : Finset (ℕ × ℕ) :=
    Finset.Ico 1 n ×ˢ Finset.range (T61VaalerAnalytic.sampleLength n)
  have hsubset : residualShortRectangle μ c Q0 n ⊆ P := by
    intro p hp
    have hrange := mem_residualShortRectangle_iff.mp hp
    have hjL : p.2 < T61VaalerAnalytic.sampleLength n :=
      hrange.2.2.1.trans_le
        (Nat.sub_le (T61VaalerAnalytic.sampleLength n) p.1)
    simp only [P, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨hrange.1, hrange.2.1⟩, hjL⟩
  have hrect : (residualShortRectangle μ c Q0 n).card ≤
      (n - 1) * T61VaalerAnalytic.sampleLength n := by
    calc
      (residualShortRectangle μ c Q0 n).card ≤ P.card :=
        Finset.card_le_card hsubset
      _ = (n - 1) * T61VaalerAnalytic.sampleLength n := by
        simp only [P, Finset.card_product, Nat.card_Ico, Finset.card_range]
  unfold residualTupleDomain positiveFejerFrequencies
  rw [Finset.card_product, Nat.card_Ico]
  simpa [shortBandwidth, mul_assoc] using
    Nat.mul_le_mul_left (shortBandwidth n - 1) hrect

/-- Fiberwise Cauchy-Schwarz with all normalizing constants exposed. -/
theorem oneScaleEnergy_le_fiber_weight
    (μ c : ℝ) (Q0 n : ℕ) (hn : 1 ≤ n) :
    oneScaleEnergy μ c Q0 n ≤
      (4 / (T61VaalerAnalytic.sampleLength n : ℝ) ^ 2) *
        (n * (n - 1) : ℕ) *
          ∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2 := by
  classical
  let S := residualTupleDomain μ c Q0 n
  let Q := frequencySupport μ c Q0 n
  let C : ℝ := (n * (n - 1) : ℕ)
  let F : ℝ := 4 / (T61VaalerAnalytic.sampleLength n : ℝ) ^ 2
  have hmaps : ∀ a ∈ S, tupleFrequency a ∈ Q := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hregroup :
      (∑ q ∈ Q, ∑ a ∈ S with tupleFrequency a = q, tupleWeight n a ^ 2) =
        ∑ a ∈ S, tupleWeight n a ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hfiber (q : ℕ) :
      (∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a) ^ 2 ≤
        C * ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a ^ 2 := by
    calc
      (∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a) ^ 2 ≤
          ((frequencyFiber μ c Q0 n q).card : ℝ) *
            ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a ^ 2 := by
        exact sq_sum_le_card_mul_sum_sq
      _ ≤ C * ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]
          exact_mod_cast frequencyFiber_card_le μ c Q0 n q hn
        · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  calc
    oneScaleEnergy μ c Q0 n =
        F * ∑ q ∈ Q,
          (∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a) ^ 2 := by
      unfold oneScaleEnergy groupedCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [F, sq_abs]
      ring
    _ ≤ F * ∑ q ∈ Q,
          C * ∑ a ∈ frequencyFiber μ c Q0 n q, tupleWeight n a ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hF
      exact Finset.sum_le_sum fun q _ => hfiber q
    _ = F * C * ∑ a ∈ S, tupleWeight n a ^ 2 := by
      rw [← Finset.mul_sum]
      simp only [frequencyFiber, S] at hregroup ⊢
      rw [hregroup]
      ring
    _ = (4 / (T61VaalerAnalytic.sampleLength n : ℝ) ^ 2) *
          (n * (n - 1) : ℕ) *
            ∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2 := by
      rfl

/-- Complete one-scale estimate with the T85 constant `36`. -/
theorem oneScaleEnergy_lt
    (μ c : ℝ) (Q0 n : ℕ) (hn : 2 ≤ n) :
    oneScaleEnergy μ c Q0 n <
      36 * (n : ℝ) ^ 3 /
        ((shortBandwidth n : ℝ) *
          (T61VaalerAnalytic.sampleLength n : ℝ)) := by
  classical
  let H := shortBandwidth n
  let L := T61VaalerAnalytic.sampleLength n
  have hn1 : 1 ≤ n := by omega
  have hpow : 10 ^ 1 ≤ 10 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 10) hn1
  have hHnat : 1 ≤ H := by
    dsimp [H, shortBandwidth, bandwidth]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    norm_num at hpow ⊢
    omega
  have hLnat : 0 < L := by
    dsimp [L, T61VaalerAnalytic.sampleLength,
      T56LagSectorAudit.t56SampleLength]
    positivity
  have hH : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hsquare (a : ResidualTuple) (ha : a ∈ residualTupleDomain μ c Q0 n) :
      tupleWeight n a ^ 2 ≤ 9 / (H : ℝ) ^ 2 := by
    have habs := (abs_tupleWeight_lt_three_div ha).le
    have hnonneg : (0 : ℝ) ≤ 3 / H := by positivity
    calc
      tupleWeight n a ^ 2 = |tupleWeight n a| ^ 2 := by rw [sq_abs]
      _ ≤ (3 / (H : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 9 / (H : ℝ) ^ 2 := by ring
  have hsum :
      (∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2) ≤
        ((residualTupleDomain μ c Q0 n).card : ℝ) *
          (9 / (H : ℝ) ^ 2) := by
    calc
      (∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2) ≤
          ∑ _a ∈ residualTupleDomain μ c Q0 n, 9 / (H : ℝ) ^ 2 :=
        Finset.sum_le_sum hsquare
      _ = ((residualTupleDomain μ c Q0 n).card : ℝ) *
          (9 / (H : ℝ) ^ 2) := by simp
  have hcard : ((residualTupleDomain μ c Q0 n).card : ℝ) ≤
      ((H - 1) * (n - 1) * L : ℕ) := by
    exact_mod_cast residualTupleDomain_card_le μ c Q0 n
  have hsum' :
      (∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2) ≤
        (((H - 1) * (n - 1) * L : ℕ) : ℝ) *
          (9 / (H : ℝ) ^ 2) := by
    exact hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hbase := oneScaleEnergy_le_fiber_weight μ c Q0 n hn1
  change oneScaleEnergy μ c Q0 n < 36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ))
  calc
    oneScaleEnergy μ c Q0 n ≤
        (4 / (L : ℝ) ^ 2) * ((n * (n - 1) : ℕ) : ℝ) *
          ∑ a ∈ residualTupleDomain μ c Q0 n, tupleWeight n a ^ 2 := by
      simpa [L] using hbase
    _ ≤ (4 / (L : ℝ) ^ 2) * ((n * (n - 1) : ℕ) : ℝ) *
          ((((H - 1) * (n - 1) * L : ℕ) : ℝ) *
            (9 / (H : ℝ) ^ 2)) := by
      gcongr
    _ < (4 / (L : ℝ) ^ 2) * ((n * n : ℕ) : ℝ) *
          ((((H : ℕ) * n * L : ℕ) : ℝ) *
            (9 / (H : ℝ) ^ 2)) := by
      have hnsub : n - 1 ≤ n := Nat.sub_le n 1
      have hHsub : H - 1 < H := Nat.sub_lt (by omega) (by omega)
      norm_cast
      gcongr <;> omega
    _ = 36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ)) := by
      field_simp [hH.ne', hL.ne']
      push_cast
      ring

/-- Elementary decimal-power comparison used to replace the exact
`H_n L_n` denominator by T85's summable `5^n` envelope. -/
theorem twentyfive_pow_le_decimalProduct (n : ℕ) (hn : 2 ≤ n) :
    25 ^ n ≤ 2 * 10 ^ (n + n / 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn2 : n = 2
      · subst n
        norm_num
      by_cases hn3 : n = 3
      · subst n
        norm_num
      let m := n - 2
      have hm : 2 ≤ m := by dsimp [m]; omega
      have hmn : m < n := by dsimp [m]; omega
      have ihm := ih m hmn hm
      have hnm : n = m + 2 := by dsimp [m]; omega
      calc
        25 ^ n = 25 ^ m * 25 ^ 2 := by rw [hnm, pow_add]
        _ ≤ (2 * 10 ^ (m + m / 2)) * 10 ^ 3 :=
          Nat.mul_le_mul ihm (by norm_num)
        _ = 2 * 10 ^ (n + n / 2) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          dsimp [m]
          omega

/-- The one-scale energy lies below the square of the explicit summable
envelope `24*n^2/5^n`. -/
theorem oneScaleEnergy_lt_square_envelope
    (μ c : ℝ) (Q0 n : ℕ) (hn : 2 ≤ n) :
    oneScaleEnergy μ c Q0 n <
      (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 := by
  let H := shortBandwidth n
  let L := T61VaalerAnalytic.sampleLength n
  have hn1 : 1 ≤ n := by omega
  have hHnat : 0 < H := by
    exact (two_le_shortBandwidth n hn1).trans_lt' (by omega)
  have hLnat : 0 < L := by
    dsimp [L, T61VaalerAnalytic.sampleLength,
      T56LagSectorAudit.t56SampleLength]
    positivity
  have htwo : 2 * H = 10 ^ n := by
    simpa [H, shortBandwidth] using
      DecimalFactorComplexity.FejerSpectralCriterion.two_mul_half_ten_pow n hn1
  have hLdef : L = 10 ^ (n / 2) := rfl
  have hprod : 2 * (H * L) = 10 ^ (n + n / 2) := by
    calc
      2 * (H * L) = (2 * H) * L := by ring
      _ = 10 ^ n * 10 ^ (n / 2) := by
        rw [htwo, hLdef]
      _ = 10 ^ (n + n / 2) := by rw [pow_add]
  have hpNat : 25 ^ n < 16 * n * H * L := by
    calc
      25 ^ n ≤ 2 * 10 ^ (n + n / 2) :=
        twentyfive_pow_le_decimalProduct n hn
      _ = 4 * (H * L) := by rw [← hprod]; ring
      _ < 16 * n * H * L := by
        have hHL : 0 < H * L := Nat.mul_pos hHnat hLnat
        nlinarith
  have hp : (25 : ℝ) ^ n < 16 * (n : ℝ) * (H : ℝ) * (L : ℝ) := by
    exact_mod_cast hpNat
  have hH : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hL : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hfive : ((5 : ℝ) ^ n) ^ 2 = (25 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  calc
    oneScaleEnergy μ c Q0 n <
        36 * (n : ℝ) ^ 3 / ((H : ℝ) * (L : ℝ)) := by
      simpa [H, L] using oneScaleEnergy_lt μ c Q0 n hn
    _ < (24 * (n : ℝ) ^ 2 / 5 ^ n) ^ 2 := by
      rw [div_pow]
      apply (div_lt_div_iff₀ (mul_pos hH hL) (sq_pos_of_pos (by positivity))).2
      rw [hfive]
      have hmul := mul_lt_mul_of_pos_left hp
        (show (0 : ℝ) < 36 * (n : ℝ) ^ 3 by positivity)
      nlinarith [hmul]

/-- Finite-dimensional Minkowski inequality in the exact finite-support form
used for the cumulative grouped coefficients. -/
theorem finite_minkowski {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (a : ι → κ → ℝ) :
    Real.sqrt (∑ q ∈ t, (∑ i ∈ s, a i q) ^ 2) ≤
      ∑ i ∈ s, Real.sqrt (∑ q ∈ t, (a i q) ^ 2) := by
  simp_rw [Finset.sum_subtype t (fun _ => Iff.rfl)]
  let v : ι → EuclideanSpace ℝ (↥t) :=
    fun i => WithLp.toLp 2 (fun q : ↥t => a i q)
  have h := norm_sum_le s v
  simpa only [v, EuclideanSpace.norm_eq, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs] using h

/-- Every scale support with `n ≤ N` is included in the declared cumulative
finite support. -/
theorem frequencySupport_subset_cumulative
    (μ c : ℝ) (Q0 : ℕ) {n N : ℕ} (hn : n ≤ N) :
    frequencySupport μ c Q0 n ⊆ cumulativeFrequencySupport μ c Q0 N := by
  intro q hq
  rw [cumulativeFrequencySupport, Finset.mem_biUnion]
  exact ⟨n, Finset.mem_range.mpr (by omega), hq⟩

/-- Extending a one-scale coefficient by zero to the cumulative support does
not change its square energy. -/
theorem sum_cumulative_groupedCoefficient_sq
    (μ c : ℝ) (Q0 : ℕ) {n N : ℕ} (hn : n ≤ N) :
    (∑ q ∈ cumulativeFrequencySupport μ c Q0 N,
        groupedCoefficient μ c Q0 n q ^ 2) = oneScaleEnergy μ c Q0 n := by
  have hsubset := frequencySupport_subset_cumulative μ c Q0 hn
  have hsum :
      (∑ q ∈ frequencySupport μ c Q0 n,
          groupedCoefficient μ c Q0 n q ^ 2) =
        ∑ q ∈ cumulativeFrequencySupport μ c Q0 N,
          groupedCoefficient μ c Q0 n q ^ 2 :=
    Finset.sum_subset hsubset (fun q _hq _hqSupport => by
      rw [groupedCoefficient_eq_zero_of_not_mem _hqSupport]
      norm_num)
  rw [oneScaleEnergy]
  simp only [sq_abs]
  exact hsum.symm

/-- Scales zero and one have no positive short lag and hence zero energy. -/
theorem oneScaleEnergy_eq_zero_of_le_one
    (μ c : ℝ) (Q0 n : ℕ) (hn : n ≤ 1) :
    oneScaleEnergy μ c Q0 n = 0 := by
  have hdomain : residualTupleDomain μ c Q0 n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hrange := mem_residualTupleDomain_iff.mp ha
    omega
  have hsupport : frequencySupport μ c Q0 n = ∅ := by
    rw [frequencySupport, hdomain]
    simp
  simp [oneScaleEnergy, hsupport]

/-- Negative antiderivative for the finite `24*n^2/5^n` telescope. -/
def envelopeTail (n : ℕ) : ℝ :=
  -(120 * (n : ℝ) ^ 2 + 60 * n + 45) / (4 * 5 ^ n)

theorem envelopeTail_step (n : ℕ) :
    24 * (n : ℝ) ^ 2 / 5 ^ n = envelopeTail (n + 1) - envelopeTail n := by
  simp only [envelopeTail]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- Exact finite constant audit replacing the informal infinite-series step. -/
theorem finite_envelope_sum_lt (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 24 * (n : ℝ) ^ 2 / 5 ^ n) < 129 / 20 := by
  by_cases hN : 2 ≤ N
  · calc
      (∑ n ∈ Finset.Icc 2 N, 24 * (n : ℝ) ^ 2 / 5 ^ n) =
          ∑ n ∈ Finset.Icc 2 N,
            (envelopeTail (n + 1) - envelopeTail n) := by
              apply Finset.sum_congr rfl
              intro n _
              exact envelopeTail_step n
      _ = envelopeTail (N + 1) - envelopeTail 2 :=
        Finset.sum_Icc_sub hN envelopeTail
      _ < 0 - envelopeTail 2 := by
        apply sub_lt_sub_right
        dsimp [envelopeTail]
        exact div_neg_of_neg_of_pos
          (neg_neg_of_pos (by positivity)) (by positivity)
      _ = 129 / 20 := by norm_num [envelopeTail]
  · have hempty : Finset.Icc 2 N = ∅ := by
      ext n
      simp
      omega
    rw [hempty]
    norm_num

/-- Minkowski, zero-extension, the one-scale envelope, and the finite
telescope give the uniform square-root bound. -/
theorem sqrt_groupedSquare_lt (μ c : ℝ) (Q0 N : ℕ) :
    Real.sqrt (groupedSquare μ c Q0 N) < 129 / 20 := by
  let Q := cumulativeFrequencySupport μ c Q0 N
  have hmink := finite_minkowski (Finset.range (N + 1)) Q
    (fun n q => groupedCoefficient μ c Q0 n q)
  have hmink' :
      Real.sqrt (groupedSquare μ c Q0 N) ≤
        ∑ n ∈ Finset.range (N + 1), Real.sqrt (oneScaleEnergy μ c Q0 n) := by
    calc
      Real.sqrt (groupedSquare μ c Q0 N) =
          Real.sqrt (∑ q ∈ Q,
            (∑ n ∈ Finset.range (N + 1),
              groupedCoefficient μ c Q0 n q) ^ 2) := by
        simp only [groupedSquare, Q, sq_abs]
      _ ≤ ∑ n ∈ Finset.range (N + 1),
          Real.sqrt (∑ q ∈ Q, groupedCoefficient μ c Q0 n q ^ 2) := hmink
      _ = ∑ n ∈ Finset.range (N + 1),
          Real.sqrt (oneScaleEnergy μ c Q0 n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [sum_cumulative_groupedCoefficient_sq μ c Q0]
        have hnrange := Finset.mem_range.mp hn
        omega
  have hsubset : Finset.Icc 2 N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    exact Finset.mem_range.mpr (by omega)
  have hrestrict :
      (∑ n ∈ Finset.range (N + 1), Real.sqrt (oneScaleEnergy μ c Q0 n)) =
        ∑ n ∈ Finset.Icc 2 N, Real.sqrt (oneScaleEnergy μ c Q0 n) := by
    symm
    apply Finset.sum_subset hsubset
    intro n hnrange hnIcc
    have hnle : n ≤ 1 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnIcc
      have hnN : n ≤ N := by
        have := Finset.mem_range.mp hnrange
        omega
      omega
    rw [oneScaleEnergy_eq_zero_of_le_one μ c Q0 n hnle]
    simp
  have henvelope :
      (∑ n ∈ Finset.Icc 2 N, Real.sqrt (oneScaleEnergy μ c Q0 n)) ≤
        ∑ n ∈ Finset.Icc 2 N, 24 * (n : ℝ) ^ 2 / 5 ^ n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hpositive : (0 : ℝ) < 24 * (n : ℝ) ^ 2 / 5 ^ n := by positivity
    exact ((Real.sqrt_lt' hpositive).mpr
      (oneScaleEnergy_lt_square_envelope μ c Q0 n hn2)).le
  calc
    Real.sqrt (groupedSquare μ c Q0 N) ≤
        ∑ n ∈ Finset.range (N + 1), Real.sqrt (oneScaleEnergy μ c Q0 n) := hmink'
    _ = ∑ n ∈ Finset.Icc 2 N, Real.sqrt (oneScaleEnergy μ c Q0 n) := hrestrict
    _ ≤ ∑ n ∈ Finset.Icc 2 N, 24 * (n : ℝ) ^ 2 / 5 ^ n := henvelope
    _ < 129 / 20 := finite_envelope_sum_lt N

/-- Final T86 bound.  This is a deterministic coefficient statement only;
it has no fixed-pi or entropy conclusion. -/
theorem groupedSquare_lt_fortyTwo
    (μ c : ℝ) (Q0 N : ℕ) (_hN : 1 ≤ N) :
    D_N μ c Q0 N < 42 := by
  have hnonneg : 0 ≤ groupedSquare μ c Q0 N := by
    unfold groupedSquare
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hroot := sqrt_groupedSquare_lt μ c Q0 N
  have hsquare : (Real.sqrt (groupedSquare μ c Q0 N)) ^ 2 <
      (129 / 20 : ℝ) ^ 2 := by
    have hsqrt := Real.sqrt_nonneg (groupedSquare μ c Q0 N)
    nlinarith [sq_nonneg (Real.sqrt (groupedSquare μ c Q0 N) - 129 / 20)]
  rw [Real.sq_sqrt hnonneg] at hsquare
  nlinarith

end DecimalFactorComplexity.T86GroupedSquareBound

#print axioms DecimalFactorComplexity.T86GroupedSquareBound.mem_residualTupleDomain_iff
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.tupleFrequency_eq
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.tupleWeight_explicit
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.mem_frequencySupport_iff
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.frequencySupport_positive
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.zero_not_mem_frequencySupport
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.groupedCoefficient_eq_zero_of_not_mem
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.groupedCoefficient_zero_scale
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.B_n_zero_frequency
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.B_n_eq_exact_fiber
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.D_N_eq_finite_grouped_square
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.sum_residualShortRectangle_eq_nested
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.residualTupleCosineSum_pi_eq_T61
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.normalized_frequency_grouping
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.frequencyFiber_card_le
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.abs_tupleWeight_lt_three_div
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.residualTupleDomain_card_le
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.oneScaleEnergy_le_fiber_weight
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.oneScaleEnergy_lt
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.twentyfive_pow_le_decimalProduct
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.oneScaleEnergy_lt_square_envelope
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.finite_minkowski
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.frequencySupport_subset_cumulative
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.sum_cumulative_groupedCoefficient_sq
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.oneScaleEnergy_eq_zero_of_le_one
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.envelopeTail_step
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.finite_envelope_sum_lt
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.sqrt_groupedSquare_lt
#print axioms DecimalFactorComplexity.T86GroupedSquareBound.groupedSquare_lt_fortyTwo
