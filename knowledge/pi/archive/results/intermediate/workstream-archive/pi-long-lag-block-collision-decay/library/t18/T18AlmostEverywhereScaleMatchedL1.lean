import TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD

/-!
# T18: the almost-everywhere scale-matched L1 sibling

Canonical local source: `problems/local/pi-long-lag-block-collision-decay.txt`
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This file concerns only a variable phase in the Lebesgue probability space
`[0,1)`. It states no conclusion for the fixed phase `Real.pi`, for the
decimal digits of pi, or for the canonical collision predicate C1.
-/

noncomputable section

set_option maxHeartbeats 800000

open Finset Set MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate Real

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T18

open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.PositiveLowerBlockDensity.T25

/-- Lebesgue measure restricted to the half-open unit interval. -/
def phaseMeasure : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

/-- The integer frequency attached to an ordered T8 pair. -/
def orderedPhaseFrequency (q : OrderedLongPair) : ℤ :=
  (10 : ℤ) ^ orderedFirst q - (10 : ℤ) ^ orderedSecond q

/-- Absolute positive frequency of an ordered pair core. -/
def orderedPhaseFrequencyNat (q : OrderedLongPair) : ℕ :=
  structuredDenominator q.2.2 q.2.1

/-- The orientation bit supplies exactly the sign of the positive structured
denominator. -/
theorem orderedPhaseFrequency_eq_sign (q : OrderedLongPair) :
    orderedPhaseFrequency q =
      if q.1 then (orderedPhaseFrequencyNat q : ℤ)
      else -(orderedPhaseFrequencyNat q : ℤ) := by
  rcases q with ⟨b, r, n⟩
  cases b <;>
    simp [orderedPhaseFrequency, orderedPhaseFrequencyNat, orderedFirst,
      orderedSecond, structuredDenominator, pow_add] <;> ring

/-- Every member of the positive-lag T8 domain has nonzero absolute phase
frequency. -/
theorem orderedPhaseFrequencyNat_pos
    {μ c : ℝ} {Q0 m N : ℕ} {q : OrderedLongPair}
    (hq : q ∈ orderedLongPairDomain μ c Q0 m N) :
    0 < orderedPhaseFrequencyNat q := by
  have hr : 0 < q.2.1 := (mem_orderedLongPairDomain_iff.mp hq).1
  unfold orderedPhaseFrequencyNat structuredDenominator
  have hpow : 1 < 10 ^ q.2.1 := Nat.one_lt_pow (Nat.ne_of_gt hr) (by norm_num)
  exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.sub_pos_of_lt hpow)

/-- Structured decimal frequencies uniquely determine the start and lag. -/
theorem structuredDenominator_injective
    {r n s d : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : structuredDenominator n r = structuredDenominator d s) :
    n = d ∧ r = s := by
  have hn := (cancellationValue_ten_reduction n r hr).1
  have hd := (cancellationValue_ten_reduction d s hs).1
  have hnd : n = d := by
    have hv := congrArg tenValuation h
    simpa [structuredDenominator, hn, hd] using hv
  subst d
  have hmul : 10 ^ n * (10 ^ r - 1) = 10 ^ n * (10 ^ s - 1) := by
    simpa [structuredDenominator] using h
  have hrep : 10 ^ r - 1 = 10 ^ s - 1 := by
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) n) hmul
  have hpowr : 1 ≤ 10 ^ r := one_le_pow₀ (by norm_num)
  have hpows : 1 ≤ 10 ^ s := one_le_pow₀ (by norm_num)
  have hpowers : 10 ^ r = 10 ^ s := by omega
  exact ⟨rfl, (Nat.pow_right_injective (by norm_num : 1 < 10)) hpowers⟩

/-- The integer phase frequency is injective on every exact restricted T8
ordered domain. -/
theorem orderedPhaseFrequency_injOn
    (μ c : ℝ) (Q0 m N : ℕ) :
    Set.InjOn orderedPhaseFrequency
      (orderedLongPairDomain μ c Q0 m N : Set OrderedLongPair) := by
  intro q hq q' hq' heq
  have hqpos := orderedPhaseFrequencyNat_pos hq
  have hq'pos := orderedPhaseFrequencyNat_pos hq'
  have hr := (mem_orderedLongPairDomain_iff.mp hq).1
  have hr' := (mem_orderedLongPairDomain_iff.mp hq').1
  rw [orderedPhaseFrequency_eq_sign, orderedPhaseFrequency_eq_sign] at heq
  rcases q with ⟨b, r, n⟩
  rcases q' with ⟨b', r', n'⟩
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_inj] at heq
    have hnat : structuredDenominator n r = structuredDenominator n' r' := by
      exact_mod_cast heq
    obtain ⟨rfl, rfl⟩ := structuredDenominator_injective hr hr' hnat
    rfl
  · simp only [Bool.false_eq_true, ↓reduceIte] at heq
    have hqposZ : (0 : ℤ) < structuredDenominator n r := by exact_mod_cast hqpos
    have hq'posZ : (0 : ℤ) < structuredDenominator n' r' := by exact_mod_cast hq'pos
    omega
  · simp only [Bool.false_eq_true, ↓reduceIte] at heq
    have hqposZ : (0 : ℤ) < structuredDenominator n r := by exact_mod_cast hqpos
    have hq'posZ : (0 : ℤ) < structuredDenominator n' r' := by exact_mod_cast hq'pos
    omega
  · simp only [↓reduceIte] at heq
    have hnat : structuredDenominator n r = structuredDenominator n' r' := by
      exact_mod_cast heq
    obtain ⟨rfl, rfl⟩ := structuredDenominator_injective hr hr' hnat
    rfl

/-- T8's exact restricted ordered-domain sum after replacing its fixed phase
`Real.pi` by the variable phase `α`. -/
def restrictedPhaseSum
    (μ c : ℝ) (Q0 m N h : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ orderedLongPairDomain μ c Q0 m N,
    Theory.PiDigits.T27.phase (h : ℤ) ((orderedPhaseFrequency q : ℝ) * α)

/-- The requested inclusive L1 frequency sum, with `1 ≤ h ≤ 10^m`. -/
def restrictedPhaseL1
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖restrictedPhaseSum μ c Q0 m N h α‖

/-- Squared spectral energy over the same inclusive frequency range. -/
def restrictedPhaseEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2

/-- The scale `N + N^2 10^(-t*m)` appearing in the sibling predicate. -/
def scaleTerm (t : ℝ) (m N : ℕ) : ℝ :=
  (N : ℝ) + (N : ℝ) ^ 2 * (10 : ℝ) ^ (-t * (m : ℝ))

/-- The exact exceptional event used by `Tail(t)`. -/
def tailBadSet
    (t : ℝ) (Q0 m N : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 ∩
    {α | 2 * (decimalFrequency m : ℝ) * scaleTerm t m N <
      restrictedPhaseL1 8 1 Q0 m N α}

/-- Phases belonging to infinitely many positive-integer `Tail(t)` events.
Pairs `(m,N)` are encoded as `(m+1,N+1)`, so no zero scale is included. -/
def tailExceptionalSet (t : ℝ) (Q0 : ℕ) : Set ℝ :=
  {α | {p : ℕ × ℕ | α ∈ tailBadSet t Q0 (p.1 + 1) (p.2 + 1)}.Infinite}

/-- The restricted volume is a probability measure. -/
theorem phaseMeasure_univ : phaseMeasure Set.univ = 1 := by
  simp [phaseMeasure]

instance phaseMeasure_isFinite : IsFiniteMeasure phaseMeasure := by
  rw [phaseMeasure]
  infer_instance

/-- Orthogonality of integer characters on the explicit half-open Lebesgue
probability interval. -/
theorem integral_phaseMeasure_phase (z : ℤ) :
    (∫ α, Theory.PiDigits.T27.phase z α ∂phaseMeasure) =
      if z = 0 then 1 else 0 := by
  have hinterval :
      (∫ α in (0 : ℝ)..1, Theory.PiDigits.T27.phase z α) =
        if z = 0 then 1 else 0 := by
    by_cases hz : z = 0
    · subst z
      simp [Theory.PiDigits.T27.phase]
    · rw [if_neg hz]
      let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)
      have hc : c ≠ 0 := by
        dsimp [c]
        exact mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (by norm_num)
              (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero)
          (Int.cast_ne_zero.mpr hz)
      change (∫ α in (0 : ℝ)..1, Complex.exp (c * α)) = 0
      rw [integral_exp_mul_complex hc]
      have hc_one : c * (1 : ℝ) =
          (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        dsimp [c]
        ring
      rw [hc_one, Complex.exp_int_mul_two_pi_mul_I]
      simp
  rw [phaseMeasure, ← hinterval, intervalIntegral.integral_of_le (by norm_num)]
  exact MeasureTheory.integral_Ico_eq_integral_Ioc
    (μ := volume) (f := Theory.PiDigits.T27.phase z)

/-- Product of two possibly different decimal characters as one integer
character. -/
theorem conj_phase_mul_phase
    (h k x y : ℤ) (α : ℝ) :
    conj (Theory.PiDigits.T27.phase h ((x : ℝ) * α)) *
        Theory.PiDigits.T27.phase k ((y : ℝ) * α) =
      Theory.PiDigits.T27.phase (k * y - h * x) α := by
  unfold Theory.PiDigits.T27.phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, Int.cast_sub, Int.cast_mul]
  push_cast
  ring

/-- Integrated character products are exactly their integer resonance
indicator. -/
theorem integral_conj_phase_mul_phase
    (h k x y : ℤ) :
    (∫ α, conj (Theory.PiDigits.T27.phase h ((x : ℝ) * α)) *
        Theory.PiDigits.T27.phase k ((y : ℝ) * α) ∂phaseMeasure) =
      if h * x = k * y then 1 else 0 := by
  simp_rw [conj_phase_mul_phase]
  rw [integral_phaseMeasure_phase]
  by_cases heq : h * x = k * y
  · simp [heq]
  · simp [heq, sub_ne_zero.mpr (Ne.symm heq)]

/-- The variable-phase T8 sum is continuous. -/
theorem continuous_restrictedPhaseSum
    (μ c : ℝ) (Q0 m N h : ℕ) :
    Continuous (restrictedPhaseSum μ c Q0 m N h) := by
  unfold restrictedPhaseSum Theory.PiDigits.T27.phase orderedPhaseFrequency
  fun_prop

/-- The inclusive L1 frequency sum is continuous. -/
theorem continuous_restrictedPhaseL1
    (μ c : ℝ) (Q0 m N : ℕ) :
    Continuous (restrictedPhaseL1 μ c Q0 m N) := by
  unfold restrictedPhaseL1
  apply continuous_finsetSum
  intro h _hh
  exact (continuous_restrictedPhaseSum μ c Q0 m N h).norm

/-- The squared spectral energy is continuous. -/
theorem continuous_restrictedPhaseEnergy
    (μ c : ℝ) (Q0 m N : ℕ) :
    Continuous (restrictedPhaseEnergy μ c Q0 m N) := by
  unfold restrictedPhaseEnergy
  apply continuous_finsetSum
  intro h _hh
  exact (continuous_restrictedPhaseSum μ c Q0 m N h).norm.pow 2

/-- The inclusive frequency interval has exactly `10^m` elements. -/
theorem decimalFrequencyDomain_card (m : ℕ) :
    (Finset.Icc 1 (decimalFrequency m)).card = decimalFrequency m := by
  simp [decimalFrequency]

/-- Pointwise Cauchy-Schwarz from the requested L1 sum to squared energy. -/
theorem restrictedPhaseL1_sq_le
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    restrictedPhaseL1 μ c Q0 m N α ^ 2 ≤
      (decimalFrequency m : ℝ) * restrictedPhaseEnergy μ c Q0 m N α := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.Icc 1 (decimalFrequency m))
    (f := fun h => ‖restrictedPhaseSum μ c Q0 m N h α‖)
  simpa [restrictedPhaseL1, restrictedPhaseEnergy, decimalFrequencyDomain_card] using h

/-- Pointwise double-character expansion of one squared spectral norm. -/
theorem restrictedPhaseSum_norm_sq_expansion
    (μ c : ℝ) (Q0 m N h : ℕ) (α : ℝ) :
    ((‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ orderedLongPairDomain μ c Q0 m N,
        ∑ r ∈ orderedLongPairDomain μ c Q0 m N,
          Theory.PiDigits.T27.phase
            ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  unfold restrictedPhaseSum
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [conj_phase_mul_phase]
  congr 1
  ring

/-- Exact second moment of every positive-frequency restricted T8 sum. -/
theorem integral_restrictedPhaseSum_norm_sq
    (μ c : ℝ) (Q0 m N h : ℕ) (hh : 1 ≤ h) :
    (∫ α, ‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2 ∂phaseMeasure) =
      (orderedLongPairDomain μ c Q0 m N).card := by
  let Q := orderedLongPairDomain μ c Q0 m N
  have hcomplex :
      (∫ α, ((‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2 : ℝ) : ℂ)
        ∂phaseMeasure) = ((orderedLongPairDomain μ c Q0 m N).card : ℂ) := by
    rw [integral_congr_ae (ae_of_all phaseMeasure fun α =>
        restrictedPhaseSum_norm_sq_expansion μ c Q0 m N h α)]
    rw [MeasureTheory.integral_finsetSum]
    · calc
        (∑ q ∈ orderedLongPairDomain μ c Q0 m N,
            ∫ α, ∑ r ∈ orderedLongPairDomain μ c Q0 m N,
              Theory.PiDigits.T27.phase
                ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α
              ∂phaseMeasure) =
            ∑ _q ∈ orderedLongPairDomain μ c Q0 m N, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [MeasureTheory.integral_finsetSum]
          · calc
              (∑ r ∈ orderedLongPairDomain μ c Q0 m N,
                  ∫ α, Theory.PiDigits.T27.phase
                    ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α
                    ∂phaseMeasure) =
                  ∑ r ∈ orderedLongPairDomain μ c Q0 m N,
                    if q = r then (1 : ℂ) else 0 := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [integral_phaseMeasure_phase]
                by_cases hqr : q = r
                · subst r
                  simp
                · have hfreq : orderedPhaseFrequency q ≠ orderedPhaseFrequency r := by
                    intro heq
                    exact hqr (orderedPhaseFrequency_injOn μ c Q0 m N hq hr heq)
                  have hhNat : h ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hh)
                  simp [hqr, mul_eq_zero, hhNat, sub_eq_zero, Ne.symm hfreq]
              _ = 1 := by simp [hq]
          · intro r hr
            rw [phaseMeasure]
            exact ((by
              unfold Theory.PiDigits.T27.phase
              fun_prop : Continuous (fun α : ℝ =>
                Theory.PiDigits.T27.phase
                  ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α)).integrableOn_Icc).mono_set
                    Set.Ico_subset_Icc_self
        _ = ((orderedLongPairDomain μ c Q0 m N).card : ℂ) := by simp
    · intro q hq
      apply integrable_finsetSum
      intro r hr
      rw [phaseMeasure]
      exact ((by
        unfold Theory.PiDigits.T27.phase
        fun_prop : Continuous (fun α : ℝ =>
          Theory.PiDigits.T27.phase
            ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α)).integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self
  rw [integral_complex_ofReal] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- Exact mean of the squared energy over all inclusive frequencies. -/
theorem integral_restrictedPhaseEnergy
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∫ α, restrictedPhaseEnergy μ c Q0 m N α ∂phaseMeasure) =
      (decimalFrequency m : ℝ) *
        (orderedLongPairDomain μ c Q0 m N).card := by
  unfold restrictedPhaseEnergy
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
          ∫ α, ‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2 ∂phaseMeasure) =
          ∑ _h ∈ Finset.Icc 1 (decimalFrequency m),
            ((orderedLongPairDomain μ c Q0 m N).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact integral_restrictedPhaseSum_norm_sq μ c Q0 m N h
          (Finset.mem_Icc.mp hh).1
      _ = (decimalFrequency m : ℝ) *
          (orderedLongPairDomain μ c Q0 m N).card := by
        rw [Finset.sum_const, nsmul_eq_mul, decimalFrequencyDomain_card]
  · intro h hh
    rw [phaseMeasure]
    exact ((continuous_restrictedPhaseSum μ c Q0 m N h).norm.pow 2).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self

/-- Positive inclusive frequency pairs satisfying one resonance equation. -/
def resonanceDomain (H d e : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter fun p => p.1 * d = p.2 * e

/-- Sharp finite resonance count in multiplication-only form. It is equivalent
to `#resonances ≤ H*gcd(d,e)/max(d,e)` whenever `d,e` are positive. -/
theorem resonanceDomain_card_mul_max_le (H d e : ℕ) :
    (resonanceDomain H d e).card * Nat.max d e ≤ H * Nat.gcd d e := by
  classical
  by_cases hd : d = 0
  · subst d
    by_cases he : e = 0
    · subst e
      simp
    · have hempty : resonanceDomain H 0 e = ∅ := by
        ext p
        constructor
        · intro hp
          rw [resonanceDomain] at hp
          have hm := Finset.mem_filter.mp hp
          have hp2 := Finset.mem_Icc.mp (Finset.mem_product.mp hm.1).2
          have hrel := hm.2
          simp only [mul_zero] at hrel
          have hepos : 0 < e := Nat.pos_of_ne_zero he
          have hprod : 0 < p.2 * e := Nat.mul_pos hp2.1 hepos
          omega
        · intro hp
          simp at hp
      simp [hempty]
  · by_cases he : e = 0
    · subst e
      have hempty : resonanceDomain H d 0 = ∅ := by
        ext p
        constructor
        · intro hp
          rw [resonanceDomain] at hp
          have hm := Finset.mem_filter.mp hp
          have hp1 := Finset.mem_Icc.mp (Finset.mem_product.mp hm.1).1
          have hrel := hm.2
          simp only [mul_zero] at hrel
          have hprod : 0 < p.1 * d := Nat.mul_pos hp1.1 (Nat.pos_of_ne_zero hd)
          omega
        · intro hp
          simp at hp
      simp [hempty]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hepos : 0 < e := Nat.pos_of_ne_zero he
      let g := Nat.gcd d e
      have hgpos : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
      by_cases hde : d ≤ e
      · let f : ℕ × ℕ → ℕ := fun p => g * p.1 / e
        have hdiv (p : ℕ × ℕ) (hp : p ∈ resonanceDomain H d e) :
            e ∣ g * p.1 := by
          have hrel := (Finset.mem_filter.mp hp).2
          have hed : e ∣ d * p.1 := by
            refine ⟨p.2, ?_⟩
            calc
              d * p.1 = p.1 * d := Nat.mul_comm _ _
              _ = p.2 * e := hrel
              _ = e * p.2 := Nat.mul_comm _ _
          have hx := dvd_gcd_mul_of_dvd_mul hed
          change e ∣ Nat.gcd e d * p.1 at hx
          simpa only [g, Nat.gcd_comm e d] using hx
        have hfmem (p : ℕ × ℕ) (hp : p ∈ resonanceDomain H d e) :
            f p ∈ Finset.Icc 1 (H * g / e) := by
          have hm := (Finset.mem_filter.mp hp).1
          have hp1 := (Finset.mem_product.mp hm).1
          have hp1range := Finset.mem_Icc.mp hp1
          have hdivp := hdiv p hp
          have hge : e ≤ g * p.1 := Nat.le_of_dvd (Nat.mul_pos hgpos hp1range.1) hdivp
          have hpos : 0 < f p := Nat.div_pos hge hepos
          have hle : g * p.1 ≤ H * g := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left g hp1range.2
          exact Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right hle⟩
        have hfinj : Set.InjOn f (resonanceDomain H d e : Set (ℕ × ℕ)) := by
          intro p hp q hq hpq
          have hpdiv := hdiv p hp
          have hqdiv := hdiv q hq
          have hmulP : e * f p = g * p.1 := by
            exact Nat.mul_div_cancel' hpdiv
          have hmulQ : e * f q = g * q.1 := by
            exact Nat.mul_div_cancel' hqdiv
          have hfirst : p.1 = q.1 := by
            apply Nat.eq_of_mul_eq_mul_left hgpos
            rw [← hmulP, ← hmulQ, hpq]
          have hrelP := (Finset.mem_filter.mp hp).2
          have hrelQ := (Finset.mem_filter.mp hq).2
          have hsecond : p.2 = q.2 := by
            apply Nat.eq_of_mul_eq_mul_right hepos
            calc
              p.2 * e = p.1 * d := hrelP.symm
              _ = q.1 * d := by rw [hfirst]
              _ = q.2 * e := hrelQ
          exact Prod.ext hfirst hsecond
        have himage : (resonanceDomain H d e).image f ⊆
            Finset.Icc 1 (H * g / e) := by
          intro x hx
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
          exact hfmem p hp
        have hcard : (resonanceDomain H d e).card ≤ H * g / e := by
          calc
            (resonanceDomain H d e).card =
                ((resonanceDomain H d e).image f).card :=
              (Finset.card_image_of_injOn hfinj).symm
            _ ≤ (Finset.Icc 1 (H * g / e)).card := Finset.card_le_card himage
            _ = H * g / e := by simp
        simp only [Nat.max_eq_right hde]
        calc
          (resonanceDomain H d e).card * e ≤ (H * g / e) * e :=
            Nat.mul_le_mul_right e hcard
          _ ≤ H * g := Nat.div_mul_le_self _ _
          _ = H * Nat.gcd d e := by rfl
      · have hed : e ≤ d := le_of_not_ge hde
        let f : ℕ × ℕ → ℕ := fun p => g * p.2 / d
        have hdiv (p : ℕ × ℕ) (hp : p ∈ resonanceDomain H d e) :
            d ∣ g * p.2 := by
          have hrel := (Finset.mem_filter.mp hp).2
          have hde' : d ∣ e * p.2 := by
            refine ⟨p.1, ?_⟩
            calc
              e * p.2 = p.2 * e := Nat.mul_comm _ _
              _ = p.1 * d := hrel.symm
              _ = d * p.1 := Nat.mul_comm _ _
          have hx := dvd_gcd_mul_of_dvd_mul hde'
          change d ∣ Nat.gcd d e * p.2 at hx
          simpa only [g] using hx
        have hfmem (p : ℕ × ℕ) (hp : p ∈ resonanceDomain H d e) :
            f p ∈ Finset.Icc 1 (H * g / d) := by
          have hm := (Finset.mem_filter.mp hp).1
          have hp2 := (Finset.mem_product.mp hm).2
          have hp2range := Finset.mem_Icc.mp hp2
          have hdivp := hdiv p hp
          have hge : d ≤ g * p.2 := Nat.le_of_dvd (Nat.mul_pos hgpos hp2range.1) hdivp
          have hpos : 0 < f p := Nat.div_pos hge hdpos
          have hle : g * p.2 ≤ H * g := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left g hp2range.2
          exact Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right hle⟩
        have hfinj : Set.InjOn f (resonanceDomain H d e : Set (ℕ × ℕ)) := by
          intro p hp q hq hpq
          have hpdiv := hdiv p hp
          have hqdiv := hdiv q hq
          have hmulP : d * f p = g * p.2 := Nat.mul_div_cancel' hpdiv
          have hmulQ : d * f q = g * q.2 := Nat.mul_div_cancel' hqdiv
          have hsecond : p.2 = q.2 := by
            apply Nat.eq_of_mul_eq_mul_left hgpos
            rw [← hmulP, ← hmulQ, hpq]
          have hrelP := (Finset.mem_filter.mp hp).2
          have hrelQ := (Finset.mem_filter.mp hq).2
          have hfirst : p.1 = q.1 := by
            apply Nat.eq_of_mul_eq_mul_right hdpos
            calc
              p.1 * d = p.2 * e := hrelP
              _ = q.2 * e := by rw [hsecond]
              _ = q.1 * d := hrelQ.symm
          exact Prod.ext hfirst hsecond
        have himage : (resonanceDomain H d e).image f ⊆
            Finset.Icc 1 (H * g / d) := by
          intro x hx
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
          exact hfmem p hp
        have hcard : (resonanceDomain H d e).card ≤ H * g / d := by
          calc
            (resonanceDomain H d e).card =
                ((resonanceDomain H d e).image f).card :=
              (Finset.card_image_of_injOn hfinj).symm
            _ ≤ (Finset.Icc 1 (H * g / d)).card := Finset.card_le_card himage
            _ = H * g / d := by simp
        simp only [Nat.max_eq_left hed]
        calc
          (resonanceDomain H d e).card * d ≤ (H * g / d) * d :=
            Nat.mul_le_mul_right d hcard
          _ ≤ H * g := Nat.div_mul_le_self _ _
          _ = H * Nat.gcd d e := by rfl

/-- Ordered pairs of distinct restricted T8 pairs whose integer phase
difference is positive. -/
def restrictedPositiveDifferenceDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset (OrderedLongPair × OrderedLongPair) :=
  ((orderedLongPairDomain μ c Q0 m N) ×ˢ
      (orderedLongPairDomain μ c Q0 m N)).filter fun p =>
    orderedPhaseFrequency p.2 < orderedPhaseFrequency p.1

/-- Positive natural difference represented by a restricted pair pair. -/
def restrictedPositiveDifferenceValue
    (p : OrderedLongPair × OrderedLongPair) : ℕ :=
  (orderedPhaseFrequency p.1 - orderedPhaseFrequency p.2).toNat

/-- Membership exposes both exact T8 restrictions and strict positivity. -/
theorem mem_restrictedPositiveDifferenceDomain_iff
    {μ c : ℝ} {Q0 m N : ℕ} {p : OrderedLongPair × OrderedLongPair} :
    p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N ↔
      p.1 ∈ orderedLongPairDomain μ c Q0 m N ∧
      p.2 ∈ orderedLongPairDomain μ c Q0 m N ∧
      orderedPhaseFrequency p.2 < orderedPhaseFrequency p.1 := by
  simp [restrictedPositiveDifferenceDomain, and_assoc]

/-- Natural distance between represented endpoints is exactly the core lag. -/
theorem ordered_coordinates_dist (q : OrderedLongPair) :
    Nat.dist (orderedFirst q) (orderedSecond q) = q.2.1 := by
  rcases q with ⟨b, r, n⟩
  cases b
  · simp only [orderedFirst, orderedSecond, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.dist_eq_sub_of_le (Nat.le_add_right n r)]
    omega
  · simp only [orderedFirst, orderedSecond, ↓reduceIte]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_add_right n r)]
    omega

/-- First endpoint as an element of `Fin N`, using exact T8 membership. -/
def restrictedFirstFin
    {μ c : ℝ} {Q0 m N : ℕ}
    (q : OrderedLongPair) (hq : q ∈ orderedLongPairDomain μ c Q0 m N) : Fin N :=
  ⟨orderedFirst q, (ordered_coordinates_lt hq).1⟩

/-- Second endpoint as an element of `Fin N`, using exact T8 membership. -/
def restrictedSecondFin
    {μ c : ℝ} {Q0 m N : ℕ}
    (q : OrderedLongPair) (hq : q ∈ orderedLongPairDomain μ c Q0 m N) : Fin N :=
  ⟨orderedSecond q, (ordered_coordinates_lt hq).2⟩

/-- Four-token vector associated to a positive difference
`lambda(q)-lambda(r)`. Its coordinate order is `(q.first,r.second,
q.second,r.first)`, matching T16's `(+,+,-,-)` signs and lag audit. -/
def restrictedDifferenceVector
    {μ c : ℝ} {Q0 m N : ℕ}
    (p : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N)) :
    BoundedExponentVector 4 N := by
  have hp := mem_restrictedPositiveDifferenceDomain_iff.mp p.property
  exact ![restrictedFirstFin p.1.1 hp.1,
    restrictedSecondFin p.1.2 hp.2.1,
    restrictedSecondFin p.1.1 hp.1,
    restrictedFirstFin p.1.2 hp.2.1]

/-- The T16 signed value of the injected vector is the original positive
integer phase difference. -/
theorem restrictedDifferenceVector_signedValue
    {μ c : ℝ} {Q0 m N : ℕ}
    (p : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N)) :
    signedDecimalValue fourTokenSign (exponentNat (restrictedDifferenceVector p)) =
      orderedPhaseFrequency p.1.1 - orderedPhaseFrequency p.1.2 := by
  rcases p with ⟨⟨q, r⟩, hp⟩
  simp only [restrictedDifferenceVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  simp [signedDecimalValue, exponentNat, fourTokenSign, orderedPhaseFrequency,
    restrictedFirstFin, restrictedSecondFin, Fin.sum_univ_succ]
  ring

/-- Natural T16 value is exactly the restricted positive difference value. -/
theorem restrictedDifferenceVector_value
    {μ c : ℝ} {Q0 m N : ℕ}
    (p : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N)) :
    longDifferenceValue (restrictedDifferenceVector p) =
      restrictedPositiveDifferenceValue p.1 := by
  simp only [longDifferenceValue, signedDecimalNatValue,
    restrictedPositiveDifferenceValue]
  rw [restrictedDifferenceVector_signedValue]

/-- Every restricted positive pair difference lands in T16's exact weak-lag
four-token domain. -/
theorem restrictedDifferenceVector_mem_longDifferenceDomain
    {μ c : ℝ} {Q0 m N : ℕ}
    (p : ↥(restrictedPositiveDifferenceDomain μ c Q0 m N)) :
    restrictedDifferenceVector p ∈ longDifferenceDomain m N := by
  have hp := mem_restrictedPositiveDifferenceDomain_iff.mp p.property
  apply mem_longDifferenceDomain_iff.mpr
  refine ⟨fun i => (restrictedDifferenceVector p i).2, ?_, ?_, ?_⟩
  · simpa [restrictedDifferenceVector, restrictedFirstFin, restrictedSecondFin,
      ordered_coordinates_dist] using
      (mem_orderedLongPairDomain_iff.mp hp.1).2.1
  · simpa [restrictedDifferenceVector, restrictedFirstFin, restrictedSecondFin,
      ordered_coordinates_dist] using
      (mem_orderedLongPairDomain_iff.mp hp.2.1).2.1
  · rw [restrictedDifferenceVector_signedValue]
    exact sub_pos.mpr hp.2.2

/-- The four endpoints recover both restricted ordered pairs, so the vector
injection loses no multiplicity. -/
theorem restrictedDifferenceVector_injective
    {μ c : ℝ} {Q0 m N : ℕ} :
    Function.Injective (restrictedDifferenceVector
      (μ := μ) (c := c) (Q0 := Q0) (m := m) (N := N)) := by
  intro p q hpq
  have pp := mem_restrictedPositiveDifferenceDomain_iff.mp p.property
  have qp := mem_restrictedPositiveDifferenceDomain_iff.mp q.property
  apply Subtype.ext
  apply Prod.ext
  · apply orderedPhaseFrequency_injOn μ c Q0 m N pp.1 qp.1
    have h0 := congrArg (fun a => (a 0).1) hpq
    have h2 := congrArg (fun a => (a 2).1) hpq
    simp [restrictedDifferenceVector, restrictedFirstFin, restrictedSecondFin,
      orderedPhaseFrequency] at h0 h2 ⊢
    rw [h0, h2]
  · apply orderedPhaseFrequency_injOn μ c Q0 m N pp.2.1 qp.2.1
    have h1 := congrArg (fun a => (a 1).1) hpq
    have h3 := congrArg (fun a => (a 3).1) hpq
    simp [restrictedDifferenceVector, restrictedFirstFin, restrictedSecondFin,
      orderedPhaseFrequency] at h1 h3 ⊢
    rw [h3, h1]

/-- Weighted ordinary-GCD sum over all pairs of restricted positive
differences. Attached domains retain the exact T8 membership proofs needed by
the endpoint injection. -/
def restrictedDifferenceWeightedGCD
    (μ c : ℝ) (Q0 m N : ℕ) : ℚ :=
  ∑ p ∈ (restrictedPositiveDifferenceDomain μ c Q0 m N).attach ×ˢ
      (restrictedPositiveDifferenceDomain μ c Q0 m N).attach,
    gcdKernel (restrictedPositiveDifferenceValue p.1.1)
      (restrictedPositiveDifferenceValue p.2.1)

/-- T16's exact finite weighted-GCD theorem dominates the restricted T8
difference sum by an injective, value-preserving map. -/
theorem restrictedDifferenceWeightedGCD_le_T16
    (μ c : ℝ) (Q0 m N : ℕ) :
    restrictedDifferenceWeightedGCD μ c Q0 m N ≤
      longDifferenceWitnessWeightedGCD m N := by
  classical
  let D := restrictedPositiveDifferenceDomain μ c Q0 m N
  let S := D.attach ×ˢ D.attach
  let L := longDifferenceDomain m N ×ˢ longDifferenceDomain m N
  let encode : (↥D × ↥D) →
      (BoundedExponentVector 4 N × BoundedExponentVector 4 N) := fun p =>
    (restrictedDifferenceVector p.1, restrictedDifferenceVector p.2)
  have hencode : Function.Injective encode := by
    intro p q hpq
    apply Prod.ext
    · exact restrictedDifferenceVector_injective (congrArg Prod.fst hpq)
    · exact restrictedDifferenceVector_injective (congrArg Prod.snd hpq)
  have himage : S.image encode ⊆ L := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hm := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr
      ⟨restrictedDifferenceVector_mem_longDifferenceDomain p.1,
        restrictedDifferenceVector_mem_longDifferenceDomain p.2⟩
  have hsumImage :
      (∑ p ∈ S,
          gcdKernel (restrictedPositiveDifferenceValue p.1.1)
            (restrictedPositiveDifferenceValue p.2.1)) =
        ∑ a ∈ S.image encode,
          gcdKernel (longDifferenceValue a.1) (longDifferenceValue a.2) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hencode h)]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [encode]
    rw [restrictedDifferenceVector_value, restrictedDifferenceVector_value]
  rw [restrictedDifferenceWeightedGCD, longDifferenceWitnessWeightedGCD]
  change (∑ p ∈ S,
      gcdKernel (restrictedPositiveDifferenceValue p.1.1)
        (restrictedPositiveDifferenceValue p.2.1)) ≤
    ∑ a ∈ L, gcdKernel (longDifferenceValue a.1) (longDifferenceValue a.2)
  rw [hsumImage]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage
    (fun a _ha _hnot => gcdKernel_nonneg _ _)

/-- Explicit T16 bound for the restricted difference sum. -/
theorem restrictedDifferenceWeightedGCD_le
    (μ c : ℝ) (Q0 m N : ℕ) :
    restrictedDifferenceWeightedGCD μ c Q0 m N ≤
      574913232 * (N : ℚ) ^ 4 := by
  calc
    restrictedDifferenceWeightedGCD μ c Q0 m N ≤
        longDifferenceWitnessWeightedGCD m N :=
      restrictedDifferenceWeightedGCD_le_T16 μ c Q0 m N
    _ = longDifferenceMultiplicityWeightedGCD m N :=
      (longDifferenceMultiplicityWeightedGCD_eq_witness m N).symm
    _ ≤ 574913232 * (N : ℚ) ^ 4 :=
      longDifferenceMultiplicityWeightedGCD_le m N

/-- Ordered off-diagonal pairs in the exact restricted T8 domain. -/
def restrictedOffDiagonalDomain
    (μ c : ℝ) (Q0 m N : ℕ) : Finset (OrderedLongPair × OrderedLongPair) :=
  ((orderedLongPairDomain μ c Q0 m N) ×ˢ
      (orderedLongPairDomain μ c Q0 m N)).filter fun p => p.1 ≠ p.2

/-- A positive difference and a Boolean orientation recover both orders of an
off-diagonal pair. -/
def orientPositiveDifference
    (p : Bool × (OrderedLongPair × OrderedLongPair)) :
    OrderedLongPair × OrderedLongPair :=
  if p.1 then p.2.swap else p.2

/-- The off-diagonal domain is exactly two orientations of every positive
difference. -/
theorem restrictedOffDiagonalDomain_eq_image_orient
    (μ c : ℝ) (Q0 m N : ℕ) :
    restrictedOffDiagonalDomain μ c Q0 m N =
      ((Finset.univ : Finset Bool).product
        (restrictedPositiveDifferenceDomain μ c Q0 m N)).image
          orientPositiveDifference := by
  classical
  ext p
  constructor
  · intro hp
    have hm := Finset.mem_filter.mp hp
    have hq := Finset.mem_product.mp hm.1
    have hfreq : orderedPhaseFrequency p.1 ≠ orderedPhaseFrequency p.2 := by
      intro heq
      exact hm.2 (orderedPhaseFrequency_injOn μ c Q0 m N hq.1 hq.2 heq)
    rcases lt_or_gt_of_ne hfreq with hlt | hgt
    · apply Finset.mem_image.mpr
      refine ⟨(true, p.swap), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply mem_restrictedPositiveDifferenceDomain_iff.mpr
        exact ⟨hq.2, hq.1, hlt⟩
      · simp [orientPositiveDifference]
    · apply Finset.mem_image.mpr
      refine ⟨(false, p), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_univ _,
          mem_restrictedPositiveDifferenceDomain_iff.mpr ⟨hq.1, hq.2, hgt⟩⟩
      · simp [orientPositiveDifference]
  · intro hp
    obtain ⟨⟨b, p⟩, hb, rfl⟩ := Finset.mem_image.mp hp
    have hm := Finset.mem_product.mp hb
    have hd := mem_restrictedPositiveDifferenceDomain_iff.mp hm.2
    apply Finset.mem_filter.mpr
    cases b
    · exact ⟨Finset.mem_product.mpr ⟨hd.1, hd.2.1⟩,
        fun heq => (ne_of_lt hd.2.2) (congrArg orderedPhaseFrequency heq).symm⟩
    · exact ⟨Finset.mem_product.mpr ⟨hd.2.1, hd.1⟩,
        fun heq => (ne_of_lt hd.2.2) (congrArg orderedPhaseFrequency heq)⟩

/-- The orientation map is injective on its exact finite source. -/
theorem orientPositiveDifference_injOn
    (μ c : ℝ) (Q0 m N : ℕ) :
    Set.InjOn orientPositiveDifference
      (((Finset.univ : Finset Bool).product
        (restrictedPositiveDifferenceDomain μ c Q0 m N)) :
          Set (Bool × (OrderedLongPair × OrderedLongPair))) := by
  intro p hp q hq hpq
  have pp := mem_restrictedPositiveDifferenceDomain_iff.mp
    (Finset.mem_product.mp hp).2
  have qp := mem_restrictedPositiveDifferenceDomain_iff.mp
    (Finset.mem_product.mp hq).2
  rcases p with ⟨bp, p⟩
  rcases q with ⟨bq, q⟩
  cases bp <;> cases bq
  · have heq : p = q := by simpa [orientPositiveDifference] using hpq
    simp [heq]
  · have heq : p = q.swap := by simpa [orientPositiveDifference] using hpq
    have hreverse : orderedPhaseFrequency q.1 < orderedPhaseFrequency q.2 := by
      simpa [heq] using pp.2.2
    exact (not_lt_of_ge qp.2.2.le hreverse).elim
  · have heq : p.swap = q := by simpa [orientPositiveDifference] using hpq
    have hreverse : orderedPhaseFrequency p.1 < orderedPhaseFrequency p.2 := by
      simpa [← heq] using qp.2.2
    exact (not_lt_of_ge pp.2.2.le hreverse).elim
  · have heq : p.swap = q.swap := by simpa [orientPositiveDifference] using hpq
    have hpq' : p = q := Prod.swap_injective heq
    simp [hpq']

/-- Summation over off-diagonal ordered pairs is summation over the two
orientations of positive differences. -/
theorem sum_restrictedOffDiagonalDomain_eq_orient
    (μ c : ℝ) (Q0 m N : ℕ)
    (f : OrderedLongPair × OrderedLongPair → ℂ) :
    (∑ p ∈ restrictedOffDiagonalDomain μ c Q0 m N, f p) =
      ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        (f p + f p.swap) := by
  classical
  rw [restrictedOffDiagonalDomain_eq_image_orient]
  rw [Finset.sum_image (fun a ha b hb h =>
    orientPositiveDifference_injOn μ c Q0 m N ha hb h)]
  have hprod :
      (∑ x ∈ (Finset.univ : Finset Bool).product
          (restrictedPositiveDifferenceDomain μ c Q0 m N),
        f (orientPositiveDifference x)) =
        ∑ b ∈ (Finset.univ : Finset Bool),
          ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
            f (orientPositiveDifference (b, p)) := by
    simpa using (Finset.sum_product
      (Finset.univ : Finset Bool)
      (restrictedPositiveDifferenceDomain μ c Q0 m N)
      (fun x => f (orientPositiveDifference x)))
  rw [hprod]
  simp [orientPositiveDifference, add_comm, ← Finset.sum_add_distrib]

/-- Cast of a positive difference recovers the original integer difference. -/
theorem restrictedPositiveDifferenceValue_cast
    {μ c : ℝ} {Q0 m N : ℕ}
    {p : OrderedLongPair × OrderedLongPair}
    (hp : p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N) :
    (restrictedPositiveDifferenceValue p : ℤ) =
      orderedPhaseFrequency p.1 - orderedPhaseFrequency p.2 := by
  have hpos := (mem_restrictedPositiveDifferenceDomain_iff.mp hp).2.2
  simp [restrictedPositiveDifferenceValue, Int.toNat_of_nonneg (sub_nonneg.mpr hpos.le)]

/-- Diagonal part of the double phase sum is exactly the cardinality of the
restricted ordered domain. -/
theorem sum_restricted_diagonal_phase
    (μ c : ℝ) (Q0 m N : ℕ) (h : ℤ) (α : ℝ) :
    (∑ p ∈ ((orderedLongPairDomain μ c Q0 m N) ×ˢ
        (orderedLongPairDomain μ c Q0 m N)).filter fun p => p.1 = p.2,
      Theory.PiDigits.T27.phase
        (h * (orderedPhaseFrequency p.2 - orderedPhaseFrequency p.1)) α) =
      (orderedLongPairDomain μ c Q0 m N).card := by
  classical
  let Q := orderedLongPairDomain μ c Q0 m N
  have hdiag : (Q ×ˢ Q).filter (fun p => p.1 = p.2) =
      Q.image fun q => (q, q) := by
    ext p
    constructor
    · intro hp
      have hm := Finset.mem_filter.mp hp
      have hparts := Finset.mem_product.mp hm.1
      apply Finset.mem_image.mpr
      exact ⟨p.1, hparts.1, Prod.ext rfl hm.2⟩
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq, hq⟩, rfl⟩
  change (∑ p ∈ (Q ×ˢ Q).filter (fun p => p.1 = p.2),
    Theory.PiDigits.T27.phase
      (h * (orderedPhaseFrequency p.2 - orderedPhaseFrequency p.1)) α) = Q.card
  rw [hdiag, Finset.sum_image (fun a _ha b _hb hab => congrArg Prod.fst hab)]
  simp [Theory.PiDigits.T27.phase_zero]

/-- One-frequency centered energy is exactly the two-sided character sum over
positive restricted differences. -/
theorem restrictedPhaseSum_norm_sq_sub_card
    (μ c : ℝ) (Q0 m N h : ℕ) (α : ℝ) :
    ((‖restrictedPhaseSum μ c Q0 m N h α‖ ^ 2 : ℝ) : ℂ) -
        (orderedLongPairDomain μ c Q0 m N).card =
      ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        (Theory.PiDigits.T27.phase (-(h : ℤ))
            ((restrictedPositiveDifferenceValue p : ℝ) * α) +
          Theory.PiDigits.T27.phase (h : ℤ)
            ((restrictedPositiveDifferenceValue p : ℝ) * α)) := by
  classical
  let Q := orderedLongPairDomain μ c Q0 m N
  let P := Q ×ˢ Q
  let f : OrderedLongPair × OrderedLongPair → ℂ := fun p =>
    Theory.PiDigits.T27.phase
      ((h : ℤ) * (orderedPhaseFrequency p.2 - orderedPhaseFrequency p.1)) α
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p => p.1 ≠ p.2) f
  have hdiag : (P.filter fun p => ¬p.1 ≠ p.2) =
      P.filter fun p => p.1 = p.2 := by
    ext p
    simp
  have hdiagSum : (∑ p ∈ P.filter (fun p => ¬p.1 ≠ p.2), f p) = Q.card := by
    rw [hdiag]
    exact sum_restricted_diagonal_phase μ c Q0 m N h α
  have hoff : P.filter (fun p => p.1 ≠ p.2) =
      restrictedOffDiagonalDomain μ c Q0 m N := by rfl
  rw [restrictedPhaseSum_norm_sq_expansion]
  have hprod :
      (∑ p ∈ P, f p) =
        ∑ q ∈ Q, ∑ r ∈ Q,
          Theory.PiDigits.T27.phase
            ((h : ℤ) * (orderedPhaseFrequency r - orderedPhaseFrequency q)) α :=
    by
      simpa [P, Q, f] using (Finset.sum_product Q Q f)
  rw [← hprod]
  have htotal : (∑ p ∈ P, f p) - Q.card =
      ∑ p ∈ restrictedOffDiagonalDomain μ c Q0 m N, f p := by
    rw [← hoff, ← hsplit, hdiagSum]
    ring
  rw [htotal, sum_restrictedOffDiagonalDomain_eq_orient]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨q, r⟩
  have hcast := restrictedPositiveDifferenceValue_cast hp
  have hcastC : (restrictedPositiveDifferenceValue (q, r) : ℂ) =
      (orderedPhaseFrequency q : ℂ) - (orderedPhaseFrequency r : ℂ) := by
    exact_mod_cast hcast
  unfold f
  simp only [Prod.swap_prod_mk]
  unfold Theory.PiDigits.T27.phase
  congr 1 <;> push_cast <;> rw [hcastC] <;> ring

/-- Energy centered at its exact Lebesgue mean. -/
def restrictedCenteredEnergy
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℝ :=
  restrictedPhaseEnergy μ c Q0 m N α -
    (decimalFrequency m : ℝ) *
      (orderedLongPairDomain μ c Q0 m N).card

/-- Explicit finite two-sided Fourier polynomial for the centered energy. -/
def centeredEnergyPolynomial
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
      (Theory.PiDigits.T27.phase (-(h : ℤ))
          ((restrictedPositiveDifferenceValue p : ℝ) * α) +
        Theory.PiDigits.T27.phase (h : ℤ)
          ((restrictedPositiveDifferenceValue p : ℝ) * α))

/-- The centered real energy is exactly the displayed finite character
polynomial. -/
theorem restrictedCenteredEnergy_eq_polynomial
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    ((restrictedCenteredEnergy μ c Q0 m N α : ℝ) : ℂ) =
      centeredEnergyPolynomial μ c Q0 m N α := by
  unfold restrictedCenteredEnergy restrictedPhaseEnergy centeredEnergyPolynomial
  have hconst :
      (decimalFrequency m : ℂ) *
          ((orderedLongPairDomain μ c Q0 m N).card : ℂ) =
        ∑ _h ∈ Finset.Icc 1 (decimalFrequency m),
          ((orderedLongPairDomain μ c Q0 m N).card : ℂ) := by
    rw [Finset.sum_const, nsmul_eq_mul, decimalFrequencyDomain_card]
  push_cast
  rw [hconst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [Complex.ofReal_pow] using
    restrictedPhaseSum_norm_sq_sub_card μ c Q0 m N h α

/-- Multiplication of characters with different integer spatial frequencies. -/
theorem phase_mul_phase
    (h k : ℤ) (d e : ℕ) (α : ℝ) :
    Theory.PiDigits.T27.phase h ((d : ℝ) * α) *
        Theory.PiDigits.T27.phase k ((e : ℝ) * α) =
      Theory.PiDigits.T27.phase (h * d + k * e) α := by
  unfold Theory.PiDigits.T27.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Integrated product of two signed positive-frequency atoms. -/
theorem integral_phase_mul_phase
    (h k : ℤ) (d e : ℕ) :
    (∫ α, Theory.PiDigits.T27.phase h ((d : ℝ) * α) *
        Theory.PiDigits.T27.phase k ((e : ℝ) * α) ∂phaseMeasure) =
      if h * d + k * e = 0 then 1 else 0 := by
  simp_rw [phase_mul_phase]
  exact integral_phaseMeasure_phase _

/-- The four sign choices contribute exactly two resonances. -/
theorem sum_two_sign_integrals
    {h k d e : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hd : 0 < d) (he : 0 < e) :
    (∑ bh : Bool, ∑ bk : Bool,
      ∫ α,
        Theory.PiDigits.T27.phase (if bh then (h : ℤ) else -(h : ℤ))
            ((d : ℝ) * α) *
          Theory.PiDigits.T27.phase (if bk then (k : ℤ) else -(k : ℤ))
            ((e : ℝ) * α) ∂phaseMeasure) =
      if h * d = k * e then 2 else 0 := by
  simp only [Fintype.sum_bool, ↓reduceIte, integral_phase_mul_phase]
  by_cases hres : h * d = k * e
  · have hresZ : (h : ℤ) * d = (k : ℤ) * e := by exact_mod_cast hres
    have hhd : (0 : ℤ) < (h : ℤ) * d := by positivity
    have hke : (0 : ℤ) < (k : ℤ) * e := by positivity
    have hsum : (h : ℤ) * d + (k : ℤ) * e ≠ 0 := ne_of_gt (add_pos hhd hke)
    have hnegSum : -((h : ℤ) * d) + -((k : ℤ) * e) ≠ 0 := by
      intro hz
      omega
    have hh0 : h ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hh)
    have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
    have hd0 : d ≠ 0 := Nat.ne_of_gt hd
    have he0 : e ≠ 0 := Nat.ne_of_gt he
    simp [hres, hresZ, hsum, hnegSum, hh0, hk0, hd0, he0]
    norm_num
  · have hresZ : (h : ℤ) * d ≠ (k : ℤ) * e := by exact_mod_cast hres
    have hhd : (0 : ℤ) < (h : ℤ) * d := by positivity
    have hke : (0 : ℤ) < (k : ℤ) * e := by positivity
    have hsum : (h : ℤ) * d + (k : ℤ) * e ≠ 0 := ne_of_gt (add_pos hhd hke)
    have hnegSum : -((h : ℤ) * d) + -((k : ℤ) * e) ≠ 0 := by
      intro hz
      omega
    have hsub₁ : (h : ℤ) * d + -((k : ℤ) * e) ≠ 0 := by
      intro hz
      apply hresZ
      omega
    have hsub₂ : -((h : ℤ) * d) + (k : ℤ) * e ≠ 0 := by
      intro hz
      apply hresZ
      omega
    simp [hres, hsum, hnegSum, hsub₁, hsub₂]

/-- One signed atom of the centered-energy character polynomial. -/
def centeredEnergyAtom
    (b : Bool) (h d : ℕ) (α : ℝ) : ℂ :=
  Theory.PiDigits.T27.phase (if b then (h : ℤ) else -(h : ℤ)) ((d : ℝ) * α)

/-- Boolean-sign expansion of the centered-energy polynomial. -/
theorem centeredEnergyPolynomial_eq_signedSum
    (μ c : ℝ) (Q0 m N : ℕ) (α : ℝ) :
    centeredEnergyPolynomial μ c Q0 m N α =
      ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
        ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          ∑ b : Bool, centeredEnergyAtom b h
            (restrictedPositiveDifferenceValue p) α := by
  unfold centeredEnergyPolynomial centeredEnergyAtom
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro p hp
  simp [Fintype.sum_bool, add_comm]

/-- Fully expanded finite signed-resonance sum. -/
def centeredEnergyResonanceSum
    (μ c : ℝ) (Q0 m N : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
    ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
      ∑ bh : Bool,
        ∑ k ∈ Finset.Icc 1 (decimalFrequency m),
          ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
            ∑ bk : Bool,
              if (if bh then (h : ℤ) else -(h : ℤ)) *
                    restrictedPositiveDifferenceValue p +
                  (if bk then (k : ℤ) else -(k : ℤ)) *
                    restrictedPositiveDifferenceValue q = 0
              then 1 else 0

/-- Parseval expansion before commuting the finite summation order. -/
theorem integral_centeredEnergyPolynomial_sq_eq_resonanceSum
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∫ α, centeredEnergyPolynomial μ c Q0 m N α ^ 2 ∂phaseMeasure) =
      centeredEnergyResonanceSum μ c Q0 m N := by
  classical
  simp_rw [centeredEnergyPolynomial_eq_signedSum, pow_two, Finset.sum_mul,
    Finset.mul_sum]
  unfold centeredEnergyResonanceSum
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro bh hbh
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [MeasureTheory.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro q hq
            rw [MeasureTheory.integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro bk hbk
              unfold centeredEnergyAtom
              exact integral_phase_mul_phase _ _ _ _
            · intro bk hbk
              rw [phaseMeasure]
              exact ((by
                unfold centeredEnergyAtom Theory.PiDigits.T27.phase
                fun_prop : Continuous (fun α : ℝ =>
                  centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
                    centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
                  Set.Ico_subset_Icc_self
          · intro q hq
            apply integrable_finsetSum
            intro bk hbk
            rw [phaseMeasure]
            exact ((by
              unfold centeredEnergyAtom Theory.PiDigits.T27.phase
              fun_prop : Continuous (fun α : ℝ =>
                centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
                  centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
                Set.Ico_subset_Icc_self
        · intro k hk
          apply integrable_finsetSum
          intro q hq
          apply integrable_finsetSum
          intro bk hbk
          rw [phaseMeasure]
          exact ((by
            unfold centeredEnergyAtom Theory.PiDigits.T27.phase
            fun_prop : Continuous (fun α : ℝ =>
              centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
                centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
              Set.Ico_subset_Icc_self
      · intro bh hbh
        apply integrable_finsetSum
        intro k hk
        apply integrable_finsetSum
        intro q hq
        apply integrable_finsetSum
        intro bk hbk
        rw [phaseMeasure]
        exact ((by
          unfold centeredEnergyAtom Theory.PiDigits.T27.phase
          fun_prop : Continuous (fun α : ℝ =>
            centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
              centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self
    · intro p hp
      apply integrable_finsetSum
      intro bh hbh
      apply integrable_finsetSum
      intro k hk
      apply integrable_finsetSum
      intro q hq
      apply integrable_finsetSum
      intro bk hbk
      rw [phaseMeasure]
      exact ((by
        unfold centeredEnergyAtom Theory.PiDigits.T27.phase
        fun_prop : Continuous (fun α : ℝ =>
          centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
            centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
          Set.Ico_subset_Icc_self
  · intro h hh
    apply integrable_finsetSum
    intro p hp
    apply integrable_finsetSum
    intro bh hbh
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro q hq
    apply integrable_finsetSum
    intro bk hbk
    rw [phaseMeasure]
    exact ((by
      unfold centeredEnergyAtom Theory.PiDigits.T27.phase
      fun_prop : Continuous (fun α : ℝ =>
        centeredEnergyAtom bh h (restrictedPositiveDifferenceValue p) α *
          centeredEnergyAtom bk k (restrictedPositiveDifferenceValue q) α)).integrableOn_Icc).mono_set
        Set.Ico_subset_Icc_self

/-- Algebraic version of the two-sign resonance calculation. -/
theorem sum_two_sign_indicators
    {h k d e : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    (hd : 0 < d) (he : 0 < e) :
    (∑ bh : Bool, ∑ bk : Bool,
      if (if bh then (h : ℤ) else -(h : ℤ)) * d +
          (if bk then (k : ℤ) else -(k : ℤ)) * e = 0
      then (1 : ℂ) else 0) =
      if h * d = k * e then 2 else 0 := by
  simpa only [centeredEnergyAtom, integral_phase_mul_phase] using
    sum_two_sign_integrals hh hk hd he

/-- Commuting the finite sums groups the two signs and identifies the exact
positive-frequency resonance-domain cardinalities. -/
theorem centeredEnergyResonanceSum_eq
    (μ c : ℝ) (Q0 m N : ℕ) :
    centeredEnergyResonanceSum μ c Q0 m N =
      2 * ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          ((resonanceDomain (decimalFrequency m)
            (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q)).card : ℂ) := by
  classical
  let F := Finset.Icc 1 (decimalFrequency m)
  let D := restrictedPositiveDifferenceDomain μ c Q0 m N
  let term : ℕ → (OrderedLongPair × OrderedLongPair) → Bool →
      ℕ → (OrderedLongPair × OrderedLongPair) → Bool → ℂ :=
    fun h p bh k q bk =>
      if (if bh then (h : ℤ) else -(h : ℤ)) *
            restrictedPositiveDifferenceValue p +
          (if bk then (k : ℤ) else -(k : ℤ)) *
            restrictedPositiveDifferenceValue q = 0
      then 1 else 0
  change (∑ h ∈ F, ∑ p ∈ D, ∑ bh : Bool,
      ∑ k ∈ F, ∑ q ∈ D, ∑ bk : Bool, term h p bh k q bk) = _
  have hsignMove (h : ℕ) (p : OrderedLongPair × OrderedLongPair) :
      (∑ bh : Bool, ∑ k ∈ F, ∑ q ∈ D, ∑ bk : Bool,
          term h p bh k q bk) =
        ∑ k ∈ F, ∑ q ∈ D, ∑ bh : Bool, ∑ bk : Bool,
          term h p bh k q bk := by
    calc
      (∑ bh : Bool, ∑ k ∈ F, ∑ q ∈ D, ∑ bk : Bool,
          term h p bh k q bk) =
          ∑ k ∈ F, ∑ bh : Bool, ∑ q ∈ D, ∑ bk : Bool,
            term h p bh k q bk := by
        exact Finset.sum_comm
      _ = ∑ k ∈ F, ∑ q ∈ D, ∑ bh : Bool, ∑ bk : Bool,
            term h p bh k q bk := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Finset.sum_comm
  calc
    (∑ h ∈ F, ∑ p ∈ D, ∑ bh : Bool,
        ∑ k ∈ F, ∑ q ∈ D, ∑ bk : Bool, term h p bh k q bk) =
        ∑ h ∈ F, ∑ p ∈ D, ∑ k ∈ F, ∑ q ∈ D,
          ∑ bh : Bool, ∑ bk : Bool, term h p bh k q bk := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro p hp
      exact hsignMove h p
    _ = ∑ p ∈ D, ∑ q ∈ D, ∑ h ∈ F, ∑ k ∈ F,
          ∑ bh : Bool, ∑ bk : Bool, term h p bh k q bk := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        (∑ h ∈ F, ∑ k ∈ F, ∑ q ∈ D,
            ∑ bh : Bool, ∑ bk : Bool, term h p bh k q bk) =
            ∑ h ∈ F, ∑ q ∈ D, ∑ k ∈ F,
              ∑ bh : Bool, ∑ bk : Bool, term h p bh k q bk := by
          apply Finset.sum_congr rfl
          intro h hh
          exact Finset.sum_comm
        _ = ∑ q ∈ D, ∑ h ∈ F, ∑ k ∈ F,
              ∑ bh : Bool, ∑ bk : Bool, term h p bh k q bk := by
          rw [Finset.sum_comm]
    _ = ∑ p ∈ D, ∑ q ∈ D, ∑ h ∈ F, ∑ k ∈ F,
          (if h * restrictedPositiveDifferenceValue p =
              k * restrictedPositiveDifferenceValue q then (2 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      have hpPos : 0 < restrictedPositiveDifferenceValue p := by
        have hlt := (mem_restrictedPositiveDifferenceDomain_iff.mp hp).2.2
        have hcast := restrictedPositiveDifferenceValue_cast hp
        have hposZ : (0 : ℤ) < (restrictedPositiveDifferenceValue p : ℤ) := by
          rw [hcast]
          exact sub_pos.mpr hlt
        exact_mod_cast hposZ
      have hqPos : 0 < restrictedPositiveDifferenceValue q := by
        have hlt := (mem_restrictedPositiveDifferenceDomain_iff.mp hq).2.2
        have hcast := restrictedPositiveDifferenceValue_cast hq
        have hposZ : (0 : ℤ) < (restrictedPositiveDifferenceValue q : ℤ) := by
          rw [hcast]
          exact sub_pos.mpr hlt
        exact_mod_cast hposZ
      exact sum_two_sign_indicators
        (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1 hpPos hqPos
    _ = 2 * ∑ p ∈ D, ∑ q ∈ D,
          ((resonanceDomain (decimalFrequency m)
            (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q)).card : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hcount :
          (∑ h ∈ F, ∑ k ∈ F,
            (if h * restrictedPositiveDifferenceValue p =
                k * restrictedPositiveDifferenceValue q then (2 : ℂ) else 0)) =
            2 * ((resonanceDomain (decimalFrequency m)
              (restrictedPositiveDifferenceValue p)
              (restrictedPositiveDifferenceValue q)).card : ℂ) := by
        have hprod :
            (∑ h ∈ F, ∑ k ∈ F,
              (if h * restrictedPositiveDifferenceValue p =
                  k * restrictedPositiveDifferenceValue q then (2 : ℂ) else 0)) =
              ∑ x ∈ F ×ˢ F,
                (if x.1 * restrictedPositiveDifferenceValue p =
                    x.2 * restrictedPositiveDifferenceValue q then (2 : ℂ) else 0) := by
          simpa using (Finset.sum_product F F (fun x =>
            if x.1 * restrictedPositiveDifferenceValue p =
                x.2 * restrictedPositiveDifferenceValue q then (2 : ℂ) else 0)).symm
        rw [hprod]
        rw [← Finset.sum_filter]
        simp [F, resonanceDomain]
        ring
      exact hcount
    _ = 2 * ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          ((resonanceDomain (decimalFrequency m)
            (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q)).card : ℂ) := by rfl

/-- Rational form of the sharp resonance count, now matching T16's ordinary
GCD kernel exactly. -/
theorem resonanceDomain_card_le_gcdKernel
    {H d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ((resonanceDomain H d e).card : ℚ) ≤
      (H : ℚ) * gcdKernel d e := by
  have hnat := resonanceDomain_card_mul_max_le H d e
  have hcast : ((resonanceDomain H d e).card : ℚ) * Nat.max d e ≤
      (H : ℚ) * Nat.gcd d e := by exact_mod_cast hnat
  have hmax : (0 : ℚ) < Nat.max d e := by
    exact_mod_cast (lt_of_lt_of_le hd (Nat.le_max_left d e))
  rw [gcdKernel]
  rw [show (H : ℚ) * ((Nat.gcd d e : ℚ) / (Nat.max d e : ℚ)) =
      ((H : ℚ) * Nat.gcd d e) / (Nat.max d e : ℚ) by ring]
  exact (le_div_iff₀ hmax).2 hcast

/-- Attached and unattached forms of the restricted weighted-GCD sum agree. -/
theorem restrictedDifferenceWeightedGCD_eq_unattached
    (μ c : ℝ) (Q0 m N : ℕ) :
    restrictedDifferenceWeightedGCD μ c Q0 m N =
      ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          gcdKernel (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q) := by
  unfold restrictedDifferenceWeightedGCD
  rw [Finset.sum_product]
  let D := restrictedPositiveDifferenceDomain μ c Q0 m N
  change (∑ p ∈ D.attach, ∑ q ∈ D.attach,
      gcdKernel (restrictedPositiveDifferenceValue p.1)
        (restrictedPositiveDifferenceValue q.1)) = _
  calc
    (∑ p ∈ D.attach, ∑ q ∈ D.attach,
      gcdKernel (restrictedPositiveDifferenceValue p.1)
        (restrictedPositiveDifferenceValue q.1)) =
        ∑ p ∈ D.attach, ∑ q ∈ D,
          gcdKernel (restrictedPositiveDifferenceValue p.1)
            (restrictedPositiveDifferenceValue q) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_attach D (fun q =>
        gcdKernel (restrictedPositiveDifferenceValue p.1)
          (restrictedPositiveDifferenceValue q))
    _ = ∑ p ∈ D, ∑ q ∈ D,
          gcdKernel (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q) :=
      Finset.sum_attach D (fun p => ∑ q ∈ D,
        gcdKernel (restrictedPositiveDifferenceValue p)
          (restrictedPositiveDifferenceValue q))
    _ = _ := by rfl

/-- The exact finite resonance sum is controlled by `H` times T16's
restricted weighted-GCD sum. -/
theorem resonanceCardSum_le_weightedGCD
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
      ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ((resonanceDomain (decimalFrequency m)
          (restrictedPositiveDifferenceValue p)
          (restrictedPositiveDifferenceValue q)).card : ℚ)) ≤
      (decimalFrequency m : ℚ) *
        restrictedDifferenceWeightedGCD μ c Q0 m N := by
  rw [restrictedDifferenceWeightedGCD_eq_unattached, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hpPos : 0 < restrictedPositiveDifferenceValue p := by
    have hlt := (mem_restrictedPositiveDifferenceDomain_iff.mp hp).2.2
    have hcast := restrictedPositiveDifferenceValue_cast hp
    have hposZ : (0 : ℤ) < (restrictedPositiveDifferenceValue p : ℤ) := by
      rw [hcast]
      exact sub_pos.mpr hlt
    exact_mod_cast hposZ
  have hqPos : 0 < restrictedPositiveDifferenceValue q := by
    have hlt := (mem_restrictedPositiveDifferenceDomain_iff.mp hq).2.2
    have hcast := restrictedPositiveDifferenceValue_cast hq
    have hposZ : (0 : ℤ) < (restrictedPositiveDifferenceValue q : ℤ) := by
      rw [hcast]
      exact sub_pos.mpr hlt
    exact_mod_cast hposZ
  exact resonanceDomain_card_le_gcdKernel hpPos hqPos

/-- Exact real Parseval identity for the centered energy. -/
theorem integral_restrictedCenteredEnergy_sq
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∫ α, restrictedCenteredEnergy μ c Q0 m N α ^ 2 ∂phaseMeasure) =
      2 * ∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          ((resonanceDomain (decimalFrequency m)
            (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q)).card : ℝ) := by
  have hcomplex := (integral_centeredEnergyPolynomial_sq_eq_resonanceSum
    μ c Q0 m N).trans (centeredEnergyResonanceSum_eq μ c Q0 m N)
  have hrewrite :
      (∫ α, centeredEnergyPolynomial μ c Q0 m N α ^ 2 ∂phaseMeasure) =
        ∫ α, ((restrictedCenteredEnergy μ c Q0 m N α ^ 2 : ℝ) : ℂ)
          ∂phaseMeasure := by
    apply integral_congr_ae
    filter_upwards [] with α
    rw [← restrictedCenteredEnergy_eq_polynomial]
    exact (Complex.ofReal_pow _ 2).symm
  rw [hrewrite, integral_complex_ofReal] at hcomplex
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_mul,
    Complex.ofReal_sum, Nat.cast_ofNat, Nat.cast_id] using hcomplex)

/-- Explicit variance estimate supplied by T16. -/
theorem integral_restrictedCenteredEnergy_sq_le
    (μ c : ℝ) (Q0 m N : ℕ) :
    (∫ α, restrictedCenteredEnergy μ c Q0 m N α ^ 2 ∂phaseMeasure) ≤
      2 * 574913232 * (decimalFrequency m : ℝ) * (N : ℝ) ^ 4 := by
  rw [integral_restrictedCenteredEnergy_sq]
  have hres := resonanceCardSum_le_weightedGCD μ c Q0 m N
  have hweighted := restrictedDifferenceWeightedGCD_le μ c Q0 m N
  have hresR :
      (∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
          ((resonanceDomain (decimalFrequency m)
            (restrictedPositiveDifferenceValue p)
            (restrictedPositiveDifferenceValue q)).card : ℝ)) ≤
        (decimalFrequency m : ℝ) *
          (restrictedDifferenceWeightedGCD μ c Q0 m N : ℝ) := by
    exact_mod_cast hres
  have hweightedR : (restrictedDifferenceWeightedGCD μ c Q0 m N : ℝ) ≤
      574913232 * (N : ℝ) ^ 4 := by exact_mod_cast hweighted
  calc
    2 * (∑ p ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
      ∑ q ∈ restrictedPositiveDifferenceDomain μ c Q0 m N,
        ((resonanceDomain (decimalFrequency m)
          (restrictedPositiveDifferenceValue p)
          (restrictedPositiveDifferenceValue q)).card : ℝ)) ≤
        2 * ((decimalFrequency m : ℝ) *
          (restrictedDifferenceWeightedGCD μ c Q0 m N : ℝ)) := by gcongr
    _ ≤ 2 * ((decimalFrequency m : ℝ) *
          (574913232 * (N : ℝ) ^ 4)) := by gcongr
    _ = 2 * 574913232 * (decimalFrequency m : ℝ) * (N : ℝ) ^ 4 := by ring

/-- Sharper cardinality bound obtained from the represented ordered
endpoints. -/
theorem orderedLongPairDomain_card_le_sq
    (μ c : ℝ) (Q0 m N : ℕ) :
    (orderedLongPairDomain μ c Q0 m N).card ≤ N ^ 2 := by
  classical
  let encode : OrderedLongPair → ℕ × ℕ := fun q =>
    (orderedFirst q, orderedSecond q)
  have hinj : Set.InjOn encode
      (orderedLongPairDomain μ c Q0 m N : Set OrderedLongPair) := by
    intro p hp q hq hpq
    apply orderedPhaseFrequency_injOn μ c Q0 m N hp hq
    simp [orderedPhaseFrequency, encode] at hpq ⊢
    rw [hpq.1, hpq.2]
  have himage : (orderedLongPairDomain μ c Q0 m N).image encode ⊆
      Finset.range N ×ˢ Finset.range N := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hcoords := ordered_coordinates_lt hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hcoords.1, Finset.mem_range.mpr hcoords.2⟩
  calc
    (orderedLongPairDomain μ c Q0 m N).card =
        ((orderedLongPairDomain μ c Q0 m N).image encode).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range N ×ˢ Finset.range N).card := Finset.card_le_card himage
    _ = N ^ 2 := by simp [pow_two]

/-- The scale has its factorized form. -/
theorem scaleTerm_eq_factorized (t : ℝ) (m N : ℕ) :
    scaleTerm t m N =
      (N : ℝ) * (1 + (N : ℝ) * (10 : ℝ) ^ (-t * (m : ℝ))) := by
  unfold scaleTerm
  ring

/-- The scale dominates its linear term. -/
theorem natCast_le_scaleTerm (t : ℝ) (m N : ℕ) :
    (N : ℝ) ≤ scaleTerm t m N := by
  unfold scaleTerm
  have hnonneg : 0 ≤ (N : ℝ) ^ 2 * (10 : ℝ) ^ (-t * (m : ℝ)) := by
    positivity
  linarith

/-- Positivity of every positive-integer scale. -/
theorem scaleTerm_pos {t : ℝ} {m N : ℕ} (hN : 1 ≤ N) :
    0 < scaleTerm t m N := by
  exact (show (0 : ℝ) < N by exact_mod_cast hN).trans_le
    (natCast_le_scaleTerm t m N)

/-- A `Tail(t)` violation forces a centered-energy deviation of size
`3 H T_t^2`. -/
theorem tailBadSet_subset_centeredDeviation
    {t : ℝ} {Q0 m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    tailBadSet t Q0 m N ⊆
      {α | 9 * (decimalFrequency m : ℝ) ^ 2 * scaleTerm t m N ^ 4 ≤
        restrictedCenteredEnergy 8 1 Q0 m N α ^ 2} := by
  intro α hα
  have hbad := hα.2
  let H : ℝ := decimalFrequency m
  let T : ℝ := scaleTerm t m N
  let A : ℝ := restrictedPhaseL1 8 1 Q0 m N α
  let E : ℝ := restrictedPhaseEnergy 8 1 Q0 m N α
  let C : ℝ := (orderedLongPairDomain 8 1 Q0 m N).card
  have hH : 0 < H := by
    dsimp [H, decimalFrequency]
    positivity
  have hT : 0 < T := scaleTerm_pos hN
  have hA : 0 ≤ A := by
    dsimp [A, restrictedPhaseL1]
    positivity
  have hCS : A ^ 2 ≤ H * E := by
    exact restrictedPhaseL1_sq_le 8 1 Q0 m N α
  have hthreshold : 4 * H ^ 2 * T ^ 2 < A ^ 2 := by
    change 2 * H * T < A at hbad
    have hbase : 0 ≤ 2 * H * T := by positivity
    have hsquare := (sq_lt_sq₀ hbase hA).mpr hbad
    calc
      4 * H ^ 2 * T ^ 2 = (2 * H * T) ^ 2 := by ring
      _ < A ^ 2 := hsquare
  have hE : 4 * H * T ^ 2 < E := by
    nlinarith [mul_pos hH (sub_pos.mpr (hthreshold.trans_le hCS))]
  have hcardNat := orderedLongPairDomain_card_le_sq 8 1 Q0 m N
  have hcard : C ≤ (N : ℝ) ^ 2 := by
    dsimp [C]
    exact_mod_cast hcardNat
  have hNT : (N : ℝ) ≤ T := natCast_le_scaleTerm t m N
  have hmean : H * C ≤ H * T ^ 2 := by
    have hNsq : (N : ℝ) ^ 2 ≤ T ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left (hcard.trans hNsq) hH.le
  have hcenter : 3 * H * T ^ 2 < E - H * C := by nlinarith
  change 9 * H ^ 2 * T ^ 4 ≤ (E - H * C) ^ 2
  have hbase : 0 ≤ 3 * H * T ^ 2 := by positivity
  have hright : 0 ≤ E - H * C := hbase.trans hcenter.le
  calc
    9 * H ^ 2 * T ^ 4 = (3 * H * T ^ 2) ^ 2 := by ring
    _ ≤ (E - H * C) ^ 2 := (sq_le_sq₀ hbase hright).2 hcenter.le

/-- The displayed `Tail(t)` estimate with all constants, the exact measure,
restricted domain, and inclusive frequency range exposed by the definitions:
`K_t = 2`, `C_t = 127758496`, and `p_t = 4`. -/
theorem tail_estimate
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    phaseMeasure.real (tailBadSet t Q0 m N) ≤
      127758496 /
        ((decimalFrequency m : ℝ) *
          (1 + (N : ℝ) * (10 : ℝ) ^ (-t * (m : ℝ))) ^ 4) := by
  let H : ℝ := decimalFrequency m
  let T : ℝ := scaleTerm t m N
  let ε : ℝ := 9 * H ^ 2 * T ^ 4
  let deviation : Set ℝ :=
    {α | ε ≤ restrictedCenteredEnergy 8 1 Q0 m N α ^ 2}
  have hH : 0 < H := by
    dsimp [H, decimalFrequency]
    positivity
  have hT : 0 < T := scaleTerm_pos hN
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hsubset : tailBadSet t Q0 m N ⊆ deviation := by
    simpa [deviation, ε, H, T] using
      (tailBadSet_subset_centeredDeviation (t := t) (Q0 := Q0) hm hN)
  have hcont : Continuous (restrictedCenteredEnergy 8 1 Q0 m N) := by
    unfold restrictedCenteredEnergy
    exact (continuous_restrictedPhaseEnergy 8 1 Q0 m N).sub continuous_const
  have hint : Integrable
      (fun α => restrictedCenteredEnergy 8 1 Q0 m N α ^ 2) phaseMeasure := by
    rw [phaseMeasure]
    exact (hcont.pow 2).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hmarkov :
      ε * phaseMeasure.real deviation ≤
        ∫ α, restrictedCenteredEnergy 8 1 Q0 m N α ^ 2 ∂phaseMeasure := by
    exact mul_meas_ge_le_integral_of_nonneg
      (ae_of_all phaseMeasure fun α => sq_nonneg
        (restrictedCenteredEnergy 8 1 Q0 m N α)) hint ε
  have hmono : phaseMeasure.real (tailBadSet t Q0 m N) ≤
      phaseMeasure.real deviation := measureReal_mono hsubset
  have hvariance := integral_restrictedCenteredEnergy_sq_le 8 1 Q0 m N
  have hscaled : ε * phaseMeasure.real (tailBadSet t Q0 m N) ≤
      2 * 574913232 * H * (N : ℝ) ^ 4 := by
    calc
      ε * phaseMeasure.real (tailBadSet t Q0 m N) ≤
          ε * phaseMeasure.real deviation := mul_le_mul_of_nonneg_left hmono hε.le
      _ ≤ ∫ α, restrictedCenteredEnergy 8 1 Q0 m N α ^ 2 ∂phaseMeasure := hmarkov
      _ ≤ 2 * 574913232 * H * (N : ℝ) ^ 4 := by simpa [H] using hvariance
  have hraw : phaseMeasure.real (tailBadSet t Q0 m N) ≤
      (2 * 574913232 * H * (N : ℝ) ^ 4) / ε :=
    (le_div_iff₀ hε).2 (by simpa [mul_comm] using hscaled)
  calc
    phaseMeasure.real (tailBadSet t Q0 m N) ≤
        (2 * 574913232 * H * (N : ℝ) ^ 4) / ε := hraw
    _ = 127758496 * (N : ℝ) ^ 4 / (H * T ^ 4) := by
      dsimp [ε]
      field_simp [ne_of_gt hH, ne_of_gt hT]
      ring
    _ = 127758496 /
        ((decimalFrequency m : ℝ) *
          (1 + (N : ℝ) * (10 : ℝ) ^ (-t * (m : ℝ))) ^ 4) := by
      dsimp [H, T]
      rw [scaleTerm_eq_factorized]
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one hN))
      field_simp [hNreal, show (decimalFrequency m : ℝ) ≠ 0 by positivity,
        show 1 + (N : ℝ) * (10 : ℝ) ^ (-t * (m : ℝ)) ≠ 0 by positivity]

/-- Every displayed `Tail(t)` event is measurable. -/
theorem measurableSet_tailBadSet
    (t : ℝ) (Q0 m N : ℕ) : MeasurableSet (tailBadSet t Q0 m N) := by
  apply MeasurableSet.inter measurableSet_Ico
  exact measurableSet_lt measurable_const
    (continuous_restrictedPhaseL1 8 1 Q0 m N).measurable

/-! ## All-integer summability and Borel--Cantelli -/

/-- The dyadic slab containing the positive integer `N`. -/
def dyadicSlab (j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (2 ^ (j + 1))

/-- Every positive integer belongs to its explicit dyadic slab. This records
that the all-integer summation below includes every slab, rather than replacing
the events in a slab by an endpoint event. -/
theorem positive_mem_dyadicSlab {N : ℕ} (hN : 0 < N) :
    N ∈ dyadicSlab (Nat.log 2 N) := by
  rw [dyadicSlab, Finset.mem_Ico]
  exact ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hN),
    Nat.lt_pow_succ_log_self (by norm_num) N⟩

/-- Membership in a dyadic slab determines its index. -/
theorem mem_dyadicSlab_iff_log_eq
    {N : ℕ} (hN : 0 < N) (j : ℕ) :
    N ∈ dyadicSlab j ↔ Nat.log 2 N = j := by
  rw [dyadicSlab, Finset.mem_Ico]
  exact (Nat.log_eq_iff
    (b := 2) (m := j) (n := N)
    (Or.inr ⟨by norm_num, Nat.ne_of_gt hN⟩)).symm

/-- The dyadic slabs form an exact partition of the positive integers. -/
theorem existsUnique_mem_dyadicSlab_iff_pos (N : ℕ) :
    (∃! j : ℕ, N ∈ dyadicSlab j) ↔ 0 < N := by
  constructor
  · rintro ⟨j, hj, _⟩
    have hlower : 2 ^ j ≤ N := (Finset.mem_Ico.mp hj).1
    exact (pow_pos (by norm_num) j).trans_le hlower
  · intro hN
    refine ⟨Nat.log 2 N, positive_mem_dyadicSlab hN, ?_⟩
    intro j hj
    exact (mem_dyadicSlab_iff_log_eq hN j).mp hj |>.symm

/-- The explicit `Tail(t)` majorant is summable over every positive integer
pair. A fractional p-series comparison proves the full all-integer statement
directly; `existsUnique_mem_dyadicSlab_iff_pos` records the corresponding
dyadic-to-all-integer partition without replacing events by slab endpoints. -/
theorem summable_tail_majorant
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (fun z : ℕ × ℕ =>
      (127758496 : ℝ) /
        ((10 : ℝ) ^ (z.1 + 1) *
          (1 + ((z.2 + 1 : ℕ) : ℝ) *
            (10 : ℝ) ^ (-t * ((z.1 + 1 : ℕ) : ℝ))) ^ 4)) := by
  let p : ℝ := (3 - t) / 2
  let q : ℝ := (10 : ℝ) ^ (t * p - 1)
  have hp1 : 1 < p := by
    dsimp [p]
    linarith
  have hp0 : 0 ≤ p := hp1.le.trans' zero_le_one
  have hp4 : p ≤ 4 := by
    dsimp [p]
    linarith
  have htp : t * p < 1 := by
    dsimp [p]
    nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  have hq0 : 0 ≤ q :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num) (sub_neg.mpr htp)
  have hqm : Summable (fun m : ℕ => q ^ (m + 1)) :=
    (summable_nat_add_iff 1).2
      (summable_geometric_of_lt_one hq0 hq1)
  have hm : Summable (fun m : ℕ =>
      (127758496 : ℝ) *
        (10 : ℝ) ^ ((t * p - 1) * ((m + 1 : ℕ) : ℝ))) := by
    apply (hqm.mul_left (127758496 : ℝ)).congr
    intro m
    rw [show q = (10 : ℝ) ^ (t * p - 1) by rfl,
      ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hn : Summable (fun N : ℕ =>
      1 / (((N + 1 : ℕ) : ℝ) ^ p)) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff
        (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1).2
        (Real.summable_one_div_nat_rpow.mpr hp1)
  have hprod : Summable (fun z : ℕ × ℕ =>
      ((127758496 : ℝ) *
        (10 : ℝ) ^
          ((t * p - 1) * ((z.1 + 1 : ℕ) : ℝ))) *
        (1 / (((z.2 + 1 : ℕ) : ℝ) ^ p))) :=
    hm.mul_of_nonneg hn
      (fun _ => by positivity)
      (fun _ => by positivity)
  apply hprod.of_nonneg_of_le (fun _ => by positivity)
  intro z
  let M : ℕ := z.1 + 1
  let K : ℕ := z.2 + 1
  let a : ℝ := (10 : ℝ) ^ (-t * (M : ℝ))
  let x : ℝ := (K : ℝ) * a
  have hK : 0 < (K : ℝ) := by
    exact_mod_cast Nat.succ_pos z.2
  have ha : 0 < a :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hx : 0 ≤ x :=
    (mul_pos hK ha).le
  have hxp : x ^ p ≤ (1 + x) ^ 4 := by
    calc
      x ^ p ≤ (1 + x) ^ p :=
        Real.rpow_le_rpow hx (by linarith) hp0
      _ ≤ (1 + x) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by linarith) hp4
      _ = (1 + x) ^ 4 :=
        Real.rpow_natCast _ 4
  have htenM : 0 < (10 : ℝ) ^ M := by
    positivity
  have hden :
      (10 : ℝ) ^ M * x ^ p ≤
        (10 : ℝ) ^ M * (1 + x) ^ 4 :=
    mul_le_mul_of_nonneg_left hxp htenM.le
  have hcmp :
      (127758496 : ℝ) /
          ((10 : ℝ) ^ M * (1 + x) ^ 4) ≤
        (127758496 : ℝ) /
          ((10 : ℝ) ^ M * x ^ p) :=
    div_le_div_of_nonneg_left
      (by norm_num)
      (mul_pos htenM (by positivity))
      hden
  change
    (127758496 : ℝ) /
        ((10 : ℝ) ^ M * (1 + x) ^ 4) ≤ _
  refine hcmp.trans_eq ?_
  dsimp [x]
  rw [Real.mul_rpow hK.le ha.le]
  dsimp [a]
  rw [← Real.rpow_mul
    (by norm_num : (0 : ℝ) ≤ 10)
    (-t * (M : ℝ)) p]
  have hcombine :
      (10 : ℝ) ^ M *
          (((K : ℝ) ^ p) *
            (10 : ℝ) ^ (-t * (M : ℝ) * p)) =
        ((K : ℝ) ^ p) *
          (10 : ℝ) ^
            ((M : ℝ) + (-t * (M : ℝ) * p)) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
    ring
  rw [hcombine]
  have heq :
      (t * p - 1) * (M : ℝ) =
        -((M : ℝ) + (-t * (M : ℝ) * p)) := by
    ring
  change
    (127758496 : ℝ) /
        ((K : ℝ) ^ p *
          (10 : ℝ) ^
            ((M : ℝ) + (-t * (M : ℝ) * p))) =
      (127758496 : ℝ) *
        (10 : ℝ) ^ ((t * p - 1) * (M : ℝ)) *
        (1 / (K : ℝ) ^ p)
  rw [heq,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
  field_simp

/-- The real measures of all positive-integer bad events are summable. -/
theorem summable_tailBadSet_measureReal
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (Q0 : ℕ) :
    Summable (fun z : ℕ × ℕ =>
      phaseMeasure.real
        (tailBadSet t Q0 (z.1 + 1) (z.2 + 1))) := by
  apply (summable_tail_majorant t ht0 ht1).of_nonneg_of_le
    (fun _ => measureReal_nonneg)
  intro z
  simpa [decimalFrequency, Nat.cast_pow] using
    tail_estimate t ht0 ht1 Q0
      (z.1 + 1) (z.2 + 1)
      (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))
      (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))

/-- First Borel--Cantelli for the exact positive-integer `Tail(t)` events. -/
theorem phaseMeasure_tailExceptionalSet_eq_zero
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (Q0 : ℕ) :
    phaseMeasure (tailExceptionalSet t Q0) = 0 := by
  have hreal :
      Summable (fun z : ℕ × ℕ =>
        phaseMeasure.real
          (tailBadSet t Q0 (z.1 + 1) (z.2 + 1))) :=
    summable_tailBadSet_measureReal t ht0 ht1 Q0
  have heq :
      (fun z : ℕ × ℕ =>
        ENNReal.ofReal
          (phaseMeasure.real
            (tailBadSet t Q0 (z.1 + 1) (z.2 + 1)))) =
      (fun z : ℕ × ℕ =>
        phaseMeasure
          (tailBadSet t Q0 (z.1 + 1) (z.2 + 1))) := by
    funext z
    exact ofReal_measureReal
  have hsum :
      (∑' z : ℕ × ℕ,
        phaseMeasure
          (tailBadSet t Q0 (z.1 + 1) (z.2 + 1))) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite :
      ∀ᵐ α ∂phaseMeasure,
        {z : ℕ × ℕ |
          α ∈ tailBadSet t Q0
            (z.1 + 1) (z.2 + 1)}.Finite :=
    ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with α hα
  change
    ¬{z : ℕ × ℕ |
      α ∈ tailBadSet t Q0
        (z.1 + 1) (z.2 + 1)}.Infinite
  exact fun hinfinite => hinfinite hα

/-! ## Simultaneous exponents and the full-measure set -/

/-- Union of the null exceptional sets over rational exponents in `(0,1)`. -/
def rationalTailExceptionalSet (Q0 : ℕ) : Set ℝ :=
  ⋃ t : ℚ, if 0 < t ∧ t < 1 then
    tailExceptionalSet (t : ℝ) Q0 else ∅

/-- A measurable full-measure subset of `[0,1)` obtained by removing a
measurable hull of all rational-exponent exceptional sets. -/
def fullMeasurePhaseSet (Q0 : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 \
    toMeasurable phaseMeasure (rationalTailExceptionalSet Q0)

/-- The countable union of rational-exponent exceptional sets is null. -/
theorem phaseMeasure_rationalTailExceptionalSet_eq_zero (Q0 : ℕ) :
    phaseMeasure (rationalTailExceptionalSet Q0) = 0 := by
  rw [rationalTailExceptionalSet]
  apply measure_iUnion_null
  intro t
  by_cases ht : 0 < t ∧ t < 1
  · rw [if_pos ht]
    exact phaseMeasure_tailExceptionalSet_eq_zero (t : ℝ)
      (by exact_mod_cast ht.1) (by exact_mod_cast ht.2) Q0
  · simp [ht]

/-- The chosen phase set is measurable. -/
theorem measurableSet_fullMeasurePhaseSet (Q0 : ℕ) :
    MeasurableSet (fullMeasurePhaseSet Q0) := by
  exact measurableSet_Ico.diff (measurableSet_toMeasurable _ _)

/-- The chosen phase set lies in the explicit half-open unit interval. -/
theorem fullMeasurePhaseSet_subset_Ico (Q0 : ℕ) :
    fullMeasurePhaseSet Q0 ⊆ Set.Ico (0 : ℝ) 1 := by
  exact Set.diff_subset

/-- The chosen phase set has full `phaseMeasure` measure. -/
theorem phaseMeasure_fullMeasurePhaseSet (Q0 : ℕ) :
    phaseMeasure (fullMeasurePhaseSet Q0) = 1 := by
  rw [fullMeasurePhaseSet, measure_diff_null]
  · simp [phaseMeasure]
  · rw [measure_toMeasurable]
    exact phaseMeasure_rationalTailExceptionalSet_eq_zero Q0

/-- Increasing the decay exponent decreases the scale. -/
theorem scaleTerm_antitone
    {s t : ℝ} (hst : s ≤ t) (m N : ℕ) :
    scaleTerm t m N ≤ scaleTerm s m N := by
  unfold scaleTerm
  have hexp : -t * (m : ℝ) ≤ -s * (m : ℝ) := by
    exact mul_le_mul_of_nonneg_right (neg_le_neg hst) (Nat.cast_nonneg m)
  have hrpow : (10 : ℝ) ^ (-t * (m : ℝ)) ≤
      (10 : ℝ) ^ (-s * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  gcongr

/-- Finitely many exceptional positive-integer pairs can be absorbed into one
bound selected before all `m,N`. -/
theorem finite_tail_violations_uniform_bound
    (t : ℝ) (Q0 : ℕ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hfinite : {z : ℕ × ℕ |
      α ∈ tailBadSet t Q0 (z.1 + 1) (z.2 + 1)}.Finite) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        restrictedPhaseL1 8 1 Q0 m N α ≤
          B * (decimalFrequency m : ℝ) * scaleTerm t m N := by
  let E : Set (ℕ × ℕ) := {z : ℕ × ℕ |
    α ∈ tailBadSet t Q0 (z.1 + 1) (z.2 + 1)}
  have hE : E.Finite := by
    simpa [E] using hfinite
  let ratio : ℕ × ℕ → ℝ := fun z =>
    restrictedPhaseL1 8 1 Q0 (z.1 + 1) (z.2 + 1) α /
      ((decimalFrequency (z.1 + 1) : ℝ) *
        scaleTerm t (z.1 + 1) (z.2 + 1))
  let B : ℝ := 2 + ∑ z ∈ hE.toFinset, ratio z
  have hratio_nonneg : ∀ z, 0 ≤ ratio z := by
    intro z
    dsimp [ratio]
    exact div_nonneg (by unfold restrictedPhaseL1; positivity)
      (mul_nonneg (by positivity)
        (scaleTerm_pos (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero _))).le)
  have hsum_nonneg : 0 ≤ ∑ z ∈ hE.toFinset, ratio z := by
    exact Finset.sum_nonneg fun z _ => hratio_nonneg z
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro m N hm hN
  let z : ℕ × ℕ := (m - 1, N - 1)
  have hzm : z.1 + 1 = m := by
    dsimp [z]
    omega
  have hzN : z.2 + 1 = N := by
    dsimp [z]
    omega
  have hH : 0 < (decimalFrequency m : ℝ) := by
    dsimp [decimalFrequency]
    positivity
  have hT : 0 < scaleTerm t m N := scaleTerm_pos hN
  have hden : 0 < (decimalFrequency m : ℝ) * scaleTerm t m N :=
    mul_pos hH hT
  by_cases hzbad : z ∈ E
  · have hzmem : z ∈ hE.toFinset := by
      simpa using hzbad
    have hsingle : ratio z ≤ ∑ w ∈ hE.toFinset, ratio w :=
      Finset.single_le_sum
        (f := ratio)
        (fun w _ => hratio_nonneg w) hzmem
    have hratioB : ratio z ≤ B := by
      dsimp [B]
      linarith
    have hdiv : restrictedPhaseL1 8 1 Q0 m N α /
          ((decimalFrequency m : ℝ) * scaleTerm t m N) ≤ B := by
      simpa [ratio, hzm, hzN] using hratioB
    have hmul := (div_le_iff₀ hden).mp hdiv
    nlinarith
  · have hnotBad : α ∉ tailBadSet t Q0 m N := by
      simpa [E, hzm, hzN] using hzbad
    have hthreshold : restrictedPhaseL1 8 1 Q0 m N α ≤
        2 * (decimalFrequency m : ℝ) * scaleTerm t m N := by
      exact le_of_not_gt fun hgt => hnotBad ⟨hα, hgt⟩
    have h2B : (2 : ℝ) ≤ B := by
      dsimp [B]
      linarith
    calc
      restrictedPhaseL1 8 1 Q0 m N α ≤
          2 * (decimalFrequency m : ℝ) * scaleTerm t m N := hthreshold
      _ ≤ B * (decimalFrequency m : ℝ) * scaleTerm t m N := by
        gcongr

/-- Every phase in the full-measure set satisfies the uniform scale-matched
L1 estimate for every real exponent `s` in `(0,1)`. The constant is selected
after `α,s` and before all positive integers `m,N`. -/
theorem fullMeasurePhaseSet_scaleMatchedL1 (Q0 : ℕ) :
    ∀ α ∈ fullMeasurePhaseSet Q0,
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ B : ℝ, 1 ≤ B ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            restrictedPhaseL1 8 1 Q0 m N α ≤
              B * (decimalFrequency m : ℝ) * scaleTerm s m N := by
  intro α hα s hs0 hs1
  obtain ⟨t : ℚ, hst, ht1⟩ := exists_rat_btwn hs1
  have ht0 : (0 : ℝ) < (t : ℝ) := hs0.trans hst
  have htRat0 : (0 : ℚ) < t := by exact_mod_cast ht0
  have htRat1 : t < (1 : ℚ) := by exact_mod_cast ht1
  have hnotAll : α ∉ rationalTailExceptionalSet Q0 := by
    intro hmem
    exact hα.2 (subset_toMeasurable phaseMeasure _ hmem)
  have hnotTail : α ∉ tailExceptionalSet (t : ℝ) Q0 := by
    intro hmem
    apply hnotAll
    rw [rationalTailExceptionalSet]
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    simpa [htRat0, htRat1] using hmem
  have hfinite : {z : ℕ × ℕ |
      α ∈ tailBadSet (t : ℝ) Q0 (z.1 + 1) (z.2 + 1)}.Finite := by
    by_contra hnotFinite
    apply hnotTail
    exact hnotFinite
  obtain ⟨B, hB, hbound⟩ :=
    finite_tail_violations_uniform_bound (t : ℝ) Q0 α
      (fullMeasurePhaseSet_subset_Ico Q0 hα) hfinite
  refine ⟨B, hB, ?_⟩
  intro m N hm hN
  calc
    restrictedPhaseL1 8 1 Q0 m N α ≤
        B * (decimalFrequency m : ℝ) * scaleTerm (t : ℝ) m N :=
      hbound m N hm hN
    _ ≤ B * (decimalFrequency m : ℝ) * scaleTerm s m N := by
      gcongr
      exact scaleTerm_antitone hst.le m N

/-- Main T18 result. This is only the Lebesgue-almost-everywhere variable
phase sibling. Its theorem type displays the exact restricted ordered T8
domain, the inclusive frequencies `1 ≤ h ≤ 10^m`, the probability measure,
and the `∀ s, ∃ B, ∀ m,N` quantifier order. -/
theorem almostEverywhere_scaleMatchedL1_sibling (Q0 : ℕ) :
    MeasurableSet (fullMeasurePhaseSet Q0) ∧
    phaseMeasure (fullMeasurePhaseSet Q0) = 1 ∧
    fullMeasurePhaseSet Q0 ⊆ Set.Ico (0 : ℝ) 1 ∧
    ∀ α ∈ fullMeasurePhaseSet Q0,
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ B : ℝ, 1 ≤ B ∧
          ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
            (∑ h ∈ Finset.Icc 1 (decimalFrequency m),
              ‖∑ q ∈ orderedLongPairDomain (8 : ℝ) 1 Q0 m N,
                Theory.PiDigits.T27.phase (h : ℤ)
                  ((orderedPhaseFrequency q : ℝ) * α)‖) ≤
              B * (decimalFrequency m : ℝ) *
                ((N : ℝ) + (N : ℝ) ^ 2 *
                  (10 : ℝ) ^ (-s * (m : ℝ))) := by
  refine ⟨measurableSet_fullMeasurePhaseSet Q0,
    phaseMeasure_fullMeasurePhaseSet Q0,
    fullMeasurePhaseSet_subset_Ico Q0, ?_⟩
  intro α hα s hs0 hs1
  obtain ⟨B, hB, hbound⟩ :=
    fullMeasurePhaseSet_scaleMatchedL1 Q0 α hα s hs0 hs1
  refine ⟨B, hB, ?_⟩
  intro m N hm hN
  simpa [restrictedPhaseL1, restrictedPhaseSum, scaleTerm] using
    hbound m N hm hN

/-- Fully unfolded form of `Tail(t)`, displaying `K_t = 2`,
`C_t = 127758496`, `p_t = 4`, the restricted ordered T8 domain, and the
inclusive frequency interval in the theorem type. -/
theorem tail_estimate_explicit
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (Q0 m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    phaseMeasure.real
      (Set.Ico (0 : ℝ) 1 ∩
        {α | 2 * (decimalFrequency m : ℝ) *
            ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-t * (m : ℝ))) <
          ∑ h ∈ Finset.Icc 1 (decimalFrequency m),
            ‖∑ q ∈ orderedLongPairDomain (8 : ℝ) 1 Q0 m N,
              Theory.PiDigits.T27.phase (h : ℤ)
                ((orderedPhaseFrequency q : ℝ) * α)‖}) ≤
      127758496 /
        ((decimalFrequency m : ℝ) *
          (1 + (N : ℝ) *
            (10 : ℝ) ^ (-t * (m : ℝ))) ^ 4) := by
  simpa [tailBadSet, restrictedPhaseL1, restrictedPhaseSum, scaleTerm] using
    tail_estimate t ht0 ht1 Q0 m N hm hN

#print axioms tail_estimate_explicit
#print axioms phaseMeasure_tailExceptionalSet_eq_zero
#print axioms phaseMeasure_fullMeasurePhaseSet
#print axioms almostEverywhere_scaleMatchedL1_sibling

end Theory.PiDigits.LongLagBlockCollisionDecay.T18
