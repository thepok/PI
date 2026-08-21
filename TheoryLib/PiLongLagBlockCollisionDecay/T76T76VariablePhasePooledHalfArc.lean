import TheoryLib.PiLongLagBlockCollisionDecay.T18T18AlmostEverywhereScaleMatchedL1
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc

/-!
# T76: variable-phase pooled one-sided half-arc sibling

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

This module proves only a Lebesgue-almost-everywhere variable-phase sibling of
T69's residual-A12, `m = 1`, dyadic pooled aggregate. It proves no estimate at
`Real.pi`, no full T29 predicate, and none of C1, C2, or C3.
-/

noncomputable section

set_option maxHeartbeats 800000

open Finset Set MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate Real

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T76

open Theory.PiDigits.LongLagBlockCollisionDecay.T16
open Theory.PiDigits.LongLagBlockCollisionDecay.T18
open Theory.PiDigits.LongLagBlockCollisionDecay.T66
open Theory.PiDigits.LongLagBlockCollisionDecay.T68
open Theory.PiDigits.LongLagBlockCollisionDecay.T69

/-- The positive integer character in the exact T69 `h/r/k` domain. -/
def pooledFrequency (h r k : ℕ) : ℕ := h * (10 ^ r - 1) * 10 ^ k

/-- T69's triangularly weighted pooled sum after replacing only its prescribed
phase by the real variable `α`. -/
def variablePooledSum (t : ℕ) (α : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℂ) *
        ∑ k ∈ Finset.range (N t - r),
          Theory.PiDigits.T27.phase 1 ((pooledFrequency h r k : ℝ) * α)

/-- The one-sided real quantity needed by the phase-substituted T69 aggregate. -/
def variablePooledReal (t : ℕ) (α : ℝ) : ℝ := (variablePooledSum t α).re

/-- T69's exact aggregate identity with only the prescribed phase replaced. -/
def variableAggregateEnergy (t : ℕ) (α : ℝ) : ℝ :=
  10 * (H t : ℝ) * N t + 2 * variablePooledReal t α

/-- The variable-phase orbit point used in the unchanged T68/T69 half-arc
interface. -/
def variableShiftedOrbitPoint (α : ℝ) (h r k : ℕ) : UnitAddCircle :=
  (((pooledFrequency h r k : ℝ) * α : ℝ) : UnitAddCircle)

/-- The multiplicity-retaining pooled excess in the centered half-open
half-arc `[-1/4,1/4)` represented inside `[-1/2,1/2)`. -/
def variableCombinedHalfArcExcess
    (t : ℕ) (α : ℝ) (y : UnitAddCircle) : ℝ :=
  ∑ h ∈ Finset.Icc (1 : ℕ) 10,
    ∑ r ∈ Finset.Ico 1 (H t),
      ((H t - r : ℕ) : ℝ) *
        halfArcExcess (N t - r) (variableShiftedOrbitPoint α h r) y

/-- Remove the unique full factor ten from the inclusive endpoint `h = 10`. -/
def primitiveMultiplier (h : ℕ) : ℕ := if h = 10 then 1 else h

/-- Move that factor ten into the orbit exponent. -/
def effectiveExponent (h k : ℕ) : ℕ := if h = 10 then k + 1 else k

theorem pooledFrequency_normalized
    {h : ℕ} (hh1 : 1 ≤ h) (hh10 : h ≤ 10) (r k : ℕ) :
    pooledFrequency h r k =
      10 ^ effectiveExponent h k *
        (primitiveMultiplier h * (10 ^ r - 1)) := by
  interval_cases h <;> simp [pooledFrequency, effectiveExponent,
    primitiveMultiplier, pow_succ] <;> ring

theorem primitiveMultiplier_bounds
    {h : ℕ} (hh1 : 1 ≤ h) (hh10 : h ≤ 10) :
    1 ≤ primitiveMultiplier h ∧ primitiveMultiplier h ≤ 9 := by
  interval_cases h <;> simp [primitiveMultiplier]

theorem repunit_mod_ten {r : ℕ} (hr : 1 ≤ r) :
    (10 ^ r - 1) % 10 = 9 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [Nat.add_comm 1 s, pow_succ]
  have hpow : 1 ≤ 10 ^ s := one_le_pow₀ (by norm_num)
  have heq : 10 ^ s * 10 - 1 = 10 * (10 ^ s - 1) + 9 := by omega
  rw [heq, Nat.add_mod]
  norm_num

theorem primitiveMultiplier_repunit_not_dvd
    {h r : ℕ} (hh1 : 1 ≤ h) (hh10 : h ≤ 10) (hr : 1 ≤ r) :
    ¬10 ∣ primitiveMultiplier h * (10 ^ r - 1) := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, repunit_mod_ten hr]
  interval_cases h <;> norm_num [primitiveMultiplier]

theorem scaled_repunit_unique
    {a b r s : ℕ} (ha1 : 1 ≤ a) (ha9 : a ≤ 9)
    (hb1 : 1 ≤ b) (hb9 : b ≤ 9) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (heq : a * (10 ^ r - 1) = b * (10 ^ s - 1)) :
    r = s ∧ a = b := by
  have hrepr : 0 < 10 ^ r - 1 := by
    have := Nat.one_lt_pow (Nat.ne_of_gt hr) (by norm_num : 1 < 10)
    omega
  have hreps : 0 < 10 ^ s - 1 := by
    have := Nat.one_lt_pow (Nat.ne_of_gt hs) (by norm_num : 1 < 10)
    omega
  have hrs : r = s := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · have hrs' : r + 1 ≤ s := by omega
      have hpow : 10 ^ (r + 1) ≤ 10 ^ s :=
        Nat.pow_le_pow_right (by norm_num) hrs'
      have hgap : 9 * (10 ^ r - 1) < 10 ^ (r + 1) - 1 := by
        rw [pow_succ]
        omega
      have hsmall : b * (10 ^ s - 1) ≤ 9 * (10 ^ r - 1) := by
        rw [← heq]
        exact Nat.mul_le_mul_right _ ha9
      have hlarge : 10 ^ (r + 1) - 1 ≤ b * (10 ^ s - 1) := by
        have hsub : 10 ^ (r + 1) - 1 ≤ 10 ^ s - 1 := Nat.sub_le_sub_right hpow 1
        exact hsub.trans (Nat.le_mul_of_pos_left _ hb1)
      omega
    · have hsr' : s + 1 ≤ r := by omega
      have hpow : 10 ^ (s + 1) ≤ 10 ^ r :=
        Nat.pow_le_pow_right (by norm_num) hsr'
      have hgap : 9 * (10 ^ s - 1) < 10 ^ (s + 1) - 1 := by
        rw [pow_succ]
        omega
      have hsmall : a * (10 ^ r - 1) ≤ 9 * (10 ^ s - 1) := by
        rw [heq]
        exact Nat.mul_le_mul_right _ hb9
      have hlarge : 10 ^ (s + 1) - 1 ≤ a * (10 ^ r - 1) := by
        have hsub : 10 ^ (s + 1) - 1 ≤ 10 ^ r - 1 := Nat.sub_le_sub_right hpow 1
        exact hsub.trans (Nat.le_mul_of_pos_left _ ha1)
      omega
  subst s
  have hcancel : a = b := by
    exact Nat.eq_of_mul_eq_mul_right hrepr heq
  exact ⟨rfl, hcancel⟩

/-- Exhaustive equality-frequency classification. Besides identical triples,
the only class collision is `(1,r,j)` with `(10,r,j-1)` for `j ≥ 1`. -/
theorem pooledFrequency_eq_iff
    {h h' r s k l : ℕ}
    (hh1 : 1 ≤ h) (hh10 : h ≤ 10)
    (hh'1 : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    pooledFrequency h r k = pooledFrequency h' s l ↔
      r = s ∧
        ((h = h' ∧ k = l) ∨
          (h = 1 ∧ h' = 10 ∧ k = l + 1) ∨
          (h = 10 ∧ h' = 1 ∧ l = k + 1)) := by
  constructor
  · intro heq
    rw [pooledFrequency_normalized hh1 hh10,
      pooledFrequency_normalized hh'1 hh'10] at heq
    have hleft0 : primitiveMultiplier h * (10 ^ r - 1) ≠ 0 := by
      have hb := primitiveMultiplier_bounds hh1 hh10
      exact Nat.mul_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb.1))
        (by have := Nat.one_lt_pow (Nat.ne_of_gt hr) (by norm_num : 1 < 10); omega)
    have hright0 : primitiveMultiplier h' * (10 ^ s - 1) ≠ 0 := by
      have hb := primitiveMultiplier_bounds hh'1 hh'10
      exact Nat.mul_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb.1))
        (by have := Nat.one_lt_pow (Nat.ne_of_gt hs) (by norm_num : 1 < 10); omega)
    have hval := congrArg tenValuation heq
    rw [tenValuation_pow_mul_of_not_dvd hleft0
        (primitiveMultiplier_repunit_not_dvd hh1 hh10 hr),
      tenValuation_pow_mul_of_not_dvd hright0
        (primitiveMultiplier_repunit_not_dvd hh'1 hh'10 hs)] at hval
    have hcore : primitiveMultiplier h * (10 ^ r - 1) =
        primitiveMultiplier h' * (10 ^ s - 1) := by
      rw [hval] at heq
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) heq
    have hbounds := primitiveMultiplier_bounds hh1 hh10
    have hbounds' := primitiveMultiplier_bounds hh'1 hh'10
    have hrs := scaled_repunit_unique hbounds.1 hbounds.2
      hbounds'.1 hbounds'.2 hr hs hcore
    refine ⟨hrs.1, ?_⟩
    interval_cases h <;> interval_cases h' <;>
      simp [primitiveMultiplier, effectiveExponent] at hrs hval ⊢ <;> omega
  · rintro ⟨rfl, hsame | hex | hex⟩
    · rcases hsame with ⟨rfl, rfl⟩
      rfl
    · rcases hex with ⟨rfl, rfl, rfl⟩
      simp [pooledFrequency, pow_succ]
      ring
    · rcases hex with ⟨rfl, rfl, rfl⟩
      simp [pooledFrequency, pow_succ]
      ring

/-- Finite-range collision classes, including both boundary singletons:
`(1,r,0)` has no predecessor and `(10,r,L-1)` has no successor. -/
theorem finite_frequencyClass_iff
    {L h h' r k l : ℕ}
    (hh1 : 1 ≤ h) (hh10 : h ≤ 10)
    (hh'1 : 1 ≤ h') (hh'10 : h' ≤ 10)
    (hr : 1 ≤ r) (_hk : k < L) (hl : l < L) :
    pooledFrequency h r k = pooledFrequency h' r l ↔
      (h' = h ∧ l = k) ∨
      (h = 1 ∧ 1 ≤ k ∧ h' = 10 ∧ l + 1 = k) ∨
      (h = 10 ∧ k + 1 < L ∧ h' = 1 ∧ l = k + 1) := by
  rw [pooledFrequency_eq_iff hh1 hh10 hh'1 hh'10 hr hr]
  constructor
  · rintro ⟨_, hsame | hforward | hbackward⟩
    · exact Or.inl ⟨hsame.1.symm, hsame.2.symm⟩
    · rcases hforward with ⟨rfl, rfl, hkl⟩
      exact Or.inr (Or.inl ⟨rfl, by omega, rfl, by omega⟩)
    · rcases hbackward with ⟨rfl, rfl, hlk⟩
      exact Or.inr (Or.inr ⟨rfl, by omega, rfl, hlk⟩)
  · rintro (hsame | hforward | hbackward)
    · exact ⟨rfl, Or.inl ⟨hsame.1.symm, hsame.2.symm⟩⟩
    · rcases hforward with ⟨rfl, hk1, rfl, hlk⟩
      exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, by omega⟩)⟩
    · rcases hbackward with ⟨rfl, hnext, rfl, rfl⟩
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

/-- The same collision classification with every literal T69 finite domain in
the theorem type. -/
theorem literal_T69_frequencyClass_iff
    {t h h' r k l : ℕ}
    (hh : h ∈ Finset.Icc (1 : ℕ) 10)
    (hh' : h' ∈ Finset.Icc (1 : ℕ) 10)
    (hr : r ∈ Finset.Ico 1
      (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))))
    (hk : k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))
    (hl : l ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r)) :
    h * (10 ^ r - 1) * 10 ^ k = h' * (10 ^ r - 1) * 10 ^ l ↔
      (h' = h ∧ l = k) ∨
      (h = 1 ∧ 1 ≤ k ∧ h' = 10 ∧ l + 1 = k) ∨
      (h = 10 ∧ k + 1 < (4 * 2 ^ t + 1 : ℕ) - r ∧
        h' = 1 ∧ l = k + 1) := by
  apply finite_frequencyClass_iff
  · exact (Finset.mem_Icc.mp hh).1
  · exact (Finset.mem_Icc.mp hh).2
  · exact (Finset.mem_Icc.mp hh').1
  · exact (Finset.mem_Icc.mp hh').2
  · exact (Finset.mem_Ico.mp hr).1
  · exact Finset.mem_range.mp hk
  · exact Finset.mem_range.mp hl

/-- One frequency channel, retaining every shift, orbit index, and triangular
weight but fixing `h`. -/
def singleChannelSum (t h : ℕ) (α : ℝ) : ℂ :=
  ∑ r ∈ Finset.Ico 1 (H t),
    ((H t - r : ℕ) : ℂ) *
      ∑ k ∈ Finset.range (N t - r),
        Theory.PiDigits.T27.phase (pooledFrequency h r k : ℤ) α

theorem variablePooledSum_eq_channelSum (t : ℕ) (α : ℝ) :
    variablePooledSum t α =
      ∑ h ∈ Finset.Icc (1 : ℕ) 10, singleChannelSum t h α := by
  unfold variablePooledSum singleChannelSum
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold Theory.PiDigits.T27.phase
  congr 1
  push_cast
  ring

theorem pooledFrequency_fixedMultiplier_injective
    {h r s k l : ℕ} (hh : 1 ≤ h) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (heq : pooledFrequency h r k = pooledFrequency h s l) :
    r = s ∧ k = l := by
  have hbase : 10 ^ k * (10 ^ r - 1) = 10 ^ l * (10 ^ s - 1) := by
    unfold pooledFrequency at heq
    have heq' : h * (10 ^ k * (10 ^ r - 1)) =
        h * (10 ^ l * (10 ^ s - 1)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq'
  have hstruct :
      Theory.PiDigits.PositiveLowerBlockDensity.T25.structuredDenominator k r =
        Theory.PiDigits.PositiveLowerBlockDensity.T25.structuredDenominator l s := by
    simpa [Theory.PiDigits.PositiveLowerBlockDensity.T25.structuredDenominator]
      using hbase
  obtain ⟨hkl, hrs⟩ := structuredDenominator_injective hr hs hstruct
  exact ⟨hrs, hkl⟩

theorem integrable_phase (z : ℤ) :
    Integrable (fun α : ℝ => Theory.PiDigits.T27.phase z α) phaseMeasure := by
  rw [phaseMeasure]
  exact ((by
    unfold Theory.PiDigits.T27.phase
    fun_prop : Continuous (fun α : ℝ => Theory.PiDigits.T27.phase z α)
    ).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self

/-- Finite weighted Parseval on the exact half-open phase probability space. -/
theorem integral_norm_sq_weightedPhase
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (frequency : ι → ℤ) (weight : ι → ℝ)
    (hinj : Set.InjOn frequency (S : Set ι)) :
    (∫ α, ‖∑ i ∈ S,
        (weight i : ℂ) * Theory.PiDigits.T27.phase (frequency i) α‖ ^ 2
      ∂phaseMeasure) = ∑ i ∈ S, weight i ^ 2 := by
  have hexpand (α : ℝ) :
      ((‖∑ i ∈ S,
          (weight i : ℂ) * Theory.PiDigits.T27.phase (frequency i) α‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ S, ∑ j ∈ S,
          ((weight i : ℂ) * (weight j : ℂ)) *
            Theory.PiDigits.T27.phase (frequency j - frequency i) α := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.conj_ofReal]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (weight i : ℂ) * conj (Theory.PiDigits.T27.phase (frequency i) α) *
          ((weight j : ℂ) * Theory.PiDigits.T27.phase (frequency j) α) =
          ((weight i : ℂ) * (weight j : ℂ)) *
            (conj (Theory.PiDigits.T27.phase (frequency i) α) *
              Theory.PiDigits.T27.phase (frequency j) α) := by ring
      _ = ((weight i : ℂ) * (weight j : ℂ)) *
          Theory.PiDigits.T27.phase (frequency j - frequency i) α := by
            rw [Theory.PiDigits.T27.phase_sub]
  have hcomplex :
      (∫ α, ((‖∑ i ∈ S,
          (weight i : ℂ) * Theory.PiDigits.T27.phase (frequency i) α‖ ^ 2 : ℝ) : ℂ)
        ∂phaseMeasure) = ((∑ i ∈ S, weight i ^ 2 : ℝ) : ℂ) := by
    rw [integral_congr_ae (ae_of_all phaseMeasure hexpand)]
    rw [MeasureTheory.integral_finsetSum]
    · calc
        (∑ i ∈ S, ∫ α,
            ∑ j ∈ S,
              ((weight i : ℂ) * (weight j : ℂ)) *
                Theory.PiDigits.T27.phase (frequency j - frequency i) α
            ∂phaseMeasure) =
            ∑ i ∈ S, ((weight i : ℂ) * (weight i : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [MeasureTheory.integral_finsetSum]
          · calc
              (∑ j ∈ S, ∫ α,
                  ((weight i : ℂ) * (weight j : ℂ)) *
                    Theory.PiDigits.T27.phase (frequency j - frequency i) α
                  ∂phaseMeasure) =
                  ∑ j ∈ S, if i = j then
                    ((weight i : ℂ) * (weight i : ℂ)) else 0 := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [integral_const_mul, integral_phaseMeasure_phase]
                by_cases hij : i = j
                · subst j
                  simp
                · have hfreq : frequency j ≠ frequency i := by
                    intro heq
                    exact hij (hinj hj hi heq).symm
                  simp [hij, sub_eq_zero, hfreq]
              _ = (weight i : ℂ) * (weight i : ℂ) := by
                simp [hi]
          · intro j hj
            simpa only [mul_assoc] using
              (integrable_phase (frequency j - frequency i)).const_mul
                ((weight i : ℂ) * (weight j : ℂ))
        _ = ((∑ i ∈ S, weight i ^ 2 : ℝ) : ℂ) := by
          push_cast
          apply Finset.sum_congr rfl
          intro i hi
          ring
    · intro i hi
      apply integrable_finsetSum
      intro j hj
      simpa only [mul_assoc] using
        (integrable_phase (frequency j - frequency i)).const_mul
          ((weight i : ℂ) * (weight j : ℂ))
  rw [integral_complex_ofReal] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- The dependent finite domain `1 ≤ r < H_t`, `k < N_t-r`. -/
def channelIndexDomain (t : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.Ico 1 (H t)).sigma fun r => Finset.range (N t - r)

/-- The exact one-channel second-moment constant before estimating it. -/
def channelMoment (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 (H t),
    ((N t - r : ℕ) : ℝ) * ((H t - r : ℕ) : ℝ) ^ 2

theorem singleChannelSum_sigma (t h : ℕ) (α : ℝ) :
    singleChannelSum t h α =
      ∑ p ∈ channelIndexDomain t,
        (((H t - p.1 : ℕ) : ℝ) : ℂ) *
          Theory.PiDigits.T27.phase (pooledFrequency h p.1 p.2 : ℤ) α := by
  unfold singleChannelSum channelIndexDomain
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  simp

/-- Exact finite second moment in one fixed frequency channel. -/
theorem integral_singleChannelSum_norm_sq
    (t h : ℕ) (hh : h ∈ Finset.Icc (1 : ℕ) 10) :
    (∫ α, ‖singleChannelSum t h α‖ ^ 2 ∂phaseMeasure) = channelMoment t := by
  have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
  let S := channelIndexDomain t
  let frequency : (Sigma fun _ : ℕ => ℕ) → ℤ := fun p =>
    (pooledFrequency h p.1 p.2 : ℤ)
  let weight : (Sigma fun _ : ℕ => ℕ) → ℝ := fun p =>
    ((H t - p.1 : ℕ) : ℝ)
  have hinj : Set.InjOn frequency (S : Set (Sigma fun _ : ℕ => ℕ)) := by
    rintro ⟨r, k⟩ hp ⟨s, l⟩ hq heq
    change ⟨r, k⟩ ∈ S at hp
    change ⟨s, l⟩ ∈ S at hq
    simp only [S, channelIndexDomain, Finset.mem_sigma, Finset.mem_Ico,
      Finset.mem_range] at hp hq
    have heqNat : pooledFrequency h r k = pooledFrequency h s l := by
      change (pooledFrequency h r k : ℤ) = pooledFrequency h s l at heq
      exact_mod_cast heq
    obtain ⟨hrs, hkl⟩ := pooledFrequency_fixedMultiplier_injective
      hh1 hp.1.1 hq.1.1 heqNat
    subst s
    subst l
    rfl
  have hparseval := integral_norm_sq_weightedPhase S frequency weight hinj
  calc
    (∫ α, ‖singleChannelSum t h α‖ ^ 2 ∂phaseMeasure) =
        ∫ α, ‖∑ p ∈ S,
          (weight p : ℂ) * Theory.PiDigits.T27.phase (frequency p) α‖ ^ 2
          ∂phaseMeasure := by
            apply integral_congr_ae
            filter_upwards [] with α
            rw [singleChannelSum_sigma]
    _ = ∑ p ∈ S, weight p ^ 2 := hparseval
    _ = channelMoment t := by
      unfold channelMoment S weight channelIndexDomain
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem channelMoment_le (t : ℕ) :
    channelMoment t ≤ (N t : ℝ) * (H t : ℝ) ^ 3 := by
  unfold channelMoment
  calc
    (∑ r ∈ Finset.Ico 1 (H t),
        ((N t - r : ℕ) : ℝ) * ((H t - r : ℕ) : ℝ) ^ 2) ≤
        ∑ _r ∈ Finset.Ico 1 (H t),
          (N t : ℝ) * (H t : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro r hr
            have hNr : ((N t - r : ℕ) : ℝ) ≤ N t := by exact_mod_cast Nat.sub_le _ _
            have hHr : ((H t - r : ℕ) : ℝ) ≤ H t := by exact_mod_cast Nat.sub_le _ _
            have hHr0 : (0 : ℝ) ≤ (H t - r : ℕ) := by positivity
            have hH0 : (0 : ℝ) ≤ H t := by positivity
            gcongr
    _ = ((Finset.Ico 1 (H t)).card : ℝ) *
        ((N t : ℝ) * (H t : ℝ) ^ 2) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H t : ℝ) * ((N t : ℝ) * (H t : ℝ) ^ 2) := by
          gcongr
          simp only [Nat.card_Ico]
          exact_mod_cast Nat.sub_le (H t) 1
    _ = (N t : ℝ) * (H t : ℝ) ^ 3 := by ring

/-- Pointwise Cauchy-Schwarz over the ten inclusive channels. -/
theorem variablePooledReal_sq_le (t : ℕ) (α : ℝ) :
    variablePooledReal t α ^ 2 ≤
      10 * ∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖ ^ 2 := by
  have hrepr : |variablePooledReal t α| ≤ ‖variablePooledSum t α‖ :=
    Complex.abs_re_le_norm _
  have hsum : ‖variablePooledSum t α‖ ≤
      ∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖ := by
    rw [variablePooledSum_eq_channelSum]
    exact norm_sum_le _ _
  have hnonneg : 0 ≤ ∑ h ∈ Finset.Icc (1 : ℕ) 10,
      ‖singleChannelSum t h α‖ := by positivity
  calc
    variablePooledReal t α ^ 2 = |variablePooledReal t α| ^ 2 := by
      rw [sq_abs]
    _ ≤ ‖variablePooledSum t α‖ ^ 2 := by gcongr
    _ ≤ (∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖) ^ 2 := by
      gcongr
    _ ≤ ((Finset.Icc (1 : ℕ) 10).card : ℝ) *
        ∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = 10 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ‖singleChannelSum t h α‖ ^ 2 := by norm_num

theorem continuous_singleChannelSum (t h : ℕ) :
    Continuous (singleChannelSum t h) := by
  unfold singleChannelSum Theory.PiDigits.T27.phase pooledFrequency
  fun_prop

theorem continuous_variablePooledReal (t : ℕ) :
    Continuous (variablePooledReal t) := by
  unfold variablePooledReal variablePooledSum Theory.PiDigits.T27.phase pooledFrequency
  fun_prop

/-- Explicit finite second-moment bound for the complete pooled real sum. -/
theorem integral_variablePooledReal_sq_le (t : ℕ) :
    (∫ α, variablePooledReal t α ^ 2 ∂phaseMeasure) ≤
      100 * (N t : ℝ) * (H t : ℝ) ^ 3 := by
  let upper : ℝ → ℝ := fun α =>
    10 * ∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖ ^ 2
  have hlowerInt : Integrable (fun α => variablePooledReal t α ^ 2) phaseMeasure := by
    rw [phaseMeasure]
    exact ((continuous_variablePooledReal t).pow 2).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hupperInt : Integrable upper phaseMeasure := by
    rw [phaseMeasure]
    have hsum : Continuous (fun α =>
        ∑ h ∈ Finset.Icc (1 : ℕ) 10, ‖singleChannelSum t h α‖ ^ 2) := by
      apply continuous_finsetSum
      intro h hh
      exact (continuous_singleChannelSum t h).norm.pow 2
    exact ((continuous_const.mul hsum : Continuous upper).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self
  have hpoint : ∀ᵐ α ∂phaseMeasure,
      variablePooledReal t α ^ 2 ≤ upper α :=
    ae_of_all phaseMeasure (variablePooledReal_sq_le t)
  calc
    (∫ α, variablePooledReal t α ^ 2 ∂phaseMeasure) ≤
        ∫ α, upper α ∂phaseMeasure := integral_mono_ae hlowerInt hupperInt hpoint
    _ = 10 * ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        (∫ α, ‖singleChannelSum t h α‖ ^ 2 ∂phaseMeasure) := by
          unfold upper
          rw [integral_const_mul, MeasureTheory.integral_finsetSum]
          intro h hh
          rw [phaseMeasure]
          exact ((continuous_singleChannelSum t h).norm.pow 2).integrableOn_Icc.mono_set
            Set.Ico_subset_Icc_self
    _ = 100 * channelMoment t := by
          calc
            10 * (∑ h ∈ Finset.Icc (1 : ℕ) 10,
                ∫ α, ‖singleChannelSum t h α‖ ^ 2 ∂phaseMeasure) =
                10 * ∑ _h ∈ Finset.Icc (1 : ℕ) 10, channelMoment t := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro h hh
                  exact integral_singleChannelSum_norm_sq t h hh
            _ = 100 * channelMoment t := by
              simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              norm_num
              ring
    _ ≤ 100 * ((N t : ℝ) * (H t : ℝ) ^ 3) := by
          gcongr
          exact channelMoment_le t
    _ = 100 * (N t : ℝ) * (H t : ℝ) ^ 3 := by ring

/-- Fully literal second-moment bound, exposing the complete T69 pooled sum
and the moment constant `100`. -/
theorem literal_secondMoment_le (t : ℕ) :
    (∫ α,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℂ) *
            ∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
              Theory.PiDigits.T27.phase 1
                (((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α)).re ^ 2
      ∂phaseMeasure) ≤
        100 * (4 * 2 ^ t + 1 : ℕ) *
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) ^ 3 := by
  simpa only [variablePooledReal, variablePooledSum, pooledFrequency, N, H] using
    integral_variablePooledReal_sq_le t

/-- The one-sided bad event at scale `t`, explicitly restricted to `[0,1)`. -/
def pooledBadSet (t : ℕ) : Set ℝ :=
  Set.Ico (0 : ℝ) 1 ∩
    {α | (H t : ℝ) * N t < variablePooledReal t α}

/-- Phases lying in infinitely many exact one-sided pooled bad events. -/
def pooledExceptionalSet : Set ℝ :=
  {α | {t : ℕ | α ∈ pooledBadSet t}.Infinite}

theorem pooledBadSet_measureReal_le (t : ℕ) :
    phaseMeasure.real (pooledBadSet t) ≤ 100 * (H t : ℝ) / N t := by
  let ε : ℝ := ((H t : ℝ) * N t) ^ 2
  let deviation : Set ℝ := {α | ε ≤ variablePooledReal t α ^ 2}
  have hH : (0 : ℝ) < H t := by exact_mod_cast H_pos t
  have hN : (0 : ℝ) < N t := by exact_mod_cast (lt_of_lt_of_le (by omega) (five_le_N t))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsubset : pooledBadSet t ⊆ deviation := by
    intro α hα
    dsimp [deviation, ε]
    have hpos : 0 ≤ variablePooledReal t α :=
      (mul_pos hH hN).le.trans hα.2.le
    exact (sq_le_sq₀ (mul_pos hH hN).le hpos).2 hα.2.le
  have hint : Integrable (fun α => variablePooledReal t α ^ 2) phaseMeasure := by
    rw [phaseMeasure]
    exact ((continuous_variablePooledReal t).pow 2).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hmarkov : ε * phaseMeasure.real deviation ≤
      ∫ α, variablePooledReal t α ^ 2 ∂phaseMeasure :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all phaseMeasure fun α => sq_nonneg (variablePooledReal t α)) hint ε
  have hmono : phaseMeasure.real (pooledBadSet t) ≤
      phaseMeasure.real deviation := measureReal_mono hsubset
  have hvariance := integral_variablePooledReal_sq_le t
  have hscaled : ε * phaseMeasure.real (pooledBadSet t) ≤
      100 * (N t : ℝ) * (H t : ℝ) ^ 3 := by
    calc
      ε * phaseMeasure.real (pooledBadSet t) ≤
          ε * phaseMeasure.real deviation := mul_le_mul_of_nonneg_left hmono hε.le
      _ ≤ ∫ α, variablePooledReal t α ^ 2 ∂phaseMeasure := hmarkov
      _ ≤ 100 * (N t : ℝ) * (H t : ℝ) ^ 3 := hvariance
  apply (le_div_iff₀ hN).2
  have hm : 0 ≤ phaseMeasure.real (pooledBadSet t) := measureReal_nonneg
  dsimp [ε] at hscaled
  nlinarith [mul_pos (sq_pos_of_pos hH) hN]

/-- Fully literal one-sided tail bound for the exact bad event. -/
theorem literal_pooledBadSet_measureReal_le (t : ℕ) :
    phaseMeasure.real
      (Set.Ico (0 : ℝ) 1 ∩
        {α |
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
              (4 * 2 ^ t + 1 : ℕ) <
            (∑ h ∈ Finset.Icc (1 : ℕ) 10,
              ∑ r ∈ Finset.Ico 1
                  (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
                ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℂ) *
                  ∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                    Theory.PiDigits.T27.phase 1
                      (((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α)).re}) ≤
      100 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) /
        (4 * 2 ^ t + 1 : ℕ) := by
  simpa only [pooledBadSet, variablePooledReal, variablePooledSum,
    pooledFrequency, N, H] using pooledBadSet_measureReal_le t

theorem sqrtTwo_pow_sq (t : ℕ) :
    ((Real.sqrt 2) ^ t) ^ 2 = ((2 ^ t : ℕ) : ℝ) := by
  rw [← pow_mul, show t * 2 = 2 * t by omega, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The dyadic ceiling ratio is dominated by an explicit geometric sequence. -/
theorem H_div_N_le_geometric (t : ℕ) :
    (H t : ℝ) / N t ≤ (Real.sqrt 2)⁻¹ ^ t := by
  let s : ℝ := Real.sqrt (N t : ℝ)
  let a : ℝ := (Real.sqrt 2) ^ t
  have hN : (0 : ℝ) < N t := by exact_mod_cast (lt_of_lt_of_le (by omega) (five_le_N t))
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 hN
  have ha : 0 < a := by dsimp [a]; positivity
  have hs_sq : s ^ 2 = (N t : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hN.le
  have ha_sq : a ^ 2 = ((2 ^ t : ℕ) : ℝ) := by
    exact sqrtTwo_pow_sq t
  have halower : 2 * a ≤ s := by
    dsimp [s]
    apply (Real.le_sqrt (by positivity) hN.le).2
    calc
      (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      _ = 4 * ((2 ^ t : ℕ) : ℝ) := by rw [ha_sq]
      _ ≤ 4 * ((2 ^ t : ℕ) : ℝ) + 1 := by norm_num
      _ = (N t : ℝ) := by simp [N]
  have hs1 : 1 ≤ s := by
    have hN1 : (1 : ℝ) ≤ N t := by exact_mod_cast (le_trans (by omega) (five_le_N t))
    nlinarith
  have hH : (H t : ℝ) ≤ 2 * s := by
    have hceil := H_lt_sqrt_N_add_one t
    dsimp [s]
    nlinarith
  have hratio : (H t : ℝ) / N t ≤ 2 / s := by
    apply (div_le_iff₀ hN).2
    rw [← hs_sq]
    have heq : (2 / s) * s ^ 2 = 2 * s := by field_simp
    rw [heq]
    exact hH
  have hgeom : 2 / s ≤ 1 / a := by
    exact (div_le_div_iff₀ hs ha).2 (by simpa using halower)
  calc
    (H t : ℝ) / N t ≤ 2 / s := hratio
    _ ≤ 1 / a := hgeom
    _ = (Real.sqrt 2)⁻¹ ^ t := by simp [a, one_div, inv_pow]

theorem summable_pooledBadSet_measureReal :
    Summable (fun t => phaseMeasure.real (pooledBadSet t)) := by
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : 1 < Real.sqrt 2 := by
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ hsqrt
  have hgeom : Summable (fun t : ℕ => 100 * q ^ t) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left 100
  apply hgeom.of_nonneg_of_le (fun _ => measureReal_nonneg)
  intro t
  calc
    phaseMeasure.real (pooledBadSet t) ≤ 100 * (H t : ℝ) / N t :=
      pooledBadSet_measureReal_le t
    _ = 100 * ((H t : ℝ) / N t) := by ring
    _ ≤ 100 * q ^ t := by
      gcongr
      simpa [q] using H_div_N_le_geometric t

/-- First Borel-Cantelli for the exact all-scale pooled bad events. -/
theorem phaseMeasure_pooledExceptionalSet_eq_zero :
    phaseMeasure pooledExceptionalSet = 0 := by
  have hreal := summable_pooledBadSet_measureReal
  have heq :
      (fun t => ENNReal.ofReal (phaseMeasure.real (pooledBadSet t))) =
        (fun t => phaseMeasure (pooledBadSet t)) := by
    funext t
    exact ofReal_measureReal
  have hsum : (∑' t, phaseMeasure (pooledBadSet t)) ≠ ∞ := by
    rw [← heq]
    exact hreal.tsum_ofReal_ne_top
  have hfinite : ∀ᵐ α ∂phaseMeasure,
      {t : ℕ | α ∈ pooledBadSet t}.Finite := ae_finite_setOf_mem hsum
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hfinite] with α hα
  exact fun hinfinite => hinfinite hα

/-- A measurable full-measure subset of the literal phase interval. -/
def pooledGoodPhaseSet : Set ℝ :=
  Set.Ico (0 : ℝ) 1 \ toMeasurable phaseMeasure pooledExceptionalSet

theorem pooledGoodPhaseSet_spec :
    MeasurableSet pooledGoodPhaseSet ∧
      phaseMeasure pooledGoodPhaseSet = 1 ∧
      pooledGoodPhaseSet ⊆ Set.Ico (0 : ℝ) 1 := by
  refine ⟨measurableSet_Ico.diff (measurableSet_toMeasurable _ _), ?_, Set.diff_subset⟩
  rw [pooledGoodPhaseSet, measure_diff_null]
  · simp [phaseMeasure]
  · rw [measure_toMeasurable]
    exact phaseMeasure_pooledExceptionalSet_eq_zero

/-- Finitely many early bad scales are absorbed into one finite constant
chosen before every natural scale. -/
theorem finite_pooledBadSet_uniform_bound
    (α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hfinite : {t : ℕ | α ∈ pooledBadSet t}.Finite) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ,
      variablePooledReal t α ≤ C * (H t : ℝ) * N t := by
  let E : Set ℕ := {t : ℕ | α ∈ pooledBadSet t}
  have hE : E.Finite := by simpa [E] using hfinite
  let ratio : ℕ → ℝ := fun t =>
    variablePooledReal t α / ((H t : ℝ) * N t)
  let C : ℝ := 1 + ∑ t ∈ hE.toFinset, max 0 (ratio t)
  have hterm : ∀ t, 0 ≤ max 0 (ratio t) := fun t => le_max_left _ _
  have hsum : 0 ≤ ∑ t ∈ hE.toFinset, max 0 (ratio t) :=
    Finset.sum_nonneg fun t ht => hterm t
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t
  have hH : (0 : ℝ) < H t := by exact_mod_cast H_pos t
  have hN : (0 : ℝ) < N t := by exact_mod_cast (lt_of_lt_of_le (by omega) (five_le_N t))
  have hden : 0 < (H t : ℝ) * N t := mul_pos hH hN
  by_cases ht : t ∈ E
  · have htFin : t ∈ hE.toFinset := by simpa using ht
    have hsingle : max 0 (ratio t) ≤
        ∑ j ∈ hE.toFinset, max 0 (ratio j) :=
      Finset.single_le_sum (fun j hj => hterm j) htFin
    have hratio : ratio t ≤ C := by
      exact (le_max_right 0 (ratio t)).trans (by dsimp [C]; linarith)
    have hdiv : variablePooledReal t α / ((H t : ℝ) * N t) ≤ C := by
      simpa [ratio] using hratio
    have hmul := (div_le_iff₀ hden).mp hdiv
    nlinarith
  · have hnotBad : α ∉ pooledBadSet t := by simpa [E] using ht
    have hone : variablePooledReal t α ≤ (H t : ℝ) * N t := by
      exact le_of_not_gt fun hgt => hnotBad ⟨hα, hgt⟩
    calc
      variablePooledReal t α ≤ (H t : ℝ) * N t := hone
      _ ≤ C * (H t : ℝ) * N t := by nlinarith

/-- The almost-everywhere all-scale one-sided pooled sibling. The theorem type
displays `N_t`, `H_t`, all ten frequencies, every strict shift and orbit range,
the triangular weight, the exceptional set, and the quantifier order
`∀ α in Ω, ∃ C, ∀ t`. -/
theorem almostEverywhere_variablePooled_oneSided :
    MeasurableSet pooledGoodPhaseSet ∧
    phaseMeasure pooledGoodPhaseSet = 1 ∧
    pooledGoodPhaseSet ⊆ Set.Ico (0 : ℝ) 1 ∧
    ∀ α ∈ pooledGoodPhaseSet, ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℂ) *
            ∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
              Theory.PiDigits.T27.phase 1
                (((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α)).re ≤
        C * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) := by
  refine ⟨pooledGoodPhaseSet_spec.1, pooledGoodPhaseSet_spec.2.1,
    pooledGoodPhaseSet_spec.2.2, ?_⟩
  intro α hα
  have hnotExceptional : α ∉ pooledExceptionalSet := by
    intro hmem
    exact hα.2 (subset_toMeasurable phaseMeasure _ hmem)
  have hfinite : {t : ℕ | α ∈ pooledBadSet t}.Finite :=
    Set.not_infinite.mp hnotExceptional
  obtain ⟨C, hC, hbound⟩ := finite_pooledBadSet_uniform_bound α hα.1 hfinite
  refine ⟨C, hC, ?_⟩
  intro t
  simpa only [variablePooledReal, variablePooledSum, pooledFrequency, N, H] using
    hbound t

/-- Literal audit of the unchanged centered half-open half-arc convention. -/
theorem variableCombinedHalfArcExcess_literal
    (t : ℕ) (α : ℝ) (y : UnitAddCircle) :
    variableCombinedHalfArcExcess t α y =
      ∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℝ) *
            ((((@Finset.filter ℕ
              (fun k =>
                (AddCircle.equivIco 1 (-(1 / 2 : ℝ))
                  (((((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α : ℝ) :
                    UnitAddCircle) - y) : ℝ) ∈
                  Set.Ico (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
              (Classical.decPred _)
              (Finset.range ((4 * 2 ^ t + 1 : ℕ) - r))).card : ℕ) : ℝ) -
              (((4 * 2 ^ t + 1 : ℕ) - r : ℕ) : ℝ) / 2) := by
  rfl

/-- Conditional implication to the exact phase-substituted T69 aggregate
threshold. It assumes, rather than asserts, the one-sided all-scale premise. -/
theorem variablePooledBound_implies_T69Aggregate
    {α C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t : ℕ,
      (∑ h ∈ Finset.Icc (1 : ℕ) 10,
        ∑ r ∈ Finset.Ico 1
            (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
          ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℂ) *
            ∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
              Theory.PiDigits.T27.phase 1
                (((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α)).re ≤
        C * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ)) :
    0 ≤ 10 + 2 * C ∧ ∀ t : ℕ,
      10 * (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
          (4 * 2 ^ t + 1 : ℕ) +
        2 * (∑ h ∈ Finset.Icc (1 : ℕ) 10,
          ∑ r ∈ Finset.Ico 1
              (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ))),
            ((Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) - r : ℕ) : ℂ) *
              ∑ k ∈ Finset.range ((4 * 2 ^ t + 1 : ℕ) - r),
                Theory.PiDigits.T27.phase 1
                  (((h * (10 ^ r - 1) * 10 ^ k : ℕ) : ℝ) * α)).re ≤
        (10 + 2 * C) *
          (Nat.ceil (Real.sqrt ((4 * 2 ^ t + 1 : ℕ) : ℝ)) : ℝ) *
            (4 * 2 ^ t + 1 : ℕ) := by
  refine ⟨by positivity, ?_⟩
  intro t
  have ht := hbound t
  nlinarith

end Theory.PiDigits.LongLagBlockCollisionDecay.T76

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.pooledFrequency_eq_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.finite_frequencyClass_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.literal_T69_frequencyClass_iff
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.integral_singleChannelSum_norm_sq
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.integral_variablePooledReal_sq_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.literal_secondMoment_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.pooledBadSet_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.literal_pooledBadSet_measureReal_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.summable_pooledBadSet_measureReal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.phaseMeasure_pooledExceptionalSet_eq_zero
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.pooledGoodPhaseSet_spec
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.finite_pooledBadSet_uniform_bound
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.almostEverywhere_variablePooled_oneSided
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.variableCombinedHalfArcExcess_literal
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T76.variablePooledBound_implies_T69Aggregate
