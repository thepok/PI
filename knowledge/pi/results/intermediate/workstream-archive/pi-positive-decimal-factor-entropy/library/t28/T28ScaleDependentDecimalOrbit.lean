import TheoryLib.PiPositiveDecimalFactorEntropy.T22T22QuantizedFejerEnergy
import TheoryLib.PiPositiveDecimalFactorEntropy.T23T23AbstractSubgroupSeparation
import TheoryLib.PiPositiveDecimalFactorEntropy.T25T25DecimalSuccessorExclusion
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Multiplicity

/-!
# T28: a scale-dependent rational decimal orbit

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

For each `n >= 1`, this file studies the first `10^n` points of the times-ten
orbit of the rational seed `1 / (9 * 3^n)`. The seed varies with `n`. Thus this
is not one fixed-real orbit, is not the orbit of pi, and proves neither C1 nor
its negation. Its purpose is to test which conclusions follow from the local
decimal successor law alone.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace DecimalFactorComplexity.ScaleDependentDecimalOrbit

open DecimalFactorComplexity.AbstractSubgroupSeparation
open DecimalFactorComplexity.DecimalSuccessorExclusion
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.FiniteCircleQuantization
open DecimalFactorComplexity.QuantizedFejerEnergy
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorEntropy.FinitePrefixMultiplicityTransfer

/-- Number of sampled orbit points at scale `n`. -/
def sampleSize (n : ℕ) : ℕ := 10 ^ n

/-- Exact period of the rational orbit at scale `n`. -/
def period (n : ℕ) : ℕ := 3 ^ n

/-- T22 bandwidth, equal to half the sample size for `n >= 1`. -/
def bandwidth (n : ℕ) : ℕ := sampleSize n / 2

/-- Ambient quantization modulus. -/
def modulus (n : ℕ) : ℕ := 9 * period n * sampleSize n

/-- The scale-dependent rational seed. -/
def seed (n : ℕ) : ℝ := 1 / (9 * period n)

instance period_neZero (n : ℕ) : NeZero (period n) := by
  exact ⟨by simp [period]⟩

instance modulus_neZero (n : ℕ) : NeZero (modulus n) := by
  exact ⟨by simp [modulus, period, sampleSize]⟩

/-- The labels are literally T25's floor-quantized decimal-orbit labels. -/
def orbitLabel (n : ℕ) : Fin (sampleSize n) → ZMod (modulus n) :=
  decimalOrbitLabel (seed n) (modulus n) (sampleSize n)

/-- Character sum of the first `M = 10^n` labels. -/
def orbitSum (n : ℕ) (h : ℤ) : ℂ :=
  ∑ j : Fin (sampleSize n), quantizedCharacter (modulus n) h (orbitLabel n j)

/-- T22's complete signed, exactly triangular Fejer energy for these labels. -/
def energy (n : ℕ) : ℝ :=
  labelFejerEnergy (orbitLabel n) (bandwidth n)

/-- The five integer parameters and the rational seed in the agenda item. -/
theorem family_parameters (n : ℕ) (hn : 1 ≤ n) :
    let M := sampleSize n
    let D := period n
    let H := bandwidth n
    let q := modulus n
    let x_n := seed n
    M = 10 ^ n ∧ D = 3 ^ n ∧ H = M / 2 ∧ M = 2 * H ∧
      q = 9 * D * M ∧ x_n = 1 / (9 * D : ℕ) := by
  dsimp [sampleSize, period, bandwidth, modulus, seed]
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
  · have htwo : 2 ∣ 10 ^ n := by
      exact dvd_pow (by norm_num) (by omega)
    omega
  · norm_cast

/-- The power of three in `10^k - 1` is exactly two plus that in `k`. -/
theorem padicVal_three_ten_pow_sub_one (k : ℕ) (hk : k ≠ 0) :
    padicValNat 3 (10 ^ k - 1) = 2 + padicValNat 3 k := by
  have h := padicValNat.pow_sub_pow (p := 3) (x := 10) (y := 1)
    (hp1 := by norm_num) (by omega) (by norm_num) (by norm_num) hk
  rw [show padicValNat 3 9 = 2 by
    simpa using padicValNat_base_pow (p := 3) (by norm_num) 2] at h
  norm_num at h
  exact h

/-- Exact period divisibility equivalence, including `k = 0`. -/
theorem nine_mul_period_dvd_ten_pow_sub_one_iff (n k : ℕ) :
    9 * period n ∣ 10 ^ k - 1 ↔ period n ∣ k := by
  rw [show 9 * period n = 3 ^ (n + 2) by
    simp [period, pow_add, Nat.mul_comm]]
  by_cases hk : k = 0
  · simp [hk]
  have hpow : 10 ^ k - 1 ≠ 0 := by
    have : 1 < 10 ^ k := one_lt_pow₀ (by norm_num) hk
    omega
  unfold period
  rw [padicValNat_dvd_iff_le hpow, padicValNat_dvd_iff_le hk,
    padicVal_three_ten_pow_sub_one k hk]
  omega

/-- Multiplying a rational with denominator `d` by a modulus `d*M` produces
an exact floor label: there is no rounding error in `ZMod (d*M)`. -/
theorem cyclicCell_nat_divisor (d M a : ℕ) (hd : 0 < d) :
    cyclicCell (d * M) ((a : ℝ) / d) = (M * a : ZMod (d * M)) := by
  unfold cyclicCell
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hreal :
      ((d * M : ℕ) : ℝ) * (((a % d : ℕ) : ℝ) / d) =
        ((M * (a % d) : ℕ) : ℝ) := by
    push_cast
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
  rw [hreal, Int.floor_natCast]
  push_cast
  rw [← Int.natCast_mod]
  have hcast : ((M * (a % d) : ℕ) : ZMod (d * M)) =
      ((M * a : ℕ) : ZMod (d * M)) := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
    refine ⟨a / d, ?_⟩
    push_cast
    have hdiv := Nat.div_add_mod' a d
    push_cast at hdiv
    nlinarith
  convert hcast using 1 <;> norm_cast

/-- The scaled fractional part used by the floor is itself an integer. -/
theorem modulus_mul_fract_nat_divisor (d M a : ℕ) (hd : 0 < d) :
    ((d * M : ℕ) : ℝ) * Int.fract ((a : ℝ) / d) =
      (M * (a % d) : ℕ) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']

/-- Exact floor-label formula for every power in the orbit. -/
theorem orbitLabel_eq_natCast (n : ℕ) (j : Fin (sampleSize n)) :
    orbitLabel n j =
      (sampleSize n * 10 ^ (j : ℕ) : ZMod (modulus n)) := by
  change cyclicCell (modulus n)
      ((10 : ℝ) ^ (j : ℕ) * seed n) = _
  rw [seed]
  have hd : 0 < 9 * period n := by simp [period]
  have hcell := cyclicCell_nat_divisor (9 * period n) (sampleSize n)
    (10 ^ (j : ℕ)) hd
  simpa [modulus, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hcell

/-- The delivered labels are definitionally the imported T25 labels. -/
theorem orbitLabel_eq_T25_decimalOrbitLabel (n : ℕ) :
    orbitLabel n = decimalOrbitLabel (seed n) (modulus n) (sampleSize n) := by
  rfl

/-- Every T25 digit error for this rational family is exactly zero. -/
theorem decimalDigitError_eq_zero (n j : ℕ) :
    DecimalSuccessorExclusion.decimalDigitError (modulus n)
      ((10 : ℝ) ^ j * seed n) = 0 := by
  have hd : 0 < 9 * period n := by simp [period]
  have hy : (10 : ℝ) ^ j * seed n =
      ((10 ^ j : ℕ) : ℝ) / (9 * period n) := by
    rw [seed]
    push_cast
    ring
  unfold DecimalSuccessorExclusion.decimalDigitError
  rw [hy]
  have hscaled := modulus_mul_fract_nat_divisor
    (9 * period n) (sampleSize n) (10 ^ j) hd
  have hscaled' :
      ((modulus n : ℕ) : ℝ) *
          Int.fract (((10 ^ j : ℕ) : ℝ) / (9 * (period n : ℝ))) =
        (sampleSize n * (10 ^ j % (9 * period n)) : ℕ) := by
    simpa [modulus, Nat.cast_mul] using hscaled
  rw [hscaled']
  rw [Int.fract_natCast]
  norm_num

/-- Exact zero-error times-ten successor law on the full linear range. -/
theorem orbitLabel_successor_zero (n j : ℕ) (hj : j + 1 < sampleSize n) :
    orbitLabel n ⟨j + 1, hj⟩ =
      10 * orbitLabel n ⟨j, by omega⟩ := by
  rw [orbitLabel_eq_natCast, orbitLabel_eq_natCast]
  push_cast
  rw [pow_succ]
  ring

/-- Cancelling the repeated scale factor converts equality in `ZMod (d*M)`
to ordinary congruence modulo `d`. -/
theorem scaled_natCast_eq_iff_modEq (d M a b : ℕ) (hM : M ≠ 0) :
    ((M * a : ℕ) : ZMod (d * M)) = ((M * b : ℕ) : ZMod (d * M)) ↔
      a ≡ b [MOD d] := by
  rw [ZMod.natCast_eq_natCast_iff]
  simpa only [Nat.mul_comm d M] using
    (Nat.ModEq.mul_left_cancel_iff' (a := a) (b := b) (m := d) hM)

/-- Two powers of ten with ordered exponents agree modulo `9D` exactly when
the exponent difference is divisible by `D`. -/
theorem ten_pow_modEq_iff_period_dvd_sub (n j k : ℕ) (hjk : j ≤ k) :
    10 ^ j ≡ 10 ^ k [MOD 9 * period n] ↔ period n ∣ k - j := by
  have hpowle : 10 ^ j ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
  rw [Nat.modEq_iff_dvd' hpowle]
  have hfactor : 10 ^ k - 10 ^ j = 10 ^ j * (10 ^ (k - j) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add]
    congr 2
    omega
  rw [hfactor]
  have hcbase : Nat.Coprime 10 (9 * period n) := by
    apply Nat.Coprime.mul_right
    · norm_num
    · unfold period
      exact Nat.Coprime.pow_right n (by norm_num)
  have hc : Nat.Coprime (10 ^ j) (9 * period n) :=
    Nat.Coprime.pow_left j hcbase
  constructor
  · intro hdvd
    have hcancel : 9 * period n ∣ 10 ^ (k - j) - 1 :=
      hc.symm.dvd_of_dvd_mul_left hdvd
    exact (nine_mul_period_dvd_ten_pow_sub_one_iff n (k - j)).mp hcancel
  · intro hD
    exact dvd_mul_of_dvd_right
      ((nine_mul_period_dvd_ten_pow_sub_one_iff n (k - j)).mpr hD) _

/-- Equality criterion for arbitrary labels in the infinite rational orbit. -/
theorem scaled_power_label_eq_iff_modEq_period (n j k : ℕ) :
    ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n)) =
        ((sampleSize n * 10 ^ k : ℕ) : ZMod (modulus n)) ↔
      j ≡ k [MOD period n] := by
  have hM : sampleSize n ≠ 0 := by simp [sampleSize]
  rw [show modulus n = (9 * period n) * sampleSize n by rfl,
    scaled_natCast_eq_iff_modEq (9 * period n) (sampleSize n)
      (10 ^ j) (10 ^ k) hM]
  wlog hjk : j ≤ k generalizing j k
  · have ih := this k j (by omega)
    constructor
    · intro h
      exact (ih.mp h.symm).symm
    · intro h
      exact (ih.mpr h.symm).symm
  rw [ten_pow_modEq_iff_period_dvd_sub n j k hjk,
    Nat.modEq_iff_dvd' hjk]

/-- The exact label period is `D = 3^n`, not merely a divisor of `D`. -/
theorem orbit_period_equivalence (n j k : ℕ) :
    ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n)) =
        ((sampleSize n * 10 ^ k : ℕ) : ZMod (modulus n)) ↔
      j ≡ k [MOD period n] :=
  scaled_power_label_eq_iff_modEq_period n j k

/-- The least positive return time of the label at time zero is `D`. -/
theorem orbit_exact_period (n k : ℕ) :
    ((sampleSize n * 10 ^ k : ℕ) : ZMod (modulus n)) =
        ((sampleSize n : ℕ) : ZMod (modulus n)) ↔
      period n ∣ k := by
  simpa [Nat.modEq_zero_iff_dvd] using
    (scaled_power_label_eq_iff_modEq_period n k 0)

/-- No positive return occurs before `D`. -/
theorem period_le_positive_return (n k : ℕ) (hk : 0 < k)
    (hreturn : ((sampleSize n * 10 ^ k : ℕ) : ZMod (modulus n)) =
      ((sampleSize n : ℕ) : ZMod (modulus n))) : period n ≤ k := by
  exact Nat.le_of_dvd hk (orbit_exact_period n k |>.mp hreturn)

/-- One representative of each label in a full period. -/
def periodLabel (n : ℕ) (a : Fin (period n)) : ZMod (modulus n) :=
  (sampleSize n * 10 ^ (a : ℕ) : ℕ)

/-- A point in the affine coset `M + 9M * Z/DZ`. -/
def affinePoint (n : ℕ) (t : Fin (period n)) : ZMod (modulus n) :=
  (sampleSize n + 9 * sampleSize n * t.val : ℕ)

/-- The affine coset containing one full period of labels. -/
def affineCoset (n : ℕ) : Finset (ZMod (modulus n)) :=
  Finset.univ.image (affinePoint n)

/-- The full-period label map is injective. -/
theorem periodLabel_injective (n : ℕ) : Function.Injective (periodLabel n) := by
  intro a b hab
  have hm := (scaled_power_label_eq_iff_modEq_period n a.val b.val).mp hab
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hm a.isLt b.isLt)

/-- The displayed parametrization of the affine coset is injective. -/
theorem affinePoint_injective (n : ℕ) : Function.Injective (affinePoint n) := by
  intro a b hab
  have hM : 0 < sampleSize n := by simp [sampleSize]
  have haSmall : sampleSize n + 9 * sampleSize n * a.val < modulus n := by
    have ha := a.isLt
    have hmul : 9 * sampleSize n * (a.val + 1) ≤
        9 * sampleSize n * period n := Nat.mul_le_mul_left _ (by omega)
    rw [modulus]
    nlinarith
  have hbSmall : sampleSize n + 9 * sampleSize n * b.val < modulus n := by
    have hb := b.isLt
    have hmul : 9 * sampleSize n * (b.val + 1) ≤
        9 * sampleSize n * period n := Nat.mul_le_mul_left _ (by omega)
    rw [modulus]
    nlinarith
  have hv := congrArg ZMod.val hab
  simp only [affinePoint, ZMod.val_natCast_of_lt haSmall,
    ZMod.val_natCast_of_lt hbSmall] at hv
  apply Fin.ext
  nlinarith

/-- Every power label lies in the displayed affine coset. -/
theorem periodLabel_mem_affineCoset (n : ℕ) (a : Fin (period n)) :
    periodLabel n a ∈ affineCoset n := by
  classical
  have h9 : 9 ∣ 10 ^ a.val - 1 := by
    simpa [period] using
      (nine_mul_period_dvd_ten_pow_sub_one_iff 0 a.val).mpr (one_dvd _)
  let u := (10 ^ a.val - 1) / 9
  let t : Fin (period n) :=
    ⟨u % period n, Nat.mod_lt _ (by simp [period])⟩
  have hpow : 10 ^ a.val = 1 + 9 * u := by
    have hle : 1 ≤ 10 ^ a.val := one_le_pow₀ (by norm_num)
    have hmul : 9 * u = 10 ^ a.val - 1 := by
      exact Nat.mul_div_cancel' h9
    omega
  have hmod : u ≡ t.val [MOD period n] := by
    simp [t, Nat.ModEq]
  have hmod' : 10 ^ a.val ≡ 1 + 9 * t.val [MOD 9 * period n] := by
    rw [hpow]
    exact (hmod.mul_left' 9).add_left 1
  rw [affineCoset]
  refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
  unfold periodLabel affinePoint
  symm
  rw [show sampleSize n + 9 * sampleSize n * t.val =
      sampleSize n * (1 + 9 * t.val) by ring]
  rw [show modulus n = (9 * period n) * sampleSize n by rfl,
    scaled_natCast_eq_iff_modEq (9 * period n) (sampleSize n)
      (10 ^ a.val) (1 + 9 * t.val) (by simp [sampleSize])]
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hmod'

/-- The support of one full period is exactly an affine coset of size `D`. -/
theorem periodLabel_support_eq_affineCoset (n : ℕ) :
    Finset.univ.image (periodLabel n) = affineCoset n ∧
      (affineCoset n).card = period n := by
  classical
  have hsubset : Finset.univ.image (periodLabel n) ⊆ affineCoset n := by
    intro z hz
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hz
    exact periodLabel_mem_affineCoset n a
  have hperiodCard : (Finset.univ.image (periodLabel n)).card = period n := by
    rw [Finset.card_image_iff.mpr (periodLabel_injective n).injOn]
    simp
  have haffineCard : (affineCoset n).card = period n := by
    rw [affineCoset, Finset.card_image_iff.mpr (affinePoint_injective n).injOn]
    simp
  exact ⟨Finset.eq_of_subset_of_card_le hsubset (by
    rw [haffineCard, hperiodCard]), haffineCard⟩

/-- A sampled label equals a chosen period representative exactly when their
indices have the same residue modulo `D`. -/
theorem orbitLabel_eq_periodLabel_iff (n : ℕ) (j : Fin (sampleSize n))
    (a : Fin (period n)) :
    orbitLabel n j = periodLabel n a ↔ j.val ≡ a.val [MOD period n] := by
  rw [orbitLabel_eq_natCast]
  unfold periodLabel
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (scaled_power_label_eq_iff_modEq_period n j.val a.val)

/-- Exact count of each period label in the first `M` samples. This is the
floor count plus one precisely for residues in the incomplete final period. -/
theorem periodLabel_exact_multiplicity (n : ℕ) (a : Fin (period n)) :
    prefixMultiplicity (orbitLabel n) (periodLabel n a) =
      sampleSize n / period n +
        if a.val < sampleSize n % period n then 1 else 0 := by
  classical
  unfold prefixMultiplicity
  have hcard :
      ((Finset.univ : Finset (Fin (sampleSize n))).filter
          (fun j => orbitLabel n j = periodLabel n a)).card =
        ((Finset.range (sampleSize n)).filter
          (fun j => j ≡ a.val [MOD period n])).card := by
    apply Finset.card_bij (fun j _hj => j.val)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨j.isLt, (orbitLabel_eq_periodLabel_iff n j a).mp hj⟩
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      let i : Fin (sampleSize n) := ⟨j, hj.1⟩
      refine ⟨i, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (orbitLabel_eq_periodLabel_iff n i a).mpr hj.2
  rw [hcard, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (sampleSize n) (by simp [period]) a.val]
  simp only [Nat.mod_eq_of_lt a.isLt]

/-- The sample size dominates one complete period. -/
theorem period_le_sampleSize (n : ℕ) : period n ≤ sampleSize n := by
  unfold period sampleSize
  exact Nat.pow_le_pow_left (by norm_num) n

/-- Support of all `M` sampled labels. -/
def orbitSupport (n : ℕ) : Finset (ZMod (modulus n)) :=
  Finset.univ.image (orbitLabel n)

/-- The first `M` labels have exactly the full affine-coset support. -/
theorem orbitSupport_eq_affineCoset (n : ℕ) :
    orbitSupport n = affineCoset n ∧ (orbitSupport n).card = period n := by
  classical
  have hperiod := periodLabel_support_eq_affineCoset n
  have hsubset : orbitSupport n ⊆ affineCoset n := by
    intro z hz
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hz
    let a : Fin (period n) :=
      ⟨j.val % period n, Nat.mod_lt _ (by simp [period])⟩
    have heq : orbitLabel n j = periodLabel n a := by
      apply (orbitLabel_eq_periodLabel_iff n j a).mpr
      simp [a, Nat.ModEq]
    rw [heq]
    exact periodLabel_mem_affineCoset n a
  have hreverse : affineCoset n ⊆ orbitSupport n := by
    rw [← hperiod.1]
    intro z hz
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hz
    let j : Fin (sampleSize n) :=
      ⟨a.val, a.isLt.trans_le (period_le_sampleSize n)⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    apply (orbitLabel_eq_periodLabel_iff n j a).mpr
    exact Nat.ModEq.rfl
  have heq := Finset.Subset.antisymm hsubset hreverse
  exact ⟨heq, by rw [heq, hperiod.2]⟩

/-- Every point of the affine support has floor-or-ceiling multiplicity. -/
theorem affineCoset_multiplicity_floor_or_ceil (n : ℕ)
    (z : ZMod (modulus n)) (hz : z ∈ affineCoset n) :
    prefixMultiplicity (orbitLabel n) z = sampleSize n / period n ∨
      prefixMultiplicity (orbitLabel n) z = sampleSize n / period n + 1 := by
  classical
  rw [← (periodLabel_support_eq_affineCoset n).1] at hz
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hz
  rw [periodLabel_exact_multiplicity]
  split_ifs <;> omega

/-- The subgroup component of an affine-coset point. -/
def stepPoint (n : ℕ) (t : Fin (period n)) : ZMod (modulus n) :=
  (t.val * (9 * sampleSize n) : ℕ)

/-- Restriction of an ambient character to the order-`D` subgroup is the
standard character on `ZMod D`. -/
theorem stepPoint_character (n : ℕ) (h : ℤ) (t : Fin (period n)) :
    quantizedCharacter (modulus n) h (stepPoint n t) =
      quantizedCharacter (period n) h (t.val : ZMod (period n)) := by
  unfold quantizedCharacter stepPoint
  rw [AddChar.mulShift_apply, AddChar.mulShift_apply]
  rw [show ((t.val * (9 * sampleSize n) : ℕ) : ZMod (modulus n)) =
      ((t.val : ℤ) * (9 * sampleSize n : ℤ) : ℤ) by norm_cast]
  rw [show (t.val : ZMod (period n)) = (t.val : ℤ) by norm_cast]
  rw [show (h : ZMod (modulus n)) *
      (((t.val : ℤ) * (9 * sampleSize n : ℤ) : ℤ) : ZMod (modulus n)) =
        ((h * (t.val : ℤ) * (9 * sampleSize n : ℤ) : ℤ) :
          ZMod (modulus n)) by
      push_cast
      ring]
  rw [show (h : ZMod (period n)) * ((t.val : ℤ) : ZMod (period n)) =
      ((h * (t.val : ℤ) : ℤ) : ZMod (period n)) by
      push_cast
      ring]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hD : (period n : ℂ) ≠ 0 := by
    exact_mod_cast (by simp [period] : period n ≠ 0)
  have hM : (sampleSize n : ℂ) ≠ 0 := by
    exact_mod_cast (by simp [sampleSize] : sampleSize n ≠ 0)
  rw [modulus]
  push_cast
  field_simp [hD, hM]

/-- Character of an affine point factors as a fixed translate times the
standard character on the period group. -/
theorem affinePoint_character (n : ℕ) (h : ℤ) (t : Fin (period n)) :
    quantizedCharacter (modulus n) h (affinePoint n t) =
      quantizedCharacter (modulus n) h (sampleSize n : ZMod (modulus n)) *
        quantizedCharacter (period n) h (t.val : ZMod (period n)) := by
  have hpoint : affinePoint n t =
      (sampleSize n : ZMod (modulus n)) + stepPoint n t := by
    unfold affinePoint stepPoint
    push_cast
    ring
  rw [hpoint, AddChar.map_add_eq_mul, stepPoint_character]

/-- Orthogonality of the standard character on the period group. -/
theorem sum_period_character (n : ℕ) (h : ℤ) :
    (∑ t : Fin (period n),
        quantizedCharacter (period n) h (t.val : ZMod (period n))) =
      if (period n : ℤ) ∣ h then (period n : ℂ) else 0 := by
  classical
  calc
    (∑ t : Fin (period n),
        quantizedCharacter (period n) h (t.val : ZMod (period n))) =
        ∑ z : ZMod (period n), quantizedCharacter (period n) h z := by
      exact Fintype.sum_equiv (ZMod.finEquiv (period n)).toEquiv
        _ _ (fun t => by
          rw [DecimalFactorComplexity.AbstractSubgroupSeparation.finEquiv_apply_eq_natCast])
    _ = if (h : ZMod (period n)) = 0 then (period n : ℂ) else 0 := by
      simpa [quantizedCharacter, mul_comm] using
        (AddChar.sum_mulShift (R' := ℂ) (h : ZMod (period n))
          (ZMod.isPrimitive_stdAddChar (period n)))
    _ = if (period n : ℤ) ∣ h then (period n : ℂ) else 0 := by
      simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A complete period has character sum of norm `D` on the annihilator and
zero off it. -/
theorem fullPeriod_character_sum (n : ℕ) (h : ℤ) :
    (∑ a : Fin (period n),
        quantizedCharacter (modulus n) h (periodLabel n a)) =
      quantizedCharacter (modulus n) h (sampleSize n : ZMod (modulus n)) *
        (if (period n : ℤ) ∣ h then (period n : ℂ) else 0) := by
  classical
  have hs := (periodLabel_support_eq_affineCoset n).1
  calc
    (∑ a : Fin (period n),
        quantizedCharacter (modulus n) h (periodLabel n a)) =
        ∑ z ∈ Finset.univ.image (periodLabel n),
          quantizedCharacter (modulus n) h z := by
      rw [Finset.sum_image]
      exact (periodLabel_injective n).injOn
    _ = ∑ z ∈ affineCoset n,
          quantizedCharacter (modulus n) h z := by rw [hs]
    _ = ∑ t : Fin (period n),
          quantizedCharacter (modulus n) h (affinePoint n t) := by
      rw [affineCoset, Finset.sum_image]
      exact (affinePoint_injective n).injOn
    _ = quantizedCharacter (modulus n) h
          (sampleSize n : ZMod (modulus n)) *
        ∑ t : Fin (period n),
          quantizedCharacter (period n) h (t.val : ZMod (period n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact affinePoint_character n h t
    _ = _ := by rw [sum_period_character]

/-- A periodic finite sum decomposes into complete periods and one remainder. -/
theorem sum_range_mul_add_of_periodic {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (D q r : ℕ) (hperiodic : ∀ j, f (D + j) = f j) :
    ∑ j ∈ Finset.range (q * D + r), f j =
      q • (∑ j ∈ Finset.range D, f j) + ∑ j ∈ Finset.range r, f j := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul]
      rw [show q * D + D + r = D + (q * D + r) by omega,
        Finset.sum_range_add]
      simp_rw [hperiodic]
      rw [ih, succ_nsmul]
      ac_rfl

/-- Character contribution of the incomplete final period. -/
def remainderSum (n : ℕ) (h : ℤ) : ℂ :=
  ∑ j ∈ Finset.range (sampleSize n % period n),
    quantizedCharacter (modulus n) h
      ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n))

/-- Exact complete-period plus remainder decomposition of the orbit sum. -/
theorem orbitSum_eq_completePeriods_add_remainder (n : ℕ) (h : ℤ) :
    orbitSum n h =
      (sampleSize n / period n) •
        (∑ a : Fin (period n),
          quantizedCharacter (modulus n) h (periodLabel n a)) +
        remainderSum n h := by
  classical
  let f : ℕ → ℂ := fun j => quantizedCharacter (modulus n) h
    ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n))
  have hfperiodic : ∀ j, f (period n + j) = f j := by
    intro j
    apply congrArg (quantizedCharacter (modulus n) h)
    exact (scaled_power_label_eq_iff_modEq_period n (period n + j) j).mpr (by
      simp [Nat.ModEq])
  have hdecomp := sum_range_mul_add_of_periodic f (period n)
    (sampleSize n / period n) (sampleSize n % period n) hfperiodic
  have hM := Nat.div_add_mod' (sampleSize n) (period n)
  have hperiodSum : (∑ j ∈ Finset.range (period n), f j) =
      ∑ a : Fin (period n),
        quantizedCharacter (modulus n) h (periodLabel n a) := by
    rw [← Fin.sum_univ_eq_sum_range f (period n)]
    rfl
  unfold orbitSum remainderSum
  calc
    (∑ j : Fin (sampleSize n),
        quantizedCharacter (modulus n) h (orbitLabel n j)) =
        ∑ j : Fin (sampleSize n), f j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [orbitLabel_eq_natCast]
      simp only [f, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = ∑ j ∈ Finset.range (sampleSize n), f j :=
      Fin.sum_univ_eq_sum_range f (sampleSize n)
    _ = ∑ j ∈ Finset.range
          (sampleSize n / period n * period n + sampleSize n % period n),
          f j := by rw [hM]
    _ = _ := by
      rw [hdecomp, hperiodSum]

/-- An annihilator character is constant on the affine coset. -/
theorem annihilator_character_eq_base (n : ℕ) (h : ℤ)
    (hh : (period n : ℤ) ∣ h) (z : ZMod (modulus n))
    (hz : z ∈ affineCoset n) :
    quantizedCharacter (modulus n) h z =
      quantizedCharacter (modulus n) h
        (sampleSize n : ZMod (modulus n)) := by
  classical
  unfold affineCoset at hz
  obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hz
  rw [affinePoint_character]
  have hzmod : (h : ZMod (period n)) = 0 :=
    by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hh
  unfold quantizedCharacter
  rw [AddChar.mulShift_apply, hzmod]
  simp

/-- First orbit-sum bound: exact norm `M` on annihilator frequencies. -/
theorem norm_orbitSum_eq_sampleSize_of_period_dvd (n : ℕ) (h : ℤ)
    (hh : (period n : ℤ) ∣ h) : ‖orbitSum n h‖ = sampleSize n := by
  unfold orbitSum
  have hterm : ∀ j : Fin (sampleSize n),
      quantizedCharacter (modulus n) h (orbitLabel n j) =
        quantizedCharacter (modulus n) h
          (sampleSize n : ZMod (modulus n)) := by
    intro j
    apply annihilator_character_eq_base n h hh
    rw [← (orbitSupport_eq_affineCoset n).1]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  simp_rw [hterm]
  simp [AddChar.norm_apply]

/-- A remainder of `r` unit character values has norm at most `r`. -/
theorem norm_remainderSum_le (n : ℕ) (h : ℤ) :
    ‖remainderSum n h‖ ≤ ((sampleSize n % period n : ℕ) : ℝ) := by
  unfold remainderSum
  calc
    ‖∑ j ∈ Finset.range (sampleSize n % period n),
        quantizedCharacter (modulus n) h
          ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n))‖ ≤
      ∑ j ∈ Finset.range (sampleSize n % period n),
        ‖quantizedCharacter (modulus n) h
          ((sampleSize n * 10 ^ j : ℕ) : ZMod (modulus n))‖ :=
      norm_sum_le _ _
    _ = ((sampleSize n % period n : ℕ) : ℝ) := by
      simp_rw [AddChar.norm_apply]
      rw [Finset.sum_const, Finset.card_range]
      simp

/-- Second orbit-sum bound: only the incomplete period remains away from the
annihilator. -/
theorem norm_orbitSum_le_mod_of_not_period_dvd (n : ℕ) (h : ℤ)
    (hh : ¬(period n : ℤ) ∣ h) :
    ‖orbitSum n h‖ ≤ ((sampleSize n % period n : ℕ) : ℝ) := by
  rw [orbitSum_eq_completePeriods_add_remainder,
    fullPeriod_character_sum]
  rw [if_neg hh, mul_zero, nsmul_zero, zero_add]
  exact norm_remainderSum_le n h

/-- Literal expansion with T22's complete signed band and exact triangular
weights. -/
theorem energy_eq_T22_complete_band (n : ℕ) :
    energy n =
      ∑ h ∈ fejerFrequencies (bandwidth n),
        (1 - (h.natAbs : ℝ) / (bandwidth n : ℝ)) * ‖orbitSum n h‖ ^ 2 := by
  rfl

/-- The modulus is strictly larger than twice the T22 bandwidth. -/
theorem modulus_gt_two_mul_bandwidth (n : ℕ) (hn : 1 ≤ n) :
    2 * bandwidth n < modulus n := by
  have hp := family_parameters n hn
  dsimp only at hp
  rcases hp with ⟨_hM, _hD, _hH, hMH, _hq, _hx⟩
  have hD : 1 ≤ period n := by
    unfold period
    exact one_le_pow₀ (by norm_num)
  have hMpos : 0 < sampleSize n := by simp [sampleSize]
  have hlarge : sampleSize n < 9 * period n * sampleSize n := by
    nlinarith
  simpa only [← hMH, modulus] using hlarge

/-- T18 alias freedom for the complete T22 band. -/
theorem family_aliasFree (n : ℕ) (hn : 1 ≤ n) :
    2 * bandwidth n < modulus n ∧
      Set.InjOn (quantizedCharacter (modulus n))
        {h : ℤ | h.natAbs < bandwidth n} := by
  have hq := modulus_gt_two_mul_bandwidth n hn
  exact ⟨hq, lowFrequency_quantizedCharacter_injective
    (modulus n) (bandwidth n) hq⟩

/-- Exact total T22 weight carried by annihilator frequencies. -/
def annihilatorWeight (n : ℕ) : ℝ :=
  ∑ h ∈ fejerFrequencies (bandwidth n),
    if (period n : ℤ) ∣ h then fejerWeight (bandwidth n) h else 0

/-- Generic closed formula for triangular weight on multiples of `D`. -/
theorem annihilator_fejerWeight_sum_general (D H : ℕ)
    (hD : 0 < D) (hH : 0 < H) :
    (∑ h ∈ fejerFrequencies H,
        if (D : ℤ) ∣ h then fejerWeight H h else 0) =
      let L := (H - 1) / D
      (2 * L + 1 : ℕ) - (D : ℝ) * L * (L + 1) / H := by
  classical
  let L := (H - 1) / D
  let K := L + 1
  have hK : 1 ≤ K := by simp [K]
  have hcut (m : ℤ) : D * m.natAbs < H ↔ m.natAbs < K := by
    rw [show m.natAbs < K ↔ m.natAbs ≤ L by omega]
    rw [show m.natAbs ≤ L ↔ D * m.natAbs ≤ H - 1 by
      simpa [L, Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hD : m.natAbs ≤ (H - 1) / D ↔
          m.natAbs * D ≤ H - 1)]
    omega
  rw [← Finset.sum_filter]
  have hreindex :
      (∑ h ∈ (fejerFrequencies H).filter (fun h => (D : ℤ) ∣ h),
          fejerWeight H h) =
        ∑ m ∈ fejerFrequencies K, fejerWeight H ((D : ℤ) * m) := by
    symm
    apply Finset.sum_bij (fun m _hm => (D : ℤ) * m)
    · intro m hm
      simp only [Finset.mem_filter]
      constructor
      · rw [mem_fejerFrequencies_iff hH]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        exact hcut m |>.2 ((mem_fejerFrequencies_iff hK).mp hm)
      · exact dvd_mul_right _ _
    · intro a ha b hb hab
      exact mul_left_cancel₀ (by exact_mod_cast hD.ne') hab
    · intro h hh
      simp only [Finset.mem_filter] at hh
      obtain ⟨m, rfl⟩ := hh.2
      refine ⟨m, ?_, rfl⟩
      rw [mem_fejerFrequencies_iff hK]
      have hm := (mem_fejerFrequencies_iff hH).mp hh.1
      rw [Int.natAbs_mul, Int.natAbs_natCast] at hm
      exact (hcut m).mp hm
    · intro m hm
      rfl
  rw [hreindex]
  have hHreal : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hterm (m : ℤ) :
      fejerWeight H ((D : ℤ) * m) =
        ((D : ℝ) * K / H) * fejerWeight K m +
          (1 - (D : ℝ) * K / H) := by
    unfold fejerWeight
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    push_cast
    field_simp [hHreal, hKreal]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    DecimalFactorComplexity.AbstractSubgroupSeparation.sum_fejerWeight K hK]
  simp only [Finset.sum_const, nsmul_eq_mul,
    DecimalFactorComplexity.ScaleAdaptiveOrbitFourier.fejerFrequencies_card K hK]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * K)]
  dsimp only [K, L]
  push_cast
  field_simp [hHreal]
  ring

/-- The exact closed annihilator-weight formula for the T28 parameters. -/
theorem annihilatorWeight_exact (n : ℕ) (hn : 1 ≤ n) :
    annihilatorWeight n =
      let L := (bandwidth n - 1) / period n
      (2 * L + 1 : ℕ) -
        (period n : ℝ) * L * (L + 1) / bandwidth n := by
  unfold annihilatorWeight
  exact annihilator_fejerWeight_sum_general (period n) (bandwidth n)
    (by simp [period]) (by
      unfold bandwidth sampleSize
      have hten : 2 ≤ 10 ^ n := by
        calc
          2 ≤ 10 ^ 1 := by norm_num
          _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact Nat.div_pos (by omega) (by norm_num))

/-- The half-decimal bandwidth is positive at every agenda scale. -/
theorem bandwidth_pos (n : ℕ) (hn : 1 ≤ n) : 0 < bandwidth n := by
  unfold bandwidth sampleSize
  have hten : 2 ≤ 10 ^ n := by
    calc
      2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact Nat.div_pos (by omega) (by norm_num)

/-- T22 weights are nonnegative throughout the signed band. -/
theorem fejerWeight_nonneg_of_mem (H : ℕ) (hH : 1 ≤ H) (h : ℤ)
    (hh : h ∈ fejerFrequencies H) : 0 ≤ fejerWeight H h := by
  have habs := (mem_fejerFrequencies_iff hH).mp hh
  unfold fejerWeight
  have hHr : (0 : ℝ) < H := by exact_mod_cast (Nat.zero_lt_of_lt hH)
  exact sub_nonneg.mpr ((div_le_one hHr).2 (by exact_mod_cast habs.le))

/-- The exact annihilator contribution is a lower bound for the full energy. -/
theorem sampleSize_sq_mul_annihilatorWeight_le_energy (n : ℕ) (hn : 1 ≤ n) :
    (sampleSize n : ℝ) ^ 2 * annihilatorWeight n ≤ energy n := by
  have hH : 1 ≤ bandwidth n := bandwidth_pos n hn
  unfold annihilatorWeight
  change (sampleSize n : ℝ) ^ 2 *
      (∑ h ∈ fejerFrequencies (bandwidth n),
        if (period n : ℤ) ∣ h then fejerWeight (bandwidth n) h else 0) ≤
    ∑ h ∈ fejerFrequencies (bandwidth n),
      fejerWeight (bandwidth n) h * ‖orbitSum n h‖ ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hw := fejerWeight_nonneg_of_mem (bandwidth n) hH h hh
  by_cases hd : (period n : ℤ) ∣ h
  · rw [if_pos hd]
    have hs := norm_orbitSum_eq_sampleSize_of_period_dvd n h hd
    rw [hs]
    rw [mul_comm]
  · rw [if_neg hd]
    have hnonneg := mul_nonneg hw (sq_nonneg ‖orbitSum n h‖)
    nlinarith

/-- Upper energy bound separating annihilator mass from the incomplete-period
remainder. -/
theorem energy_le_annihilator_add_remainder (n : ℕ) (hn : 1 ≤ n) :
    energy n ≤
      (sampleSize n : ℝ) ^ 2 * annihilatorWeight n +
        ((sampleSize n % period n : ℕ) : ℝ) ^ 2 * bandwidth n := by
  have hH : 1 ≤ bandwidth n := bandwidth_pos n hn
  unfold annihilatorWeight
  change (∑ h ∈ fejerFrequencies (bandwidth n),
      fejerWeight (bandwidth n) h * ‖orbitSum n h‖ ^ 2) ≤ _
  calc
    (∑ h ∈ fejerFrequencies (bandwidth n),
        fejerWeight (bandwidth n) h * ‖orbitSum n h‖ ^ 2) ≤
      ∑ h ∈ fejerFrequencies (bandwidth n),
        ((sampleSize n : ℝ) ^ 2 *
            (if (period n : ℤ) ∣ h then fejerWeight (bandwidth n) h else 0) +
          ((sampleSize n % period n : ℕ) : ℝ) ^ 2 *
            fejerWeight (bandwidth n) h) := by
      apply Finset.sum_le_sum
      intro h hh
      have hw := fejerWeight_nonneg_of_mem (bandwidth n) hH h hh
      by_cases hd : (period n : ℤ) ∣ h
      · rw [if_pos hd, norm_orbitSum_eq_sampleSize_of_period_dvd n h hd]
        nlinarith [sq_nonneg (((sampleSize n % period n : ℕ) : ℝ))]
      · rw [if_neg hd]
        have hs := norm_orbitSum_le_mod_of_not_period_dvd n h hd
        have hsquare : ‖orbitSum n h‖ ^ 2 ≤
            ((sampleSize n % period n : ℕ) : ℝ) ^ 2 := by nlinarith [norm_nonneg (orbitSum n h)]
        nlinarith
    _ = (sampleSize n : ℝ) ^ 2 *
          (∑ h ∈ fejerFrequencies (bandwidth n),
            if (period n : ℤ) ∣ h then fejerWeight (bandwidth n) h else 0) +
        ((sampleSize n % period n : ℕ) : ℝ) ^ 2 *
          (∑ h ∈ fejerFrequencies (bandwidth n),
            fejerWeight (bandwidth n) h) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
      rw [DecimalFactorComplexity.AbstractSubgroupSeparation.sum_fejerWeight
        (bandwidth n) hH]

/-- The annihilator weight lies between the quotient radius and twice that
radius plus one. -/
theorem annihilatorWeight_bounds (n : ℕ) (hn : 1 ≤ n) :
    let L := (bandwidth n - 1) / period n
    (L : ℝ) ≤ annihilatorWeight n ∧
      annihilatorWeight n ≤ 2 * L + 1 := by
  let L := (bandwidth n - 1) / period n
  have hD : 0 < period n := by simp [period]
  have hH : 0 < bandwidth n := by
    exact bandwidth_pos n hn
  have hDL : period n * L ≤ bandwidth n - 1 := by
    exact (Nat.mul_div_le (bandwidth n - 1) (period n))
  have hfrac : (period n : ℝ) * L * (L + 1) / bandwidth n ≤ L + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hH)]
    have hDLr : (period n : ℝ) * L ≤ bandwidth n := by exact_mod_cast hDL.trans (Nat.sub_le _ _)
    nlinarith
  have hfrac0 : 0 ≤ (period n : ℝ) * L * (L + 1) / bandwidth n := by positivity
  rw [annihilatorWeight_exact n hn]
  dsimp only
  constructor <;> push_cast <;> nlinarith

/-- Real bandwidth-to-period ratio is exactly a geometric sequence for
positive scales. -/
theorem bandwidth_div_period_eq_geometric (n : ℕ) (hn : 1 ≤ n) :
    (bandwidth n : ℝ) / period n =
      (1 / 2 : ℝ) * ((10 : ℝ) / 3) ^ n := by
  have htwo : 2 ∣ sampleSize n := by
    unfold sampleSize
    exact dvd_pow (by norm_num) (by omega)
  have hDr : (period n : ℝ) ≠ 0 := by
    exact_mod_cast (by simp [period] : period n ≠ 0)
  have hHr : (bandwidth n : ℝ) = (sampleSize n : ℝ) / 2 := by
    unfold bandwidth
    rw [Nat.cast_div htwo (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hHr]
  unfold sampleSize period
  push_cast
  rw [div_pow]
  field_simp [hDr]

/-- The quotient radius controlling the annihilator tends to infinity. -/
theorem annihilatorRadius_tendsto_atTop :
    Tendsto (fun n : ℕ =>
      (((bandwidth n - 1) / period n : ℕ) : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => ((10 : ℝ) / 3) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hratio : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((10 : ℝ) / 3) ^ n)
      atTop atTop := hpow.const_mul_atTop (by norm_num)
  rw [tendsto_atTop] at hratio ⊢
  intro B
  filter_upwards [hratio (B + 2), eventually_ge_atTop 1] with n hnlarge hn
  let L := (bandwidth n - 1) / period n
  have hD : 0 < period n := by simp [period]
  have hH : 1 ≤ bandwidth n := by
    exact bandwidth_pos n hn
  have hdecomp := Nat.div_add_mod' (bandwidth n - 1) (period n)
  have hmod := Nat.mod_lt (bandwidth n - 1) hD
  have hnat : bandwidth n ≤ L * period n + period n := by
    dsimp only [L]
    omega
  have hbound : (bandwidth n : ℝ) / period n - 1 ≤ L := by
    have hnat' : (bandwidth n : ℝ) ≤
        (L : ℝ) * period n + period n := by exact_mod_cast hnat
    rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hD)]
    nlinarith
  rw [bandwidth_div_period_eq_geometric n hn] at hbound
  nlinarith

/-- First normalized-energy limit: energy divided by `M^2` diverges. -/
theorem normalizedEnergy_tendsto_atTop :
    Tendsto (fun n : ℕ => energy n / (sampleSize n : ℝ) ^ 2) atTop atTop := by
  have hL := annihilatorRadius_tendsto_atTop
  rw [tendsto_atTop] at hL ⊢
  intro B
  filter_upwards [hL B, eventually_ge_atTop 1] with n hnL hn
  have hM : (0 : ℝ) < sampleSize n := by
    exact_mod_cast (by simp [sampleSize] : 0 < sampleSize n)
  have hlower := sampleSize_sq_mul_annihilatorWeight_le_energy n hn
  have hweight := (annihilatorWeight_bounds n hn).1
  rw [le_div_iff₀ (sq_pos_of_pos hM)]
  nlinarith

/-- The finite weighted energy is nonnegative. -/
theorem energy_nonneg (n : ℕ) : 0 ≤ energy n := by
  by_cases hn : n = 0
  · subst n
    have hw : 0 ≤ fejerWeight 0 0 := by norm_num [fejerWeight]
    norm_num [energy, labelFejerEnergy, bandwidth, sampleSize,
      fejerFrequencies,
      Theory.PiDigits.BoundaryRobustFejerDichotomy.signedFrequenciesZero,
      hw]
    exact mul_nonneg hw (sq_nonneg _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hH : 1 ≤ bandwidth n := bandwidth_pos n hn1
  unfold energy labelFejerEnergy
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg (fejerWeight_nonneg_of_mem (bandwidth n) hH h
    hh) (sq_nonneg _)

/-- Quantitative upper bound for the density-normalized energy. -/
theorem normalizedEnergyDensity_le_control (n : ℕ) (hn : 1 ≤ n) :
    energy n / ((bandwidth n : ℝ) * (sampleSize n : ℝ) ^ 2) ≤
      2 / (period n : ℝ) + 1 / bandwidth n +
        ((period n : ℝ) / sampleSize n) ^ 2 := by
  let L := (bandwidth n - 1) / period n
  have hD : (0 : ℝ) < period n := by
    exact_mod_cast (by simp [period] : 0 < period n)
  have hH : (0 : ℝ) < bandwidth n := by exact_mod_cast bandwidth_pos n hn
  have hM : (0 : ℝ) < sampleSize n := by
    exact_mod_cast (by simp [sampleSize] : 0 < sampleSize n)
  have hDL : period n * L ≤ bandwidth n - 1 :=
    Nat.mul_div_le (bandwidth n - 1) (period n)
  have hLratio : (L : ℝ) ≤ (bandwidth n : ℝ) / period n := by
    rw [le_div_iff₀ hD]
    have hcast : (period n : ℝ) * L ≤ bandwidth n := by
      exact_mod_cast hDL.trans (Nat.sub_le _ _)
    simpa [mul_comm] using hcast
  have hA := (annihilatorWeight_bounds n hn).2
  change annihilatorWeight n ≤ 2 * (L : ℝ) + 1 at hA
  have hAcontrol : annihilatorWeight n / bandwidth n ≤
      2 / (period n : ℝ) + 1 / bandwidth n := by
    calc
      annihilatorWeight n / bandwidth n ≤ (2 * (L : ℝ) + 1) / bandwidth n :=
        div_le_div_of_nonneg_right hA hH.le
      _ ≤ (2 * ((bandwidth n : ℝ) / period n) + 1) / bandwidth n := by
        gcongr
      _ = 2 / (period n : ℝ) + 1 / bandwidth n := by
        field_simp [hD.ne', hH.ne']
  have hrNat : sampleSize n % period n < period n :=
    Nat.mod_lt _ (by simp [period])
  have hr : ((sampleSize n % period n : ℕ) : ℝ) ≤ period n := by
    exact_mod_cast hrNat.le
  have hrem : (((sampleSize n % period n : ℕ) : ℝ) / sampleSize n) ^ 2 ≤
      ((period n : ℝ) / sampleSize n) ^ 2 := by
    have hdiv : ((sampleSize n % period n : ℕ) : ℝ) / sampleSize n ≤
        (period n : ℝ) / sampleSize n := div_le_div_of_nonneg_right hr hM.le
    have hr0 : (0 : ℝ) ≤ (sampleSize n % period n : ℕ) := by positivity
    nlinarith [div_nonneg hr0 hM.le,
      div_nonneg hD.le hM.le]
  have henergy := energy_le_annihilator_add_remainder n hn
  calc
    energy n / ((bandwidth n : ℝ) * (sampleSize n : ℝ) ^ 2) ≤
        ((sampleSize n : ℝ) ^ 2 * annihilatorWeight n +
          ((sampleSize n % period n : ℕ) : ℝ) ^ 2 * bandwidth n) /
            ((bandwidth n : ℝ) * (sampleSize n : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right henergy (mul_nonneg hH.le (sq_nonneg _))
    _ = annihilatorWeight n / bandwidth n +
        (((sampleSize n % period n : ℕ) : ℝ) / sampleSize n) ^ 2 := by
      field_simp [hH.ne', hM.ne']
    _ ≤ _ := add_le_add hAcontrol hrem

/-- The explicit density control is a sum of decaying geometric sequences. -/
theorem densityControl_eq_geometric (n : ℕ) (hn : 1 ≤ n) :
    2 / (period n : ℝ) + 1 / bandwidth n +
        ((period n : ℝ) / sampleSize n) ^ 2 =
      2 * ((1 : ℝ) / 3) ^ n + 2 * ((1 : ℝ) / 10) ^ n +
        (((3 : ℝ) / 10) ^ n) ^ 2 := by
  have htwo : 2 ∣ sampleSize n := by
    unfold sampleSize
    exact dvd_pow (by norm_num) (by omega)
  have hHr : (bandwidth n : ℝ) = (sampleSize n : ℝ) / 2 := by
    unfold bandwidth
    rw [Nat.cast_div htwo (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [hHr]
  unfold period sampleSize
  push_cast
  simp_rw [div_pow]
  field_simp
  ring_nf

/-- Second normalized-energy limit: dividing additionally by `H` makes the
energy density vanish. -/
theorem normalizedEnergyDensity_tendsto_zero :
    Tendsto (fun n : ℕ =>
      energy n / ((bandwidth n : ℝ) * (sampleSize n : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hthird : Tendsto (fun n : ℕ => ((1 : ℝ) / 3) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htenth : Tendsto (fun n : ℕ => ((1 : ℝ) / 10) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hratio : Tendsto (fun n : ℕ => ((3 : ℝ) / 10) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcontrol : Tendsto (fun n : ℕ =>
      2 * ((1 : ℝ) / 3) ^ n + 2 * ((1 : ℝ) / 10) ^ n +
        (((3 : ℝ) / 10) ^ n) ^ 2) atTop (𝓝 0) := by
    have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / 3) ^ n)
        atTop (𝓝 0) := by simpa using hc2.mul hthird
    have h2 : Tendsto (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / 10) ^ n)
        atTop (𝓝 0) := by simpa using hc2.mul htenth
    simpa [pow_two] using (h1.add h2).add (hratio.mul hratio)
  apply squeeze_zero' (g := fun n : ℕ =>
    2 * ((1 : ℝ) / 3) ^ n + 2 * ((1 : ℝ) / 10) ^ n +
      (((3 : ℝ) / 10) ^ n) ^ 2)
  · exact Filter.Eventually.of_forall fun n =>
      div_nonneg (energy_nonneg n)
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← densityControl_eq_geometric n hn]
    exact normalizedEnergyDensity_le_control n hn
  · exact hcontrol

/-- Consecutive scales use genuinely different rational seeds. -/
theorem seed_succ_lt_seed (n : ℕ) : seed (n + 1) < seed n := by
  unfold seed period
  rw [pow_succ]
  push_cast
  have hp : (0 : ℝ) < 3 ^ n := by positivity
  have hden : (0 : ℝ) < 9 * 3 ^ n := by positivity
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * (3 ^ n * 3)) hden]
  nlinarith

/-- There is no one real number serving as every seed in this family. -/
theorem no_fixed_real_seed : ¬ ∃ x : ℝ, ∀ n : ℕ, seed n = x := by
  rintro ⟨x, hx⟩
  have h := seed_succ_lt_seed 0
  rw [hx 1, hx 0] at h
  exact (lt_irrefl x h)

/-- The same non-fixed-seed statement restricted to the agenda domain
`n >= 1`. -/
theorem no_fixed_real_seed_positive :
    ¬ ∃ x : ℝ, ∀ n : ℕ, 1 ≤ n → seed n = x := by
  rintro ⟨x, hx⟩
  have h := seed_succ_lt_seed 1
  rw [hx 2 (by norm_num), hx 1 (by norm_num)] at h
  exact lt_irrefl x h

/-- Every seed is strictly smaller than pi; in particular this family is not
the decimal orbit of pi. -/
theorem seed_ne_pi (n : ℕ) : seed n ≠ Real.pi := by
  have hseed : seed n ≤ 1 := by
    unfold seed period
    have hden : (1 : ℝ) ≤ 9 * ((3 ^ n : ℕ) : ℝ) := by
      have hp : (0 : ℕ) < 3 ^ n := pow_pos (by norm_num) n
      exact_mod_cast (by omega : (1 : ℕ) ≤ 9 * 3 ^ n)
    have hpos : (0 : ℝ) < 9 * ((3 ^ n : ℕ) : ℝ) := by
      have hp : (0 : ℕ) < 3 ^ n := pow_pos (by norm_num) n
      exact_mod_cast (by omega : (0 : ℕ) < 9 * 3 ^ n)
    exact (div_le_one hpos).2 hden
  nlinarith [Real.pi_gt_three]

/-- Machine-readable scope record. Boolean `false` means that the present
artifact makes no such conclusion. -/
structure ScopeStatus where
  oneFixedRealOrbit : Bool
  isPiOrbit : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  oneFixedRealOrbit := false
  isPiOrbit := false
  provesC1 := false
  disprovesC1 := false

/-- Explicit fixed-real, pi, and C1 nonclaims. -/
theorem explicit_scope_nonclaims :
    scopeStatus.oneFixedRealOrbit = false ∧
      scopeStatus.isPiOrbit = false ∧
      scopeStatus.provesC1 = false ∧ scopeStatus.disprovesC1 = false := by
  norm_num [scopeStatus]

/-- Combined local-structure certificate exposing the agenda parameters and
all finite-orbit conclusions in one statement. -/
theorem T28_local_structure_certificate (n : ℕ) (hn : 1 ≤ n) :
    let M := sampleSize n
    let D := period n
    let H := bandwidth n
    let q := modulus n
    let x_n := seed n
    M = 10 ^ n ∧ D = 3 ^ n ∧ H = M / 2 ∧ M = 2 * H ∧
      q = 9 * D * M ∧ x_n = 1 / (9 * D : ℕ) ∧
      (∀ k : ℕ, 9 * D ∣ 10 ^ k - 1 ↔ D ∣ k) ∧
      orbitLabel n = decimalOrbitLabel x_n q M ∧
      (∀ j : Fin M, orbitLabel n j =
        ((M * 10 ^ j.val : ℕ) : ZMod q)) ∧
      (∀ (j : ℕ) (hj : j + 1 < M),
        orbitLabel n ⟨j + 1, hj⟩ = 10 * orbitLabel n ⟨j, by omega⟩) ∧
      orbitSupport n = affineCoset n ∧ (affineCoset n).card = D ∧
      (∀ z : ZMod q, z ∈ affineCoset n →
        prefixMultiplicity (orbitLabel n) z = M / D ∨
          prefixMultiplicity (orbitLabel n) z = M / D + 1) ∧
      2 * H < q ∧
      (∀ h : ℤ, (D : ℤ) ∣ h → ‖orbitSum n h‖ = M) ∧
      (∀ h : ℤ, ¬(D : ℤ) ∣ h → ‖orbitSum n h‖ ≤ ((M % D : ℕ) : ℝ)) := by
  dsimp only
  have hp := family_parameters n hn
  dsimp only at hp
  rcases hp with ⟨hM, hD, hH, hMH, hq, hx⟩
  refine ⟨hM, hD, hH, hMH, hq, hx, ?_,
    orbitLabel_eq_T25_decimalOrbitLabel n, ?_, ?_,
    (orbitSupport_eq_affineCoset n).1,
    (periodLabel_support_eq_affineCoset n).2, ?_,
    modulus_gt_two_mul_bandwidth n hn, ?_, ?_⟩
  · exact nine_mul_period_dvd_ten_pow_sub_one_iff n
  · intro j
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      orbitLabel_eq_natCast n j
  · intro j hj
    exact orbitLabel_successor_zero n j hj
  · exact affineCoset_multiplicity_floor_or_ceil n
  · exact norm_orbitSum_eq_sampleSize_of_period_dvd n
  · exact norm_orbitSum_le_mod_of_not_period_dvd n

end DecimalFactorComplexity.ScaleDependentDecimalOrbit

#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.family_parameters
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.nine_mul_period_dvd_ten_pow_sub_one_iff
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.orbitLabel_eq_natCast
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.decimalDigitError_eq_zero
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.orbitLabel_successor_zero
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.orbitSupport_eq_affineCoset
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.periodLabel_exact_multiplicity
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.norm_orbitSum_eq_sampleSize_of_period_dvd
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.norm_orbitSum_le_mod_of_not_period_dvd
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.energy_eq_T22_complete_band
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.annihilatorWeight_exact
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.family_aliasFree
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.normalizedEnergy_tendsto_atTop
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.normalizedEnergyDensity_tendsto_zero
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.no_fixed_real_seed_positive
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.seed_ne_pi
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.explicit_scope_nonclaims
#print axioms DecimalFactorComplexity.ScaleDependentDecimalOrbit.T28_local_structure_certificate
