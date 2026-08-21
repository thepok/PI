import TheoryLib.PiDigits.T20BaseTenOrbitDensity

/-!
# T37: exact cross-base carries and a conditional decimal bridge

Canonical source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Original external source URL: none (this is a human-authored local root).

The canonical target is V1: every finite decimal word, including words with
leading zeroes, occurs contiguously in the decimal expansion of `Real.pi`.

The hypothesis `JMix Real.pi` defined below is unproved. Consequently this file
proves neither V1 nor sibling V3 unconditionally. The exact-coordinate theorem
only obstructs state models that retain the displayed gcd-reduced carry. It
does not rule out an arbitrary finite quotient; whether such a quotient exists
remains open.
-/

namespace Theory.PiDigits.T37

open Filter Finset
open scoped Topology

/-- The half-open cylinder determined by a length and a numeric prefix. -/
def prefixCylinder (base length p : ℕ) : Set ℝ :=
  Set.Ico ((p : ℝ) / (base : ℝ) ^ length)
    (((p + 1 : ℕ) : ℝ) / (base : ℝ) ^ length)

/-- A numeric prefix is valid when it fits in the specified length. -/
def ValidPrefix (base length p : ℕ) : Prop :=
  p < base ^ length

/-- The exact signed endpoint offset between hexadecimal and decimal cylinders. -/
def carry (n m A D : ℕ) : ℤ :=
  (10 ^ m * A : ℕ) - (16 ^ n * D : ℕ)

/-- A hexadecimal cylinder on the common base-16/base-10 denominator. -/
theorem hexCylinder_commonDenominator (n m A : ℕ) :
    prefixCylinder 16 n A =
      Set.Ico
        (((10 ^ m * A : ℕ) : ℝ) / ((16 : ℝ) ^ n * (10 : ℝ) ^ m))
        (((10 ^ m * (A + 1) : ℕ) : ℝ) /
          ((16 : ℝ) ^ n * (10 : ℝ) ^ m)) := by
  apply congrArg₂ Set.Ico
  · push_cast
    field_simp
  · push_cast
    field_simp

/-- A decimal cylinder on the common base-16/base-10 denominator. -/
theorem decimalCylinder_commonDenominator (n m D : ℕ) :
    prefixCylinder 10 m D =
      Set.Ico
        (((16 ^ n * D : ℕ) : ℝ) / ((16 : ℝ) ^ n * (10 : ℝ) ^ m))
        (((16 ^ n * (D + 1) : ℕ) : ℝ) /
          ((16 : ℝ) ^ n * (10 : ℝ) ^ m)) := by
  apply congrArg₂ Set.Ico
  · push_cast
    field_simp
  · push_cast
    field_simp

/-- Exact compatibility test for two half-open cross-base cylinders. -/
theorem cylinders_overlap_iff_carry_bounds (n m A D : ℕ) :
    (prefixCylinder 16 n A ∩ prefixCylinder 10 m D).Nonempty ↔
      -((10 ^ m : ℕ) : ℤ) < carry n m A D ∧
        carry n m A D < ((16 ^ n : ℕ) : ℤ) := by
  simp only [prefixCylinder, Set.Ico_inter_Ico, Set.nonempty_Ico]
  have h16 : 0 < (16 : ℝ) ^ n := by positivity
  have h10 : 0 < (10 : ℝ) ^ m := by positivity
  have hhex :
      (A : ℝ) / (16 : ℝ) ^ n < (A + 1 : ℕ) / (16 : ℝ) ^ n := by
    rw [div_lt_div_iff_of_pos_right h16]
    norm_num
  have hdec :
      (D : ℝ) / (10 : ℝ) ^ m < (D + 1 : ℕ) / (10 : ℝ) ^ m := by
    rw [div_lt_div_iff_of_pos_right h10]
    norm_num
  have hright :
      (A : ℝ) / (16 : ℝ) ^ n < (D + 1 : ℕ) / (10 : ℝ) ^ m ↔
        carry n m A D < ((16 ^ n : ℕ) : ℤ) := by
    rw [div_lt_div_iff₀ h16 h10]
    simp only [carry]
    rw [sub_lt_iff_lt_add]
    norm_cast
    constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h
  have hleft :
      (D : ℝ) / (10 : ℝ) ^ m < (A + 1 : ℕ) / (16 : ℝ) ^ n ↔
        -((10 ^ m : ℕ) : ℤ) < carry n m A D := by
    rw [div_lt_div_iff₀ h10 h16]
    simp only [carry]
    rw [neg_lt_sub_iff_lt_add]
    norm_cast
    constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h
  constructor
  · intro h
    rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
    exact ⟨hleft.mp (by simpa using h.2.1), hright.mp (by simpa using h.1.2)⟩
  · rintro ⟨hl, hr⟩
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by simpa using hhex, by simpa using hright.mpr hr⟩,
      ⟨by simpa using hleft.mpr hl, by simpa using hdec⟩⟩

/-- Signed overlap numerator on the common denominator. It is positive exactly
for compatible half-open cylinders. -/
def signedOverlapNumerator (n m A D : ℕ) : ℤ :=
  min ((10 ^ m * (A + 1) : ℕ) : ℤ) ((16 ^ n * (D + 1) : ℕ) : ℤ) -
    max ((10 ^ m * A : ℕ) : ℤ) ((16 ^ n * D : ℕ) : ℤ)

/-- Exact carry-coordinate form of the signed overlap numerator. -/
theorem signedOverlapNumerator_eq_carry (n m A D : ℕ) :
    signedOverlapNumerator n m A D =
      min (carry n m A D + ((10 ^ m : ℕ) : ℤ)) ((16 ^ n : ℕ) : ℤ) -
        max (carry n m A D) 0 := by
  let q : ℤ := ((16 ^ n * D : ℕ) : ℤ)
  calc
    signedOverlapNumerator n m A D =
        (min ((10 ^ m * (A + 1) : ℕ) : ℤ) ((16 ^ n * (D + 1) : ℕ) : ℤ) - q) -
          (max ((10 ^ m * A : ℕ) : ℤ) ((16 ^ n * D : ℕ) : ℤ) - q) := by
            simp only [signedOverlapNumerator]
            ring
    _ = min (((10 ^ m * (A + 1) : ℕ) : ℤ) - q)
          (((16 ^ n * (D + 1) : ℕ) : ℤ) - q) -
        max (((10 ^ m * A : ℕ) : ℤ) - q)
          (((16 ^ n * D : ℕ) : ℤ) - q) := by
            rw [min_sub_sub_right, max_sub_sub_right]
    _ = min (carry n m A D + ((10 ^ m : ℕ) : ℤ)) ((16 ^ n : ℕ) : ℤ) -
        max (carry n m A D) 0 := by
          simp only [q, carry]
          push_cast
          congr 2 <;> ring

/-- Compatibility is equivalently positivity of the exact signed overlap
numerator. -/
theorem cylinders_overlap_iff_signedOverlapNumerator_pos (n m A D : ℕ) :
    (prefixCylinder 16 n A ∩ prefixCylinder 10 m D).Nonempty ↔
      0 < signedOverlapNumerator n m A D := by
  rw [cylinders_overlap_iff_carry_bounds, signedOverlapNumerator_eq_carry,
    sub_pos, max_lt_iff, lt_min_iff, lt_min_iff]
  have h10 : (0 : ℤ) < (10 ^ m : ℕ) := by positivity
  have h16 : (0 : ℤ) < (16 ^ n : ℕ) := by positivity
  omega

/-- Exact carry transition after appending hexadecimal and decimal blocks. -/
theorem carry_append (n m r s A D H E : ℕ) :
    carry (n + r) (m + s) (16 ^ r * A + H) (10 ^ s * D + E) =
      ((10 ^ s * 16 ^ r : ℕ) : ℤ) * carry n m A D +
        ((10 ^ (m + s) * H : ℕ) : ℤ) -
        ((16 ^ (n + r) * E : ℕ) : ℤ) := by
  simp only [carry]
  push_cast
  simp only [pow_add]
  ring

/-- Numeric value of a fixed-base word, retaining its separate length. -/
def wordValue {base : ℕ} : List (Fin base) → ℕ
  | [] => 0
  | d :: w => d.val * base ^ w.length + wordValue w

def hexTopWord (n : ℕ) : List (Fin 16) :=
  List.replicate n ⟨15, by norm_num⟩

def decimalTopWord (n : ℕ) : List (Fin 10) :=
  List.replicate n ⟨9, by norm_num⟩

def hexTop (n : ℕ) : ℕ := 16 ^ n - 1

def decimalTop (n : ℕ) : ℕ := 10 ^ n - 1

/-- The all-nine decimal word avoids the one-digit forbidden word `2`. -/
theorem decimalTopWord_avoids_two (n : ℕ) :
    (⟨2, by norm_num⟩ : Fin 10) ∉ decimalTopWord n := by
  simp [decimalTopWord]

theorem wordValue_hexTopWord (n : ℕ) :
    wordValue (hexTopWord n) = hexTop n := by
  induction n with
  | zero => simp [hexTopWord, hexTop, wordValue]
  | succ n ih =>
      change wordValue (List.replicate (n + 1) ⟨15, by norm_num⟩) =
        16 ^ (n + 1) - 1
      change wordValue (List.replicate n ⟨15, by norm_num⟩) = 16 ^ n - 1 at ih
      rw [show n + 1 = Nat.succ n by omega, List.replicate_succ, wordValue]
      simp only [List.length_replicate]
      rw [ih, pow_succ]
      have hp : 1 ≤ 16 ^ n := one_le_pow₀ (by norm_num)
      omega

theorem wordValue_decimalTopWord (n : ℕ) :
    wordValue (decimalTopWord n) = decimalTop n := by
  induction n with
  | zero => simp [decimalTopWord, decimalTop, wordValue]
  | succ n ih =>
      change wordValue (List.replicate (n + 1) ⟨9, by norm_num⟩) =
        10 ^ (n + 1) - 1
      change wordValue (List.replicate n ⟨9, by norm_num⟩) = 10 ^ n - 1 at ih
      rw [show n + 1 = Nat.succ n by omega, List.replicate_succ, wordValue]
      simp only [List.length_replicate]
      rw [ih, pow_succ]
      have hp : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
      omega

/-- The exact carry of the all-`F`/all-`9` family. -/
theorem topFamily_carry (n : ℕ) :
    carry n n (hexTop n) (decimalTop n) =
      (16 : ℤ) ^ n - (10 : ℤ) ^ n := by
  simp only [carry, hexTop, decimalTop]
  push_cast
  have h16 : 1 ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  have h10 : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
  rw [Nat.cast_sub h16, Nat.cast_sub h10]
  push_cast
  ring

/-- Both top cylinders meet at every positive level, while the decimal word
still avoids the forbidden digit `2`. -/
theorem topFamily_survives_digitTwo_avoidance (n : ℕ) :
    (prefixCylinder 16 n (hexTop n) ∩
      prefixCylinder 10 n (decimalTop n)).Nonempty ∧
      (⟨2, by norm_num⟩ : Fin 10) ∉ decimalTopWord n := by
  constructor
  · apply (cylinders_overlap_iff_carry_bounds n n (hexTop n) (decimalTop n)).2
    rw [topFamily_carry]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    have h16 : 0 < (16 : ℤ) ^ n := by positivity
    have h10 : 0 < (10 : ℤ) ^ n := by positivity
    constructor <;> nlinarith
  · exact decimalTopWord_avoids_two n

/-- The common factor removed from the top-family carry is exactly `2^n`. -/
theorem topFamily_gcd (n : ℕ) :
    Nat.gcd (10 ^ n) (16 ^ n) = 2 ^ n := by
  have hcop : Nat.Coprime (5 ^ n) (8 ^ n) :=
    (by norm_num : Nat.Coprime 5 8).pow n n
  calc
    Nat.gcd (10 ^ n) (16 ^ n) =
        Nat.gcd (2 ^ n * 5 ^ n) (2 ^ n * 8 ^ n) := by
          congr 1 <;> rw [← mul_pow] <;> norm_num
    _ = 2 ^ n * Nat.gcd (5 ^ n) (8 ^ n) := by
      rw [Nat.gcd_mul_left]
    _ = 2 ^ n := by simp [hcop.gcd_eq_one]

/-- The actual gcd-reduced positive carry of the top family. -/
def reducedTopCarry (n : ℕ) : ℕ :=
  (16 ^ n - 10 ^ n) / Nat.gcd (10 ^ n) (16 ^ n)

/-- Exact formula for the gcd-reduced carry. -/
theorem reducedTopCarry_eq (n : ℕ) :
    reducedTopCarry n = 8 ^ n - 5 ^ n := by
  rw [reducedTopCarry, topFamily_gcd]
  have h16 : 16 ^ n = 2 ^ n * 8 ^ n := by
    rw [← mul_pow]
    norm_num
  have h10 : 10 ^ n = 2 ^ n * 5 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h16, h10, ← Nat.mul_sub_left_distrib]
  simp

theorem reducedCarry_step (n : ℕ) :
    (8 ^ n - 5 ^ n) + 1 ≤ 8 ^ (n + 1) - 5 ^ (n + 1) := by
  have h58 : 5 ^ n ≤ 8 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h8 : 1 ≤ 8 ^ n := one_le_pow₀ (by norm_num : 0 < (8 : ℕ))
  rw [pow_succ, pow_succ]
  omega

theorem level_le_reducedTopCarry (n : ℕ) :
    n ≤ reducedTopCarry n := by
  rw [reducedTopCarry_eq]
  induction n with
  | zero => simp
  | succ n ih =>
      exact (Nat.succ_le_succ ih).trans (reducedCarry_step n)

/-- The explicit gcd-reduced carry family is unbounded. -/
theorem reducedTopCarry_unbounded :
    ∀ B : ℕ, ∃ n : ℕ, 1 ≤ n ∧ B < reducedTopCarry n := by
  intro B
  refine ⟨B + 1, by omega, ?_⟩
  have h := level_le_reducedTopCarry (B + 1)
  omega

/-- Scoped exact-coordinate obstruction: no level-independent bound can hold
for a model that retains this exact gcd-reduced carry coordinate. This says
nothing about arbitrary finite quotients that forget the coordinate. -/
theorem no_uniformBound_exactReducedCarry_coordinate :
    ¬ ∃ B : ℕ, ∀ n : ℕ, 1 ≤ n → reducedTopCarry n ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, hlarge⟩ := reducedTopCarry_unbounded B
  exact (Nat.not_lt_of_ge (hB n hn)) hlarge

/-- A state model retains the exact reduced-carry coordinate when a coordinate
readout recovers `reducedTopCarry n` from every positive-level family state. -/
def RetainsExactReducedCarry {State : Type*}
    (state : ℕ → State) (coordinate : State → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → coordinate (state n) = reducedTopCarry n

/-- No fixed finite state type can represent the surviving family while
retaining its exact gcd-reduced carry coordinate. This deliberately does not
exclude arbitrary finite quotients that forget that coordinate. -/
theorem no_finiteState_exactReducedCarry_model
    {State : Type*} [Fintype State]
    (state : ℕ → State) (coordinate : State → ℕ) :
    ¬ RetainsExactReducedCarry state coordinate := by
  classical
  intro hretain
  let B : ℕ := Finset.univ.sup coordinate
  obtain ⟨n, hn, hlarge⟩ := reducedTopCarry_unbounded B
  have hle : coordinate (state n) ≤ B := by
    exact Finset.le_sup (s := Finset.univ) (f := coordinate) (by simp)
  rw [hretain n hn] at hle
  exact (Nat.not_lt_of_ge hle) hlarge

/-- A simultaneous base-16/base-10 interval transition at orbit time `j`. -/
def CrossBaseTransition (x : ℝ) (n A m D j : ℕ) : Prop :=
  Int.fract ((16 : ℝ) ^ j * x) ∈ prefixCylinder 16 n A ∧
    Int.fract ((10 : ℝ) ^ j * x) ∈ prefixCylinder 10 m D

/-- The empirical frequency of one cross-base interval-transition type. -/
noncomputable def jointTransitionFrequency
    (x : ℝ) (n A m D N : ℕ) : ℝ :=
  by
    classical
    exact (∑ j ∈ Finset.range N,
      if CrossBaseTransition x n A m D j then (1 : ℝ) else 0) / N

/-- T36's joint cross-base mixing hypothesis. Its definition uses only
cross-base interval transitions and limiting frequencies: it contains no V1,
orbit-density, or digit-occurrence predicate. -/
def JMix (x : ℝ) : Prop :=
  ∀ n A m D : ℕ,
    ValidPrefix 16 n A → ValidPrefix 10 m D →
      Tendsto (jointTransitionFrequency x n A m D) atTop
        (𝓝 (((16 : ℝ) ^ n)⁻¹ * ((10 : ℝ) ^ m)⁻¹))

/-- Positive limiting joint frequency forces an actual transition. -/
theorem JMix_implies_crossBaseTransition
    {x : ℝ} (hJ : JMix x) (n A m D : ℕ)
    (hA : ValidPrefix 16 n A) (hD : ValidPrefix 10 m D) :
    ∃ j : ℕ, CrossBaseTransition x n A m D j := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero (N : ℕ) : jointTransitionFrequency x n A m D N = 0 := by
    simp [jointTransitionFrequency, hnone]
  have hlim := hJ n A m D hA hD
  have hlimzero : Tendsto (fun _N : ℕ => (0 : ℝ)) atTop
      (𝓝 (((16 : ℝ) ^ n)⁻¹ * ((10 : ℝ) ^ m)⁻¹)) :=
    hlim.congr' (Filter.Eventually.of_forall fun N => hzero N)
  have htargetZero :
      ((16 : ℝ) ^ n)⁻¹ * ((10 : ℝ) ^ m)⁻¹ = 0 :=
    tendsto_nhds_unique hlimzero tendsto_const_nhds
  have htargetPos :
      0 < ((16 : ℝ) ^ n)⁻¹ * ((10 : ℝ) ^ m)⁻¹ := by positivity
  exact htargetPos.ne' htargetZero

/-- The empty hexadecimal cylinder extracts the decimal-cylinder marginal. -/
theorem JMix_implies_decimalCylinderHit
    {x : ℝ} (hJ : JMix x) (m D : ℕ) (hD : ValidPrefix 10 m D) :
    ∃ j : ℕ,
      Theory.PiDigits.T20.baseTenOrbit x j ∈ prefixCylinder 10 m D := by
  have hA : ValidPrefix 16 0 0 := by simp [ValidPrefix]
  obtain ⟨j, hj⟩ := JMix_implies_crossBaseTransition hJ 0 0 m D hA hD
  refine ⟨j, ?_⟩
  simpa [CrossBaseTransition, Theory.PiDigits.T20.baseTenOrbit] using hj.2

/-- JMix implies T20's exact generic base-ten orbit-density predicate. -/
theorem JMix_implies_baseTenOrbitDense
    {x : ℝ} (hx : 0 ≤ x) (hJ : JMix x) :
    Theory.PiDigits.T20.BaseTenOrbitDense x := by
  apply Theory.PiDigits.T20.everyFiniteDecimalWord_implies_baseTenOrbitDense x hx
  intro s
  have hD : ValidPrefix 10 s.length (Theory.PiDigits.T20.wordValue s) :=
    Theory.PiDigits.T20.wordValue_lt_pow_length s
  obtain ⟨j, hj⟩ :=
    JMix_implies_decimalCylinderHit hJ s.length
      (Theory.PiDigits.T20.wordValue s) hD
  have hdigits := Theory.PiDigits.T20.decimalDigit_eq_of_mem_wordCylinder
    s (Theory.PiDigits.T20.baseTenOrbit x j) (by
      simpa [prefixCylinder] using hj)
  refine ⟨j, ?_⟩
  intro i hi
  exact (Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx j i).symm.trans
    (hdigits i hi)

/-- Conditional bridge to T20. `JMix Real.pi` is not proved in this file. -/
theorem JMix_pi_implies_T20_orbitDensity (hJ : JMix Real.pi) :
    Theory.PiDigits.T20.BaseTenOrbitDense Real.pi :=
  JMix_implies_baseTenOrbitDense Real.pi_pos.le hJ

/-- Conditional bridge from the unproved `JMix Real.pi` hypothesis to the
exact canonical V1 proposition from T7. This is not an unconditional V1 or V3
result. -/
theorem JMix_pi_implies_canonicalV1 (hJ : JMix Real.pi) :
    Theory.PiDigits.V1 := by
  apply Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense.mpr
  exact JMix_pi_implies_T20_orbitDensity hJ

end Theory.PiDigits.T37

#print axioms Theory.PiDigits.T37.hexCylinder_commonDenominator
#print axioms Theory.PiDigits.T37.decimalCylinder_commonDenominator
#print axioms Theory.PiDigits.T37.cylinders_overlap_iff_carry_bounds
#print axioms Theory.PiDigits.T37.signedOverlapNumerator_eq_carry
#print axioms Theory.PiDigits.T37.cylinders_overlap_iff_signedOverlapNumerator_pos
#print axioms Theory.PiDigits.T37.carry_append
#print axioms Theory.PiDigits.T37.topFamily_carry
#print axioms Theory.PiDigits.T37.topFamily_survives_digitTwo_avoidance
#print axioms Theory.PiDigits.T37.topFamily_gcd
#print axioms Theory.PiDigits.T37.reducedTopCarry_eq
#print axioms Theory.PiDigits.T37.reducedTopCarry_unbounded
#print axioms Theory.PiDigits.T37.no_uniformBound_exactReducedCarry_coordinate
#print axioms Theory.PiDigits.T37.no_finiteState_exactReducedCarry_model
#print axioms Theory.PiDigits.T37.JMix_implies_crossBaseTransition
#print axioms Theory.PiDigits.T37.JMix_implies_baseTenOrbitDense
#print axioms Theory.PiDigits.T37.JMix_pi_implies_T20_orbitDensity
#print axioms Theory.PiDigits.T37.JMix_pi_implies_canonicalV1
