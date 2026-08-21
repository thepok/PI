import TheoryLib.PiLacunaryNearReturnSparsity.T61DirectLabelAdjacentPhaseVariance

namespace DecimalFactorComplexity.CorrectedZudilinTransientT68

open Finset

/-- The rational argument of the `j`th base-10 orbit phase. -/
def orbitArgument (a : ℤ) (e m j : ℕ) : ℚ :=
  (a : ℚ) * 10 ^ j / (5 ^ e * m)

/-- The rational argument after adding an integer frequency. -/
def frequencyOrbitArgument (h a : ℤ) (e m j : ℕ) : ℚ :=
  (h : ℚ) * orbitArgument a e m j

/-- The common `e`-step tail argument, whose denominator is coprime to ten
when `m` is. -/
def commonTailArgument (h a : ℤ) (e m t : ℕ) : ℚ :=
  (h : ℚ) * a * 2 ^ e * 10 ^ t / m

theorem orbitArgument_add_transient
    (a : ℤ) (e m t : ℕ) (hm : 0 < m) :
    orbitArgument a e m (e + t) =
      (a : ℚ) * 2 ^ e * 10 ^ t / m := by
  unfold orbitArgument
  rw [pow_add]
  rw [show (10 : ℚ) ^ e = 2 ^ e * 5 ^ e by
    rw [← mul_pow]
    norm_num]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

theorem frequencyOrbitArgument_add_transient
    (h a : ℤ) (e m t : ℕ) (hm : 0 < m) :
    frequencyOrbitArgument h a e m (e + t) =
      commonTailArgument h a e m t := by
  unfold frequencyOrbitArgument commonTailArgument
  rw [orbitArgument_add_transient a e m t hm]
  ring

/-- All-`e,J` decomposition into the first `min e J` terms and the common
coprime-modulus tail.  The tail is empty when `J ≤ e`. -/
theorem rational_orbit_transient_tail_decomposition
    {α : Type*} [AddCommMonoid α]
    (phase : ℚ → α) (h a : ℤ) (e m J : ℕ) (hm : 0 < m) :
    (∑ j ∈ range J, phase (frequencyOrbitArgument h a e m j)) =
      (∑ j ∈ range (min e J),
        phase (frequencyOrbitArgument h a e m j)) +
      ∑ t ∈ range (J - e), phase (commonTailArgument h a e m t) := by
  by_cases heJ : e ≤ J
  · rw [Nat.min_eq_left heJ]
    conv_lhs =>
      rw [show J = e + (J - e) by omega]
    rw [sum_range_add]
    congr 1
    apply sum_congr rfl
    intro t _ht
    rw [frequencyOrbitArgument_add_transient h a e m t hm]
  · have hJe : J ≤ e := by omega
    rw [Nat.min_eq_right hJe, Nat.sub_eq_zero_of_le hJe]
    simp

/-- The decomposition together with the literal assertion that its tail
modulus is coprime to the base. -/
theorem rational_orbit_coprime_tail_decomposition
    {α : Type*} [AddCommMonoid α]
    (phase : ℚ → α) (h a : ℤ) (e m J : ℕ)
    (hm : 0 < m) (hm10 : Nat.Coprime 10 m) :
    ((∑ j ∈ range J, phase (frequencyOrbitArgument h a e m j)) =
        (∑ j ∈ range (min e J),
          phase (frequencyOrbitArgument h a e m j)) +
        ∑ t ∈ range (J - e), phase (commonTailArgument h a e m t)) ∧
      Nat.Coprime 10 m := by
  exact ⟨rational_orbit_transient_tail_decomposition phase h a e m J hm, hm10⟩

/-- Explicit factor data for a frequency `h=5^s g u` and a modulus
`m=g M`.  This avoids assuming that `s` is an exact valuation. -/
structure FrequencyFactorization
    (h : ℤ) (m : ℕ) where
  s : ℕ
  g : ℕ
  u : ℤ
  M : ℕ
  g_pos : 0 < g
  M_pos : 0 < M
  h_eq : h = (5 ^ s : ℕ) * (g : ℤ) * u
  m_eq : m = g * M

def reducedTransient {h : ℤ} {m : ℕ}
    (data : FrequencyFactorization h m) (e : ℕ) : ℕ :=
  e - data.s

def reducedTailArgument {h : ℤ} {m : ℕ}
    (data : FrequencyFactorization h m) (a : ℤ) (e t : ℕ) : ℚ :=
  (a : ℚ) * data.u * 2 ^ (e - data.s) * 5 ^ (data.s - e) *
      10 ^ t / data.M

/-- Conditions certifying that the displayed frequency-dependent fractions
are in lowest terms.  They are explicit rather than inferred from an
unformalized valuation operation. -/
def FrequencyReductionIsLowestTerms
    {h : ℤ} {m : ℕ} (data : FrequencyFactorization h m) (a : ℤ) : Prop :=
  Nat.Coprime a.natAbs (5 * data.M) ∧
  Nat.Coprime data.u.natAbs (5 * data.M) ∧
  Nat.Coprime 2 data.M ∧ Nat.Coprime 5 data.M

theorem reduced_frequency_early_identity
    {h a : ℤ} {e m j : ℕ}
    (data : FrequencyFactorization h m)
    (hj : data.s + j ≤ e) :
    frequencyOrbitArgument h a e m j =
      (a : ℚ) * data.u * 2 ^ j /
        (5 ^ (e - data.s - j) * data.M) := by
  unfold frequencyOrbitArgument orbitArgument
  have hhQ : (h : ℚ) = 5 ^ data.s * data.g * data.u := by
    exact_mod_cast data.h_eq
  have hmQ : (m : ℚ) = data.g * data.M := by
    exact_mod_cast data.m_eq
  rw [hhQ, hmQ]
  rw [show (10 : ℚ) ^ j = 2 ^ j * 5 ^ j by
    rw [← mul_pow]
    norm_num]
  rw [show e = data.s + j + (e - data.s - j) by omega]
  rw [pow_add, pow_add]
  have hgQ : (data.g : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt data.g_pos)
  have hMQ : (data.M : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt data.M_pos)
  field_simp
  congr 2
  omega

theorem reduced_frequency_tail_identity
    {h a : ℤ} {e m t : ℕ}
    (data : FrequencyFactorization h m) :
    frequencyOrbitArgument h a e m (reducedTransient data e + t) =
      reducedTailArgument data a e t := by
  by_cases hse : data.s ≤ e
  · unfold reducedTransient reducedTailArgument
    unfold frequencyOrbitArgument orbitArgument
    have hhQ : (h : ℚ) = 5 ^ data.s * data.g * data.u := by
      exact_mod_cast data.h_eq
    have hmQ : (m : ℚ) = data.g * data.M := by
      exact_mod_cast data.m_eq
    rw [hhQ, hmQ, pow_add]
    rw [show (10 : ℚ) ^ (e - data.s) =
        2 ^ (e - data.s) * 5 ^ (e - data.s) by
      rw [← mul_pow]
      norm_num]
    rw [Nat.sub_eq_zero_of_le hse]
    rw [show e = data.s + (e - data.s) by omega, pow_add]
    have hgQ : (data.g : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.g_pos)
    have hMQ : (data.M : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.M_pos)
    field_simp
    congr 2
    omega
  · have hes : e ≤ data.s := by omega
    unfold reducedTransient reducedTailArgument
    rw [Nat.sub_eq_zero_of_le hes]
    unfold frequencyOrbitArgument orbitArgument
    have hhQ : (h : ℚ) = 5 ^ data.s * data.g * data.u := by
      exact_mod_cast data.h_eq
    have hmQ : (m : ℚ) = data.g * data.M := by
      exact_mod_cast data.m_eq
    rw [hhQ, hmQ]
    simp only [zero_add]
    rw [show data.s = e + (data.s - e) by omega, pow_add]
    have hgQ : (data.g : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.g_pos)
    have hMQ : (data.M : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt data.M_pos)
    field_simp
    rw [Nat.add_sub_cancel_left]
    ring

theorem reduced_frequency_early_denominator_coprime
    {h a : ℤ} {e m j : ℕ}
    (data : FrequencyFactorization h m)
    (hlowest : FrequencyReductionIsLowestTerms data a) :
    Nat.Coprime
      (a.natAbs * data.u.natAbs * 2 ^ j)
      (5 ^ (e - data.s - j) * data.M) := by
  rcases hlowest with ⟨ha, hu, h2M, _h5M⟩
  have ha' : Nat.Coprime a.natAbs
      (5 ^ (e - data.s - j) * data.M) :=
    Nat.Coprime.mul_right
      (ha.coprime_mul_right_right.pow_right (e - data.s - j))
      ha.coprime_mul_left_right
  have hu' : Nat.Coprime data.u.natAbs
      (5 ^ (e - data.s - j) * data.M) :=
    Nat.Coprime.mul_right
      (hu.coprime_mul_right_right.pow_right (e - data.s - j))
      hu.coprime_mul_left_right
  have h2pow : Nat.Coprime (2 ^ j)
      (5 ^ (e - data.s - j) * data.M) :=
    Nat.Coprime.mul_right
      ((by norm_num : Nat.Coprime 2 5).pow j (e - data.s - j))
      (h2M.pow_left j)
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left ha' hu') h2pow

theorem reduced_frequency_tail_denominator_coprime
    {h a : ℤ} {e m : ℕ}
    (data : FrequencyFactorization h m)
    (hlowest : FrequencyReductionIsLowestTerms data a) :
    Nat.Coprime
      (a.natAbs * data.u.natAbs * 2 ^ (e - data.s) *
        5 ^ (data.s - e))
      data.M := by
  rcases hlowest with ⟨ha, hu, h2M, h5M⟩
  exact Nat.Coprime.mul_left
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left ha.coprime_mul_left_right
        hu.coprime_mul_left_right)
      (h2M.pow_left (e - data.s)))
    (h5M.pow_left (data.s - e))

theorem reduced_tail_modulus_coprime_ten
    {h a : ℤ} {m : ℕ}
    (data : FrequencyFactorization h m)
    (hlowest : FrequencyReductionIsLowestTerms data a) :
  Nat.Coprime 10 data.M := by
  rcases hlowest with ⟨_ha, _hu, h2M, h5M⟩
  have hcoprime := Nat.Coprime.mul_left h2M h5M
  norm_num at hcoprime
  exact hcoprime

/-- The frequency-dependent all-`e,J` split.  It shortens the transient from
`e` to `e-s` whenever the supplied frequency contains `5^s`. -/
theorem rational_orbit_reduced_frequency_decomposition
    {α : Type*} [AddCommMonoid α]
    (phase : ℚ → α) {h a : ℤ} {e m J : ℕ}
    (data : FrequencyFactorization h m) :
    (∑ j ∈ range J, phase (frequencyOrbitArgument h a e m j)) =
      (∑ j ∈ range (min (reducedTransient data e) J),
        phase (frequencyOrbitArgument h a e m j)) +
      ∑ t ∈ range (J - reducedTransient data e),
        phase (reducedTailArgument data a e t) := by
  by_cases hrJ : reducedTransient data e ≤ J
  · rw [Nat.min_eq_left hrJ]
    conv_lhs =>
      rw [show J = reducedTransient data e +
          (J - reducedTransient data e) by omega]
    rw [sum_range_add]
    congr 1
    apply sum_congr rfl
    intro t _ht
    rw [reduced_frequency_tail_identity data]
  · have hJr : J ≤ reducedTransient data e := by omega
    rw [Nat.min_eq_right hJr, Nat.sub_eq_zero_of_le hJr]
    simp

/-- The three literal frequency forms occurring in T55 and T61. -/
inductive RouteFrequencyKind
  | t55
  | t61Base
  | t61Ten
  deriving DecidableEq

def routeLength (kind : RouteFrequencyKind) (ell s : ℕ) : ℕ :=
  match kind with
  | .t55 => ell
  | .t61Base | .t61Ten => s

def routeFrequency
    (kind : RouteFrequencyKind) (Cq Ck ell u j : ℕ) : ℤ :=
  match kind with
  | .t55 => -((Cq * u : ℕ) : ℤ)
  | .t61Base =>
      (Ck : ℤ) *
        DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directFrequency
          ell u j
  | .t61Ten =>
      10 * (Ck : ℤ) *
        DecimalFactorComplexity.DirectLabelAdjacentPhaseVarianceT61.directFrequency
          ell u j

/-- Literal finite T55/T61 label and approximation-scale conditions. -/
def T55T61ScaleConditions
    (kind : RouteFrequencyKind)
    (K J ell s R Cq Ck u j : ℕ) (h : ℤ) (ε : ℝ) : Prop :=
  1 ≤ K ∧ 1 ≤ ell ∧ 1 ≤ s ∧ 2 ≤ R ∧
  (R - 1) / 10 < u ∧ u ≤ R - 1 ∧ j < ell ∧
  Cq = (10 ^ s - 1) * Ck ∧
  J = routeLength kind ell s ∧
  h = routeFrequency kind Cq Ck ell u j ∧ h ≠ 0 ∧
  0 < ε ∧ ε ≤ 1 ∧
  (16 * Real.pi * |(h : ℝ)| * (10 ^ J - 1)) / (9 * ε) ≤
    (5 ^ K * (2 * K + 1) : ℕ)

/-- Source-faithful applicability and nontriviality requirements for
Bailey--Crandall Theorem 4.6 after the power-of-five transient. -/
def BaileyCrandallTailApplicable
    (J E M c ν ν0 H : ℕ) (A B D : ℝ) : Prop :=
  1 < c ∧ Nat.Coprime 10 c ∧ M = c ^ ν ∧ 1 ≤ ν0 ∧ ν0 ≤ ν ∧
  Nat.Coprime 10 M ∧ E < J ∧ 1 < M ∧
  0 < A ∧ 0 < B ∧ 0 < D ∧
  (Nat.gcd H M : ℝ) < D * M ∧
  B * (A * Real.sqrt M + ((J - E : ℕ) : ℝ) / Real.sqrt M) *
      Real.log M ≤ (J - E : ℕ)

/-- The complete route-specific package.  The lower bound on `E` is the
displayed corrected-Zudilin common-denominator exponent only; it says nothing
about the unknown reduced exponent. -/
def displayedFiveExponent (K extra : ℕ) : ℕ :=
  2 * K - 1 + extra

def CorrectedZudilinRouteApplicable
    (kind : RouteFrequencyKind)
    (K extra J M c ν ν0 H ell s R Cq Ck u j : ℕ)
    (h a : ℤ) (ε A B D : ℝ) : Prop :=
  H = (h * a * ((2 ^ displayedFiveExponent K extra : ℕ) : ℤ)).natAbs ∧
  T55T61ScaleConditions kind K J ell s R Cq Ck u j h ε ∧
  BaileyCrandallTailApplicable J (displayedFiveExponent K extra)
    M c ν ν0 H A B D

theorem two_mul_add_one_le_five_pow (K : ℕ) (hK : 1 ≤ K) :
    2 * K + 1 ≤ 5 ^ K := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hK0 : K = 0
      · subst K
        norm_num
      · have hKpos : 1 ≤ K := by omega
        have hih := ih hKpos
        rw [pow_succ]
        omega

theorem ten_pow_sub_one_lower (J : ℕ) (hJ : 1 ≤ J) :
    9 * 10 ^ (J - 1) ≤ 10 ^ J - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Nat.succ_sub_one, pow_succ]
  omega

theorem five_pow_shift_lt_48_ten_pow (n : ℕ) :
    5 ^ (n + 2) < 48 * 10 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        5 ^ (n + 1 + 2) = 5 * 5 ^ (n + 2) := by
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
          ring
        _ < 5 * (48 * 10 ^ n) := by omega
        _ ≤ 10 * (48 * 10 ^ n) := by omega
        _ = 48 * 10 ^ (n + 1) := by rw [pow_succ]; ring

theorem five_pow_succ_lt_48_ten_pow_pred (J : ℕ) (hJ : 1 ≤ J) :
    5 ^ (J + 1) < 48 * 10 ^ (J - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  simpa only [Nat.succ_sub_one] using five_pow_shift_lt_48_ten_pow n

theorem approximation_scale_forces_J_lt_two_mul_K_sub_one
    {K J : ℕ} {h : ℤ} {ε : ℝ}
    (hK : 1 ≤ K) (hJ : 1 ≤ J) (hh : h ≠ 0)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hscale :
      (16 * Real.pi * |(h : ℝ)| * (10 ^ J - 1)) / (9 * ε) ≤
        (5 ^ K * (2 * K + 1) : ℕ)) :
    J < 2 * K - 1 := by
  have habsZ : 1 ≤ |h| := Int.one_le_abs hh
  have habsR : (1 : ℝ) ≤ |(h : ℝ)| := by
    exact_mod_cast habsZ
  have htenN := ten_pow_sub_one_lower J hJ
  have htenR : (9 : ℝ) * 10 ^ (J - 1) ≤ 10 ^ J - 1 := by
    have hcast :
        (((9 * 10 ^ (J - 1) : ℕ) : ℝ)) ≤
          (((10 ^ J - 1 : ℕ) : ℝ)) := by
      exact_mod_cast htenN
    have hone : 1 ≤ 10 ^ J := one_le_pow₀ (by norm_num)
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_sub hone, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hcast
    exact hcast
  have hfiveN := five_pow_succ_lt_48_ten_pow_pred J hJ
  have hfiveR : ((5 ^ (J + 1) : ℕ) : ℝ) < 48 * 10 ^ (J - 1) := by
    exact_mod_cast hfiveN
  have htenPos : (0 : ℝ) < 10 ^ (J - 1) := pow_pos (by norm_num) _
  have htermNonneg : (0 : ℝ) ≤ 10 ^ J - 1 := by
    nlinarith
  have hdenPos : (0 : ℝ) < 9 * ε := mul_pos (by norm_num) hε0
  have hscaled := (div_le_iff₀ hdenPos).mp hscale
  have hcoeffPos : (0 : ℝ) < 16 * Real.pi * |(h : ℝ)| := by
    positivity
  have h48coeff : (48 : ℝ) < 16 * Real.pi * |(h : ℝ)| := by
    have hpi16 : (48 : ℝ) < 16 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hmul : 16 * Real.pi ≤ 16 * Real.pi * |(h : ℝ)| := by
      have hnonneg : (0 : ℝ) ≤ 16 * Real.pi := by positivity
      have hmul' := mul_le_mul_of_nonneg_left habsR hnonneg
      simpa using hmul'
    exact lt_of_lt_of_le hpi16 hmul
  have hlower :
      ((5 ^ (J + 1) : ℕ) : ℝ) * (9 * ε) <
        16 * Real.pi * |(h : ℝ)| * (10 ^ J - 1) := by
    calc
      ((5 ^ (J + 1) : ℕ) : ℝ) * (9 * ε) ≤
          ((5 ^ (J + 1) : ℕ) : ℝ) * 9 := by
            have : (9 : ℝ) * ε ≤ 9 := by nlinarith
            exact mul_le_mul_of_nonneg_left this (by positivity)
      _ < (48 * 10 ^ (J - 1)) * 9 :=
        mul_lt_mul_of_pos_right hfiveR (by norm_num)
      _ = 48 * (9 * 10 ^ (J - 1)) := by ring
      _ < (16 * Real.pi * |(h : ℝ)|) * (9 * 10 ^ (J - 1)) :=
        mul_lt_mul_of_pos_right h48coeff (mul_pos (by norm_num) htenPos)
      _ ≤ (16 * Real.pi * |(h : ℝ)|) * (10 ^ J - 1) :=
        mul_le_mul_of_nonneg_left htenR (le_of_lt hcoeffPos)
  have hpowCompareR :
      ((5 ^ (J + 1) : ℕ) : ℝ) <
        ((5 ^ K * (2 * K + 1) : ℕ) : ℝ) := by
    exact lt_of_mul_lt_mul_right (lt_of_lt_of_le hlower hscaled) (le_of_lt hdenPos)
  have hpowCompareN :
      5 ^ (J + 1) < 5 ^ K * (2 * K + 1) := by
    exact_mod_cast hpowCompareR
  have hlinear := two_mul_add_one_le_five_pow K hK
  have hupper : 5 ^ K * (2 * K + 1) ≤ 5 ^ (2 * K) := by
    rw [show 5 ^ (2 * K) = 5 ^ K * 5 ^ K by
      rw [show 2 * K = K + K by omega, pow_add]]
    exact Nat.mul_le_mul_left (5 ^ K) hlinear
  have hpowers : 5 ^ (J + 1) < 5 ^ (2 * K) :=
    lt_of_lt_of_le hpowCompareN hupper
  have hexponents : J + 1 < 2 * K :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp hpowers
  omega

/-- No parameter tuple can satisfy the literal Bailey--Crandall positive-tail
condition and the T55/T61 approximation scale for the displayed corrected
Zudilin denominator. -/
theorem correctedZudilin_route_parameters_incompatible
    (kind : RouteFrequencyKind)
    (K extra J M c ν ν0 H ell s R Cq Ck u j : ℕ)
    (h a : ℤ) (ε A B D : ℝ) :
    ¬ CorrectedZudilinRouteApplicable kind K extra J M c ν ν0 H
      ell s R Cq Ck u j h a ε A B D := by
  intro happ
  rcases happ with ⟨_hH, hroute, hbc⟩
  rcases hroute with
    ⟨hK, hell, hs, _hR, _huLower, _huUpper, _hj, _hCq,
      hJ, _hhEq, hh, hε0, hε1, hscale⟩
  rcases hbc with
    ⟨_hc, _hcoprime, _hpower, _hν0, _hlarge, _hcoprimeM, htail, _hM,
      _hA, _hB, _hD, _hgcd, _hnontrivial⟩
  have hJpos : 1 ≤ J := by
    cases kind <;> simp [routeLength] at hJ <;> omega
  have hshort := approximation_scale_forces_J_lt_two_mul_K_sub_one
    hK hJpos hh hε0 hε1 hscale
  unfold displayedFiveExponent at htail
  omega

end DecimalFactorComplexity.CorrectedZudilinTransientT68

#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.orbitArgument_add_transient
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.frequencyOrbitArgument_add_transient
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.rational_orbit_transient_tail_decomposition
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.rational_orbit_coprime_tail_decomposition
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.reduced_frequency_early_identity
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.reduced_frequency_tail_identity
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.reduced_frequency_early_denominator_coprime
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.reduced_frequency_tail_denominator_coprime
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.reduced_tail_modulus_coprime_ten
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.rational_orbit_reduced_frequency_decomposition
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.two_mul_add_one_le_five_pow
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.ten_pow_sub_one_lower
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.five_pow_shift_lt_48_ten_pow
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.five_pow_succ_lt_48_ten_pow_pred
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.approximation_scale_forces_J_lt_two_mul_K_sub_one
#print axioms DecimalFactorComplexity.CorrectedZudilinTransientT68.correctedZudilin_route_parameters_incompatible
