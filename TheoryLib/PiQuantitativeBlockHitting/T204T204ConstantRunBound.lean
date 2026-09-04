import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiDigits.T20BaseTenOrbitDensity

/-!
# T204: constant-run bounds from an irrationality exponent

produced by the free model Muse Spark 1.3 through the modelbench pipeline on
2026-09-03 (wave E2, one task per lemma), against the contracted signatures of
AllMath task pack t204; gate-checked per task; assembled by Codex

The five repaired zero-run lemmas were produced by Claude Opus 5 as a Pi Lab
subagent on 2026-09-04 against the contracted signatures of AllMath task pack
t204b; each task compiled and axiom-checked; assembled by Claude Opus 5.

The original t204 zero-run contract is false as stated: the floor-based digit
stream of a negative real is identically zero (`neg_digits_zero`), so no
eventual bound on zero-run lengths can hold for arbitrary irrational `x`.  The
t204b split repairs it by adding the premise `0 <= x`, giving
`zeroRun_eventually_bounded_of_nonneg`; `Real.pi` satisfies that premise by
`Real.pi_pos.le`.  The `HypothesisForms` consumers below still quantify over
all irrational `x` and therefore remain in their explicit hypothesis form: the
repaired zero-run theorem does not have the shape they demand and does not
discharge them.
-/

namespace Theory.PiDigits.T204ConstantRunBound

def IrrationalityExponentAtMost (x M : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
    ∀ p : ℤ,
      1 / (q : ℝ) ^ (M + ε) ≤
        |x - (p : ℝ) / q|

def ZeroRunAt (x : ℝ) (n L : ℕ) : Prop :=
  ∀ i : Fin L,
    (Theory.PiDigits.T20.decimalDigit x (n + i.val)).val = 0

def NineRunAt (x : ℝ) (n L : ℕ) : Prop :=
  ∀ i : Fin L,
    (Theory.PiDigits.T20.decimalDigit x (n + i.val)).val = 9

theorem measureBelow_implies_exponentAtMost
    {x M : ℝ}
    (h : Theory.PiDigits.LongLagBlockCollisionDecay.T4.IrrationalityMeasureBelow x M) :
    IrrationalityExponentAtMost x M := by
  rcases h with ⟨μ, hμ, hwit⟩
  intro ε hε
  have hgap : 0 < M - μ := sub_pos.mpr hμ
  have hε' : 0 < (M - μ) + ε := add_pos hgap hε
  obtain ⟨Q0, hQ0⟩ := hwit ((M - μ) + ε) hε'
  refine ⟨Q0, fun q hq hqpos p => ?_⟩
  have hbound := hQ0 q hq hqpos p
  have hexp : μ + ((M - μ) + ε) = M + ε := by ring
  rw [hexp] at hbound
  exact le_of_lt hbound

/-- Geometric partial sum for a block of nines. -/
lemma geom_nine (L : ℕ) :
    ∑ i ∈ Finset.range L, (9 : ℝ) * (((10 : ℝ) ^ (i + 1))⁻¹)
      = 1 - ((10 : ℝ) ^ L)⁻¹ := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : (10 : ℝ) ^ (k + 1) = (10 : ℝ) ^ k * 10 := pow_succ _ _
    have h10k : (10 : ℝ) ^ k ≠ 0 := by positivity
    rw [hpow, mul_inv]
    field_simp
    ring

/-- Every decimal digit of a negative real is zero (floor-based stream). -/
lemma neg_digits_zero {x : ℝ} (hx : x < 0) (k : ℕ) :
    (Theory.PiDigits.T20.decimalDigit x k).val = 0 := by
  unfold Theory.PiDigits.T20.decimalDigit
  have hneg : x * (10 : ℝ) ^ (k + 1) < 1 := by
    have hle : x * (10 : ℝ) ^ (k + 1) < 0 := by
      apply mul_neg_of_neg_of_pos hx
      positivity
    linarith
  have hfl : ⌊x * (10 : ℝ) ^ (k + 1)⌋₊ = 0 := Nat.floor_eq_zero.mpr hneg
  simp [Real.digits, hfl]

/-- A nine run forces the shifted fractional part close to one. -/
lemma nine_fract_lower {x : ℝ} (hx0 : 0 ≤ x) (n L : ℕ)
    (h9 : NineRunAt x n L) :
    1 - ((10 : ℝ) ^ L)⁻¹ ≤ Int.fract ((10 : ℝ) ^ n * x) := by
  haveI : NeZero (10 : ℕ) := ⟨by norm_num⟩
  let f : ℝ := Int.fract ((10 : ℝ) ^ n * x)
  have hfmem : f ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hdig : ∀ i : ℕ, i < L →
      Real.digits f (10 : ℕ) i = (⟨9, by norm_num⟩ : Fin 10) := by
    intro i hi
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx0 n i
    have horb : Theory.PiDigits.T20.baseTenOrbit x n = f := rfl
    have hdigit_eq : Theory.PiDigits.T20.decimalDigit f i
        = Theory.PiDigits.T20.decimalDigit x (n + i) := by
      rw [← horb]
      exact hshift
    have hval : (Theory.PiDigits.T20.decimalDigit x (n + i)).val = 9 := by
      have htmp := h9 ⟨i, hi⟩
      simpa using htmp
    have hvalf : (Real.digits f (10 : ℕ) i).val = 9 := by
      have htmp : (Theory.PiDigits.T20.decimalDigit f i).val = 9 := by
        rw [hdigit_eq]
        exact hval
      simpa [Theory.PiDigits.T20.decimalDigit] using htmp
    apply Fin.ext
    simpa using hvalf
  have hterm : ∀ i ∈ Finset.range L,
      Real.ofDigitsTerm (Real.digits f (10 : ℕ)) i
        = (9 : ℝ) * (((10 : ℝ) ^ (i + 1))⁻¹) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hdi := hdig i hiL
    simp only [Real.ofDigitsTerm, hdi]
    simp
  have hsum : ∑ i ∈ Finset.range L, Real.ofDigitsTerm (Real.digits f (10 : ℕ)) i
      = ∑ i ∈ Finset.range L, (9 : ℝ) * (((10 : ℝ) ^ (i + 1))⁻¹) :=
    Finset.sum_congr rfl (fun i hi => hterm i hi)
  have hle := Real.sum_ofDigitsTerm_digits_le (b := (10 : ℕ)) hfmem (n := L)
  rw [hsum, geom_nine] at hle
  exact hle

/-- Ceiling-side approximant upper bound from a nine run. -/
lemma nine_approx_upper {x : ℝ} (hx0 : 0 ≤ x) (n L : ℕ)
    (h9 : NineRunAt x n L) :
    |x - ((⌊(10 : ℝ) ^ n * x⌋ + 1 : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ)|
      ≤ ((10 : ℝ) ^ (n + L))⁻¹ := by
  have hqR : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ n := by push_cast; ring
  have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hqR_pos : (0 : ℝ) < ((10 ^ n : ℕ) : ℝ) := by rw [hqR]; exact hpow_pos
  set y : ℝ := (10 : ℝ) ^ n * x with hy
  have hflower := nine_fract_lower hx0 n L h9
  have hf1 : Int.fract y < 1 := Int.fract_lt_one _
  have hgap : 0 ≤ 1 - Int.fract y := by linarith [Int.fract_nonneg y]
  have hgap_le : 1 - Int.fract y ≤ ((10 : ℝ) ^ L)⁻¹ := by linarith
  have hfract_eq : Int.fract y = y - (⌊y⌋ : ℝ) := rfl
  have hfloor : (⌊y⌋ : ℝ) = y - Int.fract y := by linarith
  have hdiff : ((⌊y⌋ + 1 : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ) - x
      = (1 - Int.fract y) / (10 : ℝ) ^ n := by
    have hp : ((⌊y⌋ + 1 : ℤ) : ℝ) = (⌊y⌋ : ℝ) + 1 := by push_cast; ring
    rw [hp, hfloor, hqR]
    field_simp
    rw [hy]
    ring
  have hnonneg : 0 ≤ ((⌊y⌋ + 1 : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ) - x := by
    rw [hdiff]
    apply div_nonneg hgap (le_of_lt hpow_pos)
  have habs : |x - ((⌊y⌋ + 1 : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ)|
      = ((⌊y⌋ + 1 : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ) - x := by
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
  rw [habs, hdiff]
  have hmul : ((10 : ℝ) ^ L)⁻¹ / (10 : ℝ) ^ n = ((10 : ℝ) ^ (n + L))⁻¹ := by
    rw [pow_add, mul_inv]
    ring
  calc (1 - Int.fract y) / (10 : ℝ) ^ n
      ≤ ((10 : ℝ) ^ L)⁻¹ / (10 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hgap_le (le_of_lt hpow_pos)
    _ = ((10 : ℝ) ^ (n + L))⁻¹ := hmul

/-- Powers of ten dominate naturals. -/
lemma nat_le_pow10 (m : ℕ) : m ≤ 10 ^ m := by
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  have h210 : (2 : ℕ) ^ m ≤ 10 ^ m :=
    pow_le_pow_left₀ (Nat.zero_le _) (by norm_num) m
  omega

theorem nineRun_eventually_bounded
    {x M : ℝ} (hx : Irrational x) (hM : 2 ≤ M)
    (hmu : IrrationalityExponentAtMost x M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      NineRunAt x n L →
        (L : ℝ) ≤ (M - 1 + ε) * n := by
  have _irr : Irrational x := hx
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨Q, hQ⟩ := hmu (ε / 2) hδ
  rcases le_total x 0 with hx0 | hxpos
  · rcases eq_or_lt_of_le hx0 with hxeq | hxneg
    · subst hxeq
      have hirr : Irrational (0 : ℝ) := hx
      have hnot : ¬ Irrational (0 : ℝ) := by simp
      exact False.elim (hnot hirr)
    · refine ⟨1, ?_⟩
      intro n hn L h9
      have hn1 : 1 ≤ n := hn
      have hMε : (0 : ℝ) < M - 1 + ε := by linarith
      have hprod_nonneg : (0 : ℝ) ≤ (M - 1 + ε) * (n : ℝ) := by
        apply mul_nonneg (le_of_lt hMε)
        positivity
      by_cases hL : L = 0
      · subst hL
        simp
        exact hprod_nonneg
      · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
        have hmem : Fin L := ⟨0, hLpos⟩
        have h9val := h9 hmem
        have hzero := neg_digits_zero hxneg (n + (hmem).val)
        rw [hzero] at h9val
        norm_num at h9val
  · refine ⟨max Q 1, ?_⟩
    intro n hn L h9
    have hx0 : 0 ≤ x := hxpos
    have hnQ : Q ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hMε : (0 : ℝ) < M - 1 + ε := by linarith
    by_cases hL : L = 0
    · subst hL
      simp
      apply mul_nonneg (le_of_lt hMε)
      positivity
    · have hq_nat_pos : 0 < 10 ^ n := Nat.pow_pos (by norm_num)
      have hQq : Q ≤ 10 ^ n :=
        le_trans hnQ (nat_le_pow10 n)
      have hqR : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ n := by push_cast; ring
      have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
      set p : ℤ := ⌊(10 : ℝ) ^ n * x⌋ + 1 with hp
      have hlow := hQ (10 ^ n) hQq hq_nat_pos p
      have hup := nine_approx_upper hx0 n L h9
      have hcomb : 1 / ((10 ^ n : ℕ) : ℝ) ^ (M + ε / 2)
          ≤ ((10 : ℝ) ^ (n + L))⁻¹ := le_trans hlow hup
      have h10base : (1 : ℝ) < 10 := by norm_num
      have hnR_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hqR_eq : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ ((n : ℝ)) := by
        rw [hqR, Real.rpow_natCast]
      have hlow_rw : ((10 ^ n : ℕ) : ℝ) ^ (M + ε / 2)
          = (10 : ℝ) ^ ((n : ℝ) * (M + ε / 2)) := by
        rw [hqR_eq, ← Real.rpow_mul (by norm_num)]
      have hup_rw : ((10 : ℝ) ^ (n + L))⁻¹
          = (10 : ℝ) ^ (-(((n : ℝ) + (L : ℝ)))) := by
        have hcast : ((n : ℝ) + (L : ℝ)) = (((n + L : ℕ)) : ℝ) := by
          push_cast
          ring
        rw [hcast, ← Real.rpow_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
      have hlow_inv : (1 : ℝ) / ((10 ^ n : ℕ) : ℝ) ^ (M + ε / 2)
          = (10 : ℝ) ^ (-((n : ℝ) * (M + ε / 2))) := by
        rw [hlow_rw]
        rw [one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
      rw [hlow_inv, hup_rw] at hcomb
      have hexp : -((n : ℝ) * (M + ε / 2)) ≤ -(((n : ℝ) + (L : ℝ))) := by
        have hle := (Real.rpow_le_rpow_left_iff h10base).mp hcomb
        exact hle
      have hL_le : (L : ℝ) ≤ (n : ℝ) * (M + ε / 2) - (n : ℝ) := by linarith
      have hhalf : (n : ℝ) * (M + ε / 2) - (n : ℝ) = (M - 1 + ε / 2) * (n : ℝ) := by
        ring
      rw [hhalf] at hL_le
      have hε2 : (M - 1 + ε / 2) * (n : ℝ) ≤ (M - 1 + ε) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hnR_nonneg
        linarith
      exact le_trans hL_le hε2

/-- Task `pi-t204b-zero-run-01-fract-lt-of-nonneg` — zero digits give the
strict zero cylinder. -/
theorem zeroRun_fract_lt_of_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (n L : ℕ)
    (h0 :
      Theory.PiDigits.T204ConstantRunBound.ZeroRunAt x n L) :
    Int.fract ((10 : ℝ) ^ n * x) < ((10 : ℝ) ^ L)⁻¹ := by
  haveI : NeZero (10 : ℕ) := ⟨by norm_num⟩
  let f : ℝ := Int.fract ((10 : ℝ) ^ n * x)
  have hfmem : f ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have horb : Theory.PiDigits.T20.baseTenOrbit x n = f := rfl
  have hdig : ∀ i : ℕ, i < L →
      Real.digits f (10 : ℕ) i = (⟨0, by norm_num⟩ : Fin 10) := by
    intro i hi
    have hshift := Theory.PiDigits.T20.decimalDigit_baseTenOrbit x hx0 n i
    have hdigit_eq : Theory.PiDigits.T20.decimalDigit f i
        = Theory.PiDigits.T20.decimalDigit x (n + i) := by
      rw [← horb]
      exact hshift
    have hval : (Theory.PiDigits.T20.decimalDigit x (n + i)).val = 0 := by
      have htmp := h0 ⟨i, hi⟩
      simpa using htmp
    have hvalf : (Real.digits f (10 : ℕ) i).val = 0 := by
      have htmp : (Theory.PiDigits.T20.decimalDigit f i).val = 0 := by
        rw [hdigit_eq]
        exact hval
      simpa [Theory.PiDigits.T20.decimalDigit] using htmp
    apply Fin.ext
    simpa using hvalf
  have hterm : ∀ i ∈ Finset.range L,
      Real.ofDigitsTerm (Real.digits f (10 : ℕ)) i = 0 := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hdi := hdig i hiL
    simp only [Real.ofDigitsTerm, hdi]
    simp
  have hsum : ∑ i ∈ Finset.range L,
      Real.ofDigitsTerm (Real.digits f (10 : ℕ)) i = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => hterm i hi)]
    simp
  have hfloor_eq := Real.ofDigits_digits_sum_eq (b := (10 : ℕ)) hfmem (n := L)
  rw [hsum, mul_zero] at hfloor_eq
  have hfloor_nat : ⌊((10 : ℕ) : ℝ) ^ L * f⌋₊ = 0 := by
    exact_mod_cast hfloor_eq.symm
  have hlt := Nat.lt_floor_add_one (((10 : ℕ) : ℝ) ^ L * f)
  rw [hfloor_nat] at hlt
  have hcast : ((10 : ℕ) : ℝ) = (10 : ℝ) := by norm_num
  rw [hcast] at hlt
  have hlt1 : (10 : ℝ) ^ L * f < 1 := by
    simpa using hlt
  have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ L := by positivity
  have hinv_pos : (0 : ℝ) < ((10 : ℝ) ^ L)⁻¹ := inv_pos.mpr hpow_pos
  have hmul := mul_lt_mul_of_pos_left hlt1 hinv_pos
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow_pos), one_mul, mul_one] at hmul
  exact hmul

/-- Task `pi-t204b-zero-run-02-truncation-approx-lt` — explicit truncation
approximant. -/
theorem zeroRun_truncation_approx_lt
    {x : ℝ} (hx0 : 0 ≤ x) (n L : ℕ)
    (h0 :
      Theory.PiDigits.T204ConstantRunBound.ZeroRunAt x n L) :
    |x -
        ((⌊(10 : ℝ) ^ n * x⌋ : ℤ) : ℝ) /
          ((10 ^ n : ℕ) : ℝ)|
      < ((10 : ℝ) ^ (n + L))⁻¹ := by
  have hqR : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ n := by push_cast; ring
  have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hfr := zeroRun_fract_lt_of_nonneg hx0 n L h0
  set y : ℝ := (10 : ℝ) ^ n * x with hy
  have hfract_eq : Int.fract y = y - (⌊y⌋ : ℝ) := rfl
  have hdiff : x - ((⌊y⌋ : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ)
      = Int.fract y / (10 : ℝ) ^ n := by
    rw [hfract_eq, hqR, hy]
    field_simp
  have hnonneg : 0 ≤ x - ((⌊y⌋ : ℤ) : ℝ) / ((10 ^ n : ℕ) : ℝ) := by
    rw [hdiff]
    exact div_nonneg (Int.fract_nonneg _) (le_of_lt hpow_pos)
  rw [abs_of_nonneg hnonneg, hdiff]
  have hinv_pos : (0 : ℝ) < ((10 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpow_pos
  have hstep : Int.fract y * ((10 : ℝ) ^ n)⁻¹
      < ((10 : ℝ) ^ L)⁻¹ * ((10 : ℝ) ^ n)⁻¹ :=
    mul_lt_mul_of_pos_right hfr hinv_pos
  have hL : Int.fract y / (10 : ℝ) ^ n
      = Int.fract y * ((10 : ℝ) ^ n)⁻¹ := by
    rw [div_eq_mul_inv]
  have hR : ((10 : ℝ) ^ L)⁻¹ * ((10 : ℝ) ^ n)⁻¹
      = ((10 : ℝ) ^ (n + L))⁻¹ := by
    rw [pow_add, mul_inv]
    ring
  rw [hL, ← hR]
  exact hstep

/-- Task `pi-t204b-zero-run-03-floor-approx-lower-eventually` — apply the
exponent hypothesis to the truncation numerator. -/
theorem floor_approx_lower_eventually
    {x M : ℝ}
    (hmu :
      Theory.PiDigits.T204ConstantRunBound.IrrationalityExponentAtMost x M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 / (((10 ^ n : ℕ) : ℝ) ^ (M + δ)) ≤
        |x -
          ((⌊(10 : ℝ) ^ n * x⌋ : ℤ) : ℝ) /
            ((10 ^ n : ℕ) : ℝ)| := by
  obtain ⟨Q, hQ⟩ := hmu δ hδ
  refine ⟨Q, fun n hn => ?_⟩
  have hq_pos : 0 < 10 ^ n := Nat.pow_pos (by norm_num)
  have hQq : Q ≤ 10 ^ n := le_trans hn (nat_le_pow10 n)
  exact hQ (10 ^ n) hQq hq_pos ⌊(10 : ℝ) ^ n * x⌋

/-- Task `pi-t204b-zero-run-04-powTen-bounds-force-length-lt` — isolate
strictness and exponent direction. -/
theorem powTen_bounds_force_length_lt
    {M δ a : ℝ} {n L : ℕ}
    (hlower :
      1 / (((10 ^ n : ℕ) : ℝ) ^ (M + δ)) ≤ a)
    (hupper :
      a < ((10 : ℝ) ^ (n + L))⁻¹) :
    (L : ℝ) < (M - 1 + δ) * n := by
  have hcomb : 1 / (((10 ^ n : ℕ) : ℝ) ^ (M + δ))
      < ((10 : ℝ) ^ (n + L))⁻¹ := lt_of_le_of_lt hlower hupper
  have h10base : (1 : ℝ) < 10 := by norm_num
  have hqR : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ n := by push_cast; ring
  have hqR_eq : ((10 ^ n : ℕ) : ℝ) = (10 : ℝ) ^ ((n : ℝ)) := by
    rw [hqR, Real.rpow_natCast]
  have hlow_rw : ((10 ^ n : ℕ) : ℝ) ^ (M + δ)
      = (10 : ℝ) ^ ((n : ℝ) * (M + δ)) := by
    rw [hqR_eq, ← Real.rpow_mul (by norm_num)]
  have hlow_inv : (1 : ℝ) / ((10 ^ n : ℕ) : ℝ) ^ (M + δ)
      = (10 : ℝ) ^ (-((n : ℝ) * (M + δ))) := by
    rw [hlow_rw, one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
  have hup_rw : ((10 : ℝ) ^ (n + L))⁻¹
      = (10 : ℝ) ^ (-(((n : ℝ) + (L : ℝ)))) := by
    have hcast : ((n : ℝ) + (L : ℝ)) = (((n + L : ℕ)) : ℝ) := by
      push_cast
      ring
    rw [hcast, ← Real.rpow_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10)]
  rw [hlow_inv, hup_rw] at hcomb
  have hexp : -((n : ℝ) * (M + δ)) < -(((n : ℝ) + (L : ℝ))) :=
    (Real.rpow_lt_rpow_left_iff h10base).mp hcomb
  have hring : (M - 1 + δ) * (n : ℝ) = (n : ℝ) * (M + δ) - (n : ℝ) := by ring
  rw [hring]
  linarith

/-- Task `pi-t204b-zero-run-05-eventual-bound-of-nonneg` — the valid eventual
zero-run bound for nonnegative reals. -/
theorem zeroRun_eventually_bounded_of_nonneg
    {x M : ℝ} (hx : Irrational x) (hx0 : 0 ≤ x) (hM : 2 ≤ M)
    (hmu :
      Theory.PiDigits.T204ConstantRunBound.IrrationalityExponentAtMost x M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      Theory.PiDigits.T204ConstantRunBound.ZeroRunAt x n L →
        (L : ℝ) ≤ (M - 1 + ε) * n := by
  have _irr : Irrational x := hx
  have _hM : (2 : ℝ) ≤ M := hM
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := floor_approx_lower_eventually hmu hδ
  refine ⟨N, fun n hn L h0 => ?_⟩
  have hlow := hN n hn
  have hup := zeroRun_truncation_approx_lt hx0 n L h0
  have hlt := powTen_bounds_force_length_lt hlow hup
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hwiden : (M - 1 + ε / 2) * (n : ℝ) ≤ (M - 1 + ε) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hn_nonneg
  linarith

namespace HypothesisForms

theorem constantRun_eventually_bounded
    (hZero : ∀ {x M : ℝ}, Irrational x → 2 ≤ M →
      IrrationalityExponentAtMost x M → ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
        ZeroRunAt x n L → (L : ℝ) ≤ (M - 1 + ε) * n)
    (hNine : ∀ {x M : ℝ}, Irrational x → 2 ≤ M →
      IrrationalityExponentAtMost x M → ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
        NineRunAt x n L → (L : ℝ) ≤ (M - 1 + ε) * n)
    {x M : ℝ} (hx : Irrational x) (hM : 2 ≤ M)
    (hmu : IrrationalityExponentAtMost x M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      (ZeroRunAt x n L ∨ NineRunAt x n L) →
        (L : ℝ) ≤ (M - 1 + ε) * n := by
  obtain ⟨N₀, h₀⟩ := hZero hx hM hmu hε
  obtain ⟨N₁, h₁⟩ := hNine hx hM hmu hε
  exact ⟨max N₀ N₁, fun n hn L hdisj => hdisj.elim
    (fun hz => h₀ n (le_trans (Nat.le_max_left N₀ N₁) hn) L hz)
    (fun hn9 => h₁ n (le_trans (Nat.le_max_right N₀ N₁) hn) L hn9)⟩

theorem pi_constantRun_published_bound
    (hConstant : ∀ {x M : ℝ}, Irrational x → 2 ≤ M →
      IrrationalityExponentAtMost x M → ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
        (ZeroRunAt x n L ∨ NineRunAt x n L) →
          (L : ℝ) ≤ (M - 1 + ε) * n)
    (hPublished :
      IrrationalityExponentAtMost Real.pi
        ((7103205334138 : ℝ) / (10 : ℝ) ^ 12))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      (ZeroRunAt Real.pi n L ∨ NineRunAt Real.pi n L) →
        (L : ℝ) ≤
          ((6103205334138 : ℝ) / (10 : ℝ) ^ 12 + ε) * n := by
  have hpi : Irrational Real.pi := irrational_pi
  have hM : (2 : ℝ) ≤ (7103205334138 : ℝ) / (10 : ℝ) ^ 12 := by
    norm_num
  obtain ⟨N, hN⟩ := hConstant hpi hM hPublished hε
  refine ⟨N, fun n hn L hL => ?_⟩
  have h := hN n hn L hL
  have hcoeff : ((7103205334138 : ℝ) / (10 : ℝ) ^ 12 - 1 + ε) =
      ((6103205334138 : ℝ) / (10 : ℝ) ^ 12 + ε) := by
    have hsub : ((7103205334138 : ℝ) / (10 : ℝ) ^ 12 - 1) =
        ((6103205334138 : ℝ) / (10 : ℝ) ^ 12) := by
      norm_num
    linarith
  rwa [hcoeff] at h

end HypothesisForms

end Theory.PiDigits.T204ConstantRunBound
