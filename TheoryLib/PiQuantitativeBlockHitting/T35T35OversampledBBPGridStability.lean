import TheoryLib.PiQuantitativeBlockHitting.T34T34RecurrentCellTransfer
import TheoryLib.PiQuantitativeBlockHitting.T17T17PowerTenDiophantineReduction
import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset

/-!
# T35: decimal-grid stability for oversampled BBP approximations

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The published irrationality-measure input is Doron Zeilberger and Wadim
Zudilin, "The Irrationality Measure of Pi is at most 7.103205334137...",
Moscow Journal of Combinatorics and Number Theory 9 (2020), 407--419,
DOI `10.2140/moscow.2020.9.407`.  As in T4, that external result is not proved
by Lean: it remains the explicit hypothesis `IrrationalityMeasureBelow pi 8`.

This module isolates a carry-stability fact.  A lower approximation closer to
`x` than every rational with denominator `10^t` cannot cross the `t`-digit
decimal grid.  If `a K` approaches `x` from below with error `< 16^-K`, then
the oversampled approximants `a (7*N)` have the same fixed-length arithmetic
decimal floor code at position `N` as `x`, for every sufficiently large `N`,
provided the restricted exponent-eight Diophantine bound holds.

For the intended application, `a K` is the `K`-th positive BBP truncation of
pi.  The BBP identity and its positive tail estimate are not formalized in the
verified track, so the final specialization retains the geometric-tail
statement as an explicit premise.  No theorem here proves decimal orbit
density or the every-word conjecture.

For context only, the intended BBP values have the following external
`proof sketch` observation; none of `A_K`, `c_k`, or the displayed recurrence
is defined or asserted by a declaration in this module.  Writing
`v N = fract (10^N * A_(7*N))`, the forcing is

`eta_(N+1) = 10^(N+1) * sum_(j=1)^7 c_(7*N+j) / 16^(7*N+j)`,

and `v_(N+1) = fract (10*v_N + eta_(N+1))`.  This does not supply mixing.  If
`s_N = 10^N * (pi-A_(7*N))`, then exactly
`eta_(N+1) = 10*s_N-s_(N+1)` and `fract (v_N+s_N)=fract (10^N*pi)`.
Thus, on the external BBP interpretation, the recurrence is the original
decimal orbit in moving coordinates even though the proved abstract theorem
removes eventual fixed-grid carry ambiguity once its premises are supplied.
-/

noncomputable section

namespace Theory.PiDigits.OversampledBBPGridStability

open Theory.PiDigits.PowerTenDiophantineReduction
open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Filter

/-- The integer floor after scaling `x` by `10^t`; for a general real this
includes its integer part.  It is defined without interval normalization. -/
def decimalPrefixFloor (x : ℝ) (t : ℕ) : ℤ :=
  ⌊(10 : ℝ) ^ t * x⌋

/-- The arithmetic floor code intended to encode the length-`m` decimal block
beginning after `N` digits.  For a nonterminating canonical decimal expansion
this lies between `0` and `10^m-1`; only equality of codes is used below, and
the bridge to the repository's symbolic digit code is not asserted here. -/
def decimalBlockCode (x : ℝ) (N m : ℕ) : ℤ :=
  decimalPrefixFloor x (N + m) -
    (10 ^ m : ℕ) * decimalPrefixFloor x N

/-- A one-sided approximation that is closer than the restricted
power-of-ten Diophantine radius cannot cross the corresponding decimal grid.
-/
theorem decimalPrefixFloor_eq_of_powerTenDiophantine
    {x y : ℝ} {mu A t : ℕ}
    (hD : PowerTenDiophantine x mu A)
    (ht : A ≤ t) (hyx : y ≤ x)
    (hclose : x - y < 1 / (10 : ℝ) ^ (mu * t)) :
    decimalPrefixFloor y t = decimalPrefixFloor x t := by
  let scale : ℝ := (10 : ℝ) ^ t
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hfloor_le : decimalPrefixFloor y t ≤ decimalPrefixFloor x t := by
    apply Int.floor_mono
    exact mul_le_mul_of_nonneg_left hyx hscale.le
  apply le_antisymm hfloor_le
  by_contra hnot
  have hfloor_lt : decimalPrefixFloor y t < decimalPrefixFloor x t :=
    lt_of_not_ge hnot
  let p : ℤ := decimalPrefixFloor x t
  have hscaled_y : scale * y < (p : ℝ) := by
    have h := (Int.floor_lt).mp hfloor_lt
    simpa only [decimalPrefixFloor, scale] using h
  have hy_p : y < (p : ℝ) / scale := by
    rw [lt_div_iff₀ hscale]
    simpa only [mul_comm] using hscaled_y
  have hp_scaled_x : (p : ℝ) ≤ scale * x := by
    simpa only [p, decimalPrefixFloor, scale] using
      (Int.floor_le (scale * x))
  have hp_x : (p : ℝ) / scale ≤ x := by
    rw [div_le_iff₀ hscale]
    simpa only [mul_comm] using hp_scaled_x
  have hdist_lt : |x - (p : ℝ) / scale| < x - y := by
    rw [abs_of_nonneg (sub_nonneg.mpr hp_x)]
    linarith
  have hlower := hD t ht p
  have hscale_eq : scale = (10 : ℝ) ^ t := rfl
  rw [hscale_eq] at hdist_lt
  linarith

/-- Equality of the two prefix floors determining a decimal block gives
equality of the block codes. -/
theorem decimalBlockCode_eq_of_prefixFloor_eq
    {x y : ℝ} {N m : ℕ}
    (hN : decimalPrefixFloor y N = decimalPrefixFloor x N)
    (hNm : decimalPrefixFloor y (N + m) =
      decimalPrefixFloor x (N + m)) :
    decimalBlockCode y N m = decimalBlockCode x N m := by
  simp only [decimalBlockCode, hN, hNm]

/-- The numerical scale inequality needed by sevenfold oversampling holds
eventually at every fixed block length. -/
theorem eventually_powTenEight_lt_powSixteenSeven (m : ℕ) :
    ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      (10 : ℝ) ^ (8 * (N + m)) < (16 : ℝ) ^ (7 * N) := by
  let r : ℝ := (10 : ℝ) ^ 8 / (16 : ℝ) ^ 7
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_one : r < 1 := by
    dsimp [r]
    norm_num
  have ht : Tendsto (fun N : ℕ ↦ r ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_one
  have htarget : 0 < 1 / (10 : ℝ) ^ (8 * m) := by positivity
  have hevent : ∀ᶠ N : ℕ in atTop,
      r ^ N < 1 / (10 : ℝ) ^ (8 * m) :=
    ht.eventually (Iio_mem_nhds htarget)
  obtain ⟨C, hC⟩ := eventually_atTop.1 hevent
  refine ⟨C, fun N hN ↦ ?_⟩
  have hratio := hC N hN
  have hden16 : 0 < (16 : ℝ) ^ (7 * N) := by positivity
  have hden10 : 0 < (10 : ℝ) ^ (8 * m) := by positivity
  have hcross :
      (10 : ℝ) ^ (8 * N) * (10 : ℝ) ^ (8 * m) <
        (16 : ℝ) ^ (7 * N) := by
    dsimp [r] at hratio
    rw [div_pow] at hratio
    have hratio' :
        (10 : ℝ) ^ (8 * N) / (16 : ℝ) ^ (7 * N) <
          1 / (10 : ℝ) ^ (8 * m) := by
      simpa only [← pow_mul] using hratio
    have := (div_lt_div_iff₀ hden16 hden10).mp hratio'
    simpa only [one_mul] using this
  calc
    (10 : ℝ) ^ (8 * (N + m)) =
        (10 : ℝ) ^ (8 * N) * (10 : ℝ) ^ (8 * m) := by
      rw [← pow_add]
      congr 1
      omega
    _ < (16 : ℝ) ^ (7 * N) := hcross

/-- A geometric lower approximation sampled at index `7*N` has the same
length-`m` arithmetic decimal floor code at position `N`, whenever the
displayed numerical scale inequality holds. -/
theorem decimalBlockCode_sevenOversampled_eq
    {x : ℝ} {a : ℕ → ℝ} {A N m : ℕ}
    (hD : PowerTenDiophantine x 8 A)
    (hbelow : ∀ K : ℕ, a K ≤ x)
    (htail : ∀ K : ℕ, x - a K < 1 / (16 : ℝ) ^ K)
    (hN : A ≤ N)
    (hscale : (10 : ℝ) ^ (8 * (N + m)) <
      (16 : ℝ) ^ (7 * N)) :
    decimalBlockCode (a (7 * N)) N m = decimalBlockCode x N m := by
  have hscale_N : (10 : ℝ) ^ (8 * N) < (16 : ℝ) ^ (7 * N) := by
    refine lt_of_le_of_lt ?_ hscale
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10)
    omega
  have hclose_N : x - a (7 * N) < 1 / (10 : ℝ) ^ (8 * N) :=
    (htail (7 * N)).trans
      (one_div_lt_one_div_of_lt (by positivity) hscale_N)
  have hclose_Nm : x - a (7 * N) <
      1 / (10 : ℝ) ^ (8 * (N + m)) :=
    (htail (7 * N)).trans
      (one_div_lt_one_div_of_lt (by positivity) hscale)
  apply decimalBlockCode_eq_of_prefixFloor_eq
  · exact decimalPrefixFloor_eq_of_powerTenDiophantine
      hD hN (hbelow (7 * N)) hclose_N
  · exact decimalPrefixFloor_eq_of_powerTenDiophantine
      hD (hN.trans (Nat.le_add_right N m)) (hbelow (7 * N)) hclose_Nm

/-- At each fixed code length, sevenfold oversampling eventually removes all
decimal-boundary ambiguity.  The cutoff may depend on the code length and on
the onset in the Diophantine premise. -/
theorem eventually_decimalBlockCode_sevenOversampled_eq
    {x : ℝ} {a : ℕ → ℝ} {A : ℕ}
    (hD : PowerTenDiophantine x 8 A)
    (hbelow : ∀ K : ℕ, a K ≤ x)
    (htail : ∀ K : ℕ, x - a K < 1 / (16 : ℝ) ^ K) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (a (7 * N)) N m = decimalBlockCode x N m := by
  intro m
  obtain ⟨Cscale, hscale⟩ := eventually_powTenEight_lt_powSixteenSeven m
  refine ⟨max A Cscale, fun N hN ↦ ?_⟩
  apply decimalBlockCode_sevenOversampled_eq hD hbelow htail
  · exact (le_max_left A Cscale).trans hN
  · exact hscale N ((le_max_right A Cscale).trans hN)

/-- The source-level published statement below exponent eight supplies the
restricted power-of-ten premise used above.  The publication remains an
explicit hypothesis; this theorem only checks the quantifier conversion. -/
theorem irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine
    (hSource : IrrationalityMeasureBelow Real.pi 8) :
    ∃ A : ℕ, PowerTenDiophantine Real.pi 8 A := by
  obtain ⟨Q0, hEffective⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_effectiveIrrationality
      hSource
  refine ⟨Q0, ?_⟩
  intro t ht p
  have ht_pow : Q0 ≤ 10 ^ t := by
    calc
      Q0 ≤ t := ht
      _ ≤ 10 * t := by omega
      _ ≤ 10 ^ t := Nat.mul_le_pow (by norm_num) t
  have hqpos : 0 < 10 ^ t := by positivity
  have hbound := hEffective.2.2 (10 ^ t) ht_pow hqpos p
  have hpow_eq :
      (((10 ^ t : ℕ) : ℝ) ^ (8 : ℝ)) =
        (((10 ^ t : ℕ) : ℝ) ^ (8 : ℕ)) := by
    exact Real.rpow_natCast (((10 ^ t : ℕ) : ℝ)) 8
  rw [hpow_eq] at hbound
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_mul, Nat.mul_comm] using
    hbound.le

/-- Conditional pi-target specialization for an arbitrary approximation
sequence `a`.  Its three displayed premises are the external
irrationality-measure input, one-sidedness below pi, and a geometric tail
bound.  This declaration does not identify `a` with the BBP truncations; that
identification and the corresponding tail proof remain external to the
verified module. -/
theorem pi_eventually_decimalBlockCode_sevenOversampled_eq
    {a : ℕ → ℝ}
    (hSource : IrrationalityMeasureBelow Real.pi 8)
    (hbelow : ∀ K : ℕ, a K ≤ Real.pi)
    (htail : ∀ K : ℕ, Real.pi - a K < 1 / (16 : ℝ) ^ K) :
    ∀ m : ℕ, ∃ C : ℕ, ∀ N : ℕ, C ≤ N →
      decimalBlockCode (a (7 * N)) N m =
        decimalBlockCode Real.pi N m := by
  obtain ⟨A, hD⟩ :=
    irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine hSource
  exact eventually_decimalBlockCode_sevenOversampled_eq hD hbelow htail

end Theory.PiDigits.OversampledBBPGridStability

namespace Theory.PiDigits.OversampledBBPGridStability

#print axioms decimalPrefixFloor_eq_of_powerTenDiophantine
#print axioms decimalBlockCode_eq_of_prefixFloor_eq
#print axioms eventually_powTenEight_lt_powSixteenSeven
#print axioms decimalBlockCode_sevenOversampled_eq
#print axioms eventually_decimalBlockCode_sevenOversampled_eq
#print axioms irrationalityMeasureBelow_eight_implies_exists_powerTenDiophantine
#print axioms pi_eventually_decimalBlockCode_sevenOversampled_eq

end Theory.PiDigits.OversampledBBPGridStability
