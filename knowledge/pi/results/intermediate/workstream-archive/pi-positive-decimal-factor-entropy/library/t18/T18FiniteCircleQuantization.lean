import TheoryLib.PiPositiveDecimalFactorEntropy.T4T4FinitePrefixMultiplicityTransfer
import TheoryLib.PiPositiveDecimalFactorEntropy.T10T10ScaleAdaptiveOrbitFourier
import TheoryLib.PiPositiveDecimalFactorEntropy.T16T16MicroscopicFullEntropy

/-!
# T18: finite cyclic quantization of circle orbit sums

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

The generic construction applies to an arbitrary finite real lift of a circle
sequence.  It uses T16's floor cell
`floor (q * fract x) mod q`, T4's multiplicity normalization, and the standard
characters of `ZMod q`.  The floor error is less than one cell, producing the
displayed constant `2 * pi * |h| * M / q` for an unnormalized orbit sum.

The pi theorem imports T10 and assumes the literal failure of C1.  Its order is
`B`, then `N`, then T10's witnesses, and only then the quantization modulus
`q`.  No conclusion in this file asserts C1 or its failure unconditionally.

The source-pinned T15 audit says that normalized density, a common finite model
across witnesses, and compatibility of multiple frequencies or descendants
remain absent.  This file supplies one finite model per T10 witness only.  It
does not claim that any inverse theorem audited in T15 applies.
-/

noncomputable section

set_option maxHeartbeats 800000

open Finset
open scoped BigOperators ComplexConjugate

namespace DecimalFactorComplexity.FiniteCircleQuantization

open DecimalFactorComplexity
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.MicroscopicFullEntropy
open DecimalFactorComplexity.PairCorrelationConditional
open DecimalFactorComplexity.ScaleAdaptiveOrbitFourier
open DecimalFactorEntropy.FiniteFourierObstruction
open DecimalFactorEntropy.FinitePrefixMultiplicityTransfer

abbrev phase := Theory.PiDigits.T27.phase

/-- Floor quantization of the fractional part of a circle point. -/
def quantizedOrbit {M : ℕ} (x : Fin M → ℝ) (q : ℕ) : Fin M → ZMod q :=
  fun j => cyclicCell q (x j)

/-- Number of sampled orbit points in a specified cyclic cell. -/
def orbitCellMultiplicity {M q : ℕ} (x : Fin M → ℝ) (a : ZMod q) : ℕ :=
  prefixMultiplicity (quantizedOrbit x q) a

/-- The multiplicity measure on `ZMod q`, normalized by the sample size `M`. -/
def orbitCellMeasure {M q : ℕ} (x : Fin M → ℝ) (a : ZMod q) : ℝ :=
  normalizedMultiplicity (quantizedOrbit x q) a

/-- The standard cyclic character indexed by the signed integer `h`. -/
def quantizedCharacter (q : ℕ) [NeZero q] (h : ℤ) : AddChar (ZMod q) ℂ :=
  (ZMod.stdAddChar (N := q)).mulShift (h : ZMod q)

/-- Unnormalized character sum of the quantized orbit. -/
def quantizedOrbitSum {M : ℕ} (x : Fin M → ℝ) (q : ℕ) [NeZero q]
    (h : ℤ) : ℂ :=
  ∑ j : Fin M, quantizedCharacter q h (quantizedOrbit x q j)

/-- The orbit-cell weights are exactly the normalized cell multiplicities. -/
theorem orbitCellMeasure_eq_multiplicity_div {M q : ℕ}
    (x : Fin M → ℝ) (a : ZMod q) :
    orbitCellMeasure x a = (orbitCellMultiplicity x a : ℝ) / M := by
  rfl

/-- For a nonempty sample, the cell multiplicities define a probability
measure on the complete finite cyclic group. -/
theorem orbitCellMeasure_isProbability {M q : ℕ} [NeZero q] (x : Fin M → ℝ)
    (hM : 0 < M) : IsProbability (orbitCellMeasure x : ZMod q → ℝ) := by
  classical
  constructor
  · intro a
    unfold orbitCellMeasure normalizedMultiplicity
    positivity
  · have hsum :
        ∑ a : ZMod q, prefixMultiplicity (quantizedOrbit x q) a = M := by
      simpa using sum_prefixMultiplicity_eq_prefixLength
        (Finset.univ : Finset (ZMod q)) (quantizedOrbit x q) (by simp)
    unfold orbitCellMeasure normalizedMultiplicity
    rw [← Finset.sum_div]
    have hsumR :
        ∑ a : ZMod q, (prefixMultiplicity (quantizedOrbit x q) a : ℝ) =
          (M : ℝ) := by
      exact_mod_cast hsum
    rw [hsumR]
    exact div_self (by exact_mod_cast hM.ne')

/-- The finite-group Fourier coefficient of the multiplicity measure is the
normalized quantized orbit sum. -/
theorem finiteFourier_orbitCellMeasure_eq {M q : ℕ} [NeZero q]
    (x : Fin M → ℝ) (hM : 0 < M) (h : ℤ) :
    finiteFourier (orbitCellMeasure x) (quantizedCharacter q h) =
      ((M : ℂ))⁻¹ * quantizedOrbitSum x q h := by
  classical
  calc
    finiteFourier (orbitCellMeasure x) (quantizedCharacter q h) =
        normalizedPrefixCoefficient (quantizedOrbit x q)
          (quantizedCharacter q h) := by
      symm
      simpa [finiteFourier, orbitCellMeasure] using
        normalizedPrefixCoefficient_eq_multiplicitySum
          (Finset.univ : Finset (ZMod q)) (quantizedOrbit x q)
          (quantizedCharacter q h) hM (by simp)
    _ = ((M : ℂ))⁻¹ * quantizedOrbitSum x q h := rfl

/-- Standard characters at two signed frequencies in the strict window
`|h| < H` cannot alias when `q > 2*H`. -/
theorem lowFrequency_quantizedCharacter_injective
    (q H : ℕ) [NeZero q] (hq : 2 * H < q) :
    Set.InjOn (quantizedCharacter q)
      {h : ℤ | h.natAbs < H} := by
  intro h hh k hk heq
  have hshift : Function.Injective
      (fun r : ZMod q => (ZMod.stdAddChar (N := q)).mulShift r) :=
    AddChar.to_mulShift_inj_of_isPrimitive (ZMod.isPrimitive_stdAddChar q)
  have hcast : (h : ZMod q) = (k : ZMod q) := by
    exact hshift heq
  have hdvd : (q : ℤ) ∣ k - h :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub h k q).mp hcast
  have habsNat : (k - h).natAbs < q := by
    calc
      (k - h).natAbs ≤ k.natAbs + h.natAbs := Int.natAbs_sub_le k h
      _ < H + H := Nat.add_lt_add hk hh
      _ = 2 * H := by omega
      _ < q := hq
  have habs : |k - h| < (q : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast habsNat
  have hz : k - h = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- Every nonzero frequency in the strict window gives a nontrivial character
when `q > 2*H`. -/
theorem lowFrequency_quantizedCharacter_ne_zero
    (q H : ℕ) [NeZero q] (hq : 2 * H < q)
    (h : ℤ) (hh0 : h ≠ 0) (hhH : h.natAbs < H) :
    quantizedCharacter q h ≠ 0 := by
  intro hz
  have h0H : (0 : ℤ).natAbs < H := by
    simp only [Int.natAbs_zero]
    omega
  have heq : quantizedCharacter q h = quantizedCharacter q 0 := by
    simpa [quantizedCharacter, AddChar.one_eq_zero] using hz
  exact hh0 (lowFrequency_quantizedCharacter_injective q H hq hhH h0H heq)

/-- The complex exponential restricted to the imaginary axis is
one-Lipschitz in its real angle. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤
      |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
        Complex.exp (Complex.I * b) *
          (Complex.exp (Complex.I * (a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- Evaluation of the standard character on the floor cell is exactly the
circle phase at the left endpoint of that cell. -/
theorem quantizedCharacter_quantizedOrbit_eq_phase
    {M q : ℕ} [NeZero q] (x : Fin M → ℝ) (j : Fin M) (h : ℤ) :
    quantizedCharacter q h (quantizedOrbit x q j) =
      phase h ((⌊(q : ℝ) * Int.fract (x j)⌋ : ℤ) / (q : ℝ)) := by
  unfold quantizedCharacter quantizedOrbit cyclicCell phase
  rw [AddChar.mulShift_apply, ← Int.cast_mul, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Dividing the floor cell by `q` changes a fractional part by at most the
one-cell floor-rounding constant `1/q`. -/
theorem abs_floor_div_sub_fract_le (q : ℕ) [NeZero q] (y : ℝ) :
    |((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) / q - Int.fract y| ≤
      1 / (q : ℝ) := by
  have hqNat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hfloor :
      ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) ≤
        (q : ℝ) * Int.fract y := Int.floor_le _
  have hcell :
      ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) / q ≤ Int.fract y := by
    apply (div_le_iff₀ hq).2
    simpa [mul_comm] using hfloor
  have hfloorOne :
      (q : ℝ) * Int.fract y <
        ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have heq :
      (Int.fract y - ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) / q) * q =
        (q : ℝ) * Int.fract y -
          ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) := by
    field_simp
  have hlt :
      Int.fract y - ((⌊(q : ℝ) * Int.fract y⌋ : ℤ) : ℝ) / q <
        1 / (q : ℝ) := by
    apply (lt_div_iff₀ hq).2
    rw [heq]
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hcell)]
  simpa only [neg_sub] using hlt.le

/-- One floor-rounded point changes frequency `h` by at most
`2*pi*|h|/q`.  The constant records floor, rather than nearest-cell,
rounding. -/
theorem norm_quantizedCharacter_sub_phase_le
    {M q : ℕ} [NeZero q] (x : Fin M → ℝ) (j : Fin M) (h : ℤ) :
    ‖quantizedCharacter q h (quantizedOrbit x q j) - phase h (x j)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) / q := by
  rw [quantizedCharacter_quantizedOrbit_eq_phase]
  have hfract : phase h (Int.fract (x j)) = phase h (x j) := by
    exact Theory.PiDigits.T29.phase_fract_eq_phase h (x j)
  rw [← hfract]
  let z : ℝ := ((⌊(q : ℝ) * Int.fract (x j)⌋ : ℤ) : ℝ) / q
  let t : ℝ := Int.fract (x j)
  have hexp := norm_exp_I_mul_sub_exp_I_mul_le
    (2 * Real.pi * (h : ℝ) * z) (2 * Real.pi * (h : ℝ) * t)
  have hphase :
      ‖phase h z - phase h t‖ ≤
        |2 * Real.pi * (h : ℝ) * z - 2 * Real.pi * (h : ℝ) * t| := by
    have hz : phase h z =
        Complex.exp
          (Complex.I * ((2 * Real.pi * (h : ℝ) * z : ℝ) : ℂ)) := by
      unfold phase Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring
    have ht : phase h t =
        Complex.exp
          (Complex.I * ((2 * Real.pi * (h : ℝ) * t : ℝ) : ℂ)) := by
      unfold phase Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring
    rw [hz, ht]
    exact hexp
  have hround : |z - t| ≤ 1 / (q : ℝ) := by
    simpa [z, t] using abs_floor_div_sub_fract_le q (x j)
  calc
    ‖phase h z - phase h t‖ ≤
        |2 * Real.pi * (h : ℝ) * z - 2 * Real.pi * (h : ℝ) * t| := hphase
    _ = |2 * Real.pi * (h : ℝ)| * |z - t| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |2 * Real.pi * (h : ℝ)| * (1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hround (abs_nonneg _)
    _ = 2 * Real.pi * (h.natAbs : ℝ) / q := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_nonneg Real.pi_pos.le]
      have habsh : |(h : ℝ)| = (h.natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        norm_num
      rw [habsh]
      ring

/-- Simultaneous explicit orbit-sum approximation for every signed frequency
in the strict bandwidth.  The theorem displays `M`, `H`, `h`, `q`, the
floor-rounding constant, and the alias-prevention hypothesis. -/
theorem simultaneous_quantizedOrbitSum_error
    {M : ℕ} (x : Fin M → ℝ) (H q : ℕ) [NeZero q]
    (hq : 2 * H < q) :
    ∀ h : ℤ, h ≠ 0 → h.natAbs < H →
      quantizedCharacter q h ≠ 0 ∧
      ‖quantizedOrbitSum x q h - ordinaryOrbitSum x h‖ ≤
        2 * Real.pi * (h.natAbs : ℝ) * M / q := by
  intro h hh0 hhH
  refine ⟨lowFrequency_quantizedCharacter_ne_zero q H hq h hh0 hhH, ?_⟩
  rw [quantizedOrbitSum, ordinaryOrbitSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin M,
        (quantizedCharacter q h (quantizedOrbit x q j) - phase h (x j))‖ ≤
        ∑ j : Fin M,
          ‖quantizedCharacter q h (quantizedOrbit x q j) - phase h (x j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin M, 2 * Real.pi * (h.natAbs : ℝ) / q := by
      apply Finset.sum_le_sum
      intro j _hj
      exact norm_quantizedCharacter_sub_phase_le x j h
    _ = 2 * Real.pi * (h.natAbs : ℝ) * M / q := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- A quantitative lower bound survives whenever it exceeds the displayed
rounding loss. -/
theorem quantizedOrbitSum_lower_of_rounding
    {M : ℕ} (x : Fin M → ℝ) (H q : ℕ) [NeZero q]
    (hq : 2 * H < q) (h : ℤ) (hh0 : h ≠ 0) (hhH : h.natAbs < H)
    (L : ℝ)
    (hlower : L + 2 * Real.pi * (h.natAbs : ℝ) * M / q <
      ‖ordinaryOrbitSum x h‖) :
    L < ‖quantizedOrbitSum x q h‖ := by
  have herror :=
    (simultaneous_quantizedOrbitSum_error x H q hq h hh0 hhH).2
  have htriangle :
      ‖ordinaryOrbitSum x h‖ ≤
        ‖quantizedOrbitSum x q h‖ +
          2 * Real.pi * (h.natAbs : ℝ) * M / q := by
    calc
      ‖ordinaryOrbitSum x h‖ =
          ‖(ordinaryOrbitSum x h - quantizedOrbitSum x q h) +
            quantizedOrbitSum x q h‖ := by congr 1; ring
      _ ≤ ‖ordinaryOrbitSum x h - quantizedOrbitSum x q h‖ +
          ‖quantizedOrbitSum x q h‖ := norm_add_le _ _
      _ = ‖quantizedOrbitSum x q h - ordinaryOrbitSum x h‖ +
          ‖quantizedOrbitSum x q h‖ := by
            rw [show ordinaryOrbitSum x h - quantizedOrbitSum x q h =
              -(quantizedOrbitSum x q h - ordinaryOrbitSum x h) by ring,
              norm_neg]
      _ ≤ 2 * Real.pi * (h.natAbs : ℝ) * M / q +
          ‖quantizedOrbitSum x q h‖ := by
            exact add_le_add herror le_rfl
      _ = ‖quantizedOrbitSum x q h‖ +
          2 * Real.pi * (h.natAbs : ℝ) * M / q := add_comm _ _
  linarith

/-- Once a circle orbit sum has a strict lower bound, a modulus can be chosen
after `M`, `H`, and `h` so that it is alias-free and the same strict lower
bound survives quantization. -/
theorem exists_aliasFree_quantization_preserving_lower
    {M : ℕ} (x : Fin M → ℝ) (H : ℕ) (h : ℤ)
    (hM : 0 < M) (hh0 : h ≠ 0) (hhH : h.natAbs < H)
    (L : ℝ) (hL : L < ‖ordinaryOrbitSum x h‖) :
    ∃ q : ℕ, ∃ _hq0 : NeZero q,
      2 * H < q ∧
      IsProbability (orbitCellMeasure x : ZMod q → ℝ) ∧
      (∀ r : ℤ, r ≠ 0 → r.natAbs < H →
        quantizedCharacter q r ≠ 0 ∧
        ‖quantizedOrbitSum x q r - ordinaryOrbitSum x r‖ ≤
          2 * Real.pi * (r.natAbs : ℝ) * M / q) ∧
      L < ‖quantizedOrbitSum x q h‖ := by
  let C : ℝ := 2 * Real.pi * (h.natAbs : ℝ) * M
  let eps : ℝ := ‖ordinaryOrbitSum x h‖ - L
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  obtain ⟨q : ℕ, hq⟩ :=
    exists_nat_gt (max ((2 * H : ℕ) : ℝ) (C / eps))
  have hqAliasReal : ((2 * H : ℕ) : ℝ) < q :=
    (le_max_left _ _).trans_lt hq
  have hqAlias : 2 * H < q := by exact_mod_cast hqAliasReal
  have hqPosNat : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hqAlias
  letI : NeZero q := ⟨hqPosNat.ne'⟩
  have hratio : C / eps < (q : ℝ) :=
    (le_max_right _ _).trans_lt hq
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hqPosNat
  have hC : C < (q : ℝ) * eps := (div_lt_iff₀ heps).mp hratio
  have hsmall : C / (q : ℝ) < eps := by
    apply (div_lt_iff₀ hqReal).2
    simpa [mul_comm] using hC
  have hlowerRound :
      L + 2 * Real.pi * (h.natAbs : ℝ) * M / q <
        ‖ordinaryOrbitSum x h‖ := by
    dsimp [C, eps] at hsmall
    linarith
  refine ⟨q, inferInstance, hqAlias,
    orbitCellMeasure_isProbability x hM,
    simultaneous_quantizedOrbitSum_error x H q hqAlias, ?_⟩
  exact quantizedOrbitSum_lower_of_rounding
    x H q hqAlias h hh0 hhH L hlowerRound

/-- Literal failure of C1 yields T10's witnesses first and an alias-free
modulus afterward.  The finite-group multiplicity coefficient retains the
strict normalized square lower bound `B/M`. -/
theorem piFailureC1_implies_quantized_resonance
    (hfailure :
      ¬ ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n →
          (10 : ℝ) ^ (eta * (n : ℝ)) ≤
            (canonicalFactorComplexity piDecimalStream n : ℝ)) :
    ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ, 1 ≤ N →
      ∃ n k M H : ℕ, ∃ h : ℤ, ∃ q : ℕ, ∃ _hq0 : NeZero q,
        N ≤ n ∧ M = 10 ^ n ∧ 4 ^ k ≤ M ∧
          H = M / 2 ^ (k + 1) ∧ h ≠ 0 ∧ h.natAbs < H ∧
          2 * H < q ∧
          IsProbability
            (orbitCellMeasure
              (fun j : Fin M => piDecimalShiftOrbit j) : ZMod q → ℝ) ∧
          (∀ a : ZMod q,
            orbitCellMeasure
                (fun j : Fin M => piDecimalShiftOrbit j) a =
              (orbitCellMultiplicity
                (fun j : Fin M => piDecimalShiftOrbit j) a : ℝ) / M) ∧
          (∀ r : ℤ, r ≠ 0 → r.natAbs < H →
            quantizedCharacter q r ≠ 0 ∧
            ‖quantizedOrbitSum
                (fun j : Fin M => piDecimalShiftOrbit j) q r -
              piOrbitSum r M‖ ≤
                2 * Real.pi * (r.natAbs : ℝ) * M / q) ∧
          B / (M : ℝ) <
            ‖finiteFourier
              (orbitCellMeasure
                (fun j : Fin M => piDecimalShiftOrbit j))
              (quantizedCharacter q h)‖ ^ 2 := by
  intro B hB N hN
  obtain ⟨n, k, M, H, h, hn, hMdef, hscale, hHdef,
      hh0, hhH, hlarge⟩ :=
    piFailureC1_implies_arbitrarily_large_scale_resonance
      hfailure B hB N hN
  have hMpos : 0 < M := by
    rw [hMdef]
    positivity
  let x : Fin M → ℝ := fun j => piDecimalShiftOrbit j
  have horbit (r : ℤ) : ordinaryOrbitSum x r = piOrbitSum r M := by
    rfl
  have hBM : 0 ≤ B * (M : ℝ) := mul_nonneg hB (by positivity)
  have hlarge' :
      B * (M : ℝ) < ‖ordinaryOrbitSum x h‖ ^ 2 := by
    simpa only [horbit] using hlarge
  have hsqrt :
      Real.sqrt (B * (M : ℝ)) < ‖ordinaryOrbitSum x h‖ :=
    (Real.sqrt_lt hBM (norm_nonneg _)).2 hlarge'
  obtain ⟨q, hq0, hqAlias, hprob, hall, hquantized⟩ :=
    exists_aliasFree_quantization_preserving_lower
      x H h hMpos hh0 hhH (Real.sqrt (B * (M : ℝ))) hsqrt
  letI : NeZero q := hq0
  have hsquare :
      B * (M : ℝ) < ‖quantizedOrbitSum x q h‖ ^ 2 := by
    have hs := (sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).2 hquantized
    rw [Real.sq_sqrt hBM] at hs
    exact hs
  have hcoeff := finiteFourier_orbitCellMeasure_eq (q := q) x hMpos h
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcoeffNorm :
      ‖finiteFourier (orbitCellMeasure x) (quantizedCharacter q h)‖ ^ 2 =
        ‖quantizedOrbitSum x q h‖ ^ 2 / (M : ℝ) ^ 2 := by
    rw [hcoeff, norm_mul, norm_inv]
    simp only [Complex.norm_natCast]
    field_simp
  have hnormalized :
      B / (M : ℝ) <
        ‖finiteFourier (orbitCellMeasure x) (quantizedCharacter q h)‖ ^ 2 := by
    rw [hcoeffNorm]
    rw [div_lt_div_iff₀ hMreal (sq_pos_of_pos hMreal)]
    nlinarith
  refine ⟨n, k, M, H, h, q, hq0, hn, hMdef, hscale, hHdef,
    hh0, hhH, hqAlias, ?_, ?_, ?_, ?_⟩
  · simpa only [x] using hprob
  · intro a
    exact orbitCellMeasure_eq_multiplicity_div
      (fun j : Fin M => piDecimalShiftOrbit j) a
  · intro r hr0 hrH
    have hr := hall r hr0 hrH
    simpa only [x, horbit] using hr
  · simpa only [x] using hnormalized

end DecimalFactorComplexity.FiniteCircleQuantization

#print axioms DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMeasure_eq_multiplicity_div
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.orbitCellMeasure_isProbability
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.finiteFourier_orbitCellMeasure_eq
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.lowFrequency_quantizedCharacter_injective
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.lowFrequency_quantizedCharacter_ne_zero
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.norm_exp_I_mul_sub_exp_I_mul_le
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.quantizedCharacter_quantizedOrbit_eq_phase
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.abs_floor_div_sub_fract_le
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.norm_quantizedCharacter_sub_phase_le
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.simultaneous_quantizedOrbitSum_error
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.quantizedOrbitSum_lower_of_rounding
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.exists_aliasFree_quantization_preserving_lower
#print axioms DecimalFactorComplexity.FiniteCircleQuantization.piFailureC1_implies_quantized_resonance
