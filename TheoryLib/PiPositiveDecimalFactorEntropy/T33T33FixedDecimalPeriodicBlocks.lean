import TheoryLib.PiPositiveDecimalFactorEntropy.T31T31DominantPeriodicTransfer
import TheoryLib.PiLacunaryNearReturnSparsity.T2NormalOrbitNearReturns
import TheoryLib.PiDigits.T22ChampernowneDisjunctive

/-!
# T33: one fixed decimal real with dominant periodic blocks

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none recorded; the canonical question was formulated locally.

This file formalizes a sibling construction, not the decimal orbit of pi. One
fixed decimal stream is assembled from increasingly long periodic blocks. The
complete Fejer energy is T31's signed strict-band energy, including frequency
zero. Every limit is along the explicitly defined scale index `s : ℕ`. The
T29 and T30 notes are not premises; all fixed-seed and block-boundary claims
used here are proved in this file.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace DecimalFactorComplexity.FixedDecimalPeriodicBlocks

open DecimalFactorComplexity.DominantPeriodicTransfer
open DecimalFactorComplexity.NormalOrbitNearReturns
open DecimalFactorComplexity.ScaleDependentDecimalOrbit
open DecimalFactorComplexity.FejerSpectralCriterion
open DecimalFactorComplexity.FiniteCircleQuantization
open Theory.PiDigits.T20
open Theory.PiDigits.T22

abbrev Digit := Fin 10
abbrev Stream := ℕ → Digit

/-- The model exponent doubles at each scale. -/
def exponent : ℕ → ℕ
  | 0 => 4
  | s + 1 => 2 * exponent s

/-- Sample size `M_s = 10^(n_s)`. -/
def sampleSize (s : ℕ) : ℕ :=
  ScaleDependentDecimalOrbit.sampleSize (exponent s)

/-- Bandwidth `H_s = M_s / 2`. -/
def bandwidth (s : ℕ) : ℕ :=
  ScaleDependentDecimalOrbit.bandwidth (exponent s)

/-- Exact model period `D_s = 3^(n_s)`. -/
def period (s : ℕ) : ℕ :=
  ScaleDependentDecimalOrbit.period (exponent s)

/-- Decimal look-ahead used away from the right block boundary. -/
def lookahead (s : ℕ) : ℕ := exponent s + s + 10

/-- Start of block `s`; each previous block ends exactly at its sample size. -/
def boundary : ℕ → ℕ
  | 0 => 0
  | s + 1 => sampleSize s

/-- Number of digits in block `s`. -/
def blockLength (s : ℕ) : ℕ := sampleSize s - boundary s

/-- Rational model seed at scale `s`. -/
def modelSeed (s : ℕ) : ℝ :=
  ScaleDependentDecimalOrbit.seed (exponent s)

/-- Block `s` copies the absolute-position digits of its rational model. -/
def digitBlock (s : ℕ) : List Digit :=
  List.ofFn fun i : Fin (blockLength s) =>
    decimalDigit (modelSeed s) (boundary s + i)

/-- One infinite decimal stream assembled from all model blocks. -/
def fixedDigitStream : Stream := concatStream digitBlock

/-- The one fixed real represented by `fixedDigitStream`. -/
def fixedSeed : ℝ := Real.ofDigits fixedDigitStream

/-- The ordinary fractional times-ten orbit of the fixed seed. -/
def fixedOrbit (s : ℕ) : Fin (sampleSize s) → ℝ := fun j =>
  baseTenOrbit fixedSeed j

/-- The ordinary fractional times-ten orbit of the scale-`s` rational model. -/
def periodicModel (s : ℕ) : Fin (sampleSize s) → ℝ := fun j =>
  baseTenOrbit (modelSeed s) j

/-- Old-prefix and final-look-ahead indices are the only exceptions. -/
def exceptions (s : ℕ) : Finset (Fin (sampleSize s)) :=
  Finset.univ.filter fun j =>
    j.val < boundary s ∨ sampleSize s < j.val + lookahead s + 1

/-- Coarse T31 exception budget. -/
def exceptionBudget (s : ℕ) : ℕ := boundary s + lookahead s

/-- Uniform phase tolerance supplied by `lookahead s` copied digits. -/
def phaseError (s : ℕ) : ℝ :=
  2 * Real.pi * bandwidth s / (10 : ℝ) ^ lookahead s

theorem exponent_closed (s : ℕ) : exponent s = 4 * 2 ^ s := by
  induction s with
  | zero => norm_num [exponent]
  | succ s ih => simp [exponent, ih, pow_succ]; ring

theorem exponent_pos (s : ℕ) : 0 < exponent s := by
  rw [exponent_closed]
  positivity

theorem exponent_strictMono : StrictMono exponent := by
  intro a b hab
  rw [exponent_closed, exponent_closed]
  have hp : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  omega

theorem sampleSize_strictMono : StrictMono sampleSize := by
  intro a b hab
  unfold sampleSize ScaleDependentDecimalOrbit.sampleSize
  exact Nat.pow_lt_pow_right (by norm_num) (exponent_strictMono hab)

theorem boundary_lt_sampleSize (s : ℕ) : boundary s < sampleSize s := by
  cases s with
  | zero => simp [boundary, sampleSize, ScaleDependentDecimalOrbit.sampleSize]
  | succ s =>
      simpa [boundary] using sampleSize_strictMono (Nat.lt_succ_self s)

theorem blockLength_pos (s : ℕ) : 0 < blockLength s := by
  have h := boundary_lt_sampleSize s
  unfold blockLength
  omega

theorem digitBlock_ne_nil (s : ℕ) : digitBlock s ≠ [] := by
  rw [List.ne_nil_iff_length_pos]
  simpa [digitBlock] using blockLength_pos s

theorem finiteConcat_digitBlock_length (s : ℕ) :
    (finiteConcat digitBlock s).length = boundary s := by
  induction s with
  | zero => simp [boundary]
  | succ s ih =>
      rw [finiteConcat_succ, List.length_append, ih]
      simp only [digitBlock, List.length_ofFn]
      rw [boundary]
      have h := boundary_lt_sampleSize s
      unfold blockLength
      omega

theorem fixedDigitStream_block_digit (s i : ℕ) (hi : i < blockLength s) :
    fixedDigitStream (boundary s + i) =
      decimalDigit (modelSeed s) (boundary s + i) := by
  have hi' : i < (digitBlock s).length := by simpa [digitBlock] using hi
  have hocc := enumeratedBlock_occursAt_concatStream
    digitBlock digitBlock_ne_nil s i hi'
  rw [finiteConcat_digitBlock_length] at hocc
  simpa [fixedDigitStream, digitBlock] using hocc

theorem fixedSeed_nonneg : 0 ≤ fixedSeed := by
  exact Real.ofDigits_nonneg _

theorem fixedSeed_le_one : fixedSeed ≤ 1 := by
  exact Real.ofDigits_le_one _

/-- Integer translation does not change an integer-frequency phase. -/
theorem phase_natCast (h : ℤ) (q : ℕ) :
    Theory.PiDigits.T27.phase h (q : ℝ) = 1 := by
  unfold Theory.PiDigits.T27.phase
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((q : ℝ) : ℂ) =
        ((q : ℤ) * h : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- Taking fractional part does not change an integer-frequency phase. This
local proof avoids assuming any fixed-seed inverse-limit note. -/
theorem phase_fract_eq_phase (h : ℤ) (x : ℝ) :
    Theory.PiDigits.T27.phase h (Int.fract x) =
      Theory.PiDigits.T27.phase h x := by
  unfold Theory.PiDigits.T27.phase
  rw [Int.fract]
  rw [show
    2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) *
          ((x - (⌊x⌋ : ℤ) : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (x : ℂ) +
          ((-⌊x⌋ * h : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- At every integer frequency, the symbolic decimal tail has exactly the
same phase as the ordinary fractional orbit of the represented real. This
remains valid for the repeating-nine representation. -/
theorem phase_fixedOrbit_eq_tail (h : ℤ) (j : ℕ) :
    Theory.PiDigits.T27.phase h (baseTenOrbit fixedSeed j) =
      Theory.PiDigits.T27.phase h (tailOrbit fixedDigitStream j) := by
  rw [baseTenOrbit]
  have hfract : Theory.PiDigits.T27.phase h
      (Int.fract ((10 : ℝ) ^ j * fixedSeed)) =
        Theory.PiDigits.T27.phase h ((10 : ℝ) ^ j * fixedSeed) :=
    phase_fract_eq_phase _ _
  rw [hfract]
  have hdecomp := Real.ofDigits_eq_sum_add_ofDigits fixedDigitStream j
  have hprefix :
      (∑ i ∈ Finset.range j, Real.ofDigitsTerm fixedDigitStream i) =
        (prefixLabel fixedDigitStream j 0 : ℝ) / (10 : ℝ) ^ j := by
    simpa using prefixSum_eq_label_div fixedDigitStream j 0
  rw [fixedSeed, hdecomp, hprefix]
  have hpow : (0 : ℝ) < 10 ^ j := by positivity
  have hscaled :
      (10 : ℝ) ^ j *
          ((prefixLabel fixedDigitStream j 0 : ℝ) / (10 : ℝ) ^ j +
            ((10 : ℝ) ^ j)⁻¹ *
              Real.ofDigits (fun i => fixedDigitStream (i + j))) =
        (prefixLabel fixedDigitStream j 0 : ℝ) +
          tailOrbit fixedDigitStream j := by
    unfold tailOrbit
    rw [show (fun i => fixedDigitStream (i + j)) =
        (fun i => fixedDigitStream (j + i)) by
      funext i
      rw [Nat.add_comm]]
    field_simp
  simp only [Nat.cast_ofNat]
  rw [hscaled]
  rw [Theory.PiDigits.T27.phase_add_real, phase_natCast, one_mul]

/-- The rational model's floor quantization is exact at every orbit time. -/
theorem model_leftEndpoint_eq_fract (s j : ℕ) :
    (((⌊(ScaleDependentDecimalOrbit.modulus (exponent s) : ℝ) *
          Int.fract ((10 : ℝ) ^ j * modelSeed s)⌋ : ℤ) : ℝ) /
        ScaleDependentDecimalOrbit.modulus (exponent s)) =
      Int.fract ((10 : ℝ) ^ j * modelSeed s) := by
  let n := exponent s
  let d := 9 * ScaleDependentDecimalOrbit.period n
  let m := ScaleDependentDecimalOrbit.sampleSize n
  have hd : 0 < d := by simp [d, ScaleDependentDecimalOrbit.period]
  have hy : (10 : ℝ) ^ j * modelSeed s = ((10 ^ j : ℕ) : ℝ) / d := by
    simp only [modelSeed, ScaleDependentDecimalOrbit.seed, n, d]
    push_cast
    ring
  have hscaled := ScaleDependentDecimalOrbit.modulus_mul_fract_nat_divisor
    d m (10 ^ j) hd
  rw [hy]
  change (((⌊((d * m : ℕ) : ℝ) *
      Int.fract (((10 ^ j : ℕ) : ℝ) / d)⌋ : ℤ) : ℝ) / (d * m : ℕ)) = _
  rw [hscaled, Int.floor_natCast]
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne',
    show (m : ℝ) ≠ 0 by simp [m, ScaleDependentDecimalOrbit.sampleSize]]
  norm_cast

/-- T28's exact quantized character is the ordinary phase of the rational
model point. -/
theorem quantizedCharacter_orbitLabel_eq_phase_model
    (s : ℕ) (j : Fin (sampleSize s)) (h : ℤ) :
    quantizedCharacter (ScaleDependentDecimalOrbit.modulus (exponent s)) h
        (ScaleDependentDecimalOrbit.orbitLabel (exponent s) j) =
      Theory.PiDigits.T27.phase h (periodicModel s j) := by
  change quantizedCharacter (ScaleDependentDecimalOrbit.modulus (exponent s)) h
      (quantizedOrbit
        (fun j : Fin (ScaleDependentDecimalOrbit.sampleSize (exponent s)) =>
          (10 : ℝ) ^ (j : ℕ) * modelSeed s)
        (ScaleDependentDecimalOrbit.modulus (exponent s)) j) = _
  rw [quantizedCharacter_quantizedOrbit_eq_phase,
    model_leftEndpoint_eq_fract]
  rfl

/-- The T31 model sum is definitionally T28's checked rational-orbit sum. -/
theorem circlePrefixSum_periodicModel_eq_orbitSum (s : ℕ) (h : ℤ) :
    circlePrefixSum (periodicModel s) h =
      ScaleDependentDecimalOrbit.orbitSum (exponent s) h := by
  unfold circlePrefixSum ScaleDependentDecimalOrbit.orbitSum
  apply Finset.sum_congr rfl
  intro j _hj
  exact (quantizedCharacter_orbitLabel_eq_phase_model s j h).symm

/-- The ordinary rational model repeats after exactly its T28 period. -/
theorem periodicModel_periodic (s j : ℕ) :
    baseTenOrbit (modelSeed s) (j + period s) =
      baseTenOrbit (modelSeed s) j := by
  let n := exponent s
  let d := 9 * ScaleDependentDecimalOrbit.period n
  let D := ScaleDependentDecimalOrbit.period n
  have hdpos : 0 < d := by simp [d, ScaleDependentDecimalOrbit.period]
  have hdvd : d ∣ 10 ^ D - 1 := by
    exact (ScaleDependentDecimalOrbit.nine_mul_period_dvd_ten_pow_sub_one_iff
      n D).mpr (dvd_refl D)
  obtain ⟨c, hc⟩ := hdvd
  have hten : 1 ≤ 10 ^ D := one_le_pow₀ (by norm_num)
  have hp : 10 ^ D = 1 + d * c := by omega
  have hpR : (10 : ℝ) ^ D = 1 + (d : ℝ) * c := by exact_mod_cast hp
  have hreal :
      (10 : ℝ) ^ (j + D) * ScaleDependentDecimalOrbit.seed n =
        (10 : ℝ) ^ j * ScaleDependentDecimalOrbit.seed n +
          (10 ^ j * c : ℕ) := by
    rw [pow_add, hpR]
    have hseed : ScaleDependentDecimalOrbit.seed n = 1 / (d : ℕ) := by
      simp [ScaleDependentDecimalOrbit.seed, d]
    rw [hseed]
    push_cast
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hdpos.ne']
  unfold baseTenOrbit
  change Int.fract ((10 : ℝ) ^ (j + D) *
      ScaleDependentDecimalOrbit.seed n) = _
  rw [hreal]
  exact Int.fract_add_natCast _ _

/-- T28's rational family supplies all exact T31 periodic-model bounds. -/
theorem periodicModelBounds (s : ℕ) :
    PeriodicModelBounds (periodicModel s) (bandwidth s) (period s) := by
  constructor
  · intro j hj
    apply periodicModel_periodic
  · intro h _hh hdvd
    rw [circlePrefixSum_periodicModel_eq_orbitSum]
    exact ScaleDependentDecimalOrbit.norm_orbitSum_eq_sampleSize_of_period_dvd
      (exponent s) h hdvd
  · intro h _hh hndvd
    rw [circlePrefixSum_periodicModel_eq_orbitSum]
    have hbound :=
      ScaleDependentDecimalOrbit.norm_orbitSum_le_mod_of_not_period_dvd
        (exponent s) h hndvd
    exact hbound.trans (by
      exact_mod_cast (Nat.le_of_lt (Nat.mod_lt _ (by
        simp [ScaleDependentDecimalOrbit.period]))))

/-- The old prefix and final look-ahead contain at most the displayed number
of exceptional sample indices. -/
theorem card_exceptions_le (s : ℕ) :
    (exceptions s).card ≤ exceptionBudget s := by
  classical
  let left : Finset (Fin (sampleSize s)) :=
    Finset.univ.filter fun j => j.val < boundary s
  let right : Finset (Fin (sampleSize s)) :=
    Finset.univ.filter fun j => sampleSize s < j.val + lookahead s + 1
  have hsubset : exceptions s ⊆ left ∪ right := by
    intro j hj
    simp only [exceptions, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [left, right, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hj
  have hleft : left.card ≤ boundary s := by
    change (Finset.univ.filter (fun j : Fin (sampleSize s) =>
      j.val < boundary s)).card ≤ boundary s
    rw [Fin.card_filter_val_lt]
    exact min_le_right _ _
  have hright : right.card ≤ lookahead s := by
    calc
      right.card ≤ (Finset.univ.filter fun k : Fin (sampleSize s) =>
          k.val < lookahead s).card := by
        apply Finset.card_le_card_of_injOn (f := fun j : Fin (sampleSize s) => j.rev)
        · intro j hj
          change j ∈ (Finset.univ.filter fun k : Fin (sampleSize s) =>
            sampleSize s < k.val + lookahead s + 1) at hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          change j.rev ∈ (Finset.univ.filter fun k : Fin (sampleSize s) =>
            k.val < lookahead s)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [Fin.rev]
          omega
        · intro a ha b hb hab
          exact Fin.rev_injective hab
      _ = min (sampleSize s) (lookahead s) := Fin.card_filter_val_lt
      _ ≤ lookahead s := min_le_right _ _
  calc
    (exceptions s).card ≤ (left ∪ right).card := Finset.card_le_card hsubset
    _ ≤ left.card + right.card := Finset.card_union_le left right
    _ ≤ boundary s + lookahead s := Nat.add_le_add hleft hright
    _ = exceptionBudget s := rfl

/-- Every nonexceptional position has a full copied look-ahead inside block
`s`. -/
theorem fixedDigitStream_eq_model_of_not_exception
    (s : ℕ) (j : Fin (sampleSize s)) (hj : j ∉ exceptions s)
    (i : ℕ) (hi : i < lookahead s) :
    fixedDigitStream (j.val + i) =
      decimalDigit (modelSeed s) (j.val + i) := by
  have hjbounds : ¬(j.val < boundary s ∨
      sampleSize s < j.val + lookahead s + 1) := by
    simpa [exceptions] using hj
  have hlower : boundary s ≤ j.val + i := by omega
  have hupper : j.val + i < sampleSize s := by omega
  let k := j.val + i - boundary s
  have hk : k < blockLength s := by
    dsimp [k, blockLength]
    omega
  have hindex : boundary s + k = j.val + i := by
    dsimp [k]
    omega
  rw [← hindex]
  exact fixedDigitStream_block_digit s k hk

/-- Nonexceptional symbolic tails agree with their rational model through the
entire look-ahead. -/
theorem abs_tailOrbit_sub_model_le
    (s : ℕ) (j : Fin (sampleSize s)) (hj : j ∉ exceptions s) :
    |tailOrbit fixedDigitStream j.val -
        tailOrbit (decimalDigit (modelSeed s)) j.val| ≤
      ((10 : ℝ) ^ lookahead s)⁻¹ := by
  unfold tailOrbit
  apply Real.abs_ofDigits_sub_ofDigits_le
  intro i hi
  exact fixedDigitStream_eq_model_of_not_exception s j hj i hi

/-- Integer-frequency phases are Lipschitz with the explicit `2*pi*|h|`
The constant. -/
theorem norm_phase_sub_phase_le (h : ℤ) (u v : ℝ) :
    ‖Theory.PiDigits.T27.phase h u - Theory.PiDigits.T27.phase h v‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) * |u - v| := by
  have hexp := norm_exp_I_mul_sub_exp_I_mul_le
    (2 * Real.pi * (h : ℝ) * u) (2 * Real.pi * (h : ℝ) * v)
  have hphase :
      ‖Theory.PiDigits.T27.phase h u - Theory.PiDigits.T27.phase h v‖ ≤
        |2 * Real.pi * (h : ℝ) * u - 2 * Real.pi * (h : ℝ) * v| := by
    have hu : Theory.PiDigits.T27.phase h u =
        Complex.exp (Complex.I * ((2 * Real.pi * (h : ℝ) * u : ℝ) : ℂ)) := by
      unfold Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring
    have hv : Theory.PiDigits.T27.phase h v =
        Complex.exp (Complex.I * ((2 * Real.pi * (h : ℝ) * v : ℝ) : ℂ)) := by
      unfold Theory.PiDigits.T27.phase
      congr 1
      push_cast
      ring
    rw [hu, hv]
    exact hexp
  calc
    ‖Theory.PiDigits.T27.phase h u - Theory.PiDigits.T27.phase h v‖ ≤
        |2 * Real.pi * (h : ℝ) * u - 2 * Real.pi * (h : ℝ) * v| := hphase
    _ = |2 * Real.pi * (h : ℝ)| * |u - v| := by
      rw [← abs_mul]
      congr 1
      ring
    _ = 2 * Real.pi * (h.natAbs : ℝ) * |u - v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_nonneg Real.pi_pos.le]
      have habsh : |(h : ℝ)| = (h.natAbs : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        norm_num
      rw [habsh]

/-- The fixed orbit and scale model satisfy T31's complete phase
approximation hypothesis. -/
noncomputable def phaseApproximation (s : ℕ) :
    PhaseApproximation (fixedOrbit s) (periodicModel s)
      (bandwidth s) (exceptionBudget s) (phaseError s) := by
  have hH : 1 ≤ bandwidth s := by
    unfold bandwidth ScaleDependentDecimalOrbit.bandwidth
    have hn := exponent_pos s
    have hpow : 2 ≤ ScaleDependentDecimalOrbit.sampleSize (exponent s) := by
      unfold ScaleDependentDecimalOrbit.sampleSize
      have : 10 ≤ 10 ^ exponent s := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num) hn
      omega
    omega
  refine
    { exceptions := exceptions s
      card_exceptions := card_exceptions_le s
      eps_nonneg := by unfold phaseError; positivity
      close_phase := ?_ }
  intro h hh j hj
  have hfreq : h.natAbs < bandwidth s :=
    (mem_fejerFrequencies_iff hH).mp hh
  change ‖Theory.PiDigits.T27.phase h (baseTenOrbit fixedSeed j.val) -
      Theory.PiDigits.T27.phase h (baseTenOrbit (modelSeed s) j.val)‖ ≤ _
  rw [phase_fixedOrbit_eq_tail]
  rw [← tailOrbit_decimalDigit_eq_baseTenOrbit (modelSeed s) (by
    unfold modelSeed ScaleDependentDecimalOrbit.seed
    positivity) j.val]
  have htail := abs_tailOrbit_sub_model_le s j hj
  calc
    ‖Theory.PiDigits.T27.phase h (tailOrbit fixedDigitStream j.val) -
        Theory.PiDigits.T27.phase h
          (tailOrbit (decimalDigit (modelSeed s)) j.val)‖ ≤
      2 * Real.pi * (h.natAbs : ℝ) *
        |tailOrbit fixedDigitStream j.val -
          tailOrbit (decimalDigit (modelSeed s)) j.val| :=
        norm_phase_sub_phase_le _ _ _
    _ ≤ 2 * Real.pi * (h.natAbs : ℝ) *
        ((10 : ℝ) ^ lookahead s)⁻¹ := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 2 * Real.pi * (bandwidth s : ℝ) *
        ((10 : ℝ) ^ lookahead s)⁻¹ := by
      gcongr
    _ = phaseError s := by
      unfold phaseError
      rw [div_eq_mul_inv]

/-! ## Explicit recursive parameters and asymptotic hypotheses -/

/-- All recursively defined parameters and exact scale identities are exposed
in one named statement. -/
theorem recursive_parameters (s : ℕ) :
    exponent s = 4 * 2 ^ s ∧
      sampleSize s = 10 ^ exponent s ∧
      bandwidth s = sampleSize s / 2 ∧
      sampleSize s = 2 * bandwidth s ∧
      period s = 3 ^ exponent s ∧
      boundary (s + 1) = sampleSize s ∧
      lookahead s = exponent s + s + 10 ∧
      exceptionBudget s = boundary s + lookahead s := by
  refine ⟨exponent_closed s, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  exact (ScaleDependentDecimalOrbit.family_parameters (exponent s)
    (exponent_pos s)).2.2.2.1

/-- The phase error simplifies to a geometric sequence independent of the
rapid model exponent. -/
theorem phaseError_eq_geometric (s : ℕ) :
    phaseError s = Real.pi * ((1 : ℝ) / 10) ^ (s + 10) := by
  have htwo : 2 ∣ ScaleDependentDecimalOrbit.sampleSize (exponent s) := by
    unfold ScaleDependentDecimalOrbit.sampleSize
    exact dvd_pow (by norm_num) (exponent_pos s).ne'
  unfold phaseError bandwidth ScaleDependentDecimalOrbit.bandwidth lookahead
  rw [Nat.cast_div htwo (by norm_num : (2 : ℝ) ≠ 0)]
  unfold ScaleDependentDecimalOrbit.sampleSize
  push_cast
  rw [show exponent s + s + 10 = exponent s + (s + 10) by omega]
  rw [pow_add]
  have hp : (10 : ℝ) ^ exponent s ≠ 0 := by positivity
  rw [div_pow]
  norm_num
  field_simp [hp]

/-- The preceding block occupies an exactly geometric fraction of the next
sample after shifting the scale index once. -/
theorem boundary_div_sampleSize_succ (s : ℕ) :
    (boundary (s + 1) : ℝ) / sampleSize (s + 1) =
      ((1 : ℝ) / 10) ^ exponent s := by
  rw [boundary]
  unfold sampleSize ScaleDependentDecimalOrbit.sampleSize
  rw [show exponent (s + 1) = 2 * exponent s by simp [exponent]]
  push_cast
  rw [pow_mul]
  have hpow : (10 : ℝ) ^ exponent s ≠ 0 := by positivity
  rw [div_pow]
  norm_num
  field_simp [hpow]
  rw [← pow_mul]
  rw [show exponent s * 2 = 2 * exponent s by omega, pow_mul]
  norm_num

/-- The elementary linear overhead is dominated by four model exponents. -/
theorem lookahead_le_four_mul_exponent (s : ℕ) :
    lookahead s ≤ 4 * exponent s := by
  have haux : s + 10 ≤ 3 * exponent s := by
    induction s with
    | zero => norm_num [exponent]
    | succ s ih =>
        rw [exponent]
        have hp := exponent_pos s
        omega
  unfold lookahead
  omega

theorem exponent_tendsto_atTop : Tendsto exponent atTop atTop :=
  exponent_strictMono.tendsto_atTop

theorem lookahead_div_sampleSize_eq (s : ℕ) :
    (lookahead s : ℝ) / sampleSize s =
      (lookahead s : ℝ) * ((1 : ℝ) / 10) ^ exponent s := by
  unfold sampleSize ScaleDependentDecimalOrbit.sampleSize
  push_cast
  rw [div_pow]
  norm_num
  ring

theorem lookahead_div_sampleSize_tendsto_zero :
    Tendsto (fun s => (lookahead s : ℝ) / sampleSize s) atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun n : ℕ => (n : ℝ) * ((1 : ℝ) / 10) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hcomp := hbase.comp exponent_tendsto_atTop
  have hupper : Tendsto (fun s : ℕ =>
      4 * ((exponent s : ℝ) * ((1 : ℝ) / 10) ^ exponent s))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hcomp : Tendsto (fun s : ℕ =>
      (4 : ℝ) * ((exponent s : ℝ) * ((1 : ℝ) / 10) ^ exponent s))
      atTop (𝓝 (4 * 0)))
  apply squeeze_zero' (g := fun s : ℕ =>
    4 * ((exponent s : ℝ) * ((1 : ℝ) / 10) ^ exponent s))
  · exact Filter.Eventually.of_forall fun s => by positivity
  · exact Filter.Eventually.of_forall fun s => by
      rw [lookahead_div_sampleSize_eq]
      have hc : (lookahead s : ℝ) ≤ 4 * exponent s := by
        exact_mod_cast lookahead_le_four_mul_exponent s
      have hr : 0 ≤ ((1 : ℝ) / 10) ^ exponent s := by positivity
      calc
        (lookahead s : ℝ) * ((1 : ℝ) / 10) ^ exponent s ≤
            (4 * (exponent s : ℝ)) * ((1 : ℝ) / 10) ^ exponent s :=
          mul_le_mul_of_nonneg_right hc hr
        _ = 4 * ((exponent s : ℝ) *
            ((1 : ℝ) / 10) ^ exponent s) := by ring
  · exact hupper

theorem boundary_div_sampleSize_tendsto_zero :
    Tendsto (fun s => (boundary s : ℝ) / sampleSize s) atTop (𝓝 0) := by
  have hgeo : Tendsto (fun s : ℕ => ((1 : ℝ) / 10) ^ exponent s)
      atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      exponent_tendsto_atTop
  have hshift : Tendsto (fun s : ℕ =>
      (boundary (s + 1) : ℝ) / sampleSize (s + 1)) atTop (𝓝 0) := by
    simpa only [boundary_div_sampleSize_succ] using hgeo
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

theorem exceptionBudget_div_sampleSize_tendsto_zero :
    Tendsto (fun s => (exceptionBudget s : ℝ) / sampleSize s)
      atTop (𝓝 0) := by
  have hsum := boundary_div_sampleSize_tendsto_zero.add
    lookahead_div_sampleSize_tendsto_zero
  simpa [exceptionBudget, add_div] using hsum

theorem phaseError_tendsto_zero :
    Tendsto phaseError atTop (𝓝 0) := by
  have hgeo : Tendsto (fun s : ℕ => ((1 : ℝ) / 10) ^ (s + 10))
      atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 10)
  have hmul : Tendsto (fun s : ℕ =>
      Real.pi * ((1 : ℝ) / 10) ^ (s + 10)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hgeo : Tendsto (fun s : ℕ =>
      Real.pi * ((1 : ℝ) / 10) ^ (s + 10)) atTop (𝓝 (Real.pi * 0)))
  convert hmul using 1
  funext s
  exact phaseError_eq_geometric s

theorem period_div_sampleSize_tendsto_zero :
    Tendsto (fun s => (period s : ℝ) / sampleSize s) atTop (𝓝 0) := by
  have hgeo : Tendsto (fun n : ℕ => ((3 : ℝ) / 10) ^ n)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcomp := hgeo.comp exponent_tendsto_atTop
  convert hcomp using 1
  funext s
  unfold period sampleSize ScaleDependentDecimalOrbit.period
    ScaleDependentDecimalOrbit.sampleSize
  simp only [Function.comp_apply]
  push_cast
  rw [div_pow]

theorem bandwidth_div_period_tendsto_atTop :
    Tendsto (fun s => (bandwidth s : ℝ) / period s) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => ((10 : ℝ) / 3) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hcomp := hpow.comp exponent_tendsto_atTop
  have hmul := hcomp.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  convert hmul using 1
  funext s
  simpa only [Function.comp_apply, bandwidth, period] using
    ScaleDependentDecimalOrbit.bandwidth_div_period_eq_geometric
      (exponent s) (exponent_pos s)

theorem period_tendsto_atTop :
    Tendsto (fun s => (period s : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa [period, ScaleDependentDecimalOrbit.period] using
    hpow.comp exponent_tendsto_atTop

theorem bandwidth_tendsto_atTop :
    Tendsto (fun s => (bandwidth s : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (10 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hcomp := hpow.comp exponent_tendsto_atTop
  have hmul := hcomp.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  convert hmul using 1
  funext s
  have htwo : 2 ∣ ScaleDependentDecimalOrbit.sampleSize (exponent s) := by
    unfold ScaleDependentDecimalOrbit.sampleSize
    exact dvd_pow (by norm_num) (exponent_pos s).ne'
  unfold bandwidth ScaleDependentDecimalOrbit.bandwidth
  rw [Nat.cast_div htwo (by norm_num : (2 : ℝ) ≠ 0)]
  unfold ScaleDependentDecimalOrbit.sampleSize
  push_cast
  simp only [Function.comp_apply]
  ring

theorem first_error_tendsto_zero :
    Tendsto (fun s =>
      2 * (exceptionBudget s : ℝ) / sampleSize s + phaseError s)
      atTop (𝓝 0) := by
  have hP : Tendsto (fun s : ℕ =>
      (2 : ℝ) * ((exceptionBudget s : ℝ) / sampleSize s)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      exceptionBudget_div_sampleSize_tendsto_zero : Tendsto (fun s : ℕ =>
        (2 : ℝ) * ((exceptionBudget s : ℝ) / sampleSize s)) atTop (𝓝 (2 * 0)))
  have hP' : Tendsto (fun s =>
      2 * (exceptionBudget s : ℝ) / sampleSize s) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using hP
  simpa using hP'.add phaseError_tendsto_zero

theorem density_error_tendsto_zero :
    Tendsto (fun s =>
      (period s : ℝ) / sampleSize s +
        2 * (exceptionBudget s : ℝ) / sampleSize s + phaseError s)
      atTop (𝓝 0) :=
  by
    simpa [add_assoc] using
      period_div_sampleSize_tendsto_zero.add first_error_tendsto_zero

/-! ## T31 instantiation and the two normalized limits -/

/-- T31's complete signed strict-band Fejer energy for the ordinary orbit of
the one fixed seed. -/
def energy (s : ℕ) : ℝ :=
  completeFejerEnergy (fixedOrbit s) (bandwidth s)

/-- The fields supplied to T31 are exposed as an ordinary proposition for
skeptic inspection, in addition to the `PhaseApproximation` structure itself. -/
theorem verifies_T31_finite_hypotheses (s : ℕ) :
    (exceptions s).card ≤ exceptionBudget s ∧
      0 ≤ phaseError s ∧
      (∀ h ∈ fejerFrequencies (bandwidth s), ∀ j,
        j ∉ exceptions s →
          ‖Theory.PiDigits.T27.phase h (fixedOrbit s j) -
            Theory.PiDigits.T27.phase h (periodicModel s j)‖ ≤ phaseError s) ∧
      PeriodicModelBounds (periodicModel s) (bandwidth s) (period s) := by
  exact ⟨(phaseApproximation s).card_exceptions,
    (phaseApproximation s).eps_nonneg,
    (phaseApproximation s).close_phase, periodicModelBounds s⟩

/-- Every sample, bandwidth, and period is positive, as required by both T31
limit theorems. -/
theorem parameters_eventually_positive :
    ∀ᶠ s in atTop, 0 < sampleSize s ∧ 0 < bandwidth s ∧ 0 < period s :=
  Filter.Eventually.of_forall fun s => by
    refine ⟨by simp [sampleSize, ScaleDependentDecimalOrbit.sampleSize],
      ScaleDependentDecimalOrbit.bandwidth_pos (exponent s) (exponent_pos s), ?_⟩
    simp [period, ScaleDependentDecimalOrbit.period]

/-- Along the recursive scales, complete Fejer energy divided by `M_s^2`
tends to positive infinity. -/
theorem energy_div_sampleSize_sq_tendsto_atTop :
    Tendsto (fun s => energy s / (sampleSize s : ℝ) ^ 2) atTop atTop := by
  unfold energy
  exact normalized_energy_tendsto_atTop
    sampleSize bandwidth period exceptionBudget phaseError
    fixedOrbit periodicModel parameters_eventually_positive
    phaseApproximation periodicModelBounds bandwidth_div_period_tendsto_atTop
    first_error_tendsto_zero

/-- Along the same scales and the same fixed orbit, complete Fejer energy
divided by `H_s*M_s^2` tends to zero. -/
theorem energy_div_bandwidth_sampleSize_sq_tendsto_zero :
    Tendsto (fun s =>
      energy s / ((bandwidth s : ℝ) * (sampleSize s : ℝ) ^ 2))
      atTop (𝓝 0) := by
  unfold energy
  exact normalized_energy_density_tendsto_zero
    sampleSize bandwidth period exceptionBudget phaseError
    fixedOrbit periodicModel parameters_eventually_positive
    phaseApproximation periodicModelBounds period_tendsto_atTop
    bandwidth_tendsto_atTop density_error_tendsto_zero

/-! ## Explicit fixed-real, pi, and C1 scope -/

/-- The represented fixed decimal real is not the circle constant. -/
theorem fixedSeed_ne_pi : fixedSeed ≠ Real.pi := by
  intro heq
  have hpi := Real.pi_gt_three
  rw [← heq] at hpi
  linarith [fixedSeed_le_one]

structure ScopeStatus where
  constructsOneFixedDecimalReal : Bool
  fixedRealIsPi : Bool
  specializesEnergyLimitsToPi : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  deriving DecidableEq, Repr

/-- Machine-readable scope: this file constructs one fixed decimal real, but
that real is not pi and neither direction of C1 is claimed. -/
def scopeStatus : ScopeStatus where
  constructsOneFixedDecimalReal := true
  fixedRealIsPi := false
  specializesEnergyLimitsToPi := false
  provesC1 := false
  disprovesC1 := false

theorem explicit_fixed_real_pi_C1_scope :
    fixedSeed = Real.ofDigits fixedDigitStream ∧
      fixedSeed ≠ Real.pi ∧
      scopeStatus.constructsOneFixedDecimalReal = true ∧
      scopeStatus.fixedRealIsPi = false ∧
      scopeStatus.specializesEnergyLimitsToPi = false ∧
      scopeStatus.provesC1 = false ∧ scopeStatus.disprovesC1 = false := by
  exact ⟨rfl, fixedSeed_ne_pi, by norm_num [scopeStatus],
    by norm_num [scopeStatus], by norm_num [scopeStatus],
    by norm_num [scopeStatus], by norm_num [scopeStatus]⟩

end DecimalFactorComplexity.FixedDecimalPeriodicBlocks

#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.recursive_parameters
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.periodicModelBounds
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.phaseApproximation
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.verifies_T31_finite_hypotheses
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.energy_div_sampleSize_sq_tendsto_atTop
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.energy_div_bandwidth_sampleSize_sq_tendsto_zero
#print axioms DecimalFactorComplexity.FixedDecimalPeriodicBlocks.explicit_fixed_real_pi_C1_scope
