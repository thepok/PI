import TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting
import TheoryLib.PiLacunaryNearReturnSparsity.T25FiniteMultilevelEnvelope
import TheoryLib.PiQuantitativeBlockHitting.T14T14BoundaryRobustFejerDichotomy
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# T64: one-row aggregate Fejer criterion

Canonical question: `problems/local/pi-lacunary-near-return-sparsity.txt`
SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

This module proves only a finite, conditional criterion for one literal row of
T14/T25. It does not prove the Fourier or boundary hypotheses for the fixed pi
orbit, and it makes no C2, C1, or canonical near-return claim.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset Set

namespace DecimalFactorComplexity.AggregateFejerCriterionT64

open DecimalFactorComplexity.FiniteCylinderEnergy
open DecimalFactorComplexity.ClusterNearReturns
open DecimalFactorComplexity.CylinderCollision
open DecimalFactorComplexity.CoherentSuccessorSplitting
open DecimalFactorComplexity.FiniteMultilevelEnvelope
open Theory.PiDigits.PositiveLowerBlockDensity.T8
open Theory.PiDigits.BoundaryRobustFejerDichotomy

abbrev phase := Theory.PiDigits.T27.phase

/-- Root-of-unity orthogonality on the literal grid `a = 0, ..., q-1`. -/
theorem phase_grid_sum (q : ℕ) (hq : 0 < q) (s : ℤ) :
    ∑ a : Fin q, phase s ((a : ℝ) / q) =
      if (q : ℤ) ∣ s then (q : ℂ) else 0 := by
  classical
  let z : ℂ := phase s ((1 : ℝ) / q)
  have hterm (a : ℕ) : phase s ((a : ℝ) / q) = z ^ a := by
    dsimp [z, phase]
    rw [Theory.PiDigits.T27.phase, Theory.PiDigits.T27.phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzpow : z ^ q = 1 := by
    dsimp [z, phase]
    rw [Theory.PiDigits.T27.phase, ← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff]
    refine ⟨s, ?_⟩
    rw [Complex.ofReal_div]
    push_cast
    field_simp [hq.ne']
  have hzone : z = 1 ↔ (q : ℤ) ∣ s := by
    dsimp [z, phase]
    rw [Theory.PiDigits.T27.phase]
    rw [Complex.ofReal_div]
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hq0c : (q : ℂ) ≠ 0 := by
        exact_mod_cast hq.ne'
      field_simp [hq0c] at hn
      have hint : s * 1 = (q : ℤ) * n := by
        exact_mod_cast congrArg Complex.re hn
      simpa using hint
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      push_cast
      field_simp [hq.ne']
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range]
  split_ifs with hs
  · rw [← hzone] at hs
    simp [hs]
  · have hz : z ≠ 1 := mt hzone.mp hs
    apply mul_right_cancel₀ (sub_ne_zero.mpr hz)
    rw [zero_mul, geom_sum_mul, hzpow, sub_self]

/-- The radial Fejer coefficient, including the limiting zero mode. -/
def fullFejerRadialCoefficient (q M : ℕ) (h : ℤ) : ℝ :=
  if h = 0 then 1 / (q : ℝ)
  else triangularCoefficient M h *
    (Real.sin (Real.pi * (h : ℝ) / q) / (Real.pi * (h : ℝ)))

/-- The full signed cylinder coefficient, including frequency zero. -/
def fullFejerCylinderCoefficient (q a M : ℕ) (h : ℤ) : ℂ :=
  (fullFejerRadialCoefficient q M h : ℂ) *
    phase (-h) (((a : ℝ) + 1 / 2) / q)

theorem fullFejerCylinderCoefficient_eq_fejerCylinderCoefficient
    {q a M : ℕ} {h : ℤ} (hzero : h ≠ 0) :
    fullFejerCylinderCoefficient q a M h =
      fejerCylinderCoefficient q a M h := by
  simp only [fullFejerCylinderCoefficient, fullFejerRadialCoefficient, hzero,
    if_false, fejerCylinderCoefficient]
  push_cast
  ring

theorem fullFejerCylinderCoefficient_zero {q a M : ℕ} :
    fullFejerCylinderCoefficient q a M 0 = (1 / (q : ℝ) : ℝ) := by
  simp [fullFejerCylinderCoefficient, fullFejerRadialCoefficient,
    Theory.PiDigits.T27.phase_zero]

theorem norm_fullFejerCylinderCoefficient (q a M : ℕ) (h : ℤ) :
    ‖fullFejerCylinderCoefficient q a M h‖ =
      |fullFejerRadialCoefficient q M h| := by
  rw [fullFejerCylinderCoefficient, norm_mul,
    Theory.PiDigits.T27.norm_phase, mul_one]
  simp

/-- Full Fejer amplitude on the exact signed cutoff `|h| ≤ M`. -/
def fullFejerAmplitude (q a M : ℕ) (z : ℤ → ℂ) : ℂ :=
  ∑ h ∈ signedFrequenciesZero M,
    fullFejerCylinderCoefficient q a M h * z h

theorem fullFejerAmplitude_eq_existing
    (q a M : ℕ) (z : ℤ → ℂ) :
    fullFejerAmplitude q a M z =
      ((1 / (q : ℝ) : ℝ) : ℂ) * z 0 +
        ∑ h ∈ signedFrequencies M,
          fejerCylinderCoefficient q a M h * z h := by
  classical
  have hset : signedFrequenciesZero M = insert 0 (signedFrequencies M) := by
    ext h
    rw [mem_signedFrequenciesZero]
    simp only [Finset.mem_insert, mem_signedFrequencies]
    by_cases hzero : h = 0
    · subst h
      simp
    · simp [hzero]
  unfold fullFejerAmplitude
  rw [hset, Finset.sum_insert]
  · rw [fullFejerCylinderCoefficient_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    rw [fullFejerCylinderCoefficient_eq_fejerCylinderCoefficient
      (mem_signedFrequencies.mp hh).1]
  · simp [mem_signedFrequencies]

/-- Coefficient of `z h * z k` after summing all parent labels. -/
def collectedFejerCoefficient (q M : ℕ) (h k : ℤ) : ℂ :=
  ∑ a : Fin q,
    fullFejerCylinderCoefficient q a M h *
      fullFejerCylinderCoefficient q a M k

/-- Root-of-unity collection, including every alias `q ∣ h+k`. -/
theorem collectedFejerCoefficient_eq
    (q M : ℕ) (h k : ℤ) (hq : 0 < q) :
    collectedFejerCoefficient q M h k =
      if (q : ℤ) ∣ h + k then
        (q : ℂ) *
          (fullFejerRadialCoefficient q M h : ℂ) *
          (fullFejerRadialCoefficient q M k : ℂ) *
          phase (-(h + k)) (1 / (2 * (q : ℝ)))
      else 0 := by
  classical
  have hcenter (a : Fin q) :
      (((a : ℕ) : ℝ) + 1 / 2) / q =
        1 / (2 * (q : ℝ)) + (a : ℝ) / q := by
    field_simp [hq.ne']
    ring
  have hterm (a : Fin q) :
      fullFejerCylinderCoefficient q a M h *
          fullFejerCylinderCoefficient q a M k =
        ((fullFejerRadialCoefficient q M h : ℂ) *
          (fullFejerRadialCoefficient q M k : ℂ) *
          phase (-(h + k)) (1 / (2 * (q : ℝ)))) *
          phase (-(h + k)) ((a : ℝ) / q) := by
    have hphase (x : ℝ) :
        phase (-h) x * phase (-k) x = phase (-(h + k)) x := by
      rw [← Theory.PiDigits.T27.phase_add]
      congr 1
      ring
    have hsplit :
        phase (-(h + k)) (1 / (2 * (q : ℝ)) + (a : ℝ) / q) =
          phase (-(h + k)) (1 / (2 * (q : ℝ))) *
            phase (-(h + k)) ((a : ℝ) / q) :=
      Theory.PiDigits.T27.phase_add_real _ _ _
    rw [fullFejerCylinderCoefficient, fullFejerCylinderCoefficient, hcenter]
    rw [show
      (fullFejerRadialCoefficient q M h : ℂ) *
          phase (-h) (1 / (2 * (q : ℝ)) + (a : ℝ) / q) *
          ((fullFejerRadialCoefficient q M k : ℂ) *
            phase (-k) (1 / (2 * (q : ℝ)) + (a : ℝ) / q)) =
        (fullFejerRadialCoefficient q M h : ℂ) *
          (fullFejerRadialCoefficient q M k : ℂ) *
          (phase (-h) (1 / (2 * (q : ℝ)) + (a : ℝ) / q) *
            phase (-k) (1 / (2 * (q : ℝ)) + (a : ℝ) / q)) by ring,
      hphase, hsplit]
    ring
  unfold collectedFejerCoefficient
  simp_rw [hterm]
  rw [← Finset.mul_sum, phase_grid_sum q hq]
  have hdiv : (q : ℤ) ∣ -(h + k) ↔ (q : ℤ) ∣ h + k := by
    rw [dvd_neg]
  rw [if_congr hdiv rfl rfl]
  split_ifs <;> ring

/-- Exact collected coefficient norm with its literal divisibility selector. -/
theorem norm_collectedFejerCoefficient
    (q M : ℕ) (h k : ℤ) (hq : 0 < q) :
    ‖collectedFejerCoefficient q M h k‖ =
      if (q : ℤ) ∣ h + k then
        (q : ℝ) * |fullFejerRadialCoefficient q M h| *
          |fullFejerRadialCoefficient q M k|
      else 0 := by
  rw [collectedFejerCoefficient_eq q M h k hq]
  split_ifs
  · rw [norm_mul, norm_mul, norm_mul, Theory.PiDigits.T27.norm_phase]
    simp only [Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      mul_one]
  · simp

/-- Expanding all finite amplitudes and collecting equal frequency pairs. -/
theorem sum_fullFejerAmplitude_sq_eq_collected
    (q M : ℕ) (z : ℤ → ℂ) :
    (∑ a : Fin q, (fullFejerAmplitude q a M z) ^ 2) =
      ∑ h ∈ signedFrequenciesZero M,
        ∑ k ∈ signedFrequenciesZero M,
          collectedFejerCoefficient q M h k * (z h * z k) := by
  classical
  unfold fullFejerAmplitude collectedFejerCoefficient
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Frequencies grouped by the natural shell `|h| / q`. -/
def frequencyShell (q H n : ℕ) : Finset ℤ :=
  (signedFrequenciesZero H).filter fun h => h.natAbs / q = n

def frequencyFiberShell (q H n : ℕ) (h : ℤ) : Finset ℤ :=
  (frequencyShell q H n).filter fun k => (q : ℤ) ∣ h + k

theorem frequencyShell_card_le (q H n : ℕ) (hq : 0 < q) :
    (frequencyShell q H n).card ≤ 2 * q := by
  classical
  let f : ℤ → Bool × Fin q := fun h =>
    (decide (0 ≤ h), ⟨h.natAbs % q, Nat.mod_lt _ hq⟩)
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) ?_).trans ?_
  · intro a ha b hb hab
    have haShell := (Finset.mem_filter.mp ha).2
    have hbShell := (Finset.mem_filter.mp hb).2
    have hsign : decide (0 ≤ a) = decide (0 ≤ b) := congrArg Prod.fst hab
    have hmod : a.natAbs % q = b.natAbs % q := by
      exact congrArg (fun x => (x.2 : ℕ)) hab
    have habs : a.natAbs = b.natAbs := by
      calc
        a.natAbs = a.natAbs % q + q * (a.natAbs / q) :=
          (Nat.mod_add_div _ _).symm
        _ = b.natAbs % q + q * (b.natAbs / q) := by
          rw [hmod, haShell, hbShell]
        _ = b.natAbs := Nat.mod_add_div _ _
    by_cases ha0 : 0 ≤ a
    · have hb0 : 0 ≤ b := by simpa [ha0] using hsign
      exact (Int.natAbs_inj_of_nonneg_of_nonneg ha0 hb0).mp habs
    · have ha0' : a ≤ 0 := le_of_not_ge ha0
      have hb0 : ¬0 ≤ b := by simpa [ha0] using hsign
      exact (Int.natAbs_inj_of_nonpos_of_nonpos ha0'
        (le_of_not_ge hb0)).mp habs
  · simp

theorem frequencyFiberShell_card_le_two
    (q H n : ℕ) (h : ℤ) (hq : 0 < q) :
    (frequencyFiberShell q H n h).card ≤ 2 := by
  classical
  let f : ℤ → Bool := fun k => decide (0 ≤ k)
  refine (Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) ?_).trans ?_
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haShell := (Finset.mem_filter.mp ha'.1).2
    have hbShell := (Finset.mem_filter.mp hb'.1).2
    have hsign : decide (0 ≤ a) = decide (0 ≤ b) := hab
    have hdvd : (q : ℤ) ∣ a - b := by
      simpa only [add_sub_add_left_eq_sub] using dvd_sub ha'.2 hb'.2
    have aux (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y)
        (hxs : x.natAbs / q = n) (hys : y.natAbs / q = n) :
        (x - y).natAbs < q := by
      by_cases hxy : x ≤ y
      · have hnonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
        have hcast : ((x - y).natAbs : ℤ) = y - x := by
          rw [← Int.natAbs_neg, neg_sub, Int.natAbs_of_nonneg hnonneg]
        have hxcast := Int.natAbs_of_nonneg hx
        have hycast := Int.natAbs_of_nonneg hy
        have habsOrder : x.natAbs ≤ y.natAbs := by
          apply Int.ofNat_le.mp
          rw [hxcast, hycast]
          exact hxy
        have hdiff : (x - y).natAbs = y.natAbs - x.natAbs := by
          apply Nat.cast_injective (R := ℤ)
          rw [Nat.cast_sub habsOrder, hcast, hxcast, hycast]
        rw [hdiff]
        calc
          y.natAbs - x.natAbs ≤ y.natAbs % q := by
            have hxRec := Nat.mod_add_div x.natAbs q
            have hyRec := Nat.mod_add_div y.natAbs q
            have hxEq : x.natAbs = x.natAbs % q + q * n := by
              rw [← hxs]
              exact hxRec.symm
            have hyEq : y.natAbs = y.natAbs % q + q * n := by
              rw [← hys]
              exact hyRec.symm
            calc
              y.natAbs - x.natAbs =
                  (y.natAbs % q + q * n) - (x.natAbs % q + q * n) := by
                    exact congrArg₂ (· - ·) hyEq hxEq
              _ = y.natAbs % q - x.natAbs % q := by omega
              _ ≤ y.natAbs % q := Nat.sub_le _ _
          _ < q := Nat.mod_lt _ hq
      · have hnonneg : 0 ≤ x - y := sub_nonneg.mpr (le_of_not_ge hxy)
        have hcast : ((x - y).natAbs : ℤ) = x - y :=
          Int.natAbs_of_nonneg hnonneg
        have hxcast := Int.natAbs_of_nonneg hx
        have hycast := Int.natAbs_of_nonneg hy
        have habsOrder : y.natAbs ≤ x.natAbs := by
          apply Int.ofNat_le.mp
          rw [hycast, hxcast]
          exact le_of_not_ge hxy
        have hdiff : (x - y).natAbs = x.natAbs - y.natAbs := by
          apply Nat.cast_injective (R := ℤ)
          rw [Nat.cast_sub habsOrder, hcast, hxcast, hycast]
        rw [hdiff]
        calc
          x.natAbs - y.natAbs ≤ x.natAbs % q := by
            have hxRec := Nat.mod_add_div x.natAbs q
            have hyRec := Nat.mod_add_div y.natAbs q
            have hxEq : x.natAbs = x.natAbs % q + q * n := by
              rw [← hxs]
              exact hxRec.symm
            have hyEq : y.natAbs = y.natAbs % q + q * n := by
              rw [← hys]
              exact hyRec.symm
            calc
              x.natAbs - y.natAbs =
                  (x.natAbs % q + q * n) - (y.natAbs % q + q * n) := by
                    exact congrArg₂ (· - ·) hxEq hyEq
              _ = x.natAbs % q - y.natAbs % q := by omega
              _ ≤ x.natAbs % q := Nat.sub_le _ _
          _ < q := Nat.mod_lt _ hq
    by_cases ha0 : 0 ≤ a
    · have hb0 : 0 ≤ b := by simpa [ha0] using hsign
      have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
        (by simpa using aux a b ha0 hb0 haShell hbShell)
      omega
    · have ha0' : a ≤ 0 := le_of_not_ge ha0
      have hb0n : ¬0 ≤ b := by simpa [ha0] using hsign
      have hb0 : b ≤ 0 := le_of_not_ge hb0n
      have hdvdNeg : (q : ℤ) ∣ (-a) - (-b) := by
        simpa [sub_eq_add_neg, add_comm] using dvd_neg.mpr hdvd
      have hna : 0 ≤ -a := neg_nonneg.mpr ha0'
      have hnb : 0 ≤ -b := neg_nonneg.mpr hb0
      have hshellNegA : (-a).natAbs / q = n := by simpa using haShell
      have hshellNegB : (-b).natAbs / q = n := by simpa using hbShell
      have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvdNeg
        (by simpa using aux (-a) (-b) hna hnb hshellNegA hshellNegB)
      omega
  · decide

def shellWeight (q n : ℕ) : ℝ :=
  1 / ((q : ℝ) * max 1 n)

theorem abs_fullFejerRadialCoefficient_le_inv
    {q M : ℕ} {h : ℤ} (hq : 0 < q) (hh : h.natAbs ≤ M) :
    |fullFejerRadialCoefficient q M h| ≤ 1 / (q : ℝ) := by
  by_cases hzero : h = 0
  · subst h
    simp [fullFejerRadialCoefficient]
  · have htri0 : 0 ≤ triangularCoefficient M h :=
      triangularCoefficient_nonneg hh
    have htri1 : triangularCoefficient M h ≤ 1 := by
      unfold triangularCoefficient
      have : 0 ≤ (h.natAbs : ℝ) / (M + 1 : ℝ) := by positivity
      linarith
    have hhcast : (h : ℝ) ≠ 0 := by exact_mod_cast hzero
    have hden : 0 < |Real.pi * (h : ℝ)| :=
      abs_pos.mpr (mul_ne_zero Real.pi_ne_zero hhcast)
    have hsinc :
        |Real.sin (Real.pi * (h : ℝ) / q) /
            (Real.pi * (h : ℝ))| ≤ 1 / (q : ℝ) := by
      rw [abs_div]
      calc
        |Real.sin (Real.pi * (h : ℝ) / q)| /
              |Real.pi * (h : ℝ)| ≤
            |Real.pi * (h : ℝ) / q| /
              |Real.pi * (h : ℝ)| := by
          exact div_le_div_of_nonneg_right Real.abs_sin_le_abs (abs_nonneg _)
        _ = 1 / (q : ℝ) := by
          rw [abs_div, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]
          field_simp [ne_of_gt hden]
    rw [fullFejerRadialCoefficient, if_neg hzero, abs_mul,
      abs_of_nonneg htri0]
    calc
      triangularCoefficient M h *
          |Real.sin (Real.pi * (h : ℝ) / q) /
            (Real.pi * (h : ℝ))| ≤ 1 * (1 / (q : ℝ)) := by gcongr
      _ = 1 / (q : ℝ) := one_mul _

theorem abs_fullFejerRadialCoefficient_le_natAbs_inv
    {q H : ℕ} {h : ℤ} (hh : h.natAbs ≤ H) (h0 : h ≠ 0) :
    |fullFejerRadialCoefficient q H h| ≤ 1 / (h.natAbs : ℝ) := by
  have htri0 : 0 ≤ triangularCoefficient H h := triangularCoefficient_nonneg hh
  have htri1 : triangularCoefficient H h ≤ 1 := by
    unfold triangularCoefficient
    have : 0 ≤ (h.natAbs : ℝ) / (H + 1 : ℝ) := by positivity
    linarith
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast h0
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.one_le_pi_div_two]
  have habsh : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
  rw [fullFejerRadialCoefficient, if_neg h0, abs_mul, abs_of_nonneg htri0]
  calc
    triangularCoefficient H h *
        |Real.sin (Real.pi * (h : ℝ) / q) / (Real.pi * (h : ℝ))| ≤
        1 * (1 / |Real.pi * (h : ℝ)|) := by
      gcongr
      rw [abs_div]
      have hden : 0 < |Real.pi * (h : ℝ)| :=
        abs_pos.mpr (mul_ne_zero Real.pi_ne_zero hhR)
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _)
        (le_of_lt hden)
    _ ≤ 1 / (h.natAbs : ℝ) := by
      rw [one_mul, abs_mul, abs_of_pos Real.pi_pos, habsh]
      apply one_div_le_one_div_of_le
      · exact_mod_cast Int.natAbs_pos.mpr h0
      · nlinarith [abs_nonneg (h : ℝ)]

theorem abs_fullFejerRadialCoefficient_le_shellWeight
    {q H n : ℕ} {h : ℤ} (hq : 0 < q)
    (hh : h ∈ frequencyShell q H n) :
    |fullFejerRadialCoefficient q H h| ≤ shellWeight q n := by
  have hh' := Finset.mem_filter.mp hh
  have hhH := mem_signedFrequenciesZero.mp hh'.1
  by_cases hn : n = 0
  · subst n
    simpa [shellWeight] using abs_fullFejerRadialCoefficient_le_inv hq hhH
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have habspos : 0 < h.natAbs := by
      have hmul : q * n ≤ h.natAbs := by
        simpa [hh'.2] using Nat.mul_div_le h.natAbs q
      have : 0 < q * n := Nat.mul_pos hq hnpos
      omega
    have h0 : h ≠ 0 := Int.natAbs_ne_zero.mp (Nat.ne_of_gt habspos)
    calc
      |fullFejerRadialCoefficient q H h| ≤ 1 / (h.natAbs : ℝ) :=
        abs_fullFejerRadialCoefficient_le_natAbs_inv hhH h0
      _ ≤ 1 / ((q : ℝ) * n) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact_mod_cast (show q * n ≤ h.natAbs by
            simpa [hh'.2] using Nat.mul_div_le h.natAbs q)
      _ = shellWeight q n := by
        rw [shellWeight, max_eq_right hnpos]

theorem shellIndex_mem_range
    {q H : ℕ} {h : ℤ} (hh : h ∈ signedFrequenciesZero H) :
    h.natAbs / q ∈ Finset.range (H / q + 1) := by
  rw [Finset.mem_range]
  have hh' := mem_signedFrequenciesZero.mp hh
  have hdiv : h.natAbs / q ≤ H / q := Nat.div_le_div_right hh'
  omega

theorem sum_inv_max_one_le_two_harmonic (L : ℕ) :
    (∑ n ∈ Finset.range L, 1 / ((max 1 n : ℕ) : ℝ)) ≤
      2 * (harmonic L : ℝ) := by
  calc
    (∑ n ∈ Finset.range L, 1 / ((max 1 n : ℕ) : ℝ)) ≤
        ∑ n ∈ Finset.range L, 2 / (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hn1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        rw [max_eq_right hn1]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
        have hle : (n + 1 : ℝ) ≤ 2 * n := by linarith
        rw [div_le_div_iff₀ hnpos (by positivity)]
        linarith
    _ = 2 * (harmonic L : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem sum_inv_max_one_le_log (L : ℕ) :
    (∑ n ∈ Finset.range L, 1 / ((max 1 n : ℕ) : ℝ)) ≤
      2 * (1 + Real.log L) :=
  (sum_inv_max_one_le_two_harmonic L).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by norm_num))

def radialL1Sum (q H : ℕ) : ℝ :=
  ∑ h ∈ signedFrequenciesZero H, |fullFejerRadialCoefficient q H h|

def radialFiberL1Sum (q H : ℕ) (h : ℤ) : ℝ :=
  ∑ k ∈ (signedFrequenciesZero H).filter (fun k => (q : ℤ) ∣ h + k),
    |fullFejerRadialCoefficient q H k|

theorem radialL1Sum_le
    (q H : ℕ) (hq : 0 < q) :
    radialL1Sum q H ≤ 4 * (1 + Real.log ((H / q + 1 : ℕ) : ℝ)) := by
  let L := H / q + 1
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := signedFrequenciesZero H) (t := Finset.range L)
    (g := fun h : ℤ => h.natAbs / q)
    (fun h hh => shellIndex_mem_range hh)
    (fun h => |fullFejerRadialCoefficient q H h|)
  unfold radialL1Sum
  rw [← hpartition]
  calc
    (∑ n ∈ Finset.range L,
        ∑ h ∈ signedFrequenciesZero H with h.natAbs / q = n,
          |fullFejerRadialCoefficient q H h|) ≤
        ∑ n ∈ Finset.range L, (2 * q : ℕ) * shellWeight q n := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        (∑ h ∈ signedFrequenciesZero H with h.natAbs / q = n,
            |fullFejerRadialCoefficient q H h|) ≤
            ((frequencyShell q H n).card : ℝ) * shellWeight q n := by
          simpa [frequencyShell, nsmul_eq_mul] using
            Finset.sum_le_card_nsmul (frequencyShell q H n)
              (fun h => |fullFejerRadialCoefficient q H h|)
              (shellWeight q n)
              (fun h hh => abs_fullFejerRadialCoefficient_le_shellWeight hq hh)
        _ ≤ (2 * q : ℕ) * shellWeight q n := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast frequencyShell_card_le q H n hq
          · unfold shellWeight
            positivity
    _ = 2 * ∑ n ∈ Finset.range L, 1 / ((max 1 n : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [shellWeight]
      push_cast
      field_simp [hq.ne']
    _ ≤ 2 * (2 * (1 + Real.log L)) := by
      gcongr
      exact sum_inv_max_one_le_log L
    _ = 4 * (1 + Real.log ((H / q + 1 : ℕ) : ℝ)) := by
      dsimp [L]
      ring

theorem radialFiberL1Sum_le
    (q H : ℕ) (h : ℤ) (hq : 0 < q) :
    radialFiberL1Sum q H h ≤
      (4 / (q : ℝ)) * (1 + Real.log ((H / q + 1 : ℕ) : ℝ)) := by
  let L := H / q + 1
  let S := (signedFrequenciesZero H).filter fun k => (q : ℤ) ∣ h + k
  have hmaps : ∀ k ∈ S, k.natAbs / q ∈ Finset.range L := by
    intro k hk
    exact shellIndex_mem_range (Finset.mem_filter.mp hk).1
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.range L) (g := fun k : ℤ => k.natAbs / q)
    hmaps (fun k => |fullFejerRadialCoefficient q H k|)
  unfold radialFiberL1Sum
  change (∑ k ∈ S, |fullFejerRadialCoefficient q H k|) ≤ _
  rw [← hpartition]
  calc
    (∑ n ∈ Finset.range L, ∑ k ∈ S with k.natAbs / q = n,
        |fullFejerRadialCoefficient q H k|) ≤
        ∑ n ∈ Finset.range L, 2 * shellWeight q n := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        (∑ k ∈ S with k.natAbs / q = n,
            |fullFejerRadialCoefficient q H k|) ≤
            ((frequencyFiberShell q H n h).card : ℝ) * shellWeight q n := by
          have hset : S.filter (fun k => k.natAbs / q = n) =
              frequencyFiberShell q H n h := by
            ext k
            simp [S, frequencyFiberShell, frequencyShell, and_left_comm,
              and_assoc]
            tauto
          rw [hset]
          simpa [nsmul_eq_mul] using
            Finset.sum_le_card_nsmul (frequencyFiberShell q H n h)
              (fun k => |fullFejerRadialCoefficient q H k|)
              (shellWeight q n)
              (fun k hk => abs_fullFejerRadialCoefficient_le_shellWeight hq
                (Finset.mem_filter.mp hk).1)
        _ ≤ 2 * shellWeight q n := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast frequencyFiberShell_card_le_two q H n h hq
          · unfold shellWeight
            positivity
    _ = (2 / (q : ℝ)) *
        ∑ n ∈ Finset.range L, 1 / ((max 1 n : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [shellWeight]
      push_cast
      field_simp [hq.ne']
    _ ≤ (2 / (q : ℝ)) * (2 * (1 + Real.log L)) := by
      gcongr
      exact sum_inv_max_one_le_log L
    _ = (4 / (q : ℝ)) *
        (1 + Real.log ((H / q + 1 : ℕ) : ℝ)) := by
      dsimp [L]
      ring

/-- Collected `L1` norm with the zero pair deleted. -/
def nonzeroCollectedFejerL1Norm (q H : ℕ) : ℝ :=
  ∑ h ∈ signedFrequenciesZero H,
    ∑ k ∈ signedFrequenciesZero H,
      if h = 0 ∧ k = 0 then 0 else ‖collectedFejerCoefficient q H h k‖

/-- Exact aggregate `L1` identity after numerical frequencies are collected;
the selector retains every multiple alias of `q`. -/
theorem nonzeroCollectedFejerL1Norm_eq_divisibility_sum
    (q H : ℕ) (hq : 0 < q) :
    nonzeroCollectedFejerL1Norm q H =
      ∑ h ∈ signedFrequenciesZero H,
        ∑ k ∈ signedFrequenciesZero H,
          if h = 0 ∧ k = 0 then 0
          else if (q : ℤ) ∣ h + k then
            (q : ℝ) * |fullFejerRadialCoefficient q H h| *
              |fullFejerRadialCoefficient q H k|
          else 0 := by
  unfold nonzeroCollectedFejerL1Norm
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : h = 0 ∧ k = 0
  · simp [hz]
  · simp only [hz, if_false]
    exact norm_collectedFejerCoefficient q H h k hq

/-- The root-of-unity collection has logarithmic, not exponential, `L1` loss. -/
theorem nonzeroCollectedFejerL1Norm_le
    (q H : ℕ) (hq : 0 < q) :
    nonzeroCollectedFejerL1Norm q H ≤
      16 * (2 + Real.log ((H / q + 1 : ℕ) : ℝ)) ^ 2 := by
  let L : ℕ := H / q + 1
  let A : ℝ := 1 + Real.log (L : ℝ)
  have hL : 1 ≤ L := by simp [L]
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hinner (h : ℤ) (hh : h ∈ signedFrequenciesZero H) :
      (∑ k ∈ signedFrequenciesZero H, ‖collectedFejerCoefficient q H h k‖) =
        (q : ℝ) * |fullFejerRadialCoefficient q H h| *
          radialFiberL1Sum q H h := by
    rw [radialFiberL1Sum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    rw [norm_collectedFejerCoefficient q H h k hq]
  calc
    nonzeroCollectedFejerL1Norm q H ≤
        ∑ h ∈ signedFrequenciesZero H,
          ∑ k ∈ signedFrequenciesZero H,
            ‖collectedFejerCoefficient q H h k‖ := by
      unfold nonzeroCollectedFejerL1Norm
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> simp only [norm_nonneg, le_rfl]
    _ = ∑ h ∈ signedFrequenciesZero H,
        (q : ℝ) * |fullFejerRadialCoefficient q H h| *
          radialFiberL1Sum q H h := by
      apply Finset.sum_congr rfl
      exact hinner
    _ ≤ ∑ h ∈ signedFrequenciesZero H,
        (q : ℝ) * |fullFejerRadialCoefficient q H h| *
          ((4 / (q : ℝ)) * A) := by
      apply Finset.sum_le_sum
      intro h hh
      gcongr
      simpa [A, L] using radialFiberL1Sum_le q H h hq
    _ = ((q : ℝ) * ((4 / (q : ℝ)) * A)) * radialL1Sum q H := by
      unfold radialL1Sum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ ((q : ℝ) * ((4 / (q : ℝ)) * A)) * (4 * A) := by
      gcongr
      simpa [A, L] using radialL1Sum_le q H hq
    _ = 16 * A ^ 2 := by
      field_simp [hq.ne']
      ring
    _ ≤ 16 * (2 + Real.log (L : ℝ)) ^ 2 := by
      nlinarith
    _ = 16 * (2 + Real.log ((H / q + 1 : ℕ) : ℝ)) ^ 2 := by
      rfl

theorem sum_sq_inv_max_one_le_three (L : ℕ) :
    (∑ n ∈ Finset.range L, (1 / ((max 1 n : ℕ) : ℝ)) ^ 2) ≤ 3 := by
  by_cases hL : L = 0
  · subst L
    simp
  have hset : Finset.range L = insert 0 (Finset.Ioo 0 L) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    omega
  rw [hset, Finset.sum_insert]
  · calc
      (1 / ((max 1 0 : ℕ) : ℝ)) ^ 2 +
          ∑ n ∈ Finset.Ioo 0 L, (1 / ((max 1 n : ℕ) : ℝ)) ^ 2 =
          1 + ∑ n ∈ Finset.Ioo 0 L, ((n : ℝ) ^ 2)⁻¹ := by
        congr 1
        · norm_num
        · apply Finset.sum_congr rfl
          intro n hn
          have hn1 : (1 : ℕ) ≤ n := by
            simp only [Finset.mem_Ioo] at hn
            omega
          rw [max_eq_right hn1]
          ring
      _ ≤ 1 + 2 := by
        gcongr
        simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 L)
      _ = 3 := by norm_num
  · simp

def radialL2SqSum (q H : ℕ) : ℝ :=
  ∑ h ∈ signedFrequenciesZero H, |fullFejerRadialCoefficient q H h| ^ 2

def radialFiberL2SqSum (q H : ℕ) (h : ℤ) : ℝ :=
  ∑ k ∈ (signedFrequenciesZero H).filter (fun k => (q : ℤ) ∣ h + k),
    |fullFejerRadialCoefficient q H k| ^ 2

theorem radialL2SqSum_le
    (q H : ℕ) (hq : 0 < q) :
    radialL2SqSum q H ≤ 6 / (q : ℝ) := by
  let L := H / q + 1
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := signedFrequenciesZero H) (t := Finset.range L)
    (g := fun h : ℤ => h.natAbs / q)
    (fun h hh => shellIndex_mem_range hh)
    (fun h => |fullFejerRadialCoefficient q H h| ^ 2)
  unfold radialL2SqSum
  rw [← hpartition]
  calc
    (∑ n ∈ Finset.range L,
        ∑ h ∈ signedFrequenciesZero H with h.natAbs / q = n,
          |fullFejerRadialCoefficient q H h| ^ 2) ≤
        ∑ n ∈ Finset.range L, (2 * q : ℕ) * (shellWeight q n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        (∑ h ∈ signedFrequenciesZero H with h.natAbs / q = n,
            |fullFejerRadialCoefficient q H h| ^ 2) ≤
            ((frequencyShell q H n).card : ℝ) * (shellWeight q n) ^ 2 := by
          change (∑ h ∈ frequencyShell q H n,
            |fullFejerRadialCoefficient q H h| ^ 2) ≤ _
          simpa only [nsmul_eq_mul] using
            Finset.sum_le_card_nsmul (frequencyShell q H n)
              (fun h => |fullFejerRadialCoefficient q H h| ^ 2)
              ((shellWeight q n) ^ 2)
              (fun h hh => by
                exact (sq_le_sq₀ (abs_nonneg _)
                  (by unfold shellWeight; positivity)).2
                    (abs_fullFejerRadialCoefficient_le_shellWeight hq hh))
        _ ≤ (2 * q : ℕ) * (shellWeight q n) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast frequencyShell_card_le q H n hq
          · positivity
    _ = (2 / (q : ℝ)) *
        ∑ n ∈ Finset.range L, (1 / ((max 1 n : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [shellWeight]
      push_cast
      field_simp [hq.ne']
    _ ≤ (2 / (q : ℝ)) * 3 := by
      gcongr
      exact sum_sq_inv_max_one_le_three L
    _ = 6 / (q : ℝ) := by ring

theorem radialFiberL2SqSum_le
    (q H : ℕ) (h : ℤ) (hq : 0 < q) :
    radialFiberL2SqSum q H h ≤ 6 / (q : ℝ) ^ 2 := by
  let L := H / q + 1
  let S := (signedFrequenciesZero H).filter fun k => (q : ℤ) ∣ h + k
  have hmaps : ∀ k ∈ S, k.natAbs / q ∈ Finset.range L := by
    intro k hk
    exact shellIndex_mem_range (Finset.mem_filter.mp hk).1
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.range L) (g := fun k : ℤ => k.natAbs / q)
    hmaps (fun k => |fullFejerRadialCoefficient q H k| ^ 2)
  unfold radialFiberL2SqSum
  change (∑ k ∈ S, |fullFejerRadialCoefficient q H k| ^ 2) ≤ _
  rw [← hpartition]
  calc
    (∑ n ∈ Finset.range L, ∑ k ∈ S with k.natAbs / q = n,
        |fullFejerRadialCoefficient q H k| ^ 2) ≤
        ∑ n ∈ Finset.range L, 2 * (shellWeight q n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hset : S.filter (fun k => k.natAbs / q = n) =
          frequencyFiberShell q H n h := by
        ext k
        simp [S, frequencyFiberShell, frequencyShell, and_left_comm, and_assoc]
        tauto
      rw [hset]
      calc
        (∑ k ∈ frequencyFiberShell q H n h,
            |fullFejerRadialCoefficient q H k| ^ 2) ≤
            ((frequencyFiberShell q H n h).card : ℝ) *
              (shellWeight q n) ^ 2 := by
          simpa only [nsmul_eq_mul] using
            Finset.sum_le_card_nsmul (frequencyFiberShell q H n h)
              (fun k => |fullFejerRadialCoefficient q H k| ^ 2)
              ((shellWeight q n) ^ 2)
              (fun k hk => by
                exact (sq_le_sq₀ (abs_nonneg _)
                  (by unfold shellWeight; positivity)).2
                    (abs_fullFejerRadialCoefficient_le_shellWeight hq
                      (Finset.mem_filter.mp hk).1))
        _ ≤ 2 * (shellWeight q n) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast frequencyFiberShell_card_le_two q H n h hq
          · positivity
    _ = (2 / (q : ℝ) ^ 2) *
        ∑ n ∈ Finset.range L, (1 / ((max 1 n : ℕ) : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [shellWeight]
      push_cast
      field_simp [hq.ne']
    _ ≤ (2 / (q : ℝ) ^ 2) * 3 := by
      gcongr
      exact sum_sq_inv_max_one_le_three L
    _ = 6 / (q : ℝ) ^ 2 := by ring

/-- Squared collected `L2` norm with the zero pair deleted. -/
def nonzeroCollectedFejerL2SqNorm (q H : ℕ) : ℝ :=
  ∑ h ∈ signedFrequenciesZero H,
    ∑ k ∈ signedFrequenciesZero H,
      if h = 0 ∧ k = 0 then 0
      else ‖collectedFejerCoefficient q H h k‖ ^ 2

def nonzeroCollectedFejerL2Norm (q H : ℕ) : ℝ :=
  Real.sqrt (nonzeroCollectedFejerL2SqNorm q H)

/-- Exact aggregate squared `L2` identity on the same signed cutoff. -/
theorem nonzeroCollectedFejerL2SqNorm_eq_divisibility_sum
    (q H : ℕ) (hq : 0 < q) :
    nonzeroCollectedFejerL2SqNorm q H =
      ∑ h ∈ signedFrequenciesZero H,
        ∑ k ∈ signedFrequenciesZero H,
          if h = 0 ∧ k = 0 then 0
          else if (q : ℤ) ∣ h + k then
            ((q : ℝ) * |fullFejerRadialCoefficient q H h| *
              |fullFejerRadialCoefficient q H k|) ^ 2
          else 0 := by
  unfold nonzeroCollectedFejerL2SqNorm
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : h = 0 ∧ k = 0
  · simp [hz]
  · simp only [hz, if_false]
    rw [norm_collectedFejerCoefficient q H h k hq]
    split_ifs <;> simp

theorem nonzeroCollectedFejerL2SqNorm_le
    (q H : ℕ) (hq : 0 < q) :
    nonzeroCollectedFejerL2SqNorm q H ≤ 36 / (q : ℝ) := by
  have hinner (h : ℤ) (hh : h ∈ signedFrequenciesZero H) :
      (∑ k ∈ signedFrequenciesZero H,
          ‖collectedFejerCoefficient q H h k‖ ^ 2) =
        (q : ℝ) ^ 2 * |fullFejerRadialCoefficient q H h| ^ 2 *
          radialFiberL2SqSum q H h := by
    rw [radialFiberL2SqSum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    rw [norm_collectedFejerCoefficient q H h k hq]
    split_ifs <;> ring
  calc
    nonzeroCollectedFejerL2SqNorm q H ≤
        ∑ h ∈ signedFrequenciesZero H,
          ∑ k ∈ signedFrequenciesZero H,
            ‖collectedFejerCoefficient q H h k‖ ^ 2 := by
      unfold nonzeroCollectedFejerL2SqNorm
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> simp only [sq_nonneg, le_rfl]
    _ = ∑ h ∈ signedFrequenciesZero H,
        (q : ℝ) ^ 2 * |fullFejerRadialCoefficient q H h| ^ 2 *
          radialFiberL2SqSum q H h := by
      apply Finset.sum_congr rfl
      exact hinner
    _ ≤ ∑ h ∈ signedFrequenciesZero H,
        (q : ℝ) ^ 2 * |fullFejerRadialCoefficient q H h| ^ 2 *
          (6 / (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro h hh
      gcongr
      exact radialFiberL2SqSum_le q H h hq
    _ = ((q : ℝ) ^ 2 * (6 / (q : ℝ) ^ 2)) * radialL2SqSum q H := by
      unfold radialL2SqSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ ((q : ℝ) ^ 2 * (6 / (q : ℝ) ^ 2)) * (6 / (q : ℝ)) := by
      gcongr
      exact radialL2SqSum_le q H hq
    _ = 36 / (q : ℝ) := by
      field_simp [hq.ne']
      ring

/-- The collected `L2` loss is `O(q⁻¹/²)`. -/
theorem nonzeroCollectedFejerL2Norm_le
    (q H : ℕ) (hq : 0 < q) :
    nonzeroCollectedFejerL2Norm q H ≤ 6 / Real.sqrt q := by
  have hsum0 : 0 ≤ nonzeroCollectedFejerL2SqNorm q H := by
    unfold nonzeroCollectedFejerL2SqNorm
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqR
  unfold nonzeroCollectedFejerL2Norm
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hsum0]
  calc
    nonzeroCollectedFejerL2SqNorm q H ≤ 36 / (q : ℝ) :=
      nonzeroCollectedFejerL2SqNorm_le q H hq
    _ = (6 / Real.sqrt (q : ℝ)) ^ 2 := by
      rw [div_pow, show (6 : ℝ) ^ 2 = 36 by norm_num,
        Real.sq_sqrt hqR.le]

/-- The real Fejer-smoothed number of visits to one half-open cylinder. -/
def smoothedCount (x : ℕ → ℝ) (P Q H : ℕ) (a : Fin Q) : ℝ :=
  ∑ j ∈ range P, fejerApproximation Q a H (x j)

/-- Sum of squared Fejer-smoothed cylinder counts. -/
def smoothedEnergy (x : ℕ → ℝ) (P Q H : ℕ) : ℝ :=
  ∑ a : Fin Q, smoothedCount x P Q H a ^ 2

/-- Sum of squared exact half-open cylinder counts. -/
def exactCylinderEnergy (x : ℕ → ℝ) (P Q : ℕ) : ℝ :=
  ∑ a : Fin Q, (cylinderCount x P Q a : ℝ) ^ 2

/-- Half the total two-endpoint count over all half-open cylinders. At the
disjoint widths used below this counts each grid-boundary visit once. -/
def aggregateBoundaryCount
    (x : ℕ → ℝ) (P Q : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : Fin Q, (twoBoundaryCount x P Q a δ : ℝ)

/-- Aggregating the scalar Fejer errors before comparing squared energies.
Every boundary and tail term remains literal in the conclusion. -/
theorem abs_smoothedEnergy_sub_exactCylinderEnergy_le
    (x : ℕ → ℝ) (P Q H : ℕ) (δ : ℝ)
    (hQ : 0 < Q)
    (hx : ∀ j < P, x j ∈ Set.Ico (0 : ℝ) 1)
    (hδ : 0 < δ) (hδQ : δ ≤ 1 / (2 * (Q : ℝ))) :
    |smoothedEnergy x P Q H - exactCylinderEnergy x P Q| ≤
      4 * P * aggregateBoundaryCount x P Q δ +
        2 * Q * P ^ 2 / (2 * (H + 1) * δ) := by
  classical
  have hsmooth_bounds (a : Fin Q) :
      0 ≤ smoothedCount x P Q H a ∧ smoothedCount x P Q H a ≤ P := by
    constructor
    · unfold smoothedCount
      exact Finset.sum_nonneg fun j hj =>
        (fejerApproximation_mem_unitInterval Q a H (x j) hQ a.isLt).1
    · unfold smoothedCount
      calc
        (∑ j ∈ range P, fejerApproximation Q a H (x j)) ≤
            ∑ _j ∈ range P, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (fejerApproximation_mem_unitInterval
            Q a H (x j) hQ a.isLt).2
        _ = P := by simp
  have hexact_bounds (a : Fin Q) :
      0 ≤ (cylinderCount x P Q a : ℝ) ∧
        (cylinderCount x P Q a : ℝ) ≤ P := by
    constructor
    · positivity
    · unfold cylinderCount
      have hc :
          ((range P).filter fun j => inCylinder Q a (x j)).card ≤ P := by
        simpa using Finset.card_filter_le (range P)
          (fun j => inCylinder Q a (x j))
      exact_mod_cast hc
  have hcount_error (a : Fin Q) :
      |smoothedCount x P Q H a - (cylinderCount x P Q a : ℝ)| ≤
        (twoBoundaryCount x P Q a δ : ℝ) +
          (P : ℝ) / (2 * (H + 1 : ℝ) * δ) := by
    have h := (fejerEstimator_error_and_expansion x P Q a H δ
      hQ a.isLt hx hδ hδQ).1
    rw [show
      fejerEstimator x P Q a H - (cylinderCount x P Q a : ℂ) =
        ((smoothedCount x P Q H a -
          (cylinderCount x P Q a : ℝ) : ℝ) : ℂ) by
      unfold fejerEstimator smoothedCount
      push_cast
      rfl] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  rw [smoothedEnergy, exactCylinderEnergy, ← Finset.sum_sub_distrib]
  calc
    |∑ a : Fin Q,
        (smoothedCount x P Q H a ^ 2 -
          (cylinderCount x P Q a : ℝ) ^ 2)| ≤
        ∑ a : Fin Q,
          |smoothedCount x P Q H a ^ 2 -
            (cylinderCount x P Q a : ℝ) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin Q,
        2 * P * ((twoBoundaryCount x P Q a δ : ℝ) +
          (P : ℝ) / (2 * (H + 1 : ℝ) * δ)) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [sq_sub_sq, abs_mul]
      have hsum :
          |smoothedCount x P Q H a +
            (cylinderCount x P Q a : ℝ)| ≤ 2 * P := by
        rw [abs_of_nonneg
          (add_nonneg (hsmooth_bounds a).1 (hexact_bounds a).1)]
        linarith [(hsmooth_bounds a).2, (hexact_bounds a).2]
      exact mul_le_mul hsum (hcount_error a) (abs_nonneg _) (by positivity)
    _ = 4 * P * aggregateBoundaryCount x P Q δ +
        2 * Q * P ^ 2 / (2 * (H + 1) * δ) := by
      unfold aggregateBoundaryCount
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

theorem fullFejerRadialCoefficient_eq_zero_of_dvd
    {q M : ℕ} {h : ℤ} (hq : 0 < q) (hzero : h ≠ 0)
    (hdvd : (q : ℤ) ∣ h) :
    fullFejerRadialCoefficient q M h = 0 := by
  rcases hdvd with ⟨z, rfl⟩
  rw [fullFejerRadialCoefficient, if_neg (mul_ne_zero
    (by exact_mod_cast hq.ne') (by
      intro hz
      subst z
      simp at hzero))]
  have harg : Real.pi * (((q : ℤ) * z : ℤ) : ℝ) / (q : ℝ) =
      (z : ℝ) * Real.pi := by
    push_cast
    field_simp [hq.ne']
  rw [harg, Real.sin_int_mul_pi]
  simp

theorem sum_fullFejerCylinderCoefficient
    (q M : ℕ) (h : ℤ) (hq : 0 < q) :
    ∑ a : Fin q, fullFejerCylinderCoefficient q a M h =
      if h = 0 then 1 else 0 := by
  classical
  have hcenter (a : Fin q) :
      (((a : ℕ) : ℝ) + 1 / 2) / q =
        1 / (2 * (q : ℝ)) + (a : ℝ) / q := by
    field_simp [hq.ne']
    ring
  unfold fullFejerCylinderCoefficient
  simp_rw [hcenter, Theory.PiDigits.T27.phase_add_real]
  rw [← Finset.mul_sum, ← Finset.mul_sum, phase_grid_sum q hq]
  by_cases hzero : h = 0
  · subst h
    simp [fullFejerRadialCoefficient, Theory.PiDigits.T27.phase_zero]
    field_simp [hq.ne']
  · rw [if_neg hzero]
    by_cases hdvd : (q : ℤ) ∣ -h
    · rw [if_pos hdvd]
      have hz : fullFejerRadialCoefficient q M h = 0 :=
        fullFejerRadialCoefficient_eq_zero_of_dvd hq hzero
          (by simpa using (dvd_neg.mp hdvd))
      simp [hz]
    · rw [if_neg hdvd]
      ring

theorem fejerApproximation_eq_fullFejerAmplitude
    (q a M : ℕ) (x : ℝ) (hq : 0 < q) (ha : a < q) :
    (fejerApproximation q a M x : ℂ) =
      fullFejerAmplitude q a M (fun h => phase h x) := by
  rw [fullFejerAmplitude_eq_existing]
  rw [fejerApproximation_eq_aggregated q a M x hq ha]
  simp only [Theory.PiDigits.T27.phase_zero, mul_one]

theorem sum_fejerApproximation_eq_one
    (q M : ℕ) (x : ℝ) (hq : 0 < q) :
    ∑ a : Fin q, fejerApproximation q a M x = 1 := by
  have happ (a : Fin q) :
      (fejerApproximation q a M x : ℂ) =
        fullFejerAmplitude q a M (fun h => phase h x) :=
    fejerApproximation_eq_fullFejerAmplitude q a M x hq a.isLt
  have hcomplex := congrArg Complex.re
    (show (∑ a : Fin q, (fejerApproximation q a M x : ℂ)) = 1 by
      simp_rw [happ]
      unfold fullFejerAmplitude
      rw [Finset.sum_comm]
      calc
        (∑ h ∈ signedFrequenciesZero M,
            ∑ a : Fin q,
              fullFejerCylinderCoefficient q a M h * phase h x) =
            ∑ h ∈ signedFrequenciesZero M,
              (∑ a : Fin q, fullFejerCylinderCoefficient q a M h) *
                phase h x := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [Finset.sum_mul]
        _ = 1 := by
          rw [show signedFrequenciesZero M = insert 0 (signedFrequencies M) by
            ext h
            rw [mem_signedFrequenciesZero]
            simp only [Finset.mem_insert, mem_signedFrequencies]
            by_cases hz : h = 0 <;> simp [hz]]
          rw [Finset.sum_insert]
          · rw [sum_fullFejerCylinderCoefficient q M 0 hq]
            simp only [if_pos, Theory.PiDigits.T27.phase_zero, mul_one]
            rw [add_eq_left]
            apply Finset.sum_eq_zero
            intro h hh
            have hz := (mem_signedFrequencies.mp hh).1
            rw [sum_fullFejerCylinderCoefficient q M h hq, if_neg hz,
              zero_mul]
          · simp [mem_signedFrequencies])
  push_cast at hcomplex
  simpa using hcomplex

theorem inCylinder_label_unique {Q b c : ℕ} {y : ℝ} (hQ : 0 < Q)
    (hb : inCylinder Q b y) (hc : inCylinder Q c y) : b = c := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  unfold inCylinder cylinderLeft cylinderRight at hb hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbc | hcb
  · have hsucc : b + 1 ≤ c := Nat.succ_le_iff.mpr hbc
    have hdiv : (((b + 1 : ℕ) : ℝ) / Q) ≤ (c : ℝ) / Q :=
      (div_le_div_iff_of_pos_right hQR).2 (by exact_mod_cast hsucc)
    linarith [hb.2, hc.1]
  · have hsucc : c + 1 ≤ b := Nat.succ_le_iff.mpr hcb
    have hdiv : (((c + 1 : ℕ) : ℝ) / Q) ≤ (b : ℝ) / Q :=
      (div_le_div_iff_of_pos_right hQR).2 (by exact_mod_cast hsucc)
    linarith [hc.2, hb.1]

/-- Boundary visits counted at the two endpoints of the unique active
half-open cylinder. No endpoint is discarded. -/
def activeBoundaryCount (x : ℕ → ℝ) (P Q : ℕ)
    (label : ℕ → Fin Q) (δ : ℝ) : ℕ :=
  ((range P).filter fun j =>
    circularDistance (x j) (cylinderLeft Q (label j)) < δ ∨
      circularDistance (x j) (cylinderRight Q (label j)) < δ).card

theorem sum_abs_sub_oneHot_eq {Q : ℕ} (f : Fin Q → ℝ) (b : Fin Q)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1)
    (hsum : ∑ a : Fin Q, f a = 1) :
    ∑ a : Fin Q, |f a - if a = b then 1 else 0| =
      2 * (1 - f b) := by
  classical
  have hpoint (a : Fin Q) :
      |f a - if a = b then 1 else 0| =
        if a = b then 1 - f a else f a := by
    by_cases hab : a = b
    · subst a
      simp only [if_pos]
      rw [abs_of_nonpos (sub_nonpos.mpr (hf1 b))]
      ring
    · simp only [hab, if_false, sub_zero, abs_of_nonneg (hf0 a)]
  calc
    ∑ a : Fin Q, |f a - if a = b then 1 else 0| =
        ∑ a : Fin Q, if a = b then 1 - f a else f a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hpoint a
    _ = ∑ a : Fin Q,
          (f a + if a = b then 1 - 2 * f a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hab : a = b
      · simp [hab]
        ring
      · simp [hab]
    _ = (∑ a : Fin Q, f a) +
        ∑ a : Fin Q, if a = b then 1 - 2 * f a else 0 := by
      rw [Finset.sum_add_distrib]
    _ = 1 + (1 - 2 * f b) := by
      rw [hsum]
      simp [Finset.sum_ite_eq']
    _ = 2 * (1 - f b) := by ring

theorem cylinderCount_eq_sum_activeOneHot
    (x : ℕ → ℝ) (P Q : ℕ) (label : ℕ → Fin Q) (hQ : 0 < Q)
    (hactive : ∀ j < P, inCylinder Q (label j) (x j)) (a : Fin Q) :
    (cylinderCount x P Q a : ℝ) =
      ∑ j ∈ range P, if a = label j then (1 : ℝ) else 0 := by
  classical
  have hnat : cylinderCount x P Q a =
      ∑ j ∈ range P, if a = label j then (1 : ℕ) else 0 := by
    unfold cylinderCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j hj
    have hjP := Finset.mem_range.mp hj
    by_cases ha : a = label j
    · subst a
      simp [hactive j hjP]
    · have hnot : ¬inCylinder Q a (x j) := by
        intro hmem
        apply ha
        apply Fin.ext
        exact inCylinder_label_unique hQ hmem (hactive j hjP)
      simp [ha, hnot]
  exact_mod_cast hnat

/-- Sharp aggregate boundary estimate. The Fejer tails are summed only after
using that the smoothed cylinder vector has total mass one, so no factor `Q`
is lost. -/
theorem abs_smoothedEnergy_sub_exactCylinderEnergy_le_active
    (x : ℕ → ℝ) (P Q H : ℕ) (label : ℕ → Fin Q) (δ : ℝ)
    (hQ : 0 < Q)
    (hsum : ∀ j < P,
      ∑ a : Fin Q, fejerApproximation Q a H (x j) = 1)
    (hactive : ∀ j < P, inCylinder Q (label j) (x j))
    (hδ : 0 < δ) (hδQ : δ ≤ 1 / (2 * (Q : ℝ))) :
    |smoothedEnergy x P Q H - exactCylinderEnergy x P Q| ≤
      4 * P * (activeBoundaryCount x P Q label δ : ℝ) +
        2 * P ^ 2 / ((H + 1 : ℝ) * δ) := by
  classical
  have hx (j : ℕ) (hj : j < P) : x j ∈ Set.Ico (0 : ℝ) 1 := by
    have hm := hactive j hj
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    unfold inCylinder cylinderLeft cylinderRight at hm
    constructor
    · exact (by positivity : (0 : ℝ) ≤ (label j : ℝ) / Q) |>.trans hm.1
    · calc
        x j < ((((label j : ℕ) + 1 : ℕ) : ℝ) / Q) := hm.2
        _ ≤ 1 := (div_le_one hQR).2 (by
          exact_mod_cast (Nat.succ_le_iff.mpr (label j).isLt))
  have hδhalf : δ ≤ 1 / 2 := by
    have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    calc
      δ ≤ 1 / (2 * (Q : ℝ)) := hδQ
      _ ≤ 1 / 2 := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Q)
          (by norm_num : (0 : ℝ) < 2)).2
        nlinarith
  have hsmooth_bounds (a : Fin Q) :
      0 ≤ smoothedCount x P Q H a ∧
        smoothedCount x P Q H a ≤ P := by
    constructor
    · unfold smoothedCount
      exact Finset.sum_nonneg fun j hj =>
        (fejerApproximation_mem_unitInterval Q a H (x j) hQ a.isLt).1
    · unfold smoothedCount
      calc
        (∑ j ∈ range P, fejerApproximation Q a H (x j)) ≤
            ∑ _j ∈ range P, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (fejerApproximation_mem_unitInterval
            Q a H (x j) hQ a.isLt).2
        _ = P := by simp
  have hexact_bounds (a : Fin Q) :
      0 ≤ (cylinderCount x P Q a : ℝ) ∧
        (cylinderCount x P Q a : ℝ) ≤ P := by
    constructor
    · positivity
    · unfold cylinderCount
      have hc :
          ((range P).filter fun j => inCylinder Q a (x j)).card ≤ P := by
        simpa using Finset.card_filter_le (range P)
          (fun j => inCylinder Q a (x j))
      exact_mod_cast hc
  have hpoint (j : ℕ) (hj : j ∈ range P) :
      (∑ a : Fin Q,
        |fejerApproximation Q a H (x j) -
          if a = label j then 1 else 0|) ≤
        2 * ((if
            circularDistance (x j) (cylinderLeft Q (label j)) < δ ∨
              circularDistance (x j) (cylinderRight Q (label j)) < δ
          then (1 : ℝ) else 0) +
          1 / (2 * (H + 1 : ℝ) * δ)) := by
    have hjP := Finset.mem_range.mp hj
    have hmass := sum_abs_sub_oneHot_eq
      (fun a : Fin Q => fejerApproximation Q a H (x j)) (label j)
      (fun a => (fejerApproximation_mem_unitInterval
        Q a H (x j) hQ a.isLt).1)
      (fun a => (fejerApproximation_mem_unitInterval
        Q a H (x j) hQ a.isLt).2)
      (hsum j hjP)
    rw [hmass]
    by_cases hb :
        circularDistance (x j) (cylinderLeft Q (label j)) < δ ∨
          circularDistance (x j) (cylinderRight Q (label j)) < δ
    · rw [if_pos hb]
      have hf0 := (fejerApproximation_mem_unitInterval
        Q (label j) H (x j) hQ (label j).isLt).1
      have htail0 : 0 ≤ 1 / (2 * (H + 1 : ℝ) * δ) := by positivity
      nlinarith
    · rw [if_neg hb]
      push Not at hb
      have hind : cylinderIndicator Q (label j) (x j) = 1 := by
        unfold cylinderIndicator
        rw [Int.fract_eq_self.2 (hx j hjP)]
        simp [hactive j hjP]
      have ht := norm_fejerApproximation_sub_indicator_le
        Q (label j) H (x j) δ hQ (label j).isLt (hx j hjP)
        hδ hδhalf hb.1 hb.2
      rw [show
          ((fejerApproximation Q (label j) H (x j) : ℝ) : ℂ) -
              (cylinderIndicator Q (label j) (x j) : ℂ) =
            ((fejerApproximation Q (label j) H (x j) - 1 : ℝ) : ℂ) by
        rw [hind]
        push_cast
        rfl,
        Complex.norm_real, Real.norm_eq_abs] at ht
      have hf1 := (fejerApproximation_mem_unitInterval
        Q (label j) H (x j) hQ (label j).isLt).2
      rw [abs_of_nonpos (sub_nonpos.mpr hf1)] at ht
      nlinarith
  have hboundary_sum :
      (∑ j ∈ range P,
        if circularDistance (x j) (cylinderLeft Q (label j)) < δ ∨
            circularDistance (x j) (cylinderRight Q (label j)) < δ
          then (1 : ℝ) else 0) =
        (activeBoundaryCount x P Q label δ : ℝ) := by
    unfold activeBoundaryCount
    norm_cast
    rw [Finset.card_filter]
  have hL1 :
      ∑ a : Fin Q,
          |smoothedCount x P Q H a -
            (cylinderCount x P Q a : ℝ)| ≤
        2 * (activeBoundaryCount x P Q label δ : ℝ) +
          P / ((H + 1 : ℝ) * δ) := by
    calc
      ∑ a : Fin Q,
          |smoothedCount x P Q H a -
            (cylinderCount x P Q a : ℝ)| =
          ∑ a : Fin Q, |∑ j ∈ range P,
            (fejerApproximation Q a H (x j) -
              if a = label j then 1 else 0)| := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [cylinderCount_eq_sum_activeOneHot
          x P Q label hQ hactive a]
        unfold smoothedCount
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : Fin Q, ∑ j ∈ range P,
          |fejerApproximation Q a H (x j) -
            if a = label j then 1 else 0| := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ range P, ∑ a : Fin Q,
          |fejerApproximation Q a H (x j) -
            if a = label j then 1 else 0| := by
        rw [Finset.sum_comm]
      _ ≤ ∑ j ∈ range P,
          2 * ((if
              circularDistance (x j) (cylinderLeft Q (label j)) < δ ∨
                circularDistance (x j) (cylinderRight Q (label j)) < δ
            then (1 : ℝ) else 0) +
            1 / (2 * (H + 1 : ℝ) * δ)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hpoint j hj
      _ = 2 * (activeBoundaryCount x P Q label δ : ℝ) +
          P / ((H + 1 : ℝ) * δ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hboundary_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hδ.ne', show (H + 1 : ℝ) ≠ 0 by positivity]
  rw [smoothedEnergy, exactCylinderEnergy, ← Finset.sum_sub_distrib]
  calc
    |∑ a : Fin Q,
        (smoothedCount x P Q H a ^ 2 -
          (cylinderCount x P Q a : ℝ) ^ 2)| ≤
        ∑ a : Fin Q,
          |smoothedCount x P Q H a ^ 2 -
            (cylinderCount x P Q a : ℝ) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin Q,
        2 * P * |smoothedCount x P Q H a -
          (cylinderCount x P Q a : ℝ)| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [sq_sub_sq, abs_mul]
      have hsum :
          |smoothedCount x P Q H a +
            (cylinderCount x P Q a : ℝ)| ≤ 2 * P := by
        rw [abs_of_nonneg
          (add_nonneg (hsmooth_bounds a).1 (hexact_bounds a).1)]
        linarith [(hsmooth_bounds a).2, (hexact_bounds a).2]
      exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ = 2 * P * ∑ a : Fin Q,
        |smoothedCount x P Q H a -
          (cylinderCount x P Q a : ℝ)| := by
      rw [Finset.mul_sum]
    _ ≤ 2 * P *
        (2 * (activeBoundaryCount x P Q label δ : ℝ) +
          P / ((H + 1 : ℝ) * δ)) := by
      exact mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 4 * P * (activeBoundaryCount x P Q label δ : ℝ) +
        2 * P ^ 2 / ((H + 1 : ℝ) * δ) := by
      ring

abbrev piOrbit : ℕ → ℝ := Theory.PiDigits.T27.piFractionalOrbit

def parentOrder (ell : ℕ) : ℕ := 40 * (10 ^ ell) ^ 3

def successorOrder (ell : ℕ) : ℕ := 8000 * (10 ^ ell) ^ 3

def parentBoundaryWidth (ell : ℕ) : ℝ :=
  1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)

def successorBoundaryWidth (ell : ℕ) : ℝ :=
  1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)

/-- Appending the literal decimal digit `d` to parent label `a`. -/
def decimalSuccessorLabel (ell : ℕ) (a : Fin (10 ^ ell)) (d : Fin 10) :
    Fin (10 ^ (ell + 1)) :=
  ⟨10 * (a : ℕ) + (d : ℕ), by
    rw [pow_succ]
    have ha := a.isLt
    have hd := d.isLt
    omega⟩

/-- The checked decimal code selects the literal half-open interval containing
the corresponding pi orbit point. -/
theorem piOrbit_inCylinder (ell j : ℕ) :
    inCylinder (10 ^ ell) (piCylinderCode ell j) (piOrbit j) := by
  have hmem : piDecimalCircleOrbit j ∈
      decimalCylinder ell (piCylinderCode ell j) := by
    unfold decimalCylinder
    exact (piCylinderCode_eq_decimalCode ell j).symm
  rw [mem_decimalCylinder_iff, unitCoordinate_piDecimalCircleOrbit] at hmem
  simpa [inCylinder, cylinderLeft, cylinderRight, piOrbit,
    Theory.PiDigits.T20.baseTenOrbit,
    Theory.PiDigits.T27.piFractionalOrbit] using hmem

theorem cylinderCount_piOrbit_eq_piCylinderFiber_card
    (ell P : ℕ) (a : Fin (10 ^ ell)) :
    (cylinderCount piOrbit P (10 ^ ell) a : ℝ) =
      ((piCylinderFiber ell P a).card : ℝ) := by
  classical
  have hc := cylinderCount_eq_sum_activeOneHot piOrbit P (10 ^ ell)
    (fun j => piCylinderCode ell j) (by positivity)
    (fun j hj => piOrbit_inCylinder ell j) a
  rw [hc]
  norm_cast
  unfold piCylinderFiber
  rw [Finset.card_filter]
  calc
    (∑ j ∈ Finset.range P, if a = piCylinderCode ell j then 1 else 0) =
        ∑ j ∈ Finset.range P,
          if piCylinderCode ell j = a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [eq_comm]
    _ = ∑ i : Fin P, if piCylinderCode ell i = a then 1 else 0 := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if piCylinderCode ell j = a then (1 : ℕ) else 0) P

theorem exactCylinderEnergy_piOrbit_eq_piCylinderCollisionEnergy
    (ell P : ℕ) :
    exactCylinderEnergy piOrbit P (10 ^ ell) =
      (piCylinderCollisionEnergy ell P : ℝ) := by
  unfold exactCylinderEnergy piCylinderCollisionEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  rw [cylinderCount_piOrbit_eq_piCylinderFiber_card]

/-- One literal row exposes the half-open parent and successor intervals, the
row inequalities `1 ≤ ell < m ≤ k`, the cutoff `P`, and both finite signed
frequency expansions. -/
theorem literal_row_halfOpen_fejer_expansions
    (ell m k P : ℕ) (a : Fin (10 ^ ell)) (d : Fin 10) (x : ℝ)
    (_hell : 1 ≤ ell) (_hellm : ell < m) (_hmk : m ≤ k) (_hP : 0 < P) :
    cylinderIndicator (10 ^ ell) a x =
        (if Int.fract x ∈ Set.Ico
          ((a : ℕ) / (10 ^ ell : ℝ))
          (((a : ℕ) + 1) / (10 ^ ell : ℝ)) then 1 else 0) ∧
    cylinderIndicator (10 ^ (ell + 1)) (decimalSuccessorLabel ell a d) x =
        (if Int.fract x ∈ Set.Ico
          ((10 * (a : ℕ) + (d : ℕ) : ℕ) /
            (10 * (10 ^ ell : ℕ) : ℝ))
          (((10 * (a : ℕ) + (d : ℕ) : ℕ) + 1) /
            (10 * (10 ^ ell : ℕ) : ℝ)) then 1 else 0) ∧
    fejerEstimator piOrbit P (10 ^ ell) a (40 * (10 ^ ell) ^ 3) =
        (P : ℝ) / (10 ^ ell : ℕ) +
          ∑ h ∈ signedFrequencies (40 * (10 ^ ell) ^ 3),
            fejerCylinderCoefficient (10 ^ ell) a
                (40 * (10 ^ ell) ^ 3) h *
              exponentialSum piOrbit P h ∧
    fejerEstimator piOrbit P (10 ^ (ell + 1))
        (decimalSuccessorLabel ell a d) (8000 * (10 ^ ell) ^ 3) =
        (P : ℝ) / (10 ^ (ell + 1) : ℕ) +
          ∑ h ∈ signedFrequencies (8000 * (10 ^ ell) ^ 3),
            fejerCylinderCoefficient (10 ^ (ell + 1))
                (decimalSuccessorLabel ell a d)
                (8000 * (10 ^ ell) ^ 3) h *
              exponentialSum piOrbit P h := by
  have hx : ∀ j < P, piOrbit j ∈ Set.Ico (0 : ℝ) 1 := by
    intro j hj
    simpa [piOrbit, Theory.PiDigits.T27.piFractionalOrbit,
      Theory.PiDigits.T20.baseTenOrbit] using
      Theory.PiDigits.T20.baseTenOrbit_mem_Ico Real.pi j
  have hpExp := (fejerEstimator_error_and_expansion
    piOrbit P (10 ^ ell) a (40 * (10 ^ ell) ^ 3)
      (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ))
      (by positivity) a.isLt hx (by positivity) (by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        apply one_div_le_one_div_of_le (by positivity)
        have hq : (1 : ℝ) ≤ (10 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
        nlinarith [sq_nonneg ((10 : ℝ) ^ ell - 1)])).2
  have hsExp := (fejerEstimator_error_and_expansion
    piOrbit P (10 ^ (ell + 1)) (decimalSuccessorLabel ell a d)
      (8000 * (10 ^ ell) ^ 3)
      (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ))
      (by positivity) (decimalSuccessorLabel ell a d).isLt hx (by positivity)
      (by
        rw [show 10 ^ (ell + 1) = 10 * 10 ^ ell by ring]
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        apply one_div_le_one_div_of_le (by positivity)
        have hq : (1 : ℝ) ≤ (10 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
        nlinarith [sq_nonneg ((10 : ℝ) ^ ell - 1)])).2
  refine ⟨?_, ?_, hpExp, hsExp⟩
  · simp [cylinderIndicator, inCylinder, cylinderLeft, cylinderRight]
  · simp [cylinderIndicator, inCylinder, cylinderLeft, cylinderRight,
      decimalSuccessorLabel, pow_succ, Nat.mul_comm]

/-- Parent-scale aggregate boundary error with the literal cutoff
`H0 = 40*(10^ell)^3` and half-open width `1/(4*(10^ell)^2)`. -/
theorem parent_aggregate_boundary_bound (ell P : ℕ) :
    |smoothedEnergy piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3) -
        (piCylinderCollisionEnergy ell P : ℝ)| ≤
      4 * P * (activeBoundaryCount piOrbit P (10 ^ ell)
        (fun j => piCylinderCode ell j)
        (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
      8 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
        (40 * (10 ^ ell : ℕ) ^ 3 + 1) := by
  have h := abs_smoothedEnergy_sub_exactCylinderEnergy_le_active
    piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3)
    (fun j => piCylinderCode ell j)
    (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ))
    (by positivity)
    (fun j hj => sum_fejerApproximation_eq_one
      (10 ^ ell) (40 * (10 ^ ell) ^ 3) (piOrbit j) (by positivity))
    (fun j hj => piOrbit_inCylinder ell j)
    (by positivity) (by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      apply one_div_le_one_div_of_le (by positivity)
      have hq : (1 : ℝ) ≤ (10 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
      nlinarith [sq_nonneg ((10 : ℝ) ^ ell - 1)])
  rw [exactCylinderEnergy_piOrbit_eq_piCylinderCollisionEnergy] at h
  convert h using 1
  push_cast
  field_simp
  <;> ring

/-- Successor-scale aggregate boundary error with the literal cutoff
`H1 = 8000*(10^ell)^3`, depth `ell+1`, and width `1/(400*(10^ell)^2)`. -/
theorem successor_aggregate_boundary_bound (ell P : ℕ) :
    |smoothedEnergy piOrbit P (10 ^ (ell + 1)) (8000 * (10 ^ ell) ^ 3) -
        (piCylinderCollisionEnergy (ell + 1) P : ℝ)| ≤
      4 * P * (activeBoundaryCount piOrbit P (10 ^ (ell + 1))
        (fun j => piCylinderCode (ell + 1) j)
        (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
      800 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
        (8000 * (10 ^ ell : ℕ) ^ 3 + 1) := by
  have h := abs_smoothedEnergy_sub_exactCylinderEnergy_le_active
    piOrbit P (10 ^ (ell + 1)) (8000 * (10 ^ ell) ^ 3)
    (fun j => piCylinderCode (ell + 1) j)
    (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ))
    (by positivity)
    (fun j hj => sum_fejerApproximation_eq_one
      (10 ^ (ell + 1)) (8000 * (10 ^ ell) ^ 3) (piOrbit j) (by positivity))
    (fun j hj => piOrbit_inCylinder (ell + 1) j)
    (by positivity) (by
      rw [show 10 ^ (ell + 1) = 10 * 10 ^ ell by ring]
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      apply one_div_le_one_div_of_le (by positivity)
      have hq : (1 : ℝ) ≤ (10 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
      nlinarith [sq_nonneg ((10 : ℝ) ^ ell - 1)])
  rw [exactCylinderEnergy_piOrbit_eq_piCylinderCollisionEnergy] at h
  convert h using 1
  push_cast
  field_simp
  <;> ring

/-- Spectrum on the exact half-open cutoff, including the zero mode `P`. -/
def fullSampleSpectrum (x : ℕ → ℝ) (P : ℕ) (h : ℤ) : ℂ :=
  exponentialSum x P h

theorem smoothedCount_eq_fullFejerAmplitude
    (x : ℕ → ℝ) (P Q H : ℕ) (a : Fin Q) (hQ : 0 < Q) :
    (smoothedCount x P Q H a : ℂ) =
      fullFejerAmplitude Q a H (fullSampleSpectrum x P) := by
  classical
  unfold smoothedCount fullFejerAmplitude fullSampleSpectrum
  push_cast
  simp_rw [fejerApproximation_eq_fullFejerAmplitude Q a H _ hQ a.isLt]
  unfold fullFejerAmplitude
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.mul_sum]
  rfl

/-- Exact finite tensor expansion after collecting all parent labels. -/
theorem smoothedEnergy_eq_collected_expansion
    (x : ℕ → ℝ) (P Q H : ℕ) (hQ : 0 < Q) :
    (smoothedEnergy x P Q H : ℂ) =
      ∑ h ∈ signedFrequenciesZero H,
        ∑ k ∈ signedFrequenciesZero H,
          collectedFejerCoefficient Q H h k *
            (fullSampleSpectrum x P h * fullSampleSpectrum x P k) := by
  unfold smoothedEnergy
  push_cast
  simp_rw [smoothedCount_eq_fullFejerAmplitude x P Q H _ hQ]
  exact sum_fullFejerAmplitude_sq_eq_collected
    Q H (fullSampleSpectrum x P)

/-- The finite collected Fourier remainder, with only `(0,0)` deleted. -/
def nonzeroFejerRemainder
    (x : ℕ → ℝ) (P Q H : ℕ) : ℂ :=
  ∑ h ∈ signedFrequenciesZero H,
    ∑ k ∈ signedFrequenciesZero H,
      if h = 0 ∧ k = 0 then 0
      else collectedFejerCoefficient Q H h k *
        (fullSampleSpectrum x P h * fullSampleSpectrum x P k)

theorem collectedFejerCoefficient_zero_zero
    (Q H : ℕ) (hQ : 0 < Q) :
    collectedFejerCoefficient Q H 0 0 = (1 / (Q : ℝ) : ℝ) := by
  rw [collectedFejerCoefficient_eq Q H 0 0 hQ]
  simp [fullFejerRadialCoefficient, Theory.PiDigits.T27.phase_zero]
  field_simp [hQ.ne']

theorem fullSampleSpectrum_zero
    (x : ℕ → ℝ) (P : ℕ) :
    fullSampleSpectrum x P 0 = P := by
  unfold fullSampleSpectrum exponentialSum Theory.PiDigits.T27.exponentialSum
  simp [Theory.PiDigits.T27.phase_zero]

theorem doubleSum_eq_zeroPair_add_remainder
    {α : Type*} [AddCommMonoid α] (S : Finset ℤ) (f : ℤ → ℤ → α)
    (hzero : 0 ∈ S) :
    (∑ h ∈ S, ∑ k ∈ S, f h k) =
      f 0 0 + ∑ h ∈ S, ∑ k ∈ S,
        if h = 0 ∧ k = 0 then 0 else f h k := by
  classical
  calc
    (∑ h ∈ S, ∑ k ∈ S, f h k) =
        ∑ h ∈ S, ∑ k ∈ S,
          ((if h = 0 ∧ k = 0 then f 0 0 else 0) +
            if h = 0 ∧ k = 0 then 0 else f h k) := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hz : h = 0 ∧ k = 0
      · rcases hz with ⟨rfl, rfl⟩
        simp
      · simp [hz]
    _ = (∑ h ∈ S, ∑ k ∈ S,
          if h = 0 ∧ k = 0 then f 0 0 else 0) +
        ∑ h ∈ S, ∑ k ∈ S,
          if h = 0 ∧ k = 0 then 0 else f h k := by
      simp_rw [Finset.sum_add_distrib]
    _ = f 0 0 + ∑ h ∈ S, ∑ k ∈ S,
        if h = 0 ∧ k = 0 then 0 else f h k := by
      congr 1
      rw [Finset.sum_eq_single 0]
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro k hk hk0
          simp [hk0]
        · intro hn
          exact (hn hzero).elim
      · intro h hh hh0
        apply Finset.sum_eq_zero
        intro k hk
        simp [hh0]
      · intro hn
        exact (hn hzero).elim

theorem smoothedEnergy_eq_zeroMode_add_remainder
    (x : ℕ → ℝ) (P Q H : ℕ) (hQ : 0 < Q) :
    (smoothedEnergy x P Q H : ℂ) =
      (P : ℂ) ^ 2 / Q + nonzeroFejerRemainder x P Q H := by
  classical
  rw [smoothedEnergy_eq_collected_expansion x P Q H hQ]
  rw [doubleSum_eq_zeroPair_add_remainder
    (signedFrequenciesZero H)
    (fun h k => collectedFejerCoefficient Q H h k *
      (fullSampleSpectrum x P h * fullSampleSpectrum x P k))
    (by simp [signedFrequenciesZero])]
  unfold nonzeroFejerRemainder
  rw [collectedFejerCoefficient_zero_zero Q H hQ,
    fullSampleSpectrum_zero]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- The two literal T59 scales, collected before taking norms. -/
def rowFourierRemainder (ell P : ℕ) : ℂ :=
  nonzeroFejerRemainder piOrbit P (10 ^ (ell + 1))
      (8000 * (10 ^ ell) ^ 3) -
    (1 / 2 : ℂ) * nonzeroFejerRemainder piOrbit P (10 ^ ell)
      (40 * (10 ^ ell) ^ 3)

theorem smoothed_row_defect_eq_zeroMode_add_remainder (ell P : ℕ) :
    (smoothedEnergy piOrbit P (10 ^ (ell + 1))
        (8000 * (10 ^ ell) ^ 3) : ℂ) -
      (1 / 2 : ℂ) *
        smoothedEnergy piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3) =
      -(2 : ℂ) * P ^ 2 / (5 * (10 ^ ell : ℕ)) +
        rowFourierRemainder ell P := by
  rw [smoothedEnergy_eq_zeroMode_add_remainder
      piOrbit P (10 ^ (ell + 1)) (8000 * (10 ^ ell) ^ 3) (by positivity),
    smoothedEnergy_eq_zeroMode_add_remainder
      piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3) (by positivity)]
  unfold rowFourierRemainder
  rw [show 10 ^ (ell + 1) = 10 * 10 ^ ell by ring]
  push_cast
  field_simp
  ring

/-- Every term in the passage from exact energies to the collected Fourier
tensor is displayed. -/
theorem row_energy_defect_le_full_error (ell P : ℕ) :
    (piCylinderCollisionEnergy (ell + 1) P : ℝ) -
        (1 / 2 : ℝ) * piCylinderCollisionEnergy ell P ≤
      -2 * P ^ 2 / (5 * (10 ^ ell : ℕ)) +
        ‖rowFourierRemainder ell P‖ +
        4 * P *
          ((activeBoundaryCount piOrbit P (10 ^ (ell + 1))
              (fun j => piCylinderCode (ell + 1) j)
              (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
            (1 / 2 : ℝ) *
              (activeBoundaryCount piOrbit P (10 ^ ell)
                (fun j => piCylinderCode ell j)
                (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) +
        800 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
          (8000 * (10 ^ ell : ℕ) ^ 3 + 1) +
        4 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
          (40 * (10 ^ ell : ℕ) ^ 3 + 1) := by
  have hc := successor_aggregate_boundary_bound ell P
  have hp := parent_aggregate_boundary_bound ell P
  rw [abs_le] at hc hp
  have hsmooth := congrArg Complex.re
    (smoothed_row_defect_eq_zeroMode_add_remainder ell P)
  push_cast at hsmooth
  norm_num at hsmooth
  have hscalar :
      ((-(2 * (P : ℂ) ^ 2) /
        (5 * (10 : ℂ) ^ ell)).re) =
        -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) := by
    have hcast :
        (-(2 * (P : ℂ) ^ 2) / (5 * (10 : ℂ) ^ ell)) =
          ((-2 * (P : ℝ) ^ 2 / (5 * (10 : ℝ) ^ ell) : ℝ) : ℂ) := by
      push_cast
      ring
    calc
      (-(2 * (P : ℂ) ^ 2) / (5 * (10 : ℂ) ^ ell)).re =
          (((-2 * (P : ℝ) ^ 2 / (5 * (10 : ℝ) ^ ell) : ℝ) : ℂ)).re :=
        congrArg Complex.re hcast
      _ = -2 * (P : ℝ) ^ 2 / (5 * (10 : ℝ) ^ ell) :=
        Complex.ofReal_re _
      _ = -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hsmoothReal :
      smoothedEnergy piOrbit P (10 ^ (ell + 1))
          (8000 * (10 ^ ell) ^ 3) -
        (1 / 2 : ℝ) *
          smoothedEnergy piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3) =
        -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) +
          (rowFourierRemainder ell P).re := by
    calc
      _ = ((-(2 * (P : ℂ) ^ 2) /
            (5 * (10 : ℂ) ^ ell)).re) +
          (rowFourierRemainder ell P).re := hsmooth
      _ = _ := by rw [hscalar]
  have hre : (rowFourierRemainder ell P).re ≤
      ‖rowFourierRemainder ell P‖ := Complex.re_le_norm _
  let SC := smoothedEnergy piOrbit P (10 ^ (ell + 1))
    (8000 * (10 ^ ell) ^ 3)
  let SP := smoothedEnergy piOrbit P (10 ^ ell) (40 * (10 ^ ell) ^ 3)
  let EC : ℝ := piCylinderCollisionEnergy (ell + 1) P
  let EP : ℝ := piCylinderCollisionEnergy ell P
  let bc : ℝ := activeBoundaryCount piOrbit P (10 ^ (ell + 1))
    (fun j => piCylinderCode (ell + 1) j)
    (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ))
  let bp : ℝ := activeBoundaryCount piOrbit P (10 ^ ell)
    (fun j => piCylinderCode ell j)
    (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ))
  let tc : ℝ := 800 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
    (8000 * (10 ^ ell : ℕ) ^ 3 + 1)
  let tp : ℝ := 8 * (10 ^ ell : ℕ) ^ 2 * P ^ 2 /
    (40 * (10 ^ ell : ℕ) ^ 3 + 1)
  have hcUpper : EC ≤ SC + (4 * P * bc + tc) := by
    dsimp [EC, SC, bc, tc]
    linarith [hc.1]
  have hpNegUpper : -(1 / 2 : ℝ) * EP ≤
      -(1 / 2 : ℝ) * SP + (1 / 2 : ℝ) * (4 * P * bp + tp) := by
    dsimp [EP, SP, bp, tp]
    nlinarith [hp.2]
  have hsmoothLocal : SC - (1 / 2 : ℝ) * SP =
      -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) +
        (rowFourierRemainder ell P).re := by
    exact hsmoothReal
  have hcoarse : EC - (1 / 2 : ℝ) * EP ≤
      -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) +
        ‖rowFourierRemainder ell P‖ +
        (4 * P * bc + tc) + (1 / 2 : ℝ) * (4 * P * bp + tp) := by
    calc
      EC - (1 / 2 : ℝ) * EP = EC + (-(1 / 2 : ℝ) * EP) := by ring
      _ ≤ (SC + (4 * P * bc + tc)) +
          (-(1 / 2 : ℝ) * SP + (1 / 2 : ℝ) * (4 * P * bp + tp)) :=
        add_le_add hcUpper hpNegUpper
      _ = (-2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) +
          (rowFourierRemainder ell P).re) +
          (4 * P * bc + tc) + (1 / 2 : ℝ) * (4 * P * bp + tp) := by
        rw [← hsmoothLocal]
        ring
      _ ≤ -2 * (P : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) +
          ‖rowFourierRemainder ell P‖ +
          (4 * P * bc + tc) + (1 / 2 : ℝ) * (4 * P * bp + tp) := by
        linarith
  dsimp [EC, EP, bc, bp, tc, tp] at hcoarse
  convert hcoarse using 1 <;> ring

/-- Constant-explicit implication to one literal row of T14 and T25. The row
range is `1 ≤ ell < m ≤ k`, the cutoff is exactly `N k`, all cylinders are the
half-open cylinders encoded above, and the fixed-pi Fourier estimate remains a
hypothesis. -/
theorem boundary_and_fourier_imply_literal_t14_row
    (ell m k : ℕ) (N : ℕ → ℕ)
    (hell : 1 ≤ ell) (hellm : ell < m) (hmk : m ≤ k)
    (hcutoff : 0 < N k)
    (hboundary :
      (activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
          (fun j => piCylinderCode (ell + 1) j)
          (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
        (1 / 2 : ℝ) *
          (activeBoundaryCount piOrbit (N k) (10 ^ ell)
            (fun j => piCylinderCode ell j)
            (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) ≤
        (N k : ℝ) / (40 * (10 ^ ell : ℕ)))
    (hfourier : ‖rowFourierRemainder ell (N k)‖ ≤
      (N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ))) :
    QuantitativeSplittingLevel ell (N k) (3281 / 7281 : ℝ) (1 / 100) ∧
      rowThreshold ell (N k) (1 / 100) (3281 / 7281 : ℝ) := by
  let q : ℝ := (10 ^ ell : ℕ)
  let P : ℝ := N k
  have hq : 0 < q := by dsimp [q]; positivity
  have hP : 0 < P := by dsimp [P]; exact_mod_cast hcutoff
  have hboundaryBudget :
      4 * P *
          ((activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
              (fun j => piCylinderCode (ell + 1) j)
              (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
            (1 / 2 : ℝ) *
              (activeBoundaryCount piOrbit (N k) (10 ^ ell)
                (fun j => piCylinderCode ell j)
                (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) ≤
        P ^ 2 / (10 * q) := by
    dsimp [P, q]
    calc
      4 * (N k : ℝ) *
          ((activeBoundaryCount piOrbit (N k) (10 ^ (ell + 1))
              (fun j => piCylinderCode (ell + 1) j)
              (1 / (400 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ) +
            (1 / 2 : ℝ) *
              (activeBoundaryCount piOrbit (N k) (10 ^ ell)
                (fun j => piCylinderCode ell j)
                (1 / (4 * (10 ^ ell : ℕ) ^ 2 : ℕ)) : ℝ)) ≤
          4 * (N k : ℝ) *
            ((N k : ℝ) / (40 * (10 ^ ell : ℕ))) := by
        gcongr
      _ = (N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ)) := by ring
  have hchildTail :
      800 * q ^ 2 * P ^ 2 / (8000 * q ^ 3 + 1) <
        P ^ 2 / (10 * q) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_pos_of_pos hP]
  have hparentTail :
      4 * q ^ 2 * P ^ 2 / (40 * q ^ 3 + 1) <
        P ^ 2 / (10 * q) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_pos_of_pos hP]
  have hdefect := row_energy_defect_le_full_error ell (N k)
  have hzeroBudget :
      -2 * (N k : ℝ) ^ 2 / (5 * (10 ^ ell : ℕ)) =
        -4 * ((N k : ℝ) ^ 2 / (10 * (10 ^ ell : ℕ))) := by
    field_simp
    ring
  rw [hzeroBudget] at hdefect
  have hdecStrict :
      (piCylinderCollisionEnergy (ell + 1) (N k) : ℝ) <
        (1 / 2 : ℝ) * piCylinderCollisionEnergy ell (N k) := by
    dsimp [q, P] at hchildTail hparentTail hboundaryBudget
    nlinarith
  have hsplitRaw := energy_decrement_implies_quantitativeSplittingLevel
    ell (N k) (1 / 2 : ℝ) (1 / 100 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hdecStrict.le
  have hsplit :
      QuantitativeSplittingLevel ell (N k)
        (3281 / 7281 : ℝ) (1 / 100) := by
    convert hsplitRaw using 1 <;> norm_num
  exact ⟨hsplit,
    (quantitativeSplittingLevel_iff_rowThreshold
      ell (N k) (1 / 100) (3281 / 7281 : ℝ)).mp hsplit⟩

end DecimalFactorComplexity.AggregateFejerCriterionT64

#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.phase_grid_sum
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.collectedFejerCoefficient_eq
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.norm_collectedFejerCoefficient
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.nonzeroCollectedFejerL1Norm_eq_divisibility_sum
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.nonzeroCollectedFejerL1Norm_le
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.nonzeroCollectedFejerL2SqNorm_eq_divisibility_sum
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.nonzeroCollectedFejerL2SqNorm_le
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.nonzeroCollectedFejerL2Norm_le
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.literal_row_halfOpen_fejer_expansions
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.parent_aggregate_boundary_bound
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.successor_aggregate_boundary_bound
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.smoothedEnergy_eq_collected_expansion
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.smoothedEnergy_eq_zeroMode_add_remainder
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.row_energy_defect_le_full_error
#print axioms DecimalFactorComplexity.AggregateFejerCriterionT64.boundary_and_fourier_imply_literal_t14_row
