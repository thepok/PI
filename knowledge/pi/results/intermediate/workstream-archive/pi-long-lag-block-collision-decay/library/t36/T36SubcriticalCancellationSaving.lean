import TheoryLib.PiLongLagBlockCollisionDecay.T34T34CancellingRepunitIncidence
import TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset
import TheoryLib.PiLongLagBlockCollisionDecay.T31T31CrossBlockAlmostEverywhere

/-!
# T36: source-exponent decomposition of the cancelling sector

Canonical local question: `problems/local/pi-long-lag-block-collision-decay.txt`
(the locally formulated question has no external source URL).
SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

External hypothesis source: Doron Zeilberger and Wadim Zudilin, "The
Irrationality Measure of Pi is at most 7.103205334137...", Moscow Journal of
Combinatorics and Number Theory 9 (2020), 407-419,
DOI `10.2140/moscow.2020.9.407`.  The retained publisher PDF has SHA-256
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
The definition is on PDF page 2 (journal page 407); the displayed
`7.10320533413700172750577342281...` bound is on PDF page 13 (journal page
418).  The source statement itself is not asserted by Lean.

This module imports the machine-checked T34 cancelling-row formalization, but
does not use the unverified T35 note as a premise.  The published
irrationality-measure estimate is represented by the explicit hypothesis
`PublishedEstimate36Fifths`; no declaration asserts that hypothesis,
`ARI_super`, `ARI_cancel`, C2, or C1 for `Real.pi`.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Theory.PiDigits.LongLagBlockCollisionDecay.T36

open Theory.PiDigits.LongLagBlockCollisionDecay.T4
open Theory.PiDigits.LongLagBlockCollisionDecay.T8
open Theory.PiDigits.LongLagBlockCollisionDecay.T12
open Theory.PiDigits.LongLagBlockCollisionDecay.T22
open Theory.PiDigits.LongLagBlockCollisionDecay.T24
open Theory.PiDigits.LongLagBlockCollisionDecay.T29
open Theory.PiDigits.LongLagBlockCollisionDecay.T31
open Theory.PiDigits.LongLagBlockCollisionDecay.T32
open Theory.PiDigits.LongLagBlockCollisionDecay.T34

/-! ## Explicit external source hypothesis and exponent arithmetic -/

/-- The exact eventual exponent `36/5` consequence used from the published
irrationality-measure estimate.  It remains a hypothesis in every theorem
that uses it. -/
def PublishedEstimate36Fifths (Qstar : ℕ) : Prop :=
  1 ≤ Qstar ∧ ∀ d : ℕ, Qstar ≤ d → 0 < d → ∀ p : ℤ,
    1 / (d : ℝ) ^ ((36 : ℝ) / 5) <
      |Real.pi - (p : ℝ) / (d : ℝ)|

/-- T4's source-level formulation below `36/5` supplies a finite onset for
the explicit published estimate. -/
theorem sourceBelow36Fifths_exists_onset
    (hSource : IrrationalityMeasureBelow Real.pi ((36 : ℝ) / 5)) :
    ∃ Qstar : ℕ, PublishedEstimate36Fifths Qstar := by
  rcases hSource with ⟨μ, hμ, hSource⟩
  have hε : 0 < (36 : ℝ) / 5 - μ := sub_pos.mpr hμ
  obtain ⟨Q0, hQ0⟩ := hSource ((36 : ℝ) / 5 - μ) hε
  refine ⟨max 1 Q0, by simp [PublishedEstimate36Fifths], ?_⟩
  intro d hd hd0 p
  have hbound := hQ0 d (le_trans (le_max_right 1 Q0) hd) hd0 p
  convert hbound using 1 <;> ring

/-- Multiplying the published rational-approximation inequality by its
positive denominator gives the exact scaled exponent `31/5`. -/
theorem publishedEstimate_scaledDistance
    {Qstar d : ℕ} (hPublished : PublishedEstimate36Fifths Qstar)
    (hd : Qstar ≤ d) :
    (d : ℝ) ^ (-((31 : ℝ) / 5)) <
      nearestIntegerDistance ((d : ℝ) * Real.pi) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by omega) (hPublished.1.trans hd)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  let p : ℤ := round ((d : ℝ) * Real.pi)
  have hsource := hPublished.2 d hd hd0 p
  have habs : |Real.pi - (p : ℝ) / (d : ℝ)| =
      nearestIntegerDistance ((d : ℝ) * Real.pi) / (d : ℝ) := by
    unfold nearestIntegerDistance
    have hfrac : Real.pi - (p : ℝ) / (d : ℝ) =
        ((d : ℝ) * Real.pi - (p : ℝ)) / (d : ℝ) := by
      field_simp
    rw [hfrac, abs_div, abs_of_pos hdR]
  rw [habs] at hsource
  have hmul := (lt_div_iff₀ hdR).mp hsource
  have hexponent : (1 : ℝ) - (36 / 5 : ℝ) = -(31 / 5 : ℝ) := by norm_num
  calc
    (d : ℝ) ^ (-((31 : ℝ) / 5)) =
        (d : ℝ) ^ ((1 : ℝ) - (36 / 5 : ℝ)) := by rw [hexponent]
    _ = (d : ℝ) ^ (1 : ℝ) / (d : ℝ) ^ ((36 : ℝ) / 5) :=
      Real.rpow_sub hdR _ _
    _ = (1 / (d : ℝ) ^ ((36 : ℝ) / 5)) * (d : ℝ) := by
      rw [Real.rpow_one]
      ring
    _ < nearestIntegerDistance ((d : ℝ) * Real.pi) := hmul

/-- The exact cancelling coefficient is strictly below `10^(v+rho)`. -/
theorem cancellingValue_lt_tenPow_add (v rho : ℕ) (hrho : 0 < rho) :
    cancellingValue v rho < 10 ^ (v + rho) := by
  unfold cancellingValue reducedRepunitFactor
  rw [pow_add]
  have hpow : 0 < 10 ^ v := by positivity
  have hpowrho : 0 < 10 ^ rho := by positivity
  have hsub : 10 ^ rho - 1 < 10 ^ rho := by omega
  exact Nat.mul_lt_mul_of_pos_left hsub hpow

/-- The integer onset, valuation-height cutoff, and their two strict
complements. -/
def PreOnset (Qstar : ℕ) (vr : ℕ × ℕ) : Prop :=
  cancellingValue vr.1 vr.2 < Qstar

def Subcritical (Qstar m : ℕ) (vr : ℕ × ℕ) : Prop :=
  Qstar ≤ cancellingValue vr.1 vr.2 ∧ 31 * (vr.1 + vr.2) ≤ 5 * m

def Supercritical (Qstar m : ℕ) (vr : ℕ × ℕ) : Prop :=
  Qstar ≤ cancellingValue vr.1 vr.2 ∧ 5 * m < 31 * (vr.1 + vr.2)

instance preOnsetDecidable (Qstar : ℕ) : DecidablePred (PreOnset Qstar) :=
  fun vr => inferInstanceAs (Decidable (cancellingValue vr.1 vr.2 < Qstar))

instance subcriticalDecidable (Qstar m : ℕ) :
    DecidablePred (Subcritical Qstar m) :=
  fun vr => inferInstanceAs (Decidable
    (Qstar ≤ cancellingValue vr.1 vr.2 ∧ 31 * (vr.1 + vr.2) ≤ 5 * m))

instance supercriticalDecidable (Qstar m : ℕ) :
    DecidablePred (Supercritical Qstar m) :=
  fun vr => inferInstanceAs (Decidable
    (Qstar ≤ cancellingValue vr.1 vr.2 ∧ 5 * m < 31 * (vr.1 + vr.2)))

theorem sourceExponent_partition (Qstar m : ℕ) (vr : ℕ × ℕ) :
    PreOnset Qstar vr ∨ Subcritical Qstar m vr ∨
      Supercritical Qstar m vr := by
  unfold PreOnset Subcritical Supercritical
  omega

/-- Public statement audit for the six literal T34 cancelling-row domains. -/
theorem six_cancelling_domains_audit
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} {qr : RecordPair} :
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .positiveSameEndpoint v rho z ↔
      qr = (recordOfStartEndpoint true (v + rho) z,
        recordOfStartEndpoint true v z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) ∧
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .positiveSameStart v rho z ↔
      qr = (recordOfStartEndpoint true z v,
        recordOfStartEndpoint true z (v + rho)) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) ∧
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .negativeSameEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false v z,
        recordOfStartEndpoint false (v + rho) z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) ∧
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .negativeSameStart v rho z ↔
      qr = (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint false z v) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) ∧
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .mixedFirstEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false z (v + rho),
        recordOfStartEndpoint true v z) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) ∧
    (qr ∈ cancellingRowDomain μ c Q0 m B
        .mixedSecondEndpoint v rho z ↔
      qr = (recordOfStartEndpoint false v z,
        recordOfStartEndpoint true z (v + rho)) ∧
      0 < rho ∧ qr.1 ∈ blockRecordDomain μ c Q0 m B ∧
        qr.2 ∈ blockRecordDomain μ c Q0 m B) := by
  exact ⟨mem_positiveSameEndpoint_iff, mem_positiveSameStart_iff,
    mem_negativeSameEndpoint_iff, mem_negativeSameStart_iff,
    mem_mixedFirstEndpoint_iff, mem_mixedSecondEndpoint_iff⟩

/-- Public audit of shell zero, every positive shell, and the terminal depth. -/
theorem sourceExponent_shell_endpoint_audit
    (m j : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (InDyadicShell m 0 x ↔
      0 ≤ nearestIntegerDistance x ∧
        nearestIntegerDistance x ≤ ((10 : ℝ) ^ m)⁻¹) ∧
    (j ≠ 0 → (InDyadicShell m j x ↔
      (2 : ℝ) ^ (j - 1) / (10 : ℝ) ^ m < nearestIntegerDistance x ∧
        nearestIntegerDistance x ≤
          min ((2 : ℝ) ^ j / (10 : ℝ) ^ m) (1 / 2))) ∧
    1 ≤ shellDepth m ∧
    10 ^ m ≤ 2 ^ (shellDepth m + 1) ∧
    2 ^ shellDepth m < 10 ^ m := by
  refine ⟨by simp [InDyadicShell], ?_, shellDepth_spec m hm⟩
  intro hj
  simp [InDyadicShell, hj]

/-! ## Literal restricted incidences -/

/-- T34's shell incidence with only an additional predicate on `(v,rho)`.
All canonical blocks, exact width weights, six rows, hidden exponents,
survival conditions, and shell endpoints are unchanged. -/
def restrictedShellIncidence
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (Q0 m N j : ℕ) : ℝ := by
  classical
  exact ((translatedCanonicalBlocks N).map fun B =>
      ∑ vr ∈ repunitParameterDomain N with P vr,
        if InDyadicShell m j
            ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) then
          (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B
        else 0).sum

/-- Literal shell-zero plus endpoint-pinned positive-shell weighted sum. -/
def restrictedWeightedShellIncidence
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (Q0 m N : ℕ) : ℝ :=
  restrictedShellIncidence P Q0 m N 0 +
    ∑ j ∈ Finset.Icc 1 (shellDepth m),
      ((2 : ℝ) ^ j)⁻¹ * restrictedShellIncidence P Q0 m N j

/-- The pre-onset part is finite in coefficient space. -/
def preOnsetIncidence (Q0 Qstar m N : ℕ) : ℝ :=
  by classical exact
    restrictedWeightedShellIncidence (PreOnset Qstar) Q0 m N

/-- The source-controlled low valuation-height part. -/
def subcriticalIncidence (Q0 Qstar m N : ℕ) : ℝ :=
  by classical exact
    restrictedWeightedShellIncidence (Subcritical Qstar m) Q0 m N

/-- The literal `ARI_super(36/5)` remainder. -/
def supercriticalIncidence (Q0 Qstar m N : ℕ) : ℝ :=
  by classical exact
    restrictedWeightedShellIncidence (Supercritical Qstar m) Q0 m N

/-- Exact finite decomposition in each endpoint-pinned shell. -/
theorem shellIncidence_eq_sourceExponentPieces
    (Q0 Qstar m N j : ℕ) :
    shellIncidence 8 1 Q0 m N j =
      restrictedShellIncidence (PreOnset Qstar) Q0 m N j +
      restrictedShellIncidence (Subcritical Qstar m) Q0 m N j +
      restrictedShellIncidence (Supercritical Qstar m) Q0 m N j := by
  classical
  unfold shellIncidence restrictedShellIncidence
  rw [← List.sum_map_add, ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro B hB
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro vr hvr
  rcases sourceExponent_partition Qstar m vr with hp | hl | hs
  · have hnlow : ¬ Subcritical Qstar m vr := by
      intro hlow
      unfold PreOnset at hp
      unfold Subcritical at hlow
      omega
    have hnsuper : ¬ Supercritical Qstar m vr := by
      intro hsuper
      unfold PreOnset at hp
      unfold Supercritical at hsuper
      omega
    simp [hp, hnlow, hnsuper]
  · have hnpre : ¬ PreOnset Qstar vr := by
      intro hpre
      unfold PreOnset at hpre
      unfold Subcritical at hl
      omega
    have hnsuper : ¬ Supercritical Qstar m vr := by
      intro hsuper
      unfold Subcritical at hl
      unfold Supercritical at hsuper
      omega
    simp [hl, hnpre, hnsuper]
  · have hnpre : ¬ PreOnset Qstar vr := by
      intro hpre
      unfold PreOnset at hpre
      unfold Supercritical at hs
      omega
    have hnlow : ¬ Subcritical Qstar m vr := by
      intro hlow
      unfold Subcritical at hlow
      unfold Supercritical at hs
      omega
    simp [hs, hnpre, hnlow]

/-- Exact finite decomposition of T34's full weighted shell incidence. -/
theorem weightedShellIncidence_eq_sourceExponentPieces
    (Q0 Qstar m N : ℕ) :
    weightedShellIncidence 8 1 Q0 m N =
      preOnsetIncidence Q0 Qstar m N +
      subcriticalIncidence Q0 Qstar m N +
      supercriticalIncidence Q0 Qstar m N := by
  classical
  unfold weightedShellIncidence preOnsetIncidence subcriticalIncidence
    supercriticalIncidence restrictedWeightedShellIncidence
  rw [shellIncidence_eq_sourceExponentPieces Q0 Qstar m N 0]
  simp_rw [shellIncidence_eq_sourceExponentPieces Q0 Qstar m N]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-! ## Complement bounds and the exact conditional implication -/

/-- Explicit finite coefficient-space constant.  Its deliberately coarse
factor six corresponds exactly to the six constructors of `CancellingRow`. -/
def finiteOnsetConstant (Qstar : ℕ) : ℝ :=
  6 * ((Finset.range Qstar ×ˢ Finset.range Qstar).filter fun vr =>
    0 < vr.2 ∧ cancellingValue vr.1 vr.2 < Qstar).card

theorem dyadicPartitionFrom_start_gt_base
    {q : ℕ} {js : List ℕ} {B : DyadicBlock}
    (hB : B ∈ dyadicPartitionFrom q js) : q < B.start := by
  induction js generalizing q with
  | nil => simp [dyadicPartitionFrom] at hB
  | cons j js ih =>
      simp only [dyadicPartitionFrom, List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp
      · exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (pow_pos (by omega) j))
          (Nat.le_of_lt (ih hB))

theorem first_blockLength_div_widthWeight_lt_one (j : ℕ) :
    ((DyadicBlock.blockLength ⟨1, j⟩ : ℕ) : ℝ) /
        widthWeight ⟨1, j⟩ < 1 := by
  let L : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hL : 0 < L := by positivity
  have hfinishEq : (((⟨1, j⟩ : DyadicBlock).finish : ℕ) : ℝ) = 1 + L := by
    simp [DyadicBlock.finish, DyadicBlock.blockLength, L]
  have hrad : (0 : ℝ) <
      (((⟨1, j⟩ : DyadicBlock).finish : ℝ) ^ 2 -
        ((⟨1, j⟩ : DyadicBlock).start : ℝ) ^ 2) := by
    rw [hfinishEq]
    norm_num only [Nat.cast_one, one_pow]
    nlinarith
  have hw : 0 < widthWeight (⟨1, j⟩ : DyadicBlock) :=
    Real.sqrt_pos.2 hrad
  have hsquare : widthWeight (⟨1, j⟩ : DyadicBlock) ^ 2 =
      (((⟨1, j⟩ : DyadicBlock).finish : ℝ) ^ 2 -
        ((⟨1, j⟩ : DyadicBlock).start : ℝ) ^ 2) :=
    Real.sq_sqrt hrad.le
  apply (div_lt_one hw).2
  change L < widthWeight (⟨1, j⟩ : DyadicBlock)
  rw [hfinishEq] at hsquare
  norm_num only [Nat.cast_one, one_pow] at hsquare
  nlinarith

theorem tail_blockLength_div_widthWeight_le
    {q : ℕ} (hq : 0 < q) {js : List ℕ} {B : DyadicBlock}
    (hB : B ∈ dyadicPartitionFrom q js) :
    (B.blockLength : ℝ) / widthWeight B ≤
      Real.sqrt (B.blockLength : ℝ) / Real.sqrt (2 * (q : ℝ)) := by
  have hstart : q < B.start := dyadicPartitionFrom_start_gt_base hB
  have hL : (0 : ℝ) < B.blockLength := by
    simp [DyadicBlock.blockLength]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrad : (0 : ℝ) <
      (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := by
    have hfinish : B.start < B.finish := by
      simp [DyadicBlock.finish, DyadicBlock.blockLength]
    have hstart0 : (0 : ℝ) ≤ B.start := by positivity
    have hfinishR : (B.start : ℝ) < B.finish := by exact_mod_cast hfinish
    nlinarith
  have hw : 0 < widthWeight B := Real.sqrt_pos.2 hrad
  have hD : 0 < Real.sqrt (2 * (q : ℝ)) := by positivity
  have hsqrtL : 0 < Real.sqrt (B.blockLength : ℝ) := Real.sqrt_pos.2 hL
  have hwSq : widthWeight B ^ 2 =
      (B.finish : ℝ) ^ 2 - (B.start : ℝ) ^ 2 := Real.sq_sqrt hrad.le
  have hLSq : (Real.sqrt (B.blockLength : ℝ)) ^ 2 = B.blockLength :=
    Real.sq_sqrt hL.le
  have hDSq : (Real.sqrt (2 * (q : ℝ))) ^ 2 = 2 * (q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hwidthLower :
      Real.sqrt (2 * (q : ℝ)) * Real.sqrt (B.blockLength : ℝ) ≤
        widthWeight B := by
    apply (sq_le_sq₀ (by positivity) hw.le).mp
    rw [mul_pow, hDSq, hLSq, hwSq]
    simp only [DyadicBlock.finish]
    push_cast
    have hstartR : (q : ℝ) ≤ B.start := by exact_mod_cast hstart.le
    nlinarith
  rw [div_le_div_iff₀ hw hD]
  calc
    (B.blockLength : ℝ) * Real.sqrt (2 * (q : ℝ)) =
        (Real.sqrt (B.blockLength : ℝ)) ^ 2 *
          Real.sqrt (2 * (q : ℝ)) := by rw [hLSq]
    _ = Real.sqrt (B.blockLength : ℝ) *
          (Real.sqrt (2 * (q : ℝ)) * Real.sqrt (B.blockLength : ℝ)) := by
      ring
    _ ≤ Real.sqrt (B.blockLength : ℝ) * widthWeight B :=
      mul_le_mul_of_nonneg_left hwidthLower (Real.sqrt_nonneg _)

theorem dyadicPartitionFrom_tail_budget_lt_two
    (q : ℕ) (hq : 0 < q) (j : ℕ) (hqj : q = 2 ^ j)
    (js : List ℕ) (hdesc : (j :: js).Pairwise fun a b => b < a) :
    ((dyadicPartitionFrom q js).map fun B =>
      (B.blockLength : ℝ) / widthWeight B).sum < 2 := by
  let blocks := dyadicPartitionFrom q js
  let D : ℝ := Real.sqrt (2 * (q : ℝ))
  have hD : 0 < D := by positivity
  have hpoint :
      (blocks.map fun B => (B.blockLength : ℝ) / widthWeight B).sum ≤
        (blocks.map fun B => Real.sqrt (B.blockLength : ℝ) / D).sum := by
    apply list_sum_map_le_sum_map
    intro B hB
    exact tail_blockLength_div_widthWeight_le hq hB
  have hfactor :
      (blocks.map fun B => Real.sqrt (B.blockLength : ℝ) / D).sum =
        (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum / D := by
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  have hlevels : blocks.map DyadicBlock.level = js :=
    dyadicPartitionFrom_levels q js
  have hsqrtLevels :
      (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum =
        (js.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum := by
    have h := congrArg
      (fun xs : List ℕ =>
        (xs.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum) hlevels
    simpa [DyadicBlock.blockLength, List.map_map] using h
  rw [List.pairwise_cons] at hdesc
  have hgeom := descending_levelSqrtSum_le js hdesc.2
  have hsumlt : dyadicLevelSum js < q := by
    rw [hqj]
    exact dyadicLevelSum_lt_two_pow hdesc.2.nodup hdesc.1
  have hsqrtlt : Real.sqrt (dyadicLevelSum js : ℝ) < Real.sqrt (q : ℝ) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    exact_mod_cast hsumlt
  have hsqrtq : 0 < Real.sqrt (q : ℝ) := by positivity
  have hsqrt2 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hconstant : 1 + Real.sqrt 2 < 2 * Real.sqrt 2 := by linarith
  have hD_eq : D = Real.sqrt 2 * Real.sqrt (q : ℝ) := by
    dsimp [D]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (blocks.map fun B => (B.blockLength : ℝ) / widthWeight B).sum ≤
        (blocks.map fun B => Real.sqrt (B.blockLength : ℝ) / D).sum := hpoint
    _ = (blocks.map fun B => Real.sqrt (B.blockLength : ℝ)).sum / D := hfactor
    _ = (js.map fun k => Real.sqrt ((2 ^ k : ℕ) : ℝ)).sum / D := by
      rw [hsqrtLevels]
    _ ≤ ((1 + Real.sqrt 2) * Real.sqrt (dyadicLevelSum js : ℝ)) / D :=
      div_le_div_of_nonneg_right hgeom hD.le
    _ < ((1 + Real.sqrt 2) * Real.sqrt (q : ℝ)) / D := by
      exact div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hsqrtlt (by positivity)) hD
    _ < (2 * Real.sqrt 2 * Real.sqrt (q : ℝ)) / D := by
      exact div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_right hconstant hsqrtq) hD
    _ = 2 := by rw [hD_eq]; field_simp

/-- Every canonical block has the literal T29 width, and the normalized total
length budget is uniformly below three. -/
theorem canonical_blockLength_weight_budget (N : ℕ) :
    ((translatedCanonicalBlocks N).map fun B =>
      (B.blockLength : ℝ) / widthWeight B).sum < 3 := by
  let levels := (N - 1).bitIndices.reverse
  have hdesc : levels.Pairwise fun j k => k < j :=
    Nat.bitIndices_sorted.pairwise.reverse
  rw [translatedCanonicalBlocks, canonicalDyadicPartition]
  change ((dyadicPartitionFrom 0 levels).map fun B =>
    (B.blockLength : ℝ) / widthWeight B).sum < 3
  cases hlevels : levels with
  | nil => simp [dyadicPartitionFrom]
  | cons j js =>
      have hdesc' : (j :: js).Pairwise fun a b => b < a := by
        simpa [hlevels] using hdesc
      simp only [dyadicPartitionFrom, List.map_cons, List.sum_cons, Nat.zero_add]
      have hfirst := first_blockLength_div_widthWeight_lt_one j
      have htail := dyadicPartitionFrom_tail_budget_lt_two
        (2 ^ j) (pow_pos (by omega) j) j rfl js hdesc'
      linarith

theorem inDyadicShell_unique
    {m i j : ℕ} {x : ℝ}
    (hi : InDyadicShell m i x) (hj : InDyadicShell m j x) : i = j := by
  by_contra hij
  wlog hijlt : i < j generalizing i j
  · exact this hj hi (Ne.symm hij) (by omega)
  have hjpos : j ≠ 0 := by omega
  by_cases hi0 : i = 0
  · rw [InDyadicShell, if_pos hi0] at hi
    rw [InDyadicShell, if_neg hjpos] at hj
    have hp : (1 : ℝ) ≤ 2 ^ (j - 1) := one_le_pow₀ (by norm_num)
    have hH : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
    have hle : ((10 : ℝ) ^ m)⁻¹ ≤
        (2 : ℝ) ^ (j - 1) / (10 : ℝ) ^ m := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right hp hH.le
    linarith
  · rw [InDyadicShell, if_neg hi0] at hi
    rw [InDyadicShell, if_neg hjpos] at hj
    have hexp : i ≤ j - 1 := by omega
    have hp : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (j - 1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hH : (0 : ℝ) < (10 : ℝ) ^ m := by positivity
    have hdiv : (2 : ℝ) ^ i / (10 : ℝ) ^ m ≤
        (2 : ℝ) ^ (j - 1) / (10 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hp hH.le
    exact (not_lt_of_ge (hi.2.trans (min_le_left _ _)))
      (hdiv.trans_lt hj.1)

theorem shellWeight_le_one (m : ℕ) (x : ℝ) (hm : 1 ≤ m) :
    shellWeight m x ≤ 1 := by
  classical
  obtain ⟨hidxRange, hidxShell⟩ := shellIndex_mem m hm x
  by_cases hidx0 : shellIndex m x = 0
  · have hzero : InDyadicShell m 0 x := by simpa [hidx0] using hidxShell
    have hpositive : ∀ j ∈ Finset.Icc 1 (shellDepth m),
        ¬ InDyadicShell m j x := by
      intro j hj hjshell
      have heq : (0 : ℕ) = j := inDyadicShell_unique hzero hjshell
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      exact (Nat.ne_of_gt hj1) heq.symm
    unfold shellWeight
    rw [if_pos hzero]
    have hsumzero :
        (∑ j ∈ Finset.Icc 1 (shellDepth m),
          if InDyadicShell m j x then ((2 : ℝ) ^ j)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (hpositive j hj)]
    rw [hsumzero]
    norm_num
  · have hidxMem : shellIndex m x ∈ Finset.Icc 1 (shellDepth m) :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hidx0,
        (Finset.mem_Icc.mp hidxRange).2⟩
    have hzero : ¬ InDyadicShell m 0 x := by
      intro h
      exact hidx0 (inDyadicShell_unique hidxShell h)
    have hother : ∀ j ∈ Finset.Icc 1 (shellDepth m),
        j ≠ shellIndex m x → ¬ InDyadicShell m j x := by
      intro j hj hne hshell
      exact hne (inDyadicShell_unique hshell hidxShell)
    unfold shellWeight
    rw [if_neg hzero, zero_add]
    rw [Finset.sum_eq_single (shellIndex m x)]
    · simp only [hidxShell, if_true]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
    · intro j hj hne
      simp [hother j hj hne]
    · exact fun h => (h hidxMem).elim

theorem restrictedWeightedShellIncidence_eq_direct
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (Q0 m N : ℕ) :
    restrictedWeightedShellIncidence P Q0 m N =
      ((translatedCanonicalBlocks N).map fun B =>
        ∑ vr ∈ repunitParameterDomain N with P vr,
          (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
              widthWeight B *
            shellWeight m
              ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum := by
  classical
  unfold restrictedWeightedShellIncidence restrictedShellIncidence shellWeight
  simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_comm
    (s := (repunitParameterDomain N).filter P)
    (t := Finset.Icc 1 (shellDepth m))]
  rw [List.sum_map_add]
  apply congrArg₂ (· + ·)
  · rfl
  · rw [list_sum_finset_sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro B hB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vr hvr
    by_cases hs : InDyadicShell m j
        ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)
    · simp [hs]
      ring
    · simp [hs]

theorem cancellingRowDomain_block_sum_le_one
    (Q0 m N v rho z : ℕ) (row : CancellingRow) :
    ((translatedCanonicalBlocks N).map fun B =>
      (cancellingRowDomain 8 1 Q0 m B row v rho z).card).sum ≤ 1 := by
  have aux : ∀ blocks : List DyadicBlock,
      blocks.Nodup →
      (∀ B ∈ blocks, B ∈ translatedCanonicalBlocks N) →
      (blocks.map fun B =>
        (cancellingRowDomain 8 1 Q0 m B row v rho z).card).sum ≤ 1 := by
    intro blocks hnodup hsub
    induction blocks with
    | nil => simp
    | cons B blocks ih =>
        rw [List.nodup_cons] at hnodup
        have hB : B ∈ translatedCanonicalBlocks N := hsub B (by simp)
        have hsubtail : ∀ C ∈ blocks, C ∈ translatedCanonicalBlocks N := by
          intro C hC
          exact hsub C (by simp [hC])
        by_cases hactive : cancellingRowPair row v rho z ∈
            cancellingRowDomain 8 1 Q0 m B row v rho z
        · have htailzero : ∀ C ∈ blocks,
              (cancellingRowDomain 8 1 Q0 m C row v rho z).card = 0 := by
            intro C hC
            apply Finset.card_eq_zero.mpr
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨qr, hqr⟩
            have hqreq := (mem_cancellingRowDomain_iff.mp hqr).1
            subst qr
            have hqrB := (mem_cancellingRowDomain_iff.mp hactive).2.2.1
            have hqrC := (mem_cancellingRowDomain_iff.mp hqr).2.2.1
            have heq := canonicalBlock_interval_unique hB (hsubtail C hC)
              (mem_blockRecordDomain_iff.mp hqrB).2.1
              (mem_blockRecordDomain_iff.mp hqrB).2.2
              (mem_blockRecordDomain_iff.mp hqrC).2.1
              (mem_blockRecordDomain_iff.mp hqrC).2.2
            exact hnodup.1 (heq ▸ hC)
          simp only [List.map_cons, List.sum_cons]
          rw [show (cancellingRowDomain 8 1 Q0 m B row v rho z).card = 1 by
            have hsingleton :
                cancellingRowDomain 8 1 Q0 m B row v rho z =
                  {cancellingRowPair row v rho z} := by
              apply Finset.Subset.antisymm
              · intro qr hqr
                exact Finset.mem_singleton.mpr
                  (mem_cancellingRowDomain_iff.mp hqr).1
              · intro qr hqr
                have heq := Finset.mem_singleton.mp hqr
                subst qr
                exact hactive
            rw [hsingleton]
            simp]
          have htailsum : (blocks.map fun C =>
              (cancellingRowDomain 8 1 Q0 m C row v rho z).card).sum = 0 := by
            apply List.sum_eq_zero
            intro n hn
            obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hn
            exact htailzero C hC
          rw [htailsum]
        · have hcardzero :
              (cancellingRowDomain 8 1 Q0 m B row v rho z).card = 0 := by
            apply Finset.card_eq_zero.mpr
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨qr, hqr⟩
            apply hactive
            have heq := (mem_cancellingRowDomain_iff.mp hqr).1
            simpa [heq] using hqr
          simp only [List.map_cons, List.sum_cons, hcardzero, zero_add]
          exact ih hnodup.2 hsubtail
  exact aux (translatedCanonicalBlocks N) (translatedCanonicalBlocks_nodup N)
    (by simp)

theorem list_sum_finset_sum_comm_nat
    {ι A : Type*} [DecidableEq ι]
    (xs : List A) (s : Finset ι) (f : A → ι → ℕ) :
    (xs.map fun a => ∑ i ∈ s, f a i).sum =
      ∑ i ∈ s, (xs.map fun a => f a i).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Finset.sum_add_distrib]

theorem cancellingRow_fintype_card : Fintype.card CancellingRow = 6 := by
  decide

theorem blockRepunitMultiplicity_block_sum_le
    (Q0 m N v rho : ℕ) :
    ((translatedCanonicalBlocks N).map fun B =>
      blockRepunitMultiplicity 8 1 Q0 m N B v rho).sum ≤ 6 * N := by
  simp_rw [blockRepunitMultiplicity]
  rw [list_sum_finset_sum_comm_nat
    (xs := translatedCanonicalBlocks N)
    (s := Finset.range N)
    (f := fun B z => ∑ row : CancellingRow,
      (cancellingRowDomain 8 1 Q0 m B row v rho z).card)]
  calc
    ∑ z ∈ Finset.range N,
        ((translatedCanonicalBlocks N).map fun B =>
          ∑ row : CancellingRow,
            (cancellingRowDomain 8 1 Q0 m B row v rho z).card).sum
        = ∑ z ∈ Finset.range N, ∑ row : CancellingRow,
            ((translatedCanonicalBlocks N).map fun B =>
              (cancellingRowDomain 8 1 Q0 m B row v rho z).card).sum := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [list_sum_finset_sum_comm_nat]
    _ ≤ ∑ _z ∈ Finset.range N, ∑ _row : CancellingRow, 1 := by
          gcongr with z hz row
          exact cancellingRowDomain_block_sum_le_one Q0 m N v rho z row
    _ = 6 * N := by
          simp [cancellingRow_fintype_card]
          omega

theorem preOnset_parameter_mem_finiteRange
    {Qstar N v rho : ℕ}
    (hvr : (v, rho) ∈ repunitParameterDomain N)
    (hpre : PreOnset Qstar (v, rho)) :
    (v, rho) ∈ (Finset.range Qstar ×ˢ Finset.range Qstar).filter fun vr =>
      0 < vr.2 ∧ cancellingValue vr.1 vr.2 < Qstar := by
  have hrho : 0 < rho := (mem_repunitParameterDomain_iff.mp hvr).2.2.1
  change cancellingValue v rho < Qstar at hpre
  have hfactor : 1 ≤ reducedRepunitFactor rho := by
    unfold reducedRepunitFactor
    have hten : 10 ≤ 10 ^ rho := by
      simpa using pow_le_pow_right₀ (a := 10) (by norm_num) hrho
    omega
  have hpowv : 10 ^ v ≤ cancellingValue v rho := by
    unfold cancellingValue
    simpa using Nat.mul_le_mul_left (10 ^ v) hfactor
  have hvpow : v ≤ 10 ^ v := (Nat.lt_pow_self (by norm_num : 1 < 10)).le
  have hrhopow : rho ≤ 10 ^ rho - 1 :=
    Nat.le_sub_one_of_lt (Nat.lt_pow_self (n := rho) (by norm_num : 1 < 10))
  have hfactorle : reducedRepunitFactor rho ≤ cancellingValue v rho := by
    unfold cancellingValue
    have hone : 1 ≤ 10 ^ v := one_le_pow₀ (by norm_num)
    nlinarith
  have hv : v < Qstar := (hvpow.trans hpowv).trans_lt hpre
  have hrhoQ : rho < Qstar :=
    (hrhopow.trans (by simpa [reducedRepunitFactor] using hfactorle)).trans_lt hpre
  simp [hv, hrhoQ, hrho, hpre]

/-- The complete pre-onset incidence is linear in `N`, with an explicit
constant depending only on the published onset. -/
theorem preOnsetIncidence_le
    (Q0 Qstar m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    preOnsetIncidence Q0 Qstar m N ≤
      finiteOnsetConstant Qstar * (N : ℝ) := by
  classical
  let onsetParameters :=
    (Finset.range Qstar ×ˢ Finset.range Qstar).filter fun vr =>
      0 < vr.2 ∧ cancellingValue vr.1 vr.2 < Qstar
  rw [preOnsetIncidence, restrictedWeightedShellIncidence_eq_direct]
  rw [list_sum_finset_sum_comm]
  calc
    ∑ vr ∈ (repunitParameterDomain N).filter (PreOnset Qstar),
        ((translatedCanonicalBlocks N).map fun B =>
          (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
              widthWeight B *
            shellWeight m
              ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum
        ≤ ∑ _vr ∈ (repunitParameterDomain N).filter (PreOnset Qstar),
            (6 * (N : ℝ)) := by
          apply Finset.sum_le_sum
          intro vr hvr
          calc
            ((translatedCanonicalBlocks N).map fun B =>
                (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
                    widthWeight B *
                  shellWeight m
                    ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum
                ≤ ((translatedCanonicalBlocks N).map fun B =>
                    (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ)).sum := by
                  apply List.sum_le_sum
                  intro B hB
                  have hw := canonical_widthWeight_one_le hB
                  have hsw := shellWeight_le_one m
                    ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) hm
                  have hsw0 := shellWeight_nonneg m
                    ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)
                  have hmult : 0 ≤
                      (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) := by
                    positivity
                  have hwpos : 0 < widthWeight B := lt_of_lt_of_le zero_lt_one hw
                  have hdiv :
                      (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
                          widthWeight B ≤
                        (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) := by
                    exact (div_le_iff₀ hwpos).2 (by nlinarith)
                  nlinarith
            _ = (((translatedCanonicalBlocks N).map fun B =>
                    blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2).sum : ℕ) := by
                  simpa [List.map_map, Function.comp_def] using
                    (list_natCast_sum
                      ((translatedCanonicalBlocks N).map fun B =>
                        blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2))
            _ ≤ (6 * (N : ℝ)) := by
                  exact_mod_cast blockRepunitMultiplicity_block_sum_le
                    Q0 m N vr.1 vr.2
    _ = (((repunitParameterDomain N).filter (PreOnset Qstar)).card : ℝ) *
          (6 * (N : ℝ)) := by simp
    _ ≤ (onsetParameters.card : ℝ) * (6 * (N : ℝ)) := by
          have hcard : ((repunitParameterDomain N).filter
              (PreOnset Qstar)).card ≤ onsetParameters.card :=
            Finset.card_le_card (by
              intro vr hvr
              exact preOnset_parameter_mem_finiteRange
                (Finset.mem_filter.mp hvr).1 (Finset.mem_filter.mp hvr).2)
          have hcardR : (((repunitParameterDomain N).filter
              (PreOnset Qstar)).card : ℝ) ≤ onsetParameters.card := by
            exact_mod_cast hcard
          gcongr
    _ = finiteOnsetConstant Qstar * (N : ℝ) := by
          simp only [onsetParameters, finiteOnsetConstant]
          push_cast
          ring

theorem subcritical_height_lt_longLag
    {v rho m : ℕ} (hm : 1 ≤ m) (hcut : 31 * (v + rho) ≤ 5 * m) :
    v + rho < m := by
  omega

/-- Case analysis over the six T34 constructors: below the valuation-height
cutoff, rows 2, 4, 5, and 6 are empty. -/
theorem cancellingRowDomain_eq_empty_of_height_lt
    {μ c : ℝ} {Q0 m : ℕ} {B : DyadicBlock}
    {v rho z : ℕ} (hk : v + rho < m) (row : CancellingRow)
    (hrow : row ≠ .positiveSameEndpoint)
    (hrow' : row ≠ .negativeSameEndpoint) :
    cancellingRowDomain μ c Q0 m B row v rho z = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra hcard
  obtain ⟨qr, hqr⟩ := Finset.card_ne_zero.mp hcard
  have hmem := mem_cancellingRowDomain_iff.mp hqr
  rcases hmem with ⟨rfl, hrho, hq0, hq1⟩
  have hlag0 := (mem_blockRecordDomain_iff.mp hq0).1.1
  have hlag1 := (mem_blockRecordDomain_iff.mp hq1).1.1
  have hlong0 := (mem_blockRecordDomain_iff.mp hq0).1.2.1
  have hlong1 := (mem_blockRecordDomain_iff.mp hq1).1.2.1
  cases row with
  | positiveSameEndpoint => exact hrow rfl
  | negativeSameEndpoint => exact hrow' rfl
  | positiveSameStart =>
      simp only [cancellingRowPair, recordOfStartEndpoint] at hlag0 hlag1 hlong0 hlong1
      have hzv : z ≤ v := by omega
      have hmz : m + z ≤ v := (Nat.le_sub_iff_add_le hzv).mp hlong0
      omega
  | negativeSameStart =>
      simp only [cancellingRowPair, recordOfStartEndpoint] at hlag0 hlag1 hlong0 hlong1
      have hzv : z ≤ v := by omega
      have hmz : m + z ≤ v := (Nat.le_sub_iff_add_le hzv).mp hlong1
      omega
  | mixedFirstEndpoint =>
      simp only [cancellingRowPair, recordOfStartEndpoint] at hlag0 hlag1 hlong0 hlong1
      have hvz : v ≤ z := by omega
      have hzvr : z ≤ v + rho := by omega
      have hmz : m + z ≤ v + rho :=
        (Nat.le_sub_iff_add_le hzvr).mp hlong0
      have hmv : m + v ≤ z := (Nat.le_sub_iff_add_le hvz).mp hlong1
      omega
  | mixedSecondEndpoint =>
      simp only [cancellingRowPair, recordOfStartEndpoint] at hlag0 hlag1 hlong0 hlong1
      have hvz : v ≤ z := by omega
      have hzvr : z ≤ v + rho := by omega
      have hmv : m + v ≤ z := (Nat.le_sub_iff_add_le hvz).mp hlong0
      have hmz : m + z ≤ v + rho :=
        (Nat.le_sub_iff_add_le hzvr).mp hlong1
      omega

/-- The remaining two rows contribute at most twice the literal block length. -/
theorem blockRepunitMultiplicity_le_two_mul_blockLength
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock} {v rho : ℕ}
    (hk : v + rho < m) :
    blockRepunitMultiplicity μ c Q0 m N B v rho ≤ 2 * B.blockLength := by
  classical
  unfold blockRepunitMultiplicity
  calc
    (∑ z ∈ Finset.range N, ∑ row : CancellingRow,
        (cancellingRowDomain μ c Q0 m B row v rho z).card) =
        ∑ z ∈ Finset.range N,
          ((cancellingRowDomain μ c Q0 m B
              .positiveSameEndpoint v rho z).card +
           (cancellingRowDomain μ c Q0 m B
              .negativeSameEndpoint v rho z).card) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Fintype.sum_eq_add_sum_compl CancellingRow.positiveSameEndpoint]
      rw [Finset.sum_eq_add_sum_diff_singleton
        CancellingRow.negativeSameEndpoint _ (by simp)]
      have hempty : ∀ row ∈
          ({CancellingRow.positiveSameEndpoint}ᶜ \
            {CancellingRow.negativeSameEndpoint} : Finset CancellingRow),
          (cancellingRowDomain μ c Q0 m B row v rho z).card = 0 := by
        intro row hrow
        simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton] at hrow
        rw [cancellingRowDomain_eq_empty_of_height_lt hk row hrow.1 hrow.2]
        simp
      rw [Finset.sum_eq_zero hempty]
      simp
    _ ≤ ∑ z ∈ Finset.Ico B.start B.finish, 2 := by
      let f : ℕ → ℕ := fun z =>
        (cancellingRowDomain μ c Q0 m B
          .positiveSameEndpoint v rho z).card +
        (cancellingRowDomain μ c Q0 m B
          .negativeSameEndpoint v rho z).card
      have hcard (row : CancellingRow) (z : ℕ) :
          (cancellingRowDomain μ c Q0 m B row v rho z).card ≤ 1 := by
        have hsubset : cancellingRowDomain μ c Q0 m B row v rho z ⊆
            ({cancellingRowPair row v rho z} : Finset RecordPair) :=
          Finset.filter_subset _ _
        simpa using Finset.card_le_card hsubset
      have hsupport : ∀ z, f z ≠ 0 → z ∈ Finset.Ico B.start B.finish := by
        intro z hz
        have hcases :
            (cancellingRowDomain μ c Q0 m B
              .positiveSameEndpoint v rho z).card ≠ 0 ∨
            (cancellingRowDomain μ c Q0 m B
              .negativeSameEndpoint v rho z).card ≠ 0 := by
          dsimp [f] at hz
          omega
        rcases hcases with hpos | hneg
        · obtain ⟨qr, hqr⟩ := Finset.card_ne_zero.mp hpos
          have hmemb := mem_positiveSameEndpoint_iff.mp hqr
          rcases hmemb with ⟨rfl, hrho, hq0, hq1⟩
          have hblock := (mem_blockRecordDomain_iff.mp hq0).2
          have hlag := (mem_blockRecordDomain_iff.mp hq0).1.1
          have hkz : v + rho ≤ z := by
            simp only [recordOfStartEndpoint] at hlag
            omega
          have hend : frequencyEndpoint
              (recordOfStartEndpoint true (v + rho) z).2 = z := by
            simp only [frequencyEndpoint, recordOfStartEndpoint]
            omega
          rw [hend] at hblock
          exact Finset.mem_Ico.mpr hblock
        · obtain ⟨qr, hqr⟩ := Finset.card_ne_zero.mp hneg
          have hmemb := mem_negativeSameEndpoint_iff.mp hqr
          rcases hmemb with ⟨rfl, hrho, hq0, hq1⟩
          have hblock := (mem_blockRecordDomain_iff.mp hq0).2
          have hlag := (mem_blockRecordDomain_iff.mp hq0).1.1
          have hvz : v ≤ z := by
            simp only [recordOfStartEndpoint] at hlag
            omega
          have hend : frequencyEndpoint
              (recordOfStartEndpoint false v z).2 = z := by
            simp only [frequencyEndpoint, recordOfStartEndpoint]
            omega
          rw [hend] at hblock
          exact Finset.mem_Ico.mpr hblock
      calc
        (∑ z ∈ Finset.range N,
            ((cancellingRowDomain μ c Q0 m B
                .positiveSameEndpoint v rho z).card +
             (cancellingRowDomain μ c Q0 m B
                .negativeSameEndpoint v rho z).card)) =
            ∑ z ∈ Finset.range N with z ∈ Finset.Ico B.start B.finish, f z := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hzi : z ∈ Finset.Ico B.start B.finish
          · simp [f, hzi]
          · have hf : f z = 0 := by
              by_contra hf
              exact hzi (hsupport z hf)
            simp [f, hzi, hf]
        _ ≤ ∑ z ∈ Finset.Ico B.start B.finish, f z :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => (Finset.mem_filter.mp hz).2)
            (fun _ _ _ => by omega)
        _ ≤ ∑ _z ∈ Finset.Ico B.start B.finish, 2 := by
          apply Finset.sum_le_sum
          intro z hz
          dsimp [f]
          have hp := hcard CancellingRow.positiveSameEndpoint z
          have hn := hcard CancellingRow.negativeSameEndpoint z
          omega
    _ = 2 * B.blockLength := by
      simp [DyadicBlock.finish]
      ring

theorem blockRepunitMultiplicity_weighted_sum_lt_six
    {μ c : ℝ} {Q0 m N : ℕ} {v rho : ℕ} (hk : v + rho < m) :
    ((translatedCanonicalBlocks N).map fun B =>
      (blockRepunitMultiplicity μ c Q0 m N B v rho : ℝ) /
        widthWeight B).sum < 6 := by
  calc
    ((translatedCanonicalBlocks N).map fun B =>
      (blockRepunitMultiplicity μ c Q0 m N B v rho : ℝ) /
        widthWeight B).sum ≤
        ((translatedCanonicalBlocks N).map fun B =>
          2 * ((B.blockLength : ℝ) / widthWeight B)).sum := by
      apply list_sum_map_le_sum_map
      intro B hB
      have hw := canonical_widthWeight_pos hB
      have hmult := blockRepunitMultiplicity_le_two_mul_blockLength
        (μ := μ) (c := c) (Q0 := Q0) (N := N) (B := B) hk
      have hmultR : (blockRepunitMultiplicity μ c Q0 m N B v rho : ℝ) ≤
          2 * (B.blockLength : ℝ) := by exact_mod_cast hmult
      calc
        (blockRepunitMultiplicity μ c Q0 m N B v rho : ℝ) /
            widthWeight B ≤ (2 * (B.blockLength : ℝ)) / widthWeight B :=
          div_le_div_of_nonneg_right hmultR hw.le
        _ = 2 * ((B.blockLength : ℝ) / widthWeight B) := by ring
    _ = 2 * ((translatedCanonicalBlocks N).map fun B =>
          (B.blockLength : ℝ) / widthWeight B).sum := by
      rw [List.sum_map_mul_left]
    _ < 6 := by
      have hbudget := canonical_blockLength_weight_budget N
      linarith

theorem shellWeight_eq_shellIndex (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    shellWeight m x =
      if shellIndex m x = 0 then 1 else ((2 : ℝ) ^ shellIndex m x)⁻¹ := by
  classical
  obtain ⟨hindex, hshell⟩ := shellIndex_mem m hm x
  by_cases hi0 : shellIndex m x = 0
  · rw [if_pos hi0]
    unfold shellWeight
    rw [if_pos (by simpa [hi0] using hshell)]
    have hsumzero : (∑ j ∈ Finset.Icc 1 (shellDepth m),
        if InDyadicShell m j x then ((2 : ℝ) ^ j)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hjShell
      have heq := inDyadicShell_unique hshell hjShell
      have hjone := (Finset.mem_Icc.mp hj).1
      omega
    rw [hsumzero]
    norm_num
  · rw [if_neg hi0]
    unfold shellWeight
    have hzero : ¬ InDyadicShell m 0 x := by
      intro hzeroShell
      exact hi0 (inDyadicShell_unique hshell hzeroShell)
    rw [if_neg hzero]
    have himem : shellIndex m x ∈ Finset.Icc 1 (shellDepth m) :=
      Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hi0, (Finset.mem_Icc.mp hindex).2⟩
    rw [Finset.sum_eq_single (shellIndex m x)]
    · simp [hshell]
    · intro j hj hne
      rw [if_neg]
      intro hjShell
      exact hne (inDyadicShell_unique hjShell hshell)
    · exact fun hnot => (hnot himem).elim

/-- The explicit published hypothesis yields the normalized `31/5` shell
coefficient on the source-controlled range. -/
theorem shellWeight_lt_published_power
    {Qstar m v rho : ℕ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hm : 1 ≤ m) (hrho : 0 < rho)
    (honset : Qstar ≤ cancellingValue v rho)
    (hcut : 31 * (v + rho) ≤ 5 * m) :
    shellWeight m ((cancellingValue v rho : ℝ) * Real.pi) <
      (cancellingValue v rho : ℝ) ^ ((31 : ℝ) / 5) /
        (10 : ℝ) ^ m := by
  let d := cancellingValue v rho
  let x := (d : ℝ) * Real.pi
  let a : ℝ := (31 : ℝ) / 5
  let H : ℝ := (10 : ℝ) ^ m
  have hdNat : 0 < d := lt_of_lt_of_le (by omega) (hPublished.1.trans honset)
  have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hH : 0 < H := by positivity
  have hdist : (d : ℝ) ^ (-a) < nearestIntegerDistance x := by
    simpa [d, x, a] using publishedEstimate_scaledDistance hPublished honset
  have hdtenNat : d < 10 ^ (v + rho) := by
    simpa [d] using cancellingValue_lt_tenPow_add v rho hrho
  have hdten : (d : ℝ) < (10 : ℝ) ^ (v + rho) := by
    exact_mod_cast hdtenNat
  have hpowFirst : (d : ℝ) ^ a < ((10 : ℝ) ^ (v + rho)) ^ a :=
    Real.rpow_lt_rpow hd.le hdten (by norm_num [a])
  have hpowRewrite : ((10 : ℝ) ^ (v + rho)) ^ a =
      (10 : ℝ) ^ (((v + rho : ℕ) : ℝ) * a) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hexponent : ((v + rho : ℕ) : ℝ) * a ≤ (m : ℝ) := by
    dsimp [a]
    have hcutR : (31 : ℝ) * ((v + rho : ℕ) : ℝ) ≤ 5 * (m : ℝ) := by
      exact_mod_cast hcut
    linarith
  have hpowLast : (10 : ℝ) ^ (((v + rho : ℕ) : ℝ) * a) ≤ H := by
    dsimp [H]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hpow : (d : ℝ) ^ a < H := by
    calc
      (d : ℝ) ^ a < ((10 : ℝ) ^ (v + rho)) ^ a := hpowFirst
      _ = (10 : ℝ) ^ (((v + rho : ℕ) : ℝ) * a) := hpowRewrite
      _ ≤ H := hpowLast
  obtain ⟨hindexRange, hindexShell⟩ := shellIndex_mem m hm x
  have hi0 : shellIndex m x ≠ 0 := by
    intro hi0
    rw [hi0, InDyadicShell, if_pos rfl] at hindexShell
    have hdpow : 0 < (d : ℝ) ^ a := Real.rpow_pos_of_pos hd _
    have hinv : H⁻¹ < ((d : ℝ) ^ a)⁻¹ :=
      (inv_lt_inv₀ hH hdpow).2 hpow
    have hdist' : ((d : ℝ) ^ a)⁻¹ < nearestIntegerDistance x := by
      rw [← Real.rpow_neg hd.le]
      exact hdist
    linarith
  rw [shellWeight_eq_shellIndex m hm x, if_neg hi0]
  rw [InDyadicShell, if_neg hi0] at hindexShell
  have hupper : nearestIntegerDistance x ≤
      (2 : ℝ) ^ shellIndex m x / H :=
    hindexShell.2.trans (min_le_left _ _)
  have hdpow : 0 < (d : ℝ) ^ a := Real.rpow_pos_of_pos hd _
  have htwo : 0 < (2 : ℝ) ^ shellIndex m x := by positivity
  have hsource : ((d : ℝ) ^ a)⁻¹ <
      (2 : ℝ) ^ shellIndex m x / H := by
    have hdist' : ((d : ℝ) ^ a)⁻¹ < nearestIntegerDistance x := by
      rw [← Real.rpow_neg hd.le]
      exact hdist
    exact hdist'.trans_le hupper
  have hrecip : H / (2 : ℝ) ^ shellIndex m x < (d : ℝ) ^ a := by
    have hrhs : 0 < (2 : ℝ) ^ shellIndex m x / H := by positivity
    have hainv : 0 < ((d : ℝ) ^ a)⁻¹ := by positivity
    have hinv := (inv_lt_inv₀ hrhs hainv).2 hsource
    field_simp [ne_of_gt hH, ne_of_gt htwo, ne_of_gt hdpow] at hinv ⊢
    exact hinv
  have hdiv := div_lt_div_of_pos_right hrecip hH
  field_simp [ne_of_gt hH, ne_of_gt htwo] at hdiv ⊢
  exact hdiv

theorem sum_Icc_one_half_reverse (L : ℕ) :
    (∑ rho ∈ Finset.Icc 1 L, ((1 : ℝ) / 2) ^ (L - rho)) =
      ∑ u ∈ Finset.range L, ((1 : ℝ) / 2) ^ u := by
  classical
  apply Finset.sum_bij (fun rho _ => L - rho)
  · intro rho hrho
    rw [Finset.mem_range]
    have h := Finset.mem_Icc.mp hrho
    omega
  · intro rho₁ h₁ rho₂ h₂ heq
    have hh₁ := Finset.mem_Icc.mp h₁
    have hh₂ := Finset.mem_Icc.mp h₂
    omega
  · intro u hu
    have hu' := Finset.mem_range.mp hu
    refine ⟨L - u, Finset.mem_Icc.mpr ?_, ?_⟩
    · omega
    · omega
  · intro rho hrho
    rfl

theorem published_power_div_lt_half_pow_gap
    {m v rho : ℕ} (hrho : 0 < rho)
    (hcut : 31 * (v + rho) ≤ 5 * m) :
    (cancellingValue v rho : ℝ) ^ ((31 : ℝ) / 5) /
        (10 : ℝ) ^ m <
      ((1 : ℝ) / 2) ^ (5 * m / 31 - (v + rho)) := by
  let k := v + rho
  let T := 5 * m / 31
  let a : ℝ := (31 : ℝ) / 5
  let R : ℝ := (10 : ℝ) ^ a
  have hkT : k ≤ T := by
    dsimp [k, T]
    omega
  have hRTexp : 31 * T ≤ 5 * m := by
    dsimp [T]
    omega
  have hRpos : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRtwo : 2 ≤ R := by
    have ha : (1 : ℝ) ≤ a := by norm_num [a]
    have hten : (10 : ℝ) ^ (1 : ℝ) ≤ R :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    rw [Real.rpow_one] at hten
    linarith
  have hdlt : cancellingValue v rho < 10 ^ k := by
    simpa [k] using cancellingValue_lt_tenPow_add v rho hrho
  have hdltR : (cancellingValue v rho : ℝ) < (10 : ℝ) ^ k := by
    exact_mod_cast hdlt
  have hdposNat : 0 < cancellingValue v rho := by
    unfold cancellingValue reducedRepunitFactor
    apply Nat.mul_pos (by positivity)
    have hp : 1 < 10 ^ rho := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hdpos : (0 : ℝ) < cancellingValue v rho := by exact_mod_cast hdposNat
  have hdk : (cancellingValue v rho : ℝ) ^ a < R ^ k := by
    calc
      (cancellingValue v rho : ℝ) ^ a < ((10 : ℝ) ^ k) ^ a :=
        Real.rpow_lt_rpow hdpos.le hdltR (by norm_num [a])
      _ = R ^ k := by
        calc
          ((10 : ℝ) ^ k) ^ a = (10 : ℝ) ^ ((k : ℝ) * a) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10) _ _).symm
          _ = (10 : ℝ) ^ (a * (k : ℝ)) := by ring
          _ = R ^ k := by
            dsimp [R]
            rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
  have hRT : R ^ T ≤ (10 : ℝ) ^ m := by
    have hexp : ((T : ℕ) : ℝ) * a ≤ (m : ℝ) := by
      have hR : (31 : ℝ) * (T : ℝ) ≤ 5 * (m : ℝ) := by
        exact_mod_cast hRTexp
      dsimp [a]
      linarith
    calc
      R ^ T = (10 : ℝ) ^ ((T : ℝ) * a) := by
        dsimp [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        congr 1
        ring
      _ ≤ (10 : ℝ) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (10 : ℝ) ^ m := Real.rpow_natCast _ _
  have hgap : R ^ k / R ^ T ≤ ((1 : ℝ) / 2) ^ (T - k) := by
    have hpowtwo : (2 : ℝ) ^ (T - k) ≤ R ^ (T - k) :=
      (pow_le_pow_left₀ (by norm_num) hRtwo) _
    have hsplit : R ^ T = R ^ k * R ^ (T - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkT]
    rw [hsplit]
    calc
      R ^ k / (R ^ k * R ^ (T - k)) = 1 / R ^ (T - k) := by
        field_simp [ne_of_gt (pow_pos hRpos k)]
      _ ≤ 1 / (2 : ℝ) ^ (T - k) :=
        one_div_le_one_div_of_le (pow_pos (by norm_num) _) hpowtwo
      _ = ((1 : ℝ) / 2) ^ (T - k) := by rw [div_pow]; norm_num
  calc
    (cancellingValue v rho : ℝ) ^ ((31 : ℝ) / 5) / (10 : ℝ) ^ m =
        (cancellingValue v rho : ℝ) ^ a / (10 : ℝ) ^ m := by rfl
    _ < R ^ k / (10 : ℝ) ^ m :=
      div_lt_div_of_pos_right hdk (by positivity)
    _ ≤ R ^ k / R ^ T :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hRpos _) hRT
    _ ≤ ((1 : ℝ) / 2) ^ (T - k) := hgap
    _ = ((1 : ℝ) / 2) ^ (5 * m / 31 - (v + rho)) := by rfl

theorem half_pow_gap_pair_sum_le (T : ℕ) :
    (∑ vr ∈ ((Finset.range T ×ˢ Finset.range (T + 1)).filter fun vr =>
        0 < vr.2 ∧ vr.1 + vr.2 ≤ T),
      ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2))) ≤ 2 * (T : ℝ) := by
  classical
  calc
    (∑ vr ∈ ((Finset.range T ×ˢ Finset.range (T + 1)).filter fun vr =>
        0 < vr.2 ∧ vr.1 + vr.2 ≤ T),
      ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2))) =
        ∑ v ∈ Finset.range T, ∑ rho ∈ Finset.Icc 1 (T - v),
          ((1 : ℝ) / 2) ^ ((T - v) - rho) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro v hv
      have hvT : v < T := Finset.mem_range.mp hv
      calc
        (∑ rho ∈ Finset.range (T + 1),
          if 0 < rho ∧ v + rho ≤ T then
            ((1 : ℝ) / 2) ^ (T - (v + rho)) else 0) =
            ∑ rho ∈ Finset.Icc 1 (T - v),
              ((1 : ℝ) / 2) ^ (T - (v + rho)) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext rho
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
            omega
          · intro rho hrho
            rfl
        _ = ∑ rho ∈ Finset.Icc 1 (T - v),
              ((1 : ℝ) / 2) ^ ((T - v) - rho) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          congr 1
          omega
    _ ≤ ∑ _v ∈ Finset.range T, 2 := by
      apply Finset.sum_le_sum
      intro v hv
      rw [sum_Icc_one_half_reverse]
      exact sum_geometric_two_le (T - v)
    _ = 2 * (T : ℝ) := by simp; ring

theorem canonical_blockRecordDomain_eq_empty_of_finish_le_m
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) (hNm : N ≤ m) :
    blockRecordDomain μ c Q0 m B = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra hcard
  obtain ⟨q, hq⟩ := Finset.card_ne_zero.mp hcard
  have hmemb := mem_blockRecordDomain_iff.mp hq
  have hfinish := canonical_finish_le hB
  have hlag := hmemb.1.2.1
  have hendpoint := hmemb.2.2
  have hend : q.2.1 ≤ frequencyEndpoint q.2 := by
    simp [frequencyEndpoint]
  omega

theorem blockRepunitMultiplicity_eq_zero_of_N_le_m
    {μ c : ℝ} {Q0 m N : ℕ} {B : DyadicBlock}
    (hB : B ∈ translatedCanonicalBlocks N) (hNm : N ≤ m)
    (v rho : ℕ) :
    blockRepunitMultiplicity μ c Q0 m N B v rho = 0 := by
  classical
  unfold blockRepunitMultiplicity
  apply Finset.sum_eq_zero
  intro z hz
  apply Fintype.sum_eq_zero
  intro row
  have hempty := canonical_blockRecordDomain_eq_empty_of_finish_le_m
    (μ := μ) (c := c) (Q0 := Q0) hB hNm
  have hrowempty : cancellingRowDomain μ c Q0 m B row v rho z = ∅ := by
    unfold cancellingRowDomain
    simp [hempty]
  rw [hrowempty]
  simp

theorem subcriticalIncidence_eq_zero_of_N_le_m
    {Q0 Qstar m N : ℕ} (hNm : N ≤ m) :
    subcriticalIncidence Q0 Qstar m N = 0 := by
  classical
  rw [subcriticalIncidence, restrictedWeightedShellIncidence_eq_direct]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨B, hB, rfl⟩ := hx
  apply Finset.sum_eq_zero
  intro vr hvr
  rw [blockRepunitMultiplicity_eq_zero_of_N_le_m hB hNm]
  norm_num

/-- The source-controlled subcritical incidence is uniformly `O(N)`.
The numerical constant is intentionally coarse; the strict cutoff
`31(v+rho) <= 5m` and all literal T34 domains remain in the theorem type. -/
theorem subcriticalIncidence_le
    {Q0 Qstar m N : ℕ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hm : 1 ≤ m) (hN : 1 ≤ N) :
    subcriticalIncidence Q0 Qstar m N ≤ 12 * (N : ℝ) := by
  classical
  by_cases hNm : N ≤ m
  · rw [subcriticalIncidence_eq_zero_of_N_le_m hNm]
    positivity
  · have hmN : m < N := by omega
    let T := 5 * m / 31
    let S := (repunitParameterDomain N).filter (Subcritical Qstar m)
    let U := ((Finset.range T ×ˢ Finset.range (T + 1)).filter fun vr =>
      0 < vr.2 ∧ vr.1 + vr.2 ≤ T)
    rw [subcriticalIncidence, restrictedWeightedShellIncidence_eq_direct]
    change ((translatedCanonicalBlocks N).map fun B =>
      ∑ vr ∈ S,
        (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
            widthWeight B *
          shellWeight m
            ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)).sum ≤ _
    rw [list_sum_finset_sum_comm]
    simp_rw [List.sum_map_mul_right]
    calc
      (∑ vr ∈ S,
          ((translatedCanonicalBlocks N).map fun B =>
            (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
              widthWeight B).sum *
            shellWeight m
              ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi)) ≤
          ∑ vr ∈ S, 6 *
            ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2)) := by
        apply Finset.sum_le_sum
        intro vr hvr
        have hs := (Finset.mem_filter.mp hvr).2
        have hdomain := (Finset.mem_filter.mp hvr).1
        have hrho := (mem_repunitParameterDomain_iff.mp hdomain).2.2.1
        have hk := subcritical_height_lt_longLag hm hs.2
        have hW := blockRepunitMultiplicity_weighted_sum_lt_six
          (μ := (8 : ℝ)) (c := (1 : ℝ)) (Q0 := Q0) (N := N) hk
        have htheta := shellWeight_lt_published_power
          hPublished hm hrho hs.1 hs.2
        have hpower := published_power_div_lt_half_pow_gap hrho hs.2
        have hthetaHalf : shellWeight m
            ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) <
            ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2)) :=
          htheta.trans hpower
        calc
          ((translatedCanonicalBlocks N).map fun B =>
              (blockRepunitMultiplicity 8 1 Q0 m N B vr.1 vr.2 : ℝ) /
                widthWeight B).sum *
              shellWeight m
                ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) ≤
              6 * shellWeight m
                ((cancellingValue vr.1 vr.2 : ℝ) * Real.pi) :=
            mul_le_mul_of_nonneg_right hW.le (shellWeight_nonneg _ _)
          _ ≤ 6 * ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2)) := by
            linarith
      _ ≤ ∑ vr ∈ U, 6 *
            ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro vr hvr
          have hs := (Finset.mem_filter.mp hvr).2
          have hdomain := (Finset.mem_filter.mp hvr).1
          have hd := mem_repunitParameterDomain_iff.mp hdomain
          have hkT : vr.1 + vr.2 ≤ T := by
            dsimp [T]
            exact (Nat.le_div_iff_mul_le (by omega)).2 (by
              simpa [mul_comm] using hs.2)
          simp only [U, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, hd.2.2.1, hkT⟩
        · intro vr hU hnot
          positivity
      _ = 6 * (∑ vr ∈ U,
            ((1 : ℝ) / 2) ^ (T - (vr.1 + vr.2))) := by
        rw [Finset.mul_sum]
      _ ≤ 6 * (2 * (T : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact half_pow_gap_pair_sum_le T
      _ ≤ 12 * (N : ℝ) := by
        have hTN : T ≤ N := by
          dsimp [T]
          omega
        have hTNR : (T : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTN
        nlinarith

/-- `ARI_super(36/5)` at fixed exponent and constant, with all shell endpoints,
weights, ranges, onset constants, and six-row multiplicities exposed through
`supercriticalIncidence`. -/
def ARI_superAt (Q0 Qstar : ℕ) (s C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
    supercriticalIncidence Q0 Qstar m N ≤
      C * ((N : ℝ) + (N : ℝ) ^ 2 *
        (10 : ℝ) ^ (-s * (m : ℝ)))

/-- The literal quantified `ARI_super(36/5)` remainder.  This proposition is
defined but is not asserted for any onset. -/
def ARI_super (Q0 Qstar : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 → ∃ C : ℝ, ARI_superAt Q0 Qstar s C

/-- Quantifier and literal-shell audit for `ARI_super(36/5)`.  The filter
displays the exact source onset and strict valuation-height complement. -/
theorem ARI_super_iff_quantifiers (Q0 Qstar : ℕ) :
    ARI_super Q0 Qstar ↔
      ∀ s : ℝ, 0 < s → s < 1 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          (restrictedShellIncidence
              (fun vr => Qstar ≤ cancellingValue vr.1 vr.2 ∧
                5 * m < 31 * (vr.1 + vr.2)) Q0 m N 0 +
            ∑ j ∈ Finset.Icc 1 (shellDepth m),
              ((2 : ℝ) ^ j)⁻¹ * restrictedShellIncidence
                (fun vr => Qstar ≤ cancellingValue vr.1 vr.2 ∧
                  5 * m < 31 * (vr.1 + vr.2)) Q0 m N j) ≤
            C * ((N : ℝ) + (N : ℝ) ^ 2 *
              (10 : ℝ) ^ (-s * (m : ℝ))) := by
  rfl

/-- Fixed-constant conversion.  The published estimate is still an explicit
hypothesis, and the output is exactly T34's `ARI_cancelAt`. -/
theorem ARI_superAt_implies_ARI_cancelAt
    {Q0 Qstar : ℕ} {s C : ℝ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_superAt Q0 Qstar s C) :
    ARI_cancelAt Q0 s (C + finiteOnsetConstant Qstar + 12) := by
  have hfin : 0 ≤ finiteOnsetConstant Qstar := by
    unfold finiteOnsetConstant
    positivity
  refine ⟨by nlinarith [hSuper.1], ?_⟩
  intro m N hm hN
  rw [weightedShellIncidence_eq_sourceExponentPieces Q0 Qstar m N]
  have hpre := preOnsetIncidence_le Q0 Qstar m N hm hN
  have hlow := subcriticalIncidence_le (Q0 := Q0) hPublished hm hN
  have hsuper := hSuper.2 m N hm hN
  have htail : 0 ≤ (N : ℝ) ^ 2 *
      (10 : ℝ) ^ (-s * (m : ℝ)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have htargetNonneg : 0 ≤ (N : ℝ) + (N : ℝ) ^ 2 *
      (10 : ℝ) ^ (-s * (m : ℝ)) := add_nonneg (by positivity) htail
  have hNtarget : (N : ℝ) ≤ (N : ℝ) + (N : ℝ) ^ 2 *
      (10 : ℝ) ^ (-s * (m : ℝ)) := le_add_of_nonneg_right htail
  calc
    preOnsetIncidence Q0 Qstar m N +
          subcriticalIncidence Q0 Qstar m N +
          supercriticalIncidence Q0 Qstar m N ≤
        finiteOnsetConstant Qstar * (N : ℝ) + 12 * (N : ℝ) +
          C * ((N : ℝ) + (N : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ))) := by linarith
    _ ≤ (C + finiteOnsetConstant Qstar + 12) *
        ((N : ℝ) + (N : ℝ) ^ 2 *
          (10 : ℝ) ^ (-s * (m : ℝ))) := by
      nlinarith [hSuper.1, show 0 ≤ finiteOnsetConstant Qstar by positivity]
    _ = (C + finiteOnsetConstant Qstar + 12) *
        scaleMatchedTarget s m N := by rfl

/-- Exact terminal implication required by T36.  It proves only the
conditional `ARI_super(36/5) -> ARI_cancel` reduction. -/
theorem ARI_super_implies_ARI_cancel
    {Q0 Qstar : ℕ}
    (hPublished : PublishedEstimate36Fifths Qstar)
    (hSuper : ARI_super Q0 Qstar) :
    ARI_cancel Q0 := by
  intro s hs hs1
  obtain ⟨C, hC⟩ := hSuper s hs hs1
  exact ⟨C + finiteOnsetConstant Qstar + 12,
    ARI_superAt_implies_ARI_cancelAt hPublished hC⟩

end Theory.PiDigits.LongLagBlockCollisionDecay.T36

#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.sourceBelow36Fifths_exists_onset
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.publishedEstimate_scaledDistance
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.cancellingValue_lt_tenPow_add
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.six_cancelling_domains_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.sourceExponent_shell_endpoint_audit
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.weightedShellIncidence_eq_sourceExponentPieces
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.canonical_blockLength_weight_budget
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.preOnsetIncidence_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.cancellingRowDomain_eq_empty_of_height_lt
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.blockRepunitMultiplicity_weighted_sum_lt_six
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.shellWeight_lt_published_power
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.published_power_div_lt_half_pow_gap
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.subcriticalIncidence_le
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.ARI_super_iff_quantifiers
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.ARI_superAt_implies_ARI_cancelAt
#print axioms Theory.PiDigits.LongLagBlockCollisionDecay.T36.ARI_super_implies_ARI_cancel
