import TheoryLib.PiQuantitativeBlockHitting.T20T20DigitChangeFourierDefect
import TheoryLib.PiDigits.T11PiDigitFactorComplexity
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# T23: distinct decimal factors force a natural-scale Fourier defect

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

The finite lemmas below isolate the robust part of the first-occurrence idea:
points in pairwise distinct decimal cells have many nonadjacent cell pairs,
and averaging the exact all-pairs cosine energy over one complete frequency
block detects those pairs.  The eventual specialization to pi is much weaker
than the cancellation hypothesis in T19: it produces a defect at one
frequency, at a prefix whose first-occurrence cutoff is uncontrolled.
-/

noncomputable section

open Finset Set

namespace Theory.PiDigits.MorseHedlundFrequencyDefect

open Theory.PiDigits.DigitChangeFourierDefect

open DecimalFactorComplexity
open Theory.PiDigits.FactorComplexity

/-- The canonical representative of the `i`th distinct length-`m` factor of
the pi digit stream. -/
noncomputable def piFactorRepresentative (m : ℕ) :
    Fin (piFactorComplexity m) → Factor Theory.PiDigits.piDigit m :=
  (canonicalComplexityData Theory.PiDigits.piDigit).classify m |>.symm

/-- The first position of the `i`th canonical distinct length-`m` factor. -/
noncomputable def piFactorFirstOccurrence (m : ℕ)
    (i : Fin (piFactorComplexity m)) : ℕ :=
  firstOccurrence (piFactorRepresentative m i)

/-- A canonical finite prefix containing the first occurrence of every
distinct length-`m` factor.  The sum cutoff is deliberately explicit: it is
not asserted to have any effective growth bound. -/
noncomputable def piFirstOccurrencePrefixLength (m : ℕ) : ℕ :=
  1 + ∑ i : Fin (piFactorComplexity m), piFactorFirstOccurrence m i

lemma factorAt_firstOccurrence_eq {α : Type*} [Fintype α] [DecidableEq α]
    {s : Stream α} {m : ℕ} (w : Factor s m) :
    factorAt s m (firstOccurrence w) = w := by
  apply Subtype.ext
  funext j
  exact (firstOccurrence_spec w j).symm

theorem piFactorFirstOccurrence_injective (m : ℕ) :
    Function.Injective (piFactorFirstOccurrence m) := by
  intro i j hij
  apply (canonicalComplexityData Theory.PiDigits.piDigit).classify m |>.symm.injective
  change piFactorRepresentative m i = piFactorRepresentative m j
  calc
    piFactorRepresentative m i =
        factorAt Theory.PiDigits.piDigit m (piFactorFirstOccurrence m i) :=
      (factorAt_firstOccurrence_eq (piFactorRepresentative m i)).symm
    _ = factorAt Theory.PiDigits.piDigit m (piFactorFirstOccurrence m j) := by
      rw [hij]
    _ = piFactorRepresentative m j :=
      factorAt_firstOccurrence_eq (piFactorRepresentative m j)

/-- The first occurrences, embedded into their explicit canonical prefix. -/
noncomputable def piFirstOccurrenceEmbedding (m : ℕ) :
    Fin (piFactorComplexity m) ↪ Fin (piFirstOccurrencePrefixLength m) where
  toFun i := ⟨piFactorFirstOccurrence m i, by
    have hle : piFactorFirstOccurrence m i ≤
        ∑ j : Fin (piFactorComplexity m), piFactorFirstOccurrence m j := by
      apply Finset.single_le_sum
      · intro j _hj
        exact Nat.zero_le _
      · exact Finset.mem_univ i
    unfold piFirstOccurrencePrefixLength
    omega⟩
  inj' := fun i j hij ↦
    piFactorFirstOccurrence_injective m (congrArg Fin.val hij)

/-- The half-open decimal-cylinder label at each canonical first occurrence. -/
noncomputable def piFirstOccurrenceCylinderCode (m : ℕ) :
    Fin (piFactorComplexity m) → Fin (10 ^ m) := fun i ↦
  DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m
    (piFactorFirstOccurrence m i)

theorem piFirstOccurrenceCylinderCode_injective (m : ℕ) :
    Function.Injective (piFirstOccurrenceCylinderCode m) := by
  intro i j hij
  change DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m
      (piFactorFirstOccurrence m i) =
    DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m
      (piFactorFirstOccurrence m j) at hij
  have hfactor :=
    (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_iff_factorAt_eq m
        (piFactorFirstOccurrence m i) (piFactorFirstOccurrence m j)).mp hij
  have hstream : DecimalFactorComplexity.piDecimalStream =
      Theory.PiDigits.piDigit := by
    funext n
    exact Theory.PiDigits.T20.decimalDigit_pi n
  rw [hstream] at hfactor
  apply (canonicalComplexityData Theory.PiDigits.piDigit).classify m |>.symm.injective
  change piFactorRepresentative m i = piFactorRepresentative m j
  calc
    piFactorRepresentative m i =
        factorAt Theory.PiDigits.piDigit m (piFactorFirstOccurrence m i) :=
      (factorAt_firstOccurrence_eq (piFactorRepresentative m i)).symm
    _ = factorAt Theory.PiDigits.piDigit m (piFactorFirstOccurrence m j) := hfactor
    _ = piFactorRepresentative m j :=
      factorAt_firstOccurrence_eq (piFactorRepresentative m j)

/-- The orbit point at a selected first occurrence lies in the half-open cell
encoded by its exact length-`m` decimal factor. -/
theorem piFirstOccurrenceEmbedding_mem_cell (m : ℕ)
    (i : Fin (piFactorComplexity m)) :
    piOrbit (piFirstOccurrenceEmbedding m i).val ∈ Set.Ico
      (((piFirstOccurrenceCylinderCode m i).val : ℝ) / (10 ^ m : ℕ))
      ((((piFirstOccurrenceCylinderCode m i).val + 1 : ℕ) : ℝ) /
        (10 ^ m : ℕ)) := by
  change piOrbit (piFactorFirstOccurrence m i) ∈ Set.Ico
    (((DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m
      (piFactorFirstOccurrence m i)).val : ℝ) / (10 ^ m : ℕ))
    (((((DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m
      (piFactorFirstOccurrence m i)).val + 1 : ℕ) : ℝ)) / (10 ^ m : ℕ))
  let pos := piFactorFirstOccurrence m i
  have hmem :
      DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit pos ∈
        Theory.PiDigits.PositiveLowerBlockDensity.T8.decimalCylinder m
          (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m pos) := by
    change Theory.PiDigits.PositiveLowerBlockDensity.T8.decimalCode m
        (DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit pos) =
      DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m pos
    exact (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_decimalCode m pos).symm
  have hcoord :=
    (Theory.PiDigits.PositiveLowerBlockDensity.T8.mem_decimalCylinder_iff m
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode m pos)
      (DecimalFactorComplexity.ClusterNearReturns.piDecimalCircleOrbit pos)).mp hmem
  rw [DecimalFactorComplexity.FiniteCylinderEnergy.unitCoordinate_piDecimalCircleOrbit] at hcoord
  simpa only [pos, piFirstOccurrenceEmbedding, piFirstOccurrenceCylinderCode,
    piOrbit, Theory.PiDigits.T27.piFractionalOrbit,
    Theory.PiDigits.T20.baseTenOrbit, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one] using hcoord

/-- Two cells are robustly nonadjacent when their linear label distance is
between `2` and `q-2`.  This excludes both ordinary and wraparound adjacent
cells. -/
def RobustlySeparated {q : ℕ} (a b : Fin q) : Prop :=
  2 ≤ Nat.dist a.val b.val ∧ Nat.dist a.val b.val ≤ q - 2

instance {q : ℕ} (a b : Fin q) : Decidable (RobustlySeparated a b) := by
  unfold RobustlySeparated
  infer_instance

/-- Points in robustly nonadjacent `q`-cells differ by a representative in
`[1/q,1-1/q]`. -/
lemma cell_difference_abs_bounds {q : ℕ} (hq : 4 ≤ q)
    (a b : Fin q) {x y : ℝ}
    (hx : x ∈ Set.Ico ((a.val : ℝ) / q) (((a.val + 1 : ℕ) : ℝ) / q))
    (hy : y ∈ Set.Ico ((b.val : ℝ) / q) (((b.val + 1 : ℕ) : ℝ) / q))
    (hab : RobustlySeparated a b) :
    (1 / (q : ℝ)) ≤ |y - x| ∧ |y - x| ≤ 1 - 1 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 4) hq)
  have ha : a.val < q := a.isLt
  have hb : b.val < q := b.isLt
  have hxlo : (a.val : ℝ) ≤ x * q := (div_le_iff₀ hqR).mp hx.1
  have hxhi : x * q < (a.val : ℝ) + 1 := by
    have := (lt_div_iff₀ hqR).mp hx.2
    norm_num at this ⊢
    exact this
  have hylo : (b.val : ℝ) ≤ y * q := (div_le_iff₀ hqR).mp hy.1
  have hyhi : y * q < (b.val : ℝ) + 1 := by
    have := (lt_div_iff₀ hqR).mp hy.2
    norm_num at this ⊢
    exact this
  have honeSub : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by
    field_simp
  unfold RobustlySeparated at hab
  rcases le_total a.val b.val with hle | hle
  · have hdist : Nat.dist a.val b.val = b.val - a.val :=
      Nat.dist_eq_sub_of_le hle
    rw [hdist] at hab
    have hlowNat : a.val + 2 ≤ b.val := by omega
    have hhighNat : b.val + 2 ≤ a.val + q := by omega
    have hlow : (a.val : ℝ) + 2 ≤ b.val := by exact_mod_cast hlowNat
    have hhigh : (b.val : ℝ) + 2 ≤ a.val + q := by exact_mod_cast hhighNat
    have hnonneg : 0 ≤ y - x := by nlinarith
    rw [abs_of_nonneg hnonneg, honeSub]
    constructor
    · apply (div_le_iff₀ hqR).2
      nlinarith
    · apply (le_div_iff₀ hqR).2
      nlinarith
  · have hdist : Nat.dist a.val b.val = a.val - b.val :=
      Nat.dist_eq_sub_of_le_right hle
    rw [hdist] at hab
    have hlowNat : b.val + 2 ≤ a.val := by omega
    have hhighNat : a.val + 2 ≤ b.val + q := by omega
    have hlow : (b.val : ℝ) + 2 ≤ a.val := by exact_mod_cast hlowNat
    have hhigh : (a.val : ℝ) + 2 ≤ b.val + q := by exact_mod_cast hhighNat
    have hnonpos : y - x ≤ 0 := by nlinarith
    rw [abs_of_nonpos hnonpos, honeSub]
    constructor
    · apply (div_le_iff₀ hqR).2
      nlinarith
    · apply (le_div_iff₀ hqR).2
      nlinarith

/-- A robustly separated pair contributes at least `q/2` total cosine energy
when averaged over frequencies `1,...,q`. -/
theorem sum_pairCosineEnergy_ge_half {q : ℕ} (hq : 4 ≤ q) {u : ℝ}
    (hu0 : (1 / (q : ℝ)) ≤ |u|)
    (hu1 : |u| ≤ 1 - 1 / (q : ℝ)) :
    (q : ℝ) / 2 ≤
      ∑ r : Fin q,
        (1 - Real.cos (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * u)) := by
  have hqR : (0 : ℝ) < q := by positivity
  have hL : 0 < (2 / (q : ℝ)) := by positivity
  have hhalf : (2 / (q : ℝ)) / 2 = 1 / (q : ℝ) := by field_simp
  have hsin := Theory.PiDigits.T27.abs_sin_pi_mul_lower
    (u := u) (L := 2 / (q : ℝ)) hL (by rw [hhalf]; exact hu0) (by
      rw [hhalf]; exact hu1)
  have hchord : 2 * (2 / (q : ℝ)) ≤
      ‖1 - Theory.PiDigits.T27.phase 1 u‖ := by
    rw [Theory.PiDigits.T27.norm_one_sub_phase_one]
    linarith
  have hdir := Theory.PiDigits.T27.norm_dirichletKernel_le_inv
    (H := q - 1) hL hchord
  have hqsub : q - 1 + 1 = q := by omega
  have hsumPhase :
      (∑ r : Fin q,
          Theory.PiDigits.T27.phase ((r.val + 1 : ℕ) : ℤ) u) =
        Theory.PiDigits.T27.phase 1 u *
          Theory.PiDigits.T27.dirichletKernel (q - 1) u := by
    rw [show (∑ r : Fin q,
        Theory.PiDigits.T27.phase ((r.val + 1 : ℕ) : ℤ) u) =
        ∑ r ∈ Finset.range q,
          Theory.PiDigits.T27.phase ((r + 1 : ℕ) : ℤ) u by
      simpa only using
        (Fin.sum_univ_eq_sum_range
          (fun r : ℕ ↦ Theory.PiDigits.T27.phase ((r + 1 : ℕ) : ℤ) u) q)]
    simp_rw [show ∀ r : ℕ, ((r + 1 : ℕ) : ℤ) = 1 + (r : ℤ) by
      intro r; push_cast; omega]
    simp_rw [Theory.PiDigits.T27.phase_add]
    rw [← Finset.mul_sum]
    simp only [Theory.PiDigits.T27.dirichletKernel, hqsub]
  have hsumNorm :
      ‖∑ r : Fin q,
          Theory.PiDigits.T27.phase ((r.val + 1 : ℕ) : ℤ) u‖ ≤
        (q : ℝ) / 2 := by
    rw [hsumPhase, norm_mul, Theory.PiDigits.T27.norm_phase, one_mul]
    calc
      ‖Theory.PiDigits.T27.dirichletKernel (q - 1) u‖ ≤
          (2 / (q : ℝ))⁻¹ := hdir
      _ = (q : ℝ) / 2 := by field_simp
  have hsumCos :
      (∑ r : Fin q,
          Real.cos (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * u)) ≤
        (q : ℝ) / 2 := by
    calc
      (∑ r : Fin q,
          Real.cos (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * u)) =
          (∑ r : Fin q,
            Theory.PiDigits.T27.phase ((r.val + 1 : ℕ) : ℤ) u).re := by
              rw [Complex.re_sum]
              apply Finset.sum_congr rfl
              intro r _
              simpa only [Int.cast_natCast] using
                (phase_re_eq_cos ((r.val + 1 : ℕ) : ℤ) u).symm
      _ ≤ ‖∑ r : Fin q,
          Theory.PiDigits.T27.phase ((r.val + 1 : ℕ) : ℤ) u‖ :=
        Complex.re_le_norm _
      _ ≤ (q : ℝ) / 2 := hsumNorm
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  linarith

lemma bad_cell_options_zero {q : ℕ} (hq : 4 ≤ q) (a b : Fin q)
    (ha : a.val = 0) (hbad : ¬ RobustlySeparated a b) :
    b.val = 0 ∨ b.val = 1 ∨ b.val + 1 = q := by
  unfold RobustlySeparated at hbad
  rw [ha, Nat.dist_eq_sub_of_le (Nat.zero_le _)] at hbad
  have hb := b.isLt
  omega

lemma bad_cell_options_last {q : ℕ} (hq : 4 ≤ q) (a b : Fin q)
    (ha : a.val + 1 = q) (hbad : ¬ RobustlySeparated a b) :
    b.val = 0 ∨ b.val + 1 = a.val ∨ b.val = a.val := by
  unfold RobustlySeparated at hbad
  have hba : b.val ≤ a.val := by omega
  rw [Nat.dist_eq_sub_of_le_right hba] at hbad
  have hb := b.isLt
  omega

lemma bad_cell_options_interior {q : ℕ} (hq : 4 ≤ q) (a b : Fin q)
    (ha0 : 0 < a.val) (ha1 : a.val + 1 < q)
    (hbad : ¬ RobustlySeparated a b) :
    b.val + 1 = a.val ∨ b.val = a.val ∨ b.val = a.val + 1 := by
  unfold RobustlySeparated at hbad
  have hb := b.isLt
  rcases le_total a.val b.val with hab | hab
  · rw [Nat.dist_eq_sub_of_le hab] at hbad
    omega
  · rw [Nat.dist_eq_sub_of_le_right hab] at hbad
    omega

lemma card_filter_comp_eq_le_one {P q : ℕ} (code : Fin P → Fin q)
    (hcode : Function.Injective code) (g : Fin q → ℕ)
    (hg : Function.Injective g) (c : ℕ) :
    ((Finset.univ : Finset (Fin P)).filter fun j ↦ g (code j) = c).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  apply hcode
  apply hg
  exact hi.trans hj.symm

lemma card_union_three_le {α : Type*} [DecidableEq α]
    (s t u : Finset α) :
    (s ∪ t ∪ u).card ≤ s.card + t.card + u.card := by
  have hst := Finset.card_union_le s t
  have hstu := Finset.card_union_le (s ∪ t) u
  omega

/-- For an injective assignment of cell labels, each selected cell has at
most three selected labels that are equal or cyclically adjacent to it. -/
theorem badNeighbor_card_le_three {P q : ℕ} (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code) (i : Fin P) :
    ((Finset.univ : Finset (Fin P)).filter fun j ↦
      ¬ RobustlySeparated (code i) (code j)).card ≤ 3 := by
  classical
  let bad := (Finset.univ : Finset (Fin P)).filter fun j ↦
    ¬ RobustlySeparated (code i) (code j)
  change bad.card ≤ 3
  let val : Fin q → ℕ := fun a ↦ a.val
  let valSucc : Fin q → ℕ := fun a ↦ a.val + 1
  have hval : Function.Injective val := fun _ _ h ↦ Fin.ext h
  have hvalSucc : Function.Injective valSucc := by
    intro a b h
    apply Fin.ext
    dsimp only [valSucc] at h
    omega
  have hfiberVal (c : ℕ) :
      ((Finset.univ : Finset (Fin P)).filter fun j ↦ val (code j) = c).card ≤ 1 :=
    card_filter_comp_eq_le_one code hcode val hval c
  have hfiberSucc (c : ℕ) :
      ((Finset.univ : Finset (Fin P)).filter fun j ↦ valSucc (code j) = c).card ≤ 1 :=
    card_filter_comp_eq_le_one code hcode valSucc hvalSucc c
  by_cases hi0 : (code i).val = 0
  · let f0 := (Finset.univ : Finset (Fin P)).filter fun j ↦ val (code j) = 0
    let f1 := (Finset.univ : Finset (Fin P)).filter fun j ↦ val (code j) = 1
    let fq := (Finset.univ : Finset (Fin P)).filter fun j ↦ valSucc (code j) = q
    have hsub : bad ⊆ f0 ∪ f1 ∪ fq := by
      intro j hj
      have hjbad : ¬ RobustlySeparated (code i) (code j) := by
        simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      rcases bad_cell_options_zero hq (code i) (code j) hi0 hjbad with h | h | h
      · simp [f0, val, h]
      · simp [f1, val, h]
      · simp [fq, valSucc, h]
    have hcard := Finset.card_le_card hsub
    have hunion := card_union_three_le f0 f1 fq
    have h0 : f0.card ≤ 1 := hfiberVal 0
    have h1 : f1.card ≤ 1 := hfiberVal 1
    have hq' : fq.card ≤ 1 := hfiberSucc q
    omega
  · by_cases hilast : (code i).val + 1 = q
    · let f0 := (Finset.univ : Finset (Fin P)).filter fun j ↦ val (code j) = 0
      let fp := (Finset.univ : Finset (Fin P)).filter fun j ↦
        valSucc (code j) = (code i).val
      let fs := (Finset.univ : Finset (Fin P)).filter fun j ↦
        val (code j) = (code i).val
      have hsub : bad ⊆ f0 ∪ fp ∪ fs := by
        intro j hj
        have hjbad : ¬ RobustlySeparated (code i) (code j) := by
          simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
        rcases bad_cell_options_last hq (code i) (code j) hilast hjbad with h | h | h
        · simp [f0, val, h]
        · simp [fp, valSucc, h]
        · simp [fs, val, h]
      have hcard := Finset.card_le_card hsub
      have hunion := card_union_three_le f0 fp fs
      have h0 : f0.card ≤ 1 := hfiberVal 0
      have hp : fp.card ≤ 1 := hfiberSucc (code i).val
      have hs : fs.card ≤ 1 := hfiberVal (code i).val
      omega
    · have hiPos : 0 < (code i).val := Nat.pos_of_ne_zero hi0
      have hiLt : (code i).val + 1 < q := by omega
      let fp := (Finset.univ : Finset (Fin P)).filter fun j ↦
        valSucc (code j) = (code i).val
      let fs := (Finset.univ : Finset (Fin P)).filter fun j ↦
        val (code j) = (code i).val
      let fn := (Finset.univ : Finset (Fin P)).filter fun j ↦
        val (code j) = (code i).val + 1
      have hsub : bad ⊆ fp ∪ fs ∪ fn := by
        intro j hj
        have hjbad : ¬ RobustlySeparated (code i) (code j) := by
          simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
        rcases bad_cell_options_interior hq (code i) (code j) hiPos hiLt hjbad with h | h | h
        · simp [fp, valSucc, h]
        · simp [fs, val, h]
        · simp [fn, val, h]
      have hcard := Finset.card_le_card hsub
      have hunion := card_union_three_le fp fs fn
      have hp : fp.card ≤ 1 := hfiberSucc (code i).val
      have hs : fs.card ≤ 1 := hfiberVal (code i).val
      have hn : fn.card ≤ 1 := hfiberVal ((code i).val + 1)
      omega

/-- Consequently each selected cell has at least `P-3` robustly separated
selected neighbours. -/
theorem robustNeighbor_card_ge_sub_three {P q : ℕ} (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code) (i : Fin P) :
    P - 3 ≤ ((Finset.univ : Finset (Fin P)).filter fun j ↦
      RobustlySeparated (code i) (code j)).card := by
  classical
  let good := (Finset.univ : Finset (Fin P)).filter fun j ↦
    RobustlySeparated (code i) (code j)
  change P - 3 ≤ good.card
  have hsplit : good.card +
      ((Finset.univ : Finset (Fin P)).filter fun j ↦
        ¬ RobustlySeparated (code i) (code j)).card = P := by
    simpa only [good, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin P)))
        (p := fun j ↦ RobustlySeparated (code i) (code j)))
  have hbad :
      ((Finset.univ : Finset (Fin P)).filter fun j ↦
        ¬ RobustlySeparated (code i) (code j)).card ≤ 3 :=
    badNeighbor_card_le_three hq code hcode i
  omega

lemma one_sub_cos_nonneg (t : ℝ) : 0 ≤ 1 - Real.cos t := by
  linarith [Real.cos_le_one t]

/-- For one selected point, summing its pair energies first over all selected
points and then over frequencies `1,...,q` detects its `P-3` robust
neighbours. -/
theorem sum_neighbor_frequencyEnergy_ge {P q : ℕ} (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code)
    (x : Fin P → ℝ)
    (hcell : ∀ i, x i ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q))
    (i : Fin P) :
    (q : ℝ) / 2 * (P - 3 : ℕ) ≤
      ∑ j : Fin P, ∑ r : Fin q,
        (1 - Real.cos
          (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := by
  classical
  let good := (Finset.univ : Finset (Fin P)).filter fun j ↦
    RobustlySeparated (code i) (code j)
  have hgood : P - 3 ≤ good.card := by
    simpa only [good] using robustNeighbor_card_ge_sub_three hq code hcode i
  have hpair (j : Fin P) (hj : j ∈ good) :
      (q : ℝ) / 2 ≤
        ∑ r : Fin q,
          (1 - Real.cos
            (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := by
    have hsep : RobustlySeparated (code i) (code j) := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hbounds := cell_difference_abs_bounds hq (code i) (code j)
      (hcell i) (hcell j) hsep
    exact sum_pairCosineEnergy_ge_half hq hbounds.1 hbounds.2
  have hrestricted :
      (∑ j ∈ good, (q : ℝ) / 2) ≤
        ∑ j ∈ good, ∑ r : Fin q,
          (1 - Real.cos
            (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hpair j hj
  have hmono :
      (∑ j ∈ good, ∑ r : Fin q,
          (1 - Real.cos
            (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i)))) ≤
        ∑ j : Fin P, ∑ r : Fin q,
          (1 - Real.cos
            (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
    intro j _hj _hnot
    exact Finset.sum_nonneg fun r _hr ↦ one_sub_cos_nonneg _
  calc
    (q : ℝ) / 2 * (P - 3 : ℕ) ≤ (q : ℝ) / 2 * good.card := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hgood) (by positivity)
    _ = ∑ j ∈ good, (q : ℝ) / 2 := by simp [mul_comm]
    _ ≤ ∑ j ∈ good, ∑ r : Fin q,
        (1 - Real.cos
          (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := hrestricted
    _ ≤ ∑ j : Fin P, ∑ r : Fin q,
        (1 - Real.cos
          (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))) := hmono

/-- The ordered-pair cosine energy of a finite selected support at frequency
`h`.  This is exactly the right-hand side of T20's all-pairs defect identity
when the selected support itself is used as the whole prefix. -/
def selectedPairEnergy {P : ℕ} (x : Fin P → ℝ) (h : ℤ) : ℝ :=
  ∑ ij : Fin P × Fin P,
    (1 - Real.cos (2 * Real.pi * (h : ℝ) * (x ij.2 - x ij.1)))

/-- Some value of a real-valued function on a nonempty finite set is at least
its average, stated without division. -/
lemma exists_sum_le_card_mul {ι : Type*} [Fintype ι]
    (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ S, ∑ j ∈ S, f j ≤ (S.card : ℝ) * f i := by
  obtain ⟨i, hi, himax⟩ := S.exists_max_image f hS
  refine ⟨i, hi, ?_⟩
  simpa [nsmul_eq_mul] using S.sum_le_card_nsmul f (f i) himax

/-- **Selected-support averaging theorem.** If `P` points occupy distinct
`q`-adic cells, one of the canonical frequencies `1,...,q` detects ordered
pair energy at least `P(P-3)/2`.

The conclusion retains the finite selected support.  Its eventual use for pi
selects the first occurrence of each distinct length-`m` factor; the bare
existence of a large defect at some uncontrolled prefix is not stronger than
T21's fixed-frequency unbounded-gap theorem. -/
theorem exists_selectedPairEnergy_ge {P q : ℕ} (hq : 4 ≤ q)
    (code : Fin P → Fin q) (hcode : Function.Injective code)
    (x : Fin P → ℝ)
    (hcell : ∀ i, x i ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    ∃ r : Fin q,
      (P : ℝ) * (P - 3 : ℕ) / 2 ≤
        selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
  classical
  let E : Fin P → Fin P → Fin q → ℝ := fun i j r ↦
    1 - Real.cos
      (2 * Real.pi * ((r.val + 1 : ℕ) : ℝ) * (x j - x i))
  have hsumI :
      (∑ i : Fin P, (q : ℝ) / 2 * (P - 3 : ℕ)) ≤
        ∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r := by
    apply Finset.sum_le_sum
    intro i _hi
    simpa only [E] using
      sum_neighbor_frequencyEnergy_ge hq code hcode x hcell i
  have hreorder :
      (∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r) =
        ∑ r : Fin q,
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
    calc
      (∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r) =
          ∑ i : Fin P, ∑ r : Fin q, ∑ j : Fin P, E i j r := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact Finset.sum_comm
      _ = ∑ r : Fin q, ∑ i : Fin P, ∑ j : Fin P, E i j r :=
        Finset.sum_comm
      _ = ∑ r : Fin q,
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
            apply Finset.sum_congr rfl
            intro r _hr
            rw [selectedPairEnergy, ← Finset.univ_product_univ,
              Finset.sum_product]
            rfl
  have htotal :
      (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 2) ≤
        ∑ r : Fin q,
          selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) := by
    rw [← hreorder]
    calc
      (q : ℝ) * ((P : ℝ) * (P - 3 : ℕ) / 2) =
          ∑ i : Fin P, (q : ℝ) / 2 * (P - 3 : ℕ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
      _ ≤ ∑ i : Fin P, ∑ j : Fin P, ∑ r : Fin q, E i j r := hsumI
  have hqNonempty : (Finset.univ : Finset (Fin q)).Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨r, _hr, havg⟩ := exists_sum_le_card_mul
    (Finset.univ : Finset (Fin q)) hqNonempty
    (fun r ↦ selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ))
  refine ⟨r, ?_⟩
  simp only [Finset.card_univ, Fintype.card_fin] at havg
  have hqR : (0 : ℝ) < q := by positivity
  nlinarith

/-- On the selected support itself, the averaging theorem gives square norm
at most `P(P+3)/2` at one canonical frequency.  At `P = 3` this equals the
trivial `P²`; the saving is strict from `P ≥ 4` and asymptotically relative. -/
theorem exists_selectedSupport_norm_sq_le {P q : ℕ} (hP : 3 ≤ P)
    (hq : 4 ≤ q) (code : Fin P → Fin q)
    (hcode : Function.Injective code) (x : Fin P → ℝ)
    (hcell : ∀ i, x i ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    ∃ r : Fin q,
      ‖∑ i : Fin P, phase ((r.val + 1 : ℕ) : ℤ) (x i)‖ ^ 2 ≤
        (P : ℝ) * (P + 3 : ℕ) / 2 := by
  obtain ⟨r, hr⟩ := exists_selectedPairEnergy_ge hq code hcode x hcell
  have hid := finiteCircle_defect_eq_pairCosineEnergy x
    ((r.val + 1 : ℕ) : ℤ)
  change (P : ℝ) ^ 2 -
      ‖∑ i : Fin P, phase ((r.val + 1 : ℕ) : ℤ) (x i)‖ ^ 2 =
        selectedPairEnergy x ((r.val + 1 : ℕ) : ℤ) at hid
  have hsubcast : ((P - 3 : ℕ) : ℝ) = (P : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsubcast] at hr
  refine ⟨r, ?_⟩
  have hPcast : ((P + 3 : ℕ) : ℝ) = (P : ℝ) + 3 := by norm_num
  rw [hPcast]
  nlinarith

/-- T20's all-pairs identity transfers the energy of any embedded selected
support into the defect of the full ambient prefix.  All omitted ordered
pairs have nonnegative cosine energy. -/
theorem selectedPairEnergy_le_fullDefect {P N : ℕ}
    (idx : Fin P ↪ Fin N) (x : Fin P → ℝ) (y : Fin N → ℝ)
    (h : ℤ) (hxy : ∀ i, x i = y (idx i)) :
    selectedPairEnergy x h ≤
      (N : ℝ) ^ 2 - ‖∑ i : Fin N, phase h (y i)‖ ^ 2 := by
  classical
  let idxPair : Fin P × Fin P ↪ Fin N × Fin N := idx.prodMap idx
  let energy : Fin N × Fin N → ℝ := fun ij ↦
    1 - Real.cos (2 * Real.pi * (h : ℝ) * (y ij.2 - y ij.1))
  have hselected : selectedPairEnergy x h =
      ∑ ij ∈ Finset.univ.map idxPair, energy ij := by
    rw [Finset.sum_map]
    unfold selectedPairEnergy
    apply Finset.sum_congr rfl
    intro ij _hij
    change
      1 - Real.cos (2 * Real.pi * (h : ℝ) * (x ij.2 - x ij.1)) =
        1 - Real.cos
          (2 * Real.pi * (h : ℝ) * (y (idx ij.2) - y (idx ij.1)))
    rw [← hxy ij.1, ← hxy ij.2]
  have hmono :
      (∑ ij ∈ Finset.univ.map idxPair, energy ij) ≤
        ∑ ij : Fin N × Fin N, energy ij := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro ij _hij _hnot
    exact one_sub_cos_nonneg _
  rw [finiteCircle_defect_eq_pairCosineEnergy y h]
  rw [hselected]
  simpa only [energy] using hmono

/-- Combined abstract full-prefix theorem.  Distinct occupied cells are
selected inside an ambient prefix; a canonical frequency `1,...,q` has full
prefix Fourier defect at least `P(P-3)/2`. -/
theorem exists_fullDefect_ge_of_selectedCells {P N q : ℕ} (hq : 4 ≤ q)
    (idx : Fin P ↪ Fin N) (y : Fin N → ℝ) (code : Fin P → Fin q)
    (hcode : Function.Injective code)
    (hcell : ∀ i, y (idx i) ∈ Set.Ico
      (((code i).val : ℝ) / q) ((((code i).val + 1 : ℕ) : ℝ) / q)) :
    ∃ r : Fin q,
      (P : ℝ) * (P - 3 : ℕ) / 2 ≤
        (N : ℝ) ^ 2 -
          ‖∑ i : Fin N,
            phase ((r.val + 1 : ℕ) : ℤ) (y i)‖ ^ 2 := by
  let x : Fin P → ℝ := fun i ↦ y (idx i)
  obtain ⟨r, hr⟩ := exists_selectedPairEnergy_ge hq code hcode x hcell
  refine ⟨r, hr.trans ?_⟩
  exact selectedPairEnergy_le_fullDefect idx x y
    ((r.val + 1 : ℕ) : ℤ) (fun _ ↦ rfl)

/-- On the sample containing exactly one first occurrence of each distinct
length-`m` pi factor, some `h ≤ 10^m` gives the fixed relative square-norm
saving `P(P+3)/2`.  Passing from this sparse sample to the entire prefix loses
that relative saving because the intervening repeated visits are presently
uncontrolled. -/
theorem pi_firstOccurrenceSelectedSupport_norm_sq_le (m : ℕ) (hm : 3 ≤ m) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ 10 ^ m ∧
      ‖∑ i : Fin (piFactorComplexity m),
          phase (h : ℤ) (piOrbit (piFirstOccurrenceEmbedding m i).val)‖ ^ 2 ≤
        (piFactorComplexity m : ℝ) *
          (piFactorComplexity m + 3 : ℕ) / 2 := by
  have hP : 3 ≤ piFactorComplexity m := by
    have hp := pi_factorComplexity_lower_bound m (by omega)
    omega
  have hq : 4 ≤ 10 ^ m := by
    calc
      4 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨r, hr⟩ := exists_selectedSupport_norm_sq_le hP hq
    (piFirstOccurrenceCylinderCode m)
    (piFirstOccurrenceCylinderCode_injective m)
    (fun i : Fin (piFactorComplexity m) ↦
      piOrbit (piFirstOccurrenceEmbedding m i).val)
    (piFirstOccurrenceEmbedding_mem_cell m)
  refine ⟨r.val + 1, by omega, by exact r.isLt, ?_⟩
  simpa only using hr

/-- The canonical first-occurrence specialization for pi.  The prefix length
is the explicit sum cutoff `piFirstOccurrencePrefixLength m`, so it contains
one representative of every distinct length-`m` factor.  No quantitative
upper bound on that cutoff is claimed. -/
theorem pi_firstOccurrencePrefix_defect_ge_complexity (m : ℕ) (hm : 1 ≤ m) :
    ∃ r : Fin (10 ^ m),
      (piFactorComplexity m : ℝ) *
          (piFactorComplexity m - 3 : ℕ) / 2 ≤
        (piFirstOccurrencePrefixLength m : ℝ) ^ 2 -
          ‖exponentialSum piOrbit (piFirstOccurrencePrefixLength m)
            ((r.val + 1 : ℕ) : ℤ)‖ ^ 2 := by
  have hq : 4 ≤ 10 ^ m := by
    calc
      4 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨r, hr⟩ := exists_fullDefect_ge_of_selectedCells
    (P := piFactorComplexity m)
    (N := piFirstOccurrencePrefixLength m) (q := 10 ^ m) hq
    (piFirstOccurrenceEmbedding m)
    (fun i : Fin (piFirstOccurrencePrefixLength m) ↦ piOrbit i.val)
    (piFirstOccurrenceCylinderCode m)
    (piFirstOccurrenceCylinderCode_injective m)
    (piFirstOccurrenceEmbedding_mem_cell m)
  refine ⟨r, ?_⟩
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ phase ((r.val + 1 : ℕ) : ℤ) (piOrbit i))
    (piFirstOccurrencePrefixLength m)] at hr
  simpa only [exponentialSum] using hr

/-- Morse--Hedlund makes the preceding canonical defect at least quadratic in
the factor length.  This existential corollary alone is not stronger than
T21's unbounded fixed-frequency gap; its content is the explicit prefix made
from all first occurrences and the frequency restriction `h ≤ 10^m`. -/
theorem pi_firstOccurrencePrefix_defect_ge_morseHedlund (m : ℕ) (hm : 3 ≤ m) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ 10 ^ m ∧
      ((m + 1 : ℕ) : ℝ) * (m - 2 : ℕ) / 2 ≤
        (piFirstOccurrencePrefixLength m : ℝ) ^ 2 -
          ‖exponentialSum piOrbit (piFirstOccurrencePrefixLength m) (h : ℤ)‖ ^ 2 := by
  obtain ⟨r, hr⟩ :=
    pi_firstOccurrencePrefix_defect_ge_complexity m (by omega)
  let h : ℕ := r.val + 1
  have hh1 : 1 ≤ h := by simp [h]
  have hhq : h ≤ 10 ^ m := by
    dsimp [h]
    exact r.isLt
  have hp : m + 1 ≤ piFactorComplexity m :=
    pi_factorComplexity_lower_bound m (by omega)
  have hsub : m - 2 ≤ piFactorComplexity m - 3 := by omega
  have hpR : ((m + 1 : ℕ) : ℝ) ≤ piFactorComplexity m := by
    exact_mod_cast hp
  have hsubR : ((m - 2 : ℕ) : ℝ) ≤
      (piFactorComplexity m - 3 : ℕ) := by
    exact_mod_cast hsub
  have hmul : ((m + 1 : ℕ) : ℝ) * (m - 2 : ℕ) ≤
      (piFactorComplexity m : ℝ) *
        (piFactorComplexity m - 3 : ℕ) := by
    exact mul_le_mul hpR hsubR (by positivity) (by positivity)
  refine ⟨h, hh1, hhq, ?_⟩
  dsimp only [h]
  exact (div_le_div_of_nonneg_right hmul (by norm_num)).trans hr

end Theory.PiDigits.MorseHedlundFrequencyDefect
