import TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore

/-!
# T57: a moving-word obstruction to universal linear finite cores

Source: `problems/local/pi-positive-decimal-factor-entropy.txt`
SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
Original source URL: none; the canonical question was formulated locally.

This sibling construction refutes only T44's universal linear finite-core
hypothesis. It proves no instance or negation of C6 or C1 and makes no claim
about pi.
-/

noncomputable section

open Filter Finset Set Topology

namespace DecimalFactorEntropy.T57MovingWordCoreObstruction

open DecimalFactorEntropy.TransversalEntropy
open DecimalFactorEntropy.T44EndpointSafeInvariantCore
open DecimalFactorComplexity.NormalOrbitNearReturns
open Theory.PiDigits.T20
open Theory.PiDigits.PositiveLowerBlockDensity.T7
open Theory.PiDigits.PositiveLowerBlockDensity.T8

/-- The circle point `10 ^ (-(k+1))`; indexing starts with `10⁻¹`. -/
def reciprocalPoint (k : ℕ) : UnitAddCircle :=
  (((1 : ℝ) / (10 : ℝ) ^ (k + 1) : ℝ) : UnitAddCircle)

/-- The compact countable set `{0} ∪ {10⁻ᵏ : k ≥ 1}` on the circle. -/
def X : Set UnitAddCircle := insert 0 (Set.range reciprocalPoint)

theorem X_eq_zero_union_negative_powers :
    X = {0} ∪ {x : UnitAddCircle |
      ∃ k : ℕ, 1 ≤ k ∧ x = (((10 : ℝ) ^ (-(k : ℤ)) : ℝ) : UnitAddCircle)} := by
  ext x
  simp only [X, Set.mem_insert_iff, Set.mem_range, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨k, rfl⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨k + 1, by omega, ?_⟩
      simp only [reciprocalPoint, zpow_neg, zpow_natCast]
      congr 1
      field_simp
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inl rfl
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
      right
      refine ⟨t, ?_⟩
      simp only [reciprocalPoint, zpow_neg, zpow_natCast]
      congr 1
      simp [Nat.add_comm]

theorem reciprocalPoint_tendsto_zero :
    Tendsto reciprocalPoint atTop (𝓝 0) := by
  have hreal : Tendsto (fun k : ℕ => (1 : ℝ) / (10 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => ((10 : ℝ)⁻¹) ^ (k + 1)) atTop (𝓝 0) := by
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    simpa [div_eq_mul_inv, inv_pow] using hpow
  simpa only [reciprocalPoint, AddCircle.coe_zero] using
    (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hreal

theorem X_isCompact : IsCompact X := by
  exact reciprocalPoint_tendsto_zero.isCompact_insert_range

theorem reciprocalPoint_addOrderOf (k : ℕ) :
    addOrderOf (reciprocalPoint k) = 10 ^ (k + 1) := by
  simpa [reciprocalPoint] using
    (AddCircle.addOrderOf_period_div (p := (1 : ℝ))
      (show 0 < 10 ^ (k + 1) by positivity))

theorem reciprocalPoint_injective : Function.Injective reciprocalPoint := by
  intro k l hkl
  have hpow : 10 ^ (k + 1) = 10 ^ (l + 1) := by
    rw [← reciprocalPoint_addOrderOf k, ← reciprocalPoint_addOrderOf l, hkl]
  have : k + 1 = l + 1 := (Nat.pow_right_injective (by omega : 1 < 10)) hpow
  omega

theorem X_infinite : X.Infinite := by
  exact (Set.infinite_range_of_injective reciprocalPoint_injective).mono
    (Set.range_subset_iff.mpr fun _ => Set.mem_insert_of_mem 0 (Set.mem_range_self _))

theorem timesTen_reciprocalPoint_zero : timesTen (reciprocalPoint 0) = 0 := by
  change 10 • ((((1 : ℝ) / (10 : ℝ) ^ (0 + 1) : ℝ) : UnitAddCircle)) = 0
  rw [← AddCircle.coe_nsmul]
  norm_num

theorem timesTen_reciprocalPoint_succ (k : ℕ) :
    timesTen (reciprocalPoint (k + 1)) = reciprocalPoint k := by
  change 10 • ((((1 : ℝ) / (10 : ℝ) ^ (k + 1 + 1) : ℝ) : UnitAddCircle)) =
    (((1 : ℝ) / (10 : ℝ) ^ (k + 1) : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_nsmul]
  simp only [nsmul_eq_mul]
  change ((((10 : ℝ) * (1 / (10 : ℝ) ^ (k + 1 + 1)) : ℝ) : UnitAddCircle)) =
    (((1 : ℝ) / (10 : ℝ) ^ (k + 1) : ℝ) : UnitAddCircle)
  congr 1
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
  field_simp

theorem X_forward_timesTen_invariant : ForwardTimesTenInvariant X := by
  rintro x (rfl | ⟨k, rfl⟩)
  · left
    simp [timesTen]
  · cases k with
    | zero => exact Or.inl timesTen_reciprocalPoint_zero
    | succ k =>
        rw [timesTen_reciprocalPoint_succ]
        exact Set.mem_insert_of_mem 0 (Set.mem_range_self k)

/-- The terminating, zero-tailed expansion selected throughout the proof. -/
def imageExpansion (j : ℕ) (x : UnitAddCircle) : DecimalStream :=
  Real.digits (unitCoordinate (circleMul (16 ^ j) x)) 10

/-- Its first `m` digits, represented as a fixed-length vector. -/
def imagePrefix (m j : ℕ) (x : UnitAddCircle) : Fin m → Fin 10 :=
  fun i => imageExpansion j x i.val

theorem imageExpansion_circleValue (j : ℕ) (x : UnitAddCircle) :
    circleValue (imageExpansion j x) = circleMul (16 ^ j) x := by
  rw [circleValue, imageExpansion,
    Real.ofDigits_digits (by norm_num)
      ⟨unitCoordinate_nonneg _, unitCoordinate_lt_one _⟩]
  exact coe_unitCoordinate _

theorem unitCoordinate_circleMul_reciprocalPoint (j k : ℕ) :
    unitCoordinate (circleMul (16 ^ j) (reciprocalPoint k)) =
      Int.fract ((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1)) := by
  simp only [unitCoordinate, circleMul, reciprocalPoint]
  rw [show (16 ^ j) •
      ((((1 : ℝ) / (10 : ℝ) ^ (k + 1) : ℝ) : UnitAddCircle)) =
        ((((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1) : ℝ) : UnitAddCircle)) by
    rw [← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul]
    congr 1
    push_cast
    ring]
  rw [AddCircle.coe_equivIco_mk_apply]
  simp

theorem sixteen_pow_le_ten_pow_two_mul (j : ℕ) :
    16 ^ j ≤ 10 ^ (2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      exact Nat.mul_le_mul ih (by norm_num)

/-- Once the reciprocal is deep enough, every one of its first `m` digits
after the `j`th times-16 image is zero. -/
theorem imagePrefix_reciprocal_eq_zero_of_deep
    (m j k : ℕ) (hk : m + 2 * j + 1 ≤ k) :
    imagePrefix m j (reciprocalPoint k) = fun _ => 0 := by
  funext i
  have hi : i.val < m := i.isLt
  show Real.digits (unitCoordinate (circleMul (16 ^ j) (reciprocalPoint k)))
      10 i.val = 0
  rw [unitCoordinate_circleMul_reciprocalPoint]
  have hxpos : 0 ≤ ((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1)) := by positivity
  have hxlt1 : ((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1)) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (10 : ℝ) ^ (k + 1))]
    have h1 : (16 : ℝ) ^ j ≤ (10 : ℝ) ^ (2 * j) := by
      exact_mod_cast sixteen_pow_le_ten_pow_two_mul j
    have h2 : (10 : ℝ) ^ (2 * j) < (10 : ℝ) ^ (k + 1) := by
      rw [pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)]
      have : 2 * j < k + 1 := by omega
      exact_mod_cast this
    exact h1.trans_lt h2
  rw [Int.fract_eq_self.mpr ⟨hxpos, hxlt1⟩]
  change Fin.ofNat 10
      ⌊((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1)) * ((10 : ℝ) ^ (i.val + 1))⌋₊ = 0
  have hfloor : ⌊((16 : ℝ) ^ j / (10 : ℝ) ^ (k + 1)) *
      (10 : ℝ) ^ (i.val + 1)⌋₊ = 0 := by
    apply Nat.floor_eq_zero.mpr
    have hpow_le : (16 : ℝ) ^ j ≤ (10 : ℝ) ^ (2 * j) := by
      exact_mod_cast sixteen_pow_le_ten_pow_two_mul j
    have hpow_ij_lt : 2 * j + (i.val + 1) < k + 1 := by
      have h1 : i.val + 1 ≤ m := by omega
      omega
    have hpow_add : (10 : ℝ) ^ (2 * j) * (10 : ℝ) ^ (i.val + 1) =
        (10 : ℝ) ^ (2 * j + (i.val + 1)) := by
      rw [← pow_add, pow_add]
    have hmul_lt : (16 : ℝ) ^ j * (10 : ℝ) ^ (i.val + 1) <
        (10 : ℝ) ^ (k + 1) := by
      calc
        (16 : ℝ) ^ j * (10 : ℝ) ^ (i.val + 1) ≤
            (10 : ℝ) ^ (2 * j) * (10 : ℝ) ^ (i.val + 1) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hpow_le) (by positivity)
        _ = (10 : ℝ) ^ (2 * j + (i.val + 1)) := hpow_add
        _ < (10 : ℝ) ^ (k + 1) := by
          rw [pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 10)]
          exact hpow_ij_lt
    rw [div_mul_eq_mul_div]
    rwa [div_lt_one (by positivity : (0 : ℝ) < (10 : ℝ) ^ (k + 1))]
  rw [hfloor]
  rfl

/-- The selected expansion of every nonzero point in every times-16 image has
the terminating zero-tail convention, with a uniform tail start `k + 1`. -/
theorem imageExpansion_reciprocal_zero_tail (j k n : ℕ) (hn : k + 1 ≤ n) :
    imageExpansion j (reciprocalPoint k) n = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply Fin.ext
  rw [imageExpansion, unitCoordinate_circleMul_reciprocalPoint]
  simp only [Real.digits, Fin.val_ofNat]
  rw [show (16 : ℝ) ^ j = ((16 ^ j : ℕ) : ℝ) by norm_num,
    show (10 : ℝ) ^ (k + 1) = ((10 ^ (k + 1) : ℕ) : ℝ) by norm_num]
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have heq :
      ((16 ^ j % 10 ^ (k + 1) : ℕ) : ℝ) / ((10 ^ (k + 1) : ℕ) : ℝ) *
          (10 : ℝ) ^ (k + 1 + t + 1) =
        ((16 ^ j % 10 ^ (k + 1)) * 10 ^ (t + 1) : ℕ) := by
    rw [show k + 1 + t + 1 = (k + 1) + (t + 1) by omega, pow_add]
    push_cast
    field_simp
    ring
  norm_num only [Nat.cast_ofNat]
  rw [heq, Nat.floor_natCast]
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨(16 ^ j % 10 ^ (k + 1)) * 10 ^ t, ?_⟩
  rw [pow_succ]
  ring

/-- Indexes all prefixes needed through the inclusive range `0 ≤ j ≤ R`.
The fiber over `j` has exactly `m + 2*j + 2` elements. -/
abbrev PrefixIndex (m R : ℕ) :=
  Σ j : Fin (R + 1), Fin (m + 2 * j.val + 2)

def indexedPrefix (m R : ℕ) (q : PrefixIndex m R) : Fin m → Fin 10 :=
  imagePrefix m q.1.val (reciprocalPoint q.2.val)

def observedPrefixes (m R : ℕ) : Finset (Fin m → Fin 10) :=
  Finset.univ.image (indexedPrefix m R)

/-- Exact size of the index family, displaying the inclusive `R + 1` range. -/
theorem prefixIndex_card (m R : ℕ) :
    Fintype.card (PrefixIndex m R) =
      ∑ j ∈ Finset.range (R + 1), (m + 2 * j + 2) := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  simpa using
    (Fin.sum_univ_eq_sum_range (fun j : ℕ => m + 2 * j + 2) (R + 1))

/-- The number of actually observed prefixes is bounded by the displayed
inclusive prefix count. -/
theorem observedPrefixes_card_le_prefix_count (m R : ℕ) :
    (observedPrefixes m R).card ≤
      ∑ j ∈ Finset.range (R + 1), (m + 2 * j + 2) := by
  calc
    (observedPrefixes m R).card ≤ (Finset.univ : Finset (PrefixIndex m R)).card :=
      Finset.card_image_le
    _ = Fintype.card (PrefixIndex m R) := Finset.card_univ
    _ = _ := prefixIndex_card m R

theorem imagePrefix_zero (m j : ℕ) :
    imagePrefix m j 0 = fun _ => 0 := by
  have hz : circleMul (16 ^ j) (0 : UnitAddCircle) = 0 := by
    simp [circleMul]
  have hcoord : unitCoordinate (0 : UnitAddCircle) = 0 := by
    simpa [unitCoordinate] using
      (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (0 : ℝ))
  funext i
  apply Fin.ext
  simp [imagePrefix, imageExpansion, hz, hcoord, Real.digits]

theorem imageExpansion_zero_tail (j : ℕ) (x : UnitAddCircle) (hx : x ∈ X) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → imageExpansion j x n = 0 := by
  rcases hx with rfl | ⟨k, rfl⟩
  · refine ⟨0, fun n hn => ?_⟩
    have h := congrFun (imagePrefix_zero (n + 1) j) (⟨n, by omega⟩ : Fin (n + 1))
    exact h
  · exact ⟨k + 1, fun n hn => imageExpansion_reciprocal_zero_tail j k n hn⟩

/-- Every prefix from every point of `X` at every inclusive time `j ≤ R`
appears in the finite observed-prefix family. -/
theorem imagePrefix_mem_observedPrefixes
    (m R j : ℕ) (hj : j ≤ R) (x : UnitAddCircle) (hx : x ∈ X) :
    imagePrefix m j x ∈ observedPrefixes m R := by
  let jf : Fin (R + 1) := ⟨j, by omega⟩
  let cutoff : ℕ := m + 2 * j + 1
  have hcutoff : cutoff < m + 2 * jf.val + 2 := by
    simp [cutoff, jf]
  rcases hx with rfl | ⟨k, rfl⟩
  · apply Finset.mem_image.mpr
    refine ⟨⟨jf, ⟨cutoff, hcutoff⟩⟩, Finset.mem_univ _, ?_⟩
    rw [indexedPrefix, imagePrefix_zero,
      imagePrefix_reciprocal_eq_zero_of_deep m j cutoff (by simp [cutoff])]
  · by_cases hk : k < m + 2 * j + 2
    · apply Finset.mem_image.mpr
      exact ⟨⟨jf, ⟨k, by simpa [jf] using hk⟩⟩, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_image.mpr
      refine ⟨⟨jf, ⟨cutoff, hcutoff⟩⟩, Finset.mem_univ _, ?_⟩
      rw [indexedPrefix,
        imagePrefix_reciprocal_eq_zero_of_deep m j k (by omega),
        imagePrefix_reciprocal_eq_zero_of_deep m j cutoff (by simp [cutoff])]

theorem inclusive_prefix_count_closed_form (m R : ℕ) :
    (∑ j ∈ Finset.range (R + 1), (m + 2 * j + 2)) =
      (R + 1) * (m + R + 2) := by
  calc
    (∑ j ∈ Finset.range (R + 1), (m + 2 * j + 2)) =
        ∑ j ∈ Finset.range (R + 1), ((m + 2) + 2 * j) := by
          apply Finset.sum_congr rfl
          intro j hj
          omega
    _ = (R + 1) * (m + 2) +
          (∑ j ∈ Finset.range (R + 1), j) * 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
          simp [Nat.mul_comm]
    _ = (R + 1) * (m + 2) + (R + 1) * R := by
          rw [Finset.sum_range_id_mul_two]
          simp
    _ = (R + 1) * (m + R + 2) := by ring

/-- The explicit counting inequality for the inclusive range
`0 ≤ j ≤ 2^m`. -/
theorem inclusive_prefix_count_lt_ten_pow (m : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range (2 ^ m + 1), (m + 2 * j + 2)) < 10 ^ m := by
  rw [inclusive_prefix_count_closed_form]
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hR : 4 ≤ 2 ^ m := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
      have hfive :
          (2 ^ (m + 1) + 1) * (m + 1 + 2 ^ (m + 1) + 2) ≤
            5 * ((2 ^ m + 1) * (m + 2 ^ m + 2)) := by
        rw [pow_succ]
        nlinarith
      rw [pow_succ]
      calc
        (2 ^ (m + 1) + 1) * (m + 1 + 2 ^ (m + 1) + 2) ≤
            5 * ((2 ^ m + 1) * (m + 2 ^ m + 2)) := hfive
        _ < 5 * 10 ^ m := by nlinarith
        _ < 10 ^ m * 10 := by nlinarith [show 0 < 10 ^ m by positivity]

theorem observedPrefixes_card_lt_all_words (m : ℕ) (hm : 2 ≤ m) :
    (observedPrefixes m (2 ^ m)).card < Fintype.card (Fin m → Fin 10) := by
  calc
    (observedPrefixes m (2 ^ m)).card ≤
        ∑ j ∈ Finset.range (2 ^ m + 1), (m + 2 * j + 2) :=
      observedPrefixes_card_le_prefix_count m (2 ^ m)
    _ < 10 ^ m := inclusive_prefix_count_lt_ten_pow m hm
    _ = Fintype.card (Fin m → Fin 10) := by simp

/-- A length-`m` digit vector outside every observed prefix through time
`2^m`. -/
noncomputable def omittedVector (m : ℕ) : Fin m → Fin 10 :=
  if hm : 2 ≤ m then
    Classical.choose (show ∃ u : Fin m → Fin 10,
        u ∉ observedPrefixes m (2 ^ m) by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin m → Fin 10)) ⊆
          observedPrefixes m (2 ^ m) := fun u _ => hall u
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ] at hle
      exact (Nat.not_le_of_lt (observedPrefixes_card_lt_all_words m hm)) hle)
  else fun _ => 0

/-- The moving omitted decimal word. -/
noncomputable def omittedWord (m : ℕ) : List (Fin 10) :=
  List.ofFn (omittedVector m)

@[simp] theorem omittedWord_length (m : ℕ) : (omittedWord m).length = m := by
  simp [omittedWord]

theorem omittedVector_not_mem (m : ℕ) (hm : 2 ≤ m) :
    omittedVector m ∉ observedPrefixes m (2 ^ m) := by
  rw [omittedVector, dif_pos hm]
  exact Classical.choose_spec (show ∃ u : Fin m → Fin 10,
      u ∉ observedPrefixes m (2 ^ m) by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin m → Fin 10)) ⊆
        observedPrefixes m (2 ^ m) := fun u _ => hall u
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    exact (Nat.not_le_of_lt (observedPrefixes_card_lt_all_words m hm)) hle)

/-- The selected word is absent from every canonical prefix at all inclusive
times `0 ≤ j ≤ 2^m`. -/
theorem omittedVector_ne_imagePrefix (m : ℕ) (hm : 2 ≤ m)
    (j : ℕ) (hj : j ≤ 2 ^ m) (x : UnitAddCircle) (hx : x ∈ X) :
    imagePrefix m j x ≠ omittedVector m := by
  intro heq
  apply omittedVector_not_mem m hm
  rw [← heq]
  exact imagePrefix_mem_observedPrefixes m (2 ^ m) j hj x hx

theorem unitCoordinate_circleMul_powTen (n : ℕ) (x : UnitAddCircle) :
    unitCoordinate (circleMul (10 ^ n) x) =
      baseTenOrbit (unitCoordinate x) n := by
  have hit : circleMul (10 ^ n) x =
      (((unitCoordinate x * (10 : ℝ) ^ n : ℝ) : UnitAddCircle)) := by
    calc
      circleMul (10 ^ n) x =
          circleMul (10 ^ n) ((unitCoordinate x : ℝ) : UnitAddCircle) := by
            rw [coe_unitCoordinate]
      _ = (((unitCoordinate x * (10 : ℝ) ^ n : ℝ) : UnitAddCircle)) := by
            simp only [circleMul, ← AddCircle.coe_nsmul, nsmul_eq_mul]
            apply congrArg (fun r : ℝ => (r : UnitAddCircle))
            push_cast
            ring
  rw [hit]
  change ((AddCircle.equivIco 1 0
      (((unitCoordinate x * (10 : ℝ) ^ n : ℝ) : UnitAddCircle)) :
        Set.Ico (0 : ℝ) (0 + 1)) : ℝ) =
    Int.fract ((10 : ℝ) ^ n * unitCoordinate x)
  rw [AddCircle.coe_equivIco_mk_apply]
  simp only [div_one, mul_one]
  apply congrArg Int.fract
  ring

/-- Canonical floor-based expansions shift exactly under multiplication by
`10^n`; T44's commutation then keeps the same times-16 level. -/
theorem imageExpansion_streamShift (j n : ℕ) (x : UnitAddCircle) :
    streamShift n (imageExpansion j x) =
      imageExpansion j (circleMul (10 ^ n) x) := by
  funext i
  have hcoord :
      unitCoordinate (circleMul (16 ^ j) (circleMul (10 ^ n) x)) =
        baseTenOrbit (unitCoordinate (circleMul (16 ^ j) x)) n := by
    rw [circleMul_commute]
    exact unitCoordinate_circleMul_powTen n (circleMul (16 ^ j) x)
  change decimalDigit (unitCoordinate (circleMul (16 ^ j) x)) (i + n) =
    decimalDigit (unitCoordinate (circleMul (16 ^ j)
      (circleMul (10 ^ n) x))) i
  rw [hcoord, decimalDigit_baseTenOrbit _ (unitCoordinate_nonneg _) n i]
  congr 1
  omega

theorem X_timesTen_iterate (x : UnitAddCircle) (hx : x ∈ X) (n : ℕ) :
    circleMul (10 ^ n) x ∈ X := by
  induction n with
  | zero => simpa [circleMul] using hx
  | succ n ih =>
      have hnext := X_forward_timesTen_invariant ih
      change circleMul 10 (circleMul (10 ^ n) x) ∈ X at hnext
      simpa [circleMul_comp, pow_succ, Nat.mul_comm] using hnext

/-- Prefix omission transfers to every factor in the chosen terminating
zero-tail expansion. -/
theorem imageExpansion_avoids_omittedWord (m : ℕ) (hm : 2 ≤ m)
    (j : ℕ) (hj : j ≤ 2 ^ m) (x : UnitAddCircle) (hx : x ∈ X) :
    AvoidsWord (omittedWord m) (imageExpansion j x) := by
  intro start hocc
  have hy : circleMul (10 ^ start) x ∈ X := X_timesTen_iterate x hx start
  have hprefix : imagePrefix m j (circleMul (10 ^ start) x) = omittedVector m := by
    funext i
    have hi : i.val < (omittedWord m).length := by simp
    have hdigit := hocc ⟨i.val, hi⟩
    change imageExpansion j (circleMul (10 ^ start) x) i.val = omittedVector m i
    rw [← imageExpansion_streamShift j start x]
    simpa [streamShift, omittedWord, List.get_eq_getElem, Nat.add_comm] using hdigit
  exact omittedVector_ne_imagePrefix m hm j hj _ hy hprefix

/-- For every `m ≥ 2`, the infinite set `X` lies in the depth-`2^m` core of
the exact length-`m` moving word. -/
theorem X_subset_Core_omittedWord_pow_two (m : ℕ) (hm : 2 ≤ m) :
    X ⊆ Core (omittedWord m) (2 ^ m) := by
  intro x hx n j hj
  let y := circleMul (10 ^ n) x
  have hy : y ∈ X := X_timesTen_iterate x hx n
  refine ⟨imageExpansion j y,
    imageExpansion_avoids_omittedWord m hm j hj y hy, ?_⟩
  exact imageExpansion_circleValue j y

/-- The constructed core is infinite, not merely nonempty. -/
theorem Core_omittedWord_pow_two_infinite (m : ℕ) (hm : 2 ≤ m) :
    (Core (omittedWord m) (2 ^ m)).Infinite :=
  X_infinite.mono (X_subset_Core_omittedWord_pow_two m hm)

/-- Exponential depth eventually dominates every real affine bound with
nonnegative slope. -/
theorem exists_two_pow_dominates_affine (L C : ℝ) (hL : 0 ≤ L) :
    ∃ m : ℕ, 2 ≤ m ∧ L * (m : ℝ) + C ≤ (2 ^ m : ℕ) := by
  let v : ℕ → ℝ := fun n => (2 : ℝ) ^ (n + 1) / (n + 2 : ℕ)
  have hv : Tendsto v atTop atTop := by
    apply tendsto_atTop_of_geom_le (v := v) (c := (4 / 3 : ℝ))
    · norm_num [v]
    · norm_num
    · intro n
      dsimp [v]
      rw [show n + 1 + 1 = n + 2 by omega,
        show n + 1 + 2 = n + 3 by omega, ← mul_div_assoc]
      have hn2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
      have hn3 : (0 : ℝ) < (n + 3 : ℕ) := by positivity
      rw [div_le_div_iff₀ hn2 hn3]
      have hcoef : (4 / 3 : ℝ) * (n + 3 : ℕ) ≤ 2 * (n + 2 : ℕ) := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ n by positivity]
      calc
        (4 / 3 : ℝ) * 2 ^ (n + 1) * (n + 3 : ℕ) =
            2 ^ (n + 1) * ((4 / 3 : ℝ) * (n + 3 : ℕ)) := by ring
        _ ≤ 2 ^ (n + 1) * (2 * (n + 2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = 2 ^ (n + 2) * (n + 2 : ℕ) := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          push_cast
          ring
  let D : ℝ := L + |C| + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith [abs_nonneg C]
  have hevent : ∀ᶠ n : ℕ in atTop, D < v n := hv.eventually_gt_atTop D
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let n := max N 1
  let m := n + 1
  have hnN : N ≤ n := by simp [n]
  have hn1 : 1 ≤ n := by simp [n]
  have hDv : D < v n := hN n hnN
  have hden : (0 : ℝ) < n + 2 := by positivity
  have hpow : D * (n + 2 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    exact (lt_div_iff₀ hden).mp (by simpa [v] using hDv)
  refine ⟨m, by simp [m, hn1], ?_⟩
  have haffine : L * (m : ℝ) + C ≤ D * (n + 2 : ℝ) := by
    dsimp [m, D]
    push_cast
    nlinarith [le_abs_self C, abs_nonneg C]
  calc
    L * (m : ℝ) + C ≤ D * (n + 2 : ℝ) := haffine
    _ ≤ (2 : ℝ) ^ (n + 1) := hpow.le
    _ = (2 ^ m : ℕ) := by simp [m]

/-- Expanded, exact quantifier-level failure of T44's universal predicate. -/
theorem not_uniformLinearFiniteCoreHypothesis_quantifiers :
    ∀ L C : ℝ, 0 ≤ L →
      ∃ w : List (Fin 10), w ≠ [] ∧
        ∀ r : ℕ, (r : ℝ) ≤ L * (w.length : ℝ) + C →
          (Core w r).Infinite := by
  intro L C hL
  obtain ⟨m, hm, hbound⟩ := exists_two_pow_dominates_affine L C hL
  refine ⟨omittedWord m, ?_, ?_⟩
  · intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · intro r hr
    have hrRreal : (r : ℝ) ≤ (2 ^ m : ℕ) := by
      simpa using hr.trans (by simpa using hbound)
    have hrR : r ≤ 2 ^ m := by exact_mod_cast hrRreal
    exact X_infinite.mono
      ((X_subset_Core_omittedWord_pow_two m hm).trans
        (core_antitone_radius (omittedWord m) hrR))

/-- Literal negation of the exact proposition imported from T44. -/
theorem not_uniformLinearFiniteCoreHypothesis :
    ¬ UniformLinearFiniteCoreHypothesis := by
  rintro ⟨L, C, hL, hcore⟩
  obtain ⟨w, hwne, hwitness⟩ :=
    not_uniformLinearFiniteCoreHypothesis_quantifiers L C hL
  obtain ⟨r, hr, hfinite⟩ := hcore w hwne
  exact (hwitness r hr) hfinite

/-- One named certificate exposing the exact length, `R = 2^m`, inclusive
prefix count, zero-tail convention, containment, and infinitude. -/
theorem movingWord_core_certificate (m : ℕ) (hm : 2 ≤ m) :
    let R := 2 ^ m
    IsCompact X ∧
      ForwardTimesTenInvariant X ∧
      X.Infinite ∧
      (omittedWord m).length = m ∧
      (∑ j ∈ Finset.range (R + 1), (m + 2 * j + 2)) < 10 ^ m ∧
      (∀ j : ℕ, j ≤ R → ∀ x : UnitAddCircle, x ∈ X →
        imagePrefix m j x ≠ omittedVector m) ∧
      (∀ j : ℕ, j ≤ R → ∀ x : UnitAddCircle, x ∈ X →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → imageExpansion j x n = 0) ∧
      X ⊆ Core (omittedWord m) R ∧
      (Core (omittedWord m) R).Infinite := by
  dsimp only
  exact ⟨X_isCompact, X_forward_timesTen_invariant, X_infinite,
    omittedWord_length m, inclusive_prefix_count_lt_ten_pow m hm,
    fun j hj x hx => omittedVector_ne_imagePrefix m hm j hj x hx,
    fun j hj x hx => imageExpansion_zero_tail j x hx,
    X_subset_Core_omittedWord_pow_two m hm,
    Core_omittedWord_pow_two_infinite m hm⟩

structure ScopeStatus where
  refutesT44UniversalLinearFiniteCore : Bool
  provesC6 : Bool
  disprovesC6 : Bool
  provesC1 : Bool
  disprovesC1 : Bool
  concernsPi : Bool
  deriving DecidableEq, Repr

def scopeStatus : ScopeStatus where
  refutesT44UniversalLinearFiniteCore := true
  provesC6 := false
  disprovesC6 := false
  provesC1 := false
  disprovesC1 := false
  concernsPi := false

/-- Formal scope marker: T57 refutes only T44's sufficient hypothesis and
asserts no C6, C1, or pi conclusion. -/
theorem exact_scope :
    scopeStatus.refutesT44UniversalLinearFiniteCore = true ∧
      scopeStatus.provesC6 = false ∧
      scopeStatus.disprovesC6 = false ∧
      scopeStatus.provesC1 = false ∧
      scopeStatus.disprovesC1 = false ∧
      scopeStatus.concernsPi = false := by
  norm_num [scopeStatus]

end DecimalFactorEntropy.T57MovingWordCoreObstruction

#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.X_isCompact
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.X_forward_timesTen_invariant
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.X_infinite
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.imageExpansion_reciprocal_zero_tail
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.prefixIndex_card
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.inclusive_prefix_count_lt_ten_pow
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.omittedVector_ne_imagePrefix
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.imageExpansion_streamShift
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.X_subset_Core_omittedWord_pow_two
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.Core_omittedWord_pow_two_infinite
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.not_uniformLinearFiniteCoreHypothesis_quantifiers
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.not_uniformLinearFiniteCoreHypothesis
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.movingWord_core_certificate
#print axioms DecimalFactorEntropy.T57MovingWordCoreObstruction.exact_scope
