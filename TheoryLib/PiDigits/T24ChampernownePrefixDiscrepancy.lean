import Mathlib.Data.Nat.Periodic
import TheoryLib.PiDigits.T22ChampernowneDisjunctive
import TheoryLib.PiDigits.T23ChampernowneEpochDiscrepancy

/-!
# T24: arbitrary finite prefixes of the Champernowne stream

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file concerns only the artificial Champernowne stream
`123456789101112...`.  It proves nothing about the decimal digits of pi,
canonical V1, or sibling V3.  In particular, the deliberately generous
coefficient below is not a normality result for pi or for any sibling statement.

The cutoff is represented by `q` complete `m`-digit integers and `r` digits
of the next integer.  This includes a cutoff inside an integer.  Occurrences
are counted by T23's filtered-start definition, so they overlap and include
integer boundaries, epoch boundaries, and the boundary before the terminal
partial integer.
-/

namespace Theory.PiDigits.T24

open Theory.PiDigits.T22 Theory.PiDigits.T23

/-- The complete epochs strictly before the length-`m` epoch. -/
noncomputable def completedEpochs (m : ℕ) : List (Fin 10) :=
  (List.range (m - 1)).flatMap fun j => epoch (j + 1)

/-- The first `q` complete `m`-digit integers and `r` digits of the next one. -/
def partialEpoch (m q r : ℕ) : List (Fin 10) :=
  (List.range' (10 ^ (m - 1)) q).flatMap decimalDigits ++
    (decimalDigits (10 ^ (m - 1) + q)).take r

/-- A finite Champernowne prefix ending during the length-`m` epoch. -/
noncomputable def champernownePrefix (m q r : ℕ) : List (Fin 10) :=
  completedEpochs m ++ partialEpoch m q r

/-- All overlapping occurrences in an arbitrary finite Champernowne prefix. -/
noncomputable def prefixOccurrenceCount
    (w : List (Fin 10)) (m q r : ℕ) : ℕ :=
  finiteContiguousOccurrenceCount w (champernownePrefix m q r)

/-- The same prefix indexed directly by its arbitrary digit cutoff in epoch `m`. -/
noncomputable def arbitraryPrefix (m t : ℕ) : List (Fin 10) :=
  completedEpochs m ++ (epoch m).take t

/-- All overlapping starts in the raw-cutoff prefix. -/
noncomputable def arbitraryPrefixOccurrenceCount
    (w : List (Fin 10)) (m t : ℕ) : ℕ :=
  finiteContiguousOccurrenceCount w (arbitraryPrefix m t)

/-- The fixed-length numerical value of a decimal word; leading zeros remain
part of the word even though they do not change this auxiliary value. -/
def wordValue (w : List (Fin 10)) : ℕ :=
  Nat.ofDigits 10 (w.map Fin.val).reverse

/-- A deliberately generous coefficient depending only on the word length. -/
def prefixDiscrepancyCoefficient (k : ℕ) : ℕ :=
  10 * (discrepancyCoefficient k + (k + 1) * (10 ^ k + 1)) +
    (2 + (k + 1) * (10 ^ k + 1)) + 10 ^ k * k + (10 ^ k + 1) * k

/-- The number of hits in an initial segment of a periodic residue slab. -/
def slabCount (base width value cutoff : ℕ) : ℕ :=
  Nat.count (fun n =>
    value * width ≤ n % (base * width) ∧
      n % (base * width) < (value + 1) * width) cutoff

theorem wordValue_lt_pow (w : List (Fin 10)) :
    wordValue w < 10 ^ w.length := by
  unfold wordValue
  have h := Nat.ofDigits_lt_base_pow_length (b := 10)
    (l := (w.map Fin.val).reverse) (by norm_num)
    (by
      intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt)
  simpa using h

private theorem decimalDigit_getD {n m j : ℕ}
    (hlen : (Nat.digits 10 n).length = m) (hj : j < m) :
    (decimalDigits n).getD j 0 =
      digitOfNat (n / 10 ^ (m - 1 - j) % 10) := by
  unfold decimalDigits
  change ((Nat.digits 10 n).reverse.map digitOfNat).getD j (digitOfNat 0) = _
  rw [List.getD_map]
  rw [List.getD_reverse _ (by simpa [hlen] using hj)]
  rw [hlen, Nat.getD_digits]
  norm_num

private theorem decimalDigits_length_of_interval {n m : ℕ}
    (hm : 1 ≤ m) (hlower : 10 ^ (m - 1) ≤ n) (hupper : n < 10 ^ m) :
    (decimalDigits n).length = m := by
  unfold decimalDigits
  simp only [List.length_map, List.length_reverse]
  apply Nat.le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num : 1 < (10 : ℕ)) n).mpr hupper
  · have hlowlen : m - 1 < (Nat.digits 10 n).length :=
      (Nat.lt_digits_length_iff (by norm_num : 1 < (10 : ℕ)) n).mpr hlower
    omega

private theorem digitOfNat_injective_of_lt {a b : ℕ}
    (ha : a < 10) (hb : b < 10) (h : digitOfNat a = digitOfNat b) : a = b := by
  have hv := congrArg Fin.val h
  simpa [digitOfNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

private theorem decimalDigits_map_val (n : ℕ) :
    (decimalDigits n).map Fin.val = (Nat.digits 10 n).reverse := by
  unfold decimalDigits
  rw [List.map_map]
  calc
    (Nat.digits 10 n).reverse.map (Fin.val ∘ digitOfNat) =
        (Nat.digits 10 n).reverse.map id := by
      apply List.map_congr_left
      intro d hd
      rw [List.mem_reverse] at hd
      exact Nat.mod_eq_of_lt (Nat.digits_lt_base (by norm_num) hd)
    _ = (Nat.digits 10 n).reverse := List.map_id _

private theorem reverse_slice (L : List ℕ) (m j k : ℕ)
    (hlen : L.length = m) (hjk : j + k ≤ m) :
    (((L.reverse.drop j).take k).reverse) =
      (L.drop (m - j - k)).take k := by
  have hleft : ((L.reverse.drop j).take k).length = k := by
    simp [hlen]
    omega
  have hright : ((L.drop (m - j - k)).take k).length = k := by
    simp [hlen]
    omega
  apply List.ext_getElem
  · rw [List.length_reverse, hleft, hright]
  · intro i hi₁ hi₂
    simp only [List.getElem_reverse, List.getElem_take, List.getElem_drop]
    congr 1
    rw [hleft, hlen]
    omega

private theorem wordValue_decimalSlice {n m j k : ℕ}
    (hlen : (Nat.digits 10 n).length = m) (hjk : j + k ≤ m) :
    wordValue ((decimalDigits n).drop j |>.take k) =
      n / 10 ^ (m - j - k) % 10 ^ k := by
  unfold wordValue
  rw [List.map_take, List.map_drop, decimalDigits_map_val]
  rw [reverse_slice (Nat.digits 10 n) m j k hlen hjk]
  rw [← Nat.ofDigits_mod_pow_eq_ofDigits_take k (by norm_num)
    ((Nat.digits 10 n).drop (m - j - k))]
  · rw [← Nat.self_div_pow_eq_ofDigits_drop (m - j - k) n (by norm_num)]
  · intro d hd
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_drop hd)

private theorem wordValue_injective_fixedLength {u v : List (Fin 10)}
    (hlen : u.length = v.length) (hvalue : wordValue u = wordValue v) : u = v := by
  have hraw : (u.map Fin.val).reverse = (v.map Fin.val).reverse := by
    apply Nat.ofDigits_inj_of_len_eq (by norm_num : 2 ≤ (10 : ℕ))
    · simp [hlen]
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · intro d hd
      rw [List.mem_reverse] at hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      exact x.isLt
    · exact hvalue
  have hmapped : u.map Fin.val = v.map Fin.val := by
    simpa using congrArg List.reverse hraw
  exact (List.map_injective_iff.mpr Fin.val_injective) hmapped

private theorem slabPredicate_periodic (base width value : ℕ) :
    Function.Periodic
      (fun n => value * width ≤ n % (base * width) ∧
        n % (base * width) < (value + 1) * width)
      (base * width) := by
  intro n
  simp only [Nat.add_mod_right]

private theorem slabCount_one_period (base width value : ℕ)
    (hbase : 1 ≤ base) (hwidth : 1 ≤ width) (hvalue : value < base) :
    slabCount base width value (base * width) = width := by
  unfold slabCount
  rw [Nat.count_eq_card_filter_range]
  have hfilter :
      (Finset.range (base * width)).filter (fun n =>
        value * width ≤ n % (base * width) ∧
          n % (base * width) < (value + 1) * width) =
        Finset.Ico (value * width) ((value + 1) * width) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have hp : 0 < base * width := Nat.mul_pos hbase hwidth
    constructor
    · rintro ⟨hn, hlower, hupper⟩
      rw [Nat.mod_eq_of_lt hn] at hlower hupper
      exact ⟨hlower, hupper⟩
    · rintro ⟨hlower, hupper⟩
      have htop : (value + 1) * width ≤ base * width := by
        exact Nat.mul_le_mul_right width (by omega)
      have hn : n < base * width := lt_of_lt_of_le hupper htop
      rw [Nat.mod_eq_of_lt hn]
      exact ⟨hn, hlower, hupper⟩
  rw [hfilter, Nat.card_Ico]
  simp [Nat.add_mul]

private theorem slabCount_mul_period (base width value a : ℕ)
    (hbase : 1 ≤ base) (hwidth : 1 ≤ width) (hvalue : value < base) :
    slabCount base width value (a * (base * width)) = a * width := by
  classical
  induction a with
  | zero => simp [slabCount]
  | succ a ih =>
      rw [Nat.succ_mul]
      unfold slabCount at ih ⊢
      rw [Nat.count_add]
      change Nat.count (fun n =>
            value * width ≤ n % (base * width) ∧
              n % (base * width) < (value + 1) * width)
            (a * (base * width)) +
          Nat.count (fun k =>
            value * width ≤ (a * (base * width) + k) % (base * width) ∧
              (a * (base * width) + k) % (base * width) <
                (value + 1) * width) (base * width) = _
      rw [ih]
      have hone := slabCount_one_period base width value hbase hwidth hvalue
      unfold slabCount at hone
      have hmod (k : ℕ) :
          (a * (base * width) + k) % (base * width) = k % (base * width) := by
        rw [Nat.add_comm, Nat.mul_comm a, Nat.add_mul_mod_self_left]
      simp_rw [hmod]
      calc
        a * width + Nat.count (fun n =>
            value * width ≤ n % (base * width) ∧
              n % (base * width) < (value + 1) * width) (base * width) =
            a * width + width := congrArg (a * width + ·) hone
        _ = (a + 1) * width := by rw [Nat.add_mul, one_mul]

/-- A periodic decimal cylinder has uniformly bounded initial-segment error. -/
theorem slabCount_discrepancy (base width value cutoff : ℕ)
    (hbase : 1 ≤ base) (hwidth : 1 ≤ width) (hvalue : value < base) :
    Int.natAbs
        (((base * slabCount base width value cutoff : ℕ) : ℤ) - cutoff) ≤
      base * width := by
  classical
  let period := base * width
  let a := cutoff / period
  let r := cutoff % period
  have hperiod : 0 < period := Nat.mul_pos hbase hwidth
  have hcutoff : cutoff = a * period + r := by
    simpa [a, r, period, Nat.mul_comm] using
      (Nat.div_add_mod cutoff (base * width)).symm
  have hr : r < period := by
    dsimp [r]
    exact Nat.mod_lt _ hperiod
  have hcount : slabCount base width value cutoff =
      a * width + slabCount base width value r := by
    rw [hcutoff]
    unfold slabCount
    rw [Nat.count_add]
    have hmul := slabCount_mul_period base width value a hbase hwidth hvalue
    unfold slabCount at hmul
    dsimp [period]
    rw [hmul]
    have hmod (k : ℕ) :
        (a * (base * width) + k) % (base * width) = k % (base * width) := by
      rw [Nat.add_comm, Nat.mul_comm a, Nat.add_mul_mod_self_left]
    simp_rw [hmod]
  let z := slabCount base width value r
  have hz : z ≤ r := by
    exact Nat.count_le _
  have hzwidth : z ≤ width := by
    have hmono := Nat.count_monotone
      (fun n => value * width ≤ n % (base * width) ∧
        n % (base * width) < (value + 1) * width) (Nat.le_of_lt hr)
    change z ≤ slabCount base width value period at hmono
    rw [slabCount_one_period base width value hbase hwidth hvalue] at hmono
    exact hmono
  have hleft : base * z ≤ period := by
    dsimp [period]
    exact Nat.mul_le_mul_left base hzwidth
  have habs : Int.natAbs (((base * z : ℕ) : ℤ) - r) ≤ period := by
    exact Int.natAbs_coe_sub_coe_le_of_le hleft (Nat.le_of_lt hr)
  rw [hcount, hcutoff]
  have heq :
      (((base * (a * width + z) : ℕ) : ℤ) - ((a * period + r : ℕ) : ℤ)) =
        (((base * z : ℕ) : ℤ) - r) := by
    dsimp [period]
    push_cast
    ring
  rw [heq]
  exact habs

/-- Occurrences at one fixed nonleading offset among the first `q` integers. -/
def regularPositionCount (w : List (Fin 10)) (m q j : ℕ) : ℕ :=
  Nat.count (fun i =>
    ((decimalDigits (10 ^ (m - 1) + i)).drop j).take w.length = w) q

private theorem decimalSlice_iff_slab
    (w : List (Fin 10)) (m k j i q : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hj : 1 ≤ j) (hjk : j + k ≤ m)
    (hi : i < q) (hq : q ≤ 9 * 10 ^ (m - 1)) :
    ((decimalDigits (10 ^ (m - 1) + i)).drop j).take k = w ↔
      wordValue w * 10 ^ (m - j - k) ≤
        i % (10 ^ k * 10 ^ (m - j - k)) ∧
      i % (10 ^ k * 10 ^ (m - j - k)) <
        (wordValue w + 1) * 10 ^ (m - j - k) := by
  let n := 10 ^ (m - 1) + i
  let width := 10 ^ (m - j - k)
  let base := 10 ^ k
  let period := base * width
  have hm1 : 1 ≤ m := le_trans hk hm
  have hi' : i < 9 * 10 ^ (m - 1) := lt_of_lt_of_le hi hq
  have hnlow : 10 ^ (m - 1) ≤ n := by simp [n]
  have hpowm : 10 ^ m = 10 ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  have hnupper : n < 10 ^ m := by
    dsimp [n]
    rw [hpowm]
    omega
  have hlen : (Nat.digits 10 n).length = m := by
    simpa [decimalDigits] using
      decimalDigits_length_of_interval hm1 hnlow hnupper
  have hslicelen : (((decimalDigits n).drop j).take k).length = k := by
    have hdlen : (decimalDigits n).length = m := by
      simpa [decimalDigits] using hlen
    simp [hdlen]
    omega
  have hwidth : 0 < width := pow_pos (by norm_num) _
  have hbase : 0 < base := pow_pos (by norm_num) _
  have hperiod : period = 10 ^ (m - j) := by
    dsimp [period, base, width]
    rw [← pow_add]
    congr 1
    omega
  have hperiod_dvd : period ∣ 10 ^ (m - 1) := by
    rw [hperiod]
    refine ⟨10 ^ (j - 1), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hnmod : n % period = i % period := by
    dsimp [n]
    rw [Nat.add_mod]
    rw [Nat.mod_eq_zero_of_dvd hperiod_dvd]
    simp
  have hquotient : n / width % base = n % period / width := by
    rw [Nat.mod_mul_left_div_self]
  have hdiv_iff (x v : ℕ) : x / width = v ↔ v * width ≤ x ∧ x < (v + 1) * width := by
    constructor
    · intro h
      constructor
      · simpa [h, Nat.mul_comm] using Nat.div_mul_le_self x width
      · have hmodlt := Nat.mod_lt x hwidth
        have hdecomp := Nat.div_add_mod' x width
        rw [h] at hdecomp
        calc
          x = v * width + x % width := hdecomp.symm
          _ < v * width + width := Nat.add_lt_add_left hmodlt _
          _ = (v + 1) * width := by rw [Nat.add_mul, one_mul]
    · rintro ⟨hlower, hupper⟩
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hwidth).mpr hupper)
      · exact (Nat.le_div_iff_mul_le hwidth).mpr hlower
  have hword : wordValue (((decimalDigits n).drop j).take k) =
      n / width % base := by
    simpa [n, width, base] using wordValue_decimalSlice hlen hjk
  constructor
  · intro hslice
    have hvalue : n / width % base = wordValue w := by
      rw [← hword, hslice]
    have hresidue : i % period / width = wordValue w := by
      rw [← hnmod, ← hquotient]
      exact hvalue
    exact (hdiv_iff (i % period) (wordValue w)).mp hresidue
  · intro hslab
    have hresidue : i % period / width = wordValue w :=
      (hdiv_iff (i % period) (wordValue w)).mpr hslab
    have hvalue : wordValue (((decimalDigits n).drop j).take k) = wordValue w := by
      rw [hword, hquotient, hnmod, hresidue]
    apply wordValue_injective_fixedLength
    · simpa [hwlen] using hslicelen
    · exact hvalue

theorem regularPositionCount_eq_slab
    (w : List (Fin 10)) (m k q j : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hj : 1 ≤ j) (hjk : j + k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) :
    regularPositionCount w m q j =
      slabCount (10 ^ k) (10 ^ (m - j - k)) (wordValue w) q := by
  unfold regularPositionCount slabCount
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rw [hwlen]
  exact decimalSlice_iff_slab w m k j i q hwlen hk hm hj hjk
    (Finset.mem_range.mp hi) hq

theorem regularPositionCount_discrepancy
    (w : List (Fin 10)) (m k q j : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hj : 1 ≤ j) (hjk : j + k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) :
    Int.natAbs
        (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q) ≤
      10 ^ (m - j) := by
  rw [regularPositionCount_eq_slab w m k q j hwlen hk hm hj hjk hq]
  have h := slabCount_discrepancy
    (10 ^ k) (10 ^ (m - j - k)) (wordValue w) q
    (pow_pos (by norm_num : 0 < (10 : ℕ)) _)
    (pow_pos (by norm_num : 0 < (10 : ℕ)) _) (by
      simpa [hwlen] using wordValue_lt_pow w)
  convert h using 1
  rw [← pow_add]
  congr 2
  omega

/-- The count at all nonleading internal offsets of the first `q` integers. -/
def regularInternalCount (w : List (Fin 10)) (m q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (m - w.length), regularPositionCount w m q j

theorem regularInternalCount_discrepancy
    (w : List (Fin 10)) (m k q : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) :
    Int.natAbs
        (((10 ^ k * regularInternalCount w m q : ℕ) : ℤ) -
          (((m - k) * q : ℕ) : ℤ)) ≤
      10 ^ m := by
  classical
  let S := Finset.Icc 1 (m - k)
  have hterm (j : ℕ) (hjS : j ∈ S) :
      Int.natAbs
          (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q) ≤
        10 ^ (m - j) := by
    have hj := Finset.mem_Icc.mp hjS
    exact regularPositionCount_discrepancy w m k q j hwlen hk hm hj.1 (by omega) hq
  have hsum :
      Int.natAbs
          (∑ j ∈ S,
            (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q)) ≤
        ∑ j ∈ S, 10 ^ (m - j) := by
    calc
      Int.natAbs
          (∑ j ∈ S,
            (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q)) ≤
          ∑ j ∈ S,
            Int.natAbs
              (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q) :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ j ∈ S, 10 ^ (m - j) := by
        apply Finset.sum_le_sum
        intro j hjS
        exact hterm j hjS
  have hreindex :
      (∑ j ∈ S, 10 ^ (m - j)) =
        ∑ e ∈ Finset.Icc k (m - 1), 10 ^ e := by
    apply Finset.sum_bij (fun j _ => m - j)
    · intro j hjS
      simp only [S, Finset.mem_Icc] at hjS ⊢
      omega
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [S, Finset.mem_Icc] at hj₁ hj₂
      omega
    · intro e he
      simp only [Finset.mem_Icc] at he
      refine ⟨m - e, ?_, ?_⟩
      · simp only [S, Finset.mem_Icc]
        omega
      · omega
    · intro j hjS
      rfl
  have hgeom : (∑ j ∈ S, 10 ^ (m - j)) ≤ 10 ^ m := by
    rw [hreindex]
    exact (Nat.geomSum_lt (m := 10) (n := m) (by norm_num) (by
      intro e he
      exact (Finset.mem_Icc.mp he).2.trans_lt (by omega))).le
  have heq :
      (((10 ^ k * regularInternalCount w m q : ℕ) : ℤ) -
          (((m - k) * q : ℕ) : ℤ)) =
        ∑ j ∈ S,
          (((10 ^ k * regularPositionCount w m q j : ℕ) : ℤ) - q) := by
    unfold regularInternalCount
    rw [hwlen]
    dsimp [S]
    push_cast
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
    simp [Nat.card_Icc]
  rw [heq]
  exact hsum.trans hgeom

/-- Complete `m`-digit integers before the optional terminal fragment. -/
def completeIntegerPrefix (m q : ℕ) : List (Fin 10) :=
  (List.range' (10 ^ (m - 1)) q).flatMap decimalDigits

/-- Starts crossing the join in an append. -/
def appendCrossingCount (w A B : List (Fin 10)) : ℕ :=
  ((Finset.range (w.length - 1)).filter fun t =>
    ((A ++ B).drop (A.length + 1 - w.length + t)).take w.length = w).card

private theorem append_slice_internal (w A B : List (Fin 10)) (i : ℕ)
    (hi : i < A.length + 1 - w.length) :
    ((A ++ B).drop i).take w.length = (A.drop i).take w.length := by
  rw [List.drop_append, List.take_append]
  have hiA : i ≤ A.length := by omega
  have hki : w.length ≤ A.length - i := by omega
  have hdrop : (A.drop i).length = A.length - i := by simp
  have hsub : i - A.length = 0 := by omega
  have hzero : w.length - (A.drop i).length = 0 := by omega
  rw [hsub, hzero, List.take_zero, List.append_nil]

private theorem append_slice_tail (w A B : List (Fin 10)) (j : ℕ) :
    ((A ++ B).drop (A.length + j)).take w.length =
      (B.drop j).take w.length := by
  rw [List.drop_append]
  have hsub : A.length + j - A.length = j := by omega
  have hdrop : A.drop (A.length + j) = [] :=
    List.drop_eq_nil_iff.mpr (by omega)
  rw [hsub, hdrop, List.nil_append]

/-- Exact generic append partition: internal starts, crossing starts, and tail
starts. T23's analogous implementation is private; this small interface is
needed to combine the imported T23 endpoint estimate without reproving it. -/
theorem occurrenceCount_append
    (w A B : List (Fin 10))
    (hw : 1 ≤ w.length) (hwA : w.length ≤ A.length)
    (hwB : w.length ≤ B.length) :
    finiteContiguousOccurrenceCount w (A ++ B) =
      finiteContiguousOccurrenceCount w A + appendCrossingCount w A B +
        finiteContiguousOccurrenceCount w B := by
  classical
  unfold finiteContiguousOccurrenceCount appendCrossingCount
  rw [List.length_append]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have htotal : A.length + B.length + 1 - w.length =
      (A.length + 1 - w.length) +
        ((w.length - 1) + (B.length + 1 - w.length)) := by
    omega
  rw [htotal, Finset.sum_range_add, Finset.sum_range_add]
  rw [← Nat.add_assoc]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      rw [append_slice_internal w A B i (Finset.mem_range.mp hi)]
    · rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have hindex : A.length + 1 - w.length + (w.length - 1 + j) =
        A.length + j := by omega
    rw [hindex, append_slice_tail]

theorem appendCrossingCount_le (w A B : List (Fin 10)) :
    appendCrossingCount w A B ≤ w.length - 1 := by
  unfold appendCrossingCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

private def blockInternalCount (w block : List (Fin 10)) (m : ℕ) : ℕ :=
  ((Finset.range (m + 1 - w.length)).filter fun j =>
    (block.drop j).take w.length = w).card

private theorem blockInternalCount_eq_occurrenceCount
    (w block : List (Fin 10)) (m : ℕ) (hlen : block.length = m) :
    blockInternalCount w block m = finiteContiguousOccurrenceCount w block := by
  simp [blockInternalCount, finiteContiguousOccurrenceCount, hlen]

private theorem blockInternalCount_split
    (w block : List (Fin 10)) (m : ℕ) (hwm : w.length ≤ m) :
    blockInternalCount w block m =
      (∑ j ∈ Finset.Icc 1 (m - w.length),
        if (block.drop j).take w.length = w then 1 else 0) +
      (if block.take w.length = w then 1 else 0) := by
  unfold blockInternalCount
  rw [Finset.card_filter]
  rw [show m + 1 - w.length = (m - w.length) + 1 by omega]
  rw [Finset.sum_range_succ']
  apply congrArg₂ (· + ·)
  · apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      simp only [Finset.mem_Icc]
      have := Finset.mem_range.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ heq
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨j - 1, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro i hi
      rfl
  · simp

private def regularBlockCount
    (w : List (Fin 10)) (m n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (m - w.length),
    if ((decimalDigits n).drop j).take w.length = w then 1 else 0

private def leadingBlockCount (w : List (Fin 10)) (n : ℕ) : ℕ :=
  if (decimalDigits n).take w.length = w then 1 else 0

private theorem leadingBlockCount_le_one (w : List (Fin 10)) (n : ℕ) :
    leadingBlockCount w n ≤ 1 := by
  unfold leadingBlockCount
  split <;> omega

private theorem current_mDigit_length
    (m q : ℕ) (hm : 1 ≤ m) (hq : q < 9 * 10 ^ (m - 1)) :
    (decimalDigits (10 ^ (m - 1) + q)).length = m := by
  have hpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  apply decimalDigits_length_of_interval hm
  · omega
  · rw [hpow]
    omega

private theorem completeIntegerPrefix_succ (m q : ℕ) :
    completeIntegerPrefix m (q + 1) =
      completeIntegerPrefix m q ++ decimalDigits (10 ^ (m - 1) + q) := by
  unfold completeIntegerPrefix
  rw [← List.range'_append]
  simp

private theorem completeIntegerPrefix_length
    (m q : ℕ) (hm : 1 ≤ m) (hq : q ≤ 9 * 10 ^ (m - 1)) :
    (completeIntegerPrefix m q).length = q * m := by
  induction q with
  | zero => simp [completeIntegerPrefix]
  | succ q ih =>
      have hq' : q ≤ 9 * 10 ^ (m - 1) := by omega
      have hqlt : q < 9 * 10 ^ (m - 1) := by omega
      rw [completeIntegerPrefix_succ, List.length_append,
        current_mDigit_length m q hm hqlt, ih hq']
      rw [Nat.add_mul, one_mul]

theorem epoch_eq_completeIntegerPrefix (m : ℕ) (hm : 1 ≤ m) :
    epoch m = completeIntegerPrefix m (9 * 10 ^ (m - 1)) := by
  unfold epoch completeIntegerPrefix
  rw [mDigitPositiveIntegers_eq_range m hm]

/-- The `(q,r)` representation is exactly the digit cutoff `q*m+r` in T23's
epoch.  Consequently it includes a genuinely partial final integer when
`0 < r < m`, rather than rounding the cutoff to an integer boundary. -/
theorem partialEpoch_eq_epoch_take
    (m q r : ℕ) (hm : 1 ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) (hr : r ≤ m)
    (hend : q = 9 * 10 ^ (m - 1) → r = 0) :
    partialEpoch m q r = (epoch m).take (q * m + r) := by
  let total := 9 * 10 ^ (m - 1)
  let start := 10 ^ (m - 1)
  let A := completeIntegerPrefix m q
  let R := (List.range' (start + q) (total - q)).flatMap decimalDigits
  have hAlen : A.length = q * m :=
    completeIntegerPrefix_length m q hm (by simpa [total] using hq)
  have hfull : completeIntegerPrefix m total = A ++ R := by
    unfold completeIntegerPrefix A R
    have htotal : total = q + (total - q) := by
      dsimp [total]
      omega
    conv_lhs => rw [htotal, ← List.range'_append]
    rw [List.flatMap_append]
    simp [A, R, start, completeIntegerPrefix, Nat.mul_comm]
  rw [epoch_eq_completeIntegerPrefix m hm, hfull]
  by_cases hqt : q = total
  · have hrzero : r = 0 := hend (by simpa [total] using hqt)
    subst r
    have hRnil : R = [] := by simp [R, hqt]
    rw [hRnil, List.append_nil]
    unfold partialEpoch
    simp only [List.take_zero, List.append_nil]
    rw [List.take_of_length_le]
    · simp [A, completeIntegerPrefix]
    · dsimp [A] at hAlen ⊢
      rw [hAlen]
  · have hqlt : q < total := lt_of_le_of_ne (by simpa [total] using hq) hqt
    have hR : R = decimalDigits (start + q) ++
        (List.range' (start + q + 1) (total - q - 1)).flatMap decimalDigits := by
      unfold R
      rw [show total - q = (total - q - 1) + 1 by omega]
      simp [List.range'_succ, List.flatMap_append, Nat.add_assoc]
    rw [hR]
    unfold partialEpoch A start
    rw [List.take_append]
    rw [hAlen]
    have htakeA : (completeIntegerPrefix m q).take (q * m + r) =
        completeIntegerPrefix m q := List.take_of_length_le (by
          rw [completeIntegerPrefix_length m q hm hq]
          omega)
    rw [htakeA]
    rw [Nat.add_sub_cancel_left, List.take_append]
    have hblocklen := current_mDigit_length m q hm (by simpa [total] using hqlt)
    have hzero : r - (decimalDigits (10 ^ (m - 1) + q)).length = 0 := by
      rw [hblocklen]
      omega
    rw [hzero, List.take_zero, List.append_nil]
    rfl

private theorem shiftedFiniteConcat_eq_completeIntegerPrefix (m q : ℕ) :
    finiteConcat
        (fun j => champernowneBlocks ((10 ^ (m - 1) - 1) + j)) q =
      completeIntegerPrefix m q := by
  induction q with
  | zero => simp [completeIntegerPrefix]
  | succ q ih =>
      rw [finiteConcat_succ, completeIntegerPrefix_succ, ih]
      unfold champernowneBlocks
      have hp : 0 < 10 ^ (m - 1) := pow_pos (by norm_num) _
      apply congrArg (completeIntegerPrefix m q ++ ·)
      apply congrArg decimalDigits
      calc
        10 ^ (m - 1) - 1 + q + 1 = (10 ^ (m - 1) - 1 + 1) + q := by omega
        _ = 10 ^ (m - 1) + q := by rw [Nat.sub_add_cancel hp]

private theorem completedEpochs_succ_bridge (m : ℕ) (hm : 1 ≤ m) :
    completedEpochs (m + 1) = completedEpochs m ++ epoch m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp [completedEpochs, List.range_succ, List.flatMap_append, Nat.add_comm]

/-- The complete earlier epochs are T22's canonical initial integer blocks. -/
theorem completedEpochs_eq_finiteConcat (m : ℕ) (hm : 1 ≤ m) :
    completedEpochs m =
      finiteConcat champernowneBlocks (10 ^ (m - 1) - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hmzero : m = 0
      · subst m
        simp [completedEpochs]
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmzero
        rw [completedEpochs_succ_bridge m hm1, ih hm1]
        change finiteConcat champernowneBlocks (10 ^ (m - 1) - 1) ++ epoch m =
          finiteConcat champernowneBlocks (10 ^ m - 1)
        have hpow : 10 ^ m - 1 =
            (10 ^ (m - 1) - 1) + 9 * 10 ^ (m - 1) := by
          have hp : 10 ^ m = 10 ^ (m - 1) * 10 := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
          rw [hp]
          omega
        rw [hpow, finiteConcat_add]
        apply congrArg
          (finiteConcat champernowneBlocks (10 ^ (m - 1) - 1) ++ ·)
        calc
          epoch m = completeIntegerPrefix m (9 * 10 ^ (m - 1)) :=
            epoch_eq_completeIntegerPrefix m hm1
          _ = finiteConcat
                (fun j => champernowneBlocks ((10 ^ (m - 1) - 1) + j))
                (9 * 10 ^ (m - 1)) :=
            (shiftedFiniteConcat_eq_completeIntegerPrefix m _).symm

private theorem finiteConcat_getElem_eq_concatStream
    {α : Type*} [Inhabited α] (blocks : ℕ → List α)
    (hne : ∀ j, blocks j ≠ []) (n i : ℕ)
    (hi : i < (finiteConcat blocks n).length) :
    (finiteConcat blocks n)[i] = concatStream blocks i := by
  induction n with
  | zero => simp at hi
  | succ n ih =>
      rw [finiteConcat_succ] at hi
      change (finiteConcat blocks n ++ blocks n)[i] = concatStream blocks i
      by_cases hiprev : i < (finiteConcat blocks n).length
      · rw [List.getElem_append_left hiprev]
        exact ih hiprev
      · have hj : i - (finiteConcat blocks n).length < (blocks n).length := by
          rw [List.length_append] at hi
          omega
        rw [List.getElem_append_right (by omega)]
        have hcoverage := enumeratedBlock_occursAt_concatStream
          blocks hne n (i - (finiteConcat blocks n).length) hj
        rw [show (finiteConcat blocks n).length +
            (i - (finiteConcat blocks n).length) = i by omega] at hcoverage
        exact hcoverage.symm

/-- Every raw-cutoff prefix is extensionally the corresponding prefix of
T22's canonical infinite `champernowneDigit` stream. -/
theorem arbitraryPrefix_eq_champernowneDigit_prefix
    (m t : ℕ) (hm : 1 ≤ m) (ht : t ≤ (epoch m).length) :
    arbitraryPrefix m t =
      List.ofFn (fun i : Fin (arbitraryPrefix m t).length => champernowneDigit i) := by
  let before := 10 ^ (m - 1) - 1
  let count := 9 * 10 ^ (m - 1)
  have hfull : completedEpochs m ++ epoch m =
      finiteConcat champernowneBlocks (before + count) := by
    rw [completedEpochs_eq_finiteConcat m hm,
      epoch_eq_completeIntegerPrefix m hm,
      ← shiftedFiniteConcat_eq_completeIntegerPrefix]
    exact (finiteConcat_add champernowneBlocks before count).symm
  have htake : arbitraryPrefix m t = (completedEpochs m ++ epoch m).take
      ((completedEpochs m).length + t) := by
    unfold arbitraryPrefix
    rw [List.take_append]
    have hleft : (completedEpochs m).take ((completedEpochs m).length + t) =
        completedEpochs m := List.take_of_length_le (by omega)
    rw [hleft]
    simp
  have hlen : (arbitraryPrefix m t).length = (completedEpochs m).length + t := by
    unfold arbitraryPrefix
    rw [List.length_append, List.length_take_of_le ht]
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn]
    have hifull : i < (finiteConcat champernowneBlocks (before + count)).length := by
      rw [← hfull, List.length_append]
      rw [hlen] at hi₁
      omega
    have hstream := finiteConcat_getElem_eq_concatStream
      champernowneBlocks champernowneBlocks_ne_nil (before + count) i hifull
    have htake' : arbitraryPrefix m t =
        (completedEpochs m ++ epoch m).take (arbitraryPrefix m t).length := by
      simpa [hlen] using htake
    have hitake : i < ((completedEpochs m ++ epoch m).take
        (arbitraryPrefix m t).length).length := by
      rw [← htake']
      exact hi₁
    have hprefOpt := congrArg (fun L : List (Fin 10) => L[i]?) htake'
    change (arbitraryPrefix m t)[i]? =
      ((completedEpochs m ++ epoch m).take (arbitraryPrefix m t).length)[i]? at hprefOpt
    rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hitake] at hprefOpt
    have hprefElem := Option.some.inj hprefOpt
    rw [List.getElem_take] at hprefElem
    have hifullList : i < (completedEpochs m ++ epoch m).length := by
      rw [hfull]
      exact hifull
    have hfullOpt := congrArg (fun L : List (Fin 10) => L[i]?) hfull
    change (completedEpochs m ++ epoch m)[i]? =
      (finiteConcat champernowneBlocks (before + count))[i]? at hfullOpt
    rw [List.getElem?_eq_getElem hifullList,
      List.getElem?_eq_getElem hifull] at hfullOpt
    have hfullElem := Option.some.inj hfullOpt
    change (arbitraryPrefix m t)[i] = champernowneDigit i
    calc
      (arbitraryPrefix m t)[i] = (completedEpochs m ++ epoch m)[i] := hprefElem
      _ = (finiteConcat champernowneBlocks (before + count))[i] := hfullElem
      _ = champernowneDigit i := hstream

private theorem regularInternalCount_succ
    (w : List (Fin 10)) (m q : ℕ) :
    regularInternalCount w m (q + 1) =
      regularInternalCount w m q +
        regularBlockCount w m (10 ^ (m - 1) + q) := by
  classical
  unfold regularInternalCount regularPositionCount regularBlockCount
  simp_rw [Nat.count_succ]
  rw [Finset.sum_add_distrib]

private theorem oneBlock_decomposition
    (w : List (Fin 10)) (m n : ℕ)
    (hwm : w.length ≤ m) (hlen : (decimalDigits n).length = m) :
    finiteContiguousOccurrenceCount w (decimalDigits n) =
      regularBlockCount w m n + leadingBlockCount w n := by
  rw [← blockInternalCount_eq_occurrenceCount w (decimalDigits n) m hlen]
  exact blockInternalCount_split w (decimalDigits n) m hwm

/-- The actual filtered-start count on an incomplete epoch is the balanced
nonleading count plus at most `k*q` exceptional leading and boundary starts. -/
theorem completeIntegerPrefix_occurrence_decomposition
    (w : List (Fin 10)) (m k q : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) :
    ∃ R : ℕ, R ≤ k * q ∧
      finiteContiguousOccurrenceCount w (completeIntegerPrefix m q) =
        regularInternalCount w m q + R := by
  have hm1 : 1 ≤ m := le_trans hk hm
  induction q with
  | zero =>
      refine ⟨0, by simp, ?_⟩
      have hwne : w ≠ [] := by
        intro h
        subst w
        simp at hwlen
        omega
      simp [completeIntegerPrefix, regularInternalCount, regularPositionCount,
        finiteContiguousOccurrenceCount, hwne]
  | succ q ih =>
      have hq' : q ≤ 9 * 10 ^ (m - 1) := by omega
      have hqlt : q < 9 * 10 ^ (m - 1) := by omega
      have hblocklen := current_mDigit_length m q hm1 hqlt
      have hblock := oneBlock_decomposition w m (10 ^ (m - 1) + q)
        (by simpa [hwlen] using hm) hblocklen
      obtain ⟨R, hR, hcount⟩ := ih hq'
      by_cases hqzero : q = 0
      · subst q
        refine ⟨leadingBlockCount w (10 ^ (m - 1)), ?_, ?_⟩
        · have hlead := leadingBlockCount_le_one w (10 ^ (m - 1))
          omega
        · rw [completeIntegerPrefix_succ]
          simp only [completeIntegerPrefix, List.range'_zero, List.flatMap_nil,
            List.nil_append]
          rw [hblock, regularInternalCount_succ]
          simp [regularInternalCount, regularPositionCount]
      · let old := completeIntegerPrefix m q
        let block := decimalDigits (10 ^ (m - 1) + q)
        have holdlen : old.length = q * m :=
          completeIntegerPrefix_length m q hm1 hq'
        have hwold : w.length ≤ old.length := by
          rw [hwlen, holdlen]
          have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hqzero
          nlinarith
        have hwblock : w.length ≤ block.length := by
          rw [hwlen, hblocklen]
          exact hm
        have happend := occurrenceCount_append w old block
          (by simpa [hwlen] using hk) hwold hwblock
        let X := appendCrossingCount w old block
        have hX : X ≤ k - 1 := by
          simpa [X, hwlen] using appendCrossingCount_le w old block
        refine ⟨R + leadingBlockCount w (10 ^ (m - 1) + q) + X, ?_, ?_⟩
        · have hlead := leadingBlockCount_le_one w (10 ^ (m - 1) + q)
          calc
            R + leadingBlockCount w (10 ^ (m - 1) + q) + X ≤
                k * q + 1 + (k - 1) := Nat.add_le_add (Nat.add_le_add hR hlead) hX
            _ = k * (q + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
        · rw [completeIntegerPrefix_succ]
          change finiteContiguousOccurrenceCount w (old ++ block) = _
          rw [happend, hcount, hblock, regularInternalCount_succ]
          dsimp [X]
          omega

theorem completeIntegerPrefix_discrepancy
    (w : List (Fin 10)) (m k q : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) :
    Int.natAbs
        (((10 ^ k * finiteContiguousOccurrenceCount w
            (completeIntegerPrefix m q) : ℕ) : ℤ) -
          ((completeIntegerPrefix m q).length : ℤ)) ≤
      (1 + k * (10 ^ k + 1)) * 10 ^ m := by
  have hm1 : 1 ≤ m := le_trans hk hm
  obtain ⟨R, hR, hcount⟩ :=
    completeIntegerPrefix_occurrence_decomposition w m k q hwlen hk hm hq
  have hregular := regularInternalCount_discrepancy w m k q hwlen hk hm hq
  have hlen := completeIntegerPrefix_length m q hm1 hq
  have hpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
  have hqpow : q ≤ 10 ^ m := by
    rw [hpow]
    nlinarith
  have hRabs :
      Int.natAbs ((((10 ^ k * R : ℕ) : ℤ) - ((k * q : ℕ) : ℤ))) ≤
        k * (10 ^ k + 1) * 10 ^ m := by
    calc
      Int.natAbs ((((10 ^ k * R : ℕ) : ℤ) - ((k * q : ℕ) : ℤ))) =
          Int.natAbs (((10 ^ k * R : ℕ) : ℤ) + (-((k * q : ℕ) : ℤ))) := by
        congr 1
      _ ≤ Int.natAbs ((10 ^ k * R : ℕ) : ℤ) +
          Int.natAbs (-((k * q : ℕ) : ℤ)) := Int.natAbs_add_le _ _
      _ = 10 ^ k * R + k * q := by
        simp only [Int.natAbs_neg, Int.natAbs_natCast]
      _ ≤ 10 ^ k * (k * q) + k * q := by gcongr
      _ = k * (10 ^ k + 1) * q := by ring
      _ ≤ k * (10 ^ k + 1) * 10 ^ m := by gcongr
  have heq :
      (((10 ^ k * finiteContiguousOccurrenceCount w
          (completeIntegerPrefix m q) : ℕ) : ℤ) -
        ((completeIntegerPrefix m q).length : ℤ)) =
        ((((10 ^ k * regularInternalCount w m q : ℕ) : ℤ) -
            (((m - k) * q : ℕ) : ℤ)) +
          (((10 ^ k * R : ℕ) : ℤ) - ((k * q : ℕ) : ℤ))) := by
    rw [hcount, hlen]
    have hmk : m = (m - k) + k := by omega
    have hlengthdecomp : q * m = (m - k) * q + k * q := by
      calc
        q * m = q * ((m - k) + k) := congrArg (q * ·) hmk
        _ = (m - k) * q + k * q := by ring
    rw [hlengthdecomp]
    push_cast
    ring
  rw [heq]
  calc
    Int.natAbs
        (((((10 ^ k * regularInternalCount w m q : ℕ) : ℤ) -
            (((m - k) * q : ℕ) : ℤ)) +
          (((10 ^ k * R : ℕ) : ℤ) - ((k * q : ℕ) : ℤ)))) ≤
        Int.natAbs
            (((10 ^ k * regularInternalCount w m q : ℕ) : ℤ) -
              (((m - k) * q : ℕ) : ℤ)) +
          Int.natAbs (((10 ^ k * R : ℕ) : ℤ) - ((k * q : ℕ) : ℤ)) :=
      Int.natAbs_add_le _ _
    _ ≤ 10 ^ m + k * (10 ^ k + 1) * 10 ^ m :=
      Nat.add_le_add hregular hRabs
    _ = (1 + k * (10 ^ k + 1)) * 10 ^ m := by ring

/-- Appending `T` creates at most `T.length` new valid starts. -/
theorem occurrenceCount_extension
    (w A T : List (Fin 10)) (hw : 1 ≤ w.length) :
    ∃ X : ℕ, X ≤ T.length ∧
      finiteContiguousOccurrenceCount w (A ++ T) =
        finiteContiguousOccurrenceCount w A + X := by
  classical
  by_cases h : w.length ≤ A.length + 1
  · let a := A.length + 1 - w.length
    let p (i : ℕ) := ((A ++ T).drop i).take w.length = w
    let pA (i : ℕ) := (A.drop i).take w.length = w
    have htotal : A.length + T.length + 1 - w.length = a + T.length := by
      dsimp [a]
      omega
    let X := Nat.count (fun j => p (a + j)) T.length
    refine ⟨X, Nat.count_le _, ?_⟩
    unfold finiteContiguousOccurrenceCount
    change ((Finset.range ((A ++ T).length + 1 - w.length)).filter p).card =
      ((Finset.range (A.length + 1 - w.length)).filter pA).card + X
    rw [← Nat.count_eq_card_filter_range p,
      ← Nat.count_eq_card_filter_range pA]
    rw [List.length_append, htotal, Nat.count_add]
    change Nat.count p a + X = Nat.count pA a + X
    apply congrArg (· + X)
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    have hs := append_slice_internal w A T i (by
      have := Finset.mem_range.mp hi
      dsimp [a] at this ⊢
      omega)
    dsimp [p, pA]
    rw [hs]
  · have hA : finiteContiguousOccurrenceCount w A = 0 := by
      unfold finiteContiguousOccurrenceCount
      have : A.length + 1 - w.length = 0 := by omega
      rw [this]
      simp
    let X := finiteContiguousOccurrenceCount w (A ++ T)
    refine ⟨X, ?_, by simp [X, hA]⟩
    unfold X finiteContiguousOccurrenceCount
    exact (Finset.card_filter_le _ _).trans (by
      rw [Finset.card_range, List.length_append]
      omega)

private theorem nat_le_ten_pow (m : ℕ) : m ≤ 10 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        m + 1 ≤ 10 ^ m + 1 := Nat.add_le_add_right ih 1
        _ ≤ 10 ^ m * 10 := by
          have hp : 1 ≤ 10 ^ m := one_le_pow₀ (by norm_num)
          omega
        _ = 10 ^ (m + 1) := by rw [pow_succ]

theorem partialEpoch_discrepancy
    (w : List (Fin 10)) (m k q r : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) (hr : r ≤ m)
    (_hend : q = 9 * 10 ^ (m - 1) → r = 0) :
    Int.natAbs
        (((10 ^ k * finiteContiguousOccurrenceCount w
            (partialEpoch m q r) : ℕ) : ℤ) -
          ((partialEpoch m q r).length : ℤ)) ≤
      (2 + (k + 1) * (10 ^ k + 1)) * 10 ^ m := by
  let A := completeIntegerPrefix m q
  let T := (decimalDigits (10 ^ (m - 1) + q)).take r
  have hm1 : 1 ≤ m := le_trans hk hm
  have hpartial : partialEpoch m q r = A ++ T := rfl
  have htlen : T.length ≤ r := List.length_take_le _ _
  have htlenm : T.length ≤ m := htlen.trans hr
  obtain ⟨X, hX, hcount⟩ := occurrenceCount_extension w A T (by simpa [hwlen] using hk)
  have hA := completeIntegerPrefix_discrepancy w m k q hwlen hk hm hq
  have hmPow : m ≤ 10 ^ m := nat_le_ten_pow m
  have hterm :
      Int.natAbs ((((10 ^ k * X : ℕ) : ℤ) - (T.length : ℤ))) ≤
        (10 ^ k + 1) * 10 ^ m := by
    calc
      Int.natAbs ((((10 ^ k * X : ℕ) : ℤ) - (T.length : ℤ))) =
          Int.natAbs (((10 ^ k * X : ℕ) : ℤ) + (-(T.length : ℤ))) := by
        congr 1
      _ ≤ Int.natAbs ((10 ^ k * X : ℕ) : ℤ) +
          Int.natAbs (-(T.length : ℤ)) := Int.natAbs_add_le _ _
      _ = 10 ^ k * X + T.length := by
        simp only [Int.natAbs_neg, Int.natAbs_natCast]
      _ ≤ 10 ^ k * T.length + T.length := by gcongr
      _ = (10 ^ k + 1) * T.length := by ring
      _ ≤ (10 ^ k + 1) * 10 ^ m := by
        gcongr
        exact htlenm.trans hmPow
  have heq :
      (((10 ^ k * finiteContiguousOccurrenceCount w
          (partialEpoch m q r) : ℕ) : ℤ) -
        ((partialEpoch m q r).length : ℤ)) =
        ((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
            (A.length : ℤ)) +
          (((10 ^ k * X : ℕ) : ℤ) - (T.length : ℤ))) := by
    rw [hpartial, hcount, List.length_append]
    push_cast
    ring
  rw [heq]
  calc
    Int.natAbs
        (((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
            (A.length : ℤ)) +
          (((10 ^ k * X : ℕ) : ℤ) - (T.length : ℤ)))) ≤
        Int.natAbs
            (((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
              (A.length : ℤ)) +
          Int.natAbs (((10 ^ k * X : ℕ) : ℤ) - (T.length : ℤ)) :=
      Int.natAbs_add_le _ _
    _ ≤ (1 + k * (10 ^ k + 1)) * 10 ^ m +
        (10 ^ k + 1) * 10 ^ m := Nat.add_le_add hA hterm
    _ ≤ (2 + (k + 1) * (10 ^ k + 1)) * 10 ^ m := by
      nlinarith

private theorem occurrenceCount_le_length
    (w E : List (Fin 10)) (hw : 1 ≤ w.length) :
    finiteContiguousOccurrenceCount w E ≤ E.length := by
  unfold finiteContiguousOccurrenceCount
  calc
    ((Finset.range (E.length + 1 - w.length)).filter fun i =>
        (E.drop i).take w.length = w).card ≤ E.length + 1 - w.length :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    _ ≤ E.length := by omega

private theorem completedEpochs_succ (m : ℕ) (hm : 1 ≤ m) :
    completedEpochs (m + 1) = completedEpochs m ++ epoch m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp [completedEpochs, List.range_succ, List.flatMap_append, Nat.add_assoc,
    Nat.add_comm]

private theorem completedEpochs_length_step (m : ℕ) :
    (completedEpochs m).length ≤ (completedEpochs (m + 1)).length := by
  by_cases hm : 1 ≤ m
  · rw [completedEpochs_succ m hm, List.length_append]
    omega
  · have : m = 0 := by omega
    subst m
    simp [completedEpochs]

private theorem completedEpochs_length_mono :
    Monotone fun m => (completedEpochs m).length :=
  monotone_nat_of_le_succ completedEpochs_length_step

private theorem completedEpochs_length_le (m : ℕ) :
    (completedEpochs m).length ≤ m * 10 ^ m := by
  induction m with
  | zero => simp [completedEpochs]
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        simp [completedEpochs]
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        rw [completedEpochs_succ m hm1, List.length_append, epoch_length m hm1]
        calc
          (completedEpochs m).length + m * (9 * 10 ^ (m - 1)) ≤
              m * 10 ^ m + m * (9 * 10 ^ (m - 1)) := Nat.add_le_add_right ih _
          _ ≤ (m + 1) * 10 ^ (m + 1) := by
            rw [pow_succ]
            have hp : 10 ^ m = 10 ^ (m - 1) * 10 := by
              conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
            rw [hp]
            nlinarith [Nat.zero_le (10 ^ (m - 1))]

private theorem completedEpochs_length_ge_word
    (k n : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n) :
    k ≤ (completedEpochs n).length := by
  have hbase : k ≤ (completedEpochs (k + 1)).length := by
    rw [completedEpochs_succ k hk, List.length_append, epoch_length k hk]
    have hp : 0 < 9 * 10 ^ (k - 1) :=
      Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)
    nlinarith
  exact hbase.trans (completedEpochs_length_mono hn)

/-- Coefficient for all complete epochs before the current one. -/
def completedEpochsCoefficient (k : ℕ) : ℕ :=
  10 * (discrepancyCoefficient k + (k + 1) * (10 ^ k + 1))

theorem completedEpochs_discrepancy
    (w : List (Fin 10)) (k m : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : k ≤ m) :
    Int.natAbs
        (((10 ^ k * finiteContiguousOccurrenceCount w
            (completedEpochs m) : ℕ) : ℤ) -
          ((completedEpochs m).length : ℤ)) ≤
      completedEpochsCoefficient k * 10 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hsmall : m ≤ k + 1
      · have hcount := occurrenceCount_le_length w (completedEpochs m)
          (by simpa [hwlen] using hk)
        have hlen := completedEpochs_length_le m
        have hmk : m ≤ k + 1 := hsmall
        have hmPow : m ≤ 10 ^ m := nat_le_ten_pow m
        calc
          Int.natAbs
              (((10 ^ k * finiteContiguousOccurrenceCount w
                  (completedEpochs m) : ℕ) : ℤ) -
                ((completedEpochs m).length : ℤ)) ≤
              10 ^ k * finiteContiguousOccurrenceCount w (completedEpochs m) +
                (completedEpochs m).length := by
            calc
              Int.natAbs
                  (((10 ^ k * finiteContiguousOccurrenceCount w
                      (completedEpochs m) : ℕ) : ℤ) -
                    ((completedEpochs m).length : ℤ)) =
                  Int.natAbs
                    (((10 ^ k * finiteContiguousOccurrenceCount w
                        (completedEpochs m) : ℕ) : ℤ) +
                      (-((completedEpochs m).length : ℤ))) := by congr 1
              _ ≤ Int.natAbs
                    ((10 ^ k * finiteContiguousOccurrenceCount w
                      (completedEpochs m) : ℕ) : ℤ) +
                  Int.natAbs (-((completedEpochs m).length : ℤ)) :=
                Int.natAbs_add_le _ _
              _ = 10 ^ k * finiteContiguousOccurrenceCount w (completedEpochs m) +
                  (completedEpochs m).length := by
                simp only [Int.natAbs_neg, Int.natAbs_natCast]
          _ ≤ (10 ^ k + 1) * (completedEpochs m).length := by
            calc
              10 ^ k * finiteContiguousOccurrenceCount w (completedEpochs m) +
                  (completedEpochs m).length ≤
                  10 ^ k * (completedEpochs m).length +
                    (completedEpochs m).length := by gcongr
              _ = (10 ^ k + 1) * (completedEpochs m).length := by ring
          _ ≤ (10 ^ k + 1) * (m * 10 ^ m) := by gcongr
          _ ≤ completedEpochsCoefficient k * 10 ^ m := by
            rw [← Nat.mul_assoc]
            gcongr
            calc
              (10 ^ k + 1) * m ≤ (10 ^ k + 1) * (k + 1) := by gcongr
              _ ≤ completedEpochsCoefficient k := by
                unfold completedEpochsCoefficient
                nlinarith [Nat.zero_le (discrepancyCoefficient k),
                  Nat.zero_le ((k + 1) * (10 ^ k + 1))]
      · let n := m - 1
        have hnkm : k + 1 ≤ n := by omega
        have hnm : n < m := by omega
        have hm_eq : m = n + 1 := by omega
        have hn1 : 1 ≤ n := le_trans hk (by omega)
        have hkn : k ≤ n := by omega
        have hprev := ih n hnm hkn
        have hepoch := champernowne_epoch_uniform_discrepancy w k n
          hwlen hk (by simp; omega)
        let A := completedEpochs n
        let B := epoch n
        have hwA : w.length ≤ A.length := by
          rw [hwlen]
          exact completedEpochs_length_ge_word k n hk hnkm
        have hBlen := epoch_length n hn1
        have hwB : w.length ≤ B.length := by
          rw [hwlen, hBlen]
          have hp : 0 < 9 * 10 ^ (n - 1) :=
            Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)
          nlinarith
        have happ := occurrenceCount_append w A B
          (by simpa [hwlen] using hk) hwA hwB
        let X := appendCrossingCount w A B
        have hX : X ≤ k - 1 := by
          simpa [X, hwlen] using appendCrossingCount_le w A B
        have hXabs : Int.natAbs ((10 ^ k * X : ℕ) : ℤ) ≤ 10 ^ k * k := by
          simp only [Int.natAbs_natCast]
          gcongr
          omega
        have hprefix : completedEpochs m = A ++ B := by
          rw [hm_eq, completedEpochs_succ n hn1]
        have heq :
            (((10 ^ k * finiteContiguousOccurrenceCount w
                (completedEpochs m) : ℕ) : ℤ) -
              ((completedEpochs m).length : ℤ)) =
              ((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
                  (A.length : ℤ)) +
                (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
                  (B.length : ℤ)) +
                ((10 ^ k * X : ℕ) : ℤ)) := by
          rw [hprefix, happ, List.length_append]
          dsimp [X]
          push_cast
          ring
        rw [heq]
        calc
          Int.natAbs
              (((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
                  (A.length : ℤ)) +
                (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
                  (B.length : ℤ)) +
                ((10 ^ k * X : ℕ) : ℤ))) ≤
              Int.natAbs
                  (((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
                    (A.length : ℤ)) +
                Int.natAbs
                  (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
                    (B.length : ℤ)) +
                Int.natAbs ((10 ^ k * X : ℕ) : ℤ) := by
            exact (Int.natAbs_add_le _ _).trans
              (Nat.add_le_add_right (Int.natAbs_add_le _ _) _)
          _ ≤ completedEpochsCoefficient k * 10 ^ n +
                discrepancyCoefficient k * 10 ^ n + 10 ^ k * k :=
            Nat.add_le_add (Nat.add_le_add hprev hepoch) hXabs
          _ ≤ completedEpochsCoefficient k * 10 ^ m := by
            rw [hm_eq, pow_succ]
            have hp : 1 ≤ 10 ^ n := one_le_pow₀ (by norm_num)
            let Acoeff := (k + 1) * (10 ^ k + 1)
            have hcross : 10 ^ k * k ≤ Acoeff * 10 ^ n := by
              calc
                10 ^ k * k = k * 10 ^ k := Nat.mul_comm _ _
                _ ≤ (k + 1) * (10 ^ k + 1) :=
                  Nat.mul_le_mul (Nat.le_succ k) (Nat.le_add_right (10 ^ k) 1)
                _ ≤ Acoeff * 10 ^ n := by
                  dsimp [Acoeff]
                  exact Nat.le_mul_of_pos_right _ (by omega)
            have hcoeff : discrepancyCoefficient k + Acoeff ≤
                completedEpochsCoefficient k := by
              dsimp [Acoeff]
              unfold completedEpochsCoefficient
              have hmul := Nat.le_mul_of_pos_right
                (discrepancyCoefficient k + (k + 1) * (10 ^ k + 1))
                (by norm_num : 0 < 10)
              simpa [Nat.mul_comm] using hmul
            calc
              completedEpochsCoefficient k * 10 ^ n +
                    discrepancyCoefficient k * 10 ^ n + 10 ^ k * k ≤
                  completedEpochsCoefficient k * 10 ^ n +
                    discrepancyCoefficient k * 10 ^ n + Acoeff * 10 ^ n := by
                gcongr
              _ = completedEpochsCoefficient k * 10 ^ n +
                    (discrepancyCoefficient k + Acoeff) * 10 ^ n := by ring
              _ ≤ completedEpochsCoefficient k * 10 ^ n +
                    completedEpochsCoefficient k * 10 ^ n := by gcongr
              _ ≤ completedEpochsCoefficient k * (10 ^ n * 10) := by
                nlinarith [Nat.zero_le (completedEpochsCoefficient k * 10 ^ n)]

/-!
The theorem below is the advertised cutoff-uniform result.  The hypotheses on
`q` and `r` say that the cutoff is after `q` complete `m`-digit integers and
after `r` digits of the next integer.  At the endpoint of the epoch no digits
of `10^m` may be appended.  Thus every digit cutoff in the epoch is covered,
including cutoffs inside an integer.
-/

theorem champernowne_prefix_uniform_discrepancy
    (w : List (Fin 10)) (k m q r : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : max 1 k ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) (hr : r ≤ m)
    (hend : q = 9 * 10 ^ (m - 1) → r = 0) :
    Int.natAbs
        (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) -
          ((champernownePrefix m q r).length : ℤ)) ≤
      prefixDiscrepancyCoefficient k * 10 ^ m := by
  let A := completedEpochs m
  let B := partialEpoch m q r
  have hkm : k ≤ m := le_trans (le_max_right 1 k) hm
  have hm1 : 1 ≤ m := le_trans (le_max_left 1 k) hm
  have hw : 1 ≤ w.length := by simpa [hwlen] using hk
  have hprefix : champernownePrefix m q r = A ++ B := rfl
  have hpast := completedEpochs_discrepancy w k m hwlen hk hkm
  have hcurrent := partialEpoch_discrepancy w m k q r
    hwlen hk hkm hq hr hend
  have hpowone : 1 ≤ 10 ^ m := one_le_pow₀ (by norm_num)
  by_cases hlate : k + 1 ≤ m
  swap
  · have hmkEq : m = k := by omega
    have hAlen := completedEpochs_length_le m
    have hTlen :
        ((decimalDigits (10 ^ (m - 1) + q)).take r).length ≤ r :=
      List.length_take_le _ _
    have hBlen : B.length ≤ m * 10 ^ m := by
      have hcomplete := completeIntegerPrefix_length m q hm1 hq
      change (completeIntegerPrefix m q ++
        (decimalDigits (10 ^ (m - 1) + q)).take r).length ≤ m * 10 ^ m
      rw [List.length_append, hcomplete]
      have hpow : 10 ^ m = 10 ^ (m - 1) * 10 := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      calc
        q * m + (List.take r (decimalDigits (10 ^ (m - 1) + q))).length ≤
            (9 * 10 ^ (m - 1)) * m + m := by
          apply Nat.add_le_add
          · gcongr
          · exact hTlen.trans hr
        _ = m * (9 * 10 ^ (m - 1) + 1) := by ring
        _ ≤ m * (10 ^ (m - 1) * 10) := by
          gcongr
          have hp : 1 ≤ 10 ^ (m - 1) := one_le_pow₀ (by norm_num)
          nlinarith
        _ = m * 10 ^ m := by rw [hpow]
    have hprefixlen : (champernownePrefix m q r).length ≤ 2 * m * 10 ^ m := by
      rw [hprefix, List.length_append]
      dsimp [A, B] at hAlen hBlen ⊢
      nlinarith
    have hcount : prefixOccurrenceCount w m q r ≤
        (champernownePrefix m q r).length := by
      simpa [prefixOccurrenceCount] using
        occurrenceCount_le_length w (champernownePrefix m q r) hw
    calc
      Int.natAbs
          (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) -
            ((champernownePrefix m q r).length : ℤ)) ≤
          10 ^ k * prefixOccurrenceCount w m q r +
            (champernownePrefix m q r).length := by
        calc
          Int.natAbs
              (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) -
                ((champernownePrefix m q r).length : ℤ)) =
              Int.natAbs
                (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) +
                  (-((champernownePrefix m q r).length : ℤ))) := by congr 1
          _ ≤ Int.natAbs ((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) +
              Int.natAbs (-((champernownePrefix m q r).length : ℤ)) :=
            Int.natAbs_add_le _ _
          _ = 10 ^ k * prefixOccurrenceCount w m q r +
              (champernownePrefix m q r).length := by
            simp only [Int.natAbs_neg, Int.natAbs_natCast]
      _ ≤ (10 ^ k + 1) * (champernownePrefix m q r).length := by
        calc
          10 ^ k * prefixOccurrenceCount w m q r +
                (champernownePrefix m q r).length ≤
              10 ^ k * (champernownePrefix m q r).length +
                (champernownePrefix m q r).length := by gcongr
          _ = (10 ^ k + 1) * (champernownePrefix m q r).length := by ring
      _ ≤ (10 ^ k + 1) * (2 * m * 10 ^ m) := by gcongr
      _ ≤ prefixDiscrepancyCoefficient k * 10 ^ m := by
        rw [hmkEq]
        have hcoeff : (10 ^ k + 1) * (2 * k) ≤ prefixDiscrepancyCoefficient k := by
          unfold prefixDiscrepancyCoefficient
          nlinarith [Nat.zero_le (discrepancyCoefficient k), Nat.zero_le (10 ^ k)]
        calc
          (10 ^ k + 1) * (2 * k * 10 ^ k) =
              ((10 ^ k + 1) * (2 * k)) * 10 ^ k := by ring
          _ ≤ prefixDiscrepancyCoefficient k * 10 ^ k := by gcongr
  by_cases hwB : w.length ≤ B.length
  · have hwA : w.length ≤ A.length := by
      rw [hwlen]
      exact completedEpochs_length_ge_word k m hk (by omega)
    have happ := occurrenceCount_append w A B hw hwA hwB
    let X := appendCrossingCount w A B
    have hX : X ≤ k - 1 := by
      simpa [X, hwlen] using appendCrossingCount_le w A B
    have hXabs : Int.natAbs ((10 ^ k * X : ℕ) : ℤ) ≤ 10 ^ k * k := by
      simp only [Int.natAbs_natCast]
      gcongr
      omega
    have heq :
        (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) -
          ((champernownePrefix m q r).length : ℤ)) =
          ((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
              (A.length : ℤ)) +
            (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
              (B.length : ℤ)) +
            ((10 ^ k * X : ℕ) : ℤ)) := by
      unfold prefixOccurrenceCount
      rw [hprefix, happ, List.length_append]
      dsimp [X]
      push_cast
      ring
    rw [heq]
    calc
      Int.natAbs
          (((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
              (A.length : ℤ)) +
            (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
              (B.length : ℤ)) +
            ((10 ^ k * X : ℕ) : ℤ))) ≤
          Int.natAbs
              (((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
                (A.length : ℤ)) +
            Int.natAbs
              (((10 ^ k * finiteContiguousOccurrenceCount w B : ℕ) : ℤ) -
                (B.length : ℤ)) +
            Int.natAbs ((10 ^ k * X : ℕ) : ℤ) := by
        exact (Int.natAbs_add_le _ _).trans
          (Nat.add_le_add_right (Int.natAbs_add_le _ _) _)
      _ ≤ completedEpochsCoefficient k * 10 ^ m +
            (2 + (k + 1) * (10 ^ k + 1)) * 10 ^ m + 10 ^ k * k :=
        Nat.add_le_add (Nat.add_le_add hpast hcurrent) hXabs
      _ ≤ (completedEpochsCoefficient k +
            (2 + (k + 1) * (10 ^ k + 1)) + 10 ^ k * k) * 10 ^ m := by
        calc
          completedEpochsCoefficient k * 10 ^ m +
                (2 + (k + 1) * (10 ^ k + 1)) * 10 ^ m + 10 ^ k * k ≤
              completedEpochsCoefficient k * 10 ^ m +
                (2 + (k + 1) * (10 ^ k + 1)) * 10 ^ m +
                  (10 ^ k * k) * 10 ^ m := by
            exact Nat.add_le_add_left
              (Nat.le_mul_of_pos_right (10 ^ k * k) (by omega)) _
          _ = (completedEpochsCoefficient k +
                (2 + (k + 1) * (10 ^ k + 1)) + 10 ^ k * k) * 10 ^ m := by ring
      _ ≤ prefixDiscrepancyCoefficient k * 10 ^ m := by
        apply Nat.mul_le_mul_right
        unfold prefixDiscrepancyCoefficient completedEpochsCoefficient
        omega
  · obtain ⟨X, hX, hcount⟩ := occurrenceCount_extension w A B hw
    have hBsmall : B.length < k := by simpa [hwlen] using hwB
    have hterm :
        Int.natAbs ((((10 ^ k * X : ℕ) : ℤ) - (B.length : ℤ))) ≤
          (10 ^ k + 1) * k := by
      calc
        Int.natAbs ((((10 ^ k * X : ℕ) : ℤ) - (B.length : ℤ))) =
            Int.natAbs (((10 ^ k * X : ℕ) : ℤ) + (-(B.length : ℤ))) := by
          congr 1
        _ ≤ Int.natAbs ((10 ^ k * X : ℕ) : ℤ) +
            Int.natAbs (-(B.length : ℤ)) := Int.natAbs_add_le _ _
        _ = 10 ^ k * X + B.length := by
          simp only [Int.natAbs_neg, Int.natAbs_natCast]
        _ ≤ 10 ^ k * B.length + B.length := by gcongr
        _ = (10 ^ k + 1) * B.length := by ring
        _ ≤ (10 ^ k + 1) * k := by gcongr
    have heq :
        (((10 ^ k * prefixOccurrenceCount w m q r : ℕ) : ℤ) -
          ((champernownePrefix m q r).length : ℤ)) =
          ((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
              (A.length : ℤ)) +
            (((10 ^ k * X : ℕ) : ℤ) - (B.length : ℤ))) := by
      unfold prefixOccurrenceCount
      rw [hprefix, hcount, List.length_append]
      push_cast
      ring
    rw [heq]
    calc
      Int.natAbs
          (((((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
              (A.length : ℤ)) +
            (((10 ^ k * X : ℕ) : ℤ) - (B.length : ℤ)))) ≤
          Int.natAbs
              (((10 ^ k * finiteContiguousOccurrenceCount w A : ℕ) : ℤ) -
                (A.length : ℤ)) +
            Int.natAbs (((10 ^ k * X : ℕ) : ℤ) - (B.length : ℤ)) :=
        Int.natAbs_add_le _ _
      _ ≤ completedEpochsCoefficient k * 10 ^ m + (10 ^ k + 1) * k :=
        Nat.add_le_add hpast hterm
      _ ≤ (completedEpochsCoefficient k + (10 ^ k + 1) * k) * 10 ^ m := by
        calc
          completedEpochsCoefficient k * 10 ^ m + (10 ^ k + 1) * k ≤
              completedEpochsCoefficient k * 10 ^ m +
                ((10 ^ k + 1) * k) * 10 ^ m := by
            exact Nat.add_le_add_left
              (Nat.le_mul_of_pos_right ((10 ^ k + 1) * k) (by omega)) _
          _ = (completedEpochsCoefficient k + (10 ^ k + 1) * k) * 10 ^ m := by ring
      _ ≤ prefixDiscrepancyCoefficient k * 10 ^ m := by
        apply Nat.mul_le_mul_right
        unfold prefixDiscrepancyCoefficient completedEpochsCoefficient
        omega

/-- Explicit cutoff-uniform discrepancy for every digit cutoff in epoch `m`.

This is the raw-cutoff form of the T24 result: `t` may be zero, an integer
boundary, an epoch endpoint, or a position strictly inside the terminal
integer.  The filtered-start count includes every overlap and every integer
or epoch boundary wholly contained in the prefix.
-/
theorem champernowne_arbitraryPrefix_uniform_discrepancy
    (w : List (Fin 10)) (k m t : ℕ)
    (hwlen : w.length = k) (hk : 1 ≤ k) (hm : max 1 k ≤ m)
    (ht : t ≤ (epoch m).length) :
    Int.natAbs
        (((10 ^ k * arbitraryPrefixOccurrenceCount w m t : ℕ) : ℤ) -
          ((arbitraryPrefix m t).length : ℤ)) ≤
      prefixDiscrepancyCoefficient k * 10 ^ m := by
  let q := t / m
  let r := t % m
  let total := 9 * 10 ^ (m - 1)
  have hm1 : 1 ≤ m := le_trans (le_max_left 1 k) hm
  have htbound : t ≤ total * m := by
    have hlen := epoch_length m hm1
    rw [hlen] at ht
    simpa [total, Nat.mul_comm] using ht
  have hqmul : q * m ≤ total * m := by
    exact (Nat.div_mul_le_self t m).trans htbound
  have hq : q ≤ total := Nat.le_of_mul_le_mul_right hqmul (by omega)
  have hrlt : r < m := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hr : r ≤ m := hrlt.le
  have htqr : t = q * m + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod' t m).symm
  have hend : q = total → r = 0 := by
    intro hqeq
    rw [hqeq] at htqr
    omega
  have hpartial := partialEpoch_eq_epoch_take m q r hm1
    (by simpa [total] using hq) hr (by simpa [total] using hend)
  have hprefix : champernownePrefix m q r = arbitraryPrefix m t := by
    unfold champernownePrefix arbitraryPrefix
    rw [hpartial, htqr]
  have hmain := champernowne_prefix_uniform_discrepancy w k m q r
    hwlen hk hm (by simpa [total] using hq) hr (by simpa [total] using hend)
  simpa [arbitraryPrefixOccurrenceCount, prefixOccurrenceCount, hprefix] using hmain

/-- Leading-zero specialization of the direct arbitrary-cutoff theorem. -/
theorem champernowne_arbitraryPrefix_leadingZero_discrepancy
    (d : List (Fin 10)) (m t : ℕ)
    (hm : max 1 (d.length + 1) ≤ m) (ht : t ≤ (epoch m).length) :
    Int.natAbs
        (((10 ^ (d.length + 1) *
            arbitraryPrefixOccurrenceCount ((0 : Fin 10) :: d) m t : ℕ) : ℤ) -
          ((arbitraryPrefix m t).length : ℤ)) ≤
      prefixDiscrepancyCoefficient (d.length + 1) * 10 ^ m := by
  apply champernowne_arbitraryPrefix_uniform_discrepancy
    ((0 : Fin 10) :: d) (d.length + 1) m t
  · simp
  · omega
  · exact hm
  · exact ht

/-- Explicit leading-zero specialization of the cutoff-uniform theorem. -/
theorem champernowne_prefix_leadingZero_discrepancy
    (d : List (Fin 10)) (m q r : ℕ)
    (hm : max 1 (d.length + 1) ≤ m)
    (hq : q ≤ 9 * 10 ^ (m - 1)) (hr : r ≤ m)
    (hend : q = 9 * 10 ^ (m - 1) → r = 0) :
    Int.natAbs
        (((10 ^ (d.length + 1) *
            prefixOccurrenceCount ((0 : Fin 10) :: d) m q r : ℕ) : ℤ) -
          ((champernownePrefix m q r).length : ℤ)) ≤
      prefixDiscrepancyCoefficient (d.length + 1) * 10 ^ m := by
  apply champernowne_prefix_uniform_discrepancy
    ((0 : Fin 10) :: d) (d.length + 1) m q r
  · simp
  · omega
  · exact hm
  · exact hq
  · exact hr
  · exact hend

#print axioms Theory.PiDigits.T24.champernowne_prefix_uniform_discrepancy
#print axioms Theory.PiDigits.T24.champernowne_prefix_leadingZero_discrepancy
#print axioms Theory.PiDigits.T24.champernowne_arbitraryPrefix_uniform_discrepancy
#print axioms Theory.PiDigits.T24.champernowne_arbitraryPrefix_leadingZero_discrepancy
#print axioms Theory.PiDigits.T24.arbitraryPrefix_eq_champernowneDigit_prefix
#print axioms Theory.PiDigits.T24.completedEpochs_eq_finiteConcat
#print axioms Theory.PiDigits.T24.regularPositionCount_discrepancy
#print axioms Theory.PiDigits.T24.completeIntegerPrefix_occurrence_decomposition

end Theory.PiDigits.T24
