import TheoryLib.Shared.DigitAutomata.T9T9CyclicSparseForbidden
import TheoryLib.Shared.DigitAutomata.T12T12CyclicWindowCertificates

/-!
# T13: endpoint-inclusive arithmetic bridge for the T6 constant word

Canonical source: `problems/local/multiplicative-avoidance-gap.txt`
SHA-256: `05d09b6edb60fa060cc952fc5b2fad9dea75c20d84ac628d86f1b6dd6b0ab7c8`
Original source URL: none; the canonical file records a local formulation on 2026-07-26.

This module reconstructs only the finite safety hole, the endpoint-inclusive
circle convention, and the resulting survivor inclusion from the unverified
T6 note. It imports the kernel-checked T9 and T12 modules but does not reprove
their cyclic local-lemma results. It states no entropy, `Gamma`, or C1 result.
-/

open Finset Set

namespace Theory.Shared.DigitAutomata.T13

noncomputable section

/-- The exact T6 carry range `{-1, 0, ..., q}`. -/
def CarrySet (q : ℕ) : Finset ℤ := Finset.Icc (-1) q

/-- The exact digit/carry transition equation from T6 (3.3). -/
def CarryStep (b q : ℕ) (c c' : ℤ) (a d : ℕ) : Prop :=
  (q : ℤ) * a + c' = d + (b : ℤ) * c

/-- The partial KMP transition for the constant forbidden word `0^k`. -/
def ZeroKMPTransition (k : ℕ) (r r' : Fin k) (a : ℕ) : Prop :=
  (a ≠ 0 ∧ r'.val = 0) ∨ (a = 0 ∧ r.val + 1 < k ∧ r'.val = r.val + 1)

/-- A length-`m` word read most-significant digit first as an integer. -/
def blockCode {b m : ℕ} (u : Fin m → Fin b) : Fin (b ^ m) :=
  finFunctionFinEquiv (fun i ↦ u (Fin.revPerm i))

theorem blockCode_injective (b m : ℕ) :
    Function.Injective (@blockCode b m) := by
  intro u v huv
  apply funext
  intro i
  have h := congrFun (finFunctionFinEquiv.injective huv) (Fin.revPerm i)
  simpa [blockCode] using h

/-- The ordinary lift-intersection inequalities in T6 (4.7). -/
def ordinaryUnsafeAt (B E q N j : ℕ) : Prop :=
  q * N ≤ B * j + E ∧ B * j ≤ q * (N + 1)

/-- The canonical circle endpoint `1 = 0`, kept in the `j = 0` fiber. -/
def wrapEndpointAt (B N j : ℕ) : Prop := N + 1 = B ∧ j = 0

/-- Endpoint-inclusive integer test for one component of the T6 safety hole. -/
def integerUnsafeAt (B E q N j : ℕ) : Prop :=
  ordinaryUnsafeAt B E q N j ∨ wrapEndpointAt B N j

/-- The positive integer safety predicate. -/
def integerSafeAt (B E q N j : ℕ) : Prop :=
  ¬integerUnsafeAt B E q N j

/-- Unsafe level-`m` numerals, with all ranges made explicit. -/
def unsafeCodes (B E q : ℕ) : Finset (Fin B) :=
  by
    classical
    exact Finset.univ.filter fun N ↦ ∃ j : Fin q, integerUnsafeAt B E q N j

/-- The T6 safety list `F_U`, transported from numerals to base-`b` words. -/
def safetyList (b m E q : ℕ) : Finset (Fin m → Fin b) :=
  by
    classical
    exact Finset.univ.filter fun u ↦
       ∃ j : Fin q, integerUnsafeAt (b ^ m) E q (blockCode u).val j.val

/-- The canonical T6 exponent `e_(b,q)`, the least `e` such that `q ≤ b^e`. -/
def canonicalExponent (b q : ℕ) : ℕ := Nat.clog b q

/-- The defining upper inequality for the canonical T6 exponent. -/
theorem le_pow_canonicalExponent (b q : ℕ) (hb : 2 ≤ b) :
    q ≤ b ^ canonicalExponent b q := by
  exact Nat.le_pow_clog (by omega) q

/-- The canonical T6 exponent is no larger than any admissible exponent. -/
theorem canonicalExponent_le (b q e : ℕ) (hqe : q ≤ b ^ e) :
    canonicalExponent b q ≤ e := by
  exact Nat.clog_le_of_le_pow hqe

/-- The canonical exponent satisfies and is least for the T6 power bound. -/
theorem canonicalExponent_spec (b q : ℕ) (hb : 2 ≤ b) :
    q ≤ b ^ canonicalExponent b q ∧
      ∀ e, q ≤ b ^ e → canonicalExponent b q ≤ e := by
  exact ⟨le_pow_canonicalExponent b q hb, canonicalExponent_le b q⟩

/-- The T6 list `F_0` of length-`k+e` words beginning with `0^k`. -/
def zeroPrefixList (b k e : ℕ) : Finset (Fin (k + e) → Fin b) :=
  by
    classical
    exact Finset.univ.filter fun u ↦ ∀ i : Fin k, (u (Fin.castAdd e i)).val = 0

/-- The finite forbidden list at an explicitly supplied exponent. -/
def forbiddenListWithExponent (b q k e : ℕ) : Finset (Fin (k + e) → Fin b) :=
  safetyList b (k + e) (b ^ e) q ∪ zeroPrefixList b k e

/-- The exact T6 safety list `F_U`, using the least admissible exponent. -/
def canonicalSafetyList (b q k : ℕ) :
    Finset (Fin (k + canonicalExponent b q) → Fin b) :=
  safetyList b (k + canonicalExponent b q) (b ^ canonicalExponent b q) q

/-- The exact T6 forbidden list `F = F_U ∪ F_0`, with no free exponent. -/
def forbiddenList (b q k : ℕ) :
    Finset (Fin (k + canonicalExponent b q) → Fin b) :=
  forbiddenListWithExponent b q k (canonicalExponent b q)

/-- Equality of representatives in `[0,1]` after identifying both endpoints. -/
def endpointEq (x y : ℝ) : Prop :=
  x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

theorem unitAddCircle_eq_iff_endpointEq {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (x : UnitAddCircle) = y ↔ endpointEq x y := by
  constructor
  · intro hxy
    by_cases hx1 : x = 1
    · by_cases hy1 : y = 1
      · exact Or.inl (hx1.trans hy1.symm)
      · right
        right
        refine ⟨hx1, ?_⟩
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 := ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩
        have h0y : ((0 : ℝ) : UnitAddCircle) = y := by
          rw [hx1, AddCircle.coe_period] at hxy
          exact hxy
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (a := (0 : ℝ)) (p := (1 : ℝ)) (by simp) (by simpa using hyIco)).mp h0y |>.symm
    · by_cases hy1 : y = 1
      · right
        left
        refine ⟨?_, hy1⟩
        have hxIco : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
        have hx0 : (x : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
          rw [hy1, AddCircle.coe_period] at hxy
          exact hxy
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using hxIco) (by simp)).mp hx0
      · left
        have hxIco : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 := ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using hxIco)
            (by simpa using hyIco)).mp hxy
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [AddCircle.coe_period]
      rfl
    · rw [AddCircle.coe_period]
      rfl

/-- A closed interval mapped to the circle; both real endpoints are retained. -/
def closedCircleArc (a z : ℝ) : Set UnitAddCircle :=
  ((fun x : ℝ ↦ (x : UnitAddCircle)) '' Set.Icc a z)

/-- The closed level-`B` cylinder corresponding to numeral `N`. -/
def cylinderArc (B N : ℕ) : Set UnitAddCircle :=
  closedCircleArc (N / (B : ℝ)) ((N + 1) / (B : ℝ))

/-- One closed component of `T_q⁻¹(I_k)`, in the common denominator `qB`. -/
def dangerArc (B E q j : ℕ) : Set UnitAddCircle :=
  closedCircleArc (j / (q : ℝ)) ((B * j + E) / ((q : ℝ) * B))

/-- Geometric unsafe test: the two endpoint-inclusive closed circle arcs meet. -/
def circleUnsafeAt (B E q N j : ℕ) : Prop :=
  (cylinderArc B N ∩ dangerArc B E q j).Nonempty

/-- Closed-circle avoidance, so touching either endpoint is not safe. -/
def circleAvoidsAt (B E q N j : ℕ) : Prop :=
  ¬circleUnsafeAt B E q N j

theorem cylinderLower_le_dangerUpper_iff
    (B q N A : ℕ) (hB : 0 < B) (hq : 0 < q) :
    (N : ℝ) / B ≤ (A : ℝ) / ((q : ℝ) * B) ↔ q * N ≤ A := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · intro h
    have hc := (div_le_div_iff₀ hBR (mul_pos hqR hBR)).mp h
    norm_num at hc
    exact_mod_cast (show (q : ℝ) * N ≤ A by nlinarith)
  · intro h
    apply (div_le_div_iff₀ hBR (mul_pos hqR hBR)).2
    have hR : (q : ℝ) * N ≤ A := by exact_mod_cast h
    nlinarith

theorem dangerLower_le_cylinderUpper_iff
    (B q j M : ℕ) (hB : 0 < B) (hq : 0 < q) :
    (j : ℝ) / q ≤ (M : ℝ) / B ↔ B * j ≤ q * M := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ hqR hBR]
  norm_cast
  simp [Nat.mul_comm]

/-- The integer test is exactly closed-circle intersection, including `1 = 0`. -/
theorem integerUnsafeAt_iff_circleUnsafeAt
    (B E q N j : ℕ) (hB : 0 < B) (hq : 0 < q)
    (hN : N < B) (hj : j < q) (hE : E < B) :
    integerUnsafeAt B E q N j ↔ circleUnsafeAt B E q N j := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqBR : (0 : ℝ) < (q : ℝ) * B := mul_pos hqR hBR
  have hNsucc : N + 1 ≤ B := by omega
  have hjSucc : j + 1 ≤ q := by omega
  have hAj : B * j + E < q * B := by
    calc
      B * j + E < B * j + B := Nat.add_lt_add_left hE (B * j)
      _ = B * (j + 1) := by ring
      _ ≤ B * q := Nat.mul_le_mul_left B hjSucc
      _ = q * B := by ring
  constructor
  · intro hunsafe
    rcases hunsafe with hord | hend
    · let t : ℝ := max ((N : ℝ) / B) ((j : ℝ) / q)
      have hcell : t ∈ Set.Icc ((N : ℝ) / B) ((N + 1 : ℕ) / (B : ℝ)) := by
        constructor
        · exact le_max_left _ _
        · apply max_le
          · apply div_le_div_of_nonneg_right _ hBR.le
            norm_num
          · simpa [Nat.cast_add, Nat.cast_one] using
              (dangerLower_le_cylinderUpper_iff B q j (N + 1) hB hq).2 hord.2
      have hdanger : t ∈ Set.Icc ((j : ℝ) / q)
          ((B * j + E : ℕ) / ((q : ℝ) * B)) := by
        constructor
        · exact le_max_right _ _
        · apply max_le
          · exact (cylinderLower_le_dangerUpper_iff B q N (B * j + E) hB hq).2 hord.1
          · simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using
              (cylinderLower_le_dangerUpper_iff q B j (B * j + E) hq hB).2
                (show B * j ≤ B * j + E by omega)
      refine ⟨(t : UnitAddCircle), ?_⟩
      constructor
      · exact ⟨t, by simpa [Nat.cast_add, Nat.cast_one] using hcell, rfl⟩
      · exact ⟨t, by simpa [Nat.cast_add, Nat.cast_mul] using hdanger, rfl⟩
    · rcases hend with ⟨hNB, hj0⟩
      refine ⟨(0 : UnitAddCircle), ?_⟩
      constructor
      · refine ⟨(1 : ℝ), ?_, ?_⟩
        · constructor
          · apply (div_le_iff₀ hBR).2
            norm_num
            exact_mod_cast hN.le
          · have hNBR : (N : ℝ) + 1 = B := by exact_mod_cast hNB
            rw [hNBR]
            rw [div_self hBR.ne']
        · change ((1 : ℝ) : UnitAddCircle) = 0
          exact AddCircle.coe_period (1 : ℝ)
      · refine ⟨(0 : ℝ), ?_, rfl⟩
        constructor
        · simp [hj0]
        · positivity
  · intro hcircle
    rcases hcircle with ⟨z, hzCell, hzDanger⟩
    rcases hzCell with ⟨x, hx, hxz⟩
    rcases hzDanger with ⟨y, hy, hyz⟩
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact (by positivity : (0 : ℝ) ≤ (N : ℝ) / B) |>.trans hx.1
      · exact hx.2.trans ((div_le_iff₀ hBR).2 (by norm_num; exact_mod_cast hNsucc))
    have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact (by positivity : (0 : ℝ) ≤ (j : ℝ) / q) |>.trans hy.1
      · apply hy.2.trans
        apply (div_le_iff₀ hqBR).2
        norm_num
        exact_mod_cast hAj.le
    have hxyCircle : (x : UnitAddCircle) = y := hxz.trans hyz.symm
    have hxy := (unitAddCircle_eq_iff_endpointEq hx01 hy01).mp hxyCircle
    rcases hxy with hsame | h01 | h10
    · left
      unfold ordinaryUnsafeAt
      constructor
      · apply (cylinderLower_le_dangerUpper_iff B q N (B * j + E) hB hq).1
        exact hx.1.trans (by simpa [Nat.cast_add, Nat.cast_mul] using (hsame ▸ hy.2))
      · apply (dangerLower_le_cylinderUpper_iff B q j (N + 1) hB hq).1
        exact hy.1.trans (by simpa [Nat.cast_add, Nat.cast_one] using (hsame ▸ hx.2))
    · rcases h01 with ⟨hx0, hy1⟩
      have hupperLt : ((B : ℝ) * j + E) / ((q : ℝ) * B) < 1 := by
        apply (div_lt_iff₀ hqBR).2
        norm_num
        exact_mod_cast hAj
      exfalso
      linarith [hy.2]
    · right
      rcases h10 with ⟨hx1, hy0⟩
      constructor
      · have hfrac : ((N + 1 : ℕ) : ℝ) / B = 1 := by
          apply le_antisymm
          · exact (div_le_iff₀ hBR).2 (by norm_num; exact_mod_cast hNsucc)
          · simpa [hx1] using hx.2
        have hcast : ((N + 1 : ℕ) : ℝ) = B := by
          exact (div_eq_one_iff_eq hBR.ne').mp hfrac
        exact_mod_cast hcast
      · have hjle : (j : ℝ) / q ≤ 0 := by simpa [hy0] using hy.1
        have hjcast : (j : ℝ) ≤ 0 := by
          have h := (div_le_iff₀ hqR).mp hjle
          norm_num at h ⊢
          exact h
        have hjzero : (j : ℝ) = 0 := le_antisymm hjcast (Nat.cast_nonneg j)
        exact_mod_cast hjzero

/-- Positive form of the exact bridge: integer safety is precisely avoidance
of the closed danger arc on `R/Z`, including both endpoint identifications. -/
theorem integerSafeAt_iff_circleAvoidsAt
    (B E q N j : ℕ) (hB : 0 < B) (hq : 0 < q)
    (hN : N < B) (hj : j < q) (hE : E < B) :
    integerSafeAt B E q N j ↔ circleAvoidsAt B E q N j := by
  exact not_congr (integerUnsafeAt_iff_circleUnsafeAt B E q N j hB hq hN hj hE)

/-- Every fiber of the ordinary integer intersection test has the grid bound
`E / q + 2`. -/
def ordinaryUnsafeFiber (B E q j : ℕ) : Finset ℕ := by
  classical
  exact Finset.range B |>.filter fun N ↦ ordinaryUnsafeAt B E q N j

/-- Multiples of a positive integer in an interval of length `L` occupy at
most `L / q + 1` integer positions. -/
theorem card_mul_interval_le
    (S : Finset ℕ) (q A L : ℕ) (hq : 0 < q)
    (hS : ∀ n ∈ S, A ≤ q * n ∧ q * n ≤ A + L) :
    S.card ≤ L / q + 1 := by
  have hadd : (A + L) / q ≤ A / q + L / q + 1 := by
    rw [Nat.add_div hq]
    split <;> omega
  by_cases hr : A % q = 0
  · have hA : q * (A / q) = A := by
      have h := Nat.div_add_mod A q
      omega
    have hdiv : (A + L) / q = A / q + L / q := by
      rw [Nat.add_div_of_dvd_right]
      exact (Nat.dvd_iff_mod_eq_zero).2 hr
    calc
      S.card ≤ (Finset.Icc (A / q) (A / q + L / q)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_Icc]
        obtain ⟨hl, hu⟩ := hS n hn
        constructor
        · apply Nat.le_of_mul_le_mul_left
          · rw [hA]
            exact hl
          · exact hq
        · rw [← hdiv]
          exact (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hu)
      _ = L / q + 1 := by
        rw [Nat.card_Icc,
          show A / q + L / q + 1 = A / q + (L / q + 1) by omega,
          Nat.add_sub_cancel_left]
  · have hrem : 0 < A % q := Nat.pos_of_ne_zero hr
    have hdecomp : q * (A / q) + A % q = A := by
      simpa [Nat.mul_comm] using Nat.div_add_mod A q
    calc
      S.card ≤ (Finset.Icc (A / q + 1) (A / q + L / q + 1)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_Icc]
        obtain ⟨hl, hu⟩ := hS n hn
        constructor
        · apply Nat.lt_of_mul_lt_mul_left
          have hbase : q * (A / q) < A := by omega
          exact hbase.trans_le hl
        · have hn : n ≤ (A + L) / q :=
            (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hu)
          exact hn.trans hadd
      _ = L / q + 1 := by
        rw [Nat.card_Icc,
          show A / q + L / q + 1 + 1 = (A / q + 1) + (L / q + 1) by omega,
          Nat.add_sub_cancel_left]

theorem ordinaryUnsafeFiber_card_le (B E q j : ℕ) (hq : 0 < q) :
    (ordinaryUnsafeFiber B E q j).card ≤ E / q + 2 := by
  classical
  let S := ordinaryUnsafeFiber B E q j
  let T := S.image (fun N ↦ N + 1)
  have hT := card_mul_interval_le T q (B * j) (E + q) hq (by
    intro M hM
    rcases Finset.mem_image.mp hM with ⟨N, hNS, rfl⟩
    have hN := (Finset.mem_filter.mp hNS).2
    rcases hN with ⟨hupper, hlower⟩
    constructor
    · exact hlower
    · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Nat.add_le_add_right hupper q)
  rw [Finset.card_image_of_injective S (by
    intro x y hxy
    exact Nat.add_right_cancel hxy)] at hT
  simpa [T, S, Nat.add_div_of_dvd_left (dvd_refl q), Nat.div_self hq] using hT

/-- One endpoint-inclusive unsafe fiber. -/
def integerUnsafeFiber (B E q : ℕ) (j : Fin q) : Finset (Fin B) := by
  classical
  exact Finset.univ.filter fun N ↦ integerUnsafeAt B E q N.val j.val

theorem integerUnsafeFiber_card_le (B E q : ℕ) (j : Fin q) (hq : 0 < q) :
    (integerUnsafeFiber B E q j).card ≤ E / q + 2 := by
  classical
  by_cases hj : j.val = 0
  · let target := Finset.Icc 0 (E / q) ∪ {B - 1}
    calc
      (integerUnsafeFiber B E q j).card ≤ target.card := by
        apply Finset.card_le_card_of_injOn (fun N : Fin B ↦ N.val)
        · intro N hN
          have hunsafe := (Finset.mem_filter.mp hN).2
          change N.val ∈ target
          simp only [target, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
          rcases hunsafe with hord | hend
          · left
            constructor
            · exact Nat.zero_le _
            · exact (Nat.le_div_iff_mul_le hq).2
                (by simpa [ordinaryUnsafeAt, hj, Nat.mul_comm] using hord.1)
          · right
            unfold wrapEndpointAt at hend
            omega
        · intro N hN M hM hNM
          exact Fin.ext hNM
      _ ≤ (Finset.Icc 0 (E / q)).card + ({B - 1} : Finset ℕ).card :=
        by simpa [target] using
          (Finset.card_union_le (Finset.Icc 0 (E / q)) ({B - 1} : Finset ℕ))
      _ = E / q + 2 := by simp
  · calc
      (integerUnsafeFiber B E q j).card ≤ (ordinaryUnsafeFiber B E q j.val).card := by
        apply Finset.card_le_card_of_injOn (fun N : Fin B ↦ N.val)
        · intro N hN
          have hunsafe := (Finset.mem_filter.mp hN).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr N.isLt, ?_⟩
          rcases hunsafe with hord | hend
          · exact hord
          · exact False.elim (hj hend.2)
        · intro N hN M hM hNM
          exact Fin.ext hNM
      _ ≤ E / q + 2 := ordinaryUnsafeFiber_card_le B E q j.val hq

theorem unsafeCodes_card_le (B E q : ℕ) (hq : 0 < q) :
    (unsafeCodes B E q).card ≤ E + 2 * q := by
  classical
  have heq : unsafeCodes B E q =
      Finset.univ.biUnion (integerUnsafeFiber B E q) := by
    ext N
    simp [unsafeCodes, integerUnsafeFiber]
  rw [heq]
  calc
    (Finset.univ.biUnion (integerUnsafeFiber B E q)).card ≤
        (Finset.univ : Finset (Fin q)).card * (E / q + 2) :=
      Finset.card_biUnion_le_card_mul _ _ _
        (fun j _ ↦ integerUnsafeFiber_card_le B E q j hq)
    _ = q * (E / q + 2) := by simp
    _ = (E / q) * q + 2 * q := by ring
    _ ≤ E + 2 * q := Nat.add_le_add_right (Nat.div_mul_le_self E q) (2 * q)

/-- Sharp T6 safety-list cardinality bounds. The first two inequalities are
the estimates `|F_U| ≤ E+2q` and `|F| ≤ 2E+2q`; `q ≤ E` gives `|F| ≤ 4E`. -/
theorem safetyList_cardinality_bound_of_exponent
    (b q k e : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hqe : q ≤ b ^ e) :
    (safetyList b (k + e) (b ^ e) q).card ≤ b ^ e + 2 * q ∧
      (forbiddenListWithExponent b q k e).card ≤ 2 * b ^ e + 2 * q ∧
      (forbiddenListWithExponent b q k e).card ≤ 4 * b ^ e := by
  classical
  let code : (Fin (k + e) → Fin b) → Fin (b ^ (k + e)) := blockCode
  have hSafety : (safetyList b (k + e) (b ^ e) q).card ≤
      (unsafeCodes (b ^ (k + e)) (b ^ e) q).card := by
    apply Finset.card_le_card_of_injOn code
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩
    · exact (blockCode_injective b (k + e)).injOn
  have hSafetyBound : (safetyList b (k + e) (b ^ e) q).card ≤ b ^ e + 2 * q :=
    hSafety.trans (unsafeCodes_card_le (b ^ (k + e)) (b ^ e) q (by omega))
  have hZero : (zeroPrefixList b k e).card ≤ b ^ e := by
    let suffix : (Fin (k + e) → Fin b) → (Fin e → Fin b) :=
      fun u i ↦ u (Fin.natAdd k i)
    calc
      (zeroPrefixList b k e).card ≤ (Finset.univ : Finset (Fin e → Fin b)).card := by
        apply Finset.card_le_card_of_injOn suffix
        · exact fun _ _ ↦ Finset.mem_univ _
        · intro u hu v hv hsuffix
          apply funext
          intro i
          obtain ⟨a | c, hi⟩ := finSumFinEquiv.surjective i
          · rw [← hi, finSumFinEquiv_apply_left]
            have hu0 := (Finset.mem_filter.mp hu).2 a
            have hv0 := (Finset.mem_filter.mp hv).2 a
            apply Fin.ext
            exact hu0.trans hv0.symm
          · rw [← hi, finSumFinEquiv_apply_right]
            exact congrFun hsuffix c
      _ = b ^ e := by simp
  have hForbidden : (forbiddenListWithExponent b q k e).card ≤
      2 * b ^ e + 2 * q := by
    calc
      (forbiddenListWithExponent b q k e).card ≤
          (safetyList b (k + e) (b ^ e) q).card + (zeroPrefixList b k e).card :=
        by simpa [forbiddenListWithExponent] using
          (Finset.card_union_le (safetyList b (k + e) (b ^ e) q)
            (zeroPrefixList b k e))
      _ ≤ (b ^ e + 2 * q) + b ^ e := Nat.add_le_add hSafetyBound hZero
      _ = 2 * b ^ e + 2 * q := by omega
  refine ⟨hSafetyBound, hForbidden, hForbidden.trans ?_⟩
  omega

/-- Sharp cardinality bounds for the canonical T6 safety and forbidden lists. -/
theorem safetyList_cardinality_bound
    (b q k : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) :
    (canonicalSafetyList b q k).card ≤ b ^ canonicalExponent b q + 2 * q ∧
      (forbiddenList b q k).card ≤ 2 * b ^ canonicalExponent b q + 2 * q ∧
      (forbiddenList b q k).card ≤ 4 * b ^ canonicalExponent b q := by
  simpa [canonicalSafetyList, forbiddenList] using
    safetyList_cardinality_bound_of_exponent b q k (canonicalExponent b q) hb hq
      (canonicalExponent_spec b q hb).1

/-- Infinite base-`b` digit sequences. -/
abbrev DigitSequence (b : ℕ) := ℕ → Fin b

/-- Endpoint-complete carry witnesses use every layer from `-1` through `q`. -/
def EndpointCarryWitness (b q : ℕ) (x y : DigitSequence b) : Prop :=
  ∃ c : ℕ → ℤ, ∀ n,
    c n ∈ CarrySet q ∧ CarryStep b q (c n) (c (n + 1)) (x n).val (y n).val

/-- Circle evaluation of a digit sequence using mathlib's convergent series. -/
noncomputable def piB {b : ℕ} (x : DigitSequence b) : UnitAddCircle :=
  (Real.ofDigits x : UnitAddCircle)

/-- The sequence shifted left by `n` digits. -/
def shift {b : ℕ} (n : ℕ) (x : DigitSequence b) : DigitSequence b :=
  fun i ↦ x (i + n)

/-- Avoidance of the constant word `0^k` at every start. -/
def avoidsZeroWord {b : ℕ} (k : ℕ) (x : DigitSequence b) : Prop :=
  ∀ n, ¬∀ i : Fin k, (x (n + i.val)).val = 0

/-- Canonical endpoint-inclusive survivor relation: an output expansion is
existentially quantified, so both expansions at base-`b` endpoints are allowed. -/
def YZero (b q k : ℕ) : Set (DigitSequence b) :=
  {x | avoidsZeroWord k x ∧
    ∃ y : DigitSequence b, avoidsZeroWord k y ∧ piB y = q • piB x}

/-- The T6 SFT at an explicitly supplied exponent. -/
def ZSetWithExponent (b q k e : ℕ) : Set (DigitSequence b) :=
  {x | ∀ n, (fun i : Fin (k + e) ↦ x (n + i.val)) ∉
    forbiddenListWithExponent b q k e}

/-- The named T6 SFT `Z_{b,q,k}`, using the least admissible exponent. -/
def ZSet (b q k : ℕ) : Set (DigitSequence b) :=
  ZSetWithExponent b q k (canonicalExponent b q)

theorem real_coe_nat_eq_zero (n : ℕ) : ((n : ℝ) : UnitAddCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
  exact ⟨n, by simp⟩

theorem piB_shift_one (b : ℕ) (hb : 2 ≤ b) (x : DigitSequence b) :
    piB (shift 1 x) = b • piB x := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hreal := Real.ofDigits_eq_sum_add_ofDigits x 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Real.ofDigitsTerm, pow_one] at hreal ⊢
  have hscaled : (b : ℝ) * Real.ofDigits x = x 0 + Real.ofDigits (fun i ↦ x (i + 1)) := by
    field_simp [hbR] at hreal
    nlinarith
  change (Real.ofDigits (fun i ↦ x (i + 1)) : UnitAddCircle) =
    b • (Real.ofDigits x : UnitAddCircle)
  rw [← AddCircle.coe_nsmul (p := (1 : ℝ))]
  simp only [nsmul_eq_mul]
  rw [hscaled, AddCircle.coe_add, real_coe_nat_eq_zero]
  simp

theorem piB_shift (b : ℕ) (hb : 2 ≤ b) (x : DigitSequence b) (n : ℕ) :
    piB (shift n x) = b ^ n • piB x := by
  induction n with
  | zero =>
      rw [pow_zero, one_nsmul]
      congr 1
  | succ n ih =>
      calc
        piB (shift (n + 1) x) = piB (shift 1 (shift n x)) := by
          congr 1
          funext i
          simp [shift, Nat.add_comm, Nat.add_left_comm]
        _ = b • piB (shift n x) := piB_shift_one b hb (shift n x)
        _ = b • (b ^ n • piB x) := by rw [ih]
        _ = b ^ (n + 1) • piB x := by
          rw [← mul_nsmul', pow_succ]
          congr 1
          exact Nat.mul_comm _ _

/-- Every circle point has an endpoint-inclusive base-`b` expansion. -/
theorem exists_digit_expansion (b : ℕ) (hb : 2 ≤ b) (z : UnitAddCircle) :
    ∃ y : DigitSequence b, piB y = z := by
  let r : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z).val
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [r] using (AddCircle.equivIco (1 : ℝ) 0 z).property
  letI : NeZero b := ⟨by omega⟩
  refine ⟨Real.digits r b, ?_⟩
  rw [piB, Real.ofDigits_digits (by omega) hr]
  change (r : UnitAddCircle) = z
  simpa [r] using (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z

/-- The finite digit sum is the most-significant-first block numeral divided
by the level denominator. -/
theorem prefixSum_eq_blockCode_div (b m : ℕ) (hb : 0 < b) (x : DigitSequence b) :
    (∑ i ∈ Finset.range m, Real.ofDigitsTerm x i) =
      (blockCode (fun i : Fin m ↦ x i.val)).val / (b ^ m : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Real.ofDigitsTerm, blockCode, finFunctionFinEquiv_apply]
  rw [Nat.cast_sum]
  conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
  rw [Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.revPerm_apply]
  have hsum : i.rev.val + 1 + i.val = m := by
    simp [Fin.rev]
    omega
  have hpow : (b : ℝ) ^ m = (b : ℝ) ^ (i.rev.val + 1) * (b : ℝ) ^ i.val := by
    rw [← pow_add, hsum]
  rw [hpow]
  field_simp

/-- Every endpoint expansion with a fixed prefix lies in its closed cylinder. -/
theorem ofDigits_mem_cylinder (b m : ℕ) (hb : 0 < b) (x : DigitSequence b) :
    Real.ofDigits x ∈ Set.Icc
      ((blockCode (fun i : Fin m ↦ x i.val)).val / (b ^ m : ℝ))
      (((blockCode (fun i : Fin m ↦ x i.val)).val + 1) / (b ^ m : ℝ)) := by
  rw [Real.ofDigits_eq_sum_add_ofDigits x m, prefixSum_eq_blockCode_div b m hb x]
  have hpow : (0 : ℝ) < (b : ℝ) ^ m := by positivity
  have htail0 := Real.ofDigits_nonneg (fun i ↦ x (i + m))
  have htail1 := Real.ofDigits_le_one (fun i ↦ x (i + m))
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (by positivity) htail0)
  · calc
      (blockCode (fun i : Fin m ↦ x i.val)).val / (b ^ m : ℝ) +
          ((b : ℝ) ^ m)⁻¹ * Real.ofDigits (fun i ↦ x (i + m)) ≤
          (blockCode (fun i : Fin m ↦ x i.val)).val / (b ^ m : ℝ) +
            ((b : ℝ) ^ m)⁻¹ * 1 := by
        gcongr
      _ = ((blockCode (fun i : Fin m ↦ x i.val)).val + 1) / (b ^ m : ℝ) := by
        field_simp

theorem piB_mem_prefix_cylinderArc (b m : ℕ) (hb : 0 < b) (x : DigitSequence b) :
    piB x ∈ cylinderArc (b ^ m) (blockCode (fun i : Fin m ↦ x i.val)).val := by
  exact ⟨Real.ofDigits x, by simpa [Nat.cast_pow] using ofDigits_mem_cylinder b m hb x, rfl⟩

theorem ofDigits_le_invPow_of_zero_prefix
    (b k : ℕ) (hb : 0 < b) (y : DigitSequence b)
    (hy : ∀ i : Fin k, (y i.val).val = 0) :
    Real.ofDigits y ≤ ((b : ℝ) ^ k)⁻¹ := by
  let z : DigitSequence b := fun _ ↦ ⟨0, hb⟩
  have hprefix : ∀ i < k, y i = z i := by
    intro i hi
    apply Fin.ext
    simpa [z] using hy ⟨i, hi⟩
  have hbound := Real.abs_ofDigits_sub_ofDigits_le hprefix
  have hz : Real.ofDigits z = 0 := by
    simp [Real.ofDigits, Real.ofDigitsTerm, z]
  rw [hz, sub_zero, abs_of_nonneg (Real.ofDigits_nonneg y)] at hbound
  exact hbound

/-- If an endpoint expansion of `q*piB x` begins with `0^k`, then `piB x`
lies in one of the closed danger arcs, including the wraparound component. -/
theorem exists_dangerArc_of_zero_output
    (b q k e : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (x y : DigitSequence b) (hxy : piB y = q • piB x)
    (hyzero : ∀ i : Fin k, (y i.val).val = 0) :
    ∃ j : Fin q, piB x ∈ dangerArc (b ^ (k + e)) (b ^ e) q j.val := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hBR : (0 : ℝ) < (b : ℝ) ^ (k + e) := by positivity
  have hqBR : (0 : ℝ) < (q : ℝ) * (b : ℝ) ^ (k + e) := mul_pos hqR hBR
  let X := Real.ofDigits x
  let Y := Real.ofDigits y
  have hX0 : (0 : ℝ) ≤ X := Real.ofDigits_nonneg x
  have hX1 : X ≤ 1 := Real.ofDigits_le_one x
  have hY0 : (0 : ℝ) ≤ Y := Real.ofDigits_nonneg y
  have hYsmall : Y ≤ ((b : ℝ) ^ k)⁻¹ :=
    ofDigits_le_invPow_of_zero_prefix b k (by omega) y hyzero
  have hInvLt : ((b : ℝ) ^ k)⁻¹ < 1 := by
    apply (inv_lt_one₀ (by positivity)).2
    have hb1R : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
    exact one_lt_pow₀ hb1R (by omega)
  have hxy' : (Y : UnitAddCircle) = ((q : ℝ) * X : UnitAddCircle) := by
    simpa only [piB, X, Y, ← AddCircle.coe_nsmul (p := (1 : ℝ)), nsmul_eq_mul]
      using hxy
  have hzero : (((q : ℝ) * X - Y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr hxy'.symm
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 hzero with ⟨z, hz⟩
  have hzreal : (z : ℝ) = (q : ℝ) * X - Y := by
    simpa [zsmul_eq_mul] using hz
  have hzgt : (-1 : ℝ) < z := by rw [hzreal]; nlinarith
  have hznonneg : (0 : ℤ) ≤ z := by
    have : (-1 : ℤ) < z := by exact_mod_cast hzgt
    omega
  have hzleR : (z : ℝ) ≤ q := by rw [hzreal]; nlinarith
  have hzle : z ≤ (q : ℤ) := by exact_mod_cast hzleR
  by_cases hzq : z = (q : ℤ)
  · have hXeq : X = 1 := by rw [hzq] at hzreal; norm_num at hzreal; nlinarith
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hpi : piB x = 0 := by
      change (X : UnitAddCircle) = 0
      rw [hXeq]
      exact AddCircle.coe_period (1 : ℝ)
    rw [hpi]
    exact ⟨(0 : ℝ), ⟨by simp, by positivity⟩, rfl⟩
  · have hzlt : z < (q : ℤ) := lt_of_le_of_ne hzle hzq
    have hnatInt : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
    let j : Fin q := ⟨z.toNat, by
      have hint : (z.toNat : ℤ) < (q : ℤ) := by rw [hnatInt]; exact hzlt
      have : z.toNat < q := by exact_mod_cast hint
      exact this⟩
    have hjcast : (j.val : ℝ) = z := by
      norm_cast
    have hratio : (b : ℝ) ^ e / (b : ℝ) ^ (k + e) = ((b : ℝ) ^ k)⁻¹ := by
      rw [pow_add]
      field_simp
    have hlower : (j.val : ℝ) / q ≤ X := by
      apply (div_le_iff₀ hqR).2
      rw [hjcast, hzreal]
      nlinarith
    have hupper : X ≤
        (((b : ℝ) ^ (k + e)) * j.val + (b : ℝ) ^ e) /
          ((q : ℝ) * (b : ℝ) ^ (k + e)) := by
      apply (le_div_iff₀ hqBR).2
      have hqX : (q : ℝ) * X ≤ (j.val : ℝ) + (b : ℝ) ^ e / (b : ℝ) ^ (k + e) := by
        rw [hjcast, hratio, hzreal]
        nlinarith
      have := mul_le_mul_of_nonneg_right hqX hBR.le
      calc
        X * ((q : ℝ) * (b : ℝ) ^ (k + e)) =
            ((q : ℝ) * X) * (b : ℝ) ^ (k + e) := by ring
        _ ≤ ((j.val : ℝ) + (b : ℝ) ^ e / (b : ℝ) ^ (k + e)) *
            (b : ℝ) ^ (k + e) := this
        _ = (b : ℝ) ^ (k + e) * j.val + (b : ℝ) ^ e := by
          field_simp
    refine ⟨j, ?_⟩
    exact ⟨X, ⟨hlower, by simpa [Nat.cast_pow] using hupper⟩, rfl⟩

/-- The arithmetic bridge required by T6: avoiding the finite safety list
produces a canonical existential output which also avoids `0^k`. -/
theorem ZSetWithExponent_subset_YZero
    (b q k e : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q)
    (he : q ≤ b ^ e) (hk : 2 ≤ k) :
    ZSetWithExponent b q k e ⊆ YZero b q k := by
  classical
  intro x hxZ
  have hbpos : 0 < b := by omega
  have hBpos : 0 < b ^ (k + e) := pow_pos hbpos _
  have hEsmall : b ^ e < b ^ (k + e) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro n hzero
    apply hxZ n
    apply Finset.mem_union_right (safetyList b (k + e) (b ^ e) q)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    simpa using hzero i
  · rcases exists_digit_expansion b hb (q • piB x) with ⟨y, hy⟩
    refine ⟨y, ?_, hy⟩
    intro n hyzero
    let xs := shift n x
    let ys := shift n y
    have hyzero' : ∀ i : Fin k, (ys i.val).val = 0 := by
      intro i
      simpa [ys, shift, Nat.add_comm] using hyzero i
    have hshiftEq : piB ys = q • piB xs := by
      calc
        piB ys = b ^ n • piB y := piB_shift b hb y n
        _ = b ^ n • (q • piB x) := by rw [hy]
        _ = q • (b ^ n • piB x) := nsmul_left_comm _ _ _
        _ = q • piB xs := by rw [piB_shift b hb x n]
    rcases exists_dangerArc_of_zero_output b q k e hb hq (by omega) xs ys hshiftEq
      hyzero' with ⟨j, hjDanger⟩
    let u : Fin (k + e) → Fin b := fun i ↦ x (n + i.val)
    have huCell : piB xs ∈ cylinderArc (b ^ (k + e)) (blockCode u).val := by
      simpa [xs, u, shift, Nat.add_comm] using
        piB_mem_prefix_cylinderArc b (k + e) hbpos xs
    have hcircle : circleUnsafeAt (b ^ (k + e)) (b ^ e) q (blockCode u).val j.val :=
      ⟨piB xs, huCell, hjDanger⟩
    have hinteger := (integerUnsafeAt_iff_circleUnsafeAt
      (b ^ (k + e)) (b ^ e) q (blockCode u).val j.val hBpos (by omega)
      (blockCode u).isLt j.isLt hEsmall).2 hcircle
    have huSafety : u ∈ safetyList b (k + e) (b ^ e) q := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨j, hinteger⟩⟩
    exact hxZ n (Finset.mem_union_left (zeroPrefixList b k e) huSafety)

/-- The canonical T6 arithmetic inclusion `Z_{b,q,k} ⊆ Y_{b,0^k,q}`. -/
theorem ZSet_subset_YZero
    (b q k : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    ZSet b q k ⊆ YZero b q k := by
  simpa [ZSet] using
    ZSetWithExponent_subset_YZero b q k (canonicalExponent b q) hb hq
      (canonicalExponent_spec b q hb).1 hk

#print axioms Theory.Shared.DigitAutomata.T13.canonicalExponent_spec
#print axioms Theory.Shared.DigitAutomata.T13.safetyList_cardinality_bound
#print axioms Theory.Shared.DigitAutomata.T13.integerSafeAt_iff_circleAvoidsAt
#print axioms Theory.Shared.DigitAutomata.T13.ZSet_subset_YZero

end
end Theory.Shared.DigitAutomata.T13

