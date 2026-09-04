import TheoryLib.PiPositiveLowerBlockDensity.T2StrictHierarchyWitnesses
import TheoryLib.PiDigits.T22ChampernowneDisjunctive
import TheoryLib.PiDigits.T25ChampernowneNormality
import TheoryLib.PiDigits.T48ScaledOneHotDigitOne
import TheoryLib.PiQuantitativeBlockHitting.T208T208GenericEndpointRecurrence
import Mathlib

/-!
# T210: word hierarchy and separator witnesses

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t210; each task compiled and
axiom-checked; assembled by Claude Opus 5

Every task embedded T208's starter definitions verbatim because T208 was not
yet promoted.  Those embedded copies are byte-identical to the promoted
`TheoryLib/PiQuantitativeBlockHitting/T208T208GenericEndpointRecurrence.lean`
definitions (task 04 renames the bound variable `ℓ` to `ell` in `ZeroRun` and
`MaxRun`, which it never uses), so they are dropped here in favour of the
import.
-/

namespace Theory.PiDigits.T210WordHierarchy

open Topology

def Occurs {b : ℕ} (w : List (Fin b)) (a : ℕ → Fin b) : Prop :=
  ∃ n, ∀ i : Fin w.length, a (n + i) = w.get i
def Disjunctive {b : ℕ} (a : ℕ → Fin b) : Prop :=
  ∀ w : List (Fin b), Occurs w a
def EveryDigitOccurs {b : ℕ} (a : ℕ → Fin b) : Prop :=
  ∀ d, ∃ n, a n = d

/-! ### The hierarchy implications

Tasks `pi-t210-hierarchy-01-normal-implies-disjunctive` and
`pi-t210-hierarchy-02-disjunctive-every-digit`. -/

section
variable {b : ℕ} {a : ℕ → Fin b}

theorem normal_implies_disjunctive
    (hfreq : ∀ w : List (Fin b), w ≠ [] →
      Filter.Tendsto (fun N =>
        ((Finset.filter (fun n => ∀ i : Fin w.length, a (n + i) = w.get i)
          (Finset.range N)).card : ℝ) / N)
        Filter.atTop (𝓝 (1 / (b : ℝ) ^ w.length))) :
    Disjunctive a := by
  intro w
  rcases eq_or_ne w [] with rfl | hw
  · refine ⟨0, ?_⟩
    intro i
    exact absurd i.isLt (by simp)
  · by_contra hcon
    have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (a 0).isLt
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
    have hempty : ∀ N : ℕ,
        (Finset.filter (fun n => ∀ i : Fin w.length, a (n + i) = w.get i)
          (Finset.range N)) = ∅ := by
      intro N
      rw [Finset.filter_eq_empty_iff]
      intro m _ hp
      exact hcon ⟨m, hp⟩
    have hzero : (fun N : ℕ =>
        ((Finset.filter (fun n => ∀ i : Fin w.length, a (n + i) = w.get i)
          (Finset.range N)).card : ℝ) / N) = fun _ : ℕ => (0 : ℝ) := by
      funext N
      rw [hempty N]
      simp
    have h1 := hfreq w hw
    rw [hzero] at h1
    have h2 : (0 : ℝ) = 1 / (b : ℝ) ^ w.length :=
      tendsto_nhds_unique tendsto_const_nhds h1
    have hpos : (0 : ℝ) < 1 / (b : ℝ) ^ w.length := one_div_pos.2 (pow_pos hbR _)
    linarith
theorem disjunctive_implies_everyDigitOccurs :
    Disjunctive a → EveryDigitOccurs a := by
  intro h d
  obtain ⟨n, hn⟩ := h [d]
  refine ⟨n, ?_⟩
  have hv := hn ⟨0, by simp⟩
  simpa using hv
end

/-! ### The every-digit separator

Task `pi-t210-hierarchy-03-every-digit-separator`. -/

theorem exists_everyDigitOccurs_not_disjunctive :
    ∃ a : ℕ → Fin 10, EveryDigitOccurs a ∧ ¬ Disjunctive a := by
  refine ⟨fun n => (⟨n % 10, Nat.mod_lt _ (by norm_num)⟩ : Fin 10), ?_, ?_⟩
  · intro d
    refine ⟨d.val, ?_⟩
    apply Fin.ext
    show d.val % 10 = d.val
    exact Nat.mod_eq_of_lt d.isLt
  · intro hdisj
    obtain ⟨n, hn⟩ := hdisj [(0 : Fin 10), (0 : Fin 10)]
    have h0 := hn ⟨0, by simp⟩
    have h1 := hn ⟨1, by simp⟩
    have e0 : (n + 0) % 10 = 0 := congrArg Fin.val h0
    have e1 : (n + 1) % 10 = 0 := congrArg Fin.val h1
    omega
/-! ### The endpoint-recurrent separator

Task `pi-t210-hierarchy-04-endpoint-recurrent-separator`. -/

lemma frac_zero_val : Theory.PiDigits.T208GenericEndpointRecurrence.frac 0 = 0 := by
  rw [Theory.PiDigits.T208GenericEndpointRecurrence.frac]
  simp

lemma digit_ten_zero (n : ℕ) :
    Theory.PiDigits.T208GenericEndpointRecurrence.digit 10 n 0 = 0 := by
  rw [Theory.PiDigits.T208GenericEndpointRecurrence.digit]
  have h : ((10 : ℕ) : ℝ) ^ n * (0 : ℝ) = 0 := by ring
  rw [h, frac_zero_val]
  simp

theorem exists_endpoint_recurrent_not_disjunctive :
    ∃ (x : ℝ) (a : ℕ → Fin 10),
      Theory.PiDigits.T208GenericEndpointRecurrence.ApproachesZero 10 x ∧
      (∀ n : ℕ, (a n).val =
        Theory.PiDigits.T208GenericEndpointRecurrence.digit 10 n x) ∧
      ¬ Disjunctive a := by
  refine ⟨0, fun _ => (0 : Fin 10), ?_, ?_, ?_⟩
  · intro ε hε N
    refine ⟨N, le_refl N, ?_⟩
    have h : ((10 : ℕ) : ℝ) ^ N * (0 : ℝ) = 0 := by ring
    rw [h, frac_zero_val]
    exact hε
  · intro n
    rw [digit_ten_zero n]
    rfl
  · intro hdisj
    obtain ⟨n, hn⟩ := hdisj [(1 : Fin 10)]
    have hv := hn ⟨0, by simp⟩
    have hval : (0 : ℕ) = 1 := congrArg Fin.val hv
    exact absurd hval (by norm_num)
end Theory.PiDigits.T210WordHierarchy
