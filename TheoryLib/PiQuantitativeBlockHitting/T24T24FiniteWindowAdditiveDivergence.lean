import TheoryLib.PiQuantitativeBlockHitting.T22T22AllFixedFrequencyGap

/-!
# T24: simultaneous additive divergence on every finite frequency window

Source: `problems/local/pi-quantitative-block-hitting.txt`
SHA-256: `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`

T22 proves eventual additive divergence after fixing one nonzero integer
frequency.  This file performs the valid finite quantifier upgrade: after
fixing a finite frequency window and a real threshold, one common prefix
cutoff works for every frequency in the window and every later prefix.

The threshold here is fixed before the common cutoff is chosen.  It is not a
positive fraction of the later prefix length.  Consequently this theorem
does not provide the relative cancellation required by T19 and proves no
instance of decimal disjunctivity or normality.
-/

noncomputable section

open Finset

namespace Theory.PiDigits.FiniteWindowAdditiveDivergence

open Theory.PiDigits.AllFixedFrequencyGap

/-- Finitely many individual eventual assertions have one common cutoff. -/
lemma Finset.exists_common_eventual_cutoff
    {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (hP : ∀ i ∈ s, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P i N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i ∈ s, P i N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨Na, hNa⟩ := hP a (Finset.mem_insert_self a s)
      obtain ⟨Ns, hNs⟩ := ih (fun i hi ↦ hP i (Finset.mem_insert_of_mem hi))
      refine ⟨max Na Ns, ?_⟩
      intro N hN i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hNa N (le_trans (Nat.le_max_left Na Ns) hN)
      · exact hNs N (le_trans (Nat.le_max_right Na Ns) hN) i hi

/-- Every finite set of nonzero frequencies has simultaneous eventual
additive divergence at every prescribed real threshold. -/
theorem pi_finiteSet_additiveGap_eventually_ge
    (F : Finset ℤ) (hF : ∀ h ∈ F, h ≠ 0) (A : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ h ∈ F,
      A ≤ (N : ℝ) -
        ‖Theory.PiDigits.T27.exponentialSum
          Theory.PiDigits.T27.piFractionalOrbit N h‖ := by
  let P : ℤ → ℕ → Prop := fun h N ↦
    A ≤ (N : ℝ) -
      ‖Theory.PiDigits.T27.exponentialSum
        Theory.PiDigits.T27.piFractionalOrbit N h‖
  have heach : ∀ h ∈ F, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P h N := by
    intro h hh
    exact pi_fixedFrequency_additiveGap_eventually_ge h (hF h hh) A
  exact Finset.exists_common_eventual_cutoff F P heach

/-- Bounded-window form used by finite Fourier criteria.  The window is
fixed before the real threshold and the common cutoff are chosen. -/
theorem pi_finiteWindow_additiveGap_eventually_ge (H : ℕ) (A : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ h : ℤ,
      h ≠ 0 → h.natAbs ≤ H →
        A ≤ (N : ℝ) -
          ‖Theory.PiDigits.T27.exponentialSum
            Theory.PiDigits.T27.piFractionalOrbit N h‖ := by
  let F := Theory.PiDigits.T29.boundedFrequencies H
  have hnonzero : ∀ h ∈ F, h ≠ 0 := by
    intro h hh
    exact (Theory.PiDigits.T29.mem_boundedFrequencies_iff.mp hh).1
  obtain ⟨N₀, hN₀⟩ :=
    pi_finiteSet_additiveGap_eventually_ge F hnonzero A
  refine ⟨N₀, ?_⟩
  intro N hN h h0 hH
  exact hN₀ N hN h
    (Theory.PiDigits.T29.mem_boundedFrequencies_iff.mpr ⟨h0, hH⟩)

end Theory.PiDigits.FiniteWindowAdditiveDivergence
