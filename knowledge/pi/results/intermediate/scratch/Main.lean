import Mathlib

theorem digit_stream_recurrent_digit (s : ℕ → Fin 10) :
    ∃ d : Fin 10, ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ s m = d := by
  classical
  by_contra h
  push Not at h
  let N : Fin 10 → ℕ := fun d => Classical.choose (h d)
  have hN : ∀ d : Fin 10, ∀ m : ℕ, N d ≤ m → s m ≠ d := by
    intro d m hm
    exact Classical.choose_spec (h d) m hm
  let M : ℕ := Finset.univ.sup N
  have hNM : ∀ d : Fin 10, N d ≤ M := by
    intro d
    exact Finset.le_sup (Finset.mem_univ d)
  have hne : s M ≠ s M := by
    apply hN (s M) M
    exact le_trans (hNM (s M)) (le_refl M)
  exact hne rfl
