import Mathlib

/-!
# T218: Rajchman orbit closure

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t218; each task compiled and
axiom-checked; assembled by Claude Opus 5
-/

noncomputable section

namespace Theory.PiDigits.T218RajchmanOrbitClosure

open Filter MeasureTheory Topology

noncomputable def orbit (b : ℕ) (x : UnitAddCircle) (n : ℕ) : UnitAddCircle :=
  (b ^ n) • x

def BaseDisjunctive (b : ℕ) (x : UnitAddCircle) : Prop :=
  DenseRange (orbit b x)

noncomputable def orbitClosure (b : ℕ) (x : UnitAddCircle) : Set UnitAddCircle :=
  closure (Set.range (orbit b x))

noncomputable def FourierCoeff (μ : Measure UnitAddCircle) (m : ℤ) : ℂ :=
  ∫ t, fourier (-m) t ∂μ

def Rajchman (μ : Measure UnitAddCircle) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ m : ℤ,
    M ≤ Int.natAbs m → ‖FourierCoeff μ m‖ < ε

def SupportsRajchman (E : Set UnitAddCircle) : Prop :=
  ∃ μ : Measure UnitAddCircle,
    IsProbabilityMeasure μ ∧ μ (Eᶜ) = 0 ∧ Rajchman μ

def NondisjunctiveUSetCoverInput
    (IsUSet : Set UnitAddCircle → Prop) : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ x : UnitAddCircle,
    ¬ BaseDisjunctive b x →
      ∃ E : Set UnitAddCircle,
        IsClosed E ∧ IsUSet E ∧ orbitClosure b x ⊆ E

def USetExcludesRajchman
    (IsUSet : Set UnitAddCircle → Prop) : Prop :=
  ∀ E : Set UnitAddCircle,
    IsClosed E → IsUSet E → ¬ SupportsRajchman E

/-- Nonzero Fourier coefficients of normalized Haar measure on the circle vanish. -/
lemma haar_fourierCoeff_eq_zero {m : ℤ} (hm : m ≠ 0) :
    FourierCoeff (AddCircle.haarAddCircle (T := (1 : ℝ))) m = 0 := by
  have h := fourierCoeff_fourier (T := (1 : ℝ)) (0 : ℤ)
  have h2 := congrFun h m
  rw [Pi.single_apply, if_neg hm] at h2
  rw [fourierCoeff] at h2
  simpa [FourierCoeff] using h2

lemma haar_rajchman : Rajchman (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
  intro ε hε
  refine ⟨1, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
  rw [haar_fourierCoeff_eq_zero hm0, norm_zero]
  exact hε

lemma disjunctive_supports_haar
    {b : ℕ} {x : UnitAddCircle} (hx : BaseDisjunctive b x) :
    SupportsRajchman (orbitClosure b x) := by
  have huniv : orbitClosure b x = (Set.univ : Set UnitAddCircle) := hx.closure_eq
  refine ⟨AddCircle.haarAddCircle (T := (1 : ℝ)), inferInstance, ?_, haar_rajchman⟩
  rw [huniv, Set.compl_univ, measure_empty]

theorem R1_conditional
    {IsUSet : Set UnitAddCircle → Prop}
    (hcover : NondisjunctiveUSetCoverInput IsUSet)
    (hexcl : USetExcludesRajchman IsUSet)
    {b : ℕ} (hb : 2 ≤ b) (x : UnitAddCircle) :
    SupportsRajchman (orbitClosure b x) ↔ BaseDisjunctive b x := by
  constructor
  · intro hsupp
    by_contra hnd
    obtain ⟨E, hEclosed, hEU, hsub⟩ := hcover b hb x hnd
    refine hexcl E hEclosed hEU ?_
    obtain ⟨μ, hprob, hnull, hraj⟩ := hsupp
    refine ⟨μ, hprob, ?_, hraj⟩
    have hmono : Eᶜ ⊆ (orbitClosure b x)ᶜ := Set.compl_subset_compl.mpr hsub
    exact measure_mono_null hmono hnull
  · intro hd
    exact disjunctive_supports_haar hd

end Theory.PiDigits.T218RajchmanOrbitClosure
