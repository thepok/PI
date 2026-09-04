import TheoryLib.PiPositiveLowerBlockDensity.T11T11HausdorffDimensionDefect
import TheoryLib.PiPositiveLowerBlockDensity.T12T12OverlappingForbiddenWordDimension
import TheoryLib.PiPositiveLowerBlockDensity.T13T13ForbiddenLanguageEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T14T14PrefixAutomatonCertificates
import TheoryLib.PiPositiveLowerBlockDensity.T15T15FinitePrefixIntrinsicEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T16T16MatrixPowerEntropy
import TheoryLib.PiPositiveLowerBlockDensity.T21T21FinitePrefixFrostman
import TheoryLib.PiPositiveLowerBlockDensity.T22T22DecimalBoundaryAmbiguity
import TheoryLib.PiQuantitativeBlockHitting.T206T206EndpointBridge
import TheoryLib.PiQuantitativeBlockHitting.T208T208GenericEndpointRecurrence
import TheoryLib.PiQuantitativeBlockHitting.T209T209EndpointCylinderBridge
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# T212: paper alignment for avoidance dimension

produced by Claude Opus 5 as a Pi Lab subagent on 2026-09-04 against the
contracted signatures of AllMath task pack t212; each task compiled and
axiom-checked; assembled by Claude Opus 5

The task artifacts embedded T208's and T209's starter definitions verbatim
because neither pack was promoted at the time.  Those embedded copies are
byte-identical to the now-promoted T208 and T209 modules, so they are dropped
here in favour of the imports.
-/

noncomputable section

namespace Theory.PiDigits.T212AvoidanceDimensionAlignment

abbrev CanonicalAvoids (w : List (Fin 10)) : Set ℝ :=
  Theory.PiDigits.T206EndpointBridge.CWord w

abbrev IntrinsicAvoids (w : List (Fin 10)) : Set ℝ :=
  Theory.PiDigits.T206EndpointBridge.KWordReal w

abbrev radixEndpoints : Set ℝ :=
  Theory.PiDigits.T206EndpointBridge.E10

abbrev DecimalWord (ell : ℕ) :=
  Theory.PiDigits.PositiveLowerBlockDensity.T12.DecimalWord ell

def wordValue (P : List (Fin 10)) : ℕ :=
  P.foldl (fun z d => 10 * z + d.val) 0

def PrefixCylinder (P : List (Fin 10)) : Set ℝ :=
  Set.Ico ((wordValue P : ℝ) / (10 : ℝ) ^ P.length)
    (((wordValue P : ℝ) + 1) / (10 : ℝ) ^ P.length)

def FullDimensionPrefixCopy (w P : List (Fin 10)) : Prop :=
  ∃ a : ℝ, ∃ q : ℕ,
    let f : ℝ → ℝ := fun x => a + x / (10 : ℝ) ^ q
    dimH (f '' CanonicalAvoids w) = dimH (CanonicalAvoids w) ∧
      f '' CanonicalAvoids w ⊆
        CanonicalAvoids w ∩ PrefixCylinder P

theorem canonical_eq_intrinsic_away_endpoints (w : List (Fin 10)) :
    CanonicalAvoids w \ radixEndpoints =
      IntrinsicAvoids w \ radixEndpoints := by
  ext x
  simp only [Set.mem_diff]
  constructor
  · rintro ⟨hC, hE⟩
    exact ⟨Theory.PiDigits.T206EndpointBridge.CWord_subset_KWordReal w hC, hE⟩
  · rintro ⟨hK, hE⟩
    refine ⟨?_, hE⟩
    by_contra hC
    exact hE
      (Theory.PiDigits.T206EndpointBridge.KWordReal_diff_CWord_subset_E10 w ⟨hK, hC⟩)

/-- The decimal endpoint set is countable. -/
lemma radixEndpoints_countable : radixEndpoints.Countable := by
  have h : radixEndpoints =
      Set.range (fun p : ℤ × ℕ => (p.1 : ℝ) / (10 : ℝ) ^ p.2) := by
    ext x
    constructor
    · rintro ⟨m, k, rfl⟩
      exact ⟨(m, k), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  rw [h]
  exact Set.countable_range _

/-- The endpoint set carries no Hausdorff dimension. -/
lemma dimH_radixEndpoints : dimH radixEndpoints = 0 :=
  radixEndpoints_countable.dimH_zero

/-- T206's countable endpoint transfer: the canonical and intrinsic avoidance
sets have the same Hausdorff dimension. -/
lemma dimH_canonical_eq_intrinsic (v : List (Fin 10)) :
    dimH (CanonicalAvoids v) = dimH (IntrinsicAvoids v) := by
  refine le_antisymm
    (dimH_mono (Theory.PiDigits.T206EndpointBridge.CWord_subset_KWordReal v)) ?_
  have hsub : IntrinsicAvoids v ⊆ CanonicalAvoids v ∪ radixEndpoints := by
    intro x hx
    by_cases hc : x ∈ CanonicalAvoids v
    · exact Or.inl hc
    · exact Or.inr
        (Theory.PiDigits.T206EndpointBridge.KWordReal_diff_CWord_subset_E10 v ⟨hx, hc⟩)
  calc
    dimH (IntrinsicAvoids v) ≤ dimH (CanonicalAvoids v ∪ radixEndpoints) :=
      dimH_mono hsub
    _ = max (dimH (CanonicalAvoids v)) (dimH radixEndpoints) := dimH_union _ _
    _ = dimH (CanonicalAvoids v) := by
        rw [dimH_radixEndpoints]
        simp

theorem dimH_avoidance
    {ell : ℕ} (hell : 0 < ell) (w : DecimalWord ell) (rho : ℝ)
    (hIntrinsicDimension :
      dimH (IntrinsicAvoids (List.ofFn w)) =
        ENNReal.ofReal
          (Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenEntropy w /
            Real.log 10))
    (hPerron :
      Theory.PiDigits.PositiveLowerBlockDensity.T13.forbiddenEntropy w =
        Real.log rho) :
    dimH (CanonicalAvoids (List.ofFn w)) =
      ENNReal.ofReal (Real.log rho / Real.log 10) := by
  rw [dimH_canonical_eq_intrinsic, hIntrinsicDimension, hPerron]

theorem dimH_admissible_prefix
    (w P : List (Fin 10)) (hw : w ≠ [])
    (hPrefix : FullDimensionPrefixCopy w P) :
    dimH (CanonicalAvoids w ∩ PrefixCylinder P) =
      dimH (CanonicalAvoids w) := by
  obtain ⟨a, q, hdim, hsub⟩ := hPrefix
  refine le_antisymm (dimH_mono Set.inter_subset_left) ?_
  calc
    dimH (CanonicalAvoids w)
        = dimH ((fun x : ℝ => a + x / (10 : ℝ) ^ q) '' CanonicalAvoids w) := hdim.symm
    _ ≤ dimH (CanonicalAvoids w ∩ PrefixCylinder P) := dimH_mono hsub

-- The general-base starter layer of task
-- `pi-t212-dimension-01-countable-prefix-union`.  Its `CanonicalAvoids` and
-- `PrefixCylinder` are the base-`b` T208/T209 definitions, which clash by
-- name with the decimal T206 layer above, so that task is kept verbatim
-- inside this sub-namespace.
namespace BaseLayer

noncomputable section
def CanonicalAvoids (b : ℕ) (w : List (Fin b)) : Set ℝ :=
  {x | ∀ n, ∃ i : Fin w.length,
    Theory.PiDigits.T208GenericEndpointRecurrence.digit b (n + i) x ≠ (w.get i).val}
def PrefixCylinder (b : ℕ) (P : List (Fin b)) : Set ℝ :=
  Theory.PiDigits.T209EndpointCylinderBridge.cylinder b (P.map Fin.val)

variable {b : ℕ} {w : List (Fin b)}

theorem dimH_countable_prefix_union (A : ℕ → Set ℝ)
    (hA : ∀ n, ∃ P, A n = CanonicalAvoids b w ∩ PrefixCylinder b P) :
    dimH (⋃ n, A n) = ⨆ n, dimH (A n) :=
  dimH_iUnion A

end

end BaseLayer

end Theory.PiDigits.T212AvoidanceDimensionAlignment

end
