import Mathlib

/-!
# T9: cyclic sparse-forbidden-list counting

Canonical source: `problems/local/multiplicative-avoidance-gap.txt`
SHA-256: `05d09b6edb60fa060cc952fc5b2fad9dea75c20d84ac628d86f1b6dd6b0ab7c8`

This module isolates the finite local-lemma argument used in the unverified T6
upper-bound note.  It does not define carries, endpoint expansions, `Y`,
`Gamma`, or C1.  In particular, the T6 list-cardinality estimate is an explicit
hypothesis of the final specialization rather than an imported assertion.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Theory.Shared.DigitAutomata.T9

section FiniteLocalLemma

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
  [Fintype ι] [DecidableEq ι]

/-- Outcomes avoiding every bad event indexed by `S`. -/
def avoids (bad : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ bad i

/-- Outcomes in event `i` while avoiding all events indexed by `S`. -/
def badAndAvoids (bad : ι → Finset Ω) (i : ι) (S : Finset ι) : Finset Ω :=
  bad i ∩ avoids bad S

/-- Real-valued counting mass.  No measure-theoretic normalization is hidden. -/
def mass (s : Finset Ω) : ℝ := s.card

@[simp] theorem avoids_empty (bad : ι → Finset Ω) :
    avoids bad ∅ = Finset.univ := by
  ext ω
  simp [avoids]

@[simp] theorem avoids_insert (bad : ι → Finset Ω) (i : ι) (S : Finset ι) :
    avoids bad (insert i S) = avoids bad S \ bad i := by
  ext ω
  simp [avoids, and_comm]

theorem badAndAvoids_subset_right (bad : ι → Finset Ω) (i : ι)
    {S T : Finset ι} (hTS : T ⊆ S) :
    badAndAvoids bad i S ⊆ badAndAvoids bad i T := by
  intro ω hω
  unfold badAndAvoids at hω ⊢
  rw [mem_inter] at hω ⊢
  refine ⟨hω.1, ?_⟩
  have hS : ∀ j ∈ S, ω ∉ bad j := (mem_filter.mp hω.2).2
  exact mem_filter.mpr ⟨mem_univ _, fun j hjT ↦ hS j (hTS hjT)⟩

theorem mass_avoids_insert_add (bad : ι → Finset Ω) (i : ι) (S : Finset ι) :
    mass (avoids bad (insert i S)) + mass (badAndAvoids bad i S) =
      mass (avoids bad S) := by
  classical
  rw [avoids_insert]
  unfold badAndAvoids mass
  rw [inter_comm]
  norm_cast
  exact Finset.card_sdiff_add_card_inter (avoids bad S) (bad i)

/-- The strong dependency condition used by the finite local lemma.  For a set
of nonneighbors, avoiding all corresponding events is exactly independent of
the event at `i`, expressed using integer cardinalities after clearing the
uniform denominator `|Ω|`. -/
def StrongDependency (bad : ι → Finset Ω) (neighbor : ι → Finset ι) : Prop :=
  ∀ i T, i ∉ T → (∀ j ∈ T, j ∉ neighbor i) →
    mass (badAndAvoids bad i T) * mass (Finset.univ : Finset Ω) =
      mass (bad i) * mass (avoids bad T)

/-- Iterating conditional event bounds over a finite set of new indices. -/
theorem avoids_union_prod_lower
    (bad : ι → Finset Ω) (z : ι → ℝ) (n : ℕ)
    (hz1 : ∀ i, z i < 1) (T N : Finset ι)
    (hcond : ∀ i S, S ⊆ T ∪ N → S.card < n → i ∉ S →
      mass (badAndAvoids bad i S) ≤ z i * mass (avoids bad S))
    (hTN : Disjoint T N) (hcard : (T ∪ N).card ≤ n) :
    (∏ i ∈ N, (1 - z i)) * mass (avoids bad T) ≤
      mass (avoids bad (T ∪ N)) := by
  classical
  induction N using Finset.induction_on with
  | empty => simp
  | @insert j N hj ih =>
      have hjT : j ∉ T := by
        intro hjmem
        exact Finset.disjoint_left.mp hTN hjmem (mem_insert_self j N)
      have hTN' : Disjoint T N :=
        hTN.mono_right (subset_insert j N)
      have hcard' : (T ∪ N).card ≤ n := by
        apply (card_le_card ?_).trans hcard
        intro x hx
        simp only [mem_union] at hx ⊢
        exact hx.imp_right mem_insert_of_mem
      have hsmallSubset : T ∪ N ⊆ T ∪ insert j N := by
        intro x hx
        simp only [mem_union] at hx ⊢
        exact hx.imp_right mem_insert_of_mem
      have hcond' : ∀ i S, S ⊆ T ∪ N → S.card < n → i ∉ S →
          mass (badAndAvoids bad i S) ≤ z i * mass (avoids bad S) := by
        intro i S hS hSn hiS
        exact hcond i S (hS.trans hsmallSubset) hSn hiS
      have hIH := ih hcond' hTN' hcard'
      have hjU : j ∉ T ∪ N := by simp [hjT, hj]
      have hUcard : (T ∪ N).card < n := by
        have hstrict : (T ∪ N).card < (T ∪ insert j N).card := by
          rw [show T ∪ insert j N = insert j (T ∪ N) by ext x; simp [or_assoc]]
          simp [hjU]
        exact hstrict.trans_le hcard
      have hbad := hcond j (T ∪ N) hsmallSubset hUcard hjU
      have hsplit := mass_avoids_insert_add bad j (T ∪ N)
      have hstep :
          (1 - z j) * mass (avoids bad (T ∪ N)) ≤
            mass (avoids bad (insert j (T ∪ N))) := by
        nlinarith
      rw [prod_insert hj]
      calc
        (1 - z j) * (∏ i ∈ N, (1 - z i)) * mass (avoids bad T) =
            (1 - z j) * ((∏ i ∈ N, (1 - z i)) * mass (avoids bad T)) := by ring
        _ ≤ (1 - z j) * mass (avoids bad (T ∪ N)) :=
          mul_le_mul_of_nonneg_left hIH (by linarith [hz1 j])
        _ ≤ mass (avoids bad (insert j (T ∪ N))) := hstep
        _ = mass (avoids bad (T ∪ insert j N)) := by
          congr 2
          ext x
          simp [or_assoc, or_left_comm]

/-- Finite asymmetric local lemma, in a cardinality-only formulation. -/
theorem finite_local_lemma_cardinality
    (bad : ι → Finset Ω) (neighbor : ι → Finset ι) (z : ι → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i < 1)
    (hdep : StrongDependency bad neighbor)
    (hlocal : ∀ i,
      mass (bad i) ≤ z i * (∏ j ∈ neighbor i, (1 - z j)) *
        mass (Finset.univ : Finset Ω)) :
    (∏ i : ι, (1 - z i)) * mass (Finset.univ : Finset Ω) ≤
      mass (avoids bad Finset.univ) := by
  classical
  have hmass_nonneg (s : Finset Ω) : 0 ≤ mass s := by
    unfold mass
    positivity
  have htotal : 0 < mass (Finset.univ : Finset Ω) := by
    unfold mass
    exact_mod_cast Fintype.card_pos
  have hcond : ∀ S : Finset ι, ∀ i, i ∉ S →
      mass (badAndAvoids bad i S) ≤ z i * mass (avoids bad S) := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        intro i hiS
        let T := S \ neighbor i
        let N := S ∩ neighbor i
        have hpart : T ∪ N = S := by
          ext x
          simp [T, N]
          tauto
        have hTN : Disjoint T N := by
          rw [Finset.disjoint_left]
          intro x hxT hxN
          exact (mem_sdiff.mp hxT).2 (mem_inter.mp hxN).2
        have hiT : i ∉ T := by
          intro hi
          exact hiS (mem_sdiff.mp hi).1
        have hTnon : ∀ j ∈ T, j ∉ neighbor i := by
          intro j hj
          exact (mem_sdiff.mp hj).2
        have hiter :
            (∏ j ∈ N, (1 - z j)) * mass (avoids bad T) ≤
              mass (avoids bad S) := by
          have hsmall : ∀ j U, U ⊆ T ∪ N → U.card < S.card → j ∉ U →
              mass (badAndAvoids bad j U) ≤ z j * mass (avoids bad U) := by
            intro j U hUS hcardU hjU
            have hUS' : U ⊆ S := by simpa [hpart] using hUS
            have hne : U ≠ S := by
              intro hEq
              subst U
              omega
            exact ih U (Finset.ssubset_iff_subset_ne.mpr ⟨hUS', hne⟩) j hjU
          have := avoids_union_prod_lower bad z S.card hz1 T N hsmall hTN
            (by simpa [hpart])
          simpa [hpart] using this
        have hprod :
            (∏ j ∈ neighbor i, (1 - z j)) ≤ ∏ j ∈ N, (1 - z j) := by
          apply Finset.prod_le_prod_of_subset_of_le_one
          · exact inter_subset_right
          · intro j _
            linarith [hz1 j]
          · intro j _ _
            linarith [hz0 j]
        have hhitSubset : badAndAvoids bad i S ⊆ badAndAvoids bad i T :=
          badAndAvoids_subset_right bad i sdiff_subset
        have hhitMass :
            mass (badAndAvoids bad i S) ≤ mass (badAndAvoids bad i T) := by
          unfold mass
          exact_mod_cast card_le_card hhitSubset
        have hdepEq := hdep i T hiT hTnon
        have hlocal' := hlocal i
        have hbadBound :
            mass (bad i) ≤ z i * (∏ j ∈ N, (1 - z j)) *
              mass (Finset.univ : Finset Ω) := by
          calc
            mass (bad i) ≤ z i * (∏ j ∈ neighbor i, (1 - z j)) *
                mass (Finset.univ : Finset Ω) := hlocal'
            _ ≤ z i * (∏ j ∈ N, (1 - z j)) *
                mass (Finset.univ : Finset Ω) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hprod (hz0 i))
                (hmass_nonneg Finset.univ)
        have hnum :
            mass (badAndAvoids bad i S) * mass (Finset.univ : Finset Ω) ≤
              z i * mass (avoids bad S) * mass (Finset.univ : Finset Ω) := by
          calc
            mass (badAndAvoids bad i S) * mass (Finset.univ : Finset Ω) ≤
                mass (badAndAvoids bad i T) * mass (Finset.univ : Finset Ω) := by
              gcongr
            _ = mass (bad i) * mass (avoids bad T) := hdepEq
            _ ≤ (z i * (∏ j ∈ N, (1 - z j)) *
                mass (Finset.univ : Finset Ω)) * mass (avoids bad T) := by
              exact mul_le_mul_of_nonneg_right hbadBound (hmass_nonneg _)
            _ = z i * ((∏ j ∈ N, (1 - z j)) * mass (avoids bad T)) *
                mass (Finset.univ : Finset Ω) := by ring
            _ ≤ z i * mass (avoids bad S) * mass (Finset.univ : Finset Ω) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hiter (hz0 i)) htotal.le
        nlinarith
  have hfinal := avoids_union_prod_lower bad z (Finset.univ : Finset ι).card hz1
    ∅ Finset.univ (fun i S _ hcard hiS ↦ hcond S i hiS)
      (Finset.disjoint_empty_left Finset.univ) (by simp)
  simpa using hfinal

/-- Symmetric degree form of the finite local lemma. -/
theorem symmetric_local_lemma_cardinality
    (bad : ι → Finset Ω) (neighbor : ι → Finset ι)
    (p z : ℝ) (d : ℕ)
    (hp0 : 0 ≤ p) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hdegree : ∀ i, (neighbor i).card ≤ d)
    (hdep : StrongDependency bad neighbor)
    (hbad : ∀ i, mass (bad i) ≤ p * mass (Finset.univ : Finset Ω))
    (hcriterion : p ≤ z * (1 - z) ^ d) :
    (1 - z) ^ Fintype.card ι * mass (Finset.univ : Finset Ω) ≤
      mass (avoids bad Finset.univ) := by
  classical
  have hbase0 : 0 ≤ 1 - z := by linarith
  have hbase1 : 1 - z ≤ 1 := by linarith
  have hmass : 0 ≤ mass (Finset.univ : Finset Ω) := by
    unfold mass
    positivity
  have hmain := finite_local_lemma_cardinality bad neighbor (fun _ ↦ z)
    (fun _ ↦ hz0) (fun _ ↦ hz1) hdep (fun i ↦ by
    calc
      mass (bad i) ≤ p * mass (Finset.univ : Finset Ω) := hbad i
      _ ≤ (z * (1 - z) ^ d) * mass (Finset.univ : Finset Ω) := by
        exact mul_le_mul_of_nonneg_right hcriterion hmass
      _ ≤ (z * (1 - z) ^ (neighbor i).card) *
          mass (Finset.univ : Finset Ω) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hbase0 hbase1 (hdegree i)) hz0)
          hmass
      _ = z * (∏ j ∈ neighbor i, (1 - z)) *
          mass (Finset.univ : Finset Ω) := by simp)
  simpa using hmain

end FiniteLocalLemma

section CyclicWords

/-- The length-`m` block beginning at `i` in a cyclic word of positive period
`n`.  Both the word length and cyclic period are explicit arguments. -/
def cyclicWindow (b n m : ℕ) (hn : 0 < n)
    (x : Fin n → Fin b) (i : Fin n) : Fin m → Fin b :=
  fun j ↦ x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

/-- Cyclic words whose window at `i` belongs to the forbidden list `F`. -/
def cyclicBadAt (b n m : ℕ) (hn : 0 < n)
    (F : Finset (Fin m → Fin b)) (i : Fin n) :
    Finset (Fin n → Fin b) :=
  Finset.univ.filter fun x ↦ cyclicWindow b n m hn x i ∈ F

/-- Cyclic words avoiding `F` at every one of their `n` cyclic starts. -/
def cyclicAvoiders (b n m : ℕ) (hn : 0 < n)
    (F : Finset (Fin m → Fin b)) : Finset (Fin n → Fin b) :=
  avoids (cyclicBadAt b n m hn F) Finset.univ

/-- The total number of period-`n` words over an alphabet of size `b`. -/
theorem mass_univ_cyclicWords (b n : ℕ) :
    mass (Finset.univ : Finset (Fin n → Fin b)) = (b : ℝ) ^ n := by
  unfold mass
  norm_cast
  simp [Fintype.card_congr (Equiv.refl (Fin n → Fin b))]

/-- Fully explicit cyclic sparse-list estimate.  `neighbor` may be any
dependency graph certificate.  Its degree bound, exact strong dependency,
and the single-window density bound are all visible hypotheses. -/
theorem cyclic_sparse_forbidden_count
    (b n m d : ℕ) (hb : 0 < b) (hn : 0 < n) (F : Finset (Fin m → Fin b))
    (neighbor : Fin n → Finset (Fin n)) (pbar : ℝ)
    (hp0 : 0 ≤ pbar) (hp4 : pbar ≤ 1 / 4)
    (hdegree : ∀ i, (neighbor i).card ≤ d)
    (hdep : StrongDependency (cyclicBadAt b n m hn F) neighbor)
    (hwindow : ∀ i,
      mass (cyclicBadAt b n m hn F i) ≤
        pbar * mass (Finset.univ : Finset (Fin n → Fin b)))
    (hsmall : 2 * d * pbar ≤ 1 / 2) :
    ((b : ℝ) * (1 - 2 * pbar)) ^ n ≤ (cyclicAvoiders b n m hn F).card := by
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have hz0 : 0 ≤ 2 * pbar := by positivity
  have hz1 : 2 * pbar < 1 := by linarith
  have hBernoulli : 1 - (d : ℝ) * (2 * pbar) ≤ (1 - 2 * pbar) ^ d := by
    convert one_add_mul_le_pow (a := -(2 * pbar)) (by linarith) d using 1 <;> ring
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 2 * pbar) ^ d := by
    have : (d : ℝ) * (2 * pbar) ≤ 1 / 2 := by
      have hsmall' := hsmall
      norm_num [Nat.cast_mul] at hsmall' ⊢
      nlinarith
    linarith
  have hcriterion : pbar ≤ (2 * pbar) * (1 - 2 * pbar) ^ d := by
    nlinarith
  have hLLL := symmetric_local_lemma_cardinality
    (bad := cyclicBadAt b n m hn F) (neighbor := neighbor)
    (p := pbar) (z := 2 * pbar) (d := d)
    hp0 hz0 hz1 hdegree hdep hwindow hcriterion
  rw [mass_univ_cyclicWords] at hLLL
  change ((b : ℝ) * (1 - 2 * pbar)) ^ n ≤
    mass (cyclicAvoiders b n m hn F)
  simpa [cyclicAvoiders, mul_pow, mul_comm] using hLLL

/-- T6-parameter specialization.  The forbidden list has length `k+e` and
cardinality at most `4*b^e`.  The exact single-window counting identity,
dependency factorization, degree bound, and the two numerical smallness
conditions are explicit hypotheses.  The conclusion is precisely the cyclic
exponential estimate; it makes no statement about carries or `Gamma`. -/
theorem t6_cyclic_list_growth
    (b q e k n : ℕ) (hb : 2 ≤ b) (hq : 2 ≤ q) (hqe : q ≤ b ^ e)
    (hk : 2 * e + 12 ≤ k)
    (hn : 0 < n) (F : Finset (Fin (k + e) → Fin b))
    (neighbor : Fin n → Finset (Fin n))
    (hFcard : F.card ≤ 4 * b ^ e)
    (hdegree : ∀ i, (neighbor i).card ≤ 2 * (k + e - 1))
    (hdep : StrongDependency (cyclicBadAt b n (k + e) hn F) neighbor)
    (hwindowExact : ∀ i,
      mass (cyclicBadAt b n (k + e) hn F i) * (b : ℝ) ^ (k + e) =
        F.card * mass (Finset.univ : Finset (Fin n → Fin b)))
    (hquarter : 4 / (b : ℝ) ^ k ≤ 1 / 4)
    (hdependencySmall :
      ((2 * (2 * (k + e - 1)) : ℕ) : ℝ) *
        (4 / (b : ℝ) ^ k) ≤ 1 / 2) :
    ((b : ℝ) * (1 - 8 / (b : ℝ) ^ k)) ^ n ≤
      (cyclicAvoiders b n (k + e) hn F).card := by
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbe : (0 : ℝ) < (b : ℝ) ^ e := pow_pos hbR e
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hbR k
  have hmass0 : 0 ≤ mass (Finset.univ : Finset (Fin n → Fin b)) := by
    unfold mass
    positivity
  have hFcardR : (F.card : ℝ) ≤ 4 * (b : ℝ) ^ e := by
    exact_mod_cast hFcard
  have hwindow : ∀ i,
      mass (cyclicBadAt b n (k + e) hn F i) ≤
        (4 / (b : ℝ) ^ k) *
          mass (Finset.univ : Finset (Fin n → Fin b)) := by
    intro i
    have hexact := hwindowExact i
    rw [pow_add] at hexact
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hbk).2
    have hupper :
        (F.card : ℝ) * mass (Finset.univ : Finset (Fin n → Fin b)) ≤
          (4 * (b : ℝ) ^ e) *
            mass (Finset.univ : Finset (Fin n → Fin b)) :=
      mul_le_mul_of_nonneg_right hFcardR hmass0
    nlinarith
  have hp0 : (0 : ℝ) ≤ 4 / (b : ℝ) ^ k := by positivity
  have hsmall' :
      2 * ((2 * (k + e - 1) : ℕ) : ℝ) * (4 / (b : ℝ) ^ k) ≤ 1 / 2 := by
    norm_num [Nat.cast_mul] at hdependencySmall ⊢
    exact hdependencySmall
  have hmain := cyclic_sparse_forbidden_count b n (k + e)
    (2 * (k + e - 1)) (by omega) hn F neighbor (4 / (b : ℝ) ^ k)
    hp0 hquarter hdegree hdep hwindow hsmall'
  convert hmain using 1 <;> ring

/-- A direct cyclic-to-entropy interface.  No existence of a canonical entropy
limit is assumed: convergence of the displayed normalized log counts is an
explicit premise. -/
theorem entropy_limit_lower_of_eventual_term_bound
    (count : ℕ → ℕ) (h c : ℝ)
    (hlimit : Tendsto (fun n ↦ Real.log (count n) / (n : ℝ)) atTop (nhds h))
    (hlower : ∀ᶠ n in atTop, c ≤ Real.log (count n) / (n : ℝ)) :
    c ≤ h := by
  exact ge_of_tendsto hlimit hlower

/-- Exponential lower counts imply the corresponding entropy lower bound
whenever the normalized logarithmic counts converge.  Convergence remains an
explicit premise rather than an assertion about canonical subshift entropy. -/
theorem entropy_limit_lower_of_eventual_exponential_count
    (count : ℕ → ℕ) (a h : ℝ) (ha : 0 < a)
    (hlimit : Tendsto (fun n ↦ Real.log (count n) / (n : ℝ)) atTop (nhds h))
    (hgrowth : ∀ᶠ n in atTop, a ^ n ≤ (count n : ℝ)) :
    Real.log a ≤ h := by
  apply entropy_limit_lower_of_eventual_term_bound count h (Real.log a) hlimit
  filter_upwards [hgrowth, eventually_gt_atTop 0] with n hnGrowth hn
  have hcount : 0 < (count n : ℝ) :=
    (pow_pos ha n).trans_le hnGrowth
  have hlog : Real.log (a ^ n) ≤ Real.log (count n) :=
    Real.strictMonoOn_log.monotoneOn (pow_pos ha n) hcount hnGrowth
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (by exact_mod_cast hn)).2
  simpa [mul_comm] using hlog

end CyclicWords

#print axioms Theory.Shared.DigitAutomata.T9.finite_local_lemma_cardinality
#print axioms Theory.Shared.DigitAutomata.T9.symmetric_local_lemma_cardinality
#print axioms Theory.Shared.DigitAutomata.T9.cyclic_sparse_forbidden_count
#print axioms Theory.Shared.DigitAutomata.T9.t6_cyclic_list_growth
#print axioms Theory.Shared.DigitAutomata.T9.entropy_limit_lower_of_eventual_term_bound
#print axioms Theory.Shared.DigitAutomata.T9.entropy_limit_lower_of_eventual_exponential_count

end Theory.Shared.DigitAutomata.T9

