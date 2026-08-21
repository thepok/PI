import TheoryLib.PiQuantitativeBlockHitting.T33T33RecurrentSharpnessSeparator
import TheoryLib.PiLacunaryNearReturnSparsity.T7FiniteCylinderEnergy

/-!
# T34: recurrent-cell transfer under an eventual two-valued shadow

Source: `problems/local/pi-digits.txt`
SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

This file isolates the finite combinatorial core of the BBP-shadow argument.
Suppose that, after some cutoff, every value of a source stream is one of two
fixed lifts of the simultaneous value of a target stream.  Every recurrent
source value then selects a recurrent target value, and recording which lift
was used embeds recurrent source values into recurrent target values times a
two-element type.  Consequently the target retains at least half as many
recurrent values.

For the intended BBP application, the source values are decimal cell indices
of `{10^N pi}`, the target values are the corresponding cell indices of the
rational BBP truncation, and the two lifts are a cell and its cyclic successor.
The exact BBP truncations and their positive vanishing tail are not presently
formalized in the verified track.  Accordingly this module proves the strongest
clean abstract transfer and does not claim that its eventual-shadow premise has
been discharged for pi.
-/

noncomputable section

namespace Theory.PiDigits.RecurrentCellTransfer

open DecimalFactorComplexity

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- A value is recurrent when it occurs beyond every cutoff. -/
def RecurrentValue (s : Stream α) (a : α) : Prop :=
  ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧ s i = a

/-- The finite type of recurrent values of a stream. -/
abbrev RecurrentValues (s : Stream α) :=
  {a : α // RecurrentValue s a}

/-- The number of values that occur arbitrarily late. -/
def recurrentValueCount (s : Stream α) : ℕ :=
  Nat.card (RecurrentValues s)

omit [DecidableEq α] in
/-- Finiteness gives one cutoff after which every occurring value is
recurrent. -/
lemma exists_recurrentValue_cutoff (s : Stream α) :
    ∃ C : ℕ, ∀ i : ℕ, C ≤ i → RecurrentValue s (s i) := by
  classical
  have hthreshold : ∀ a : α, ∃ N : ℕ,
      ∀ i : ℕ, N ≤ i → s i = a → RecurrentValue s a := by
    intro a
    by_cases ha : RecurrentValue s a
    · exact ⟨0, fun _ _ _ ↦ ha⟩
    · simp only [RecurrentValue, not_forall] at ha
      obtain ⟨N, hN⟩ := ha
      push Not at hN
      exact ⟨N, fun i hi hia ↦ (hN i hi hia).elim⟩
  let cutoff : α → ℕ := fun a ↦ (hthreshold a).choose
  let C : ℕ := Finset.univ.sup cutoff
  refine ⟨C, fun i hi ↦ ?_⟩
  have hcutoff : cutoff (s i) ≤ C :=
    Finset.le_sup (Finset.mem_univ (s i))
  exact (hthreshold (s i)).choose_spec i (hcutoff.trans hi) rfl

/-- Eventually every source value is one of two fixed lifts of the
simultaneous target value. -/
def EventuallyTwoLift
    (source : Stream α) (target : Stream β) (left right : β → α) : Prop :=
  ∃ C : ℕ, ∀ i : ℕ, C ≤ i →
    source i = left (target i) ∨ source i = right (target i)

/-- The one-sided cell-shadow relation needed in the BBP application: after a
cutoff, the source cell is either the target cell or its cyclic successor. -/
def EventuallyCyclicSuccessorShadow {q : ℕ}
    (source target : Stream (Fin q)) : Prop :=
  EventuallyTwoLift source target (fun a ↦ a) (finRotate q)

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- Every recurrent source value has a recurrent target witness under one of
the two lifts. -/
lemma exists_recurrentTarget_of_eventuallyTwoLift
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right)
    (x : RecurrentValues source) :
    ∃ y : RecurrentValues target,
      x.1 = left y.1 ∨ x.1 = right y.1 := by
  obtain ⟨Cshadow, hshadow⟩ := hshadow
  obtain ⟨Ctarget, htarget⟩ := exists_recurrentValue_cutoff target
  obtain ⟨i, hi, hix⟩ := x.2 (max Cshadow Ctarget)
  let y : RecurrentValues target :=
    ⟨target i, htarget i (by omega)⟩
  refine ⟨y, ?_⟩
  rcases hshadow i (by omega) with hleft | hright
  · exact Or.inl (hix ▸ hleft)
  · exact Or.inr (hix ▸ hright)

/-- A chosen recurrent target witness for a recurrent source value. -/
noncomputable def recurrentTarget
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right)
    (x : RecurrentValues source) : RecurrentValues target :=
  (exists_recurrentTarget_of_eventuallyTwoLift
    source target left right hshadow x).choose

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma recurrentTarget_spec
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right)
    (x : RecurrentValues source) :
    x.1 = left (recurrentTarget source target left right hshadow x).1 ∨
      x.1 = right (recurrentTarget source target left right hshadow x).1 :=
  (exists_recurrentTarget_of_eventuallyTwoLift
    source target left right hshadow x).choose_spec

/-- The bit records whether the chosen witness uses the left lift. -/
noncomputable def recurrentBranch
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right)
    (x : RecurrentValues source) : Bool :=
  if x.1 = left (recurrentTarget source target left right hshadow x).1
    then false else true

omit [Fintype α] [DecidableEq β] in
/-- A recurrent source value is recovered from its chosen target and branch. -/
lemma value_eq_left_or_right_of_recurrentBranch
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right)
    (x : RecurrentValues source) :
    if recurrentBranch source target left right hshadow x = false then
      x.1 = left (recurrentTarget source target left right hshadow x).1
    else
      x.1 = right (recurrentTarget source target left right hshadow x).1 := by
  by_cases hleft :
      x.1 = left (recurrentTarget source target left right hshadow x).1
  · simp [recurrentBranch, hleft]
  · have hright := (recurrentTarget_spec
      source target left right hshadow x).resolve_left hleft
    simp [recurrentBranch, hright]

/-- Encode a recurrent source value by one recurrent target value and one
branch bit. -/
noncomputable def recurrentValueEmbedding
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right) :
    RecurrentValues source → RecurrentValues target × Bool :=
  fun x ↦
    (recurrentTarget source target left right hshadow x,
      recurrentBranch source target left right hshadow x)

omit [Fintype α] [DecidableEq β] in
lemma recurrentValueEmbedding_injective
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right) :
    Function.Injective
      (recurrentValueEmbedding source target left right hshadow) := by
  intro x z hxz
  have htarget :
      recurrentTarget source target left right hshadow x =
        recurrentTarget source target left right hshadow z :=
    congrArg Prod.fst hxz
  have hbranch :
      recurrentBranch source target left right hshadow x =
        recurrentBranch source target left right hshadow z :=
    congrArg Prod.snd hxz
  apply Subtype.ext
  by_cases hb : recurrentBranch source target left right hshadow x = false
  · have hbx := value_eq_left_or_right_of_recurrentBranch
      source target left right hshadow x
    have hbz := value_eq_left_or_right_of_recurrentBranch
      source target left right hshadow z
    rw [if_pos hb] at hbx
    have hb' : recurrentBranch source target left right hshadow z = false := by
      rw [← hbranch]
      exact hb
    rw [if_pos hb'] at hbz
    rw [hbx, hbz, htarget]
  · have hbx := value_eq_left_or_right_of_recurrentBranch
      source target left right hshadow x
    have hbz := value_eq_left_or_right_of_recurrentBranch
      source target left right hshadow z
    rw [if_neg hb] at hbx
    have hb' : recurrentBranch source target left right hshadow z ≠ false := by
      rw [← hbranch]
      exact hb
    rw [if_neg hb'] at hbz
    rw [hbx, hbz, htarget]

omit [Fintype α] [DecidableEq β] in
/-- An eventual two-valued shadow loses at most a factor of two in recurrent
value count. -/
theorem recurrentValueCount_le_two_mul_of_eventuallyTwoLift
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right) :
    recurrentValueCount source ≤ 2 * recurrentValueCount target := by
  rw [recurrentValueCount, recurrentValueCount]
  calc
    Nat.card (RecurrentValues source) ≤
        Nat.card (RecurrentValues target × Bool) :=
      Nat.card_le_card_of_injective
        (recurrentValueEmbedding source target left right hshadow)
        (recurrentValueEmbedding_injective source target left right hshadow)
    _ = 2 * Nat.card (RecurrentValues target) := by
      simp [Nat.card_prod, Nat.mul_comm]

omit [Fintype α] [DecidableEq β] in
/-- Equivalent lower-bound form: the target retains the ceiling of half the
source recurrent values. -/
theorem half_recurrentValueCount_le_of_eventuallyTwoLift
    (source : Stream α) (target : Stream β) (left right : β → α)
    (hshadow : EventuallyTwoLift source target left right) :
    (recurrentValueCount source + 1) / 2 ≤ recurrentValueCount target := by
  have h := recurrentValueCount_le_two_mul_of_eventuallyTwoLift
    source target left right hshadow
  omega

/-- A one-sided cyclic cell shift gives an injection from recurrent source
cells into recurrent target cells times a branch bit. -/
theorem recurrentValueCount_le_two_mul_of_eventuallyCyclicSuccessorShadow
    {q : ℕ} (source target : Stream (Fin q))
    (hshadow : EventuallyCyclicSuccessorShadow source target) :
    recurrentValueCount source ≤ 2 * recurrentValueCount target :=
  recurrentValueCount_le_two_mul_of_eventuallyTwoLift
    source target (fun a ↦ a) (finRotate q) hshadow

/-- Ceiling-half form of the one-sided cyclic cell-shadow transfer. -/
theorem half_recurrentValueCount_le_of_eventuallyCyclicSuccessorShadow
    {q : ℕ} (source target : Stream (Fin q))
    (hshadow : EventuallyCyclicSuccessorShadow source target) :
    (recurrentValueCount source + 1) / 2 ≤ recurrentValueCount target :=
  half_recurrentValueCount_le_of_eventuallyTwoLift
    source target (fun a ↦ a) (finRotate q) hshadow

open Theory.PiDigits.RecurrentFactorComplexity
open Theory.PiDigits.FactorComplexity

lemma piDecimalStream_eq_piDigit :
    DecimalFactorComplexity.piDecimalStream = Theory.PiDigits.piDigit := by
  funext n
  exact Theory.PiDigits.T20.decimalDigit_pi n

/-- A chosen occurrence of a recurrent pi factor. -/
noncomputable def piRecurrentFactorStart (n : ℕ)
    (w : RecurrentFactor Theory.PiDigits.piDigit n) : ℕ :=
  (w.2 0).choose

lemma piRecurrentFactorStart_spec (n : ℕ)
    (w : RecurrentFactor Theory.PiDigits.piDigit n) :
    blockAt Theory.PiDigits.piDigit n (piRecurrentFactorStart n w) = w.1 :=
  (w.2 0).choose_spec.2

/-- Encode a recurrent pi factor by the decimal-cylinder label at one chosen
occurrence. -/
noncomputable def piRecurrentFactorCylinderCode (n : ℕ) :
    RecurrentFactor Theory.PiDigits.piDigit n →
      RecurrentValues
        (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n) := by
  intro w
  let start := piRecurrentFactorStart n w
  let code :=
    DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n start
  refine ⟨code, ?_⟩
  intro N
  obtain ⟨i, hi, hiw⟩ := w.2 N
  refine ⟨i, hi, ?_⟩
  apply (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_iff_factorAt_eq
    n i start).2
  rw [piDecimalStream_eq_piDigit]
  apply Subtype.ext
  change blockAt Theory.PiDigits.piDigit n i =
    blockAt Theory.PiDigits.piDigit n start
  exact hiw.trans (piRecurrentFactorStart_spec n w).symm

lemma piRecurrentFactorCylinderCode_injective (n : ℕ) :
    Function.Injective (piRecurrentFactorCylinderCode n) := by
  intro w v hwv
  have hcode := congrArg Subtype.val hwv
  have hfactor :=
    (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode_eq_iff_factorAt_eq n
        (piRecurrentFactorStart n w) (piRecurrentFactorStart n v)).1 hcode
  rw [piDecimalStream_eq_piDigit] at hfactor
  have hblock := congrArg Subtype.val hfactor
  apply Subtype.ext
  exact (piRecurrentFactorStart_spec n w).symm.trans
    (hblock.trans (piRecurrentFactorStart_spec n v))

/-- Pi's recurrent symbolic factors inject into the recurrent values of its
canonical decimal-cylinder code stream. -/
theorem pi_recurrentFactorComplexity_le_recurrentCylinderCount (n : ℕ) :
    recurrentFactorComplexity Theory.PiDigits.piDigit n ≤
      recurrentValueCount
        (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n) := by
  rw [recurrentFactorComplexity, recurrentValueCount]
  exact Nat.card_le_card_of_injective
    (piRecurrentFactorCylinderCode n)
    (piRecurrentFactorCylinderCode_injective n)

omit [DecidableEq β] in
/-- Conditional pi specialization of the abstract transfer.  The explicit
premise is the still-unformalized analytic bridge needed for the rational BBP
cell stream. -/
theorem pi_recurrentFactorComplexity_le_two_mul_shadowCount
    (n : ℕ) (target : Stream β)
    (left right : β → Fin (10 ^ n))
    (hshadow : EventuallyTwoLift
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n)
      target left right) :
    recurrentFactorComplexity Theory.PiDigits.piDigit n ≤
      2 * recurrentValueCount target := by
  exact (pi_recurrentFactorComplexity_le_recurrentCylinderCount n).trans
    (recurrentValueCount_le_two_mul_of_eventuallyTwoLift
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n)
      target left right hshadow)

omit [DecidableEq β] in
/-- Ceiling-half form of the conditional pi transfer. -/
theorem pi_half_recurrentFactorComplexity_le_shadowCount
    (n : ℕ) (target : Stream β)
    (left right : β → Fin (10 ^ n))
    (hshadow : EventuallyTwoLift
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n)
      target left right) :
    (recurrentFactorComplexity Theory.PiDigits.piDigit n + 1) / 2 ≤
      recurrentValueCount target := by
  have h := pi_recurrentFactorComplexity_le_two_mul_shadowCount
    n target left right hshadow
  omega

omit [DecidableEq β] in
/-- Combining T31 with the conditional transfer gives the explicit linear
lower bound intended for the rational BBP cell stream. -/
theorem pi_length_half_le_shadowCount
    (n : ℕ) (hn : 0 < n) (target : Stream β)
    (left right : β → Fin (10 ^ n))
    (hshadow : EventuallyTwoLift
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n)
      target left right) :
    (n + 2) / 2 ≤ recurrentValueCount target := by
  have hhalf := pi_half_recurrentFactorComplexity_le_shadowCount
    n target left right hshadow
  have hlower := pi_recurrentFactorComplexity_lower_bound n hn
  omega

/-- The exact conditional shape intended for a rational BBP cell stream.  No
such stream or proof of `hshadow` is asserted here: this theorem records the
remaining analytic interface without promoting it into the verified track. -/
theorem pi_length_half_le_cyclicShadowCount
    (n : ℕ) (hn : 0 < n) (target : Stream (Fin (10 ^ n)))
    (hshadow : EventuallyCyclicSuccessorShadow
      (DecimalFactorComplexity.FiniteCylinderEnergy.piCylinderCode n)
      target) :
    (n + 2) / 2 ≤ recurrentValueCount target :=
  pi_length_half_le_shadowCount n hn target (fun a ↦ a)
    (finRotate (10 ^ n)) hshadow

end Theory.PiDigits.RecurrentCellTransfer

#print axioms Theory.PiDigits.RecurrentCellTransfer.exists_recurrentValue_cutoff
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.exists_recurrentTarget_of_eventuallyTwoLift
#print axioms Theory.PiDigits.RecurrentCellTransfer.recurrentValueEmbedding_injective
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.recurrentValueCount_le_two_mul_of_eventuallyTwoLift
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.half_recurrentValueCount_le_of_eventuallyTwoLift
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.recurrentValueCount_le_two_mul_of_eventuallyCyclicSuccessorShadow
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.half_recurrentValueCount_le_of_eventuallyCyclicSuccessorShadow
#print axioms Theory.PiDigits.RecurrentCellTransfer.piDecimalStream_eq_piDigit
#print axioms Theory.PiDigits.RecurrentCellTransfer.piRecurrentFactorStart_spec
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.piRecurrentFactorCylinderCode_injective
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.pi_recurrentFactorComplexity_le_recurrentCylinderCount
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.pi_recurrentFactorComplexity_le_two_mul_shadowCount
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.pi_half_recurrentFactorComplexity_le_shadowCount
#print axioms Theory.PiDigits.RecurrentCellTransfer.pi_length_half_le_shadowCount
#print axioms
  Theory.PiDigits.RecurrentCellTransfer.pi_length_half_le_cyclicShadowCount
