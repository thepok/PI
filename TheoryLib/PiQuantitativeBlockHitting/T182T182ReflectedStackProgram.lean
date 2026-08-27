import TheoryLib.PiQuantitativeBlockHitting.T181T181ReflectedIntervalArithmetic

/-!
# T182: a reflected stack program for interval certificates

This is the generic orchestration layer for a later finite root-score
certificate.  Transcendental and rational constants are supplied as a table
of already justified common-scale leaves.  A compact reverse-Polish program
then combines them using T181's checked arithmetic.  Every instruction stores
an untrusted proposed output interval; the evaluator accepts it only when the
corresponding integer checker succeeds.

One induction over the instruction list proves the whole reflected program
sound.  Consequently a generated score payload does not require one theorem
invocation per trigonometric leaf or arithmetic node.
-/

namespace Theory.PiDigits.T182ReflectedStackProgram

open Theory.PiDigits.T171CompactFixedPointCertificate
open Theory.PiDigits.T181ReflectedIntervalArithmetic

noncomputable section

/-- Reverse-Polish interval bytecode.  For binary operations the top stack
entry is the right operand and the next entry is the left operand. -/
inductive Instruction where
  | load (leaf : Nat)
  | add (out : FixedInterval)
  | sub (out : FixedInterval)
  | mul (out : FixedInterval)
  | square (out : FixedInterval)
  | div (out : FixedInterval)
deriving DecidableEq, Repr

/-- One reflected step.  Failure records a bad leaf reference, stack shape,
or arithmetic certificate. -/
def step (scale : Nat) (leaves stack : List FixedInterval) :
    Instruction → Option (List FixedInterval)
  | .load i => leaves[i]?.map fun row => row :: stack
  | .add out => match stack with
      | right :: left :: rest =>
          if checkAdd left right out then some (out :: rest) else none
      | _ => none
  | .sub out => match stack with
      | right :: left :: rest =>
          if checkSub left right out then some (out :: rest) else none
      | _ => none
  | .mul out => match stack with
      | right :: left :: rest =>
          if checkMul scale left right out then some (out :: rest) else none
      | _ => none
  | .square out => match stack with
      | x :: rest =>
          if checkSquare scale x out then some (out :: rest) else none
      | _ => none
  | .div out => match stack with
      | denominator :: numerator :: rest =>
          if checkDiv scale numerator denominator out then some (out :: rest) else none
      | _ => none

/-- Exact real semantics of the same bytecode. -/
def exactStep (leaves stack : List Real) :
    Instruction → Option (List Real)
  | .load i => leaves[i]?.map fun x => x :: stack
  | .add _ => match stack with
      | right :: left :: rest => some ((left + right) :: rest)
      | _ => none
  | .sub _ => match stack with
      | right :: left :: rest => some ((left - right) :: rest)
      | _ => none
  | .mul _ => match stack with
      | right :: left :: rest => some ((left * right) :: rest)
      | _ => none
  | .square _ => match stack with
      | x :: rest => some ((x ^ 2) :: rest)
      | _ => none
  | .div _ => match stack with
      | denominator :: numerator :: rest => some ((numerator / denominator) :: rest)
      | _ => none

def run (scale : Nat) (leaves : List FixedInterval) :
    List FixedInterval → List Instruction → Option (List FixedInterval)
  | stack, [] => some stack
  | stack, op :: ops => (step scale leaves stack op).bind fun next =>
      run scale leaves next ops

def exactRun (leaves : List Real) :
    List Real → List Instruction → Option (List Real)
  | stack, [] => some stack
  | stack, op :: ops => (exactStep leaves stack op).bind fun next =>
      exactRun leaves next ops

/-- Pointwise semantic relation between a reflected and an exact stack. -/
def StackRel (scale : Nat) : List FixedInterval → List Real → Prop :=
  List.Forall₂ (EnclosesReal scale)

private theorem get?_related {scale : Nat} {rows : List FixedInterval}
    {xs : List Real} (h : StackRel scale rows xs) {i : Nat} {row : FixedInterval}
    (hi : rows[i]? = some row) :
    ∃ x, xs[i]? = some x ∧ EnclosesReal scale row x := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons row₀ x₀ rows xs hhead htail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst row₀
          exact ⟨x₀, by simp, hhead⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          exact ih hi

/-- Soundness of one accepted bytecode step. -/
theorem step_sound {scale : Nat} (hscale : 0 < scale)
    {leafRows : List FixedInterval} {leafValues : List Real}
    (hleaves : StackRel scale leafRows leafValues)
    {stackRows : List FixedInterval} {stackValues : List Real}
    (hstack : StackRel scale stackRows stackValues)
    {op : Instruction} {nextRows : List FixedInterval}
    (hstep : step scale leafRows stackRows op = some nextRows) :
    ∃ nextValues, exactStep leafValues stackValues op = some nextValues ∧
      StackRel scale nextRows nextValues := by
  cases op with
  | load i =>
      simp only [step, Option.map_eq_some_iff] at hstep
      obtain ⟨row, hrow, rfl⟩ := hstep
      obtain ⟨x, hx, hsound⟩ := get?_related hleaves hrow
      refine ⟨x :: stackValues, ?_, .cons hsound hstack⟩
      simp [exactStep, hx]
  | add out =>
      cases hstack with
      | nil => simp [step] at hstep
      | @cons rightR rightV tailR tailV hright htail =>
          cases htail with
          | nil => simp [step] at hstep
          | @cons leftR leftV restR restV hleft hrest =>
              simp only [step] at hstep
              split at hstep
              next hop =>
                simp only [Option.some.injEq] at hstep
                subst nextRows
                refine ⟨(leftV + rightV) :: restV, by simp [exactStep], ?_⟩
                exact .cons (checkAdd_sound hleft hright (by simpa using hop)) hrest
              next => simp at hstep
  | sub out =>
      cases hstack with
      | nil => simp [step] at hstep
      | @cons rightR rightV tailR tailV hright htail =>
          cases htail with
          | nil => simp [step] at hstep
          | @cons leftR leftV restR restV hleft hrest =>
              simp only [step] at hstep
              split at hstep
              next hop =>
                simp only [Option.some.injEq] at hstep
                subst nextRows
                refine ⟨(leftV - rightV) :: restV, by simp [exactStep], ?_⟩
                exact .cons (checkSub_sound hleft hright (by simpa using hop)) hrest
              next => simp at hstep
  | mul out =>
      cases hstack with
      | nil => simp [step] at hstep
      | @cons rightR rightV tailR tailV hright htail =>
          cases htail with
          | nil => simp [step] at hstep
          | @cons leftR leftV restR restV hleft hrest =>
              simp only [step] at hstep
              split at hstep
              next hop =>
                simp only [Option.some.injEq] at hstep
                subst nextRows
                refine ⟨(leftV * rightV) :: restV, by simp [exactStep], ?_⟩
                exact .cons (checkMul_sound hscale hleft hright (by simpa using hop)) hrest
              next => simp at hstep
  | square out =>
      cases hstack with
      | nil => simp [step] at hstep
      | @cons xR xV restR restV hx hrest =>
          simp only [step] at hstep
          split at hstep
          next hop =>
            simp only [Option.some.injEq] at hstep
            subst nextRows
            refine ⟨(xV ^ 2) :: restV, by simp [exactStep], ?_⟩
            exact .cons (checkSquare_sound hscale hx (by simpa using hop)) hrest
          next => simp at hstep
  | div out =>
      cases hstack with
      | nil => simp [step] at hstep
      | @cons denR denV tailR tailV hden htail =>
          cases htail with
          | nil => simp [step] at hstep
          | @cons numR numV restR restV hnum hrest =>
              simp only [step] at hstep
              split at hstep
              next hop =>
                simp only [Option.some.injEq] at hstep
                subst nextRows
                refine ⟨(numV / denV) :: restV, by simp [exactStep], ?_⟩
                exact .cons (checkDiv_sound hscale hnum hden (by simpa using hop)) hrest
              next => simp at hstep

/-- One semantic induction validates an arbitrary accepted program. -/
theorem run_sound {scale : Nat} (hscale : 0 < scale)
    {leafRows : List FixedInterval} {leafValues : List Real}
    (hleaves : StackRel scale leafRows leafValues)
    {stackRows : List FixedInterval} {stackValues : List Real}
    (hstack : StackRel scale stackRows stackValues)
    {ops : List Instruction} {finalRows : List FixedInterval}
    (hrun : run scale leafRows stackRows ops = some finalRows) :
    ∃ finalValues, exactRun leafValues stackValues ops = some finalValues ∧
      StackRel scale finalRows finalValues := by
  induction ops generalizing stackRows stackValues with
  | nil =>
      simp only [run, Option.some.injEq] at hrun
      subst finalRows
      exact ⟨stackValues, by simp [exactRun], hstack⟩
  | cons op ops ih =>
      simp only [run] at hrun
      cases hnext : step scale leafRows stackRows op with
      | none => simp [hnext] at hrun
      | some nextRows =>
          simp only [hnext, Option.bind_some] at hrun
          obtain ⟨nextValues, hexactStep, hnextRel⟩ :=
            step_sound hscale hleaves hstack hnext
          obtain ⟨finalValues, hexactRun, hfinalRel⟩ :=
            ih hnextRel hrun
          refine ⟨finalValues, ?_, hfinalRel⟩
          simp [exactRun, hexactStep, hexactRun]

/-- Compact top-level certificate. -/
structure ProgramCertificate where
  scale : Nat
  leaves : List FixedInterval
  code : List Instruction
  claimed : FixedInterval
deriving DecidableEq, Repr

def checkProgram (c : ProgramCertificate) : Bool :=
  decide (0 < c.scale) &&
    match run c.scale c.leaves [] c.code with
    | some [row] => row == c.claimed
    | _ => false

/-- A successful reflected check plus semantic leaf enclosures yields an
exact real result enclosed by the claimed output row. -/
theorem checkedProgram_sound {c : ProgramCertificate}
    {leafValues : List Real} (hleaves : StackRel c.scale c.leaves leafValues)
    (hc : checkProgram c = true) :
    ∃ value, exactRun leafValues [] c.code = some [value] ∧
      EnclosesReal c.scale c.claimed value := by
  simp only [checkProgram, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨hscale, hcheck⟩
  cases heq : run c.scale c.leaves [] c.code with
  | none => simp [heq] at hcheck
  | some rows =>
      cases rows with
      | nil => simp [heq] at hcheck
      | cons row rest =>
          cases rest with
          | nil =>
              simp only [heq, beq_iff_eq] at hcheck
              subst row
              obtain ⟨values, hexact, hrel⟩ :=
                run_sound hscale hleaves (.nil) heq
              cases hrel with
              | cons hvalue htail =>
                  cases htail
                  exact ⟨_, hexact, hvalue⟩
          | cons row₂ rest => simp [heq] at hcheck

/-! A tiny nontrivial executable program certifies
`((-1 + 1/2)^2) / (1/2) ∈ [0.4,0.6]` at scale ten. -/

private def demo : ProgramCertificate where
  scale := 10
  leaves := [⟨-10, -10⟩, ⟨5, 5⟩]
  code := [
    .load 0,
    .load 1,
    .add ⟨-5, -5⟩,
    .square ⟨2, 3⟩,
    .load 1,
    .div ⟨4, 6⟩]
  claimed := ⟨4, 6⟩

private theorem demo_checks : checkProgram demo = true := by rfl

theorem demo_encloses_half : EnclosesReal demo.scale demo.claimed (1 / 2 : Real) := by
  have hleaves : StackRel demo.scale demo.leaves [(-1 : Real), (1 / 2 : Real)] := by
    constructor
    · norm_num [EnclosesReal, demo]
    constructor
    · norm_num [EnclosesReal, demo]
    · exact .nil
  obtain ⟨value, hexact, hvalue⟩ := checkedProgram_sound hleaves demo_checks
  have hvalueEq := Option.some.inj hexact.symm
  norm_num [demo, exactRun, exactStep] at hvalueEq
  simpa [hvalueEq] using hvalue

end

end Theory.PiDigits.T182ReflectedStackProgram

#print axioms Theory.PiDigits.T182ReflectedStackProgram.step_sound
#print axioms Theory.PiDigits.T182ReflectedStackProgram.run_sound
#print axioms Theory.PiDigits.T182ReflectedStackProgram.checkedProgram_sound
#print axioms Theory.PiDigits.T182ReflectedStackProgram.demo_encloses_half
