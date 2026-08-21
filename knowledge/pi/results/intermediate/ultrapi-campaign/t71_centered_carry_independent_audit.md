# T71 centered-carry recurrence: independent adversarial audit

Audit date: **2026-08-13 UTC**.

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is the exact local, human-authored source; it has no external source URL.

Audited module:
[T71T71CenteredCarryRecurrence.lean](../../TheoryLib/PiQuantitativeBlockHitting/T71T71CenteredCarryRecurrence.lean),
SHA-256
`566ba24822d98366faaa7208b3b655cea5b6157522ee54ed02cea9073b2443e7`.

Compared primary artifacts:

- [bbp_centered_carry_recurrence_20260813.md](bbp_centered_carry_recurrence_20260813.md),
  SHA-256
  `3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6`;
- [bbp_centered_carry_recurrence_20260813_check.py](bbp_centered_carry_recurrence_20260813_check.py),
  SHA-256
  `b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff`.

Independent artifacts:

- [t71_centered_carry_independent_checks.lean](t71_centered_carry_independent_checks.lean),
  SHA-256
  `6ca67044ab3ae702e9fd3c7fe829246dcb33d837c1d97fe9d6a7186e8017a130`;
- [t71_centered_carry_independent_check.py](t71_centered_carry_independent_check.py),
  SHA-256
  `ee87f7bbd75d7c9afb61fcc684951435352e3117b68bb7eaad5d967620892c7d`.

## Verdict

**PASS — `machine-checked` generic integer algebra.**

All four theorem interfaces, the changing-denominator orientation, the sign
of the carry correction, and both half-open boundaries agree with the
intended one-step recurrence in the primary report and exact Python replay.
Every theorem is registered exactly once in `audit/AxiomAudit.lean`, and the
full verification gate passed.

This result proves no positive density of nonzero carries, no sublinear or
bounded zero-carry gap, and no occurrence of any decimal word in pi. It does
not prove canonical V1; V1 remains a `conjecture`.

## Semantic audit

### 1. Centered representation and uniqueness

`CenteredRepresentation D U z S` says exactly

\[
  D>0,\qquad U=Dz+S,\qquad -D\leq 2S<D.
\]

Thus $S/D\in[-1/2,1/2)$. This is the residue obtained from
$z=\lfloor U/D+1/2\rfloor$: a tie at the lower endpoint is admitted, while
a candidate at the upper endpoint is rejected and advances the quotient.
The independent Lean file checks the concrete boundary rows

\[
(D,U,z,S)=(10,-5,0,-5),\quad(10,5,1,-5),
\]

and rejects ((10,5,0,5)). The independent integer replay checks 1,212
small signed numerators and finds exactly one centered quotient in every row.

The uniqueness proof has the correct strict bounds. Two representations give

\[
 D(z-z')=S'-S,
\]

while the half-open hypotheses imply (-D<S'-S<D). A nonzero integral
(z-z') would force the left side outside that interval. No unmentioned
rounding convention is imported from mathlib.

### 2. One-step recurrence orientation

The theorem `centeredNumerator_step` assumes

\[
D'=\mathit{scale}\,D,\qquad
U'=\mathit{base}\,\mathit{scale}\,U+\mathit{forcing},
\qquad
\mathit{carry}=z'-\mathit{base}\,z
\]

and concludes

\[
S'=\mathit{base}\,\mathit{scale}\,S+\mathit{forcing}
   -\mathit{carry}\,D'.
\]

With `base = 10`, `scale = Λ_n`, and `forcing = J_{n,P}`, this is exactly
equations (1)--(2) of the primary report. In particular, the denominator on
the correction term is the **new** denominator (D_{n+1}), and the sign is
negative. `advancedQuotient_representation` independently pins the same
orientation before centering:

\[
U'=D'(\mathit{base}\,z)
 +\bigl(\mathit{base}\,\mathit{scale}\,S+\mathit{forcing}\bigr).
\]

The independent Python audit exhaustively checks 35,700 small recurrences,
including negative and zero bases, positive changing scales, signed
numerators, and signed forcing terms. The separately frozen primary checker
also replays 3,000 exact BBP one-step rows and returned `PASS`.

### 3. Exact zero-carry criterion and half-open boundary

Given centered current and next states, the theorem proves

\[
\mathit{carry}=0
\iff
-D'\leq
2(\mathit{base}\,\mathit{scale}\,S+\mathit{forcing})<D'.
\]

The implication from left to right substitutes $z'=\mathit{base}\,z$ and
identifies the next centered residue with the uncorrected numerator. For the
reverse implication, that numerator forms a second valid centered
representation at quotient $\mathit{base}\,z$; uniqueness forces it to
equal $z'$. Both `CenteredRepresentation` hypotheses remain explicit.

The lower comparison is correctly non-strict and the upper comparison is
correctly strict. Independent Lean instantiations verify zero carry at
uncorrected remainder $-D'/2$ and carry one at $+D'/2$. This matches
equation (14) of the primary report and the primary checker's `nearest`
definition, including negative inputs.

### 4. Exact scope of the formalization

T71 is deliberately generic. It does not define the BBP coefficients,
(L_m,A_m,R_n,H_n), or the rational approximants; prove their analytic sum
is pi; establish the hypotheses of the recurrence for those objects in Lean;
formalize the multi-step criterion; or prove that nonzero carries have
positive lower density. The formal result is therefore the reusable algebraic
step **conditional on its displayed integer identities**, not a formalized
fixed-pi density theorem.

There is one documentation lag in the frozen primary report: Section 8 says
that no Lean declaration was added and that nothing there is
`machine-checked`. That statement accurately described the primary report
before T71 was added, but is stale for the repository state audited here.
Only these four generic algebra theorems may now be labeled
`machine-checked`; the report's BBP valuation, analytic, density, and V1
claims retain their original weaker labels.

## Kernel, trust, and registration checks

The independent Lean file restates all four exact theorem types and separately
checks the two tie boundaries. The deterministic checker:

- pins the canonical source, primary report/checker, T71 module, independent
  Lean checks, and the complete axiom audit;
- rejects `sorry`, `admit`, `native_decide`, `sorryAx`, new `axiom`, `opaque`,
  `constant`, or `unsafe` declarations and compiler-trusting shortcuts;
- confirms that T71 declares exactly the four audited theorems;
- confirms exactly one full-name registration for each theorem in
  `audit/AxiomAudit.lean`;
- compiles T71, the independent type/boundary checks, and the full axiom
  audit;
- reruns the frozen primary integer checker; and
- performs the independent 36,912-row small-integer replay described above.

The following commands succeeded:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T71T71CenteredCarryRecurrence.lean
lake env lean work/ultrapi-resume/t71_centered_carry_independent_checks.lean
lake env lean audit/AxiomAudit.lean
.venv/bin/python work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py
.venv/bin/python work/ultrapi-resume/t71_centered_carry_independent_check.py
pwsh -File scripts/check.ps1
```

The full gate ended with:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

At audit time, [AxiomAudit.lean](../../audit/AxiomAudit.lean) had SHA-256
`0bb45a8f484d7ef47e40e3fce362df15fae7532395a06bec4af09daf47cbf77b`.
The four theorem dependency sets are subsets of the existing exact allowlist:

```text
propext
Classical.choice
Quot.sound
```

No forbidden proof mechanism occurs in the audited module.

## Claim boundary

The correct result is a `machine-checked` algebraic normalization of the
one-step centered-carry recurrence. It makes the remaining obstruction more
inspectable, but it supplies no frequency estimate for the actual pi carry
stream. In particular, neither this module nor the primary replay establishes
positive carry density or canonical V1. No complete proof of the every-word
statement has been obtained here.
