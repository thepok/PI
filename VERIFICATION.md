# Pi Lab verification policy

Every formal research claim must pass the same fixed gate.

## Statement integrity

The Lean theorem must match the stated mathematical claim quantifier by quantifier. Explicitly record conditional hypotheses, especially external irrationality or distribution results. Check for vacuity and degenerate cases.

## Kernel verification

- Build against the pinned Lean toolchain and mathlib revision.
- Reject `sorry`, `admit`, `native_decide`, new `axiom` declarations, opaque/constant proof declarations, unsafe declarations, and compiler-trusting shortcuts.
- Run `#print axioms` for every theorem supporting a research claim.
- Accept only `propext`, `Classical.choice`, and `Quot.sound`.
- Register supporting theorems in `audit/AxiomAudit.lean`.

Run:

```bash
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

## Computation and model output

Computed examples are `experiment` only. Search code and model drafts are untrusted until independently replayed and, where applicable, converted into kernel-checked lemmas. A model's self-report is never evidence.

## Literature and external claims

Read primary sources and record exact theorem-to-claim matching. Literature evidence does not become a Lean axiom. No external publication or reviewer contact is authorized without Marcel's explicit approval.

