# Proof trust boundary

A successful build is necessary but not sufficient for a claimed resolution.

## Logical trust policy

Every theorem supporting a research claim must appear in `audit/AxiomAudit.lean`.
The verification gate runs Lean's `#print axioms` and accepts exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

These are the standard axioms used by ordinary mathlib mathematics. Any other
dependency fails the gate. The verified source tree also rejects placeholders,
custom axiom-like declarations, unsafe declarations, and compiler-trusting
shortcuts such as `native_decide`.

Run the adversarial regression suite with:

```powershell
powershell -ExecutionPolicy Bypass -File .\workflows\verification\test-verification-gate.ps1
```

It deliberately constructs a fake theorem from a custom axiom and a theorem
using `native_decide`; both must be rejected before the positive control passes.

## Remaining non-logical risks

Kernel checking cannot detect a mistranscribed, weakened, vacuous, or irrelevant
statement. Each target therefore also requires:

- a source quotation and a separate normalized statement;
- explicit domains and quantifiers;
- a non-vacuity witness and a typechecked negation where meaningful;
- human back-translation from Lean to ordinary mathematics;
- independent comparison with the original source;
- a dated literature and novelty review.

Changes to `workflows/verification/check.ps1`,
`workflows/verification/test-verification-gate.ps1`,
`audit/AxiomAudit.lean`, or this trust policy change the verifier itself and must
be reviewed separately from any proposed mathematical solution.
