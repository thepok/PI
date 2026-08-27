# Verified-core index

Last audited: 2026-08-27 UTC

Canonical source: [`TheoryLib/`](../../../TheoryLib/) and
[`TheoryLib.lean`](../../../TheoryLib.lean). The explicit theorem audit is
[`audit/AxiomAudit.lean`](../../../audit/AxiomAudit.lean); the allowlist is
`propext`, `Classical.choice`, and `Quot.sound`.

Current frontier modules are T148, T153, T156, T172, T176–T179, T189, and
T190 in `TheoryLib/PiQuantitativeBlockHitting/`. The latest machine-checked
milestone is T190's complementary-rank same-digit alignment theorem; its
actual-π rank premises are unproved.

See [`../active/VERIFIED_CONSUMER_PATH.md`](../active/VERIFIED_CONSUMER_PATH.md)
for the short path and [`../active/evidence/machine-checked/20260827-complementary-rank-alignment.md`](../active/evidence/machine-checked/20260827-complementary-rank-alignment.md)
for the T190 report.

No theorem in the core proves V1, decimal density, normality, or the required
actual-π signed cancellation.
