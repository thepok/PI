# T52 three-primary seed audit

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

The new verified-track module is
[`T52T52MachinSeedThreePrimaryPersistence.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean).
Its SHA-256 is
`5ba17b604338ca283144223c0a284858669cd38b9025413ca674162ec673d4a0`.

The following result is `machine-checked`. For every `j >= 1` and every
natural `a` satisfying

\[
 3^a\le 12j+3<3^{a+1},
\]

T52 proves

\[
 v_3\!\left(10^j M_{3j}\right)=1-a
\]

in the exact rational form
`padicValRat_three_sampledMachinValueRat_at_index`. It also proves that the
reduced denominator has exact multiplicity `a-1` in
`padicValNat_three_sampledMachinValueRat_den_at_index`.

This is a persistent local denominator theorem. It does not determine the
complementary numerator phase and does not prove a decimal cylinder hit,
recurrence, density, normality, or the every-word conjecture. The canonical
target remains a `conjecture`.

## Proof structure checked by Lean

1. `4*239^u-5^u` is congruent to `3*5^u` modulo nine. The latter is nonzero
   modulo nine, while the cancellation factor is zero modulo three. Hence
   its exact three-adic order is one.
2. Every combined common odd-exponent pair has valuation
   `1 - padicValNat 3 u`.
3. If `3^a <= d < 3^(a+1)`, the only odd `u <= d` with exact order `a` is
   `u=3^a`; writing `u=3^a*k` forces the positive odd cofactor `k<3` to be
   one.
4. All other paired terms have valuation at least `2-a`. The extra
   base-239 endpoint has exponent `12*N+17`, hence is a three-adic unit.
5. The unique-minimum valuation law gives the exact seed valuation `1-a`.
   Multiplication by the decimal power is a three-adic unit, and reducedness
   then gives denominator multiplicity `a-1`.

## Mechanical audit

- T52 contains **25** proposition declarations (`theorem` or `lemma`) and
  **2** definitions.
- All **25** proposition names occur exactly once in
  [`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean); a sorted name-set
  comparison had no difference.
- Direct module compilation succeeded.
- Direct compilation of `audit/AxiomAudit.lean` succeeded.
- Every T52 declaration reported only the allowlisted axioms `propext`,
  `Classical.choice`, and `Quot.sound` (some use a strict subset).
- A focused forbidden-construct scan found no `sorry`, `admit`, new `axiom`,
  `native_decide`, `unsafe`, or `opaque` declaration.
- `git diff --check` passed for the module and shared integration files.

The final repository-wide `pwsh -NoProfile -File scripts/check.ps1` replay
also passed after integration. Its terminal verdict was:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```
