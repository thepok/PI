# T68 Hutton simultaneous-primary formalization report

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and exact claim scope

The dominant-layer argument and the simultaneous (3)- and (7)-primary
denominator valuations from
[`hutton_primary_phase_attack.md`](hutton_primary_phase_attack.md) are now
`machine-checked` in
[`T68T68HuttonSimultaneousPrimary.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T68T68HuttonSimultaneousPrimary.lean).

For every natural number \(a\ge2\), Lean defines

\[
 R_a=3^a7^{a+1},\qquad K_a=\lfloor R_a/4\rfloor
\]

and proves \(R_a=4K_a+3\). If \(H_{K_a}\) is the existing exact rational
Hutton lower shadow and `den` denotes its reduced positive denominator, the
main theorem is

\[
 \boxed{
 v_3(\operatorname{den}H_{K_a})=R_a+a,\qquad
 v_7(\operatorname{den}H_{K_a})=R_a+a+1.}
\]

The stronger rational-valued statements are also checked:

\[
 v_3(H_{K_a})=-(R_a+a),\qquad
 v_7(H_{K_a})=-(R_a+a+1).
\]

The proof does not merely replay the sample \(a=2\). It proves a general
odd-prime dominant-layer lemma: under the exact endpoint valuation and the
stated logarithmic bound, every earlier odd exponent \(r<R\) satisfies

\[
 r+v_p(r)\le R-2.
\]

It then proves the logarithmic hypotheses uniformly for \(p=3\) and \(p=7\),
computes all four kinds of Hutton-term valuation, isolates the unique final
minimum in each primary component, controls the remaining finite sums by the
ultrametric inequality, and transfers the negative rational valuations to
the reduced denominator.

## Verification ledger

- Formal artifact SHA-256:
  `716f6e83f9d340b1ecf03d7f41169950062ac3f1fc32f91a87ef0b0136274380`.
- The module contributes **42 proposition declarations**. Every declaration
  is registered exactly once in [`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean).
- [`TheoryLib.lean`](../../TheoryLib.lean) imports T68.
- Focused `lake env lean` compilation passed.
- `lake build TheoryLib.PiQuantitativeBlockHitting.T68T68HuttonSimultaneousPrimary`
  passed.
- `pwsh -File scripts/check.ps1` passed on 2026-08-12 UTC:
  kernel build, forbidden-shortcut scan, and exact-allowlist axiom audit all
  succeeded.
- The only reported axioms are the repository allowlist
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new axiom, `native_decide`, opaque proof declaration,
  unsafe declaration, or compiler-trusting shortcut occurs in T68.

## What was not formalized and what remains open

This module does **not** formalize the growing-precision leading-unit
congruences, the additive-CRT coordinate formulas, the high-prime
subexponential-complement bound, or the stationary-lift separator from the
larger proof-sketch note. Those remain outside T68's exact claim scope.

More importantly, exact large denominator factors do not control the one
actual ordered decimal phase selected by the numerator. T68 proves no
short exponential-sum cancellation, no prescribed decimal-cylinder hit,
and no occurrence of an arbitrary word in pi. The canonical V1 statement
therefore remains a `conjecture`; T68 is not a `candidate resolution` or a
`verified resolution` of V1.
