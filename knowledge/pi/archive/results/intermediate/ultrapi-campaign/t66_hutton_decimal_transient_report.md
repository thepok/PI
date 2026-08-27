# T66 exact Hutton decimal transient

Date: **2026-08-12 UTC**

Status: `machine-checked`.  Focused Lean compilation, independent adversarial
review, and the integrated repository gate all pass.  This is a support
theorem, not V1.

## Source and statement

The normalized source is
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt), SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It is a local question with no supplied external source URL; none is invented.

Let (H_K) be the lower Hutton rational shadow and put (R=4K+3).  T63
already proves, whenever

\[
  5^e\le R<5^{e+1},
\]

that the reduced denominator of (H_K) has five-adic exponent exactly (e).
T66 proves

\[
 v_2(\operatorname{den}H_K)=0
 \quad\text{and hence}\quad
 \max\{v_2(\operatorname{den}H_K),v_5(\operatorname{den}H_K)\}=e.
\]

The maximum is precisely the denominator exponent governing the finite
base-ten preperiod of a reduced rational.  Thus T63's (e) is the entire
base-ten denominator transient, not merely its five-primary component.  The
displayed maximum formula is formalized here; its identification with the
minimal eventual-period start is the standard reduced-denominator argument
for rational base-ten expansions and is not a separate T66 declaration.

## Proof mechanism

Pair the base-three and base-seven terms with common odd exponent
(r=2k+1):

\[
 U_k={4(-1)^k(2\,7^r+3^r)\over r3^r7^r}.
\]

The factor (2\,7^r+3^r) is odd, and every factor below the displayed
coefficient four is odd.  T66 therefore proves (v_2(U_k)=2) exactly.
The Hutton shadow is the nonzero finite sum of these pairs.  The
nonarchimedean inequality gives (v_2(H_K)\ge2), and positivity excludes the
zero-sum branch.  Positive two-adic valuation of a reduced rational forces
its denominator to be odd.  Combining this with T63 yields the maximum
formula above.

The proof deliberately claims only the lower bound on (v_2(H_K)); extra
two-adic cancellation in the reduced numerator is irrelevant to denominator
oddness.

## Trust surface and scope

The formal module is
[`T66T66HuttonDecimalTransient.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T66T66HuttonDecimalTransient.lean).
It contains seven declarations, all imported by `TheoryLib.lean` and
registered in `audit/AxiomAudit.lean`.  Direct `#print axioms` reports only

```text
propext
Classical.choice
Quot.sound
```

and a focused scan finds no `sorry`, `admit`, `native_decide`, new axiom,
unsafe declaration, or opaque proof shortcut.

The independent review and concrete checks are recorded in
[`t66_independent_audit.md`](t66_independent_audit.md) and
[`t66_independent_checks.lean`](t66_independent_checks.lean).  The full
`pwsh -File scripts/check.ps1` gate ended with
`PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.`

T66 removes an ambiguity in the shifted Hutton CRT formulas.  It supplies no
selected-numerator estimate, decimal-cylinder hit, distribution theorem, or
proof that every word occurs in pi.  V1 remains a `conjecture`.
