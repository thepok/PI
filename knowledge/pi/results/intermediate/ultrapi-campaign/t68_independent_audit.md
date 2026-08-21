# Independent adversarial audit: T68 Hutton simultaneous primary layers

Audit date: **2026-08-12 UTC**  
Formal module:
[`T68T68HuttonSimultaneousPrimary.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T68T68HuttonSimultaneousPrimary.lean)  
Formalization report:
[`t68_hutton_simultaneous_primary_report.md`](t68_hutton_simultaneous_primary_report.md)  
Proof-sketch source:
[`hutton_primary_phase_attack.md`](hutton_primary_phase_attack.md)  
Independent checks:
[`t68_independent_checks.lean`](t68_independent_checks.lean)

## Verdict

**PASS for T68's exact stated scope.** The two simultaneous reduced-denominator
valuations and their supporting dominant-layer lemmas are `machine-checked`.
The module, aggregate library, direct axiom audit, and full repository gate all
pass. No mathematical or formal defect was found.

The audit found one presentation-only defect: five TeX expressions in the
formalization report were written outside math delimiters. Those delimiters
were corrected. No Lean declaration, theorem statement, or proof changed.

T68 does not formalize the leading-unit congruences, additive-CRT coordinates,
high-prime compression, or stationary-lift obstruction from the larger
proof-sketch note. It proves no decimal-cylinder hit. Canonical V1 remains a
`conjecture`; this audit makes no `candidate resolution` or `verified
resolution` claim.

## Audited artifact hashes

- canonical source:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`;
- formal module:
  `716f6e83f9d340b1ecf03d7f41169950062ac3f1fc32f91a87ef0b0136274380`;
- corrected formalization report:
  `becd410f186dce9fc0bfeaa4b20f40fd139608dd6f15df68efcfd1fd45e5ba7c`;
- proof-sketch source:
  `f8a5757b142cc888ea5db84c4e1955744ac373bd8f3b756a8e4599757f3fb74c`;
- independent Lean checks:
  `872e22dcaa9337310a245d0d58281af03f304de766b5e27773b458fda2b6ce2b`.

The source file is Marcel's immutable local question and contains no external
source URL; neither T68 nor its report invents one.

## Statement correspondence and boundary audit

Lean defines

\[
R_a=3^a7^{a+1},\qquad K_a=\left\lfloor R_a/4\right\rfloor.
\]

The parity calculation is exact:

\[
R_a\equiv(-1)^a(-1)^{a+1}\equiv-1\equiv3\pmod4.
\]

Consequently the theorem `four_mul_primaryIndex_add_three` proves

\[
4K_a+3=R_a,
\]

so the quotient definition agrees with the proof-sketch notation
\((R_a-3)/4\). The final Taylor index is \(2K_a+1\), its odd exponent is
\(4K_a+3=R_a\), and the Hutton prefix contains exactly \(2K_a+2\) terms.

The first allowed parameter is checked independently in Lean:

\[
a=2,\quad R_2=3^2 7^3=3087,\quad K_2=771,
\quad 2K_2+1=1543.
\]

The specialized denominator conclusions are therefore

\[
v_3(\operatorname{den}H_{771})=3089,
\qquad
v_7(\operatorname{den}H_{771})=3090.
\]

All six index/radius identities, both rational valuations, both denominator
valuations, and both boundary score-gap specializations compile in the
independent check file. The hypothesis \(a\ge2\) is retained exactly; the
audit does not silently extend the theorem to \(a=0\) or \(a=1\).

## Independent mathematical rederivation

For the generic dominant-layer lemma, put \(t=v_p(r)\) and \(d=R-r\).
Because \(R\) and \(r\) are odd, \(d\ge2\) is even.

- If \(t=0\), parity directly gives \(d\ge t+2\).
- If \(0<t<u=v_p(R)\), then \(p^t\mid R\) and \(p^t\mid r\), hence
  \(p^t\mid d\). Since \(p\ge3\), \(d\ge p^t\ge t+2\).
- If \(t\ge u\), then \(p^u\mid d\). Moreover
  \(t\le\lfloor\log_pR\rfloor\le p^u-2\), so again
  \(d\ge p^u\ge t+2\).

Thus \(r+v_p(r)\le R-2\). At the selected radius, Lean proves

\[
v_3(R_a)=a,\qquad v_7(R_a)=a+1,
\]

and the sufficient logarithmic bounds

\[
\lfloor\log_3R_a\rfloor\le3^a-2,
\qquad
\lfloor\log_7R_a\rfloor\le7^{a+1}-2
\]

uniformly for \(a\ge2\). The three-bound is tight in the auxiliary linear
estimate at \(a=2\), which is why the boundary case deserved an explicit
replay.

At the prime 3, a base-3 Hutton term at odd exponent \(r\) has valuation
\(-r-v_3(r)\), while a base-7 term has valuation only \(-v_3(r)\). Every
earlier base-3 term and every cross-base term therefore lies at least at
\(-(R_a-2)\), whereas the final base-3 term has valuation
\(-(R_a+a)\). The latter is a strict, unique minimum. The ultrametric sum
lemmas preserve that minimum, giving

\[
v_3(H_{K_a})=-(R_a+a).
\]

The symmetric argument at 7 gives

\[
v_7(H_{K_a})=-(R_a+a+1).
\]

Finally, the rational-denominator transfer is sound: because
\(H_{K_a}>0\), its numerator is nonzero; reducedness prevents a prime from
dividing both numerator and denominator; and a negative exact rational
valuation forces the numerator valuation to be zero and the denominator
valuation to be its negation. This yields exactly the two statements in the
proof-sketch equation (2), simultaneously for every \(a\ge2\).

## Declaration, registration, and trust audit

The module contains **42** `lemma`/`theorem` declarations. Extracting the
declaration names and comparing them with fully qualified `#print axioms`
entries found **42 unique registrations**, each occurring exactly once and
with no missing or extra T68 name. `TheoryLib.lean` imports the T68 module.

The module contains no `sorry`, `admit`, new axiom, `native_decide`, unsafe
declaration, opaque proof declaration, or compiler-trusting shortcut. Direct
`#print axioms` output for all T68 propositions contains only the repository
allowlist:

\[
\texttt{propext},\qquad \texttt{Classical.choice},\qquad
\texttt{Quot.sound}.
\]

## Verification replay

The following all passed on 2026-08-12 UTC:

1. `lake env lean TheoryLib/PiQuantitativeBlockHitting/T68T68HuttonSimultaneousPrimary.lean`;
2. `lake env lean work/ultrapi-resume/t68_independent_checks.lean`;
3. `lake build TheoryLib.PiQuantitativeBlockHitting.T68T68HuttonSimultaneousPrimary`;
4. `lake env lean TheoryLib.lean`;
5. `lake env lean audit/AxiomAudit.lean`;
6. `pwsh -File scripts/check.ps1`.

The final gate reported: `PASS: kernel build, exploit scan, and
exact-allowlist axiom audit succeeded.` Existing repository linter warnings
were nonfatal and unrelated to T68.

The correct terminal status is therefore: T68's simultaneous primary
valuation package is `machine-checked`; the unformalized extensions in the
larger note remain `proof sketch`; V1 remains a `conjecture`.
