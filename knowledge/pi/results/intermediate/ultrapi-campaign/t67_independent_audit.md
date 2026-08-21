# T67 independent audit: two-primary wall for the `1/2 + 1/3` shadow

Audit date: **2026-08-12 UTC**

Verdict: **PASS** for the stated `machine-checked` bracket, valuation,
denominator, and post-transient-width claims. This audit finds no proof of a
decimal-cylinder hit and makes no V1 claim. The canonical every-finite-word
statement remains a `conjecture`.

## Scope and provenance

Audited artifacts:

- `TheoryLib/PiQuantitativeBlockHitting/T67T67TwoThreeArctanShadow.lean`
- the T67 import in `TheoryLib.lean`
- all T67 registrations in `audit/AxiomAudit.lean`
- `work/ultrapi-resume/t67_independent_checks.lean`
- `work/ultrapi-resume/t67_two_three_arctan_shadow_report.md`

The formal module preserves the immutable local source
`problems/local/pi-digits.txt` and its SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
That source has no external URL, and the report does not invent one.

## Independent mathematical re-derivation

Write

\[
 t_{q,j}=\frac{(-1)^j}{(2j+1)q^{2j+1}},\qquad
 N=2(K+1),\qquad E_K=4\sum_{j<N}(t_{2,j}+t_{3,j}).
\]

1. **Pair decomposition.** Expanding the two finite sums and distributing the
   coefficient four gives exactly the sum of `twoThreePairRat j` over
   `j < N`. The two closed-fraction lemmas are direct rewrites of the
   definition of `arctanTermRat`.

2. **Individual two-adic valuations.** Since `2*j+1` is odd,

   \[
   v_2(4t_{2,j})=2-(2j+1)=1-2j,
   \qquad v_2(4t_{3,j})=2.
   \]

   The first valuation is always strictly smaller than the second. Therefore
   the two terms cannot cancel, and the ultrametric equality for unequal
   valuations gives

   \[
   v_2\bigl(4t_{2,j}+4t_{3,j}\bigr)=1-2j.
   \]

3. **Full lower-shadow two-adic law.** These pair valuations strictly decrease
   by two with `j`. Induction on a nonempty prefix therefore leaves its final
   pair as the unique valuation minimum. The last index in the `N`-term
   prefix is `2K+1`, hence

   \[
   v_2(E_K)=1-2(2K+1)=-(4K+1).
   \]

   This also proves `E_K` is nonzero. Because Lean rationals are reduced, a
   negative valuation of that exact size forces
   `v_2(E_K.den)=4*K+1`; the numerator cannot contain a factor two
   simultaneously with the reduced denominator.

4. **Five-adic denominator bound.** Both individual terms have valuation

   \[
   v_5(4t_{q,j})=-v_5(2j+1),\qquad q\in\{2,3\}.
   \]

   Thus each pair has valuation at least this common lower bound. For
   `j < 2(K+1)`, the module proves
   `v_5(2*j+1) <= 4*K+1`, including a separate `K=0` branch. The finite-sum
   ultrametric inequality and the already-proved nonzeroness of `E_K` give
   `v_5(E_K) >= -(4*K+1)`. Reducedness then yields
   `v_5(E_K.den) <= 4*K+1`. Combining this with the exact two-adic exponent
   proves

   \[
   \max(v_2(E_K.den),v_5(E_K.den))=4K+1.
   \]

   This is exactly the standard denominator exponent governing the minimal
   base-10 preperiod of a reduced rational.

5. **Bracket and exact width.** Mathlib supplies
   `arctan(1/2)+arctan(1/3)=pi/4`. Each truncation uses the even number
   `N=2(K+1)` of alternating-series terms, so their sum is below pi; adjoining
   the next positive term to each gives the upper endpoint. Consequently

   \[
   E_K\le\pi\le U_K,
   \qquad
   U_K-E_K=
   \frac4{(4K+5)2^{4K+5}}+
   \frac4{(4K+5)3^{4K+5}}.
   \]

6. **Post-transient width.** With `e=4*K+1`, the scaled base-two summand alone
   is

   \[
   10^e\frac4{(4K+5)2^{e+4}}
   =\frac{5^{4K+3}}{100(4K+5)}.
   \]

   The inductively proved integer inequality
   `10*(4*K+5) < 5^(4*K+3)` makes this strictly greater than `1/10`.
   The base-three summand is positive, so the full scaled width is also
   strictly greater than `1/10`.

## Boundary and normalization replay

The independent Lean replay now checks, without adding research claims:

- `twoThreeTermCount 0 = 2`;
- the first two pairs are `10/3` and `-35/162`;
- `twoThreeLowerRat 0 = 505/162`, whose reduced denominator has two-adic
  exponent one and five-adic exponent zero;
- `twoThreeUpperRat 0 = 6115/1944`, so the exact `K=0` width is `55/1944`;
- `twoThreeLowerRat 1 = 1538665/489888`, with reduced denominator `489888`
  and exact two-adic exponent five;
- the general pair, prefix, full valuation, five-adic bound, base-10 exponent,
  bracket, and explicit-width theorems;
- at `K=0`, the scaled base-two omitted contribution is exactly `1/4`, hence
  already strictly larger than `1/10`.

This explicitly covers the boundary case rather than relying only on the
universal wrapper theorem.

## Registration, dependency, and exploit audit

- The aggregate `TheoryLib.lean` imports T67 exactly once.
- The formal module contains **29** propositions (`theorem` or `lemma`).
- `audit/AxiomAudit.lean` contains **29 of 29** corresponding T67
  `#print axioms` registrations; no proposition is missing.
- Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for these
  declarations.
- The focused source and replay contain no `sorry`, `admit`, new `axiom`,
  `native_decide`, `unsafe`, or opaque proof shortcut.
- `ultrapi.md` was not edited by this independent audit.

## Verification commands

All commands passed on 2026-08-12 UTC:

```text
lake build TheoryLib.PiQuantitativeBlockHitting.T67T67TwoThreeArctanShadow
lake env lean work/ultrapi-resume/t67_independent_checks.lean
pwsh -File scripts/check.ps1
```

The full gate ended with:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

## Artifact hashes

- formal module:
  `512fdf1c72c8adddb946765b6645c509c867b0245d0c45bd0a20e7c25921556e`
- strengthened independent checks:
  `968729837e1806fca72c43141e6f3ea62bf42e45beb306ee78b8fcad67791153`
- verified report:
  `8558313686225269cb131c3ca8f0cd408593f00736a875c1598ffd1c78c51f09`
- aggregate import file at audit time:
  `14aeacf47604119b7f7c9935e66ccb6fd17c57541610ed5e0757657c72573606`
- axiom registry at audit time:
  `d4909a6a28c6f97af56b6ddf7c588314dd20b2c486942278a76ca36122f3860f`

## Final assessment

T67 correctly closes the complete-period version of this particular
two-arctangent rational-shadow route: by the first position at which the
rational endpoint has entered its denominator-coprime period, its certified
bracket is already wider than a one-digit decimal cylinder. This is a
meaningful `machine-checked` obstruction. It does not control the selected
numerator during the dyadic transient and therefore does not establish V1.
