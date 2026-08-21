# T67 verified report: the exact transient wall in the `1/2 + 1/3` shadow

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented. This report records a verified-track result supporting the
existing normalized problem record.

## Claim status

The exact rational-bracket and denominator statements below are
`machine-checked`. They do **not** prove a decimal-cylinder hit or the
canonical every-word statement. That target remains a `conjecture`.

## Exact statement formalized

Let

\[
 N=2(K+1),\qquad
 E_K=4\sum_{j<N}{(-1)^j\over(2j+1)2^{2j+1}}
       +4\sum_{j<N}{(-1)^j\over(2j+1)3^{2j+1}}.
\]

Using mathlib's theorem
\(\arctan(1/2)+\arctan(1/3)=\pi/4\), T67 proves:

1. `E_K` is the lower endpoint of an adjacent rational bracket for pi.
2. The exact bracket width is

   \[
   W_K={4\over(4K+5)2^{4K+5}}+
       {4\over(4K+5)3^{4K+5}}.
   \]

3. The combined equal-index pair has exact valuation

   \[
   v_2\!\left(4t_{2,j}+4t_{3,j}\right)=1-2j.
   \]

   These values strictly decrease, so the final pair is the unique minimum
   and

   \[
   v_2(E_K)=-(4K+1),\qquad
   v_2(\operatorname{den}E_K)=4K+1.
   \]

4. A separate five-adic bound proves

   \[
   v_5(\operatorname{den}E_K)\le 4K+1.
   \]

   Hence the exact base-10 preperiod length is `4*K+1`.
5. At the first post-transient position the adjacent bracket is already too
   wide even for a one-digit cylinder:

   \[
   10^{4K+1}W_K>{1\over10}.
   \]

   The proof uses the elementary strict inequality
   \(10(4K+5)<5^{4K+3}\), formalized by induction.

## Why this is meaningful but not V1

Any estimate that begins only after the rational expansion reaches its
coprime periodic part is too late for bracket transfer: at that first
position the uncertainty interval is wider than every nonempty decimal
cylinder. This closes the complete-period version of the `1/2 + 1/3`
rational-shadow strategy. It does not analyze or control the selected
numerator during the dyadic transient, which is precisely the remaining
obstruction identified in the accompanying proof-sketch audit.

## Verified artifacts

- Formal module:
  [`TheoryLib/PiQuantitativeBlockHitting/T67T67TwoThreeArctanShadow.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T67T67TwoThreeArctanShadow.lean)
- Independent replay checks:
  [`t67_independent_checks.lean`](t67_independent_checks.lean)
- Independent audit:
  [`t67_independent_audit.md`](t67_independent_audit.md)
- Aggregate import: [`TheoryLib.lean`](../../TheoryLib.lean)
- Axiom registry: [`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean)

Every proposition in T67 is registered in `audit/AxiomAudit.lean`. The
allowed dependencies printed by Lean are only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorry`, `admit`, new axiom, `native_decide`, unsafe
declaration, or compiler-trusting shortcut is used.

Artifact pins:

- formal module SHA-256:
  `512fdf1c72c8adddb946765b6645c509c867b0245d0c45bd0a20e7c25921556e`
- independent checks SHA-256:
  `968729837e1806fca72c43141e6f3ea62bf42e45beb306ee78b8fcad67791153`
- registered propositions: **29 of 29**

## Verification

Final checks on 2026-08-12 UTC:

- `lake build TheoryLib.PiQuantitativeBlockHitting.T67T67TwoThreeArctanShadow`
  — PASS
- `lake env lean work/ultrapi-resume/t67_independent_checks.lean` — PASS
- `pwsh -File scripts/check.ps1` — PASS:
  `kernel build, exploit scan, and exact-allowlist axiom audit succeeded`
- independent line-by-line audit and boundary replay — PASS

A green build means these exact statements are `machine-checked`; it does
not promote the canonical conjecture.
