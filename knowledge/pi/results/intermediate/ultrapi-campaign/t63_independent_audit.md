# T63 independent five-adic audit

Audit date: **2026-08-12 UTC**

Verdict: **PASS** for the stated support theorem.  T63 is `machine-checked`:
under

\[
  5^e \le 4K+3 < 5^{e+1},
\]

Lean proves

\[
  v_5(H_K)=-e,
  \qquad
  v_5(\operatorname{den}(H_K))=e,
  \quad H_K=\texttt{huttonLowerRat K}.
\]

This audit does not promote V1.  T63 is exact rational-denominator
arithmetic and supplies neither a decimal-cylinder hit nor the missing
numerator-phase/distribution estimate for pi.

## Audited artifacts

- Source problem: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
  SHA-256
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
  The source is local and has no external URL; none was invented.
- Formal module:
  [`T63T63HuttonFiveAdicTransient.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean),
  SHA-256
  `d7f42ff02ae0ab0877f8f165e88c9353e8bf72ee49f00c71087198f9cd41aaa2`.
- Primary note:
  [`t63_hutton_five_adic_transient.md`](t63_hutton_five_adic_transient.md),
  SHA-256
  `ac4b58ba1f1ded06d888bf3020d15e8a6877a5468f530c084a29d3c18ae1aec8`.
- Independent Lean replay:
  [`t63_independent_checks.lean`](t63_independent_checks.lean),
  SHA-256
  `5b4acce76fe57bd8105f1a3594a0dff15f403ac02af79fb0cc3fb7be6f986975`.

## Mathematical audit

The proof was checked against the defining paired summand

\[
 U_k=
 \frac{4(-1)^k\bigl(2\,7^r+3^r\bigr)}
      {r\,3^r7^r},\qquad r=2k+1.
\]

1. For odd `r`, modulo five one has `7=2`, `3=-2`, and hence
   `2*7^r+3^r = 2^r`, a nonzero residue.  Therefore
   `v_5(U_k)=-v_5(r)`; there is no hidden numerator cancellation.
2. If `0<r<=R<5^(e+1)`, `r` is odd, and `v_5(r)=e`, then
   `r=c*5^e` with `0<c<5`.  Oddness forces `c=1` or `c=3`.  This
   argument remains valid at `e=0`.
3. Since `5^e=1 mod 4`, the index of `5^e` is even.  The index of
   `3*5^e` is odd.  Thus the first minimum term has positive sign and
   the optional second minimum term has negative sign.
4. In the two-minimum case, scaling by `5^e` gives residues `3` and `1`
   modulo five.  T63 does not merely assert this: its common numerator is
   proved equal to `2` in `ZMod 5`, while the common denominator is a
   five-unit.  The minimum layer therefore cannot cancel.
5. Every other paired term has valuation at least `1-e`.  The finite
   ultrametric sum lemma explicitly allows the regular remainder to be
   zero; otherwise it retains that lower bound.  Adding it to the
   nonzero minimum layer preserves valuation `-e`.
6. The rational-denominator conversion uses reducedness.  If the reduced
   numerator were divisible by five, the denominator would be a
   five-unit, contradicting valuation `-e`; this also correctly handles
   `e=0`.  Positivity of every `H_K` supplies the required nonzero premise.

No endpoint or quantifier defect was found.  The lower inequality is closed,
the upper inequality is open, and inclusion of the second minimum is exactly
the closed test `3*5^e <= 4*K+3`.

The independent replay covers:

- `K=0`, `e=0`, where both minimum exponents `1` and `3` occur;
- the one-minimum cases `R=7` and `R=11` at `e=1`;
- the exact two-minimum boundary `R=15`;
- the one-minimum case `R=27` at `e=2`;
- the exact two-minimum boundary `R=75`;
- direct rational normalization at `K=1` and `K=3`, independently checking
  divisibility by `5` but not by `25`;
- the exact `K=0` identity
  `H_0=87112/27783` and its common numerator residue `87112=2 mod 5`.

The existing exact-arithmetic replay
[`hutton_global_crt_check.py`](hutton_global_crt_check.py) was also rerun.  It
checked the transient identity over all of its sampled Hutton prefixes and
ended with `all exact checks passed`; that finite replay is an `experiment`,
not a proof.

## Registration and trust surface

The module contains **33** named declarations.  A mechanical name comparison
found:

```text
module declarations       33
module #print axioms       33
audit/AxiomAudit.lean      33
TheoryLib.lean imports      1
audit imports               1
```

The two lists of registered declaration names are identical.  Direct Lean
auditing reports only the repository allowlist:

```text
propext
Classical.choice
Quot.sound
```

A token scan found no `sorry`, `admit`, `native_decide`, new `axiom`,
`unsafe`, or `opaque` declaration in the formal module or independent check.

## Commands rerun

```text
lake build TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient
lake env lean work/ultrapi-resume/t63_independent_checks.lean
lake env lean audit/AxiomAudit.lean
python3 work/ultrapi-resume/hutton_global_crt_check.py
pwsh -File scripts/check.ps1
git diff --check -- <T63 module, note, checks, imports, and axiom audit>
```

All commands exited zero.  The full gate ended with:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

## Correction made during review

The primary note originally described the five-adic exponent as the exact
length of the initial decimal transient.  That wording was too broad: the
full decimal preperiod can also depend on the denominator's two-adic
exponent.  The note now states precisely that T63 determines the exact
exponent of five in the base-10 transient component.

## Scope verdict

T63 is a sound `machine-checked` support theorem and may be used as the exact
five-adic input to the Hutton CRT analysis.  It is not a `candidate
resolution` of V1 and does not alter the open status of the every-finite-word
problem for pi.
