# T66 independent adversarial audit

Date: **2026-08-12 UTC**

Verdict: **PASS** for the stated support theorem.  The seven T66 declarations
compile, are imported and individually registered in the axiom audit, use only
the exact allowed axioms, and the mathematical parity/valuation argument is
sound.  The result is `machine-checked`; it is not a decimal-cylinder hit and
does not resolve V1.  V1 remains a `conjecture`.

## Audited artifacts

- source statement: `problems/local/pi-digits.txt`, SHA-256
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`;
- formal module:
  `TheoryLib/PiQuantitativeBlockHitting/T66T66HuttonDecimalTransient.lean`,
  SHA-256
  `b57aa7265d913c11ea42c8f64d6b91b1cb9a781d31ddad5eb5612a1a3153a01f`;
- primary report: `work/ultrapi-resume/t66_hutton_decimal_transient_report.md`,
  SHA-256 at review time
  `e21ca36e85600bae057678398f70b39bbfa6c26022ab381f94ffe159ffbf45d8`;
- independent concrete checks:
  `work/ultrapi-resume/t66_independent_checks.lean`, SHA-256
  `3a65d04e04b1465757078c443ad350c940a370b9c83ab9399a30593ac00f6c73`.

The source hash matches the immutable local normalization.  No external URL
was supplied, and T66 does not invent one.

## Independent mathematical derivation

Write (r=2k+1).  The equal-index base-three and base-seven Hutton terms
combine exactly as

\[
 U_k={4(-1)^k\bigl(2\,7^r+3^r\bigr)\over r3^r7^r}.
\]

Every factor in the displayed denominator is odd.  The integer
(2\,7^r+3^r) is even plus odd and is therefore odd.  The sign is a two-adic
unit, while (4) has exact two-adic valuation two.  Thus (U_k\ne0) and

\[
 v_2(U_k)=2
\]

for every (k\ge0).  This verifies the content of
`huttonCancellationFactor_odd` and
`padicValRat_two_huttonPairRat` without relying on examples.

For a finite sum, the nonarchimedean inequality says

\[
 v_2\!\left(\sum_k U_k\right)\ge \min_k v_2(U_k)=2
\]

unless the sum is zero.  T66 handles the zero branch explicitly in its
finite-set induction.  The exact pair-sum identity from T63 identifies this
sum with (H_K), and T63's proved positivity of (H_K) excludes zero.
Consequently (v_2(H_K)\ge2).  Cancellation may increase this valuation but
cannot lower it; T66 correctly avoids claiming an exact numerator valuation.

Now write nonzero (H_K=a/d) in reduced form.  Positive two-adic valuation
is incompatible with even (d): if (2\mid d), coprimality forces (a) odd,
so (v_2(a/d)<0).  Therefore (d) is odd and

\[
 v_2(d)=0.
\]

The imported T63 theorem has exactly the hypotheses
(5^e\le4K+3<5^{e+1}) and conclusion (v_5(d)=e), including (e=0).
Substitution gives the T66 endpoint

\[
 \max\{v_2(d),v_5(d)\}=\max\{0,e\}=e.
\]

No direction of an inequality is reversed, and no exactness is inferred from
the finite-sum lower bound: exactness at two is unnecessary because the
denominator conclusion only needs strict positivity.

## Decimal-preperiod interpretation

For a reduced nonzero rational (a/d), put
(alpha=v_2(d)), (eta=v_5(d)), and remove the (2)- and (5)-primary
parts to obtain a denominator (m) coprime to ten.  After
(n=\max(\alpha,\beta)) decimal shifts, those primary parts are cleared;
multiplication by ten permutes the residue classes modulo (m), so the tail
is periodic (or is the terminating zero tail when (m=1)).

Minimality is equally exact.  If a periodic tail of period (t>0) began
after (n) digits, the reduced denominator would divide
(10^n(10^t-1)).  Since (10^t-1) is coprime to ten, this forces
(alpha\le n) and (eta\le n).  Hence the minimal base-ten preperiod is
precisely (max(\alpha,\beta)).  The T66 theorem formalizes the maximum of
the denominator exponents; this standard expansion lemma is not separately
declared in T66.  The primary report was amended to make that trust boundary
explicit.

## Edge and boundary checks

The independent Lean check file verifies:

- (K=0), (R=3), (e=0):
  (H_0=87112/27783), and the maximum denominator exponent is zero;
- (K=1), (R=7), (e=1): a direct kernel reduction gives
  (H_1=198037417616/63038098935), with
  (63038098935=5\cdot12607619787), the cofactor not divisible by five,
  and the denominator odd;
- (K=6), (R=27): the first admissible (R\equiv3\pmod4) above
  (5^2=25), giving exponent two;
- (K=30), (R=123), and (K=31), (R=127): the last admissible value
  below (5^3=125) and the first above it give exponents two and three,
  respectively;
- nontrivial generic instances of the pair valuation, sum lower bound,
  denominator oddness, and the final maximum theorem.

These examples are checks only; the universal result comes from the Lean
proof, not finite evidence.

## Trust and integration audit

The module contains exactly seven declarations and exactly seven local
`#print axioms` commands.  `TheoryLib.lean` imports the module, while
`audit/AxiomAudit.lean` both imports it and registers all seven declarations:

1. `huttonCancellationFactor_odd`;
2. `padicValRat_two_huttonPairRat`;
3. `padicValRat_two_sum_lower`;
4. `two_le_padicValRat_two_huttonLowerRat`;
5. `huttonLowerRat_den_odd`;
6. `padicValNat_two_huttonLowerRat_den`;
7. `huttonLowerRat_baseTen_denominator_exponent`.

Direct axiom output for each declaration is a subset of
`propext`, `Classical.choice`, and `Quot.sound`.  A focused source scan found
no `sorry`, `admit`, `native_decide`, new axiom, `opaque`, `constant`, or
`unsafe` declaration.  The similarly numbered long-lag T66 file has a
different module path and namespace and creates no registration ambiguity.

Verification commands and outcomes:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T66T66HuttonDecimalTransient.lean
PASS (all seven axiom reports within the allowlist)

lake env lean work/ultrapi-resume/t66_independent_checks.lean
PASS

pwsh -File scripts/check.ps1
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.

git diff --check -- <T66 module, imports, audit, report, checks>
PASS
```

The full build emitted existing linter warnings elsewhere in the repository;
none was a T66 error and the verification command exited successfully.

## Scope boundary

T66 closes a bookkeeping ambiguity: for the Hutton rational shadow, T63's
five-adic exponent is the entire base-ten preperiod, because the reduced
denominator is odd.  It does not control any selected numerator after that
preperiod, prove that a decimal orbit enters a prescribed cylinder, or prove
distribution of pi's digits.  It therefore supplies no proof of the canonical
every-finite-word statement.
