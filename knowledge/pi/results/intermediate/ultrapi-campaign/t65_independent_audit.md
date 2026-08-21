# T65 independent audit: one-fifth-band Hutton prime product

Audit time: **2026-08-12T14:22:20Z**

## Verdict

**PASS.**  The exact finite statement in
`T65T65HuttonOneFifthPrimeProduct.lean` is `machine-checked`.  For
(R=4K+3), prime (p>7), (p\ne10889), and

\[
 3p\le R<5p,
\]

Lean proves (v_p(H_K)=-1), proves exact multiplicity one in the reduced
denominator of (H_K), and proves that the complete squarefree product of
the eligible finite prime set divides that denominator.  All 26 declarations
are imported into the aggregate library and registered in the central axiom
audit.  Their axiom surface is contained in the exact repository allowlist
`[propext, Classical.choice, Quot.sound]`.

This is exact rational-denominator arithmetic.  It proves no asymptotic
prime-product estimate, selected-numerator or complementary-phase estimate,
decimal-cylinder hit, or every-word theorem for pi.  V1 remains a
`conjecture`.

## Audited artifacts

- Normalized source: `problems/local/pi-digits.txt`
  - SHA-256:
    `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
  - The module header preserves this path and hash exactly.  The local source
    has no external source URL; none is invented.
- Formal module:
  `TheoryLib/PiQuantitativeBlockHitting/T65T65HuttonOneFifthPrimeProduct.lean`
  - SHA-256:
    `5abbbccd8b6cde2296edad23644709f1f714c7a0408dc6003b796645b8c045d9`
  - 448 lines; seven definitions, six lemmas, and thirteen theorems.
- Primary report: `work/ultrapi-resume/t65_one_fifth_prime_product_report.md`
  - SHA-256:
    `470ecaa48293c748bf035cac35fb5d140ec016fe6f8c8d83c90696ce058d11c5`
- Independent Lean replay:
  `work/ultrapi-resume/t65_independent_checks.lean`
  - SHA-256:
    `5166aba09d270df47f02dbc6d341befd697341f8c84cbd24c71d1c924fc1dab4`
- Aggregate import snapshot: `TheoryLib.lean`
  - SHA-256 at audit time:
    `0ed116f840e340780175b6b52d6cb161f3cca8bb15f0d66e189812c290d1a4ca`
- Central audit snapshot: `audit/AxiomAudit.lean`
  - SHA-256 at audit time:
    `006f0a00d49a3a64ee074521389dc5fa04333445935e932867a18e995ab72ef3`

## Mathematical audit

Write (H_K=\texttt{huttonLowerRat K}) and (R=4K+3).  The Taylor index
set is `range (huttonTermCount K)`, where
`huttonTermCount K = 2*(K+1)`.  Its largest odd exponent is therefore
(2(2K+1)+1=R).

### 1. Exact band and endpoint logic

The hypotheses

```text
R < 5*p,    3*p <= R
```

are exactly (R/5<p\le R/3).  Primality and (p>7) make (p) odd, so
(p=2k+1) for (k=p/2).  The exponent (p) occurs at index (k); the
exponent (3p) occurs at index (3k+1).  The closed inequality (3p\le R)
puts the second index in the prefix even when (3p=R).  This is reflected
correctly by `huttonLowerRat_eq_oneThreeRegular_add_singular`.

The upper inequality must be strict.  If (R=5p), the odd exponent (5p)
is still in the prefix but neither of the two erased indices.  The independent
check makes this defect concrete with (K=13), (R=55=5\cdot11): index 27
survives both erasures and its exponent is (2\cdot27+1=55), divisible by
11.  Thus T65 neither loses a valid equality endpoint nor admits an invalid
one.

### 2. Four-term combination

T61's exact pair identity at exponent (p=2k+1) is

\[
 {4(-1)^k(2\,7^p+3^p)\over p3^p7^p}.
\]

At exponent (3p), the index is (3k+1), whose sign is the negative of
((-1)^k).  Combining the two base-3/base-7 pairs over one denominator gives

\[
 {4(-1)^k C_p\over 3p\,3^{3p}7^{3p}},
 \qquad
 C_p=3(2\,7^p+3^p)3^{2p}7^{2p}
       -(2\,7^{3p}+3^{3p}).
\]

The independent Lean file re-derives this identity from T61's pair theorem;
it does not invoke T65's exported four-term identity.  This checks the factor
3, both powers (3^{2p}7^{2p}), the opposite sign, and the common
denominator (3p3^{3p}7^{3p}).

Fermat reduction gives

\[
\begin{aligned}
 C_p
 &\equiv3(2\cdot7+3)3^2 7^2-(2\cdot7^3+3^3)\\
 &=22491-713=21778=2\cdot10889\pmod p.
\end{aligned}
\]

The full displayed numerator has the additional unit factor (4(-1)^k),
so its corresponding unsigned residue is (4\cdot21778=87112).  T65
deliberately names `21778` after removing that outer unit; the two
presentations are consistent.

### 3. Exact exception scope

Lean verifies that 10889 is prime.  If a prime (p>7) divides (C_p), the
fixed-residue congruence makes (p\mid2\cdot10889).  The factor 2 is excluded
by (p>7), and primality of 10889 then forces (p=10889).  Conversely, the
independent replay proves

```text
(10889 : Int) divides huttonOneThreeCancellationFactor 10889.
```

Hence 10889 is the genuine and only exception to T65's singular-block
noncancellation mechanism among primes above seven.

The exception is not vacuous: for (K=8166),

\[
 R=4K+3=32667=3\cdot10889<5\cdot10889.
\]

Here (k=5444), the second singular index is 16333, and the term count is
16334, so both singular pairs really occur.  These facts are checked in Lean.

Scope matters: T65 proves valuation (-1) and denominator survival only
under `p != 10889`.  It proves the fixed singular residue cancels at 10889,
but it does **not** contain a declaration that 10889 is absent from the full
reduced denominator at (K=8166), nor the general exceptional-prime
if-and-only-if from `hutton_multi_band_attack.md`.  Those stronger assertions
remain part of that note's `proof sketch`/exact `experiment`, not T65's
`machine-checked` claim.  Calling 10889 a genuine exception is sound when
read precisely as an exception to the noncancellation/survival theorem.

### 4. Erased-index parity proof

For an unerased index (j), its exponent satisfies (2j+1\le R<5p).  If
(p\mid2j+1), write (2j+1=pt).  Positivity gives (t<5).  Since both
(p=2k+1) and (2j+1) are odd, the cofactor is odd, hence (t=1) or
(t=3).  The first case forces (j=k); the second forces (j=3k+1).
Both contradict membership in the twice-erased set.

The independent check isolates the parity kernel as a separate lemma and
then re-proves `oneFifthPrime_not_dvd_other_hutton_exponent` without calling
the exported theorem.  The argument does not silently require primality:
the explicit odd representation (p=2k+1), positivity, the strict prefix
bound, and the two erasures are sufficient.

### 5. Valuation and denominator multiplicity

For every unerased exponent, the preceding isolation makes its linear
denominator a (p)-unit.  Since (p>7), the bases 3 and 7 and coefficients
4 and 8 are also (p)-units.  T61's term lemmas therefore give valuation zero
termwise.  T65 applies the nonarchimedean finite-sum lemma separately to the
base-3 and base-7 sums and handles zero sub-sums and a zero regular block
explicitly, yielding a nonnegative valuation for the regular block.

Outside (p=10889), the combined numerator factor is a (p)-unit.  The
common denominator has exactly one factor of (p): its explicit linear
factor is (3p), while (p>7) keeps (p) away from 3 and 7.  Thus the
singular four-term block has valuation exactly (-1).  Adding a regular
block of valuation at least zero retains (-1) by the strict minimum form of
the ultrametric inequality.

The denominator theorem is stronger than divisibility.  It uses reducedness
of the rational numerator and denominator to show

```text
padicValNat p (huttonLowerRat K).den = 1.
```

The independent replay checks the closed endpoint (K=9), (R=39=3\cdot13):
13 belongs to the exact set, (v_{13}(H_9)=-1), and the reduced denominator
has exact 13-adic multiplicity one.  It also directly normalizes (H_8),
independently confirming divisibility of its denominator by 11 but not by
(11^2).

### 6. Exact finite set and product

The set definition is

```text
{p < R+1 | p.Prime and 7 < p and p != 10889
           and R < 5*p and 3*p <= R}.
```

Thus `mem_huttonOneFifthPrimeSet_iff` exposes exactly the theorem hypotheses;
the range bound is equivalent to (p\le R) and is already implied by
(3p\le R).  Every member is converted to its odd index using primality and
(p>7).  Distinct members are coprime because they are distinct primes, so
the generic T62 finite-product lemma combines their individual denominator
divisors.  The independent replay checks

```text
huttonOneFifthPrimeSet 8 = {11}
huttonOneFifthPrimeProduct 8 = 11
huttonOneFifthPrimeSet 9 = {11, 13}.
```

T64's band uses (R<3p), while T65 uses (3p\le R); their boundary split is
disjoint and exhaustive over the stated union.

## Registration and forbidden-construct audit

A mechanical name comparison found:

```text
module declarations       26
module #print axioms       26
audit/AxiomAudit.lean      26
TheoryLib.lean imports      1
audit imports               1
```

Both declaration-name comparisons were identical.  A focused token scan
found no `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, or `opaque`
declaration in the formal module or independent check.  Focused
`git diff --check` was clean.

Direct module compilation, the independent replay, and the central audit
reported no axioms beyond:

```text
propext
Classical.choice
Quot.sound
```

## Commands and outcomes

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T65T65HuttonOneFifthPrimeProduct.lean
lake env lean work/ultrapi-resume/t65_independent_checks.lean
lake env lean TheoryLib.lean
lake env lean audit/AxiomAudit.lean
python3 work/ultrapi-resume/hutton_multi_band_check.py
pwsh -File scripts/check.ps1
git diff --check -- <T65 module, report, independent checks, imports, and audit>
```

All commands exited zero.  The exact arithmetic checker replayed 102,404
local-coordinate assertions, 51,202 exact-valuation assertions, and 7,449
one-fifth-band assertions; these finite checks are an `experiment`, not the
proof.  The full repository gate ended with:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

Repository-wide output included pre-existing linter warnings in unrelated
modules; there was no T65 warning or gate failure.

## Scope verdict

T65 is a sound `machine-checked` support theorem.  It is not by itself
`literature-checked`, a `candidate resolution`, or a `verified resolution` of
V1.  The unresolved bridge is Archimedean: denominator support does not
control the selected numerator/complementary CRT phase or force a prescribed
decimal cylinder for pi.
