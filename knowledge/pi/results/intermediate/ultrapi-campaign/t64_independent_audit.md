# T64 independent audit: one-third-band Hutton prime product

Audit time: 2026-08-12T13:55:18Z

## Verdict

**PASS.**  The exact finite denominator statement in
`T64T64HuttonOneThirdPrimeProduct.lean` is `machine-checked`.  The extension
from the upper-half condition `4*K+3 < 2*p` to the one-third condition
`4*K+3 < 3*p` is mathematically valid because all Taylor exponents in the
prefix are odd.  All eleven declarations are imported into the aggregate
library and registered in the central axiom audit.  Their reported axiom
footprint is exactly the repository allowlist
`[propext, Classical.choice, Quot.sound]`.

This result is not a proof that any prescribed decimal word occurs in pi.  It
contains no asymptotic lower bound for the prime product and no decimal-phase,
prefix-localization, cylinder-hit, normality, or V1 conclusion.

## Audited artifacts

- Formal module: `TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean`
  - SHA-256: `c1a40fe144a954bf5f6570d19700262c11a8e8e31d9a0f66a34d3d9b2dce6ab9`
  - 211 lines; two definitions, two lemmas, and seven theorems.
- Independent concrete checks: `work/ultrapi-resume/t64_independent_checks.lean`
  - SHA-256: `fc951e1099d60baabb39a6f4681e7bc4af65e4adf917ea9da936389ee4f6908b`
- Aggregate import snapshot: `TheoryLib.lean`
  - SHA-256 at audit time: `a13c26ec7ed87ed966ee7d77678058f512fa91a57832a8fb93b693b714c9abd8`
- Central audit snapshot: `audit/AxiomAudit.lean`
  - SHA-256 at audit time: `3a324de21f5eb5a2489e1520627bae7bce696f3739013ada0986cf1ebb49a0d9`
- Normalized source: `problems/local/pi-digits.txt`
  - SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
  - The module header records this path and hash exactly.  The local source has
    no external source URL to preserve.

## Mathematical audit

Write `R = 4*K+3`.  The Taylor index set is
`range (huttonTermCount K)` with `huttonTermCount K = 2*(K+1)`.  Therefore an
index in the range has odd exponent `2*j+1 <= R`.

### 1. Parity extension

`oneThirdPrime_not_dvd_other_hutton_exponent` assumes

```text
R < 3*p,    p = 2*k+1,
j in (range (huttonTermCount K)).erase k.
```

If `p | 2*j+1`, write `2*j+1 = p*t`.  The prefix bound and `R < 3*p`
give `t < 3`; positivity gives `p > 0`.  The three natural-number cases are:

- `t = 0`, impossible because `2*j+1 > 0`;
- `t = 1`, forcing `j = k`, contrary to membership in the erased set;
- `t = 2`, impossible because `2*j+1` is odd and `2*p` is even.

The Lean proof obtains exactly these three cases and closes each by Presburger
arithmetic.  It does not silently use primality: the odd representation
`p = 2*k+1` is the sufficient hypothesis for this isolation lemma.

### 2. Valuation transfer

`padicValRat_huttonRegularBlockRat_nonneg_oneThird` applies the isolation
lemma separately to every base-3 and base-7 regular term.  The inherited T61
lemmas give valuation zero termwise for prime `p > 7`; the nonarchimedean sum
lemmas then give a nonnegative valuation for the nonzero regular block.  Zero
sub-sums and a zero regular block are handled explicitly.

`padicValRat_huttonLowerRat_oneThirdPrime` uses:

- `p <= R` to ensure the singular index `k` lies in the prefix;
- prime `p > 7` to keep `p` away from the bases and coefficients;
- `p != 17` to prevent cancellation of the combined singular numerator;
- `R < 3*p` only for uniqueness of the singular exponent;
- `p = 2*k+1` to identify that exponent.

The inherited exact singular-pair valuation is `-1`, while the regular block
has valuation at least zero (or is zero).  Hence the valuation of the full
reduced rational shadow is exactly `-1`.

### 3. Reduced-denominator statements

`oneThirdPrime_dvd_huttonLowerRat_den` correctly converts negative rational
valuation into denominator divisibility.  The multiplicity theorem
`padicValNat_huttonLowerRat_den_oneThirdPrime` additionally uses reducedness
of the rational numerator and denominator to prove the denominator valuation
is exactly one.  Thus "occurs exactly once" means exact `padicValNat` value
one, not merely divisibility.

### 4. Exact finite set and product

The set is

```text
{p < R+1 | p.Prime and 7 < p and p != 17 and R < 3*p}.
```

Consequently `mem_huttonOneThirdPrimeSet_iff` exposes exactly

```text
p.Prime, 7 < p, p != 17, R < 3*p, p <= R.
```

The conversion of a member prime to `p = 2*(p/2)+1` uses primality and
`p != 2`, justified by `p > 7`.  Distinct members are coprime because they are
distinct primes.  The inherited generic finite-product lemma then proves that
the squarefree product of all members divides the reduced denominator.

The independent check file verifies representative endpoints by kernel
reduction:

- `K=2`, `R=11`: set `{11}`, product `11`, and the closed endpoint divides;
- `K=3`, `R=15`: set `{11,13}`, product `143`;
- `K=4`, `R=19`: set `{11,13,19}`, confirming exclusion of `17` and inclusion
  of the prime upper endpoint;
- `K=9`, `R=39=3*13`: `13` is excluded because the lower endpoint is strict,
  while `19` is included;
- at `K=2`, the denominator has exact 11-adic multiplicity one.

## Registration and forbidden-construct audit

`TheoryLib.lean` imports the T64 module.  `audit/AxiomAudit.lean` imports it
and contains `#print axioms` entries for all eleven declarations:

1. `oneThirdPrime_not_dvd_other_hutton_exponent`
2. `padicValRat_huttonRegularBlockRat_nonneg_oneThird`
3. `padicValRat_huttonLowerRat_oneThirdPrime`
4. `oneThirdPrime_dvd_huttonLowerRat_den`
5. `padicValNat_huttonLowerRat_den_oneThirdPrime`
6. `huttonOneThirdPrimeSet`
7. `huttonOneThirdPrimeProduct`
8. `mem_huttonOneThirdPrimeSet_iff`
9. `huttonOneThirdPrime_dvd_huttonLowerRat_den`
10. `huttonOneThirdPrimeSet_pairwise_coprime`
11. `huttonOneThirdPrimeProduct_dvd_huttonLowerRat_den`

A focused search found no `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe`, or `opaque` declaration in the module.  `git diff --check` was clean
for the module, aggregate imports, central audit, and independent check file.

## Commands and exact outcomes

```text
$ sha256sum problems/local/pi-digits.txt TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825  problems/local/pi-digits.txt
c1a40fe144a954bf5f6570d19700262c11a8e8e31d9a0f66a34d3d9b2dce6ab9  TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean

$ lake env lean TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean
exit 0; all eleven declarations reported only [propext, Classical.choice, Quot.sound]

$ lake env lean work/ultrapi-resume/t64_independent_checks.lean
exit 0; both printed declarations reported only [propext, Classical.choice, Quot.sound]

$ lake env lean TheoryLib.lean
exit 0; no output

$ lake env lean audit/AxiomAudit.lean
exit 0; all eleven T64 entries reported only [propext, Classical.choice, Quot.sound]

$ pwsh -File scripts/check.ps1
exit 0
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.

$ rg -n "\\b(sorry|admit|axiom|native_decide|unsafe|opaque)\\b" TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean
no matches

$ git diff --check -- TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean TheoryLib.lean audit/AxiomAudit.lean work/ultrapi-resume/t64_independent_checks.lean
exit 0; no output
```

Repository-wide build output included pre-existing linter warnings in unrelated
modules; no T64 warning or gate failure occurred.

## Scope boundary

The audited result is `machine-checked` exact arithmetic about a finite
rational approximation.  It is not `literature-checked`, a `candidate
resolution`, or a `verified resolution` of V1.  The remaining mathematical
gap is to turn denominator structure into a controlled decimal phase or
prefix-cylinder hit for fixed pi; T64 does not supply that bridge.
