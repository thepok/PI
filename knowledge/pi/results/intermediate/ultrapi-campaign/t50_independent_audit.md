# T50 independent audit

Date: 2026-08-12 UTC  
Target: `TheoryLib/PiQuantitativeBlockHitting/T50T50MachinSeedLowerBandPrimeSurvival.lean`  
Target SHA-256: `931a50d0203ca0aa9c9d92eacf684d8d45022f8bf233dde00408a2ea25ff256c`  
Problem source: `problems/local/pi-digits.txt` (human-authored local root; no source URL)  
Problem-source SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Status: `machine-checked`. No arithmetic, indexing, band-splitting,
valuation, reduced-denominator, forbidden-construct, or axiom-audit error was
found in the exact T50 statements. This status applies only to the stated
fixed-seed rational and p-adic results. T50 does not prove a decimal-cylinder
hit, recurrence, normality, or occurrence of every finite decimal word in pi.

The independent audit first found that the original endpoint hypothesis was
the only non-fixed hole in the claimed two-band coverage. The endpoint case
has since been formalized in the same module and re-audited. Existing theorem
signatures were preserved; the strengthened final API uses names ending in
`closedEndpoint`.

## Exact scope and the remaining exclusions

Put `d = 12*N+15`. The final union theorem quantifies over `N p : Nat` and
assumes

- `p.Prime` and `d < 5*p` and `p <= d`, equivalently `d/5 < p <= d` in
  division-free form;
- `p` is different from `5, 11, 19, 233, 239, 317, 13757`.

It proves

`padicValRat p (sampledMachinValueRat (N+1)) = -1`

and separately that the reduced denominator contains `p` with exact
multiplicity one. No endpoint-divisibility hypothesis remains. Thus the final
theorem covers every prime in `d/5 < p <= d` except the displayed fixed finite
set. The earlier theorems with an explicit endpoint hypothesis remain intact
for compatibility and as simpler intermediate results.

## Exact-arithmetic audit

For the common odd exponents `p` and `3*p`, the combined singular block is

`4*(-1)^k * B(p) / (3*p*5^(3*p)*239^(3*p))`,

where

`B(p) = 3*(4*239^p-5^p)*5^(2*p)*239^(2*p) - (4*239^(3*p)-5^(3*p))`.

The index of `3*p` is `3*k+1` when `p=2*k+1`, and its sign is the opposite
of the sign at `p`; this agrees with the formula. Fermat reduction modulo
`p` gives the fixed residue

`R = 3*(4*239-5)*5^2*239^2 - (4*239^3-5^3)`.

Independent integer and rational calculations agree with the Lean
`norm_num` proofs:

```text
R = 4,019,547,774
  = 2 * 3 * 11 * 19 * 233 * 13,757

4*R / (3*5^3*239^3)
  = 5,359,397,032 / 1,706,489,875

5,359,397,032
  = 2^3 * 11 * 19 * 233 * 13,757
```

Consequently, for `p>5`, the only numerator exceptions in this lower block
are exactly `11, 19, 233, 13757`; `5` and `239` are denominator-base
exceptions. There is no missing factor `317` in this branch. The unique-term
branch instead uses `4*239-5 = 951 = 3*317`, so its exclusion of `317` is
load-bearing.

## Band, index, and endpoint audit

The common prefix has `6*N+8` terms. Its largest odd exponent is `d`, while
the extra base-239 term has exponent `d+2`.

- Lower band: `d < 5*p` and `3*p <= d`. Every common odd exponent is below
  `5*p`. Since both it and `p` are odd, its multiplier of `p` can only be
  `1` or `3`; the proof erases exactly the indices for `p` and `3*p`.
  Equality `3*p=d` is included and puts the second singular term at the last
  common index.
- Unique-term band: `d < 3*p` and `p <= d`. The only common odd exponent
  divisible by `p` is `p`: the possible multiplier `2` is even and multiplier
  `3` is excluded by the strict inequality.
- Union: splitting on `3*p <= d` yields exactly
  `d/5 < p <= d/3` or `d/3 < p <= d`. There is no gap or double-counting
  problem at `3*p=d`.

The extra exponent `d+2` is outside both common-term analyses, so it cannot be
silently treated as regular. The new `machine-checked` classification theorem
shows that, under the two-band bounds, `p | d+2` forces `d+2=5*p`. Its proof
extracts the quotient, proves it is below six, and eliminates all values other
than five using the exact linear congruences encoded by `d=12*N+15`.

As an `experiment`, exact rational evaluation for `0 <= N <= 30` checked all
908 non-fixed-exception `(N,p)` pairs in the final interval and found
reduced-denominator multiplicity one in every case. The endpoint cases were
`(N,p)=(4,13),(14,37),(24,61),(29,73)`; all four also happened to have
multiplicity one, in agreement with the strengthened theorem.

The endpoint closure groups the extra base-239 term with the common `p,3*p`
terms. The new exact Fermat residue is

```text
E = 5*R*239^2 - 3*5^3
  = 1,148,002,941,992,895
  = 3^2 * 5 * 463 * 55,099,733,237.
```

The corresponding localized coefficient is `machine-checked` as

```text
5,359,397,032 / 1,706,489,875 - 4/(5*239^5)
  = 306,134,117,864,772 / 97,476,408,149,875
  = (2^2 * 3 * 463 * 55,099,733,237) / (5^3 * 239^5).
```

Both `463` and `55,099,733,237` are proved prime by Lean. In the endpoint
valuation theorem, the equality `12*N+17=5*p` directly rules out equality of
`p` with either factor. The variable cancellation factor is then a p-unit by
its exact `ZMod p` reduction to `E`. The grouped singular block has valuation
`-1`; all remaining common terms are p-integral. This closes the endpoint
without adding either large factor to the final theorem's exception list.

## Exact denominator multiplicity

The last step is oriented correctly. From `v_p(q)=-1`, T50 first obtains
`p | q.den`. Reducedness of `q` then makes `p` coprime to `abs(q.num)`, so
the numerator valuation is zero. Expanding

`padicValRat p q = padicValInt p q.num - padicValNat p q.den`

therefore forces `padicValNat p q.den = 1`. The lower-band, unique-term, and
new endpoint branches each perform or feed this argument. The final
closed-endpoint theorem derives exact multiplicity directly from its unified
valuation result.

## Declarations, trust surface, and verification

The final file contains exactly 9 definitions and 49 propositions: 32
introduced with `theorem` and 17 with `lemma`. This is an addition of 4
definitions and 22 propositions over the initially audited version.

A source-token scan found no `sorry`, `admit`, `native_decide`, custom
`axiom`, `unsafe`, `opaque`, `constant`, `partial`, or `implemented_by`
declaration. Independent axiom output for all 22 new propositions contains
only the allowlisted dependencies `propext`, `Classical.choice`, and
`Quot.sound`; the two new exact integer-factorization propositions use only
`propext`. The original 27 propositions had the same clean trust surface.
All 49 proposition names are now registered exactly once under the T50
namespace in `audit/AxiomAudit.lean`; a sorted declaration-to-registration
comparison found no missing or extra name.

Verification performed:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T50T50MachinSeedLowerBandPrimeSurvival.lean
  passed

lake build TheoryLib.PiQuantitativeBlockHitting.T50T50MachinSeedLowerBandPrimeSurvival
  passed: 8566 jobs (T50 rebuilt)

temporary T50 endpoint axiom probe
  new propositions checked: 22
  non-allowlisted axioms: []

lake env lean audit/AxiomAudit.lean
  passed

final T50 declaration/audit comparison
  declared propositions: 49
  registered propositions: 49
  missing: []
  extra: []
```

Subsequent integration result: the coordinating agent ran the repository-wide
`scripts/check.ps1` gate after T49 and T50 settled. It completed all 8,493 jobs
and passed the kernel build, exploit scan, and exact-allowlist axiom audit on
2026-08-12 UTC.
