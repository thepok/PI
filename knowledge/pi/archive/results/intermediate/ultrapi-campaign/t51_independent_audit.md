# T51 independent audit

Date: 2026-08-12 UTC  
Target: `TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean`  
Target SHA-256: `62d481ff6d7f0e10db8462fb439c8579f9d1cf75679f5fea1a840fa4366682d1`  
Problem source: `problems/local/pi-digits.txt` (Marcel's local source; no external source URL)  
Problem-source SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Status: `machine-checked`. I found no sign, coefficient, factorization,
band, endpoint, valuation, denominator, quantifier, registration, forbidden-
construct, or axiom-allowlist defect in the exact T51 statements. This status
applies only to T51's fixed-seed rational results. T51 is not a proof that
every finite decimal word occurs in pi, and it does not settle the
complementary numerator/CRT phase.

## Exact theorem scope

Put `d = 12*N+15` and

`Y_N = sampledMachinValueRat (N+1) = 10^(N+1) * machinLowerRat (3*(N+1))`.

The final closed-endpoint theorem assumes

- `p.Prime` and `7 < p`;
- `p != 239` and `p` is different from
  `19, 37, 79, 48049, 3586217`;
- `5*p <= d` and `d < 7*p`.

It proves `padicValRat p Y_N = -1`. A separate final theorem proves
`padicValNat p Y_N.den = 1`. Thus T51 covers the third band
`d/7 < p <= d/5`, expressed without natural-number division, outside the
displayed fixed finite set. Neither final theorem retains an endpoint
nondivisibility hypothesis.

## Independent sign and coefficient reconstruction

For `p = 2*k+1`, the combined base-5/base-239 pair at an odd exponent `m`
and its Taylor index `j` is

`4*(-1)^j * (4*239^m - 5^m) / (m*5^m*239^m)`.

The three relevant indices and signs are

```text
m = p:    j = k,       sign =  (-1)^k
m = 3*p:  j = 3*k+1,   sign = -(-1)^k
m = 5*p:  j = 5*k+2,   sign =  (-1)^k
```

Writing `M(m)=4*239^m-5^m`, their sum is therefore

```text
4*(-1)^k * T(p) / (15*p*5^(5*p)*239^(5*p)),

T(p) = 5*(3*M(p)*5^(2*p)*239^(2*p) - M(3*p))
         *5^(2*p)*239^(2*p)
       + 3*M(5*p).
```

This is exactly the module's `thirdBandCancellationFactor`; in particular,
the plus sign on the `5*p` contribution and the coefficients `5` and `3`
are correct. Fermat reduction modulo `p` gives

```text
R3 = 5*lowerBandFixedResidue*5^2*239^2
       + 3*(4*239^5-5^5)
   = 28,709,431,285,004,763
   = 3 * 19 * 37 * 79 * 48,049 * 3,586,217.
```

Independent integer and rational arithmetic reproduced the two exact Lean
equalities

```text
4*R3/(15*5^5*239^5)
  = 38,279,241,713,339,684 / 12,184,551,018,734,375,

38,279,241,713,339,684
  = 2^2 * 19 * 37 * 79 * 48,049 * 3,586,217.
```

The five displayed odd factors are prime. Since `p>7`, these are exactly the
non-base primes that can cancel the localized three-pair coefficient.

## Band and regular-term exclusion

The common prefix has `seedCommonTermCount N = 6*N+8` terms, so its largest
odd exponent is `d`. Under `d < 7*p`, every positive odd common exponent
divisible by odd `p` has an odd quotient strictly below seven. The quotient
is consequently `1`, `3`, or `5`, and the proof erases exactly the indices
`k`, `3*k+1`, and `5*k+2`.

The lower inequality `5*p <= d` puts all three erased indices inside the
common prefix, including equality at the last common term. No even quotient
is possible because both the common exponent and `p` are odd. The remaining
base-5 and base-239 common terms are individually `p`-integral. The extra
base-239 endpoint is treated separately, rather than silently included in
the regular common block.

## Endpoint reconstruction

Let `e=d+2=12*N+17` be the extra base-239 exponent. If `p | e`, then the band
gives `5*p < e < 8*p`; parity leaves only the quotient seven. Hence

`12*N+17 = 7*p`, and reduction modulo 12 gives `p % 12 = 11`.

At this endpoint the Taylor index is `6*N+8 = 7*k+3`. Its arctangent sign is
`-(-1)^k`, while the base-239 coefficient itself is `-4`; the resulting
endpoint term is therefore positive relative to `4*(-1)^k`. Combining it
with the three common pairs gives

```text
A(p) = 7*T(p)*239^(2*p) + 15*5^(5*p).
```

Its Fermat residue is

```text
E3 = 7*R3*239^2 + 15*5^5
   = 11,479,379,971,015,299,518,136
   = 2^3 * 3^3 * 13 * 29 * 8,429 * 35,533 * 470,668,789.
```

The corresponding reduced local coefficient is independently reproduced as

```text
4*E3/(105*5^5*239^7)
  = 15,305,839,961,353,732,690,848
      / 4,871,956,171,187,883,640,625,

15,305,839,961,353,732,690,848
  = 2^5 * 3^2 * 13 * 29 * 8,429 * 35,533 * 470,668,789.
```

Lean checks that `13, 29, 8429, 35533, 470668789` are prime. Their residues
modulo 12 are respectively `1, 5, 5, 1, 1`, so none can equal an endpoint
prime with residue 11. This correctly discharges the endpoint without adding
those factors to the final exception list. The separate exclusion `p != 239`
remains necessary because 239 is a denominator base and is itself 11 modulo
12.

## Valuation and reduced denominator

Outside the fixed exceptions, the three-pair singular numerator is a
`p`-unit. Its denominator has one explicit factor `p`, while `15`, `5`, and
`239` are `p`-units, so its valuation is exactly `-1`. In the endpoint case,
the adjusted numerator is likewise a `p`-unit and the adjusted denominator
again contains exactly one explicit factor `p`. Every regular term has
nonnegative valuation. The nonarchimedean addition lemma is applied in the
correct orientation: a valuation-`-1` singular block plus a zero or
nonnegative-valuation regular block still has valuation `-1`.

Multiplication by `10^(N+1)` does not change the valuation because `p>7`.
For the reduced-denominator theorem, `v_p(Y_N)=-1` first gives `p | Y_N.den`.
Reducedness makes `p` coprime to the absolute numerator, so its numerator
valuation is zero. Expanding `padicValRat` then forces the denominator
multiplicity to equal one. There is no reversal or loss of strength in this
conversion.

## Independent exact computations

As an `experiment`, an independent `fractions.Fraction` evaluation rebuilt
the arctangent prefixes directly from their definitions. For every admissible
pair with `0 <= N <= 30`, it checked the theorem hypotheses, the valuation,
and the reduced-denominator multiplicity. There were 72 admissible pairs and
no failures. The endpoint pairs in that range were

```text
(N,p) = (5,11), (12,23), (26,47),
```

and all had rational valuation `-1` and denominator multiplicity one. Direct
six-term identities were also checked at
`p = 11,13,17,23,31,41,47,59`; direct endpoint-adjusted identities were
checked at `(N,p)=(5,11),(12,23),(26,47),(33,59)`.

The fixed exceptions are genuine rather than cosmetic. For example, direct
evaluation gives valuation zero for `p=19` at `N=7,8,9`, and for `p=37` at
`N=15,16,17,18,19`; these pairs satisfy the third-band inequalities but not
the exception hypotheses. Finite computation is only an `experiment`, not a
proof; the Lean arguments establish the universal statements actually
claimed.

## Declarations and trust surface

The file contains exactly 9 definitions and 37 propositions: 24 introduced
with `theorem` and 13 with `lemma`. A sorted comparison against every T51
entry in `audit/AxiomAudit.lean` found 37 registrations, no duplicate, no
missing proposition, and no extra proposition. `TheoryLib.lean` imports T51.

A focused source-token scan found no `sorry`, `admit`, `native_decide`, new
`axiom`, `unsafe`, `opaque`, `constant`, `partial`, or `implemented_by`
declaration. The axiom output for all 37 propositions contains only the
allowlisted dependencies `propext`, `Classical.choice`, and `Quot.sound`;
several exact arithmetic equalities need only `propext`.

Checks performed independently:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean
  passed

lake build TheoryLib.PiQuantitativeBlockHitting.T51T51MachinSeedThirdBandPrimeSurvival
  passed: Build completed successfully (8567 jobs)

lake env lean audit/AxiomAudit.lean
  passed

T51 declaration/registration comparison
  declared propositions: 37
  registered propositions: 37
  duplicate: []
  missing: []
  extra: []
```

No module, umbrella-import, or audit file was changed by this independent
audit.
