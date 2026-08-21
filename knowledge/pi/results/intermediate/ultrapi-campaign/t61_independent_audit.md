# Independent adversarial audit: T61 Hutton upper-half prime survival

Audit time: 2026-08-12T13:17:11Z.

Claim label: `machine-checked` for the exact rational and valuation theorems
listed below.  This is not a claim about decimal-block coverage of pi.

## Verdict

The revised T61 formal statement is correct as written.  I found no defect in
the term count, endpoint arithmetic, singular-pair combination, exceptional
prime analysis, p-adic valuation argument, or reduced-denominator conclusion.
The focused module, aggregate `TheoryLib` target, and direct axiom audit all
compiled successfully.  Each of the 15 theorem/lemma declarations is
registered exactly once in `audit/AxiomAudit.lean`, and every one reports only
the allowlisted axioms `propext`, `Classical.choice`, and `Quot.sound`.

During this audit I found that the first version of the module header omitted
the formal hypothesis `p > 7`.  That wording was too broad: for example, the
exact reduced denominators have `v_3(den(H_0)) = 4` and
`v_7(den(H_1)) = 8`, not one.  The author corrected the header during the
audit.  The audited version now says "every prime `p > 7`" and agrees with the
formal theorem.  No formal declaration changed as part of that correction.

## Normalized formal content

Put

```text
H_K = 8 * sum_{j=0}^{2K+1} (-1)^j / ((2j+1) 3^(2j+1))
    + 4 * sum_{j=0}^{2K+1} (-1)^j / ((2j+1) 7^(2j+1)),
R   = 4K+3.
```

For natural numbers `K,k,p`, T61 proves that if

```text
p is prime,  7 < p,  p != 17,
R < 2p,      p <= R, p = 2k+1,
```

then

```text
padicValRat p H_K = -1,
p divides den(H_K),
padicValNat p den(H_K) = 1.
```

Thus the eligible prime occurs exactly once in the reduced denominator.  The
API carries the odd-index witness `k` explicitly.  Since every prime `p > 7`
is odd, the intended universal consequence is obtained by taking
`k = (p-1)/2`; T61 does not package that choice as a separate wrapper theorem.

## Index, exponent, and uniqueness audit

`huttonTermCount K = 2*(K+1) = 2K+2`, so each `Finset.range` contains exactly
the indices

```text
j = 0,...,2K+1.
```

The corresponding odd exponents are `e_j = 2j+1`, from `1` through
`4K+3 = R`.  This agrees exactly with `huttonLowerRat K` in T58, whose Taylor
prefix length is `2*(K+1)`.

If `R < 2p` and `p` divides an exponent `e_j`, then
`0 < e_j <= R < 2p`; hence `e_j = p`.  The hypothesis `p = 2k+1` then forces
`j = k`.  Conversely, `p <= R` gives `k <= 2K+1`, so the singular index is
actually in the prefix, including the endpoint case `p = R`.  Therefore the
only `p`-divisible linear denominators are precisely the base-three and
base-seven terms at the one index `k`.  There is no off-by-one gap at either
endpoint.

The condition `p > 7` is essential to the formal unit argument: it excludes
the coefficients' prime divisor `2` and both series bases `3` and `7`.

## Singular numerator and the prime 17

At `p = 2k+1`, the two singular terms combine exactly as

```text
8*(-1)^k/(p*3^p) + 4*(-1)^k/(p*7^p)
  = 4*(-1)^k*(2*7^p + 3^p)/(p*3^p*7^p).
```

For prime `p`, Fermat in `ZMod p` gives

```text
2*7^p + 3^p = 2*7 + 3 = 17 (mod p),
4*(2*7^p + 3^p) = 68 (mod p).
```

Consequently no prime other than `17` can cancel the single linear factor
`p`.  Together with `p > 7`, all other numerator and denominator factors are
`p`-units, so the singular pair has valuation exactly `-1`.

The exception at `p = 17` is genuine, not a proof artifact.  Exact integer
arithmetic gives

```text
2*7^17 + 3^17 = 465261157114577
                  = 17 * 27368303359681,
27368303359681 = 5 (mod 17).
```

Thus the cancellation factor has 17-adic valuation exactly one.  For
`k = 8`, the unreduced singular fraction has numerator
`1861044628458308`, denominator `510713022416388762210597`, and gcd `17`.
After reduction it is

```text
109473213438724 / 30041942495081691894741,
```

whose numerator and denominator are both 17-units.  Correspondingly, in all
upper-half cases where `17` can occur (`K = 4,5,6,7`), exact computation finds
no factor `17` in the reduced denominator of `H_K`.

## Regular block and reduced-denominator audit

After erasing `k`, every remaining exponent is a `p`-unit by the uniqueness
argument above.  Since `p > 7`, the coefficients and bases are also units;
each remaining term therefore has valuation zero.  T61 separately sums the
base-three and base-seven regular terms and uses the ultrametric inequality to
obtain a nonnegative valuation for the complete regular block (with explicit
zero cases).

The singular block has valuation `-1` while the regular block is zero or has
valuation at least zero.  Unequal valuations prevent cancellation, so their
sum has valuation exactly `-1`.  Finally, `Rat.reduced` makes the numerator
coprime to the reduced denominator.  Once `p` is known to divide that
denominator, its numerator valuation is zero, and

```text
padicValRat p H_K
  = padicValInt p num(H_K) - padicValNat p den(H_K)
  = 0 - padicValNat p den(H_K) = -1
```

forces denominator multiplicity exactly one.

## Independent exact-rational experiments

These are `experiment` checks performed with Python's arbitrary-precision
`fractions.Fraction`, independently expanding both finite Taylor sums.  The
entries are `(v_p(numerator), v_p(denominator))` after exact reduction.

| `K` | `R` | exact reduced `H_K` | upper-half primes `p > 7` and valuations |
|---:|---:|---|---|
| 2 | 11 | `60523600449215608 / 19265262529822155` | `11: (0,1)` |
| 3 | 15 | `459056974189868332544096 / 146122373360431358535645` | `11: (0,1)`, `13: (0,1)` |
| 4 | 19 | `565426443440975989311677846008 / 179980826858896989916014909885` | `11: (0,1)`, `13: (0,1)`, `17: (0,0)`, `19: (0,1)` |
| 5 | 23 | `2529188103403767381744610578756515824 / 805065577331938346404699400854927755` | `13: (0,1)`, `17: (0,0)`, `19: (0,1)`, `23: (0,1)` |

Additional exact checks through `K = 8` found valuation one for every tested
eligible nonexceptional prime and valuation zero for `17` whenever it lay in
the upper half.  These computations corroborate but do not replace the Lean
proof.

The excluded small-prime behavior was also checked exactly:

```text
H_0 = 87112 / 27783,       v_3(den(H_0)) = 4;
H_1 = 198037417616 / 63038098935,
                              v_5(den(H_1)) = 1,
                              v_7(den(H_1)) = 8.
```

This confirms why the corrected prose must retain `p > 7`.

## Registration, build, and axiom evidence

`TheoryLib.lean` imports T61 exactly once, and `audit/AxiomAudit.lean` imports
it exactly once.  A scripted exact-name count found one audit registration for
each of these 15 declarations:

```text
huttonThreeTermRat_eq_fraction
huttonSevenTermRat_eq_fraction
huttonLowerRat_eq_term_sums
hutton_singular_pair_eq
huttonCancellationFactor_cast_zmod
prime_not_dvd_huttonCancellationFactor
upperHalfPrime_not_dvd_other_hutton_exponent
padicValRat_huttonThreeTermRat_eq_zero
padicValRat_huttonSevenTermRat_eq_zero
padicValRat_hutton_singular_pair
padicValRat_huttonRegularBlockRat_nonneg
huttonLowerRat_eq_regular_add_singular
padicValRat_huttonLowerRat_upperHalfPrime
upperHalfPrime_dvd_huttonLowerRat_den
padicValNat_huttonLowerRat_den_upperHalfPrime
```

Commands run against the revised source:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean
  exit 0; all 15 declarations report only the exact allowlist

lake build TheoryLib
  exit 0; aggregate TheoryLib build completed successfully (8765 jobs)

lake env lean audit/AxiomAudit.lean
  exit 0; all 15 T61 registrations report
  [propext, Classical.choice, Quot.sound]

forbidden-construct scan of T61
  no sorry, admit, native_decide, sorryAx, Lean.ofReduceBool,
  Lean.trustCompiler, axiom, opaque, constant, or unsafe declaration

git diff --check -- T61 module TheoryLib.lean audit/AxiomAudit.lean
  exit 0
```

Point-in-time SHA-256 hashes:

```text
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825  problems/local/pi-digits.txt
b8842721079f84c8a1bd7aa561d7d068f66a5e3e90cf91a2fb1cd52aaf49862c  TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean
14f5d4c1bd3fb7f34e009511359174640d886ad3a6d99b37114594422106bc2c  TheoryLib.lean
b9fd295c9ed2d54100305aa63f957fb25a69caf9d3e3836b1eda178dce0295f0  audit/AxiomAudit.lean
```

## V1 scope

T61 is exact denominator arithmetic for rational Hutton lower shadows.  It
does not prove a decimal-cylinder hit, discrepancy estimate, normality,
disjunctivity, or the canonical V1 statement that every finite decimal word
occurs in pi.  A large reduced denominator or long eventual decimal period of
`H_K` does not locate any desired block inside the short approximation horizon
available from the Hutton bracket (nor does the bracket automatically certify
decimal-prefix agreement at a boundary).  Therefore T61 is supporting
`machine-checked` infrastructure only; it is not a `candidate resolution` or
`verified resolution` of V1.
