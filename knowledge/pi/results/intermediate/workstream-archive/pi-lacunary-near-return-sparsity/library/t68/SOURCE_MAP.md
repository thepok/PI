# T68 pinned source map

Checked: 2026-08-07 UTC.

## Canonical statement

- Source URL: `local:pi-lacunary-near-return-sparsity`.
- Project source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Delivered byte-exact copy: `canonical_statement.txt`.
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Scope: T68 proves no assertion about `Q_pi`, C1, C2, normality, or
  equidistribution.  It checks only one proposed rational-approximation route.

## External source facts

### Corrected Zudilin manuscript

Wadim Zudilin, *A BBP-style computation for pi in base 5*,
arXiv:2409.10097v2, 17 September 2024.

- Versioned record: <https://arxiv.org/abs/2409.10097v2>
- Versioned PDF: <https://arxiv.org/pdf/2409.10097v2>
- PDF SHA-256:
  `01ba3b7b1ebd22d0d718b0fa3ed67d20030870a2bfe41a3a6b3ff7a3ce479d25`.
- `pdftotext -layout` SHA-256:
  `73f138af3f4871548dcad600f862cf2bc6a84bc77548bbb95c4d0d549afa16c8`.
- Exact locator: Section 3, "An obvious flaw", PDF p. 3; retained text line
  151 states that the affected term has denominator
  `5^(2n+1-d+k) m`.

T68 uses this only to identify the corrected displayed-denominator route.  It
does not assert a formula for the reduced denominator of a sum of corrected
terms.

### Bailey--Crandall theorem

David H. Bailey and Richard E. Crandall, *Random Generators and Normal
Numbers*, Experimental Mathematics 11 (2002), no. 4, 527--546.

- DOI: <https://doi.org/10.1080/10586458.2002.10504704>
- Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
- PDF SHA-256:
  `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`.
- `pdftotext -layout` SHA-256:
  `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`.
- Exact locator: Theorem 4.6 and its proof, printed pp. 12--13; retained text
  lines 621--645.

For fixed coprime integers `b,c>1`, the theorem supplies positive constants
`A,B,D`, depending only on `b,c`, and for every positive length `J`, all
sufficiently large exponents `nu`, and
`gcd(H,c^nu) < D*c^nu`, bounds the exponential sum by

```text
B * (A*c^(nu/2) + J*c^(-nu/2)) * log(c^nu).
```

The logarithm multiplies both terms.  This is the source-faithful placement;
T63 REPORT equations (3.17) and (7.5) misplaced it on only the second term.

## Pinned prior maps and interfaces

- T63 `REPORT.md` SHA-256:
  `28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59`.
- T63 `SOURCE_PINS.md` SHA-256:
  `8087d065d6bb44f5f5e36b9d2a8fac0eae351196ba6fa421335f849776be1c34`.
- T55 `SignedMultiplierTenPairing.lean` SHA-256:
  `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd`.
- T61 `DirectLabelAdjacentPhaseVariance.lean` SHA-256:
  `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb`.
- T65 `REPORT.md` SHA-256:
  `5c3a83661ecf6ec7556639d4198bf61c37b48a2ef76289e0d7e51a8f6e51bf38`.

T55 and T61 are kernel-checked interfaces.  Their literal route data used in
T68 are the terminal shell `((R-1)/10, R-1]`, T55 frequencies `-Cq*u` at
length `ell`, T61 frequencies `Ck*u*(10^ell-10^j)` and ten times those at
length `s`, and `Cq=(10^s-1)Ck`.  The Lean module imports T61 and directly
uses its `directFrequency` declaration.

T65 is an unverified proof sketch.  It was used to identify statements needing
formalization, but it is not imported and no T65 claim is a premise of the
Lean module.

## Kernel-checked algebra map

All declarations below are in
`DecimalFactorComplexity.CorrectedZudilinTransientT68`.

| Lean declarations | Checked content | External premise used |
|---|---|---|
| `orbitArgument_add_transient`, `frequencyOrbitArgument_add_transient` | Cancels `5^e` from `10^(e+t)` exactly | None |
| `rational_orbit_transient_tail_decomposition`, `rational_orbit_coprime_tail_decomposition` | All-`e,J` split at `min(e,J)`, including empty tails, with the latter exposing coprimality of `m` with base 10 | None |
| `reduced_frequency_early_identity`, `reduced_frequency_tail_identity` | Explicit factor-dependent shortening from `e` to `e-s` | None |
| `reduced_frequency_early_denominator_coprime`, `reduced_frequency_tail_denominator_coprime`, `reduced_tail_modulus_coprime_ten` | Lowest-term and base-coprime tail certificates under displayed coprimality conditions | None |
| `rational_orbit_reduced_frequency_decomposition` | Frequency-dependent all-`e,J` finite-sum split | None |
| `T55T61ScaleConditions` | Literal T55/T61 label, length, frequency, and approximation-scale fields | Predicate definition only |
| `BaileyCrandallTailApplicable` | Every one-instance applicability and nontriviality field listed below | Predicate definition only |
| `approximation_scale_forces_J_lt_two_mul_K_sub_one` | Source-scale arithmetic forces `J < 2K-1` | Its explicit hypotheses only |
| `correctedZudilin_route_parameters_incompatible` | Displayed exponent and positive tail contradict the scale inequality | Its explicit predicate only |

`BaileyCrandallTailApplicable` displays: `c>1`, coprimality with base 10,
`M=c^nu`, a positive sufficiently-large threshold `nu0<=nu`, coprimality of
the resulting modulus, positive tail length `E<J`, nontrivial modulus,
positive `A,B,D`, the frequency gcd condition, and the source-faithful
square-root/logarithmic majorant being no larger than the trivial tail length.
The enclosing predicate also identifies
`H=|h*a*2^(displayedFiveExponent K extra)|`.

## Scope boundary

`displayedFiveExponent K extra = 2K-1+extra` represents the displayed common
power-of-five denominator and its nonnegative lcm contribution.  The final
predicate passes this exponent definitionally to the Bailey--Crandall tail
predicate; it is not supplied through an assumed equality.  The theorem
concerns that displayed exponent only.  It does not claim that the
reduced exponent equals it, does not bound cancellation in a common numerator,
and does not exclude another representation of pi or another rational
approximant with a shorter reduced transient.
