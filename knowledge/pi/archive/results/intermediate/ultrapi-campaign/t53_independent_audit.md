# T53 independent audit: factored quotient and decimal carry

Date: 2026-08-12 UTC

Status: **machine-checked** for the 15 propositions stated in
`TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean`.
This status does not apply to decimal-word occurrence for pi, numerator
equidistribution, or V1.

## Pinned inputs

- Local problem source: `problems/local/pi-digits.txt`
- Source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Audited module SHA-256:
  `d3725c0e4c818765b9bc9b8bf4a8716b916e2e025f18461963f5ef270c44dcba`
- Independent checker SHA-256:
  `8e7e067473e2c1bdd695429f6565a8c372897d10005ab4efb43208856b3c5e9b`

## Statement and proof audit

The state represented by `b = F*c + r` is split at the factor `F`.  With

```text
k  = floor(10*r/F),       r' = (10*r) mod F,
q  = floor((10*c+k)/D),   c' = (10*c+k) mod D,
b' = F*c' + r',
```

the module proves

```text
10*b = (F*D)*q + b'.
```

This is the composition of the two Euclidean divisions
`10*r = F*k + r'` and `10*c+k = D*q+c'`.  No coprimality relation between
`F` and `D` is used or needed.

The range hypotheses are correctly separated:

- The unconditional reconstruction identity is valid even when `F=0` or
  `D=0`, using Lean's natural-number division and remainder conventions.
- Positivity of `F` and `D` is required for canonical remainder bounds and
  for identifying `q` and `b'` as quotient and remainder modulo `F*D`.
- The hypotheses `c<D` and `r<F` are additionally required to prove
  `q<10`.  Together they imply `F*c+r < F*D`, so this `q` is one decimal
  digit of the canonical rational state.
- `decimalCarry_eq_fullQuotient` itself is stronger and remains true for
  noncanonical `c,r`.  Its documentation now explicitly restricts the
  “base-ten digit” interpretation to a canonical state.

The rational identities

```text
(F*c+r)/(F*D) = c/D + r/(F*D),
D*(F*c+r)/(F*D) = c + r/F
```

have precisely the needed positivity hypotheses, which make both rational
denominators nonzero.

The next-state identities are mutually consistent:

```text
b' = (10*b) mod (F*D),
b' mod F = r',
floor(b'/F) = c'.
```

## Kernel, registration, and forbidden-construct audit

Direct recompilation succeeded:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean
```

All 15 theorem-level `#print axioms` results used only the exact repository
allowlist `{propext, Classical.choice, Quot.sound}`; several used no axioms.
There were no occurrences of `sorry`, `admit`, `native_decide`, `unsafe`,
`opaque`, or declarations of a new `axiom` or `constant` in the module.

The module contains 15 distinct audited theorem names.  The same 15 names
occur exactly once under `Theory.PiDigits.MachinQuotientCarry` in
`audit/AxiomAudit.lean`: no missing, extra, or duplicate registrations were
found.  The module is also imported by both `TheoryLib.lean` and the audit
file.

## Independent finite check

Label: **experiment**.  Finite enumeration is corroboration only, not a
proof.  Running

```text
python work/ultrapi-resume/t53_quotient_carry_check.py
```

gave:

```text
unconditional reconstruction cases: 456976
canonical two-level carry cases: 4326400
exact rational split cases: 360000
Euclidean reconstruction cases: 67617
coarse quotient bound cases: 4326400
all T53 independent exact finite checks passed
```

The first sweep includes zero factors and independently implements Lean's
`Nat.div`/`Nat.mod` zero-divisor convention.  The canonical sweep covers all
`1 <= F,D <= 64`, `0 <= c < D`, and `0 <= r < F`, checking the full quotient,
full remainder, fine and coarse next-state projections, all bounds, and the
digit range.

## Verdict

No mathematical, range-hypothesis, registration, forbidden-construct, or
axiom-footprint defect was found.  A documentation-only ambiguity about when
the quotient is a digit was corrected; no statement or proof changed.  T53 is
a clean **machine-checked** exact carry decomposition.  It exposes the
complementary quotient state but gives no estimate or control for the actual
Machin numerator, so it does not imply a cylinder hit, normality, V1, or a
proof that every finite decimal word occurs in pi.
