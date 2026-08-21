# Independent audit of T60: Hutton adjacent increment

Audit timestamp: 2026-08-12 12:54:59 UTC

Claim label: `machine-checked` for the three exact rational statements in
T60 after focused compilation and registration in the direct axiom audit.
This label does not apply to any decimal-occurrence or V1 claim.

## Verdict

Pass. I found no index, sign, coefficient, denominator, monotonicity,
registration, forbidden-construct, or axiom-surface defect in
`TheoryLib/PiQuantitativeBlockHitting/T60T60HuttonAdjacentIncrement.lean`.
The theorem scope and module documentation accurately stop at an exact
adjacent-step identity and strict monotonicity of the rational lower Hutton
approximants.

Nothing toward V1 follows from T60 alone. In particular, T60 supplies no
decimal-cylinder witness, no bound placing a prescribed cylinder around pi,
no orbit-distribution statement, and no proof that an arbitrary finite word
occurs in pi.

## Source and point-in-time hashes

- Original local source: `problems/local/pi-digits.txt`
  - SHA-256:
    `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Audited T60 module:
  - SHA-256:
    `8446346e507c4d2eb96a9b5aa7d4ad8ae6f0165d8fc202a0ab5fcd5c78c80fea`
- Point-in-time aggregate import file `TheoryLib.lean`:
  - SHA-256:
    `e8ea177a566c4c6f977b97b3cdb80767378133a891c9897bed729d0a622b60fd`
- Point-in-time audit file `audit/AxiomAudit.lean`:
  - SHA-256:
    `b288adbd96d3bb6aab6388bb80d3c9a02a3901a100f3336f2972ff46ff0c4c29`

The two aggregate files are shared, actively edited research artifacts, so
their hashes are only pins for the state audited here.

## Independent mathematical check

The definition imported from T58 is

```text
huttonLowerRat K
  = 8 * arctanPartialRat 3 (2*(K+1))
  + 4 * arctanPartialRat 7 (2*(K+1)).
```

Since `arctanPartialRat q t` sums indices `0,...,t-1`, passing from `K` to
`K+1` changes the number of terms from `2K+2` to `2K+4`. Thus the new indices
are exactly

```text
n = 2K+2 = 2*(K+1),
n+1 = 2K+3 = 2*(K+1)+1.
```

The first is even and the second is odd. For either positive base `q`, their
sum is therefore

```text
  1 / ((4K+5) q^(4K+5))
- 1 / ((4K+7) q^(4K+7))

= ((4K+7)q^2 - (4K+5))
  / ((4K+7)(4K+5)q^(4K+7)).
```

At `q=3`, the numerator before the outer Hutton coefficient is

```text
9(4K+7) - (4K+5) = 32K+58 = 2(16K+29).
```

Multiplication by the outer coefficient `8` gives the displayed numerator
`16(16K+29)`. At `q=7`, it is

```text
49(4K+7) - (4K+5) = 192K+338 = 2(96K+169),
```

and multiplication by the outer coefficient `4` gives
`8(96K+169)`. Both denominators are exactly
`(4K+7)(4K+5)q^(4K+7)`.

Writing `R=4K+7` makes `R-2=4K+5`, `16K+29=4R+1`, and
`96K+169=24R+1`. Hence the documentation's equivalent form is also exact:

```text
16(4R+1) / (R(R-2)3^R) + 8(24R+1) / (R(R-2)7^R).
```

All factors and both numerators are positive for every `K : Nat`. Therefore
`huttonLowerRat (K+1) - huttonLowerRat K > 0`, which gives precisely the
formal direction

```text
huttonLowerRat K < huttonLowerRat (K+1).
```

This is also consistent with the alternating-series picture: each even
partial sum gains one positive term followed by a smaller negative term.

## Independent exact rational examples

I independently evaluated the defining finite sums with exact rational
arithmetic and compared (i) direct subtraction, (ii) the two newly appended
Taylor terms, and (iii) T60's closed form.

| `K` | `huttonLowerRat K` | `huttonLowerRat (K+1)` | common exact increment | equality and positivity |
|---:|---:|---:|---:|:---:|
| 0 | `87112/27783` | `198037417616/63038098935` | `385080776/63038098935` | yes |
| 1 | `198037417616/63038098935` | `60523600449215608/19265262529822155` | `158227867400/3853052505964431` | yes |
| 2 | `60523600449215608/19265262529822155` | `459056974189868332544096/146122373360431358535645` | `4633661473347784/13283852123675578048695` | yes |
| 3 | `459056974189868332544096/146122373360431358535645` | `565426443440975989311677846008/179980826858896989916014909885` | `826084889271037384/251721436166289496386034839` | yes |

For all four rows, the three independently computed values of the increment
were identical as reduced fractions and strictly positive.

## Lean and registration checks

- Focused command:
  `lake env lean TheoryLib/PiQuantitativeBlockHitting/T60T60HuttonAdjacentIncrement.lean`
  - Exit code `0`.
  - Each of the three declarations reports exactly
    `[propext, Classical.choice, Quot.sound]`.
- Build command:
  `lake build TheoryLib.PiQuantitativeBlockHitting.T60T60HuttonAdjacentIncrement TheoryLib`
  - Exit code `0`; the aggregate build completed successfully.
- Direct audit command:
  `lake env lean audit/AxiomAudit.lean`
  - Exit code `0` after the new module was explicitly built.
  - The three T60 audit entries again report only
    `propext`, `Classical.choice`, and `Quot.sound`.
- A first direct-audit invocation before that build failed solely because the
  new T60 object file did not yet exist. The explicit build generated it, and
  the immediate rerun passed; this was build ordering, not a source or proof
  failure.
- `TheoryLib.lean` contains exactly one import of the audited T60 module.
- `audit/AxiomAudit.lean` contains exactly one import of it and exactly one
  `#print axioms` registration for each of its three declarations.
- A targeted forbidden-token scan found no `sorry`, `admit`, `native_decide`,
  `sorryAx`, compiler-trusting shortcut, new `axiom`, `opaque`, `constant`, or
  `unsafe` declaration in T60.
- `git diff --check` was clean for the T60 module and the two registration
  files at the audited state.

## Scope boundary

The exact adjacent increment can support later denominator or period
analysis, but it does not itself prove such a bound. Even an exact monotone
rational sequence converging to pi does not force any specified decimal
cylinder to contain pi, nor does it prove that the base-10 orbit of pi hits
every cylinder. Accordingly, the only justified research label here is
`machine-checked` for the three local T60 statements; there is no candidate
resolution of V1.
