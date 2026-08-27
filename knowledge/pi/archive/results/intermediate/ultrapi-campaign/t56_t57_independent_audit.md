# Independent audit: T56 residual lift and T57 phase recombination

Audit time: 2026-08-12 12:25 UTC.

## Verdict

The seven displayed declarations in T56 and T57 are `machine-checked` with
only `propext`, `Classical.choice`, and `Quot.sound` among their reported
dependencies.  Their integer, rational, and `ZMod` algebra is correct.

This status is deliberately narrow.  T56 and T57 prove generic identities
under explicit hypotheses; neither module constructs those variables and
hypotheses from the actual Machin numerator state.  The Machin-specific
interpretation of the residual tower, including equation (11bj) in
`ultrapi.md`, therefore remains a `proof sketch`.  Neither module bounds,
equidistributes, contracts, or forces the fine residual.  Neither proves a
decimal-cylinder hit and neither advances canonical V1.

## Provenance and inspected artifacts

The immutable local source is `problems/local/pi-digits.txt`.  It has no
external source URL; this audit does not invent one.  Its SHA-256 is

```text
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
```

That digest agrees with the provenance header in both audited modules.

```text
fdf30c89cda9f49e3fb239fbfabb28f9f2f9dd417bc612d8e800334ca6bba903  TheoryLib/PiQuantitativeBlockHitting/T56T56ThreePrimaryResidualLift.lean
6eebf90b8fec7494c857f584621a5a0fdd2cb3ff2ad293d885b1e5c8b184a1c7  TheoryLib/PiQuantitativeBlockHitting/T57T57ThreePrimaryPhaseRecombination.lean
97a7fabb52386ca91bd3fbd6a925e231733d2e2c0c404eb6fcdb1c0d40a291ba  TheoryLib/PiQuantitativeBlockHitting/T55T55ThreePrimaryCoarseSelector.lean
```

T56 imports T55 and T57 imports T56.  Each of T56 and T57 occurs exactly once
in `TheoryLib.lean` and exactly once in `audit/AxiomAudit.lean`.  Every one of
the three T56 theorems and four T57 theorems occurs exactly once as an
explicit `#print axioms` entry in the audit file.

## Statement-by-statement semantic audit

### T56

- `residualNumerator_lift` expands
  `F*((C+d*u)-(L+d*v))+r` correctly as the old residual numerator plus
  `d*F*(u-v)`.
- `residual_ternary_recurrence` uses the two supplied divisibility equations
  and `d != 0` to cancel `d`, yielding exactly
  `3*R' = R + F*(u-v)`.  It does not prove that actual adjacent selector
  depths satisfy either divisibility equation, nor that `u` and `v` are
  canonical ternary digits.
- `residual_eq_inv_three_mul_zmod` correctly casts the supplied recurrence
  modulo `F` and multiplies by the inverse of three.  Calling this a
  permutation is justified only under its explicit hypothesis
  `IsUnit (3 : ZMod F)`.  The theorem does not prove that hypothesis for the
  intended actual value of `F`.

Thus T56 is `machine-checked` generic algebra.  Its intended actual-Machin
instantiation is a `proof sketch`.

### T57

- `residual_phase_recombination` correctly combines
  `b=F*c+r`, `c=C+d*t`, and `F*(C-L)+r=d*R` into
  `b=F*d*t+F*L+d*R`, then divides by nonzero `F*d` over the rationals.
- `residualNumerator_decimal_lift` correctly expands the proposed
  same-depth transformations
  `C'=10*C+f-d*a`, `L'=10*L-d*v`, and `r'=10*r-F*f`.
- `residual_decimal_recurrence` correctly cancels the nonzero fixed selector
  modulus `d` to obtain `R'=10*R+F*(v-a)`.
- `residual_eq_ten_mul_zmod` correctly casts that supplied recurrence modulo
  `F`.  It proves multiplication by ten, but not that this map is a
  permutation: that stronger wording would additionally require ten to be a
  unit modulo `F`.

T57 supplies no range conditions for `r`, `C`, `L`, or any carry variable; it
does not identify `f`, `a`, or `v` with canonical Euclidean carries; it keeps
`F` and `d` fixed; and it supplies no theorem connecting this generic state
to adjacent actual Machin samples.  Those omissions do not weaken the stated
identities, but they prevent an actual digit-dynamics claim.  T57 is
`machine-checked` only at this generic algebraic scope; the intended
Machin-specific bridge remains a `proof sketch`.

## Reproducible checks

The following commands were run from `/home/Marcel/dev/AllMath`.

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T56T56ThreePrimaryResidualLift.lean
```

Result: exit 0.  The first two declarations report `[propext, Quot.sound]`;
the `ZMod` inverse theorem reports `[propext, Classical.choice, Quot.sound]`.

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T57T57ThreePrimaryPhaseRecombination.lean
```

Result: exit 0.  The rational recombination theorem reports
`[propext, Classical.choice, Quot.sound]`; each remaining declaration reports
`[propext, Quot.sound]`.

```text
lake env lean audit/AxiomAudit.lean
```

Result: exit 0.  Its output includes all seven declarations with exactly the
dependencies just listed.

The focused forbidden-construct scan over T55--T57 searched for `sorry`,
`admit`, `native_decide`, `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, and declarations beginning with `axiom`, `opaque`,
`constant`, or `unsafe`.  It returned no matches.  `git diff --check` over
T56, T57, `TheoryLib.lean`, `audit/AxiomAudit.lean`, and `ultrapi.md` also
returned exit 0 with no output.

This audit did not rerun the full `scripts/check.ps1` gate.  Focused source
compilation plus the complete current axiom-audit compilation passed; the
full gate is still required after all concurrent repository edits settle.

## Required wording boundaries for `ultrapi.md`

Wording that the modules prove the displayed generic identities is accurate
when labeled `machine-checked`.  The note should retain all of these limits:

1. T56 formalizes only the generic algebra underlying (11bj), not its
   Machin-specific instantiation.
2. The T56 update is a permutation only with the explicit unit-of-three
   premise.
3. T57 formalizes exact generic recombination and fixed-depth carry
   transport, not canonical carries for the actual Machin sequence.
4. T57's multiplication-by-ten conclusion is transport, not necessarily a
   permutation and not cancellation or distribution.
5. T56 and T57 prove no residual estimate, decimal-cylinder hit, normality,
   disjunctivity, or V1.

With those boundaries, no wording correction is required for the existing
T56 table row and formalization-map paragraph inspected at audit time.  Any
new T57 row should use the narrower wording above.

The SHA-256 of this audit artifact is reported in the agent handoff rather
than embedded here, because embedding a file's own digest changes that
digest.
