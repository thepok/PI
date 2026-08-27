# T68: checked transient removal and route-specific incompatibility

Date: 2026-08-07 UTC.

Claim status: **machine-checked**, subject to the final independent axiom gate.

## Statement and scope

The canonical source remains
`local:pi-lacunary-near-return-sparsity`, with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Its canonical quantifiers are: for every integer `A>=1`, every sufficiently
large decimal depth `n` must admit an `N>=1` satisfying the ordered,
diagonal-inclusive near-return inequality.  T68 does not change or prove those
quantifiers.

The only question checked here is auxiliary and route-specific: after a
rational denominator is written as `5^e*m`, can the first power-of-five
iterates be removed and the remaining orbit treated by Bailey--Crandall at the
T55/T61 lengths and frequencies arising from the corrected-Zudilin displayed
denominator?

Ambiguities resolved explicitly:

- `e=0`, `J=0`, `J<=e`, and a frequency consuming all of `5^e` are included.
- The common split and the frequency-reduced split are distinct theorems.
- "Reduced" means a proved coprimality certificate under explicit factor and
  coprimality data, not a guessed valuation of a truncation numerator.
- The incompatibility concerns the displayed common exponent
  `2K-1+extra`, not the unknown reduced exponent.
- T65 is a proof sketch and is not a premise.

## Lean result

The module `CorrectedZudilinTransient.lean` uses the fresh namespace
`DecimalFactorComplexity.CorrectedZudilinTransientT68`.  It imports the
kernel-checked T61 module and reuses T61's `directFrequency`; it does not import
T65.

For arbitrary `e,J` and positive `m`, it proves

```text
sum(j<J) phase(h*a*10^j/(5^e*m))
  = sum(j<min(e,J)) phase(h*a*10^j/(5^e*m))
    + sum(t<J-e) phase(h*a*2^e*10^t/m).
```

This is valid for every function from rational arguments to an additive
commutative monoid, so it includes complex exponential phases without making
analytic assumptions.  The companion
`rational_orbit_coprime_tail_decomposition` retains the premise
`Coprime 10 m` and returns it alongside the exact split, making the
coprime-tail applicability condition literal in the theorem statement.

Given explicit data `h=5^s*g*u` and `m=g*M`, the module also proves the early
argument identity with denominator `5^(e-s-j)*M`, the tail identity beginning
at `(e-s)_+`, and the corresponding all-`e,J` sum decomposition.  Separate
theorems prove numerator/denominator coprimality under the explicit
`FrequencyReductionIsLowestTerms` conditions, and
`reduced_tail_modulus_coprime_ten` proves that the resulting tail modulus is
coprime to base 10.

## Applicability predicate

`T55T61ScaleConditions` retains:

- `K,ell,s>=1` and `R>=2`;
- the literal terminal shell `(R-1)/10 < u <= R-1` and `j<ell`;
- `Cq=(10^s-1)Ck`;
- T55 length `J=ell` and frequency `h=-Cq*u`, or T61 length `J=s` and either
  `h=Ck*u*(10^ell-10^j)` or ten times that frequency;
- `h!=0`, `0<epsilon<=1`, and the source-scale approximation inequality.

`BaileyCrandallTailApplicable` retains the full one-instance checklist from
Theorem 4.6: fixed pure-power presentation, coprime base and modulus, positive
large-exponent threshold, positive tail, positive source constants, frequency
gcd bound, and the source-faithful nontriviality majorant with `log M`
multiplying both square-root terms.

No field of either predicate states the desired contradiction or an equivalent
obstruction.

## Incompatibility

The kernel-checked arithmetic is:

1. The approximation scale and `0<epsilon<=1` imply
   `5^(J+1) < 5^K*(2K+1)`.
2. Induction gives `2K+1 <= 5^K`, hence the right side is at most `5^(2K)`.
3. Strict monotonicity of powers of five gives `J < 2K-1`.
4. The displayed exponent is `E=2K-1+extra`, while Bailey--Crandall requires
   a positive tail `E<J`.
5. These inequalities are contradictory.

Thus `correctedZudilin_route_parameters_incompatible` denies the complete
displayed-denominator parameter package.  It does not deny a package formed
from a genuinely shorter reduced exponent.  The displayed exponent is passed
definitionally to the Bailey--Crandall predicate rather than assumed equal to
an otherwise free exponent.

## Reproduction

From the project root, after the required package-cache setup:

```text
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t68-1786062320-r0/theory_artifacts/CorrectedZudilinTransient.lean
```

The command completed and the appended `#print axioms` audit reported only
`propext`, `Classical.choice`, and `Quot.sound`.  `SOURCE_MAP.md` pins the
external facts, prior interface hashes, applicability checklist, and exact
scope boundary.

## Non-claims

This result proves no normality, equidistribution, FSFS, C1, C2, canonical
near-return estimate, or statement about unrelated representations of pi.  It
does not formalize or assume an exact reduced 5-adic denominator exponent.
