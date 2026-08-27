# T52 independent audit

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Module: [`T52T52MachinSeedThreePrimaryPersistence.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean)  
Module SHA-256: `5ba17b604338ca283144223c0a284858669cd38b9025413ca674162ec673d4a0`

This audit was performed independently of the construction report. The local
source has no external source URL; none is invented here.

## Verdict and exact scope

No defect was found in T52's statement, indexing, three-adic argument, or
registration. The following local result is `machine-checked`:

> For all natural numbers `j,a`, if `1 <= j` and
> `3^a <= 12*j+3 < 3^(a+1)`, then
> `padicValRat 3 (sampledMachinValueRat j) = 1-a`, and the reduced
> denominator of `sampledMachinValueRat j` has exact three-adic multiplicity
> `a-1`.

The result is conditional only on the displayed interval, which selects the
usual unique exponent `a=floor(log_3(12*j+3))`. The hypotheses themselves
force `a >= 2`; there is no hidden small-`a` exception.

This is a local theorem about the rational Machin approximants. It does not
determine their complementary numerator phase or prove a decimal cylinder
hit. The canonical every-finite-word statement remains a `conjecture`; T52
is not a resolution of V1.

## Mathematical audit

### Index conversion and endpoints

At the `N`-indexed seed, T52 studies
`sampledMachinValueRat (N+1)` and puts `d=12*N+15`. The common Taylor indices
are

```text
0 <= k < seedCommonTermCount N = 6*(N+1)+2 = 6*N+8,
```

so their odd exponents run through `1,3,...,12*N+15`. The single unpaired
base-239 endpoint has Taylor index `6*N+8` and exponent `12*N+17`, which is
`2 mod 3` and hence a three-adic unit. Substitution `N=j-1`, justified by
`j>=1`, gives exactly

```text
12*(j-1)+15 = 12*j+3
```

and `sampledMachinValueRat ((j-1)+1) = sampledMachinValueRat j`. Thus the
direct-index theorems neither shift nor drop a boundary case.

### Cancellation factor and distinguished exponent

For every natural odd-exponent parameter `u`, the combined Machin numerator
is

```text
machinCancellationFactor u = 4*239^u - 5^u.
```

Since `239 = 5 (mod 9)`, this is `3*5^u (mod 9)`. It is divisible by three
and nonzero modulo nine because `5` is a unit modulo nine. Its exact
three-adic order is therefore one. After accounting for the denominator
`u*5^u*239^u`, the combined pair has exact valuation

```text
1 - padicValNat 3 u.
```

If `3^a <= d < 3^(a+1)`, then `u=3^a` occurs among the common odd exponents.
It is also the unique such exponent with three-adic order `a`: divisibility
gives `u=3^a*t`, the upper bound gives `0<t<3`, and oddness excludes `t=2`.
Every other common pair consequently has valuation at least `2-a`.

### Remainder, unique minimum, scaling, and denominator

T52 erases the distinguished pair, groups every other common exponent into
its exact two-term Machin pair, and appends the unpaired base-239 endpoint.
The nonarchimedean sum bound proves that this regular remainder is either
zero or has valuation at least `2-a`; the endpoint valuation zero satisfies
that threshold because the hypotheses force `a>=2`.

The distinguished pair has valuation `1-a`, strictly below the regular
threshold. T52 handles a zero regular remainder separately, proves the full
sum cannot vanish in the nonzero case, and applies the unique-minimum
addition law. This yields exact valuation `1-a` for the unscaled seed.
Multiplication by `10^(N+1)` changes nothing at the prime three.

Finally, `a>=2` makes the valuation negative, so three divides the reduced
denominator. Rational reducedness then makes the numerator coprime to three;
expanding `padicValRat` gives denominator valuation exactly `a-1`. This
conversion uses the reduced denominator, not an unreduced presentation.

## Mechanical audit

- The module contains **25** proposition declarations and **2** definitions.
- All 25 proposition names occur exactly once as fully qualified
  `#print axioms` entries in [`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean).
  Sorted name-set comparison produced no difference.
- The module is imported exactly once by both
  [`TheoryLib.lean`](../../TheoryLib.lean) and the axiom audit.
- `LEAN_NUM_THREADS=4 lake env lean --trust=0` compiled the T52 module
  successfully.
- An independent temporary harness printed axioms for all 25 declarations;
  every declaration used only a subset of `propext`, `Classical.choice`, and
  `Quot.sound`. The harness was removed after the check.
- Direct compilation of the complete `audit/AxiomAudit.lean` succeeded after
  a concurrently integrated T53 object became available. All 25 T52 entries
  were reached and printed.
- A focused scan found no `sorry`, `admit`, new `axiom`, `native_decide`,
  `unsafe`, or `opaque` declaration.
- `git diff --check` passed for T52 and its two integration files.

## Exact finite checks

These checks are labeled `experiment`; they corroborate indexing and signs
but are not part of the proof.

- `cross_index_quotient_check.py --max-j 80` reconstructed the exact rational
  Machin seeds for every `1 <= j <= 80` and found the predicted valuation
  `1-floor(log_3(12*j+3))` in all **80** cases. Its **3,240** persistent-tail
  divisibility checks also passed.
- Independent exact-integer checks verified `v_3(4*239^u-5^u)=1` for all
  **501** values `0 <= u <= 500`.
- Independent exact-rational checks verified the common-pair formula for all
  **251** indices `0 <= k <= 250`.
- Independent endpoint checks verified `3` does not divide `12*N+17` for all
  **251** values `0 <= N <= 250`.

All exact checks passed. No V1 claim is inferred from finite evidence.
