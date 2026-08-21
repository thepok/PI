# T76 abstract exceptional-path cylinder cover

Audit date: **2026-08-13 UTC**

Status: `machine-checked`

Canonical source: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The source is Marcel's immutable local question and contains no external URL;
none is invented here.

## Exact scope

The Lean module
[T76T76ExceptionalPathCylinderCover.lean](../../TheoryLib/PiQuantitativeBlockHitting/T76T76ExceptionalPathCylinderCover.lean)
formalizes only the following abstract implication.

Let `p >= 2`.  At every depth `n`, let `B n` be a finite family of prefixes
in `(Fin n -> Fin p)`, and suppose there is one fixed natural number `C` such
that

\[
                         |B_n|\le C\qquad(n\ge0).                \tag{T76.1}
\]

Each depth-`n` cylinder receives uniform Bernoulli weight `p^{-n}`.  Define
the infinitely-often bad set by

\[
 L=\{x:\ \forall N\ \exists n\ge N,\ x|_n\in B_n\}.           \tag{T76.2}
\]

Then for every `epsilon > 0`, there is a depth `N` such that all of `L` is
covered by the countable family

\[
 \bigl\{[w]: k\in\mathbb N,\ w\in B_{N+k}\bigr\},              \tag{T76.3}
\]

and the sum of its individual cylinder weights is below `epsilon`.  The
proof records the explicit bound

\[
 \sum_{k\ge0}|B_{N+k}|p^{-(N+k)}
 \le {C p^{-N}\over1-p^{-1}}.                                  \tag{T76.4}
\]

The formal theorem is
`badLimsup_has_arbitrarily_small_indexed_cylinder_cover`.  It contains a
concrete countable sigma index for every individual cylinder, proves that
its union equals the tail cover, and proves that the corresponding `tsum`
equals the aggregate tail weight.

## Connection to the current BBP exceptional-path calculation

The frozen `proof sketch`
[bbp_exceptional_path_actual_complement_20260813.md](bbp_exceptional_path_actual_complement_20260813.md),
SHA-256
`95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc`,
derives for a fixed threshold `eta > 0` an even-epoch Haar bound

\[
 \mu(E_{4+2r}(\eta))\le {2\over\eta^2 3^{2+2r}},\qquad
 \sum_{r\ge0}\mu(E_{4+2r}(\eta))\le {1\over4\eta^2}.           \tag{T76.5}
\]

T76 is an abstract, measure-free outer-cover counterpart of the elementary
summability step behind that argument.  Its theorem
`hasSum_evenEpochHaarMajorant` separately checks the exact real-series
identity in (T76.5), including the constant `1 / (4 * eta^2)`.  It does not
formalize the complex correlation estimate, Haar cylinder normalization, or
the threshold intersection.  Those require a separate faithful translation
of the arithmetic setup.

Most importantly, neither (T76.5) nor T76 selects the actual deterministic
BBP coefficient path.  The exceptional-prefix complements change across
levels because the weights `W_e` change; there is no nested bad tree or
proved Haar-genericity of the selected path.  The module therefore proves
nothing about `Real.pi`, canonical V1, decimal disjunctivity, or normality.

## Normalized quantifiers and ambiguities

- `p`, `C`, and the complete family `B` are fixed before `epsilon` is chosen.
- The same bound `C` holds at every natural depth.
- `badLimsup` means cofinally many bad-prefix depths, not eventual badness.
- The cover may depend on `epsilon` through its starting depth `N`.
- No nesting or compatibility between `B_n` and `B_{n+1}` is assumed.
- No probability law on a named path is assumed or concluded.
- The result remains true if some prefix families are empty.

## Mathlib and literature check

The repository and mathlib were searched before implementation.  Existing
local modules use the measure-theoretic first Borel--Cantelli lemma, and
mathlib provides `MeasureTheory.measure_limsup_atTop_eq_zero` in
`Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`.  T76 deliberately avoids
duplicating measure infrastructure: its target is the more elementary
outer-cover certificate requested here.  The classical Borel--Cantelli
deduction is not a novelty claim.  The dated primary-literature context is
recorded in
[fresh_special_value_fractal_literature_20260813.md](fresh_special_value_fractal_literature_20260813.md).

## Verification

The module contains no `sorry`, `admit`, `native_decide`, custom axiom,
unsafe declaration, or compiler-trusting shortcut.  Every theorem used for
the research claim is registered in `audit/AxiomAudit.lean` and the module is
imported by `TheoryLib.lean`.

Focused command:

```text
lake env lean \
  TheoryLib/PiQuantitativeBlockHitting/T76T76ExceptionalPathCylinderCover.lean
```

The focused module build, `TheoryLib.lean`, and `audit/AxiomAudit.lean` all
compiled successfully.  The required full gate was then run from the
repository root:

```text
pwsh -NoProfile -File scripts/check.ps1
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

The printed dependencies for every registered T76 theorem were subsets of
exactly `propext`, `Classical.choice`, and `Quot.sound`.
