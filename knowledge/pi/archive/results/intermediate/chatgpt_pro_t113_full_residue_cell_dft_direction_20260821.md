# ChatGPT Pro T113 full-residue cell/DFT direction

Status: `proof sketch`

Experiment subsection status: `experiment`

## Executive finding

The completed web-Pro direction review agrees with the independent local
director on the central obstruction: T111's signed nonzero-frequency trough is
not a softer cancellation surrogate.  By exact character orthogonality it is
equivalent to positive multiplicity of the selected cell.  The next useful
bridge must therefore expose the actual floor-cell arithmetic of

`Q_N = 10^N * bbpPartial (7*N)`

through its full reduced numerator `A_N`, denominator `D_N`, residue
`r_N = A_N % D_N`, cell quotient `c_{q,N} = (q*r_N)/D_N`, and remainder
`e_{q,N} = (q*r_N)%D_N`.

The exact identity

`r_N/D_N = c_{q,N}/q + e_{q,N}/(q*D_N)`

shows why T112's unquantized phase is not yet T111's cell character.  The
missing factor is the sample-dependent phase of the exact floor defect.  At
frequencies comparable with `q`, it can be order one and cannot be discarded
as a uniform `O(1/q)` error.

## Recommended formal split

1. Exact generic quotient/remainder arithmetic and the specialization
   `cyclicCell q (sampledBBPOrbit N) = ((q*r_N)/D_N : ZMod q)`.
2. An exact pointwise factorization of the centered cell character into the
   raw T112 residue phase, target phase, and floor-defect phase.
3. A finite-sum rewrite of T111 through those synchronized factors, retaining
   the same `j : Fin M` in `10^j`, `bbpPartial (7*j)`, numerator, denominator,
   quotient, remainder, and both phases.
4. In parallel, the exact reduced-state successor with raw cross-product
   numerator/denominator and normalization gcd.  This is useful dynamic state,
   but it supplies no gcd bound or cell hit by itself.

The live free-model T113 precursor wave already implements the first rational
successor/seven-fraction layer and is attempting the exact cyclic-cell layer.
Independent direction review ranks the exact gcd-normalized successor as the
next research task because it adds non-tautological dynamic state.  The
defect-character factorization is then the best T111-facing dependent task,
followed by the finite DFT rewrite; the weighted-trough corollary is optional
bookkeeping because it is equivalent to the cell hit.

## Corrections and adaptation

The Pro model inspected stale remote head `9974c6b`, before canonical T112 was
visible.  Its assumed module name
`T112T112BBPFullResidueRepresentation` and proposed public `qN` definition do
not match the actual canonical module
`T112T112SampledBBPSelectedResidue`.  The mathematical proposal is retained,
but its Lean signatures must be adapted to T112's actual API and independently
compiled.  No proposed T113 declaration is currently promoted by this note.

The Pro answer also proposed importing `Mathlib.Data.Rat.Floor` directly.
Canonical integration should first check whether T111/T112 already provide the
needed transitive interface and keep the explicit import set minimal.  It
should also use canonical `Theory.PiDigits.T27.phase`, not the brittle
`FiniteCircleQuantization.phase` abbreviation.  Because the running T113 wave
already owns the successor/cell namespace, the later defect-weighted bridge
must be numbered T114 or above rather than colliding with it.

## Independently replayed exact experiment

An exact `fractions.Fraction` replay on 2026-08-21 reproduced every reported
pilot value:

- mesh `q=10`: first full cover at prefix `M=32`;
- mesh `q=100`: at `M=600`, cell 68 is uniquely missing; its first hit is
  `N=604`, so first full cover is `M=605`;
- mesh `q=200`: first full cover is `M=909`, with cell 8 first hit at `N=908`;
- mesh `q=1000`: only 635 cells occur among `N=0,...,1000`.

The `q=100` witness falsifies the naive universal bound `M <= 6*q` for full
coverage.  These finite values are `experiment`, not evidence for an
asymptotic coverage or cancellation theorem.

## Anti-hack boundary

Reject any continuation that remains invariant under same-three-adic-fiber
replacement, separates marginal CRT coordinates, keeps only numerator or only
denominator data, substitutes Parseval/scalar energy/symmetric moments for the
target-specific signed quantity, reindexes samples by target or frequency, or
defines the arithmetic cell as an alias of `cyclicCell`.  Unfolding must expose
the actual numerator, denominator, Euclidean quotient, Euclidean remainder,
and defect phase.

No cancellation, cell occupancy, cover, density, C1, V1, normality, novelty,
or digit theorem is claimed.

## Provenance

- Request SHA-256:
  `99d6e9bcaa633ec11ff28b2a595348d76025a942d47703ae7fc27dbbd41ca0dc`
- Raw answer SHA-256:
  `3fa9698ccafe2dce0c1ceed19a9d9310b537c82c186fbb83b3a58b8f7f5fe7ea`
- Web model label: `Pro`
- Completion contract: process exit 0, state `done`, nonempty answer, and
  `browser_closed: true`.
- The raw browser run is ignored operational state and is not proof authority.
