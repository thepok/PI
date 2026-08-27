# T67 Formalization Report

Claim label: **machine-checked** for the named Lean theorems in
`TerminalRayStrength.lean`, subject to the independent kernel gate and statement
review. This report makes no additional mathematical claim.

## Immutable Statement

The canonical file is `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
Its verified SHA-256 is:

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical fixed-pi question remains open. Its count uses strict circular
distance, ordered pairs, all diagonal pairs, every positive `A`, every
sufficiently large `n`, and an `N` which may depend on `A,n`. No theorem in the
delivered module concludes that statement, C1, C2, normality, equidistribution,
or pair correlation.

## Imported Interfaces

The module imports the checked empirical-orbit interface T4, finite
cylinder-energy interface T7, signed terminal-shell interface T55, and direct
adjacent-variance interface T61. It also imports the checked Weyl empirical mean
and generic finite-group Parseval theorem. It does not import T60.

## Formalized Statements

1. `finiteEmpiricalFourier` is the positive-sign `1/N` Fourier coefficient of
   the genuine finite real decimal ray `10^j * beta`. Its identification with
   `Theory.PiDigits.T26.circleEmpiricalMean` is proved.
2. `length_mul_finiteEmpiricalInvarianceDefect` retains both finite telescope
   endpoints and proves
   `N*d(m) = phase(10^N*m,beta) - phase(m,beta)` for `1 <= N`.
3. `primitiveDecimalBases` uses `not 10 divides v`, not coprimality.
   `primitiveDecimalRayShell H v` is filtered on the exact half-open interval
   `H/10 < u <= H`, and `terminalShell_succ_eq` identifies this interval with
   T55's literal shell at `R=H+1`.
4. `T61QualifiedUPRID` is explicitly qualified to T61's exact predecessor
   remainder. It is not identified with T60's unformalized valuation-expanded
   predecessor budget. Its pointwise bound retains every `(u,j)` label on
   `terminalShell R` and `range ell`.
5. The qualified UPRID predicate implies T61's literal exact-remainder premise
   and then the literal strict Fejer threshold, retaining `R-1`, `j < ell`, the
   adjacent node `k+1`, and strict inequality.
6. `WalshWord m = Fin m -> ZMod 10` is the digitwise Walsh group, not the cyclic
   carry group `ZMod (10^m)`. The actual pi words use starts `Fin N` and the
   literal `1/N` empirical probabilities.
7. `walsh_centeredEnergy_eq_cylinderCollision_eq_nontrivial` proves the exact
   centered Parseval identity. Its middle term is T7's normalized half-open
   cylinder energy, hence counts ordered equal-cylinder pairs with all diagonal
   pairs and denominator `N^2`.
8. `AbstractFourierCutoffArray H` is only an arbitrary complex array on
   `Icc 1 H`. The sparse-ray and triangular bulk-shell separator theorems have
   witnesses only in this abstract type. Their theorem types contain no real
   parameter, circle sequence, probability measure, empirical measure, or
   orbit-realizability premise or conclusion.

## Verification

The exact command run was:

```text
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t67-1786060619-r0/theory_artifacts/TerminalRayStrength.lean
```

It completed successfully. The fourteen printed public endpoints depend only
on `propext`, `Classical.choice`, and `Quot.sound`.
