# T78 source manifest

Canonical statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`

Canonical SHA-256:

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical question was formulated locally and has no external source URL.
T78 is an explicit sibling construction and makes no claim about pi.

Imported kernel-checked modules at build time:

```text
0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083  T44T44EndpointSafeInvariantCore.lean
5c3dc436a961f6081777053a848d19394ca656fc918c931e6aa5062a14859a1b  T57T57MovingWordCoreObstruction.lean
d05450c90bfc2aff6567fc4c492575004e2dc96dc6a87fbb2aab4fcb12cd16e7  T72T72ProjectedPeriodicity.lean
```

Delivered Lean artifact SHA-256:

```text
168bea9f90088b50ae9bf1173dda8c443ca3dd161875770f8f8a50568211cd85  T78SquareSparseProjectedPhaseObstruction.lean
```

Verification commands run from the workspace root:

```text
lake env lean TheoryLib/PiPositiveDecimalFactorEntropy/T78T78SquareSparseProjectedPhaseObstruction.lean
lake build TheoryLib.PiPositiveDecimalFactorEntropy.T78T78SquareSparseProjectedPhaseObstruction
```

Both completed successfully. The printed axiom sets of every claimed theorem
are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
