# T96 source manifest

| File or module | Role | Verification |
|---|---|---|
| `pi-positive-decimal-factor-entropy.txt` | Immutable canonical statement; locally formulated, so no external URL exists | SHA-256 `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore` | Imported definitions and endpoint-safe closure/core lemmas | Kernel-checked accumulated-library source SHA-256 `0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083` |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T57T57MovingWordCoreObstruction` | Comparison only; no premise imported | Kernel-checked accumulated-library source SHA-256 `5c3dc436a961f6081777053a848d19394ca656fc918c931e6aa5062a14859a1b` |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T78T78SquareSparseProjectedPhaseObstruction` | Comparison only; no premise imported | Kernel-checked accumulated-library source SHA-256 `168bea9f90088b50ae9bf1173dda8c443ca3dd161875770f8f8a50568211cd85` |
| `T96FixedSeedSibling.lean` | Explicit fixed series, irrationality, carry-free scaled streams, factor overcount, omitted word, T44 Core membership, and orbit-closure theorem | Compiles with only `propext`, `Classical.choice`, and `Quot.sound`; imports T44 but not T57 or T78 |

No literature source is needed for the elementary fixed-seed construction.
The exact finite replay uses only the files delivered in this directory.
