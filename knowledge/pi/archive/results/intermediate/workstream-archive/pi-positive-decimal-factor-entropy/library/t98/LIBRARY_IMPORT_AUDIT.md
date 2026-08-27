# T98 accepted-library import audit

The following accepted local modules were read before the T98 derivation.  A
full `lake build TheoryLib` completed in this workspace after the prescribed
package-cache setup.  These hashes identify exactly the imported definitions
used for the convention audit; T98 does not treat any prose note as a proved
premise.

| module and role | SHA-256 | imported literal content |
|---|---|---|
| `TheoryLib/PiPositiveDecimalFactorEntropy/T56T56LagSectorAudit.lean` | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` | Lines 31-44 define `t56SampleLength n = 10^(n/2)` and the exact strict ordered lag decomposition: diagonal `L_n`, positive lags `1 <= r < L_n`, and starts `0 <= j < L_n-r`. |
| `TheoryLib/PiPositiveDecimalFactorEntropy/T27T27SparseMicroscopicEquivalence.lean` | `e4e7b2dd5d080616edee252e05c50c3cc9f56ddc7cd0420b71c3acaca2710c65` | Lines 456-565 expose C7 as the eventual `completePiFejerEnergy(10^(n/2),10^n/2) <= C*(10^n/2)*10^(n/2)` form and retain its quantifier order. Lines 154-160 give the complete signed triangular band. |
| `TheoryLib/PiPositiveDecimalFactorEntropy/T58T58TriangularFejerAudit.lean` | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` | Lines 26-46 repeat `L_n`, `H_n`, the positive strict band, the triangular short-lag rectangle, and weight `1-h/H`. |

T98 imports only these conventions into its prose and replay.  Its strict
integer block cutoff is explicitly labeled an analogue: it is not asserted to
equal T56's `circleDistance` condition for either pi or an infinite
Champernowne suffix.  The full C7 band is displayed but deliberately not
replaced by a finite block-collision count.
