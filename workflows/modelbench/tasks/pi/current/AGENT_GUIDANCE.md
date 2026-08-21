# Wave N: denominator valuation leaves

T87 machine-checks the literal rational SP1 congruence.  This wave addresses
only denominator clearing needed before scaled BBP partial sums and hidden
carry representatives can be defined safely.

Create `Contribution.lean` immediately, use the full project import path, and
compile against the real workspace.  Prove the requested universal bound; a
finite check is only `experiment`.  Preserve `t >= 1` and the inclusive
`k <= selectedDepth (2*t)` range.  No `sorry`, `admit`, new axioms,
`native_decide`, opaque/constant proof declarations, unsafe declarations, or
compiler-trusting shortcuts.  Make no hidden-carry, decimal, SP2, or V1 claim.

