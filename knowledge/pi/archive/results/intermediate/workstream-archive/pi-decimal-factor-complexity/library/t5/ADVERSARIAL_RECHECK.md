# T5 adversarial recheck

Date: 2026-07-22

Claim status remains **proof sketch**.  The separator proof is complete on
paper but has not itself been formalized in Lean.  This note records checks;
it does not promote the claim to `machine-checked`.

## Immutable source

Command:

```text
sha256sum knowledge/pi/statements/pi-decimal-factor-complexity.txt
```

Observed SHA-256:

```text
e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43
```

This equals the required source hash.

## Reopened dependencies

The definitions and bridge theorem cited by
`GENERIC_DISJUNCTIVE_C1_SEPARATOR.md` were reread in the integrated T1 and T4
files and compared with the copies supplied in the accepted knowledge
library.  Their hashes agree pairwise:

```text
8b61e1319cd9fc753b93723f6f059583741da721252bdb7d3cace8b9c7a80c2e
  TheoryLib/PiDecimalFactorComplexity/T1DecimalFactorComplexity.lean
8b61e1319cd9fc753b93723f6f059583741da721252bdb7d3cace8b9c7a80c2e
  knowledge_library/t1/DecimalFactorComplexity.lean

805c1473696d94c689ea45f33d1c7270084518ebe20e5d3a05cbe094e485ceb1
  TheoryLib/PiDecimalFactorComplexity/T4FinitePrefixCollisionEnergy.lean
805c1473696d94c689ea45f33d1c7270084518ebe20e5d3a05cbe094e485ceb1
  knowledge_library/t4/FinitePrefixCollisionEnergy.lean
```

The relevant exact checks were:

- T1's stream is zero-based and its factors are contiguous blocks at
  arbitrary positions.
- T1's `Disjunctive` quantifies over every natural length, including zero.
- T4's sample is `Fin N`, exactly starts `0,...,N-1`.
- T4's energy is the sum of squared observed-factor multiplicities.
- T4's `CollisionEnergyC1` has quantifier order
  `forall C>0, exists n0>=1, forall n>=n0, exists N>=1` and uses a strict
  real inequality.

There are no external literature citations in the separator proof to reopen.

## Lean dependency compilation

After linking the pinned package cache, these commands completed
successfully:

```text
lake build TheoryLib
lake env lean TheoryLib/PiDecimalFactorComplexity/T1DecimalFactorComplexity.lean
lake env lean TheoryLib/PiDecimalFactorComplexity/T4FinitePrefixCollisionEnergy.lean
```

The output contained existing style and unused-variable warnings but no
errors.  The printed axioms of the cited T1/T4 theorems were subsets of the
allowed list `propext`, `Classical.choice`, and `Quot.sound`.

The T5 separator artifact contains no Lean file and claims no Lean theorem.
Accordingly, this compilation checks its accepted dependencies, not the new
separator argument.

## Proof attack checklist

The proof was re-derived against the acceptance sentence with the following
failure modes treated explicitly.

1. **Recursive circularity:** at stage `k`, `n_k` uses only `e_(k-1)`;
   `B_(j,k)` then uses known `n_j` and explicit `ell_r`; only afterward are
   `a_k` and `e_k` defined.
2. **Overlapping coding intervals:** the `j=k` term in the maximum gives
   `a_k>e_(k-1)`, so coding intervals are disjoint and ordered.
3. **Non-effective stream definition:** strict increase and unboundedness of
   `a_k` permit a terminating search for the first interval beginning after
   any requested coordinate.
4. **Omitted factor look-ahead:** a sampled start `i<N` can meet a future
   interval only if `a_r<i+n`; the proof counts such intervals through the
   inequality `a_m<N+n`.
5. **Off-by-one in one-interval counting:** starts meeting
   `[a_r,e_r)` lie from at earliest `a_r-n+1` through `e_r-1`, at most
   `ell_r+n-1`; the proof deliberately uses the weaker `ell_r+n`.
6. **All-prefix quantifier:** small `N` use the diagonal bound `E>=N`; every
   large `N` uses the bad-start invariant.  No prefix length is omitted.
7. **Eventual-length quantifier:** the lengths `n_j` are strictly increasing,
   so every proposed threshold has a bad `n_j` beyond it.
8. **Strict inequality:** the fixed witness `C=4` gives the reverse weak
   inequality for every positive `N`, which excludes C1's strict inequality.
9. **Disjunctivity at length zero:** the unique empty block occurs at position
   zero; positive lengths occur inside their explicitly enumerated `U_k`.
10. **Scope:** the construction is an artificial generic decimal stream and
    makes no claim about pi or canonical A1.

No mathematical defect was found in these checks.  The only earlier issue was
an omitted written mention of T1's zero-length disjunctivity case; that case
was added before this recheck.

## Experiments

The delivered argument contains no experiment and relies on no finite
computation.  Therefore there is no experiment to rerun and no empirical
output being presented as proof.

## Residual risk

The new construction and interval union bound remain manually checked rather
than kernel-checked.  The artifact therefore remains labeled `proof sketch`,
not `machine-checked`, `candidate resolution`, or `verified resolution`.
