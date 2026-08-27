# T23 finite successor envelope replay

Status: `machine-checked` finite A14 sibling result.

## Scope

The canonical statement is `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`,
whose required SHA-256 is
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
T23 treats one fixed prefix depth and one fixed finite cutoff. It does not assert
C2, canonical A1, coherent splitting, or any asymptotic property of pi.

The finite domains are an arbitrary parent `Fintype` and the ten-element type
`Fin 10`. Parent occupancy is the sum of the ten successor counts. The
second-largest count is the maximum, over all ordered pairs of distinct digits,
of the smaller count. Every energy weight is the square of parent occupancy.

## Theorem map

- Exact generic envelope:
  `feasibleParameters_iff_exact_envelope`.
- Explicit breakpoint set and completeness:
  `mem_parameterBreakpoints_iff`,
  `rowSplitEnergy_eq_of_no_breakpoint`, and
  `feasibleParameters_iff_at_cell_endpoint`.
- Low-multiplicity and singleton occupancy ceilings:
  `energy_le_of_lowMultiplicity_dominates` and
  `energy_le_of_singletons_dominate`.
- Accepted-T14 specialization:
  `pi_quantitativeSplittingLevel_iff_exact_envelope`,
  `pi_admissible_splitting_iff_mu_le_cap`,
  `mem_piRowParameterBreakpoints_iff`,
  `pi_rowSplitEnergy_eq_of_no_breakpoint`, and
  `pi_collisionEnergy_le_of_lowMultiplicity_dominates`.

The T14 theorems expose `0 < eta`, `eta <= 1/10`, `0 < mu`, `mu < 1`,
the positive cutoff assumption `1 <= N` where division by collision energy is
used, the finite parent set `Fin (10^n)`, every squared occupancy weight, and
both left-open/right-closed breakpoint endpoints.

## Replay

From the workspace root, after linking the pinned package cache as required by
the workflow, run:

```sh
lake env lean "removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t23-1784828087-r0/theory_artifacts/FiniteSuccessorEnvelope.lean"
```

The file imports
`TheoryLib.PiLacunaryNearReturnSparsity.T14CoherentSuccessorSplitting` and prints
the axioms of every theorem listed above. The observed axiom set is exactly
`propext`, `Classical.choice`, and `Quot.sound`.
