# GP-0006 — central axiom-audit registration

Completed: 2026-08-21 UTC  
Claim effect: none; C1 remains a `conjecture`.

RA-0003 correctly found that nine representative T1–T17 endpoint theorems
were locally printed but absent from the central audit. Independent review
confirmed the exact declarations, and this task registered all nine in
`audit/AxiomAudit.lean`:

| Module | Registered endpoint |
|---|---|
| T1 | `QuantitativeBlockHitting.acceptance_audit_surface` |
| T2 | `QuantitativeChampernowneCover.champernowne_explicit_22_cover` |
| T3 | `QuantitativeAnalyticCover.explicit_uniform_pi_finiteFrequencyBounds_imply_C1` |
| T5 | `QuantitativeResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_resonance` |
| T6 | `PiNaturalScaleResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance` |
| T8 | `PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance` |
| T14 | `BoundaryRobustFejerDichotomy.not_C1_implies_unbounded_explicit_boundary_or_aggregated_resonance` |
| T16 | `DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance` |
| T17 | `PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine` |

## Verification

`pwsh workflows/verification/check.ps1` passed on 2026-08-21:

- 8,761 Lean jobs built;
- the forbidden-marker/exploit scan passed;
- the exact central axiom audit compiled;
- each added endpoint depends only on the allowlisted `propext`,
  `Classical.choice`, and `Quot.sound`.

The stale command originally written in the task was replaced by the current
repository gate. No Lean theorem, theorem statement, or proof was changed.
