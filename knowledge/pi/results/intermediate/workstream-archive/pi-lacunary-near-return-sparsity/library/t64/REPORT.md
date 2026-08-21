# T64: machine-checked one-row aggregate Fejer criterion

Status: `machine-checked` for the finite conditional theorems listed below.
This artifact makes no C2, C1, canonical near-return, normality, or
unconditional fixed-pi cancellation claim.

## Scope and provenance

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

`AggregateFejerCriterion.lean` directly imports the kernel-checked T14 and T25
modules and the separately checked boundary-robust scalar Fejer module. It does
not import T59; the T59 note was used only as an unverified specification to be
re-proved.

The formal row is exactly

```text
1 <= ell < m <= k,    P = N k > 0,    q = 10^ell.
```

Parent cylinders are `[a/q,(a+1)/q)`. Successor cylinders are
`[(10*a+d)/(10*q),(10*a+d+1)/(10*q))`. The theorem
`literal_row_halfOpen_fejer_expansions` displays those half-open intervals,
the row inequalities, cutoff, and both finite signed-frequency expansions.

## Checked content

1. `phase_grid_sum` proves root-of-unity orthogonality on all labels
   `a : Fin q`.
2. `collectedFejerCoefficient_eq` collects equal numerical pairs and retains
   every alias satisfying `q | h+k`, not only `k=-h`.
3. `nonzeroCollectedFejerL1Norm_eq_divisibility_sum` and
   `nonzeroCollectedFejerL2SqNorm_eq_divisibility_sum` are exact finite norm
   identities on `[-H,H]^2` with `(0,0)` deleted.
4. `nonzeroCollectedFejerL1Norm_le` proves
   `L1 <= 16*(2+log(H/q+1))^2`; the frequency-shell proof has at most `2*q`
   entries per shell and at most two entries in each divisibility fiber.
5. `nonzeroCollectedFejerL2SqNorm_le` and
   `nonzeroCollectedFejerL2Norm_le` prove respectively `L2^2 <= 36/q` and
   `L2 <= 6/sqrt(q)`.
6. `parent_aggregate_boundary_bound` proves the explicit parent error

   ```text
   4*P*B_parent + 8*q^2*P^2/(40*q^3+1).
   ```

7. `successor_aggregate_boundary_bound` proves the explicit successor error

   ```text
   4*P*B_successor + 800*q^2*P^2/(8000*q^3+1).
   ```

   Here each `B` counts visits at both endpoints of the unique active
   half-open cylinder. The sharp vector argument uses total smoothed mass one,
   so the Fejer tail does not acquire an extra factor `q`.
8. `smoothedEnergy_eq_collected_expansion` is the exact finite two-frequency
   expansion. `smoothedEnergy_eq_zeroMode_add_remainder` separates the zero
   mode from every remaining collected pair.
9. `row_energy_defect_le_full_error` displays the zero mode, Fourier remainder,
   both boundary terms, and both rational Fejer tails in one theorem type.
10. `boundary_and_fourier_imply_literal_t14_row` assumes

    ```text
    B_successor + (1/2)*B_parent <= P/(40*q)
    ||rowFourierRemainder ell P|| <= P^2/(10*q)
    ```

    and proves both

    ```text
    QuantitativeSplittingLevel ell P (3281/7281) (1/100)
    rowThreshold ell P (1/100) (3281/7281).
    ```

The second displayed assumption is explicitly hypothetical for the fixed-pi
orbit. No theorem asserts either premise.

## Verification

The workspace cache was initialized using the required pinned package link and
prebuilt build cache. The relevant commands completed successfully:

```text
timeout 900 lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t64-1786052370-r0/theory_artifacts/AggregateFejerCriterion.lean
```

The concluding `#print axioms` output reports exactly `propext`,
`Classical.choice`, and `Quot.sound` for all 15 claimed endpoints. A scan found
no `sorry`, `admit`, `native_decide`, unsafe declaration, or tactic-discovery
placeholder in the delivered Lean file.

Lean file SHA-256:

```text
ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16
```

## Recorded friction

The advisory `flash-prove` call for the root-of-unity helper reached its
15-minute timeout and left scratch files; those files were removed. The helper
was instead proved and compiled directly. No mathematical premise was added as
a workaround.
