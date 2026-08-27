# T73: many-child two-scale resonance obstruction

Claim label: **machine-checked** for the declarations in
`ManyChildResonance.lean`, subject to the recorded direct Lean compilation and
allowed-axiom output. This is only a necessary obstruction.

## Canonical statement and terminology

The immutable statement at
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt` was hash-checked as

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

Its canonical A1 is

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1,
  A * n * Q_pi(n,N) <= N^2,
```

where `Q_pi` counts ordered pairs and includes the diagonal. The current
agenda's conjecture identifier C1 denotes this same near-return statement.
The source's sibling A10 instead counts equal length-`n` decimal factors and
notes that A10 was called C1 in the parent program. T73 uses the literal
negation of canonical A1/current-C1 and never substitutes A10/parent-C1.

## Checked declarations

- `goodMiddleShifts` is the inclusive finite set `B <= s <= M-R`, excluding
  `F`, for which
  `((M-s) cast to real)/(8*D^2) < re(autocorrelation z M s)`.
- `mem_goodMiddleShifts_iff` unfolds the complete range, exclusion, and strict
  threshold.
- `goodMiddleShift_child_resonance` exposes the endpoint condition
  `R <= M-s`, the real-part threshold, and the norm threshold.
- `goodMiddleShifts_card_lower` proves

  ```text
  3*M/(8*D^2) - 1/2 - (B + |F| + R) < |goodMiddleShifts|.
  ```

  Here `1/2` is the diagonal term from the exact squared-sum identity, `B` is
  the short-shift loss, `|F|` is the forbidden-shift loss, and `R` is the
  terminal-shift loss. No floor or ceiling is hidden in this real-valued bound.
- `autocorrelation_geometricPhase_eq` identifies each selected
  autocorrelation with the child coefficient multiplied by `10^s-1`.
- `goodGeometricMiddleShift_child_resonance` gives the literal child phase sum.
- `manyChildLengthThreshold D children R =
  8*D^2*(children+R+3)` is an explicit sufficient parent length; it uses no
  floor or ceiling.
- `literal_not_canonical_C1_implies_many_child_two_scale_resonances` keeps the
  fully unfolded canonical quantifiers. For every requested positive child
  count and residual length, it retains the T13 parent resonance and produces
  at least that many simultaneous legal child resonances.

All declarations are public and lie in the fresh namespace
`DecimalFactorComplexity.ManyChildResonanceT73`.

## Verification

The module imports the accumulated kernel-checked T10 and T13 modules. It was
compiled directly with:

```text
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t73-1786070815-r0/theory_artifacts/ManyChildResonance.lean
```

The six theorem axiom reports contain exactly the allowed axioms
`propext`, `Classical.choice`, and `Quot.sound`. The delivered module contains
no `sorry`, `admit`, `native_decide`, new axiom, unsafe declaration, or tactic
query command.

## Scope exclusions

T73 does not prove that canonical A1/current-C1 fails. It proves no pairwise
compatibility among the selected children, cancellation estimate,
distinct-coefficient bound, canonical A1/current-C1, A10/parent-C1, C2,
normality, pair correlation, or decimal-complexity conclusion.
