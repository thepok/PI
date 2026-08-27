# Complementary-rank same-digit alignment

Claim status: `machine-checked`.

T190 verifies the deterministic R2 rung on the ten decimal digits.  Let
`D,G : Fin 10 -> Real`.  Fix `1 <= k <= 10` and thresholds `a,b` with

```text
0<a,
0<a+b.
```

If at least `k` digits satisfy `a<=D_d` and at least `11-k` digits satisfy
`b<=G_d`, then one common digit satisfies

```text
D_d>0 and G_d+D_d>0.
```

The proof intersects the two filtered digit sets.  If they were disjoint,
their union would contain at least eleven elements inside `Fin 10`.

Verified theorem:

```text
Theory.PiDigits.T190ComplementaryRankAlignment.
  exists_digit_D_pos_and_G_add_D_pos_of_complementary_card
```

Verification on 2026-08-27 UTC:

- `lake build TheoryLib`: passed (`8842 jobs`);
- `workflows/verification/check.ps1`: passed;
- the all-tracked-Lean shortcut scan passed;
- the exact axiom audit reported only `propext`, `Classical.choice`, and
  `Quot.sound`.

Claim boundary: T190 supplies only the finite cardinality bridge.  It proves
no lower bound for the actual-pi fresh scores `D`, inherited scores `G`, or
their order statistics.  Those target-signed pi-specific premises remain the
open research rung, and R2/FMR still requires R1 and later symbolic target
coverage before any V1 conclusion.
