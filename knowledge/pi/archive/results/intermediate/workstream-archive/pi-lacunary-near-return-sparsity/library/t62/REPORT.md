# T62: closed decimal expansion and predecessor-depth regrouping

Status: `machine-checked`

## Scope and source pin

The canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with verified SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

T62 proves finite coefficient identities only. It does not address the open
fixed-pi quantifiers in the canonical question.

The Lean module explicitly imports the kernel-checked T55 and T61 modules. It
does not import T58 or use a T58 statement as a premise.

## Normalized finite statement

Parameters `beta : Real` and `ell R : Nat` are unrestricted. The public closed
coefficient theorem additionally assumes `1 <= u`; this avoids the conventional
zero value of `padicValNat`. No positivity assumption on `ell` or `R` is hidden:
their degenerate cases are represented by empty finite ranges.

Define

```text
nu_10(u) = padicValNat 10 u,
w_R(v)   = 1 - v/R,
E_a(u)   = w_R(u/10^a)
           * phase((u/10^a - u), beta*10^ell).
```

The theorem `orbitCoefficient_eq_closed_decimal_expansion` proves directly
from T55's recursive definition that

```text
orbitCoefficient(beta,ell,R,u)
  = sum_{0 <= a <= nu_10(u)} E_a(u).
```

The index set in the Lean type is literally
`range (decimalValuation u + 1)`. The signed phase frequency
`(u / 10^a : Int) - u` remains visible.

## Exact predecessor remainder

The theorem `predecessorRemainder_eq_frequency_depth_block_sum` first expands
T61's exact remainder without regrouping:

```text
sum_{(R-1)/10 < u <= R-1}
  sum_{1 <= a <= nu_10(u)}
    sum_{0 <= j < ell}
      w_R(u/10^a)
      * phase((u/10^a)*10^ell - u*10^j, beta).
```

Thus the terminal-shell lower endpoint, terminal endpoint `R-1`, positive
predecessor depths, block endpoint, minus sign, and Fourier cutoff all occur in
the theorem type. Distinct triples `(u,a,j)` remain distinct even when their
integer phase frequencies coincide.

## Finite bijection and depth order

`predecessorLabels` uses source order `(u,(a,j))` and `depthFirstLabels` uses
depth order `(a,(u,j))`, both inside the explicit finite box

```text
range R x (range R x range ell).
```

`predecessorDepthEquiv` is the coordinate permutation

```text
(u,(a,j)) <-> (a,(u,j)).
```

The public theorems `predecessorDepthEquiv_apply` and
`predecessorDepthEquiv_bijective` expose its action and bijectivity. The final
theorem `predecessorRemainder_eq_literal_depth_regrouping` uses this equivalence
and states the remainder with depth outermost:

```text
sum_{1 <= a <= R-1}
  sum_{(R-1)/10 < u <= R-1, a <= nu_10(u)}
    sum_{0 <= j < ell} ... .
```

The Lean type represents the middle condition by filtering the literal
terminal shell with `a <= decimalValuation u`. No quotient, image sum, or
frequency deduplication is used.

## Verification

The module was compiled with:

```text
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t62-1786046596-r0/theory_artifacts/ClosedExpansionPredecessorRegrouping.lean
```

All printed public claims depend only on the allowed axioms `propext`,
`Classical.choice`, and `Quot.sound`. The delivered module contains no `sorry`,
`admit`, `native_decide`, new axiom, unsafe declaration, or provisional search
tactic.

## Explicit nonclaims

This artifact makes no covariance, FSFS, adjacent-compatibility, fixed-pi,
C1, or C2 claim. It supplies only a machine-checked finite phase target for
later work on G11.
