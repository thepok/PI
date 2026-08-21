# T37 replay

`ArtificialStreamObstruction.lean` is a machine-checked formalization of an
artificial-stream A14 sibling of the local canonical question. It makes no C2,
canonical A1, or claim about pi.

The module formalizes T35's staged mechanism using exhaustive repeated decimal
seeds in place of the note's unformalized de Bruijn cycles. The stream and all
counting, leakage, tangent, and no-original-branch conclusions are proved for
that explicit replacement construction.

The canonical statement is `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
It was formulated locally and has no original source URL. Its pinned SHA-256 is:

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

From the workspace root, with the pinned mathlib package link installed, run:

```sh
lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t37-1784872477-r0/theory_artifacts/ArtificialStreamObstruction.lean
```

The file prints the axioms of the principal declarations. The permitted output
contains only `propext`, `Classical.choice`, and `Quot.sound`.
