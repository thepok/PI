# T14 replay

`CoherentSuccessorSplitting.lean` extends the accepted `TheoryLib` modules T9
and T12. It is intentionally not a standalone replacement for those modules.
Replay it from the pinned AllMath project root so Lean can resolve the accepted
library sources:

```sh
rm -rf .lake/packages
mkdir -p .lake
ln -sfn /opt/allmath-lean/.lake/packages .lake/packages
timeout 600 lake build TheoryLib
lake env lean \
  removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t14-1784794818-r1/theory_artifacts/CoherentSuccessorSplitting.lean
```

Before replay, verify the canonical statement and direct accepted dependencies:

```sh
sha256sum -c \
  removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t14-1784794818-r1/theory_artifacts/DEPENDENCIES.sha256
```

The Lean file ends with `#print axioms` commands for every claimed endpoint.
The allowed output is exactly `propext`, `Classical.choice`, and `Quot.sound`.
