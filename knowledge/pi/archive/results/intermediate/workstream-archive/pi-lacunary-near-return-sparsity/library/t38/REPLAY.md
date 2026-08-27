# T38 replay

Canonical statement SHA-256:

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

From the record directory inside the pinned AllMath workspace, compile the
delivered module with:

```sh
lake env lean theory_artifacts/FixedStratumFejerSpike.lean
```

The terminal `#print axioms` commands audit the claimed declarations.  Their
only dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

`FSFS` and `ExpandedFSFS` are definitions of conditional hypotheses.  The
module does not construct either predicate for `Real.pi`, assert unconditional
adjacent compatibility, or prove canonical A1.
