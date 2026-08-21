# Pi knowledge base

This directory holds durable research state. It intentionally excludes raw model transcripts, copied sandboxes, and retry logs.

- `verified/`: trust policy and indexes into the canonical Lean source in `../../TheoryLib/`.
- `results/machine-checked/`: concise reports for results accepted by Lean and the axiom audit.
- `results/intermediate/`: useful reductions, experiments, literature notes, and legacy campaign artifacts.
- `results/negative/`: refuted routes and reusable obstructions.
- `workstreams/`: bounded current/restartable lines of work.
- `programs/`: a compact index; program JSON lives with its workstream.
- `state/`: migration and continuation metadata.
- `statements/`: normalized Pi problem statements and variants.
- `handoffs/`: concise review or continuation handoffs.

The proof authority is `TheoryLib/`, not this directory. Reports here describe proof artifacts; they do not replace them.

## External-model integration

`handoffs/external/` is an inbox and immutable provenance layer. Every newly
committed GPT Pro handoff receives an independent semantic and source review.
Accepted conclusions are distilled into the appropriate `results/negative/`,
`results/intermediate/`, `workstreams/`, or `results/machine-checked/` location
with their source commit recorded; they are not left only in the inbox.
Promotion preserves the existing claim label. External work is never upgraded
to `machine-checked` without canonical Lean integration and the complete axiom
gate.
