# Strict Lean research microloop

Use this workflow for long-horizon theorem-proving evaluations.  It measures
inspectable progress, not the amount of hidden reasoning produced.

1. Start from an exact theorem statement and a dated source/provenance note.
2. Create the candidate file before doing broad library research.
3. Let the controller run the real Lean compiler.
4. Feed only the first relevant compiler error back to the model.
5. In one model turn, research only that error, make the smallest useful edit,
   and stop.  The controller compiles again.
6. Reject a turn that neither changes the candidate nor produces a precise
   blocker.  Do not reward orientation text as progress.
7. Preserve every prompt, JSONL trace, candidate revision, and compiler log
   under a unique run identifier.
8. After compilation succeeds, run the forbidden-token scan and the isolated
   axiom gate.  Compilation alone is not a research-status promotion.

Operational limits used for the Ox Alpha evaluation:

- first candidate: 120 seconds;
- first compiler invocation: 240 seconds;
- one compiler error per repair turn;
- no repeated broad Mathlib search;
- 240 seconds per repair turn by default;
- provider routes work on separate candidate copies;
- a theorem is `machine-checked` only after the independent gate succeeds.

