# Isolated T191 revision test

You are executing one real AllMath workitem, not proposing a plan. Work only
inside the current arm directory. Treat `input/` as immutable evidence and
write every deliverable under `output/`. Do not modify the parent repository,
the operator pause guard, the research ledger, or any knowledge graph.

## Workitem

Revise T191, the source-pinned three-domain negative mechanism map for G28.
The original task is the `T191` entry in `input/program.json`. The previous
artifact packet is in `input/original_artifacts/`; the rejecting independent
review is `input/theory_skeptic_result.json`; and the recorded through-T188
history is available in `input/program.json` and `input/knowledge.jsonl`.

The previous packet passed its integrity replay but was rejected for three
substantive reasons:

1. F1 was presented as belonging to the required named-non-generic-point
   Fourier domain although the cited theorem is only an ambient limsup-set
   Fourier-dimension theorem and supplies no named-point bound.
2. R1 omitted the standing hypothesis `1 <= a_n <= b_n` and did not state the
   convergence condition belonging to Theorem 1(b).
3. The T1--T188 exclusion ledger used generic placeholders and did not give an
   independently auditable accepted/rejected classification and provenance.

Repair those defects literally and conservatively. It is permissible—and may
be more honest—to treat F1 as a source-pinned near miss rejected at domain
admission and to reduce the retained-fingerprint count; the original task says
"at most three", not exactly three. Do not invent a named-point theorem. The
survey must still state that exactly three domains were searched. Derive ledger
classifications and provenance from the supplied recorded files; distinguish
missing/failed/sketch/accepted/rejected states and do not manufacture status.
Do not use T189 or T190 as evidence or compare against their artifacts.

Preserve all other literal T191 constraints: at most ten pinned primary
source/theorem tuples; at most three retained source-, theorem-, and
mechanism-distinct fingerprints; exact source locators and full applicability
cards for every retained candidate; one explicit quantitative rejection and
one unproved transfer hypothesis for every retained candidate; one batch
verdict; at most one successor, and none when there are zero survivors. Keep
finite computation labelled `experiment`, calculations `proof sketch`, and
source statements `literature-checked` only when the delivered pinned source
supports them. Make no claim of progress on pi, A1, C1, or C2.

## Required output packet

Create under `output/`:

- `REPORT.md`
- `SOURCE_LEDGER.csv`
- `EXCLUSION_LEDGER.csv`
- `verify_t191.py`
- `replay_output.txt`, produced by actually running the verifier
- `SHA256SUMS`
- `RESULT.json`

Copy into `output/` any pinned source derivatives or PDFs that your verifier
or report treats as delivered evidence. `RESULT.json` must contain:

```json
{
  "workitem": "T191",
  "completed": true,
  "self_verdict": "accept|revise|blocked",
  "summary": "...",
  "files": ["..."],
  "checks": [{"command": "...", "exit_code": 0, "result": "..."}],
  "known_limitations": ["..."]
}
```

`completed` means the requested attempt and packet are complete, not that the
mathematics was accepted. The verifier must test substantive repaired
invariants, not merely file existence. Run it from `output/` and preserve its
actual stdout. Finish only after inspecting the packet for consistency.

