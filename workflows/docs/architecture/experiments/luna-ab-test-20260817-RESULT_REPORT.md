# GPT-5.6 Luna max: isolated T191 A/B test

Date: 2026-08-17 UTC

## Result

**Luna at maximum reasoning did not finish this demanding workitem to literal
acceptance in either one-shot arm.** The Sol-guided arm was materially better
and close to acceptance, but still required revision.

| Arm | Treatment | Technical self-gates | Blind Sol verdict | Score |
|---|---|---:|---:|---:|
| A / red | `openai/gpt-5.6-luna`, `variant=max`, no guidance | verifier and hashes pass | `revise` | 61/100 |
| B / blue | same Luna configuration plus a coarse prior Sol guide | verifier and hashes pass | `revise` | 89/100 |

The +28-point difference is meaningful on this workitem. It is not a general
benchmark estimate because this was one real task and one sample per arm.

## Follow-up: Sol-guided repair loop

The preferred 89/100 packet was subsequently put through a real repair loop:

1. a fresh Sol-max session produced a source- and invariant-specific repair
   guide;
2. Luna max rebuilt the packet and its semantic verifier;
3. a fresh Sol-max review scored it 92/100 and found one remaining trust-anchor
   defect;
4. Luna repaired that exact defect in-session from the Sol review;
5. a second fresh Sol-max reviewer reran the gates and an adversarial mutation
   test and returned **`accept`, 100/100, with no defects**.

The decisive final repair pins the authoritative `program.json` and
`knowledge.jsonl` snapshots to expected SHA-256 values before reconstructing
the 188-row ledger. In an isolated test, jointly mutating ordinary source row
T100 and regenerating the ledger is now rejected at the digest gate.

This changes the operational conclusion: **Luna max can complete this hard
workitem inside a Sol-directed, critique-and-repair loop, but did not do so in
one shot.** The loop, not Luna alone, is the demonstrated capable unit.

## What each arm achieved

Both arms correctly:

- rejected F1 at domain admission instead of pretending that an ambient
  Fourier-dimension theorem gives named-point Fourier decay;
- retained two rather than three candidate fingerprints;
- added the standing R1 ordering and the literal Theorem 1(b) convergence
  series;
- preserved the negative-map, zero-survivor, no-successor, fixed-pi, and claim
  discipline constraints;
- produced replayable packets whose own verifier and checksum commands exited
  successfully.

The unaided arm nevertheless failed the central historical-ledger repair. It
mapped workflow `done` status to `accepted`, did not preserve latest result
adjudication or knowledge evidence state, and disagreed with the supplied
snapshots on 14 rows. Its verifier was too shallow to detect that failure.

The guided arm correctly reconstructed all 188 history rows in the blind
review and separated program status, adjudication, failure cause, and evidence
strength. Its remaining defects were bounded but literal:

1. its supposedly full R1 applicability card omitted
   `psi : N -> [0,infinity)`;
2. its verifier did not bind every ledger row back to `program.json` and
   `knowledge.jsonl`, even though the generated ledger itself matched them;
3. `RESULT.json` was omitted from `SHA256SUMS` while the result claimed all
   listed files were checked.

## Interpretation for the architecture

Luna max is capable of substantial execution on a difficult, evidence-heavy
research workitem, but this test does **not** support letting it autonomously
close such items. Coarse Sol guidance transformed a fundamental semantic miss
into three local repair defects. The sensible workflow is therefore:

1. Sol supplies a compact decision guide for demanding or ambiguous items;
2. Luna max performs the artifact-heavy execution;
3. deterministic gates bind outputs to source snapshots rather than checking
   only self-authored markers;
4. a skeptical review/repair step remains mandatory before acceptance.

The test also shows that green self-written gates are weak evidence when the
same worker designs both artifact and verifier.

## Protocol and resource observations

- Real workitem: T191 revision after a prior independent `revise` verdict.
- Both Luna arms received byte-identical base task and input snapshots.
- Arm B alone received the 766-word coarse `GUIDANCE.md` written beforehand by
  `openai/gpt-5.6-sol` at `variant=max`.
- Runs were fresh, sequential sessions in separate directories.
- Blind mapping: red = unaided; blue = Sol-guided. The reviewer was not told
  this mapping.
- Blind reviewer: fresh `openai/gpt-5.6-sol`, `variant=max` session.
- Approximate elapsed model-run times: guidance 99 s; unaided Luna 267 s;
  guided Luna 294 s; blind review 237 s.
- OpenCode trace usage (sum of step receipts): unaided Luna 2,115,407 total
  context tokens, of which 1,986,048 were cache reads; guided Luna 2,350,431,
  of which 2,221,056 were cache reads. These are repeated agent-step context
  receipts, not a clean count of unique prompt text.

The research orchestrator remained inactive, the durable pause guard remained
present, and no result was incorporated into the trusted AllMath graph or
ledger.

## Evidence

- Sol guide: `guidance/GUIDANCE.md`
- Unaided packet: `arm_a/output/`
- Guided packet: `arm_b/output/`
- Blind verdict: `evaluation/VERDICT.json`
- Detailed blind review: `evaluation/REVIEW.md`
- Raw traces: `guidance/run.jsonl`, `arm_a/run.jsonl`, `arm_b/run.jsonl`, and
  `evaluation/run.jsonl`
