# Next Evolution of AllMath

## Objective

Reduce token consumption and frontier-model usage without lowering mathematical reliability. The system should spend expensive reasoning only where a wrong decision would cause large downstream waste: research-direction selection, genuinely hard proof steps, conflict resolution, and final review of substantive claims.

The implemented capability ladder is now explicit rather than job-title based:
`low = Luna`, `medium = Terra`, and `high = Sol`. Low means mechanical
transformation, replay, formatting, or compiler-guided iteration; medium means
execution under an already bounded contract; high means new direction choice,
an unresolved hard lemma, or semantic acceptance. Deterministic gates run
before every model acceptance stage. A pinned Lean-verifier delivery that
passes the isolated kernel build and exact axiom allowlist stops there: another
LLM cannot improve proof validity. Arbitrary formalizations still require a
semantic statement-alignment review, because Lean proves the encoded theorem,
not that the theorem matches the intended problem or is novel.

The intended pipeline is:

```text
Terra candidate generation
    -> deterministic deduplication and targeted retrieval
    -> Sol direction decision
    -> Terra-guided execution
    -> deterministic verification
    -> conditional independent Sol review
```

This document did not itself authorize a restart. The later operator goal authorizes only the controlled three-workitem deployment described below.

## Implementation status (2026-08-17)

The architecture is implemented behind the durable operator pause guard. The canonical ledger database contains immutable snapshots of all 14 theory programs, including mathematical `revise` as well as `reject` outcomes; retrieval emits bounded status-preserving evidence packets with stable block hashes. Reviewed theory outcomes are projected back as immutable result events that create, strengthen, or weaken mechanism-linked obstructions without creating trusted proof receipts.

Directors now run as two explicit stages: Terra preparation followed by Sol decision. Theory builders and broad scouts default to Terra; a third attempt is an explicit named-gap Sol escalation after two Terra attempts. Fixed-π and substantive informal/source reviews remain Sol, while routine non-π artifact review can use Terra after deterministic gates. Workflow telemetry separately records execution/review input, output, reasoning, cache-read, and cache-write tokens plus retrieval size, routing reason, verdict, and claim boundary.

A cost-optimized bounded-repair lane is now implemented without changing the
trusted review boundary. When a prior independent review has (a) accepted the
deterministic gate, (b) returned `revise` for a nonmathematical pipeline or
environmental defect, and (c) left an artifact-bearing packet, that review is
reused directly as the repair contract and Luna performs only the retry
execution. Fresh work, mathematical objections, failed gates, and missing
artifacts remain on Terra/Sol. Fixed-π and substantive review still routes to
a fresh Sol session. This lane is dormant while the operator pause is active.

Deployment requires the passing shadow report at `work/architecture/NEXT_EVOLUTION_SHADOW.json` and the controlled three-workitem trial. The trial file hard-caps dispatch; after the third incorporated item the system is paused again for audit.

## Diagnosis

The main inefficiency is not merely the number of expensive agents. It is repeated ingestion of oversized program histories. Recent director microsteps repeatedly processed roughly 167k cached context tokens. Provider-side prompt caching can lower monetary cost and latency, but it may not lower quota or token-budget consumption. Caching therefore cannot replace context reduction.

The current pattern also spends frontier reasoning on separable activities: orienting, strategizing, falsifying, formatting a schema-valid result, artifact bookkeeping, source extraction, and routine review. Much of this can be deterministic or handled by a cheaper model once a precise research contract exists.

## Hierarchical execution model

| Level | Default mechanism | Responsibilities |
|---|---|---|
| L0 | Deterministic code | Scheduling, hashes, schemas, dependency checks, replay, Lean gates, source inventories, exact duplicate detection, token accounting |
| L1 | `openai/gpt-5.6-terra` | Literature extraction, broad candidate generation, computation, experiments, Lean iteration, comparison tables, artifact packaging, routine repairs |
| L1R | `openai/gpt-5.6-luna` | Bounded artifact repair only after a passed deterministic gate and an independent nonmathematical `revise`; no new direction, theorem, source mechanism, or claim status |
| L2 | `openai/gpt-5.6-sol` on demand | Direction selection, difficult proof ideas, novel mechanism design, conflicting evidence, repeated executor failure |
| L3 | Independent `openai/gpt-5.6-sol` | Skeptical review only for substantive mathematical claims, difficult informal arguments, or claim-status upgrades |

Routing should be based on uncertainty and consequence, not a rigid job title. A proof executor may need Sol for one hard lemma and Terra for the rest. Conversely, generic brainstorming does not deserve Sol merely because it is called direction setting.

## Division of reasoning

### Candidate generation

Terra should cheaply produce a wide but bounded set of candidate directions. Each candidate must include a mechanism fingerprint, relevant prior items, a cheap falsification test, expected payoff, and a reason it is not a renamed known obstruction.

### Direction choice

Sol receives only the best three to five candidates plus their evidence packets. It ranks, attacks, and selects at most one bounded next task. Sol is used here because a poor choice can waste many execution hours.

### Execution

Terra performs source retrieval, calculations, proof scaffolding, experiment construction, and artifact preparation under the exact Sol-authored contract. Pinned-template Lean proof attempts use Luna because independent kernel compilation and the axiom audit—not the proposal model—decide validity. Ordinary theory construction runs at Terra-medium; only a named hard gap escalates to Sol-high. It escalates individual hard parts rather than handing the entire task back to Sol.

For a closed repair contract, do not pay for a second director interpretation.
The existing independent review is injected verbatim as bounded cumulative
feedback. Luna may execute that repair at the workflow's requested reasoning
level, but only after the prior deterministic gate passed and the defect was
classified as nonmathematical. A mathematical objection is never downgraded to
this lane. The repaired artifact returns through the unchanged independent
review route.

### Review

Every delivery first passes deterministic verification and a Terra completeness review. Independent Sol review is triggered only when mathematical judgment remains material.

## Context and retrieval design

Agents should not receive the entire theory program or all prior T-items. Each prompt should contain only:

- the exact task and acceptance condition;
- the canonical statement hash and path;
- five to ten relevant result fingerprints;
- named obstructions that must be addressed;
- paths and hashes for artifacts available on demand;
- the current claim-status boundary;
- a small run-specific delta describing what changed.

Each accepted result should have a compact structured fingerprint:

```text
id, claim, claim_status, mechanism, assumptions, quantitative_range,
dependencies, obstructions, source_pins, verified_artifacts,
conflicts, applicability_boundary
```

The full report remains the authoritative artifact on disk. Prompts carry the fingerprint and path, not a pasted copy. An agent can request additional artifacts when it identifies a specific missing premise.

Retrieval should combine:

1. explicit dependency traversal;
2. mechanism/fingerprint similarity;
3. named comparison requirements;
4. obstruction and contradiction links;
5. recency only as a weak final signal.

Every retrieved item must retain its actual status. A sketch, experiment, or observation must never be silently promoted because a summary sounds authoritative.

## Unified dead-end and obstruction memory

Negative knowledge needs the same first-class treatment as successful theorems. Today it is split across task outcomes, `program.json`, skeptic prose, accepted negative reports, parked agenda items, and a bounded prompt-only obstruction view. This loses semantics: an accepted proof that a method cannot work may look like an ordinary positive result, while a rejected artifact may reflect only a bad citation or malformed delivery.

Do not create another parallel JSON database. Use the proof ledger as the canonical index, its append-only evidence and artifact tables as provenance, and the existing theory library as immutable payload storage. Project the relevant compact view into prompts.

### Canonical obstruction node

Create one ledger node per normalized mathematical dead end:

```text
obstruction:<program>:<mechanism-fingerprint>
```

Attach a schema-validated `obstruction_v1` annotation containing:

```json
{
  "mechanism": "fractional deletion variance proxy",
  "attempted_claim": "the proxy is measurable after deleting one digit",
  "failure_kind": "certificate_failure",
  "exact_failure": "the proxy still depends on the deleted coordinate",
  "scope": {
    "problem": "local:pi-lacunary-near-return-sparsity",
    "model": "iid decimal blocks",
    "quantifiers": "every N >= 2 and m >= 1"
  },
  "evidence_status": "proof sketch",
  "minimal_separator": "all-zero word with a one-digit flip",
  "blocks": ["fractional-deletion route to gamma < 3"],
  "does_not_block": ["conditional resampling", "fixed-pi methods"],
  "reopen_condition": "a genuinely dropped-coordinate-measurable proxy or a changed concentration theorem",
  "mechanism_fingerprint": "content-addressed normalized fingerprint"
}
```

The annotation is an index, not evidence. Every substantive field must point through an append-only ledger evidence row to a content-addressed report, Lean theorem, replay, counterexample, or pinned source. The artifact remains authoritative.

### Failure taxonomy

Store failure classes separately so operational noise cannot masquerade as mathematical knowledge:

| Class | Meaning | Research obstruction? |
|---|---|---|
| `refutation` | The attempted mathematical statement is false | Yes |
| `certificate_failure` | A proposed sufficient method or proxy fails; the target may remain true | Yes, narrowly scoped |
| `scale_mismatch` | A valid theorem cannot reach the required parameter regime | Yes, with exact ranges |
| `applicability_failure` | A theorem premise or transfer condition is absent | Yes, with the missing premise |
| `duplicate` | The mechanism is already represented elsewhere | No new mathematics; link to the canonical node |
| `pipeline` | Schema, path, packaging, or orchestration failure | No; operational telemetry only |
| `environmental` | Network, resource, or unavailable-source failure | No; retry metadata only |

Never infer this class solely from `accept`, `revise`, or `reject`. The mathematical content and the artifact-review verdict are orthogonal. An accepted negative theorem creates or strengthens an obstruction; a rejected report with a locator typo does not.

### Typed graph edges

Connect tasks, claims, and obstructions with explicit edges:

```text
task --tests--> mechanism
task --produces--> obstruction
obstruction --refutes--> claim
obstruction --blocks--> mechanism-or-agenda-branch
obstruction --requires_missing--> premise
obstruction --specializes--> broader-obstruction
obstruction --supersedes--> weaker-obstruction
new-task --reopens--> obstruction
new-evidence --weakens|strengthens--> obstruction
```

Use `refutes` only when the target statement itself is false. Use `blocks` or `certificate_failure` when only a proposed proof route has failed. This prevents the recurring error of interpreting failure of a sufficient estimate as evidence against the underlying conjecture.

### Ingestion rules

After every reviewed task, a deterministic projector reads the final review plus explicit result metadata and performs exactly one of:

1. create a new obstruction node;
2. attach stronger evidence to an existing obstruction;
3. link the attempt as a duplicate of an existing node;
4. record only operational failure telemetry;
5. record no dead end because the result was positive and created no obstruction.

The projector may propose classification, but mathematical `refutation`, scope expansion, or branch-closing status requires an independent mathematical review. Pipeline code must never promote prose automatically into a trusted obstruction.

Normalize the mechanism fingerprint from mathematical objects and ranges, not generic task wording. Include the target statistic, proof technique, parameter regime, needed premise, and failure mode. This is stronger than token overlap and catches renamed retries without conflating nearby but genuinely distinct methods.

### Reopening and lifecycle

An obstruction has lifecycle state `active`, `weakened`, `superseded`, or `retracted`; history is append-only. It is never deleted.

A proposed task overlapping an active obstruction is rejected unless it provides:

- the exact obstruction ID;
- a changed premise, theorem, parameter range, or mechanism;
- evidence that the change is material;
- a cheap discriminator that would fail before expensive execution if the route is still blocked.

The Director sees all matching active obstructions, not merely the latest fixed-size tail. Retrieval ranks them by mechanism and dependency relevance rather than recency. Superseded or retracted records remain available for audit but are omitted from normal prompts unless the new task depends on their history.

### Compact prompt card

The prompt projection for one obstruction should normally fit within a few hundred tokens:

```text
ID / mechanism / exact failed implication / scope / evidence status /
minimal separator / blocks / does-not-block / reopen condition /
artifact hashes and paths
```

This replaces repeated injection of entire negative reports while preserving on-demand access to exact evidence.

### Migration of existing π research

Perform a one-time offline migration while the orchestrator remains paused:

1. scan all π-program results, accepted library reports, parked items, and skeptic notes;
2. separate mathematical negatives from pipeline and environmental failures;
3. propose normalized obstruction records and mechanism clusters;
4. have a Sol review only the ambiguous classifications and scope boundaries;
5. write ledger nodes, typed edges, annotations, and evidence links transactionally;
6. verify that known examples such as coefficient-only stopping rules, sparse-ray dilution, irrationality-scale mismatch, representation/modulus barriers, and T187's fractional-deletion failure are retrieved for the appropriate candidate tasks;
7. compare historical Director decisions with and without the new memory to measure duplicate suppression and context savings.

Migration must not rewrite old artifacts, verdicts, or claim labels. It adds a normalized graph projection over immutable historical evidence.

## Cache-aware prompt construction

Prompt layout should maximize stable prefixes:

1. immutable system and safety contract;
2. stable workflow instructions and schema;
3. stable compact program brief;
4. retrieved artifact manifest sorted deterministically;
5. small run-specific task delta at the end.

Content-address all stable prompt blocks and record their hashes. Do not regenerate semantically identical blocks with changed timestamps, ordering, whitespace, or prose. Cache misses should be observable in telemetry.

Caching is a secondary optimization. The primary optimization remains omitting irrelevant context.

## Director redesign

Replace the four large frontier microsteps (`orient`, `strategize`, `falsify`, `deliver`) with at most two stages:

1. **Terra preparation:** construct a compact evidence packet, generate candidates, detect duplicates, and mark known obstructions.
2. **Sol decision:** adversarially select or reject candidates and write one schema-valid agenda item.

A second Sol repair call is allowed only when the first output is schema-invalid, internally contradictory, demonstrably duplicative, or missing required evidence. Formatting-only repair should be deterministic or Terra-based.

The director should run on material events, not merely on ticks: accepted/rejected result, new source evidence, changed operator direction, exhausted agenda, or a real blocker.

## Escalation policy

Escalate from Terra to Sol when at least one condition holds:

- a proof attempt exposes a named mathematical gap rather than a tooling issue;
- two materially distinct Terra attempts fail;
- primary sources conflict or applicability is ambiguous;
- the result would change a goal, conjecture, or claim status;
- a candidate claims fixed-constant or fixed-\(\pi\) progress;
- selecting the wrong route would consume substantial compute or researcher time;
- deterministic and Terra reviews disagree on a substantive point.

Do not escalate for schema repair, file copying, citation-table assembly, routine Lean errors, raw computation, or verbose restatement of known context.

## Review policy

The review ladder is:

```text
schema/hash/replay gates
    -> Lean and axiom gate when applicable (stop if this exactly binds acceptance)
    -> Terra completeness/source/statement packet when semantic judgment remains
    -> one Sol mathematical skeptic when triggered
```

Sol review is mandatory for:

- candidate or verified resolution claims;
- new fixed-\(\pi\) implications;
- a new theorem whose proof is not fully kernel checked;
- source-dependent novelty or applicability judgments;
- an obstruction that would close a major research branch.

Routine negative experiments, formatting repairs, and related-model results with mechanically checkable proofs can stop before Sol unless sampling or conflict detection triggers escalation.

## Token budgets and telemetry

Initial budget targets, to be calibrated from actual traces:

| Activity | Target input | Target output | Frontier calls |
|---|---:|---:|---:|
| Sol direction decision | 20k–30k | 4k–6k | 1 normally, 2 maximum |
| Sol hard-lemma consultation | 10k–20k | 3k–5k | 1 per named gap |
| Sol skeptical review | 20k–40k | 4k–8k | 1 |
| Terra execution turn | retrieved context only | artifact-first | bounded by task |

Exceeding a context budget requires a machine-readable reason naming the missing information. The scheduler should record:

- uncached, cached, and output tokens per phase;
- context bytes and retrieved item count;
- cache-hit ratio for stable blocks;
- model and reasoning level;
- retries and escalation reason;
- accepted useful result versus rejected/duplicate result;
- tokens per accepted result and per material mathematical finding.

Optimize for accepted useful work per frontier token, not raw task throughput.

### Measured bounded-repair result

The isolated T174 trial on 2026-08-17 used a fresh unresolved workitem rather
than replaying T191. It reused the existing Sol rejection as guidance, ran one
Luna-high executor, deterministic replay/hash gates, and exactly one fresh
Sol-max final source audit. The final reviewer returned `accept`, 100/100.

At the local OpenCode price table and observed step receipts:

| Phase | Estimated cost |
|---|---:|
| Luna-high repair | $0.105 |
| Sol-max independent review | $1.085 |
| Total | $1.190 |

The same observed executor tokens priced as Sol would have cost $2.634, making
the same-token all-Sol route $3.719. The measured saving was therefore about
$2.529 or 68%, with the final quality gate unchanged. This is one fresh-item
validation, not yet a population estimate. The report and traces are under
`work/architecture/cost-optimized-quality-trial-20260817/`.

The earlier T191 experiment showed the complementary failure mode: Luna
execution was cheap, but repeated Sol planning/review calls dominated 96.8% of
the accepted path's estimated cost. Consequently, a review result must double
as the next repair contract; no separate Sol "explain the review" call is
allowed. A second Sol call is justified only as a fresh acceptance gate after
the repaired packet passes deterministic checks.

## Artifact-first communication

Nested agents should write results to files and return a small manifest. Avoid returning long reports through orchestration messages and then injecting those reports into subsequent prompts.

A normal agent response should contain only:

```text
status, verdict, artifact paths and hashes, named blocker,
claim-status impact, proposed escalation (if any)
```

The next agent reads only the specifically required files. This preserves exact evidence while preventing conversational history from becoming the database.

## Expected savings

These are hypotheses to measure, not promises, and they overlap rather than add directly:

- delta retrieval instead of full-ledger prompts: approximately 60–85% less input context;
- one Sol director decision instead of four large Sol microsteps: approximately 50–75% less director usage;
- Terra execution and pre-review: approximately 70–90% fewer frontier tokens on routine items;
- conditional rather than universal Sol review: approximately 30–60% less frontier review usage.

Result quality must remain the controlling metric. Any saving that increases duplicate work, false mathematical claims, or missed proof gaps is a regression.

## Safe rollout

### Phase 0 — Measure the baseline

Replay recent records such as T183–T188 without restarting research. Measure context composition, cached versus uncached tokens, per-microstep duplication, model usage, retries, and result value.

### Phase 1 — Compact evidence packets

Introduce structured result fingerprints and targeted retrieval while keeping the existing model policy. Compare old and compact prompts on the same historical decisions.

Acceptance: the compact packet preserves every source, dependency, obstruction, and claim-status fact needed to reproduce the prior decision.

### Phase 2 — Collapse the director

Move preparation to Terra and retain one Sol decision pass. Shadow-run the new director on historical events and compare selected tasks, duplicate rejection, and mathematical scope discipline.

### Phase 3 — Tier execution and review

Default execution to Terra, add named-gap Sol escalation, and place deterministic/Terra gates before conditional Sol review.

### Phase 4 — Controlled live trial

After explicit operator authorization, run a small capped trial. Compare frontier tokens, total tokens, wall time, duplicate rate, reviewer reversals, and accepted-result quality against the baseline. Roll back if quality deteriorates.

## Non-negotiable invariants

- No model tier may weaken the claim vocabulary or verification gates.
- Luna repair routing requires an artifact-bearing prior attempt, a passed
  deterministic gate, and an independent nonmathematical `revise`; otherwise
  it fails closed to Terra/Sol.
- The independent review model and acceptance contract are unchanged by a
  cheaper executor route.
- A cheap-model report is never evidence by itself.
- Retrieval summaries never replace authoritative source artifacts.
- Fixed-\(\pi\) claims always receive independent frontier review.
- Failed cheap attempts are bounded; the system must escalate or close the route rather than loop.
- The operator pause guard remains authoritative and cannot be bypassed by the scheduler, goal continuation, or model output.
- The system must not restart until Marcel explicitly requests resumption.

## Recommended target architecture

```text
Material event
  -> deterministic state delta and dependency retrieval
  -> Terra candidate packet
  -> one Sol decision
  -> Terra artifact-producing execution
  -> deterministic gates
  -> Terra completeness audit
  -> conditional independent Sol skeptic
  -> ledger incorporation and compact fingerprint
```

This architecture preserves frontier judgment for the hardest and most consequential work while making execution, bookkeeping, and evidence movement substantially cheaper.

## Implemented and live-validated (2026-08-16)

The architecture above is now implemented rather than merely proposed. The canonical graph contains migrated theory-program results, UltraPi intake, typed obstruction lifecycle, provenance pins, and append-only corrections. Builders receive deterministic packets capped at 10 records / 30 KB; directors use Terra preparation plus one Sol decision; ordinary execution uses Terra; fixed-pi work receives Sol review; post-review results are projected into the graph; and phase telemetry is recovered from actual workflow traces.

Controlled trial v3 dispatched exactly three real records and then paused. It exercised a pipeline-only retry, a rejected mathematical/completeness result, and an accepted repaired result. The run also exposed and repaired cumulative-retry memory, owned control cleanup, failed-director context commit ordering, and negated unfinished-item references. Full details and measured token/cache totals are in `work/architecture/NEXT_EVOLUTION_TRIAL_20260816_V3.md`.

The measured cache-read share was 93.19%, but total provider tokens remained high because long stable blocks still count in provider totals. The next efficiency target is therefore not another routing layer: it is reducing the stable operator/program block itself or supplying it by durable server-side cache/reference without weakening source and claim boundaries.
