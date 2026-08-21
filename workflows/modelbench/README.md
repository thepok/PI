# modelbench — role-fit capability benchmark

Judges candidate models on the dimensions the theory track staffs, so role
assignments (builder / skeptic / referee / director / formulator) rest on
measured capability instead of vibes.

## Dimensions and grading

| dimension | tests | graded by |
|---|---|---|
| lean_prove | prove given theorem signatures against mathlib | network-free pod gate: compile + `#print axioms` allowlist (objective) |
| lean_formalize | encode English statements as Lean Props | pod gate compile (objective) |
| refutation | find the uniquely fatal step in a plausible wrong proof | answer key (objective) |
| review | ACCEPT/REJECT vs a binding acceptance criterion, traps on both sides | ground-truth key (objective) |
| honesty | flag the unverifiable, answer the knowable | fixed grader model + author rubric (semi-objective, grader recorded) |
| schema | constrained JSON emission | jsonschema validation (objective) |

Generic benchmark tasks live in `tasks/benchmark/`; Pi task packs live in
`tasks/pi/`. Disposable run output goes to `workflows/state/runs/` by default.
Only compact conclusions and accepted artifacts should be promoted into
`knowledge/pi/` or `TheoryLib/`.

## Running

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --models fable,sol,terra,luna,m3 --concurrency 4
# report only:
.venv/bin/python workflows/modelbench/runner.py \
  --report workflows/state/runs/benchmark/results.jsonl
```

Models are invoked one-shot in a disposable empty directory (`claude -p` for
Fable, `opencode run -m <id>` for the rest). Honesty grading uses
`openai/gpt-5.6-terra` with the task author's rubric; the grader never knows
which model produced a response.

Ox calls are sandbox-required. A full two-provider wave uses:

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --models ox,oxzen --concurrency 14 --sandbox \
  --sandbox-image localhost/allmath-research:latest \
  --sandbox-cpus 2 --sandbox-memory 4g --sandbox-timeout-s 5400 \
  --tasks-dir <task-bank> --out <result-dir> --cancel-file <unique-marker>
```

Each call gets a Podman container and a private copied task workspace. The
only writable mounts are the temporary sandbox run record, that copy, ephemeral
OpenCode data, and an ephemeral `/root/.cache`; the canonical checkout and host
HOME are not mounted. Network remains enabled for the model API. Native free
Ox (`oxzen`) receives no auth file. OpenRouter Ox receives a transient
`auth.json` containing only the `openrouter` entry; unrelated OpenAI and MiniMax
credentials never enter the pod. Config and the model catalog remain read-only.
The root filesystem is read-only, all Linux capabilities are dropped,
no-new-privileges is set, process count is capped at 512, and `/tmp` is a
bounded tmpfs.
Each pod's PID 1 also watches a per-call heartbeat in its private run mount.
If the owning runner crashes or is killed before cidfile cleanup, the stale
lease terminates that pod's child (TERM, then KILL after five seconds) and
exits, allowing `--rm` to remove the container. Graceful cancellation still
uses the exact cidfile immediately and never scans or signals sibling pods.
Lean tasks use the image-pinned `/opt/allmath-prebuilt` snapshot/build via
links inside the copied task workspace. Only the grading contract's declared
artifact and `REPORT.md` return to the result directory; model-created links
are rejected. Host-captured JSONL remains the authoritative trace.

The runner enforces provider-specific ceilings both within one process and
across concurrent refill processes: native OpenCode Ox (`oxzen`) has 10 slots;
OpenRouter Ox (`ox`) and other models default to 4. Cross-process slots use
advisory locks under `/tmp/allmath-modelbench-provider-slots`; interrupted
runners release their slots automatically. Agentic tasks may override the
default timeout in their task JSON, which is useful for slower free routes.
Slot acquisition is bounded by `--slot-wait-timeout-s` (5,400 seconds by
default). For a wave that may be superseded, pass a unique `--cancel-file`;
creating that file cancels queued calls and gracefully stops only that
runner's active child process groups. SIGINT and SIGTERM use the same path.
Partial artifacts and JSONL traces are retained, provider locks are released,
and cancelled artifacts are not sent through an expensive Lean gate.

For the two free Ox providers, inspect the lock-backed occupancy (including
resumed OpenCode sessions) with:

```bash
.venv/bin/python workflows/modelbench/runner.py --models ox,oxzen --slot-status
```

This is a point-in-time view of the actual slot locks, rather than a process
count. An isolated Lean gate that reports Lean exit code 137 is retained as a
failed infrastructure run, not misreported as a candidate proof error; it is
not automatically sent back to a model for a futile repair. If an OpenCode
artifact turn instead ends with a provider-side `reason: unknown`, zero tokens,
and no artifact, the retry starts a fresh session with the complete original
prompt after cancellation-aware exponential backoff (5-second base, 60-second
cap, ±25% jitter). This provider-failure backoff does not delay ordinary Lean
compiler-error repair; a partial artifact still uses same-session repair.
Lean repair excerpts begin at the actual elaboration error so trailing
`#print axioms` recovery noise cannot hide the actionable mismatch.

## Caveats (read before trusting numbers)

- Single-shot prompts without tools understate agentic performance (the real
  builder iterates with a compiler). Treat lean_* as a floor, not a ceiling.
- The honesty grader is itself a model; disputes deserve a manual read of the
  corresponding disposable run directory before promoting any conclusion.
- Task banks are small (~32 tasks); differences of one task are noise. Use
  for role ranking, not fine-grained scoring.
- MiniMax M3 remains outside the trusted research path regardless of scores
  (policy: hint-only) unless Marcel changes that policy explicitly.
