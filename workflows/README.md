# Workflow layout

All research execution machinery lives under this directory.

- `modelbench/`: Ox/OpenCode runner, compiler microloop, tests, and task packs.
- `modelbench/tasks/pi/current/`: the active Pi task pack.
- `definitions/`: reusable workflow contracts retained for Pi work.
- `runtime/`: pod images, isolated Lean gate, image refresh, and numerical runtime tools.
- `verification/`: repository-wide Lean and axiom gates.
- `chatgpt-pro/`: persisted web-Pro request prompts; raw browser run state is
  ignored and only one call may be active at a time.
- `state/`: ignored runtime state and the durable operator pause marker.
- `docs/`: architecture and historical design notes.

## Current sandboxed run

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --sandbox \
  --sandbox-image localhost/allmath-research:latest \
  --tasks-dir workflows/modelbench/tasks/pi/current \
  --models ox,oxzen \
  --concurrency 20 \
  --out workflows/state/runs/pi-current
```

The runner enforces the provider limits independently: up to four concurrent
OpenRouter `ox` calls and ten concurrent OpenCode `oxzen` calls. It copies only
declared artifacts back from each pod and independently invokes the trusted
Lean gate.

Do not launch while `workflows/state/OPERATOR_PAUSED` exists.

## Web ChatGPT Pro director

Use the `chatgpt-pro` skill only for an explicit bounded high-intelligence
direction or review task. Name the repository and branch in the prompt, use a
unique output directory, and wait for the complete four-part success contract:
exit code zero, `state.json` status `done`, nonempty `answer.md`, and
`browser_closed: true`. Never run two web-Pro calls concurrently. Authentication,
permission, or capacity-break conditions require an immediate operator stop and
notification to Marcel.
