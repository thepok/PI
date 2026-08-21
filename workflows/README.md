# Workflow layout

All research execution machinery lives under this directory.

- `modelbench/`: Ox/OpenCode runner, compiler microloop, tests, and task packs.
- `modelbench/tasks/pi/current/`: the active Pi task pack.
- `definitions/`: reusable workflow contracts retained for Pi work.
- `runtime/`: pod images, isolated Lean gate, image refresh, and numerical runtime tools.
- `verification/`: repository-wide Lean and axiom gates.
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
