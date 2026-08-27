#!/usr/bin/env bash
set -euo pipefail

readonly ARTIFACT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

python3 "$ARTIFACT_DIR/fixed_pi_experiment.py" \
  --statement "$ARTIFACT_DIR/canonical_statement.txt" \
  --output "$ARTIFACT_DIR/raw_output.json"

cd "$ARTIFACT_DIR"
sha256sum \
  canonical_statement.txt \
  fixed_pi_experiment.py \
  requirements.txt \
  raw_output.json \
  run_experiment.sh \
  REPORT.md \
  > SHA256SUMS
