#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
sha256sum --check SHA256SUMS
python3 -B experiment.py \
  --config config.json \
  --output "$TMP/raw_output.json" \
  --report "$TMP/REPORT.md"
cmp raw_output.json "$TMP/raw_output.json"
cmp REPORT.md "$TMP/REPORT.md"
python3 -B verify_output.py \
  --config config.json \
  --output "$TMP/raw_output.json" \
  --report "$TMP/REPORT.md"
python3 -B naive_check.py \
  --config config.json \
  --output "$TMP/raw_output.json"
printf '%s\n' "T50 replay passed: hashes, certified intervals, exact predicates, all strata, controls, and naive checks reproduced."
