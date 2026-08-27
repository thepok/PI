#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
START=$SECONDS

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
ELAPSED=$((SECONDS - START))
if (( ELAPSED > 300 )); then
  printf '%s\n' "T53 replay exceeded declared 300-second budget: ${ELAPSED}s" >&2
  exit 1
fi
printf '%s\n' "T53 replay passed in ${ELAPSED}s: hashes, 65,536 tuples, 40,320 legal decisions, 16,320 certified pi-dependent node inequalities, empty T24/T28 transition stages, and exact RESOURCE FRONTIER reproduced."
