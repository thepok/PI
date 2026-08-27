#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
sha256sum --check SHA256SUMS
python3 experiment.py run \
  --config config.json \
  --pi-digits pi_digits.txt \
  --output "$TMP/raw_output.json" \
  --report "$TMP/REPORT.md"
cmp raw_output.json "$TMP/raw_output.json"
cmp REPORT.md "$TMP/REPORT.md"
python3 verify_output.py --config config.json --output "$TMP/raw_output.json"
python3 naive_check.py \
  --config config.json \
  --pi-digits pi_digits.txt \
  --output "$TMP/raw_output.json"
printf '%s\n' "T20 replay passed: hashes, exact envelopes, affine frontiers, T9 rows, and naive cases reproduced."
