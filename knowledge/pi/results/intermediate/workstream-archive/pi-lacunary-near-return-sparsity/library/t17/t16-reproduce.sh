#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/allmath-t16.XXXXXX")
trap 'rm -rf -- "$TMP"' EXIT

for command in python3 sha256sum cmp; do
  command -v "$command" >/dev/null 2>&1 || {
    printf 'missing required command: %s\n' "$command" >&2
    exit 1
  }
done

python3 "$ROOT/pi_certify.py" 1048596 \
  "$TMP/pi_digits.txt" "$TMP/pi_certificate.json"
cmp "$TMP/pi_digits.txt" "$ROOT/pi_digits.txt"
cmp "$TMP/pi_certificate.json" "$ROOT/pi_certificate.json"

python3 "$ROOT/experiment.py" \
  --artifact-dir "$ROOT" \
  --pi-digits "$TMP/pi_digits.txt" \
  --pi-certificate "$TMP/pi_certificate.json" \
  --output "$TMP/raw_output.json" \
  --report "$TMP/REPORT.md"
cmp "$TMP/raw_output.json" "$ROOT/raw_output.json"
cmp "$TMP/REPORT.md" "$ROOT/REPORT.md"

python3 "$ROOT/verify_output.py" "$ROOT" "$TMP/raw_output.json"
(cd "$ROOT" && sha256sum -c SHA256SUMS)

printf '%s\n' 'T16 replay passed: certified digits, exact tables, naive cases, report, and hashes agree.'
