#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

cd "$ROOT"
sha256sum --check SHA256SUMS
python3 certify_pi.py "$TMP"
cmp pi_digits.txt "$TMP/pi_digits.txt"
cmp interval_endpoints.hex "$TMP/interval_endpoints.hex"
cmp certificate.json "$TMP/certificate.json"
python3 t16-pi_certify.py 1048596 \
  "$TMP/t16-pi_digits.txt" "$TMP/t16-certificate.json"
cmp pi_digits.txt "$TMP/t16-pi_digits.txt"
printf '%s\n' "T17 replay passed: exact endpoints and T16 decimal-prefix hash reproduced."
