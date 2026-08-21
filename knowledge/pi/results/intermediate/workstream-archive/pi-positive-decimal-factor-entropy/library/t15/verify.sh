#!/usr/bin/env bash
set -euo pipefail

artifact_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

cd "$artifact_dir"
sha256sum -c SHA256SUMS
sha256sum -c ARTIFACT_HASHES.sha256

check_pin() {
  local expected="$1"
  local path="$2"
  local actual
  actual="$(sha256sum "$path" | cut -d ' ' -f 1)"
  if [[ "$actual" != "$expected" ]]; then
    printf 'hash mismatch: %s\nexpected: %s\nactual:   %s\n' "$path" "$expected" "$actual" >&2
    return 1
  fi
  printf '%s: OK\n' "$path"
}

check_pin "390946b9d5bc2f3d964b28eb98293db7c3268ad3dfe90aad2f75d4fef37fb4b8" \
  "dependencies/t10/T10ScaleAdaptiveOrbitFourier.lean"
check_pin "0550764bdae3e9c19ddf1ea76321c674046b2cd674f825007ca5bc6652e95ea1" \
  "dependencies/t13/T13AutocorrelationAmplification.lean"
check_pin "93089b4f44db9e295d1f8f560adf5b5b2922e624abfd084b92f6cfb8a0543129" \
  "dependencies/t5/DELTA_AUDIT.md"
check_pin "a1d9bbac1e5043476c3f2053ec4cdf2c65179acfee63ee03c1f3c397547bdb05" \
  "dependencies/t5/SOURCE_MANIFEST.md"

check_pin "a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6" \
  "dependencies/problems/pi-positive-decimal-factor-entropy.txt"

for pdf in *.pdf; do
  if [[ "$(dd if="$pdf" bs=5 count=1 status=none)" != "%PDF-" ]]; then
    printf 'not a PDF: %s\n' "$pdf" >&2
    exit 1
  fi
done

printf 'T15 source and dependency verification: OK\n'
