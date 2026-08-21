#!/bin/sh
set -eu

artifact_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$artifact_dir"

sha256sum -c SHA256SUMS

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT HUP INT TERM
pdftotext -f 47 -l 48 -layout furstenberg-1967.pdf "$tmp"
grep -q 'IV.2.' "$tmp"
grep -q 'IV. 1.' "$tmp"
grep -q 'non-lacunary' "$tmp"
grep -q 'irrational' "$tmp"

if [ "${ALLMATH_ROOT:-}" ]; then
  (cd "$ALLMATH_ROOT" && lake env lean "$artifact_dir/T77FixedWordCoreStabilization.lean")
fi

printf '%s\n' 'T77 hashes and pinned Furstenberg locators verified.'
