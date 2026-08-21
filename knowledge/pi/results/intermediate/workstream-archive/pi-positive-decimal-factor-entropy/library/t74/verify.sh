#!/bin/sh
set -eu

sha256sum -c SHA256SUMS

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT HUP INT TERM
pdftotext -f 47 -l 48 -layout furstenberg-1967.pdf "$tmp"

grep -q 'IV.2.' "$tmp"
grep -q 'IV. 1.' "$tmp"
grep -q 'non-lacunary' "$tmp"
grep -q 'irrational' "$tmp"

test "$(sha256sum pi-positive-decimal-factor-entropy.txt | cut -d' ' -f1)" = \
  'a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6'

printf '%s\n' 'T74 source and artifact verification passed.'
