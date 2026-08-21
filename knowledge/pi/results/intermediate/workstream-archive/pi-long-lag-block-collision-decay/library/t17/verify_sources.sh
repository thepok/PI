#!/bin/sh
set -eu

sha256sum -c SOURCE_SHA256SUMS

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT HUP INT TERM
pdftotext -layout becher-reimann-slaman-1601.00153v2.pdf "$tmp"

grep -F "supremum of the set of real numbers z" "$tmp" >/dev/null
grep -F "irrationality exponent greater than or equal to a is" "$tmp" >/dev/null
grep -F "2/a" "$tmp" >/dev/null

printf '%s\n' "source hashes and locators verified"
