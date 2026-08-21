#!/bin/sh
set -eu

cd "$(dirname "$0")"

printf '%s  %s\n' \
  'a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6' \
  'pi-positive-decimal-factor-entropy.txt' | sha256sum -c -

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT HUP INT TERM
python3 ./t56_obstruction.py --write "$tmp" >/dev/null
cmp "$tmp" ./obstruction_results.json

if [ -f SHA256SUMS ]; then
  sha256sum -c SHA256SUMS
fi

printf '%s\n' 'T56 obstruction replay and artifact hashes: PASS'
