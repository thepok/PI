#!/bin/sh
set -eu

expected_statement_hash="a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
actual_statement_hash=$(sha256sum pi-positive-decimal-factor-entropy.txt | cut -d ' ' -f 1)
test "$actual_statement_hash" = "$expected_statement_hash"

sha256sum -c SHA256SUMS

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT HUP INT TERM
python3 t82_symbolic_replay.py > "$tmp"
cmp replay_expected.json "$tmp"

printf '%s\n' "T82 artifact hashes and exact symbolic replay: PASS"
