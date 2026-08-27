#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS

tmp_normal="$(mktemp)"
tmp_optimized="$(mktemp)"
trap 'rm -f "$tmp_normal" "$tmp_optimized"' EXIT HUP INT TERM

PYTHONDONTWRITEBYTECODE=1 python3 t83_cross_scale_replay.py > "$tmp_normal"
PYTHONDONTWRITEBYTECODE=1 python3 -O t83_cross_scale_replay.py > "$tmp_optimized"
cmp replay_expected.json "$tmp_normal"
cmp replay_expected.json "$tmp_optimized"

printf '%s\n' "T83 verification passed"
