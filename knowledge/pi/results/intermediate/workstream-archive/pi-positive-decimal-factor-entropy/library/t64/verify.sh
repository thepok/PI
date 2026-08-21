#!/bin/sh
set -eu

sha256sum -c SHA256SUMS
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
python3 t64_replay.py --write "$tmp"
cmp "$tmp" replay_expected.json
python3 t64_replay.py --constants 7 12345 --write "$tmp"
printf '%s\n' 'T64 exact replay passed'
