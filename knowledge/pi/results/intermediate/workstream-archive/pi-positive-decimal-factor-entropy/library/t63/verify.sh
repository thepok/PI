#!/bin/sh
set -eu

sha256sum -c SHA256SUMS
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
python3 t63_replay.py --write "$tmp"
cmp "$tmp" replay_expected.json
printf '%s\n' 'T63 replay verified'
