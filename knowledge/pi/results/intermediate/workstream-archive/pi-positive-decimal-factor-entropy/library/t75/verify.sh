#!/bin/sh
set -eu

cd "$(dirname "$0")"

sha256sum -c SHA256SUMS

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT HUP INT TERM
python3 ./t75_replay.py --write "$tmp"
cmp "$tmp" ./replay_expected.json

printf '%s\n' "T75 replay passed: synthetic labels only; zero pi digits read."
