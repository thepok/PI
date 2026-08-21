#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
python3 t98_replay.py > replay_actual.json
cmp -s replay_actual.json replay_expected.json
rm replay_actual.json
printf '%s\n' 'T98 replay verification passed.'
