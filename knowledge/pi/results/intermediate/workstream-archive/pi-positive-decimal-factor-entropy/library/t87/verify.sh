#!/bin/sh
set -eu

sha256sum -c SHA256SUMS
python3 t87_replay.py > replay_actual.json
cmp replay_expected.json replay_actual.json
python3 -O t87_replay.py > replay_optimized.json
cmp replay_expected.json replay_optimized.json
rm replay_actual.json
rm replay_optimized.json
printf '%s\n' 'T87 replay: PASS'
