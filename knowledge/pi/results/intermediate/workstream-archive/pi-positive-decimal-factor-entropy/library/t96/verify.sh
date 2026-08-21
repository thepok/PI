#!/bin/sh
set -eu

sha256sum -c SHA256SUMS
python3 t96_exact_replay.py --verify replay_expected.json
