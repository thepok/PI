#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$SCRIPT_DIR"

sha256sum -c SHA256SUMS
actual=$(mktemp "${TMPDIR:-/tmp}/t67-replay.XXXXXX")
trap 'rm -f "$actual"' EXIT HUP INT TERM
python3 t67_replay.py --write "$actual"
cmp "$actual" replay_expected.json
printf '%s\n' 'T67 replay verified'
