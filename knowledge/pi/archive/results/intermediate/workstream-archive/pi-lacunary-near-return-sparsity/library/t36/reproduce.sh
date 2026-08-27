#!/bin/sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=${TMPDIR:-/tmp}/t36-verify-$$.json
trap 'rm -f "$TMP"' EXIT HUP INT TERM

python3 "$HERE/verify_bound.py" > "$TMP"
cmp "$HERE/raw_output.json" "$TMP"
(cd "$HERE" && sha256sum -c "SHA256SUMS")
printf '%s\n' "T36 replay passed"
