#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$SCRIPT_DIR/verify_stream.py" --max-order 2
