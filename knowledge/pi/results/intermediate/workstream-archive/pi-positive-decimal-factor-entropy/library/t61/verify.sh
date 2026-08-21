#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../../../.." && pwd)

cd "$SCRIPT_DIR"
sha256sum -c SHA256SUMS

cd "$ROOT"
lake env lean "$SCRIPT_DIR/T61VaalerAnalytic.lean"
