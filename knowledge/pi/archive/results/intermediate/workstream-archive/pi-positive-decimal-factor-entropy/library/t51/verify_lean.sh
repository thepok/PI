#!/usr/bin/env sh
set -eu

if [ "$#" -ne 1 ]; then
  printf '%s\n' "usage: ./verify_lean.sh /path/to/AllMath" >&2
  exit 2
fi

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$1
cd "$ROOT"
lake env lean "$HERE/T51DecimalChainRange.lean"
