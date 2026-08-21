#!/usr/bin/env sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

sha256sum -c SHA256SUMS
python3 t51_checker.py --verify certificates.json
