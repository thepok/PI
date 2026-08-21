#!/bin/sh
set -eu

sha256sum -c HASHES.sha256
python3 finite_prefix_diagnostics.py | diff -u expected-output.txt -
printf '%s\n' 'replay=PASS'
