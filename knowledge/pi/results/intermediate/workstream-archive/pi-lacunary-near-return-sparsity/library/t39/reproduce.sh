#!/bin/sh
set -eu
sha256sum -c SHA256SUMS
python3 verify_audit.py
