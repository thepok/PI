#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

# Source hashes and exact locations are recorded in REPORT.md. They were
# checked before delivery; replay intentionally uses only exported artifacts.
python3 verify_examples.py
sha256sum -c SHA256SUMS
