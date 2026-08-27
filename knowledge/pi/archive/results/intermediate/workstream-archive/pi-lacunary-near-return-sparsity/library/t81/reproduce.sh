#!/usr/bin/env bash
set -euo pipefail
sha256sum -c SHA256SUMS
python3 verify_note.py
