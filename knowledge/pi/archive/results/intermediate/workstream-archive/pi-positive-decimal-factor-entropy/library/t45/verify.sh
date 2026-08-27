#!/usr/bin/env bash
set -euo pipefail

sha256sum --check SHA256SUMS
python3 verify_bounds.py
