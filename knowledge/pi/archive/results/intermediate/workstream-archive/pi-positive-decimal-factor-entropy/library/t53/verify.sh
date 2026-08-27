#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
PYTHONDONTWRITEBYTECODE=1 python3 ./t53_lift_check.py verify
