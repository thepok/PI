#!/bin/sh
set -eu

artifact_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$artifact_dir"
sha256sum -c SHA256SUMS >/dev/null
python3 "$artifact_dir/t68_projection.py" replay --directory "$artifact_dir"
