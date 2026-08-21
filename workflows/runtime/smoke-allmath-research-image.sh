#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TAG="${1:-localhost/allmath-research:latest}"

podman run --rm \
  -v "$ROOT_DIR:/work" \
  -v "$HOME/.local/bin:/lab-tools:ro" \
  -w /work \
  "$TAG" \
  /bin/bash -lc '
    set -euo pipefail
    export PATH=/lab-tools:$PATH
    test "$(opencode --version)" = "1.18.3"
    lean --version
    lake --version
    test "$ALLMATH_AUDIT_LEAN_TOOLCHAIN" = "leanprover/lean4:v4.31.0"
    elan run "$ALLMATH_AUDIT_LEAN_TOOLCHAIN" lean --version | grep -F "version 4.31.0"
    elan run "$ALLMATH_AUDIT_LEAN_TOOLCHAIN" lake --version
    ! command -v docker
    ! command -v podman
    test -f /opt/allmath-lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
    kissat --version | head -1
    geng -help >/dev/null 2>&1
    pdftotext -v 2>&1 | grep -q "pdftotext version"
    rg --version | grep -q "ripgrep"
    python3 -c "import hypothesis, jsonschema, matplotlib, networkx, numpy, pysat, scipy, sympy, yaml"
    python3 workflows/runtime/templates/fastmath/sparse_milp.py --self-test
    FASTMATH_CACHE_DIR=/run/fastmath-cache workflows/runtime/fastmath.sh cpp workflows/runtime/templates/fastmath/streaming_search.cpp -- --self-test
    FASTMATH_CACHE_DIR=/run/fastmath-cache workflows/runtime/fastmath.sh rust workflows/runtime/templates/fastmath/rust-search/Cargo.toml -- --self-test
    printf "ALLMATH_POD_SMOKE_OK\n"
  '
