#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TAG="${1:-localhost/allmath-research:latest}"

BUILDAH_ISOLATION="${BUILDAH_ISOLATION:-chroot}" podman build \
  -f "$ROOT_DIR/workflows/runtime/containers/Containerfile.allmath" \
  -t "$TAG" \
  "$ROOT_DIR"
