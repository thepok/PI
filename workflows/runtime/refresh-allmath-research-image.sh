#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BASE_TAG="${1:-localhost/allmath-research:latest}"
OUTPUT_TAG="${2:-localhost/allmath-research:refreshed}"

if ! podman image exists "$BASE_TAG"; then
  printf 'base image does not exist: %s\n' "$BASE_TAG" >&2
  exit 2
fi

BUILDAH_ISOLATION="${BUILDAH_ISOLATION:-chroot}" podman build \
  --build-arg "BASE_IMAGE=$BASE_TAG" \
  -f "$ROOT_DIR/workflows/runtime/containers/Containerfile.allmath-refresh" \
  -t "$OUTPUT_TAG" \
  "$ROOT_DIR"
