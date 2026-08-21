#!/usr/bin/env bash
# Overlay a complete trusted-source snapshot onto an existing prebake and
# incrementally rebuild it. This runs only inside the image builder stage.
set -euo pipefail

CURRENT="${1:?current prebake directory required}"
NEXT="${2:?next snapshot directory required}"

snapshot_sha() {
  local tree="$1"
  (
    cd "$tree"
    find TheoryLib -name '*.lean' -print0 | sort -z | xargs -0 sha256sum
    sha256sum TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain
  ) | sha256sum | cut -d' ' -f1
}

purge_module_outputs() {
  local source="$1" module
  module="${source%.lean}"
  # Lake stores every output for these libraries under these two module trees.
  # Removing all suffixes includes the olean/ilean, hashes, traces, C output,
  # and setup metadata without guessing Lake's exact current extension set.
  rm -f -- "$CURRENT/.lake/build/lib/lean/$module".*
  rm -f -- "$CURRENT/.lake/build/ir/$module".*
}

full_rebuild=0
if [[ ! -d "$CURRENT/TheoryLib" ||
      ! -f "$CURRENT/PREBAKE_SHA" ]]; then
  full_rebuild=1
else
  recorded="$(cat "$CURRENT/PREBAKE_SHA" 2>/dev/null || true)"
  actual="$(snapshot_sha "$CURRENT" 2>/dev/null || true)"
  if [[ ! "$recorded" =~ ^[0-9a-f]{64}$ || "$recorded" != "$actual" ]]; then
    echo "existing prebake marker is absent or inconsistent; rebuilding project outputs"
    full_rebuild=1
  fi
fi

# Project/toolchain metadata can change the build graph or artifact format.
# Reusing any project output in that case would be unsafe.
if (( full_rebuild == 0 )); then
  for config in lakefile.toml lake-manifest.json lean-toolchain; do
    if ! cmp -s "$CURRENT/$config" "$NEXT/$config"; then
      echo "$config changed; rebuilding all project outputs"
      full_rebuild=1
      break
    fi
  done
fi

if (( full_rebuild == 1 )); then
  rm -rf -- "$CURRENT/.lake/build"
else
  # Invalidate direct artifacts before replacing sources. Lake then rebuilds
  # the changed module and propagates its output hash through all dependents.
  # Deleted source files are covered by the same walk, so orphan oleans cannot
  # survive the overlay.
  while IFS= read -r -d '' source; do
    relative="${source#"$CURRENT/"}"
    if [[ ! -f "$NEXT/$relative" ]] || ! cmp -s "$source" "$NEXT/$relative"; then
      purge_module_outputs "$relative"
    fi
  done < <(
    find "$CURRENT/TheoryLib" -name '*.lean' -print0
    printf '%s\0' "$CURRENT/TheoryLib.lean"
  )
fi

# Replace, rather than merge, the source trees. This is the deletion boundary:
# after it, the builder contains exactly the staged trusted source snapshot.
rm -rf -- "$CURRENT/TheoryLib"
cp -a "$NEXT/TheoryLib" "$CURRENT/"
cp -a "$NEXT/TheoryLib.lean" \
  "$NEXT/lakefile.toml" "$NEXT/lake-manifest.json" "$NEXT/lean-toolchain" \
  "$CURRENT/"

expected="$(cat "$NEXT/PREBAKE_SHA")"
actual="$(snapshot_sha "$CURRENT")"
if [[ ! "$expected" =~ ^[0-9a-f]{64}$ || "$expected" != "$actual" ]]; then
  echo "staged prebake snapshot mismatch: expected '$expected', got '$actual'" >&2
  exit 1
fi
printf '%s\n' "$actual" > "$CURRENT/PREBAKE_SHA"

mkdir -p "$CURRENT/.lake"
ln -sfn /opt/allmath-lean/.lake/packages "$CURRENT/.lake/packages"
(
  cd "$CURRENT"
  lake build TheoryLib
)

# The build must not mutate trusted source bytes or leave a lying marker.
actual="$(snapshot_sha "$CURRENT")"
if [[ "$actual" != "$expected" ]]; then
  echo "trusted source changed during incremental prebake build" >&2
  exit 1
fi
printf '%s\n' "$actual" > "$CURRENT/PREBAKE_SHA"
