#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -lt 2 ]]; then
  echo "usage: allmath-lean-gate <project-root> <candidate.lean> [lib ...]" >&2
  echo "   or: allmath-lean-gate <project-root> --batch <candidate.lean>... -- [lib ...]" >&2
  exit 2
fi

source_root="$1"
shift
candidates=()
if [[ "$1" == "--batch" ]]; then
  shift
  while [[ "$#" -gt 0 && "$1" != "--" ]]; do
    candidates+=("$1")
    shift
  done
  if [[ "${#candidates[@]}" -eq 0 || "$#" -eq 0 ]]; then
    echo "batch mode requires at least one candidate and a -- separator" >&2
    exit 2
  fi
  shift
else
  candidates+=("$1")
  shift
fi
# Libraries to build before compiling the candidate.
libs=("$@")
if [[ "${#libs[@]}" -eq 0 ]]; then
  libs=(TheoryLib)
fi
gate_root="$(mktemp -d /tmp/allmath-lean-gate.XXXXXX)"
trap 'rm -rf "$gate_root"' EXIT

# Fast path: if the image carries a prebaked build of exactly this trusted
# source (hash-verified), compile the candidate against it directly — no
# copying, no rebuilding. Any mismatch falls through to the full build.
prebaked=/opt/allmath-prebuilt
if [[ -d "$prebaked" && -f "$prebaked/PREBAKE_SHA" ]]; then
  src_sha="$( (cd "$source_root" && find TheoryLib -name '*.lean' -print0 2>/dev/null | sort -z | xargs -0 sha256sum && sha256sum TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain) 2>/dev/null | sha256sum | cut -d' ' -f1 )"
  if [[ -n "$src_sha" && "$src_sha" == "$(cat "$prebaked/PREBAKE_SHA")" ]]; then
    cd "$prebaked"
    for candidate in "${candidates[@]}"; do
      echo "ALLMATH_LEAN_GATE_CANDIDATE=$candidate"
      lake env lean "$candidate"
    done
    exit 0
  fi
fi

# Never consume `.lake` from the model workspace. Build a clean project view
# from the controller-pinned source snapshot and the image-pinned dependency
# cache. The scratch candidate remains outside the verified source tree.
cp -a "$source_root/lakefile.toml" "$gate_root/lakefile.toml"
cp -a "$source_root/lake-manifest.json" "$gate_root/lake-manifest.json"
cp -a "$source_root/lean-toolchain" "$gate_root/lean-toolchain"
cp -a "$source_root/TheoryLib.lean" "$gate_root/TheoryLib.lean"
cp -a "$source_root/TheoryLib" "$gate_root/TheoryLib"
mkdir -p "$gate_root/.lake"
# Lake occasionally refreshes dependency-owned `.hash` metadata even when all
# compiled artifacts are already present. Keep the image and its package cache
# read-only: create real scratch directory trees for the two packages Lake
# touches, symlink their substantive image-pinned files, and replace only hash
# symlinks with tiny writable copies. Other packages stay single read-only
# symlinks. A genuinely stale dependency artifact still cannot be overwritten.
mkdir -p "$gate_root/.lake/packages"
for package in /opt/allmath-lean/.lake/packages/*; do
  name="$(basename "$package")"
  case "$name" in
    mathlib|proofwidgets)
      scratch_package="$gate_root/.lake/packages/$name"
      mkdir -p "$scratch_package"
      cp -as "$package"/. "$scratch_package"/
      # Keep Lake's URL/revision check tied to the image-pinned checkout.
      # A recursively symlinked .git directory is not recognized as the same
      # repository and makes networkless Lake attempt a fresh clone.
      rm -rf "$scratch_package/.git"
      ln -s "$package/.git" "$scratch_package/.git"
      (
        cd "$package"
        find . -type f -name '*.hash' -print0 |
          tar --null -T - -cf -
      ) | tar -C "$scratch_package" --overwrite -xf -
      ;;
    *) ln -s "$package" "$gate_root/.lake/packages/$name" ;;
  esac
done
# The trusted source can be newer than the image marker by one or more
# accepted modules.  Seed the scratch build with the image's kernel-checked
# oleans and let Lake rebuild only source hashes that changed; without this,
# one small imported TheoryLib module triggers an 8k-module cold rebuild.
if [[ -d "$prebaked/.lake/build" ]]; then
  cp -a "$prebaked/.lake/build" "$gate_root/.lake/build"
fi

cd "$gate_root"
for lib in "${libs[@]}"; do
  case "$lib" in
    TheoryLib) ;;
    NoBuild) continue ;;
    *) echo "unknown gate lib: $lib" >&2; exit 2 ;;
  esac
  if [[ "$lib" == "TheoryLib" && ! -e "$gate_root/TheoryLib.lean" ]]; then
    continue
  fi
  lake build "$lib"
done
for candidate in "${candidates[@]}"; do
  echo "ALLMATH_LEAN_GATE_CANDIDATE=$candidate"
  lake env lean "$candidate"
done
