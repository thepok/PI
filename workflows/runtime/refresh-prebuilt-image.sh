#!/usr/bin/env bash
# Rebake localhost/allmath-research:latest with current TheoryLib oleans at
# /opt/allmath-prebuilt, so gate pods skip unchanged trusted modules.
# Cheap derived build (~1-3 min with the image's mathlib cache). Invoked by
# the orchestrator after each TheoryLib integration, or manually.
set -euo pipefail
PREBAKE_LOCK="${ALLMATH_PREBAKE_LOCK:-/tmp/allmath-prebake.lock}"
PREBAKE_QUIET_SECONDS="${ALLMATH_PREBAKE_QUIET_SECONDS:-60}"
PREBAKE_POLL_SECONDS="${ALLMATH_PREBAKE_POLL_SECONDS:-5}"
PREBAKE_MAX_ITERATIONS="${ALLMATH_PREBAKE_MAX_ITERATIONS:-3}"
if [[ ! "$PREBAKE_QUIET_SECONDS" =~ ^[0-9]+$ ]] ||
   [[ ! "$PREBAKE_POLL_SECONDS" =~ ^[1-9][0-9]*$ ]] ||
   [[ ! "$PREBAKE_MAX_ITERATIONS" =~ ^[1-9][0-9]*$ ]]; then
  echo "prebake quiet/poll/max-iteration values must be nonnegative/positive integers" >&2
  exit 2
fi
exec 9>"$PREBAKE_LOCK"
# The lock owner already rechecks the live source hash after its build and
# loops until the image is current. Queuing one sleeping process per accepted
# integration therefore adds no coverage; during a disk-full incident it left
# twenty refresh processes waiting for up to 21 hours. If an owner exists,
# let that owner absorb this refresh request and exit immediately.
if ! flock -n 9; then
  echo "prebake refresh already active; current owner will recheck source"
  exit 0
fi
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
STAGE=""
cleanup() {
  if [[ -n "$STAGE" && -d "$STAGE" ]]; then
    rm -rf -- "$STAGE"
  fi
}
trap cleanup EXIT

snapshot_sha() {
  local tree="$1"
  (
    cd "$tree"
    find TheoryLib -name '*.lean' -print0 | sort -z | xargs -0 sha256sum
    sha256sum TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain
  ) | sha256sum | cut -d' ' -f1
}

stable_snapshot_sha() {
  local tree="$1"
  local previous current attempt
  previous="$(snapshot_sha "$tree")"
  for attempt in 1 2 3 4 5; do
    current="$(snapshot_sha "$tree")"
    if [[ "$current" == "$previous" ]]; then
      printf '%s\n' "$current"
      return 0
    fi
    previous="$current"
    sleep 1
  done
  echo "trusted snapshot hash did not stabilize for $tree" >&2
  return 1
}

image_snapshot() {
  podman run --rm --network none localhost/allmath-research:latest \
    sh -c '
      cd /opt/allmath-prebuilt || exit 1
      test ! -e ErdosLab || exit 1
      test ! -e ErdosLab.lean || exit 1
      test -z "$(find .lake/build/lib/lean .lake/build/ir \
        -path "*/ErdosLab*" -print -quit 2>/dev/null)" || exit 1
      recorded="$(cat PREBAKE_SHA 2>/dev/null || true)"
      actual="$(
        (find TheoryLib -name "*.lean" -print0 | sort -z | xargs -0 sha256sum
         sha256sum TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain) |
          sha256sum | cut -d" " -f1
      )"
      printf "%s %s\n" "$recorded" "$actual"
    ' 2>/dev/null || true
}

image_matches_snapshot() {
  local expected="$1"
  local attempt snapshot
  for attempt in 1 2 3; do
    snapshot="$(image_snapshot)"
    if [[ "$snapshot" == "$expected $expected" ]]; then
      return 0
    fi
    # Two valid hashes mean the image is genuinely stale.  Retry only empty or
    # malformed probes, which can occur transiently while Podman is busy.
    if [[ "$snapshot" =~ ^[0-9a-f]{64}\ [0-9a-f]{64}$ ]]; then
      return 1
    fi
    (( attempt == 3 )) || sleep 1
  done
  return 1
}

wait_for_quiet_source() {
  (( PREBAKE_QUIET_SECONDS == 0 )) && return 0
  local previous current stable_since
  previous="$(snapshot_sha "$ROOT")"
  stable_since=$SECONDS
  while true; do
    sleep "$PREBAKE_POLL_SECONDS"
    current="$(snapshot_sha "$ROOT")"
    if [[ "$current" != "$previous" ]]; then
      previous="$current"
      stable_since=$SECONDS
      echo "trusted source changed; waiting for a quiet prebake window"
      continue
    fi
    if (( SECONDS - stable_since >= PREBAKE_QUIET_SECONDS )); then
      return 0
    fi
  done
}

PREBAKE_ITERATION=0
while true; do
  PREBAKE_ITERATION=$((PREBAKE_ITERATION + 1))
  if (( PREBAKE_ITERATION > PREBAKE_MAX_ITERATIONS )); then
    echo "prebake source did not converge after $PREBAKE_MAX_ITERATIONS build iterations" >&2
    exit 1
  fi
  # A queued request for an image that is already current remains an immediate
  # no-op.  Only an actually stale image waits for the source tree to settle.
  CURRENT_SHA="$(stable_snapshot_sha "$ROOT")"
  if image_matches_snapshot "$CURRENT_SHA"; then
    echo "prebaked image already current (PREBAKE_SHA $CURRENT_SHA)"
    exit 0
  fi
  # During bursts of accepted integrations, rebuilding every intermediate
  # snapshot can churn forever.  Preserve the post-build hash check below, but
  # wait for one bounded quiet window before paying for another full build.
  wait_for_quiet_source

  STAGE="$(mktemp -d /tmp/allmath-prebake.XXXXXX)"
  cd "$ROOT"
  cp -r TheoryLib "$STAGE/"
  cp TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain "$STAGE/"
  # The pristine base predates in-repo gate-script updates (flattening to it
  # reverted the gate to Jul-17 and broke theory reviews) — always bake the
  # CURRENT gate from the repo.
  cp workflows/runtime/containers/allmath-lean-gate.sh "$STAGE/"
  cp workflows/runtime/prebake-incremental-overlay.sh "$STAGE/"
  # Content manifest so the gate can verify the bake matches its trusted source.
  # Compute before opening the marker. This keeps the staged snapshot value
  # independent of marker-file write timing and makes it easy to audit.
  STAGED_SHA="$(stable_snapshot_sha "$STAGE")"
  printf '%s\n' "$STAGED_SHA" > "$STAGE/PREBAKE_SHA"
  if image_matches_snapshot "$STAGED_SHA"; then
    echo "prebaked image already current (PREBAKE_SHA $STAGED_SHA)"
    exit 0
  fi
  # Reuse :latest only as a disposable builder stage, so Lake can retain clean
  # project outputs and rebuild the changed dependency cone. The published
  # stage still starts from the pristine base and receives one flattened copy;
  # repeated refreshes therefore cannot compound image layers.
  cat > "$STAGE/Containerfile" <<'CF'
FROM localhost/allmath-research:latest AS incremental
USER root
COPY TheoryLib /tmp/allmath-next/TheoryLib
COPY TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain PREBAKE_SHA /tmp/allmath-next/
COPY prebake-incremental-overlay.sh /tmp/prebake-incremental-overlay.sh
RUN chmod +x /tmp/prebake-incremental-overlay.sh && \
    /tmp/prebake-incremental-overlay.sh /opt/allmath-prebuilt /tmp/allmath-next && \
    rm -rf /tmp/allmath-next /tmp/prebake-incremental-overlay.sh

FROM localhost/allmath-research:pre-theorylib
USER root
RUN rm -rf /opt/allmath-prebuilt
COPY --from=incremental /opt/allmath-prebuilt /opt/allmath-prebuilt
COPY allmath-lean-gate.sh /usr/local/bin/allmath-lean-gate
RUN chmod +x /usr/local/bin/allmath-lean-gate
# The builder recomputed the marker from the overlaid bytes before and after
# Lake ran. Recompute after the cross-stage copy as a final flattening check.
RUN cd /opt/allmath-prebuilt; \
    test -L .lake/packages; \
    test "$(readlink .lake/packages)" = /opt/allmath-lean/.lake/packages; \
    expected="$(cat PREBAKE_SHA)"; \
    actual="$( (find TheoryLib -name '*.lean' -print0 | sort -z | xargs -0 sha256sum; \
      sha256sum TheoryLib.lean lakefile.toml lake-manifest.json lean-toolchain) | \
      sha256sum | cut -d' ' -f1)"; \
    test "$expected" = "$actual"; \
    printf '%s\n' "$actual" > PREBAKE_SHA
LABEL org.opencontainers.image.title="pi-research" \
      org.opencontainers.image.description="Sandboxed Pi research environment with OpenCode, Lean, numerical tools, and an isolated kernel verification gate."
CF
  # Do not allow a stale cached COPY layer to pair current trusted sources with
  # an older PREBAKE_SHA. The expensive mathlib cache remains in the base image.
  BUILDAH_ISOLATION="${BUILDAH_ISOLATION:-chroot}" podman build --pull=never --no-cache \
    -f "$STAGE/Containerfile" -t localhost/allmath-research:latest "$STAGE"
  IMAGE_SNAPSHOT="$(image_snapshot)"
  read -r IMAGE_RECORDED_SHA IMAGE_ACTUAL_SHA <<< "$IMAGE_SNAPSHOT"
  if [[ -z "$IMAGE_ACTUAL_SHA" || "$IMAGE_RECORDED_SHA" != "$IMAGE_ACTUAL_SHA" ]]; then
    echo "prebaked image manifest verification failed: got '$IMAGE_SNAPSHOT'" >&2
    exit 1
  fi
  echo "prebaked image tagged latest (PREBAKE_SHA $IMAGE_ACTUAL_SHA)"
  # A busy research run can change TheoryLib during every build, keeping this
  # process inside the loop for hours.  Pruning only after loop exit allowed
  # each superseded derived image to accumulate until the filesystem filled.
  # Image prune removes dangling layers only; tagged and live-container images
  # remain protected.
  podman image prune -f >/dev/null 2>&1 || true

  # If another accepted theorem landed during the build, loop back.  The next
  # attempt waits for a quiet source window instead of baking every transient
  # intermediate snapshot; a queued refresh still exits cheaply once current.
  CURRENT_SHA="$(stable_snapshot_sha "$ROOT")"
  if [[ "$CURRENT_SHA" == "$IMAGE_ACTUAL_SHA" ]]; then
    break
  fi
  # Confirm a mismatch before paying for another full build.  A concurrent
  # file replacement or a transient Podman probe must not turn a current image
  # into hours of rebuild churn.
  sleep 1
  CURRENT_SHA="$(stable_snapshot_sha "$ROOT")"
  if image_matches_snapshot "$CURRENT_SHA"; then
    echo "prebaked image current after post-build recheck (PREBAKE_SHA $CURRENT_SHA)"
    break
  fi
  echo "trusted source changed during prebake; scheduling latest snapshot (source $CURRENT_SHA, image $IMAGE_ACTUAL_SHA)"
  rm -rf -- "$STAGE"
  STAGE=""
done
# Auto-prune superseded prebaked layers: each rebake leaves the previous
# derived image dangling; 138 accumulated (38GB) before this line existed.
podman image prune -f >/dev/null 2>&1 || true
