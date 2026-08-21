#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

check_file() {
  expected=$1
  path=$2
  actual=$(sha256sum "$path" | cut -d ' ' -f 1)
  if [ "$actual" != "$expected" ]; then
    printf '%s\n' "hash mismatch: $path" >&2
    printf '%s\n' "expected $expected" >&2
    printf '%s\n' "actual   $actual" >&2
    exit 1
  fi
}

check_object() {
  hash=$1
  check_file "$hash" "$STORE/$(printf '%.2s' "$hash")/$hash"
}

(cd "$SCRIPT_DIR" && sha256sum --check SHA256SUMS)
(cd "$SCRIPT_DIR" && sha256sum --check ARTIFACT_HASHES.sha256)

for pdf in "$SCRIPT_DIR"/sources/*.pdf; do
  pdfinfo "$pdf" >/dev/null
done

for id in AB07 EG55 SZ47 PH75-T1 PH75-D FU08 RZ99 RZ02-CORR RZ02-MS BBP97 BC02 ZZ20; do
  line=$(rg "^\| $id," "$SCRIPT_DIR/DELTA_AUDIT.md")
  count=$(printf '%s\n' "$line" | rg -o 'DOES NOT APPLY' | wc -l | tr -d ' ')
  if [ "$count" != 4 ]; then
    printf '%s\n' "matrix row $id has $count target verdicts, expected 4" >&2
    exit 1
  fi
done
for locator in EG-II PH75 BBP97; do
  rg -q "^\| $locator" "$SCRIPT_DIR/SOURCE_MANIFEST.md"
done
rg -q 'C_N->infinity.*c_N=o\(C_N\)' "$SCRIPT_DIR/DELTA_AUDIT.md"
rg -q 'a\(x\)=10\^\(x-1\)' "$SCRIPT_DIR/DELTA_AUDIT.md"
rg -q 'APPLIES' "$SCRIPT_DIR/DELTA_AUDIT.md"
rg -q 'DOES NOT APPLY' "$SCRIPT_DIR/DELTA_AUDIT.md"
rg -q 'Poisson pair-correlation upper bound' "$SCRIPT_DIR/DELTA_AUDIT.md"
rg -q 'derived arithmetic, not a verbatim source quote' "$SCRIPT_DIR/DELTA_AUDIT.md"

# Replay verification is self-contained. If the checkout is available, also
# verify the external accepted dependencies referenced by content hash.
PROJECT_ROOT=${ALLMATH_PROJECT_ROOT:-}
if [ -z "$PROJECT_ROOT" ]; then
  candidate=$SCRIPT_DIR
  while [ "$candidate" != / ]; do
    if [ -f "$candidate/problems/local/pi-positive-decimal-factor-entropy.txt" ]; then
      PROJECT_ROOT=$candidate
      break
    fi
    candidate=$(dirname -- "$candidate")
  done
fi

if [ -n "$PROJECT_ROOT" ]; then
  STORE="$PROJECT_ROOT/.research/proof-ledger-artifacts/sha256"
  KNOWLEDGE=${ALLMATH_KNOWLEDGE_LIBRARY:-"$SCRIPT_DIR/../knowledge_library"}

  check_file a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6 \
    "$PROJECT_ROOT/problems/local/pi-positive-decimal-factor-entropy.txt"
  check_file 8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf \
    "$KNOWLEDGE/t1/CanonicalEntropy.lean"
  check_file 608e959dcbb2114c7102ca7d06ae0b16c8c6309c7f994e25c372c495b00f0fac \
    "$KNOWLEDGE/t2/T2ExponentialCollisionCriterion.lean"
  check_file 5bb975c9107c5a1862e269b85a9797c195a6f96747b8f35c41e80e5de808c798 \
    "$KNOWLEDGE/t3/FiniteFourierObstruction.lean"
  check_file af8fff5d30cb98164ba6730e457adc4de8c18b6f9944d16cb794f1c3cc60eb3c \
    "$KNOWLEDGE/t4/T4FinitePrefixMultiplicityTransfer.lean"
  check_file 45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff \
    "$PROJECT_ROOT/TheoryLib/PiDecimalFactorComplexity/T10PiWeightedFourierReduction.lean"

  for hash in \
    54d0dca52b5640c1030714cdf58e3cb5f12ac16a2a3dd90c407e3b41bd96443a \
    9e24221a6578169d22f85cb9a3245cf0a23ae0cda11304a0435716be6e2fd0fa \
    1aed7541bb15deec6489fd633ce1003214a769834b688d04d808bc4a30942b9d \
    8661237d2363358c4f2328fb974c693b5f2abaff40470a9eb8340cece34a4b4f \
    caf0f52164d53e5e965ae0523fda342b6f34f52d6ab63d16f0361048ea2cd6e7 \
    dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58 \
    4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd \
    33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544 \
    5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401 \
    1508a10c2a9ec6dd5a4f3400c40e912e7a9c4e5e95a010d8065ca54744145548 \
    35ace6757dba2f6defc0f3d4402eb24e53ef834a34aff6f6a3ff279be8b15583 \
    04b55c7c6a716e23cceac8d22f545a5e4763f6a40dbe2ea22b1a7085d0e35db4 \
    bd95aa34c512ea934801d9baa2d574854ecbb4dc7575670fc4d8304637928f33 \
    8ca6c6555b6892a376ae5e313c13e3b09aa132d150e4eb471925fa864b75b631 \
    fedbf2ae2f990ddd57442d240989f878be9db1868a0fde9b85534572cdfab0bd \
    ba716f7deb6c82c33366cfb4f569c904d59d70283860a4ae7ab5e6be1c924b53 \
    95a85aae4b6fc49b573292621f2fdb09052865594cdcc5f9f7bc154172cb0fd5
  do
    check_object "$hash"
  done
  printf '%s\n' "External workspace dependency verification passed"
else
  printf '%s\n' "External workspace dependencies unavailable; retained-artifact replay checks completed"
fi

printf '%s\n' "T5 audit verification passed"
