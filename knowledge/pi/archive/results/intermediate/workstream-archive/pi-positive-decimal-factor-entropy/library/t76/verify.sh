#!/bin/sh
set -eu

artifact_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=${ALLMATH_ROOT:-$(CDPATH= cd -- "$artifact_dir/../../../.." && pwd)}

check_hash() {
  expected=$1
  file=$2
  actual=$(sha256sum "$file" | cut -d ' ' -f 1)
  test "$actual" = "$expected"
}

check_hash a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6 \
  "$root/problems/local/pi-positive-decimal-factor-entropy.txt"
check_hash 41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc \
  "$root/TheoryLib/PiPositiveDecimalFactorEntropy/T56T56LagSectorAudit.lean"
check_hash 43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9 \
  "$root/TheoryLib/PiPositiveDecimalFactorEntropy/T69T69FiveCaseCharging.lean"
check_hash fe5f46836cd82973d9a487eda8fbcb3396152b97c1692e9a883998b89f13c9eb \
  "$root/TheoryLib/PiPositiveDecimalFactorEntropy/T75T75WindowLocalLoad.lean"

if grep -Eq '\bsorry\b|\badmit\b|native_decide|^[[:space:]]*axiom\b|^[[:space:]]*unsafe\b' \
    "$artifact_dir/T76WindowLocalReverse.lean"; then
  exit 1
fi

cd "$root"
rm -rf .lake/packages; mkdir -p .lake && ln -sfn /opt/allmath-lean/.lake/packages .lake/packages && cp -r /opt/allmath-prebuilt/.lake/build .lake/build 2>/dev/null || true
timeout 900 lake build TheoryLib
lake env lean "$artifact_dir/T76WindowLocalReverse.lean"
