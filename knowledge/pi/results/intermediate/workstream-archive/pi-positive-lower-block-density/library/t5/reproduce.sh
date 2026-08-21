#!/bin/sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$HERE/../../../.." && pwd)

if [ "${1:-}" != "verify" ]; then
  printf '%s\n' "usage: ./reproduce.sh verify" >&2
  exit 2
fi

cd "$HERE"
sha256sum -c HASHES.sha256

check_workspace_file() {
  expected=$1
  path=$2
  actual=$(sha256sum "$path" | cut -d ' ' -f 1)
  if [ "$actual" != "$expected" ]; then
    printf '%s\n' "hash mismatch: $path" >&2
    exit 1
  fi
  printf '%s\n' "$path: OK"
}

check_workspace_file 11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8 \
  "$ROOT/problems/local/pi-positive-lower-block-density.txt"
check_workspace_file 50f169aef3efd7d940cefd1447673fc3f828db9317251dda86b5d563e631befa \
  "$HERE/../knowledge_library/t3/T3FiniteFourierLowerDensity.lean"
check_workspace_file 50f169aef3efd7d940cefd1447673fc3f828db9317251dda86b5d563e631befa \
  "$ROOT/TheoryLib/PiPositiveLowerBlockDensity/T3T3FiniteFourierLowerDensity.lean"

check_workspace_file 4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd \
  "$ROOT/.research/proof-ledger-artifacts/sha256/48/4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd"
check_workspace_file 33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/33/33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544"
check_workspace_file 5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/59/5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401"
check_workspace_file 432500da9cd3e29470cfba78ab1fd0f5f5362c20bf6038fccdfede8987e3d5a0 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/43/432500da9cd3e29470cfba78ab1fd0f5f5362c20bf6038fccdfede8987e3d5a0"
check_workspace_file 673d31125cb1776ceff7dec5c72f9ba48ab46f12dd20f1c7369745838f6be913 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/67/673d31125cb1776ceff7dec5c72f9ba48ab46f12dd20f1c7369745838f6be913"
check_workspace_file c383d9d70dfebed6e9a2fc778ee935258b2308dcf23496daf9c25508e408b223 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/c3/c383d9d70dfebed6e9a2fc778ee935258b2308dcf23496daf9c25508e408b223"
check_workspace_file 9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/97/9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350"
check_workspace_file 27ecb1ef8221d1e5bb5903d004b192caa86288415b518eaa993e7d05eb38e870 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/27/27ecb1ef8221d1e5bb5903d004b192caa86288415b518eaa993e7d05eb38e870"
check_workspace_file c139f6f8ce2cd95f44936fde22131e922871c8b693c93197a5163119daa52128 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/c1/c139f6f8ce2cd95f44936fde22131e922871c8b693c93197a5163119daa52128"
check_workspace_file 19842fdad9fae9ea19abadeaf21121946558b181ab8eb49c57668e8823107016 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/19/19842fdad9fae9ea19abadeaf21121946558b181ab8eb49c57668e8823107016"
check_workspace_file bb2b0c4ed44a6e77b800ca6aef3fc1a635828890e080dce9ccd60d82c7a4d328 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/bb/bb2b0c4ed44a6e77b800ca6aef3fc1a635828890e080dce9ccd60d82c7a4d328"
check_workspace_file dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58 \
  "$ROOT/.research/proof-ledger-artifacts/sha256/da/dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58"

jq -e 'any(.message.items[]; .DOI == "10.4064/aa-26-3-241-251")' \
  searches/crossref-t5-additional-sources.json >/dev/null
jq -e 'any(.message.items[]; .DOI == "10.1007/s10474-007-6201-8")' \
  searches/crossref-t5-fukuyama.json >/dev/null
printf '%s\n' "bounded-search source DOI checks: OK"

TMPDIR_T5=$(mktemp -d)
trap 'rm -rf "$TMPDIR_T5"' EXIT HUP INT TERM

check_extraction() {
  expected=$1
  source=$2
  name=$3
  pdftotext -layout "$source" "$TMPDIR_T5/$name.txt"
  actual=$(sha256sum "$TMPDIR_T5/$name.txt" | cut -d ' ' -f 1)
  if [ "$actual" != "$expected" ]; then
    printf '%s\n' "extraction hash mismatch: $source" >&2
    exit 1
  fi
  printf '%s\n' "$source extraction: OK"
}

check_extraction d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406 \
  sources/bailey-crandall-2001.pdf bailey-crandall-2001
check_extraction d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346 \
  sources/lagarias-2001.pdf lagarias-2001
check_extraction f275c64a4382da3d73cd81575c3d6183189d1974b4870be47a4e7c0ffb01c613 \
  sources/kuipers-niederreiter-1974.pdf kuipers-niederreiter-1974
check_extraction 6175283cb39e9db819143e86537058a73c4a803819d695f606cedd09f4ff8521 \
  sources/weyl-1916.pdf weyl-1916
check_extraction 7b2aa16484b6ad79ef5bec51da3501f5079367b625da44bf97468422d27e8e95 \
  sources/philipp-1975.pdf philipp-1975
check_extraction f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808 \
  sources/fukuyama-2008.pdf fukuyama-2008

jq -e '
  .item == "T5" and
  (.sources | length) == 6 and
  (.rows | length) <= .limits.maximum_theorem_rows and
  .limits.additional_primary_sources <= .limits.maximum_additional_primary_sources and
  ([.sources[].id] | sort) == (["BC2001","FU2008","KN1974","LAG2001","PH1975","WEYL1916"] | sort) and
  (all(.rows[];
    . as $row |
    ($row.locator | length) > 0 and
    ($row.exact_scope_quantifiers | length) > 0 and
    ($row.base | length) > 0 and
    ($row.conditional_status | length) > 0 and
    (["YES","NO","CONDITIONAL"] | index($row.C1.verdict)) != null and
    (["YES","NO","CONDITIONAL"] | index($row.T3.verdict)) != null and
    ($row.C1.first_unmatched_premise | length) > 0 and
    ($row.C1.exact_comparison | length) > 0 and
    ($row.T3.first_unmatched_premise | length) > 0 and
    ($row.T3.exact_comparison | length) > 0))
' CORPUS.json >/dev/null

printf '%s\n' "CORPUS.json structure: OK"
