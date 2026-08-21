#!/bin/sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

if [ "${1:-}" != "verify" ]; then
  printf '%s\n' "usage: ./reproduce.sh verify" >&2
  exit 2
fi

cd "$HERE"
sha256sum -c HASHES.sha256

TMPDIR_T24=$(mktemp -d)
trap 'rm -rf "$TMPDIR_T24"' EXIT HUP INT TERM
tar -xf "$HERE/EVIDENCE.tar" -C "$TMPDIR_T24"
EVIDENCE="$TMPDIR_T24/evidence"

if [ ! -d "$EVIDENCE" ]; then
  printf '%s\n' "EVIDENCE.tar does not contain the evidence root" >&2
  exit 1
fi

(cd "$EVIDENCE" && sha256sum -c "$HERE/EVIDENCE_HASHES.sha256")
(cd "$EVIDENCE/knowledge_library/t5" && sha256sum -c HASHES.sha256)

check_extraction() {
  expected=$1
  source=$2
  name=$3
  pdftotext -layout "$source" "$TMPDIR_T24/$name.txt"
  actual=$(sha256sum "$TMPDIR_T24/$name.txt" | cut -d ' ' -f 1)
  if [ "$actual" != "$expected" ]; then
    printf '%s\n' "extraction hash mismatch: $source" >&2
    exit 1
  fi
  printf '%s\n' "$source extraction: OK"
}

check_extraction 1e2078a709f2bd824f09aefe177c255e6d4b17d230d037828d95e379a801c69b \
  "$EVIDENCE/sources/mahler-1953-reprint.pdf" mahler-1953-reprint
check_extraction 9cdbfaf41eed00c7a14e45bb1e800af1c25be75bec14a33b2c8eae808d83c7a4 \
  "$EVIDENCE/sources/mignotte-1974.pdf" mignotte-1974
check_extraction ba9053ed473dccfe7bff22b3bb00ea92ee3cdb291ee924632441b40c1d3987aa \
  "$EVIDENCE/sources/hata-1993.pdf" hata-1993
check_extraction e05fcf2c6941386ab51d0bb2705110f4e67660d7669d9f2a92d9c3e9a9466699 \
  "$EVIDENCE/sources/salikhov-2008.pdf" salikhov-2008
check_extraction 49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68 \
  "$EVIDENCE/sources/zeilberger-zudilin-2020.pdf" zeilberger-zudilin-2020

check_extraction d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406 \
  "$EVIDENCE/knowledge_library/t5/sources/bailey-crandall-2001.pdf" t5-bailey-crandall-2001
check_extraction d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346 \
  "$EVIDENCE/knowledge_library/t5/sources/lagarias-2001.pdf" t5-lagarias-2001
check_extraction f275c64a4382da3d73cd81575c3d6183189d1974b4870be47a4e7c0ffb01c613 \
  "$EVIDENCE/knowledge_library/t5/sources/kuipers-niederreiter-1974.pdf" t5-kuipers-niederreiter-1974
check_extraction 6175283cb39e9db819143e86537058a73c4a803819d695f606cedd09f4ff8521 \
  "$EVIDENCE/knowledge_library/t5/sources/weyl-1916.pdf" t5-weyl-1916
check_extraction 7b2aa16484b6ad79ef5bec51da3501f5079367b625da44bf97468422d27e8e95 \
  "$EVIDENCE/knowledge_library/t5/sources/philipp-1975.pdf" t5-philipp-1975
check_extraction f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808 \
  "$EVIDENCE/knowledge_library/t5/sources/fukuyama-2008.pdf" t5-fukuyama-2008

python3 - "$HERE/CORPUS.json" "$HERE/EVIDENCE_HASHES.sha256" "$HERE/HASHES.sha256" \
  "$HERE/T24_APPLICABILITY_AUDIT.md" "$HERE/LOCKED_EVIDENCE.md" "$EVIDENCE" <<'PY'
import hashlib
import json
import os
import re
import sys
from decimal import Decimal

corpus_path, evidence_manifest, delivery_manifest, audit_path, lock_path, evidence = sys.argv[1:]

with open(corpus_path, encoding="utf-8") as handle:
    corpus = json.load(handle)

def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

def manifest_hashes(path):
    hashes = set()
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                digest, _name = line.rstrip("\n").split("  ", 1)
                assert re.fullmatch(r"[0-9a-f]{64}", digest)
                hashes.add(digest)
    return hashes

def resolve(scope, path):
    assert scope in {"artifact", "workspace_locked"}
    return os.path.join(evidence, path)

assert corpus["item"] == "T24"
assert corpus["replay_bundle"]["file"] == "EVIDENCE.tar"
assert len(corpus["sources"]) <= corpus["limits"]["maximum_primary_sources"] == 6
assert len(corpus["rows"]) <= corpus["limits"]["maximum_theorem_rows"] == 12
assert len(corpus["sources"]) == corpus["limits"]["primary_sources"] == 5
assert len(corpus["rows"]) == corpus["limits"]["theorem_rows"] == 6
assert set(corpus["verdict_policy"]) == {"FULL", "PARTIAL", "NONE", "C1_rule"}

assert sha256(os.path.join(evidence, "problems/local/pi-positive-lower-block-density.txt")) == \
    corpus["canonical_target"]["sha256"] == \
    "11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8"
assert sha256(os.path.join(evidence, "knowledge_library/t23/T23FiniteCylinderEnergyCriterion.lean")) == \
    corpus["T23"]["sha256"]
assert sha256(os.path.join(evidence, "knowledge_library/t3/T3FiniteFourierLowerDensity.lean")) == \
    "50f169aef3efd7d940cefd1447673fc3f828db9317251dda86b5d563e631befa"
assert sha256(os.path.join(evidence, "TheoryLib/PiLacunaryNearReturnSparsity/T7FiniteCylinderEnergy.lean")) == \
    corpus["collision_bridge"]["finite_energy_source"]["sha256"]
assert sha256(os.path.join(evidence, "TheoryLib/PiLacunaryNearReturnSparsity/T1LagDecomposition.lean")) == \
    corpus["collision_bridge"]["lag_source"]["sha256"]

quantifiers = corpus["T23"]["exact_quantifiers"]
for phrase in ("For every real s", "0 < s < 1", "there exist a real C >= 1",
               "a natural N0", "for every natural N >= N0",
               "every natural m >= 1", "not on N or m"):
    assert phrase in quantifiers

source_ids = {source["id"] for source in corpus["sources"]}
assert source_ids == {"MAH1953", "MIG1974", "HATA1993", "SAL2008", "ZZ2020"}
source_by_id = {source["id"]: source for source in corpus["sources"]}
for source in corpus["sources"]:
    for field in ("citation", "doi", "url", "file", "sha256", "text_file",
                  "file_scope", "text_file_scope", "pdftotext_layout_sha256",
                  "locators"):
        assert source[field]
    source_path = resolve(source["file_scope"], source["file"])
    text_path = resolve(source["text_file_scope"], source["text_file"])
    assert os.path.getsize(source_path) == source["bytes"]
    assert sha256(source_path) == source["sha256"]
    assert sha256(text_path) == source["pdftotext_layout_sha256"]

row_ids = [row["id"] for row in corpus["rows"]]
assert len(row_ids) == len(set(row_ids))
for row in corpus["rows"]:
    assert row["source_id"] in source_ids
    assert row["source_sha256"] == source_by_id[row["source_id"]]["sha256"]
    assert row["T23_verdict"] in {"FULL", "PARTIAL", "NONE"}
    assert row["T23_verdict"] == "PARTIAL"
    assert Decimal(row["a_decimal"]) == Decimal(row["mu_decimal"]) - 1
    for field in ("source_sha256", "locator", "exact_source_statement",
                  "denominator_scope", "norm_consequence", "controlled_region",
                  "unresolved_region", "prefix_consequence", "T23_comparison",
                  "C1_consequence"):
        assert row[field]
    assert "10^n*(10^r-1)" in row["norm_consequence"] or row["id"] == "MIG-20"
    assert "m" in row["controlled_region"]
    assert row["C1_consequence"] == \
        "None. Partial scale control neither proves nor supports C1."

assert corpus["generic_translation"]["structured_denominator"].startswith(
    "Q(n,r)=10^n*(10^r-1)")
assert "Q*|pi-P/Q|" in corpus["generic_translation"]["nearest_integer_step"]
assert "Q^(1-mu)" in corpus["generic_translation"]["source_form"]
assert "a=mu-1" in corpus["generic_translation"]["substitution"]
assert "L*(L+1)" in corpus["generic_translation"]["global_energy_translation"]
assert "m=floor(sqrt(N))" in corpus["generic_translation"]["scale_mismatch"]
assert "does not prove or support C1" in corpus["bounded_conclusion"]

t5_root = os.path.join(evidence, "knowledge_library/t5")
with open(os.path.join(t5_root, "CORPUS.json"), encoding="utf-8") as handle:
    t5 = json.load(handle)
assert t5["item"] == "T5"
assert len(t5["sources"]) == 6
assert len(t5["rows"]) <= t5["limits"]["maximum_theorem_rows"]
assert t5["limits"]["additional_primary_sources"] <= \
    t5["limits"]["maximum_additional_primary_sources"]
assert {source["id"] for source in t5["sources"]} == \
    {"BC2001", "FU2008", "KN1974", "LAG2001", "PH1975", "WEYL1916"}
for source in t5["sources"]:
    source_path = os.path.join(t5_root, source["file"])
    assert os.path.getsize(source_path) == source["bytes"]
    assert sha256(source_path) == source["sha256"]
for row in t5["rows"]:
    for field in ("locator", "exact_scope_quantifiers", "base", "conditional_status"):
        assert row[field]
    for target in ("C1", "T3"):
        assert row[target]["verdict"] in {"YES", "NO", "CONDITIONAL"}
        assert row[target]["first_unmatched_premise"]
        assert row[target]["exact_comparison"]

with open(os.path.join(t5_root, "searches/crossref-t5-additional-sources.json"),
          encoding="utf-8") as handle:
    additional_search = json.load(handle)
with open(os.path.join(t5_root, "searches/crossref-t5-fukuyama.json"),
          encoding="utf-8") as handle:
    fukuyama_search = json.load(handle)
assert any(item.get("DOI") == "10.4064/aa-26-3-241-251"
           for item in additional_search["message"]["items"])
assert any(item.get("DOI") == "10.1007/s10474-007-6201-8"
           for item in fukuyama_search["message"]["items"])

generated = {
    "d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406",
    "d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346",
    "f275c64a4382da3d73cd81575c3d6183189d1974b4870be47a4e7c0ffb01c613",
    "6175283cb39e9db819143e86537058a73c4a803819d695f606cedd09f4ff8521",
    "7b2aa16484b6ad79ef5bec51da3501f5079367b625da44bf97468422d27e8e95",
    "f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808",
}
retained = manifest_hashes(evidence_manifest) | manifest_hashes(delivery_manifest) | generated
checked_texts = (
    corpus_path,
    audit_path,
    lock_path,
    os.path.join(os.path.dirname(corpus_path), "SEARCH_LOG.md"),
    os.path.join(t5_root, "T5_APPLICABILITY_AUDIT.md"),
    os.path.join(t5_root, "CORPUS.json"),
    os.path.join(t5_root, "LOCKED_EVIDENCE.md"),
    os.path.join(t5_root, "HASHES.sha256"),
    os.path.join(t5_root, "reproduce.sh"),
)
for path in checked_texts:
    with open(path, encoding="utf-8") as handle:
        mentioned = set(re.findall(r"(?<![0-9a-f])[0-9a-f]{64}(?![0-9a-f])", handle.read()))
    missing = mentioned - retained
    assert not missing, f"unretained hashes in {path}: {sorted(missing)}"

print("CORPUS.json caps, locators, exponents, translations, T23 quantifiers, and verdicts: OK")
print("Imported T5 corpus, DOI records, source hashes, and extraction hashes: OK")
print("Every hash promised by T24 and T5's manifest, replay, or locked evidence is available: OK")
PY

printf '%s\n' "T24 self-contained offline replay: OK"
