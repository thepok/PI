#!/usr/bin/env python3
"""Self-contained integrity and bounded-screen replay for T181."""

import csv
import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_HASHES = {
    "peres-yang-2606.28860v1.pdf": "bbfbd8b3cbcb0e4523873142eea72326f8d729c4cb2eeb58104741828688ac24",
    "peres-yang-2606.28860v1.txt": "9591c2cc7b37e2c643301df0aad7e9f3a96218605ecd70cd0fa88483603c30d7",
    "lai-xie-2601.03402v1.pdf": "aa0b248aef35849ad26f45ecae3697e6860f7fdf2d5735e23fd7886ab2110545",
    "lai-xie-2601.03402v1.txt": "2f6209b6958776b3769d637a525f9f62eb6b0828d8773590d7f6044143ee51d7",
    "kim-2603.23250v2.pdf": "695a82578f5b8d7669d5a1ca24a8934bc070fbc240c39b4487f16b92d728fc7d",
    "kim-2603.23250v2.txt": "6127370b96ee2cec3aa9176f924e4f5d9bc8b8d1e0a2a545e2f44680b386fcf7",
}
ANCHORS = {
    "peres-yang-2606.28860v1.txt": [
        "5    Divisibility chains: the sharp constant",
        "Proposition 5.2 (No-hit estimate for regular intervals).",
        "Sharp upper bound in Theorem 1.2.",
        "Sharp lower bound in Theorem 1.2.",
        "Combining (5.6) and (5.17) proves Theorem 1.2.",
    ],
    "lai-xie-2601.03402v1.txt": [
        "Theorem 1.7.",
        "Proof of Theorem 1.7.",
        "This completes the proof of Theorem 1.7.",
    ],
    "kim-2603.23250v2.txt": [
        "Definition 1.1.",
        "Theorem 1.2.",
        "Lemma 2.1.",
        "2. Exponential Sums over Short Intervals",
    ],
}


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


require(digest("canonical_statement.txt") == CANONICAL_SHA, "canonical hash")
for name, expected in SOURCE_HASHES.items():
    require(digest(name) == expected, f"hash: {name}")
for name, anchors in ANCHORS.items():
    text = (ROOT / name).read_text(encoding="utf-8")
    for anchor in anchors:
        require(anchor in text, f"missing anchor in {name}: {anchor}")

with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    sources = list(csv.DictReader(handle))
require(len(sources) == 3 <= 12, "source tuple cap")
require(len({row["domain"] for row in sources}) == 3, "three searched domains")
for field in ("stable_id", "pdf_sha256", "theorem_range", "normalized_fingerprint"):
    require(len({row[field] for row in sources}) == 3, f"unique {field}")
require(all(row["exact_locator"] and row["theorem_range"] for row in sources), "locators and ranges")
require(all(row["nearest_prior"] for row in sources), "nearest prior")
require(all(row["quantitative_test"] for row in sources), "quantitative tests")
require(all(row["explicit_unproved_transfer_premise"] for row in sources), "transfer premises")
require(sum(row["retained"] == "yes" for row in sources) == 0 <= 4, "retained cap")
require("Proposition 5.2" in sources[0]["exact_locator"], "S1 corrected proof range")

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    exclusions = list(csv.DictReader(handle))
expected = [f"T{i}" for i in range(89, 181)]
require([row["item"] for row in exclusions] == expected, "ledger continuity")
require(len(exclusions) == 92, "ledger count")
by_item = {row["item"]: row for row in exclusions}
require(by_item["T166"]["verification"] == "machine-checked", "T166 level")
require(by_item["T174"]["verification"].startswith("rejected"), "T174 rejection")
require(by_item["T176"]["verification"] == "accepted pinned literature", "T176 level")
require(by_item["T177"]["verification"] == "accepted sketch note", "T177 level")
require(by_item["T178"]["verification"] == "accepted pinned literature", "T178 level")
for item in ("T179", "T180"):
    require(by_item[item]["verification"] == "accepted pinned literature", f"{item} accepted level")
    require("PRIOR_EXCLUSIONS.csv" in by_item[item]["T181_disposition"], f"{item} tuple boundary")
    require("import no proof-sketch deduction" in by_item[item]["T181_disposition"], f"{item} claim firewall")

with (ROOT / "PRIOR_EXCLUSIONS.csv").open(newline="", encoding="utf-8") as handle:
    prior = list(csv.DictReader(handle))
require(len(prior) == 10, "all T179/T180 tuples")
require(sum(row["item"] == "T179" for row in prior) == 6, "six T179 tuples")
require(sum(row["item"] == "T180" for row in prior) == 4, "four T180 tuples")
for field in ("stable_id", "exact_locator", "theorem_range", "normalized_fingerprint"):
    require(all(row[field] for row in prior), f"prior field {field}")
require(set(row["stable_id"] for row in sources).isdisjoint(row["stable_id"] for row in prior), "new/prior source nonduplication")
require(set(row["normalized_fingerprint"] for row in sources).isdisjoint(row["normalized_fingerprint"] for row in prior), "new/prior literal fingerprint nonduplication")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
markers = [
    "SEARCHED_DOMAIN_COUNT: 3",
    "NEW_SOURCE_THEOREM_TUPLE_COUNT: 3",
    "NEW_SOURCE_THEOREM_TUPLE_CAP: 12",
    "RETAINED_FINGERPRINT_COUNT: 0",
    "RETAINED_FINGERPRINT_CAP: 4",
    "SCOPED_VERDICT_COUNT: 1",
    "SUCCESSOR_COUNT: 0",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
    "**SCOPED VERDICT (1/1): CLOSE this T181 scout as a source-pinned negative map.**",
]
for marker in markers:
    require(report.count(marker) == 1, f"report marker: {marker}")
require(report.count("Additional unproved premise toward") == 3, "three transfer premises")

# Finite checks instantiate only the declared screens; they prove no pi claim.
n = 10**12
m = math.floor(math.log10(n) / 4)
grid = math.ceil(n / math.log(n))
gap = math.log(n) / n
collision_ratio = ((n - grid) / n) ** 2
require(m == 3 and gap < 10 ** (-m), "S1 depth and gap")
require(1 / grid <= gap and collision_ratio > 0.9289, "S1 collision separator")

n3 = 10**72
m3 = math.floor(math.log10(n3) / 4)
term1_ratio = n3 ** (-13 / 160)
term2_ratio = n3 ** (-1 / 4)
require(m3 == 18, "S3 logarithmic depth")
require(n3 ** (9 / 40) > 1, "S3 phase-scale hypothesis")
require(term1_ratio + term2_ratio < 1 / m3**2, "S3 raw exponent test")

lines = [
    "T181_REPLAY: PASS",
    f"CANONICAL_SHA256: {CANONICAL_SHA}",
    "EXCLUSION_LEDGER_RANGE: T89-T180",
    f"EXCLUSION_LEDGER_COUNT: {len(exclusions)}",
    f"PRIOR_T179_T180_TUPLE_COUNT: {len(prior)}",
    f"NEW_SOURCE_THEOREM_TUPLE_COUNT: {len(sources)}",
    f"SEARCHED_DOMAIN_COUNT: {len({row['domain'] for row in sources})}",
    "RETAINED_FINGERPRINT_COUNT: 0",
    f"S1_TEST_N: {n}",
    f"S1_TEST_M_DEPTH: {m}",
    f"S1_MAXIMAL_GAP_SCALE: {gap:.11e}",
    f"S1_COLLISION_RATIO_LOWER_BOUND: {collision_ratio:.10f}",
    f"S3_TEST_N: {n3}",
    f"S3_TEST_M_DEPTH: {m3}",
    f"S3_LEADING_TERM_RATIO: {term1_ratio:.10f}",
    f"S3_SECOND_TERM_RATIO: {term2_ratio:.10e}",
    f"S3_TARGET_RATIO: {1 / m3**2:.10f}",
    "QUANTITATIVE_SCREEN_COUNT: 3",
    "EXPLICIT_TRANSFER_PREMISE_COUNT: 3",
    "SCOPED_VERDICT_COUNT: 1",
    "SUCCESSOR_COUNT: 0",
]
print("\n".join(lines))
