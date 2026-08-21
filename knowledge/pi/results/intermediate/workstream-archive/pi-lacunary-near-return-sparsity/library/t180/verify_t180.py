#!/usr/bin/env python3
"""Self-contained integrity and bounded-screen replay for T180."""

import csv
import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_HASH = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_HASHES = {
    "baier-rahaman-2504.09650v2.pdf": "960479d87946fff14fc4124258467c73045851f3ae9f036b62ba5587e38ff8af",
    "baier-rahaman-2504.09650v2.txt": "4fed152dfff1d8b88602481b4194cabf26f2b7b14a5996992f13141cd2d447fe",
    "lu-zheng-2603.16794v3.pdf": "589612c81259286682897c888a207539d8ddb2bf5704f92910234d920cf85bc1",
    "lu-zheng-2603.16794v3.txt": "a381386b0097f21a57f0f4fff683bcbbeac4a1052f56743a1c899ef7d25271ea",
    "i-koppl-1802.10355v1.pdf": "18261d4747eb360e754c8515bf2ab9167056a588cf74db9f6a04fa5ecd3f5976",
    "i-koppl-1802.10355v1.txt": "301e7890d07d4f20aa37fc2047bf4a78ba27dff3fe27f177d2b0dcf24292a0d7",
    "milicevic-1407.4100v1.pdf": "a0d092d63ca8a94604ee77dea2d39d4033f40cf54479cf4dd306b3c0bb9c339e",
    "milicevic-1407.4100v1.txt": "a932c8455cfcfd0effe31de92ff1ce4b81977c9bfb4fa8b4a547586a308cfed5",
}
ANCHORS = {
    "baier-rahaman-2504.09650v2.txt": [
        "Theorem 1. There are infinitely many integers n",
        "Theorem 4. Let q",
        "compactly supported in [X, 2X]",
        "Corollary 1. Suppose that q",
        "3. Proof of Corollary 1",
        "where C1 > 0 is a suitable constant depending on Q",
    ],
    "lu-zheng-2603.16794v3.txt": [
        "Theorem 1.1. Let",
        "Theorem 1.2. For any real number",
        "Lemma 3.1. The sequence",
        "Proof of Theorem 1.1.",
    ],
    "i-koppl-1802.10355v1.txt": [
        "Corollary 2.2. A periodic factor",
        "Lemma 3.4. Let",
        "Lemma 3.6. Let",
        "Theorem 3.7. Given a real number",
    ],
    "milicevic-1407.4100v1.txt": [
        "Definition 1. Let",
        "Definition 2. Let",
        "Theorem 4 (B-process).",
        "applying Theorem 4 to the trivial p-adic exponent datum",
    ],
}


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


require(sha256("canonical_statement.txt") == CANONICAL_HASH, "canonical hash")
for filename, expected in SOURCE_HASHES.items():
    require(sha256(filename) == expected, f"hash: {filename}")
for filename, anchors in ANCHORS.items():
    text = (ROOT / filename).read_text(encoding="utf-8")
    for anchor in anchors:
        require(anchor in text, f"missing anchor in {filename}: {anchor}")

with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    sources = list(csv.DictReader(handle))
require(len(sources) == 4, "source tuple count")
require(len(sources) <= 12, "source cap")
domains = {row["domain"] for row in sources}
require(len(domains) == 4 and len(domains) >= 3, "searched domains")
require(len({row["stable_id"] for row in sources}) == 4, "stable identifiers unique")
require(len({row["pdf_sha256"] for row in sources}) == 4, "PDF hashes unique")
require(all(row["exact_locator_and_range"] for row in sources), "source locators")
require(all(row["nearest_prior"] for row in sources), "nearest prior")
require(all(row["quantitative_screen"] for row in sources), "quantitative screens")
require(all(row["transfer_target"] in {"T7", "T10", "T28", "T107"} for row in sources), "transfer targets")
require(all(row["additional_unproved_transfer_premise"] for row in sources), "transfer premises")
require("epsilon=1/100" in sources[0]["quantitative_screen"], "S1 admissible epsilon")
require("X<=d<=2X" in sources[0]["quantitative_screen"], "S1 support range")
require("X^(1/12)>=C1" in sources[0]["quantitative_screen"], "S1 retained constant")
retained = [row for row in sources if row["retained"] == "yes"]
require(len(retained) == 0 and len(retained) <= 4, "retained fingerprint cap")

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    exclusions = list(csv.DictReader(handle))
expected_items = [f"T{i}" for i in range(89, 180)]
require([row["item"] for row in exclusions] == expected_items, "ledger continuity T89-T179")
require(len(exclusions) == 91, "ledger count")
by_item = {row["item"]: row for row in exclusions}
require("algorithmic-randomness" in by_item["T177"]["mechanism_or_fingerprint"], "T177 boundary")
require(by_item["T173"]["verification"] == "accepted sketch note", "T173 refreshed level")
require("import no note deduction" in by_item["T173"]["T180_disposition"], "T173 note firewall")
require(by_item["T174"]["verification"] == "rejected literature artifact", "T174 refreshed level")
require("import no rejected locator or claim" in by_item["T174"]["T180_disposition"], "T174 rejection firewall")
require(by_item["T166"]["verification"] == "MC", "T166 refreshed machine-checked level")
require(by_item["T166"]["source_boundary"] == "Lean declaration readable", "T166 readable module")
require("unlike T179 heavy-lag additive structure" in by_item["T166"]["T180_disposition"], "T166/T179 nonduplication")
require("exceptional-set and prescribed-point" in by_item["T178"]["mechanism_or_fingerprint"], "T178 boundary")
require("additive structure of heavy return lags" in by_item["T179"]["mechanism_or_fingerprint"], "T179 boundary")
require("infer no" in by_item["T178"]["T180_disposition"], "T178 availability firewall")
require(by_item["T179"]["verification"] == "pinned revise", "T179 refreshed status")
require("import no proof-sketch deduction" in by_item["T179"]["T180_disposition"], "T179 claim firewall")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
for marker in [
    "SEARCHED_DOMAIN_COUNT: 4",
    "SOURCE_THEOREM_TUPLE_COUNT: 4",
    "SOURCE_THEOREM_TUPLE_CAP: 12",
    "RETAINED_FINGERPRINT_COUNT: 0",
    "RETAINED_FINGERPRINT_CAP: 4",
    "SCOPED_VERDICT_COUNT: 1",
    "SUCCESSOR_COUNT: 0",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
    "SCOPED VERDICT (1/1): CLOSE.",
]:
    require(report.count(marker) == 1, f"report marker: {marker}")
for source_id in ["S1", "S2", "S3", "S4"]:
    require(report.count(f"## {2 + int(source_id[1:])}. {source_id}:") == 1, f"card: {source_id}")
require(report.count("Additional unproved transfer premise toward") == 4, "four transfer premises")
require(report.count("T178") >= 5 and report.count("T179") >= 5, "T178/T179 comparisons")

# Exact finite witnesses for the four declared scale screens. The S1 witness
# illustrates the threshold for one chosen C1; it is not evidence for a
# universal statement or a replacement for the symbolic proof-sketch bound.
c1 = 100
n = 10**36
m = int(math.log10(n) // 4)
require(m == 9, "S1 logarithmic depth")
require(n ** (1 / 12) >= c1, "S1 explicit C1 threshold")
require(c1 * n ** (-1 / 3) <= 10 ** (-m), "S1 retained-constant scale witness")
require(m * (n - 1) ** 2 / n**2 > 2.9, "S2 concentration counter-screen")
n3 = 10**100
m3 = int(math.log10(n3) // 4)
length3 = n3 + m3 - 1
alpha3 = n3 / m3
descriptor_bound = 3 * (math.pi**2 / 6 + 2.5) * alpha3 * length3
require(descriptor_bound < n3**2, "S3 descriptor count is smaller than constant-word pair energy")
n4 = 10**24
m4 = int(math.log10(n4) // 4)
require(math.sqrt(n4) * math.log(n4) < n4 / m4**2, "S4 favorable raw exponent screen")

print("T180 replay: PASS")
print("canonical hash: PASS")
print("source hashes and anchors: 4/4 PASS")
print("source/theorem tuples: 4 <= 12")
print("searched domains: 4 >= 3")
print("retained fingerprints: 0 <= 4")
print("exclusion ledger: consecutive T89-T179 (91 rows)")
print("T166/T177/T178/T179 boundaries: PASS")
print("quantitative screens: 4/4 PASS")
print("explicit transfer premises: 4/4 PASS")
print("scoped verdicts: 1; successors: 0")
print("fixed-pi/A1/C1/C2 claims: none")
