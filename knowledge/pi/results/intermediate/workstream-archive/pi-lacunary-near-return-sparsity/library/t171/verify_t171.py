#!/usr/bin/env python3
import csv
import hashlib
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CANONICAL_HASH = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
PRIOR_LEDGER_HASH = "85f31058e192d151117a7779d2c8d287a5c7033ae21aabf60c2855407e86b883"


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def rows(name):
    with (ROOT / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


require(digest("canonical_statement.txt") == CANONICAL_HASH, "canonical hash")
require(digest("PRIOR_EXCLUSION_LEDGER.csv") == PRIOR_LEDGER_HASH, "prior ledger hash")

sources = rows("SOURCE_LEDGER.csv")
require(len(sources) == 3 and len(sources) <= 12, "source cap")
require(len({row["domain"] for row in sources}) >= 3, "domain minimum")
require(len({row["stable_id"] for row in sources}) == len(sources), "stable ID uniqueness")
require(len({row["pdf_sha256"] for row in sources}) == len(sources), "PDF uniqueness")
require(len({(row["stable_id"], row["exact_locator"], row["normalized_fingerprint"]) for row in sources}) == len(sources), "tuple uniqueness")
require(all(row["disposition"] == "screened_close" for row in sources), "candidate dispositions")
require(sum(row["disposition"] != "screened_close" for row in sources) == 0, "candidate cap")

prior_sources = (ROOT / "PRIOR_THEOREM_SOURCE_LEDGER.txt").read_text(encoding="utf-8", errors="replace")
for row in sources:
    require(digest(row["pdf_file"]) == row["pdf_sha256"], row["pdf_file"])
    require(digest(row["text_file"]) == row["text_sha256"], row["text_file"])
    require(row["stable_id"].split(":", 1)[1].split("v", 1)[0] not in prior_sources, "prior stable ID")
    require(row["pdf_sha256"] not in prior_sources, "prior PDF hash")
    require(row["exact_locator"], "empty locator")
    require(row["quantitative_screen"], "empty screen")
    require(row["transfer_id"].startswith("PI_S") and row["transfer_id"].endswith("_T10"), "transfer marker")

anchors = {
    "merai-winterhof-1710.03026v1.txt": ["Theorem 2.", "C2 (sn , N )", "for N ≥ 2ℓ+1 + 4", "(6)", "(7)"],
    "pollington-et-al-1906.01151v2.txt": ["non-atomic probability measure", "qn+1", "≥K", "Theorem 1.", "R(x, N ) = 2Ψ(N )", "A > 2", "Ψ(N ) :="],
    "gao-yip-2408.02972v2.txt": ["Theorem 1.7.", "1 ≤ ξ ≤ α", "Theorem 4.2.", "gcd(l1 , l2 . . . , lm ) = 1", "conjugate different from itself outside", "normal to any base b ≥ 2"],
}
for name, needles in anchors.items():
    text = (ROOT / name).read_text(encoding="utf-8", errors="replace")
    for needle in needles:
        require(needle in text, f"missing anchor {needle!r} in {name}")

exclusions = rows("EXCLUSION_LEDGER.csv")
items = [row["item"] for row in exclusions]
require(items == [f"T{i}" for i in range(89, 171)], "ledger coverage")
prior_lines = (ROOT / "PRIOR_EXCLUSION_LEDGER.csv").read_text(encoding="utf-8").splitlines()
current_lines = (ROOT / "EXCLUSION_LEDGER.csv").read_text(encoding="utf-8").splitlines()
require(current_lines[:len(prior_lines)] == prior_lines, "T89-T165 inheritance")
by_item = {row["item"]: row for row in exclusions}
require("active" in by_item["T166"]["verification"] and "reserved" in by_item["T166"]["T163_disposition"], "T166 reservation")
for item, tokens in {
    "T159": ("Palm-Stein", "local-dependence"),
    "T161": ("same-lag", "declumping"),
    "T164": ("power-freeness", "hard agenda exclusion"),
    "T165": ("Champernowne", "hard agenda exclusion"),
    "T168": ("iid", "hard agenda exclusion"),
    "T169": ("Champernowne", "hard agenda exclusion"),
    "T170": ("cumulant", "hard agenda exclusion"),
}.items():
    joined = " ".join(by_item[item].values())
    require(all(token in joined for token in tokens), f"hard exclusion {item}")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
for marker in [
    "PRIMARY_SOURCE_COUNT: 3", "PRIMARY_SOURCE_CAP: 12",
    "SEARCHED_DOMAIN_COUNT: 3", "RETAINED_CANDIDATE_COUNT: 0",
    "RETAINED_CANDIDATE_CAP: 4", "EXCLUSION_LEDGER_RANGE: T89-T170",
    "EXCLUSION_LEDGER_COUNT: 82", "SUCCESSOR_COUNT: 0",
    "FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none",
    "PI_S1_T10", "PI_S2_T10", "PI_S3_T10",
]:
    require(marker in report, f"report marker {marker}")
require(report.count("SCOPED VERDICT (1/1):") == 1, "verdict count")
require(report.count("Disposition: `screened_close`.") == 3, "screen count")
require(report.count("`unproved fixed-pi transfer`") >= 4, "transfer separation")

def discriminator(u):
    return 0.5 * u ** (-1.0 / 3.0) * math.log(u + 2.0) ** 3

d10 = discriminator(10.0 ** 10)
d20 = discriminator(10.0 ** 20)
require(d10 > 2.83 and d20 < 0.0106, "S2 arithmetic")

print("T171 artifact verification: PASS")
print(f"canonical_sha256={CANONICAL_HASH}")
print(f"primary_sources={len(sources)} domains={len({row['domain'] for row in sources})} retained_candidates=0")
print(f"exclusion_rows={len(exclusions)} range={items[0]}-{items[-1]} active_T166_reserved=yes")
print(f"S2_D_1e10={d10:.12f}")
print(f"S2_D_1e20={d20:.12f}")
print("scoped_verdicts=1 successors=0 fixed_pi_claims=0")
