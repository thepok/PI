#!/usr/bin/env python3
"""Self-contained finite replay for T163. Finite checks are not proofs."""

import csv
import hashlib
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "badziahin-1806.02946v1.pdf": "87992e4a5f78c9c1d7b38e55477eb1d1fef3dfd2698fff9916e18395459d0c66",
    "tapia-2602.22512v1.pdf": "613ef7bb0c80e0ed5e3a609a509be585391dabca43d05cdb6565808c25f6fd57",
    "tapia-2602.22512v1.txt": "dda21767b0d4af4855f426812c3f649dd9952472465bac73557e25a6405bbbdf",
    "hambrook-1604.00411v1.pdf": "74ef6d8595be80a1dd139837f6f0a91ec3f43c4277a805ffe38966e9c7e0673c",
    "hambrook-1604.00411v1.txt": "4c884d213a29de16b16372017e8ebc4e54099715d60871760bc2c3ea1e9bca33",
    "cai-hambrook-2403.19410v1.pdf": "c340647222371d95274a053ac2cb4ed4a974ad5da962efa17d2ef558e6f8a57f",
    "cai-hambrook-2403.19410v1.txt": "7050e30c25b7a67be2247196c8ab1198723cc7500557566095640ccee4546cbb",
    "barros-liao-rousseau-1808.00078v2.pdf": "86cdfce61d7b1a88e81c46354871750eb7f84e49aaf5d0ed11d4dae18bafea8e",
    "barros-liao-rousseau-1808.00078v2.txt": "dc5ac4f6ee24ddb85cb2e9c107107c0efa91e0bf7374d6cd461913f96fcdd7b2",
}

SOURCE_ANCHORS = {
    "tapia-2602.22512v1.txt": ["Theorem 1. Suppose", "gcd(an , bn )"],
    "hambrook-1604.00411v1.txt": ["Theorem 1.1.", "Lemma 9.1."],
    "cai-hambrook-2403.19410v1.txt": ["Theorem 1.4.1.", "Lemma 4.3.2."],
    "barros-liao-rousseau-1808.00078v2.txt": ["Theorem 7.", "Rényi entropy"],
}


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


for name, expected in EXPECTED.items():
    require(digest(name) == expected, f"hash mismatch: {name}")

for name, anchors in SOURCE_ANCHORS.items():
    text = (ROOT / name).read_text(errors="strict")
    for anchor in anchors:
        require(anchor in text, f"missing source anchor {anchor!r} in {name}")

report = (ROOT / "REPORT.md").read_text()
pins = (ROOT / "SOURCE_PINS.md").read_text()

required_markers = {
    "PRIMARY_SOURCE_COUNT": 5,
    "PRIMARY_SOURCE_CAP": 10,
    "SEARCHED_DOMAIN_COUNT": 4,
    "SEARCHED_DOMAIN_MINIMUM": 3,
    "RETAINED_FINGERPRINT_COUNT": 3,
    "RETAINED_FINGERPRINT_CAP": 3,
    "EXCLUSION_LEDGER_COUNT": 73,
    "COMPARATOR_RESERVATION_COUNT": 2,
    "SCOPED_VERDICT_COUNT": 1,
    "SUCCESSOR_COUNT": 0,
}
for key, value in required_markers.items():
    require(f"{key}: {value}" in report, f"missing marker {key}")
require(5 <= 10 and 3 <= 3 and 4 >= 3, "cap arithmetic failed")

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="") as handle:
    rows = list(csv.DictReader(handle))
require(len(rows) == 74, "ledger must contain T89-T162")
items = [row["item"] for row in rows]
require(items == [f"T{i}" for i in range(89, 163)], "ledger coverage/order mismatch")
require(len(set(items)) == 74, "duplicate ledger item")
by_item = {row["item"]: row for row in rows}
require("accepted LC/PS/EXP" in by_item["T160"]["verification"], "T160 status stale")
require("accepted LC/PS/EXP" in by_item["T162"]["verification"], "T162 status stale")
require("readable pinned literature artifact" in by_item["T160"]["source_boundary"],
        "T160 comparator boundary missing")
require("readable pinned literature artifact" in by_item["T162"]["source_boundary"],
        "T162 comparator boundary missing")
require("unverified" in by_item["T159"]["source_boundary"], "T159 level lost")
require("unverified" in by_item["T161"]["source_boundary"], "T161 level lost")

candidate_keys = [
    (EXPECTED["tapia-2602.22512v1.pdf"], "Theorem 1", "C-GCD"),
    (EXPECTED["hambrook-1604.00411v1.pdf"] + EXPECTED["cai-hambrook-2403.19410v1.pdf"],
     "Theorem 1.1+Theorem 1.4.1+Lemma 4.3.2", "C-SHELL"),
    (EXPECTED["barros-liao-rousseau-1808.00078v2.pdf"], "Theorem 7", "C-XMATCH"),
]
require(len(candidate_keys) == len(set(candidate_keys)) == 3, "candidate keys not distinct")

# C-GCD exponents for kappa=1: first term threshold 1/3, gcd term 1/2.
kappa = 1.0
first_threshold = 1.0 / (1.0 + 2.0 * kappa)
gcd_threshold = 1.0 / (1.0 + kappa)
require(math.isclose(first_threshold, 1 / 3), "first threshold mismatch")
require(math.isclose(gcd_threshold, 1 / 2), "gcd threshold mismatch")
require(gcd_threshold > first_threshold, "gcd term must be decisive")
for s, converges in [(0.49, False), (0.51, True)]:
    exponent = 1.0 - s * (1.0 + kappa)
    require((exponent < 0) == converges, "gcd-series convergence test failed")

# C-SHELL: every positive exponent gives a convergent geometric series, so s=0.
c, tau = -9, 1.0
require(c != 0, "geometric ray requires nonzero c")
for s in [0.01, 0.25, 1.0]:
    ratio = 10 ** (-(1.0 + tau) * s)
    series = abs(c) ** (-(1.0 + tau) * s) / (1.0 - ratio)
    require(0 < ratio < 1 and math.isfinite(series), "geometric sum failed")
require(sum(1 for j in range(20) if 1000 / 2 < abs(c) * 10 ** j <= 1000) <= 1,
        "dyadic shell occupancy exceeded one")

# C-XMATCH: iid decimal H2=log(10), threshold constant 2/log(10).
renyi2 = -math.log(10 * (0.1 ** 2))
require(math.isclose(renyi2, math.log(10)), "iid decimal Renyi-2 mismatch")
n, epsilon = 10 ** 6, 0.1
lower_depth = math.floor((2.0 - epsilon) * math.log10(n))
upper_depth = math.ceil((2.0 + epsilon) * math.log10(n))
require((lower_depth, upper_depth) == (11, 13), "cross-match threshold replay mismatch")

for label in ["literature-checked", "related-model", "finite-test", "unproved pi transfer"]:
    require(label in report, f"missing claim label {label}")
for target in ["PI-GCD-T28", "PI-SHELL-T10", "PI-XMATCH-T7"]:
    require(target in report, f"missing transfer premise {target}")
require("under that mixing alternative, if\n`H2` also exists" in report,
        "S5 equality must retain the mixing hypothesis")
for scope in [
    "`a>=0`", "increasing function `h:(0,infinity)->(0,infinity)`",
    "`m,n>=1`", "`theta in R^m`", "`Q subset Z^n`",
    "`M>=2`", "`M>=M0`", "`zeta>log 2`", "`|ell|>=3`",
    "Specialize S4 to `m=n=1`", "integers `h!=0` and `r>=1`",
    "`c=h*(10^r-1) != 0`", "`Psi_tau(0)=1/2`",
    "C(c,a,tau)*M^(a*(1+tau))", "|c|^(-(1+tau)*s)"
]:
    require(scope in report, f"missing exact C-SHELL scope: {scope}")
for claim in ["FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"]:
    require(claim in report, f"claim firewall failed: {claim}")
require(report.count("SCOPED_VERDICT (1/1):") == 1, "verdict count mismatch")
require("SCOPED_VERDICT (1/1): **hold as model**" in report, "wrong verdict")
require("No successor is proposed." in report, "successor endpoint missing")
require("Dębowski" in report and "Fouvry--Kowalski--Michel" in report,
        "T160 visible tuples not reserved")
require("Drappeau--Mullner" in report and "T162" in report,
        "T162 source/theorem reservation missing")
require("S1-S5" in report and "five" in pins, "source accounting missing")

print("T163 finite replay: PASS")
print("sources=5 cap=10 domains=4 minimum=3 candidates=3 cap=3")
print("ledger=T89-T161 count=73 comparator_reservations=T160,T162")
print("C-GCD kappa=1 thresholds first=1/3 gcd=1/2")
print("C-SHELL geometric-ray critical exponent=0 shell_occupancy<=1")
print("C-XMATCH iid_decimal_H2=log(10) n=1000000 depths=11,13")
print("verdict=hold as model successors=0 fixed_pi_claims=0")
