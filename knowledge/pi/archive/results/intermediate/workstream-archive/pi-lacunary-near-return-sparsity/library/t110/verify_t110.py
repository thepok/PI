#!/usr/bin/env python3
"""Self-contained integrity and transcription checks for the T110 package."""

from __future__ import annotations

import hashlib
import math
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"

EXPECTED = {
    "canonical_statement.txt": CANONICAL_SHA,
    "konieczny-1611.09985v2.pdf": "92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360",
    "konieczny-1611.09985v2.txt": "ba1c7f0f36212a3b7131c8c8dc82177d21b8dc571a8e03e6b7dd629a14d49f37",
    "fan-konieczny-1806.04267v2.pdf": "e5fdb01f5f1c717cd5733158edcb97cf70d2f4a18f423c9ab6fd8476fb67f114",
    "fan-konieczny-1806.04267v2.txt": "32fcce0f37082dc6f4bc90f8a9e6b191f57864a07d04c9a0342c804a04efc51d",
    "chaubey-yesha-2108.00431v1.pdf": "b660b086d52ecaf9d2e7abe13bcc306765dbc1166076ccb9ddbb14d1461e7e54",
    "chaubey-yesha-2108.00431v1.txt": "97855f7a140140671801c463f10d2d78eb4613a0a70f0407f39f8604013f9043",
    "bkm-2002.09509v3.pdf": "6a55a35657c2d3a95d1d11c8de3c472cd3a650312e7248d70c00e6bb5f54553e",
    "eisner-konieczny-1710.08643v3.pdf": "00627afdff0baef233976eaa09fc367c705f57357eac82740b40b5e033daa4a3",
    "zeilberger-1704.05560v1.pdf": "fc31fd7558c5191f13b00a4e0c8688d5f7b6098a95310471331ebfb6054f3f8b",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(text: str, needle: str, where: str) -> None:
    assert needle in text, f"missing marker in {where}: {needle}"


for name, expected in EXPECTED.items():
    actual = digest(ROOT / name)
    assert actual == expected, f"hash mismatch for {name}: {actual}"

canonical = (ROOT / "canonical_statement.txt").read_text()
for phrase in (
    "pairs are ordered and the diagonal is included",
    "for every integer A >= 1 there exists an integer n_0 >= 1",
    "for every integer n >= n_0, there exists an integer N >= 1",
    "A*n*Q_pi(n,N) <= N^2",
):
    require(canonical, phrase, "canonical_statement.txt")

report = (ROOT / "REPORT.md").read_text()
pins = (ROOT / "SOURCE_PINS.md").read_text()
search = (ROOT / "SEARCH_LOG.md").read_text()

counts = {
    key: int(value)
    for key, value in re.findall(
        r"^(PRIMARY_SOURCE_COUNT|PRIMARY_SOURCE_CAP|SEARCHED_LANE_COUNT|"
        r"CANDIDATE_COUNT|RETAINED_FINGERPRINT_COUNT|CANDIDATE_CAP|"
        r"TERMINAL_VERDICT_COUNT|SUCCESSOR_COUNT): (\d+)$",
        report,
        flags=re.MULTILINE,
    )
}
assert counts["PRIMARY_SOURCE_COUNT"] == 7 <= counts["PRIMARY_SOURCE_CAP"] == 10
assert counts["SEARCHED_LANE_COUNT"] == 3
assert counts["CANDIDATE_COUNT"] == 3 <= counts["CANDIDATE_CAP"] == 3
assert counts["RETAINED_FINGERPRINT_COUNT"] == 2
assert counts["TERMINAL_VERDICT_COUNT"] == 1
assert counts["SUCCESSOR_COUNT"] == 0

assert report.count("TERMINAL VERDICT (1/1):") == 1
assert report.count("## 5. F1:") == 1
assert report.count("## 6. F2:") == 1
assert report.count("## 7. F3:") == 1
for excluded in (
    "T91",
    "T104",
    "T105",
    "active T109",
    "Stoneham family",
    "paperfolding family",
    "Toeplitz family",
    "universal charging",
):
    require(report, excluded, "REPORT.md")

for marker in (
    "H_p = 40*q^3",
    "H_c = 8000*q^3",
    "epsilon_ell(theta)",
    "Gamma_c/sqrt(10) + Gamma_p/2",
    "d=1-theta,       B=1-theta",
    "40q*L_ell(P)/P -> 12",
    "(TM-pi)",
    "(LAC-pi)",
    "(QM-pi)",
    "m0=1",
    "piDecimalEmpiricalMeasure(N(k)) -> nu weakly",
    "Delta^3 10^j=(10-1)^3*10^j=729*10^j",
):
    require(report, marker, "REPORT.md")

assert len(re.findall(r"^## S[1-7]\.", pins, flags=re.MULTILINE)) == 7
require(pins, "INSPECTED_PRIMARY_SOURCE_IDS: S1,S2,S3,S4,S5,S6,S7", "SOURCE_PINS.md")
require(pins, "RETAINED_FINGERPRINT_SOURCE_IDS: S1,S2", "SOURCE_PINS.md")
require(pins, "T104-duplicate comparator", "SOURCE_PINS.md")
require(search, "No result-set paper omitted from that ledger was opened.", "SEARCH_LOG.md")

source_texts = {
    "S1": (ROOT / "konieczny-1611.09985v2.txt").read_text(),
    "S2": (ROOT / "fan-konieczny-1806.04267v2.txt").read_text(),
    "S3": (ROOT / "chaubey-yesha-2108.00431v1.txt").read_text(),
}
for marker in ("Theorem A. Let t", "deg p = s − 1", "large self-correlations"):
    require(source_texts["S1"], marker, "S1 derivative")
for marker in ("Theorem A. Let f", "Theorem B. For any integer s", "q-multiplicative"):
    require(source_texts["S2"], marker, "S2 derivative")
for marker in ("Theorem 1. Let (an )", "k-level correlation", "an+1 ≥ can"):
    require(source_texts["S3"], marker, "S3 derivative")

# Arithmetic checks for the displayed T107 constants and cheap obstructions.
for ell in range(1, 8):
    q = 10**ell
    child_measure = 2 * (10 * q) / (400 * q * q)
    parent_measure = 2 * q / (4 * q * q)
    load = child_measure + 0.5 * parent_measure
    assert math.isclose(load, 3 / (10 * q), rel_tol=0, abs_tol=1e-15)
    assert math.isclose(40 * q * load, 12.0, rel_tol=0, abs_tol=1e-12)
    ac = 2 + math.log(800 * q * q + 1)
    ap = 2 + math.log(40 * q * q + 1)
    theta = 0.5
    epsilon = math.sqrt(theta / (160 * q * (ac * ac + 0.5 * ap * ap)))
    fourier_defect = 160 * q * (ac * ac + 0.5 * ap * ap) * epsilon * epsilon
    assert math.isclose(fourier_defect, theta, rel_tol=1e-12)

for j in range(8):
    assert 10 ** (j + 3) - 3 * 10 ** (j + 2) + 3 * 10 ** (j + 1) - 10**j == 729 * 10**j
for q in range(2, 20):
    assert 10 ** (q + 1) - 10**q - 10 != 0

print("T110 verification passed")
print("primary sources: 7/10; candidates: 3/3; retained fingerprints: 2/3; lanes: 3")
print("terminal verdicts: 1; successors: 0")
print("canonical and source hashes: verified")
print("T107 constants, boundary ratio, and cheap obstruction arithmetic: verified")
