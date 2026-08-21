#!/usr/bin/env python3
"""Network-free finite replay for the T135 literature audit."""

from __future__ import annotations

import hashlib
import subprocess
import tarfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "madiman-tetali-0901.0044v2.pdf": "761ebe13bb09c631b65fd0b8045b9c6dfc4336ad1c1b96a607a6caae24834234",
    "renyi-1961.pdf": "1f653d4192b783b8b87cc40cff788c17a2d04da9eb766f6614bd6f69339ea6fa",
    "rastegin-1505.03256v3.pdf": "bcbeb10f655b646d59fa61434b7c43de64f26db6c163b058a2bc9ddb70176ee0",
    "shmerkin-1609.07802v3.pdf": "be918d5906a02c1ff17bedcc2cdb15c1c2559c6da2198bf0818b251157d824dd",
    "bourgain-2004-diffie-hellman.pdf": "d508344e2834a5d347c64d04985c293ac9eda205c3ed9f455fde86888545b7e3",
    "prior_evidence.tar.gz": "a34a1c2c6f8c4168065b967cf0889d23f4cb123b95c5a7d17ce015e91446c6dc",
}

PRIOR_MEMBERS = {
    "knowledge_library/t7/FiniteCylinderEnergy.lean": (
        "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
        "piCylinderCollisionEnergy_le_Q_pi_le_three_mul",
    ),
    "knowledge_library/t14/CoherentSuccessorSplitting.lean": (
        "bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833",
        "piPolynomialSmallBallC2_iff_coherentPositiveDensitySplitting",
    ),
    "knowledge_library/t130/prior-t119-REPORT.md": (
        "72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a",
        "## 8. Exact rejection ledger",
    ),
    "knowledge_library/t121/REPORT.md": (
        "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
        "C_m = 2^(-m) sum_S R_S^2",
    ),
    "knowledge_library/t130/REPORT.md": (
        "c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c",
        "PI-SUNIT-RANK",
    ),
    "knowledge_library/t131/REPORT.md": (
        "ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db",
        "## 7. Exact T121 and T122 comparison",
    ),
    "knowledge_library/t133/REPORT.md": (
        "53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40",
        "## 8. Displayed logarithmic-range kill test",
    ),
    "orchestrator-input.json": (
        "6d2b6cb9075ca89626a7bb4c3cd238293f86728c95b51ec940dfe02b4c1c2a71",
        "todo:theory-pi-lacunary-near-return-sparsity:t134",
    ),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pdf_page(name: str, page: int) -> str:
    result = subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), "-layout", str(ROOT / name), "-"],
        check=True,
        capture_output=True,
        text=True,
    )
    return " ".join(result.stdout.split())


def collision(counts: list[int]) -> Fraction:
    total = sum(counts)
    return Fraction(sum(c * c for c in counts), total * total)


for filename, expected in EXPECTED_HASHES.items():
    actual = sha256(ROOT / filename)
    assert actual == expected, (filename, actual, expected)

with tarfile.open(ROOT / "prior_evidence.tar.gz", "r:gz") as archive:
    members = {member.name: member for member in archive.getmembers() if member.isfile()}
    assert set(members) == set(PRIOR_MEMBERS), sorted(members)
    for name, (expected_hash, anchor) in PRIOR_MEMBERS.items():
        stream = archive.extractfile(members[name])
        assert stream is not None, name
        data = stream.read()
        assert hashlib.sha256(data).hexdigest() == expected_hash, name
        assert anchor in data.decode("utf-8"), (name, anchor)
    orchestrator = archive.extractfile(members["orchestrator-input.json"])
    assert orchestrator is not None
    orchestrator_text = orchestrator.read().decode("utf-8")
    assert "todo:theory-pi-lacunary-near-return-sparsity:t132" in orchestrator_text

anchors = [
    ("madiman-tetali-0901.0044v2.pdf", 2, "Definition II"),
    ("madiman-tetali-0901.0044v2.pdf", 5, "Theorem I"),
    ("madiman-tetali-0901.0044v2.pdf", 6, "Proposition II"),
    ("renyi-1961.pdf", 3, "(1.20)"),
    ("renyi-1961.pdf", 7, "THEOREM 2"),
    ("rastegin-1505.03256v3.pdf", 2, "(2.1)"),
    ("rastegin-1505.03256v3.pdf", 8, "Proposition 7"),
    ("shmerkin-1609.07802v3.pdf", 11, "Definition 1.9"),
    ("shmerkin-1609.07802v3.pdf", 12, "Theorem 1.11"),
    ("shmerkin-1609.07802v3.pdf", 38, "Theorem 5.1"),
    ("bourgain-2004-diffie-hellman.pdf", 4, "Theorem 2.1"),
]
for filename, page, anchor in anchors:
    text = pdf_page(filename, page)
    assert anchor in text, (filename, page, anchor)

# Forward tensorization separator: periodic 0000011111 edge law.
full_forward = collision([4, 1, 1, 4])
single = collision([5, 5])
assert full_forward == Fraction(17, 50)
assert single == Fraction(1, 2)
assert full_forward > single * single

# Reverse fractional-partition separator: counts 001:1, 100:1, 101:2.
full_reverse = collision([1, 1, 2])
pair_01 = collision([1, 3])
pair_12 = collision([1, 3])
pair_02 = collision([1, 1, 2])
assert full_reverse == Fraction(3, 8)
assert pair_01 == pair_12 == Fraction(5, 8)
assert pair_02 == Fraction(3, 8)
assert full_reverse * full_reverse < pair_01 * pair_12 * pair_02
assert Fraction(72, 512) < Fraction(75, 512)

# Ordered diagonal-inclusive identity on the first separator.
counts = [4, 1, 1, 4]
ordered_pairs = sum(c * c for c in counts)
assert ordered_pairs == 34
assert ordered_pairs >= sum(counts) == 10
assert Fraction(ordered_pairs, 10 * 10) == full_forward

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
prior_index = (ROOT / "PRIOR_INDEX.md").read_text(encoding="utf-8")

required_report = [
    "PRIMARY_SOURCE_COUNT: 5",
    "PRIMARY_SOURCE_CAP: 10",
    "SEARCHED_DOMAIN_COUNT: 3",
    "RETAINED_CANDIDATE_COUNT: 3",
    "RETAINED_CANDIDATE_CAP: 3",
    "E_[m] <= N^2/(6*A*m)",
    "C-SHEARER",
    "C-SHMERKIN",
    "C-BOURGAIN",
    "T14",
    "T119",
    "T121",
    "T132",
    "T134",
    "T130",
    "T131",
    "T133",
    "UNPROVED PI-TRANSFER PREMISE",
    "FIXED_PI_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
    "SUCCESSOR_COUNT: 0",
]
for marker in required_report:
    assert marker in report, marker

assert report.count("SCOPED_VERDICT:") == 1
assert report.count("SCOPED_VERDICT: HOLD AS MODEL") == 1
assert pins.count("## S") == 5
assert "PRIMARY_SOURCE_COUNT: 5" in pins
assert "PRIMARY_SOURCE_CAP: 10" in pins
assert "RETAINED_CANDIDATE_COUNT: 3" in search
assert "a34a1c2c6f8c4168065b967cf0889d23f4cb123b95c5a7d17ce015e91446c6dc" in prior_index

print("T135 replay: PASS")
print("hashes: 7/7; source page anchors: 11/11; prior members: 8/8")
print("finite separators: forward and reverse Renyi-2 product claims fail")
print("caps: 5 primary sources <= 10; 3 candidates <= 3; domains = 3")
print("scope: one verdict; zero successors; no fixed-pi, C1, or C2 claim")
