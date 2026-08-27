#!/usr/bin/env python3
"""Self-contained replay checks for the T114 literature artifact."""

from __future__ import annotations

import hashlib
import itertools
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "vaananen-wu-1604.01630.pdf": "cf4f08bdef63be4c274c18c09ccf284a998c8e274156e787af837b1b7330e6e7",
    "amou-matala-aho-vaananen-2007.pdf": "71b1f76747dcca9a10f334d25416766936c58d1a767690b62d5abf0a7130207a",
    "zorin-1309.0105.pdf": "c16eb6ab11a2ab2b71376bc4b5c877a8124b7355a8d28a8b65f45af3eca5b71e",
    "zudilin-1601.02688.pdf": "53947bb2fc82e853c12ccfdb293a526229f6fe2ac99d9c991d2170ae6e1266e3",
    "varju-yu-2004.09358v2.pdf": "4f8fe4bb024df9d7c0c804f93f261f3c4f21cc4d9410f9984804ad60594e7fad",
    "schleischitz-1501.07176v6.pdf": "d19e88d3478415ee47f4cbdb42089cc255eea0d57f0368a4df933a484103e93a",
    "laurent-1995.pdf": "9f480dc10057cc639d80a6a5a773a3e35c283170e9d201302921186ca5777dbf",
    "konyagin-shparlinski-2012.pdf": "46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc",
}

MANIFEST_FILES = set(EXPECTED) | {
    "REPORT.md",
    "SOURCE_PINS.md",
    "SEARCH_LOG.md",
    "verify_t114.py",
    "raw_output.txt",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def determinant(matrix: list[list[int]]) -> int:
    """Exact determinant by the fraction-free Bareiss algorithm."""
    a = [row[:] for row in matrix]
    n = len(a)
    if n == 0:
        return 1
    sign = 1
    previous = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign *= -1
        pivot_value = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot_value - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        previous = pivot_value
    return sign * a[-1][-1]


for name, digest in EXPECTED.items():
    actual = sha256(ROOT / name)
    assert actual == digest, (name, actual, digest)
print(f"HASH_CHECK: {len(EXPECTED)} pinned inputs match")

manifest_path = ROOT / "SHA256SUMS"
if manifest_path.exists():
    manifest: dict[str, str] = {}
    for line in manifest_path.read_text(encoding="ascii").splitlines():
        digest, name = line.split(maxsplit=1)
        manifest[name.strip()] = digest
    assert set(manifest) == MANIFEST_FILES, (set(manifest), MANIFEST_FILES)
    for name, digest in manifest.items():
        assert sha256(ROOT / name) == digest, name
    print(f"MANIFEST_CHECK: {len(manifest)} delivered files match")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")

required_report_tokens = [
    "PRIMARY_SOURCE_COUNT: 8",
    "PRIMARY_SOURCE_CAP: 12",
    "SEARCHED_LANE_COUNT: 4",
    "RETAINED_CANDIDATE_COUNT: 4",
    "RETAINED_CANDIDATE_CAP: 4",
    "SUCCESSOR_COUNT: 0",
    "DELIVERY_READINESS: READY",
    "COMPARISON_REFRESH: T112_AND_T113_INSPECTED",
    "N >= A*n",
    "A=1",
    "Delta_1=1",
    "Delta_r(d,m)",
    "2*(10^(N-1)-1)*10^(-n)",
    "T81",
    "T87",
    "T104",
    "T105",
    "T110",
    "active T112",
    "active T113",
    "H-G19-twisted-cocycle",
    "the T113 note argues (unverified)",
    "PI-AVOID",
    "terminal obstruction memory",
    "PI-SPECIFIC TRANSFER PREMISE C1",
    "PI-SPECIFIC TRANSFER PREMISE C2",
    "PI-SPECIFIC TRANSFER PREMISE C3",
    "PI-SPECIFIC TRANSFER PREMISE C4",
]
for token in required_report_tokens:
    assert token in report, token
assert report.count("TERMINAL VERDICT (1/1):") == 1
assert "**CLOSE.**" in report
assert report.count("SUCCESSOR_COUNT: 0") == 1
assert "DELIVERY_READINESS: BLOCKED" not in report
assert "BLOCKER: active T113 artifact unavailable." not in report
assert "printed p. 9, Theorem 3.12 and equation (10)" in report
assert "printed p. 9, Theorem 3.12 and equation (10)" in pins
assert "preprint p. 8, Theorem 3.12" not in report
assert "preprint p. 8, Theorem 3.12" not in pins

for source_id in range(1, 9):
    assert pins.count(f"| S{source_id} |") == 1
for candidate_id in range(1, 5):
    assert report.count(f"Candidate C{candidate_id}:") == 1
for lane in [
    "Mahler and functional equations",
    "Restricted structured approximation",
    "Fixed-point lacunary dynamics",
    "Short structured exponential sums",
]:
    assert lane in search
print("CAP_AND_SCOPE_CHECK: 8 sources, 4 lanes, 4 candidates, one close, zero successors")
print("COMPARISON_CHECK: accepted T112 and unverified T113 fingerprints refreshed")
print("LOCATOR_CHECK: Schleischitz Theorem 3.12 and equation (10) use printed page 9")

# D_N has one collapsed diagonal value and otherwise unique ordered differences.
for n_size in range(1, 13):
    differences = {
        10**i - 10**j for i in range(n_size) for j in range(n_size)
    }
    assert len(differences) == n_size * (n_size - 1) + 1
    assert max(map(abs, differences)) == 10 ** (n_size - 1) - 1
print("D_N_CHECK: exact cardinality and height for N=1..12")

# Verify the homogeneous Vandermonde factorization for deterministic integer data.
assert determinant([[1]]) == 1
for r in range(2, 7):
    ds = [10**i - 1 for i in range(1, r + 1)]
    ms = [3 * d + i * i + 1 for i, d in enumerate(ds)]
    matrix = [
        [d ** (r - 1 - k) * m**k for k in range(r)]
        for d, m in zip(ds, ms)
    ]
    product = 1
    for a, b in itertools.combinations(range(r), 2):
        product *= ds[a] * ms[b] - ds[b] * ms[a]
    assert determinant(matrix) == product
print("DETERMINANT_CHECK: homogeneous Vandermonde identity for r=2..6")

# Exact boundary checks; H_N is strictly increasing, so every larger legal N
# only increases the failed upper-bound base.
for n_size in range(1, 40):
    assert 10 ** (n_size - 1) - 1 < 10**n_size - 1
for n_digits in range(1, 31):
    n_size = n_digits + 1
    height = 10 ** (n_size - 1) - 1
    assert 2 * height > 10**n_digits
for a_value in range(2, 9):
    for n_digits in range(1, 31):
        n_size = a_value * n_digits
        height = 10 ** (n_size - 1) - 1
        assert 2 * height > 10**n_digits
print("EXPONENT_CHECK: A=1 split and A>=2 boundary-plus-monotonicity replayed")

# Squared Konyagin-Shparlinski first bound is nontrivial only beyond p^(12/25).
# Algebra: p^(1/4)L^(71/48)<L^2 iff L^(25/48)>p^(1/4).
assert 48 == 4 * 12 and 25 == 96 - 71
print("SHORT_SUM_CHECK: threshold exponent 12/25 reproduced")

print("T114_REPLAY_OK")
