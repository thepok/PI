#!/usr/bin/env python3
"""Self-contained T179 integrity and bounded falsification replay."""

from __future__ import annotations

import csv
import hashlib
import math
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_HASHES = {
    "green-ruzsa-math0505198v2.pdf": "52386eb9e6c3ad51f71f9872365de9ccd361f25532f070e1197112e5c4c815ff",
    "lev-1709.05539v2.pdf": "29228c722ef93d67dbc07e6f77033d8a99a54594434594398f632677f1fca2e2",
    "boshernitzan-frantzikinakis-wierdl-1603.07720v3.pdf": "0fa8457c6809f95984c2d36bce16722d53f0194b37f03331b22f4d948aab07b3",
    "glasscock-et-al-2511.02080v2.pdf": "f31b2d46ec09c123044245f0a814487f0cda3c3e72a477714b143bc873499a87",
    "lee-1508.07109v2.pdf": "1e9d552511797a2b86a9cc319da21856597e401cfd879d4f1a53433fc7a4df17",
    "yau-1707.09707v5.pdf": "2ab4e0ac2820652b5561b8e25e1eab6ea4067d8161ce592a2c737e77ef863ad0",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(word: str, n: int, m: int) -> list[str]:
    assert len(word) == n + m - 1
    return [word[i : i + m] for i in range(n)]


def lag_counts(word: str, n: int, m: int) -> list[int]:
    bs = blocks(word, n, m)
    return [sum(bs[i] == bs[i + r] for i in range(n - r)) for r in range(1, n)]


def collision_energy(word: str, n: int, m: int) -> int:
    bs = blocks(word, n, m)
    return sum(a == b for a in bs for b in bs)


def heavy(lags: list[int], n: int, m: int) -> set[int]:
    q = math.ceil(n / (4 * m))
    return {r for r, count in enumerate(lags, 1) if count >= q}


def additive_energy(values: set[int]) -> int:
    reps: dict[int, int] = {}
    for a in values:
        for b in values:
            reps[a + b] = reps.get(a + b, 0) + 1
    return sum(v * v for v in reps.values())


def debruijn(k: int, alphabet: str = "0123456789") -> str:
    a = [0] * (len(alphabet) * k)
    seq: list[int] = []

    def db(t: int, p: int) -> None:
        if t > k:
            if k % p == 0:
                seq.extend(a[1 : p + 1])
            return
        a[t] = a[t - p]
        db(t + 1, p)
        for j in range(a[t - p] + 1, len(alphabet)):
            a[t] = j
            db(t + 1, t)

    db(1, 1)
    return "".join(alphabet[i] for i in seq)


assert sha(ROOT / "canonical_statement.txt") == CANONICAL_SHA
for name, expected in SOURCE_HASHES.items():
    assert sha(ROOT / name) == expected

source_anchors = {
    "green-ruzsa-math0505198v2.pdf": (15, ["Theorem 1.1.", "CK 4 log(K + 2)"]),
    "lev-1709.05539v2.pdf": (11, ["Theorem 4.", "Pγ (A)", "Proof of Theorem 4"]),
    "boshernitzan-frantzikinakis-wierdl-1603.07720v3.pdf": (
        18,
        ["Khintchine Recurrence Theorem", "Theorem 2.1.", "Theorem 2.2."],
    ),
    "glasscock-et-al-2511.02080v2.pdf": (31, ["Theorem A.", "is not piecewise syndetic"]),
    "lee-1508.07109v2.pdf": (11, ["Theorem 3.2 (Bloom).", "Theorem 3.3 (Chang).", "Lemma 3.5."]),
    "yau-1707.09707v5.pdf": (6, ["Theorem 2.1.", "Lemma 3.2.", "g x1 + g x2"]),
}
for name, (pages, anchors) in source_anchors.items():
    info = subprocess.run(
        ["pdfinfo", str(ROOT / name)], check=True, capture_output=True, text=True
    ).stdout
    assert f"Pages:           {pages}" in info
    text = subprocess.run(
        ["pdftotext", "-layout", str(ROOT / name), "-"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert all(anchor in text for anchor in anchors)

lev_page_9 = subprocess.run(
    ["pdftotext", "-f", "9", "-l", "9", "-layout", str(ROOT / "lev-1709.05539v2.pdf"), "-"],
    check=True,
    capture_output=True,
    text=True,
).stdout
lev_page_10 = subprocess.run(
    ["pdftotext", "-f", "10", "-l", "10", "-layout", str(ROOT / "lev-1709.05539v2.pdf"), "-"],
    check=True,
    capture_output=True,
    text=True,
).stdout
assert "Proof of Theorem 4" not in lev_page_9
assert "Proof of Theorem 4" in lev_page_10

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
required = [
    "PRIMARY_SOURCE_COUNT: 6",
    "PRIMARY_SOURCE_CAP: 8",
    "RETAINED_CANDIDATE_COUNT: 3",
    "RETAINED_CANDIDATE_CAP: 3",
    "RESERVED_ACTIVE_ITEMS: T178",
    "L_m(r;N)=#{i in Z:0<=i<=N-r-1",
    "C_m(N)=#{(i,j):0<=i,j<N",
    "E_+(R)=#{(a,b,c,d) in R^4:a+b=c+d}",
    "m=m_N=floor((1/4)*log_10 N)",
    "SEP-CONSTANT",
    "SEP-PERIODIC",
    "SEP-REPEATED-DE-BRUIJN",
    "SEP-T147-SHARED-PREFIX",
    "SEP-T169-CHAMPERNOWNE",
    "T105 arithmetic difference-set energy",
    "T157 block-difference concentration",
    "T160 recurrence certificates",
    "T162 return separation",
    "T166 finite-word separation and collision packing",
    "equal_factors_start_separation",
    "factorMultiplicity_le_packing",
    "collisionEnergy_le_packing",
    "It does not form the complete threshold set",
    "neither duplicates nor subsumes",
    "T176 repeated-offset analysis",
    "PI-HEAVY-LAG-EXCLUSION-T179",
    "UNPROVED PI-SPECIFIC PREMISE; NOT",
    "SCOPED_VERDICT (1/1): CLOSE.",
    "SUCCESSOR (0/1): NONE.",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
]
assert all(marker in report for marker in required)
assert report.count("SCOPED_VERDICT (1/1):") == 1
assert report.count("SUCCESSOR (0/1):") == 1

with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as f:
    sources = list(csv.DictReader(f))
assert len(sources) == 6 <= 8
assert {row["domain"] for row in sources} == {
    "additive combinatorics",
    "symbolic return-set theory",
    "structured exponential sums",
}
assert sum(row["disposition"].startswith("retained") for row in sources) == 3
assert all(len(row["pdf_sha256"]) == 64 and "p." in row["inspected_range"] for row in sources)
lev = next(row for row in sources if row["id"] == "S2")
assert lev["inspected_range"] == (
    "printed/physical p. 4 for definition and complete theorem statement; "
    "p. 10 for complete proof"
)

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as f:
    exclusions = list(csv.DictReader(f))
assert [row["item"] for row in exclusions] == [f"T{i}" for i in range(89, 179)]
by_item = {row["item"]: row for row in exclusions}
assert by_item["T166"]["verification"] == "MC"
assert by_item["T166"]["source_boundary"] == "Lean declaration readable"
assert "complete heavy-lag set" in by_item["T166"]["T179_disposition"]
assert by_item["T173"]["verification"] == "accepted sketch note"
assert by_item["T174"]["verification"] == "rejected pinned attempt"
assert by_item["T177"]["verification"] == "accepted sketch note"
assert by_item["T178"]["verification"] == "active reserved"

checked = 0
for n in range(8, 81):
    for m in range(1, min(5, n) + 1):
        words = [
            "0" * (n + m - 1),
            ("012" * ((n + m + 1) // 3))[: n + m - 1],
            ("00101" * ((n + m + 3) // 5))[: n + m - 1],
        ]
        for word in words:
            lags = lag_counts(word, n, m)
            energy = collision_energy(word, n, m)
            assert energy == n + 2 * sum(lags)
            rset = heavy(lags, n, m)
            if energy >= n * n / m and m > 0:
                lower = (n + 1 - 2 * m) / (4 * m - 1)
                assert len(rset) + 1e-12 >= lower
            if rset:
                sums = {a + b for a in rset for b in rset}
                assert len(sums) <= 2 * n - 3
                assert additive_energy(rset) * len(sums) >= len(rset) ** 4
            checked += 1

for n in (100, 257, 1000):
    m = max(1, math.floor(math.log10(n) / 4))
    q = math.ceil(n / (4 * m))
    word = "0" * (n + m - 1)
    assert heavy(lag_counts(word, n, m), n, m) == set(range(1, n - q + 1))
    for period in (2, 7, 11):
        pattern = "0" * (period - 1) + "1"
        periodic = (pattern * ((n + m + period) // period))[: n + m - 1]
        if m >= period:
            expected = set(range(period, n - q + 1, period))
            assert heavy(lag_counts(periodic, n, m), n, m) == expected

cycle = debruijn(2)
assert len(cycle) == 100
n, m = 700, 2
q = math.ceil(n / (4 * m))
word = (cycle * 8)[: n + m - 1]
assert heavy(lag_counts(word, n, m), n, m) == set(range(100, n - q + 1, 100))

print("T179 replay: PASS")
print(f"canonical_sha256={CANONICAL_SHA}")
print("primary_sources=6/8 retained_candidates=3/3 domains=3")
print("exclusion_ledger=T89-T178 rows=90 active_reserved=T178 refreshed=T166,T173,T174,T177")
print(f"bounded_word_cases={checked} exact_identity_and_additive_checks=passed")
print("separators=constant,periodic,repeated-de-Bruijn,T147-shared-prefix,T169-range")
print("verdict=close successors=0 fixed_pi_A1_C1_C2_claims=none")
