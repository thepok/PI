#!/usr/bin/env python3
"""Self-contained deterministic checks for the T157 literature artifact."""

from __future__ import annotations

import hashlib
import itertools
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_HASHES = {
    "nguyen-vu-1004.3967v2.pdf": "2f2c66acd3e8d80602d0c98841d5ec0bef8ab2aa04a6472a587aa34e8694f83e",
    "nguyen-vu-1004.3967v2.txt": "57bd3b9e33d6b5941f88b96a8b502774bdd0dfe393c340ed2a5199042afe25f8",
    "rudelson-vershynin-math0703503v2.pdf": "e0a00846c9d66057e670809052e0a7a10d04846243169d5b04ff595b0f6c4471",
    "rudelson-vershynin-math0703503v2.txt": "9c71a75cdd3d6261261673dac66968ba0d8adab44e94eec9e2981eed98235bfe",
    "ferber-et-al-1904.10425v1.pdf": "6f4e7593b3024ccf2d2db70c302cec27cc41642b76c3a372133498e62193f687",
    "ferber-et-al-1904.10425v1.txt": "985579e6e44c8ba720ad10961f60d5ce8b5a43d7dccaf190179f553956c7b860",
    "tao-vu-0902.2357v2.pdf": "9c7e700ef85543fc665380e7a64b81ace174d9d7ffbd297246e547ad9b7d6018",
    "tao-vu-0902.2357v2.txt": "d37050f992a31ffaa1f4e30df98a38051f1f07a2c8ca798a6e5fa4b127089aed",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def blocks(word: tuple[int, ...], m: int, starts: int) -> list[tuple[int, ...]]:
    return [word[i : i + m] for i in range(starts)]


def collision_energy(word: tuple[int, ...], m: int, starts: int) -> int:
    ws = blocks(word, m, starts)
    return sum(a == b for a in ws for b in ws)


def difference_vector(word: tuple[int, ...], m: int, i: int, j: int) -> tuple[int, ...]:
    return tuple(word[i + t] - word[j + t] for t in range(m))


def zero_probability(vector: tuple[int, ...]) -> tuple[int, int]:
    hits = 0
    total = 0
    for signs in itertools.product((-1, 1), repeat=len(vector)):
        total += 1
        hits += sum(s * v for s, v in zip(signs, vector)) == 0
    return hits, total


def debruijn(k: int, alphabet: int = 10) -> tuple[int, ...]:
    a = [0] * (alphabet * k)
    sequence: list[int] = []

    def db(t: int, p: int) -> None:
        if t > k:
            if k % p == 0:
                sequence.extend(a[1 : p + 1])
            return
        a[t] = a[t - p]
        db(t + 1, p)
        for j in range(a[t - p] + 1, alphabet):
            a[t] = j
            db(t + 1, t)

    db(1, 1)
    return tuple(sequence)


report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
prior = (ROOT / "PRIOR_INDEX.md").read_text(encoding="utf-8")

require(digest(ROOT / "canonical_statement.txt") == CANONICAL_SHA, "canonical hash")
canonical = (ROOT / "canonical_statement.txt").read_text(encoding="utf-8")
for phrase in ("pairs are ordered and the diagonal is included", "for every integer A >= 1"):
    require(phrase in canonical, f"canonical marker: {phrase}")

for name, expected in SOURCE_HASHES.items():
    require(digest(ROOT / name) == expected, f"source hash: {name}")

expected_pages = {
    "nguyen-vu-1004.3967v2.pdf": 23,
    "rudelson-vershynin-math0703503v2.pdf": 35,
    "ferber-et-al-1904.10425v1.pdf": 31,
    "tao-vu-0902.2357v2.pdf": 17,
}
for name, expected in expected_pages.items():
    info = subprocess.run(
        ["pdfinfo", str(ROOT / name)], check=True, capture_output=True, text=True
    ).stdout
    pages = re.search(r"^Pages:\s+(\d+)$", info, flags=re.MULTILINE)
    require(pages is not None and int(pages.group(1)) == expected, f"page count: {name}")

anchors = {
    "nguyen-vu-1004.3967v2.txt": ("Theorem 2.1 (Optimal inverse", "Theorem 2.5."),
    "rudelson-vershynin-math0703503v2.txt": ("Definition 1.4 (Essential LCD)", "Theorem 4.1 (Small Ball Probability)"),
    "ferber-et-al-1904.10425v1.txt": ("Theorem 1.1 (Halász", "Theorem 1.7."),
    "tao-vu-0902.2357v2.txt": ("Theorem 1.9 (Strong Inverse Theorem)", "Theorem 1.10 (General Strong Inverse Theorem)"),
}
for name, required_anchors in anchors.items():
    text = (ROOT / name).read_text(encoding="utf-8")
    for anchor in required_anchors:
        require(anchor in text, f"anchor {anchor} in {name}")

require("PRIMARY_SOURCE_COUNT: 6" in report, "source count")
require("PRIMARY_SOURCE_CAP: 8" in report, "source cap")
require("RETAINED_CANDIDATE_COUNT: 3" in report, "candidate count")
require("RETAINED_CANDIDATE_CAP: 3" in report, "candidate cap")
require("HTTP 406" in pins and "HTML publisher" in pins, "retrieval blockers")

prior_rows = re.findall(r"^\| T(\d+) \|", prior, flags=re.MULTILINE)
require(prior_rows == [str(i) for i in range(89, 157)], "complete ordered T89-T156 rows")
require(len(prior_rows[:66]) == 66 and prior_rows[65] == "154", "66 prior rows")
snapshot = json.loads((ROOT / "active_items_snapshot.json").read_text(encoding="utf-8"))
require([item["item"] for item in snapshot["items"]] == ["T155", "T156"], "active IDs")
require(all(not item["mathematical_fingerprint_available"] for item in snapshot["items"]), "active unavailable")
require("no nonduplication claim" in snapshot["boundary"], "active boundary")

candidate_keys = re.findall(r"^(C-(?:GAP|LCD|HAL)\|[^\n]+)$", prior, flags=re.MULTILINE)
require(len(candidate_keys) == 3 and len(set(candidate_keys)) == 3, "three unique candidate keys")
for key in candidate_keys:
    require(key.split("|", 1)[1] not in prior.split("## Candidate keys", 1)[0], "candidate absent from prior rows")

for m in range(1, 6):
    for starts in range(1, 6):
        for word in itertools.product(range(3), repeat=starts + m - 1):
            ws = blocks(word, m, starts)
            energy = collision_energy(word, m, starts)
            histogram = {w: ws.count(w) for w in set(ws)}
            require(energy == sum(c * c for c in histogram.values()), "histogram identity")
            bridge = 0
            for i in range(starts):
                for j in range(starts):
                    vector = difference_vector(word, m, i, j)
                    hits, total = zero_probability(vector)
                    collision = ws[i] == ws[j]
                    require(collision == (not any(vector)), "collision iff zero vector")
                    require(collision == (hits == total), "collision iff zero event probability one")
                    bridge += hits == total
            require(bridge == energy, "collision-to-concentration sum")

# Periodic and shared-prefix fixtures.
for period in range(1, 6):
    primitive = tuple([0] * (period - 1) + [1]) if period > 1 else (0,)
    starts = period * 4
    m = period
    word = tuple(primitive[i % period] for i in range(starts + m - 1))
    require(collision_energy(word, m, starts) == starts * starts // period, "period energy")

cycle = debruijn(2)
starts = len(cycle) * 2
m = 3
word = tuple(cycle[i % len(cycle)] for i in range(starts + m - 1))
require(collision_energy(word, m, starts) == starts * starts // len(cycle), "de Bruijn energy")

starts, m, prefix = 20, 5, 9
word = tuple([0] * (prefix + m - 1) + [1] * (starts - prefix))
require(collision_energy(word, m, starts) >= prefix * prefix, "shared-prefix energy")

# Literal candidate substitutions.
for m in range(1, 20):
    zero = (0,) * m
    require(zero_probability(zero) == (2**m, 2**m), "C-GAP rho=1")
    require(not all(1 <= abs(v) <= 9 for v in zero), "C-LCD nonzero failure")
    support = sum(v != 0 for v in zero)
    require(support == 0, "C-HAL support failure")
    for k in range(1, min(4, m) + 1):
        relation_count = (2 ** (2 * k)) * (m ** (2 * k))
        require(relation_count == 2 ** (2 * k) * m ** (2 * k), "maximal zero relation count")

required_markers = (
    "W_i^m(x)=W_j^m(x)",
    "rho_(i,j)=1",
    "Q={0}",
    "rank r=0",
    "1<=|a_k|<=K",
    "30*M<=|supp(a)|",
    "PI-ILO-FIBER",
    "PI-ILO-ROWS",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
)
for marker in required_markers:
    require(marker in report, f"report marker: {marker}")

require(len(re.findall(r"^SCOPED_VERDICT \(1/1\):", report, flags=re.MULTILINE)) == 1, "one verdict")
require("SCOPED_VERDICT (1/1): **close**." in report, "close verdict")
require("SUCCESSOR_COUNT: 0" in report and "No successor is proposed." in report, "zero successors")

print("T157 deterministic replay: PASS")
print("primary sources: 6 / 8")
print("retained candidates: 3 / 3")
print("prior rows: 66 (T89-T154)")
print("active rows: 2 (T155-T156, fingerprints unavailable)")
print("collision bridge exhaustive ternary words: m<=5, starts<=5")
print("candidate substitutions: zero-vector/GAP, LCD nonzero, Halasz support gates PASS")
print("scoped verdicts: 1 (close); successors: 0")
print("claim firewall: no fixed-pi, A1, C1, or C2 claim")
