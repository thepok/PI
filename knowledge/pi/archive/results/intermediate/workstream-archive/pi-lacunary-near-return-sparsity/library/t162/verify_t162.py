#!/usr/bin/env python3
import csv
import hashlib
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CANONICAL_HASH = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_HASHES = {
    "dvorakova-medkova-pelantova-2003.06916v3.pdf": "db42c488a3bb5f661b78a0c1a21d1ceb3ca139933c01c7862f258f0bd12d6239",
    "dvorakova-medkova-pelantova-2003.06916v3.txt": "96b5822f84d56ee069f7ef75c359cd0945df51924f2a548a1cd4eb3d93e1d333",
    "klouda-et-al-1801.09203v3.pdf": "25dec8d82fead16046c4951c1609a0ab7e25b4e1ae68115d64832559598e0211",
    "klouda-et-al-1801.09203v3.txt": "e76c24bed42876329376b59533eea8b18cd8a8fa44b18498c0c561cf11910a8e",
    "drappeau-mullner-1710.01091v1.pdf": "241363dacb03315ef512900d82eadd401583a9b1a76ff77c6a31dd452d411074",
    "drappeau-mullner-1710.01091v1.txt": "d64ad8af80f222f9220df2d9235d35e8e318cdc7318cec689c31bb20c8977d1e",
}


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def stats(word, starts, depth):
    blocks = [word[i:i + depth] for i in range(starts)]
    counts = {}
    positions = {}
    for i, block in enumerate(blocks):
        counts[block] = counts.get(block, 0) + 1
        positions.setdefault(block, []).append(i)
    energy = sum(v * v for v in counts.values())
    cmax = max(counts.values())
    gaps = [b - a for pos in positions.values() for a, b in zip(pos, pos[1:])]
    gap = min(gaps) if gaps else float("inf")
    return cmax, energy, gap


def debruijn(k, n):
    a = [0] * (k * n)
    sequence = []

    def db(t, p):
        if t > n:
            if n % p == 0:
                sequence.extend(a[1:p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, k):
                a[t] = j
                db(t + 1, t)

    db(1, 1)
    return "".join(str(x) for x in sequence)


assert digest("canonical_statement.txt") == CANONICAL_HASH
for name, expected in SOURCE_HASHES.items():
    assert digest(name) == expected, name

report = (ROOT / "REPORT.md").read_text()
pins = (ROOT / "SOURCE_PINS.md").read_text()
assert report.count("SCOPED_VERDICT (1/1):") == 1
assert report.count("SUCCESSOR (0/1): none") == 1
assert "PRIMARY_SOURCE_COUNT: 3" in report and "PRIMARY_SOURCE_CAP: 8" in report
assert "RETAINED_CANDIDATE_COUNT: 3" in report and "RETAINED_CANDIDATE_CAP: 3" in report
assert "SEPARATOR_TEST_COUNT: 5" in report
for marker in ["FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"]:
    assert marker in report
for marker in ["C-RET", "C-DER", "C-AUT", "g_m>=K*A*m", "M>=K*A*m", "m<=floor(kappa log_10 M)"]:
    assert marker in report
for marker in ["Definition1;Lemma3;Definition39;Observation40;Lemma41;Theorem54",
               "Section2.1;Theorem1;Definition22;Theorem25;Example27;Corollary35",
               "Definition1;Theorem1(1.2)-(1.3);Definition2;Proposition1(4.1)"]:
    assert marker in pins

source_anchors = {
    "dvorakova-medkova-pelantova-2003.06916v3.txt": [
        "Definition 1. The critical exponent", "Lemma 3. Let u be a uniformly recurrent",
        "Definition 39. Let u be a uniformly recurrent", "Observation 40.",
        "Lemma 41. Let u be a uniformly recurrent", "Theorem 54. Let v be a CS Rote sequence",
    ],
    "klouda-et-al-1801.09203v3.txt": [
        "2.1. Derivated words.", "Theorem 1. If u is a Sturmian word",
        "Definition 22.", "Theorem 25.", "Example 27.", "Corollary 35.",
    ],
    "drappeau-mullner-1710.01091v1.txt": [
        "Definition 1. Let f", "Theorem 1. Let (an ) be an automatic sequence",
        "Definition 2. A function f", "Proposition 1. Let g",
    ],
}
for name, anchors in source_anchors.items():
    text = (ROOT / name).read_text()
    for anchor in anchors:
        assert anchor in text, (name, anchor)

with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="") as handle:
    rows = list(csv.DictReader(handle))
items = [row["item"] for row in rows]
assert items == [f"T{i}" for i in range(89, 162)]
assert "accepted changed evidence" in rows[69]["T162_disposition"]
assert rows[70]["verification"] == "PS/EXP indexed/unavailable"
assert "import no claim" in rows[70]["T162_disposition"]
assert rows[71]["verification"] == "pipeline-revised/unavailable"
assert rows[72]["verification"] == "PS/EXP accepted note"
assert "import no claim" in rows[71]["T162_disposition"]
assert "import no claim" in rows[72]["T162_disposition"]

# Exhaustive finite check of the elementary gap implication over binary words.
checked = 0
for length in range(2, 10):
    for bits in product("01", repeat=length):
        word = "".join(bits)
        for depth in range(1, length + 1):
            starts = length - depth + 1
            cmax, energy, gap = stats(word, starts, depth)
            if gap != float("inf"):
                assert cmax <= 1 + (starts - 1) // gap
            for A in (1, 2):
                K = 2
                if starts >= K * A * depth and gap >= K * A * depth:
                    assert energy * A * depth <= starts * starts
            checked += 1

# SPT1 constant.
M, m = 30, 4
cmax, energy, gap = stats("0" * (M + m - 1), M, m)
assert (cmax, energy, gap) == (M, M * M, 1)

# SPT2 primitive period 2. One period has no repeated phase; J >= 2 does.
M, m = 2, 5
word = ("01" * 10)[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert (cmax, energy, gap) == (1, M, float("inf"))
M, m = 24, 5
word = ("01" * 20)[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert (cmax, energy, gap) == (M // 2, M * M // 2, 2)

# SPT3 binary de Bruijn analogue: one cycle has no repeated phase; J >= 2 does.
cycle = debruijn(2, 3)
M, m = len(cycle), 6
word = (cycle * 10)[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert (cmax, energy, gap) == (1, M, float("inf"))
M, m = 32, 6
word = (cycle * 10)[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert len(cycle) == 8 and (cmax, energy, gap) == (4, 128, 8)

# SPT4 shared prefix.
M, m, R = 40, 5, 12
suffix = (debruijn(2, 4) * 10)
word = ("0" * (R + m - 1) + suffix)[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert cmax >= R and energy >= R * R and gap == 1

# SPT5 bounded multi-core; actual global gap sees within- and cross-core pairs.
M, m = 36, 4
word = (("01" * 12) + ("23" * 12))[:M + m - 1]
cmax, energy, gap = stats(word, M, m)
assert gap == 2 and cmax >= 9 and energy >= 162

print("T162_REPLAY: PASS")
print("PRIMARY_SOURCE_COUNT: 3/8")
print("RETAINED_CANDIDATE_COUNT: 3/3")
print("LEDGER_RANGE: T89-T161 (73 rows)")
print(f"FINITE_GAP_CASES: {checked}")
print("SEPARATORS: constant periodic repeated-debruijn shared-prefix bounded-multicore")
print("SCOPED_VERDICT_COUNT: 1")
print("SUCCESSOR_COUNT: 0")
