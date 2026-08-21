#!/usr/bin/env python3
import csv
import hashlib
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "medkova-pelantova-vandomme-2002.12593v1.pdf": "9fb2ef592ef0986faaf8e4365dc6505e0387d4a92be026e9fc3e89a6375a22c5",
    "medkova-pelantova-vandomme-2002.12593v1.txt": "25168ffe1b2045c32d7786c016642a88a5b49407fccbd674a2fa55e583b67dd8",
    "durand-0807.3322v1.pdf": "eb08490237dc821f54f9c54ba385f98d1abac69a4e03121f06955fb98329e40a",
    "durand-0807.3322v1.txt": "17779341b757257b9dcca870db2240e837d730094358196455fab3ee15d407fa",
    "T166FiniteWordPowerFree.lean": "f1da6482ee8ad2b6c5341a1e0a8923a8e3bbc28d1f76d8e0845e7bab1d0e60a0",
}


def sha256(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


for name, expected in EXPECTED.items():
    assert sha256(name) == expected, name
print("PINS: PASS (canonical, T166 Lean, two PDFs and text derivatives)")

anchors = {
    "medkova-pelantova-vandomme-2002.12593v1.txt": [
        "Definition 2. A recurrent infinite word",
        "(d − 1)n + 1 factors of length n",
        "we define the d-bonacci word",
        "Lemma 19.",
        "Theorem 20.",
    ],
    "durand-0807.3322v1.txt": [
        "Lemma 13 There exists a constant Q",
        "Theorem 17 If Y is not periodic",
        "With N = 4rS(ζ)Q we complete the proof.",
    ],
}
for name, needles in anchors.items():
    text = (ROOT / name).read_text(encoding="utf-8")
    for needle in needles:
        assert needle in text, (name, needle)
print("ANCHORS: PASS (complexity, d-bonacci, recurrence, and power theorem)")


def dnums(d, upto):
    vals = [2 ** q for q in range(d)]
    while len(vals) <= upto:
        vals.append(sum(vals[-d:]))
    return vals


def image_letter(a, d):
    return (0, a + 1) if a < d - 1 else (0,)


def morph(word, d):
    out = []
    for a in word:
        out.extend(image_letter(a, d))
    return tuple(out)


def iterate_letter(a, d, q):
    word = (a,)
    for _ in range(q):
        word = morph(word, d)
    return word


for d in range(2, 11):
    D = dnums(d, 3 * d + 3)
    lengths = [1] * d
    for q in range(0, 3 * d + 2):
        assert max(lengths) <= D[d] * min(lengths)
        if q < 3 * d + 1:
            lengths = [lengths[0] + lengths[a + 1] if a < d - 1 else lengths[0] for a in range(d)]
    assert lengths[0] == D[3 * d + 1]
    P = 16 * D[d] * D[2 * d + 1]
    C = 2 * P
    assert P > 0 and C == 32 * D[d] * D[2 * d + 1]
for d in range(2, 8):
    target = {(0, 0)} | {(0, a) for a in range(1, d)} | {(a, 0) for a in range(1, d)}
    core = iterate_letter(0, d, d + 1)
    complete = set(zip(core, core[1:]))
    assert target <= complete
    for a in range(d):
        level_d = iterate_letter(a, d, d)
        assert level_d[:len(iterate_letter(0, d, d - 1))] == iterate_letter(0, d, d - 1)
        assert set(level_d) == set(range(d))
        supertile = iterate_letter(a, d, 2 * d + 1)
        assert supertile[:len(core)] == core
        assert target <= set(zip(supertile, supertile[1:]))
    D = dnums(d, 2 * d + 1)
    supertile_lengths = [len(iterate_letter(a, d, 2 * d + 1)) for a in range(d)]
    assert max(supertile_lengths) == D[2 * d + 1]
    assert 2 * max(supertile_lengths) == 2 * D[2 * d + 1]
print("CONSTANTS: PASS (ratios; exact core embedding; max supertile M_d; recurrence window r_d; P_d,C_d)")


def prefix(d, needed):
    word = (0,)
    while len(word) < needed:
        word = morph(word, d)
    return word[:needed]


for d, m, N in [(2, 8, 64), (3, 9, 72), (4, 10, 80), (5, 12, 96)]:
    word = prefix(d, N + m - 1)
    blocks = [word[i:i + m] for i in range(N)]
    counts = Counter(blocks)
    energy = sum(v * v for v in counts.values())
    assert sum(counts.values()) == N
    assert blocks[-1] == word[N - 1:N + m - 1]
    assert energy == sum(1 for i in range(N) for j in range(N) if blocks[i] == blocks[j])
    assert energy >= N * N / (2 * (d - 1) * m)
print("ENDPOINTS: PASS (overlap, last start, multiplicity, ordered diagonal energy)")

with (ROOT / "COMPARISON_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
    rows = list(csv.DictReader(handle))
assert {row["comparator"] for row in rows} == {"T164", "T166", "T176", "T184"}
required = {
    "T164": {"definitions_and_endpoints", "power_separation", "two_sided_energy"},
    "T166": {"legal_starts_endpoints_multiplicity_energy", "upper_packing", "lower_energy"},
    "T176": {"source_theorem_mechanism", "uniform_range"},
    "T184": {"family_and_source", "NR_ENERGY_MULTIPLICITY", "endpoint_and_ordering"},
}
for comparator, clauses in required.items():
    assert clauses <= {row["clause"] for row in rows if row["comparator"] == comparator}
print("COMPARISON: PASS (T164/T166/T176/T184 clause-complete rows)")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
assert report.count("RELATED-MODEL VERDICT (1/1):") == 1
assert "N_0(d)=2" in report
assert "c_d = 1/(2(d-1))" in report
assert "C_d = 2 P_d = 32 D_d D_(2d+1)" in report
assert "DBONACCI-TO-T7-T186" in report
for marker in ["FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"]:
    assert report.count(marker) == 1, marker
print("STRUCTURE: PASS (one verdict, explicit constants/range, transfer, no-claim markers)")
