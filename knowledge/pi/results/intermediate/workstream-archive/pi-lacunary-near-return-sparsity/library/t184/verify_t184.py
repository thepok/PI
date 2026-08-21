#!/usr/bin/env python3
import csv
import hashlib
import math
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def digest(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


expected = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "medkova-pelantova-vandomme-2002.12593v1.pdf": "9fb2ef592ef0986faaf8e4365dc6505e0387d4a92be026e9fc3e89a6375a22c5",
    "medkova-pelantova-vandomme-2002.12593v1.txt": "25168ffe1b2045c32d7786c016642a88a5b49407fccbd674a2fa55e583b67dd8",
    "T176_SOURCE_LEDGER.csv": "6335969ce09c40fe014f6bbebd726725dfca9779e7b946a23564b0c56b1ecaf1",
    "T180_SOURCE_LEDGER.csv": "964b3b7ba8d3bbe9479015bda7846cd1351c09e966439764bd8b4bd4b476b170",
    "T181_SOURCE_LEDGER.csv": "7c114e1f84337df12b662b075e59ebadf5249525c63fb1a0d78651c5263f9f53",
}
for name, value in expected.items():
    assert digest(name) == value, name
print("PINS: PASS (canonical, primary PDF/text, T176/T180/T181 ledgers)")

source_text = (ROOT / "medkova-pelantova-vandomme-2002.12593v1.txt").read_text()
for anchor in (
    "Definition 1. The non-repetitive complexity",
    "we define the d-bonacci word t as the fixed point",
    "The sequence of the d-bonacci numbers",
    "Theorem 20. Let t be the d-bonacci word",
    "Theorem 21. Let t be the d-bonacci word",
    "Then inrCt (n) = Dk",
):
    assert anchor in source_text, anchor
print("SOURCE_ANCHORS: PASS (Definition 1, morphism, recurrence, Theorems 20-21)")

with (ROOT / "SOURCE_LEDGER.csv").open(newline="") as handle:
    rows = list(csv.DictReader(handle))
assert len(rows) == 1
assert rows[0]["stable_id"] == "arXiv:2002.12593v1"
assert rows[0]["pdf_sha256"] == expected["medkova-pelantova-vandomme-2002.12593v1.pdf"]

prior_ids = {
    "T176": {"1507.02510v1", "2408.14059v1", "1604.02300v1", "2007.15482v2"},
    "T180": {"2504.09650v2", "2603.16794v3", "1802.10355v1", "1407.4100v1"},
    "T181": {"2606.28860v1", "2601.03402v1", "2603.23250v2"},
}
for item, ids in prior_ids.items():
    text = (ROOT / f"{item}_SOURCE_LEDGER.csv").read_text()
    assert all(source_id in text for source_id in ids), item
    assert "2002.12593" not in text, item
with (ROOT / "COMPARISON_LEDGER.csv").open(newline="") as handle:
    comparisons = list(csv.DictReader(handle))
assert [row["comparator"] for row in comparisons] == ["T176", "T180", "T181"]
print("COMPARISONS: PASS (three accepted source/theorem/mechanism boundaries)")


def dnums(d, upto):
    values = {-r: 0 for r in range(2, d + 1)}
    values[-1] = 1
    for k in range(d):
        values[k] = 2**k
    for k in range(d, upto + 1):
        values[k] = sum(values[k - j] for j in range(1, d + 1))
    return values


def endpoints(d, values, k):
    lower_num = sum((d - i) * values[k - i - 2] for i in range(d)) - d
    upper_num = sum((d - i) * values[k - i - 1] for i in range(d)) - d
    assert lower_num % (d - 1) == 0
    assert upper_num % (d - 1) == 0
    return lower_num // (d - 1), upper_num // (d - 1)


for d in range(2, 10):
    values = dnums(d, 45)
    previous_upper = None
    for k in range(1, 35):
        lower, upper = endpoints(d, values, k)
        assert lower < upper
        assert lower == (0 if previous_upper is None else previous_upper)
        previous_upper = upper
        assert values[k + 1] <= 8 * values[k - 2]
        for m in (lower + 1, upper):
            r_plus_one = values[k + 1] - upper + m
            assert 1 <= r_plus_one <= values[k + 1]
            assert d * values[k - 2] < (d - 1) * m + d
            assert values[k + 1] < 16 * m
print("RECURRENCE: PASS (d=2..9, k=1..34, exact endpoints and 16m bound)")


def morphism_word(d, needed):
    word = [0]
    while len(word) < needed:
        image = []
        for value in word:
            image.append(0)
            if value < d - 1:
                image.append(value + 1)
        word = image
    return word


def energy(word, m, n):
    blocks = Counter(tuple(word[i : i + m]) for i in range(n))
    assert sum(blocks.values()) == n
    return sum(value * value for value in blocks.values())


sample_count = 0
for d in range(2, 7):
    values = dnums(d, 30)
    for n in (10**4, 25000, 10**5):
        m = math.floor(math.log10(n) / 4)
        assert m >= 1
        k = 1
        lower, upper = endpoints(d, values, k)
        while not (lower < m <= upper):
            k += 1
            lower, upper = endpoints(d, values, k)
        r_plus_one = values[k + 1] - upper + m
        word = morphism_word(d, n + m - 1)
        observed = energy(word, m, n)
        exact_floor = 2 * (n // r_plus_one)
        uniform_floor = 2 * (n // (16 * m))
        logarithmic_floor = n / (2 * math.log10(n)) - 2
        assert observed - n >= exact_floor >= uniform_floor >= logarithmic_floor
        sample_count += 1
print(f"COLLISIONS: PASS ({sample_count} generated overlapping-prefix cases; diagonal included)")

report = (ROOT / "REPORT.md").read_text()
assert report.count("SCOPED VERDICT (1/1):") == 1
assert report.count("HOLD AS MODEL") == 1
assert report.count("NR-ENERGY-MULTIPLICITY") == 2
for marker in (
    "SCHEDULE: m_N=floor((1/4)*log_10(N))",
    "COLLISION_ORDERING: ordered",
    "COLLISION_DIAGONAL: included",
    "OVERLAP: allowed",
    "WRAPPING: forbidden",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
):
    assert marker in report, marker
print("STRUCTURE: PASS (one verdict, one named gap, endpoint and no-claim markers)")
print("T184_REPLAY: PASS (finite checks are experiment evidence only)")
