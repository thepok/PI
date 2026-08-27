#!/usr/bin/env python3
"""Self-contained finite falsification and package checks for T187."""

import csv
import hashlib
import itertools
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent

PINS = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "boucheron-lugosi-massart-ejp14-690.pdf": "e1cd5fac74d4863df5417a6513bc05aeb5e83408a16a0512d29ac656d9e6a179",
    "boucheron-lugosi-massart-ejp14-690.txt": "15ab5ae9f3edb19705e6c91ce803f9beca7b529b8b65570e7a4d6b0396cd1144",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(word, n, m):
    assert len(word) == n + m - 1
    return [word[i : i + m] for i in range(n)]


def unordered_energy(word, n, m):
    bs = blocks(word, n, m)
    return sum(bs[i] == bs[j] for i in range(n) for j in range(i + 1, n))


def ordered_energy(word, n, m):
    bs = blocks(word, n, m)
    return sum(bs[i] == bs[j] for i in range(n) for j in range(n))


def support(i, m):
    return set(range(i, i + m))


def fractional_drop(word, n, m, r):
    bs = blocks(word, n, m)
    total = Fraction(0)
    for i in range(n):
        for j in range(i + 1, n):
            union = support(i, m) | support(j, m)
            if bs[i] == bs[j] and r in union:
                total += Fraction(1, len(union))
    return total


def fractional_surrogate(word, n, m, r):
    return Fraction(unordered_energy(word, n, m)) - fractional_drop(word, n, m, r)


for name, expected in PINS.items():
    assert sha(ROOT / name) == expected, name

source = (ROOT / "boucheron-lugosi-massart-ejp14-690.txt").read_text(errors="replace")
source_lines = source.splitlines()
assert "obtained by dropping the i-th component" in source_lines[79]
assert "f i (x (i) ) = inf" in source_lines[96]
assert "f i is measurable" in source_lines[102]
assert "Definition 2. A function" in source_lines[108]
assert "a, b > 0" in source_lines[108]
assert "f (x) − f i (x (i) ) ≤ a f (x) + b" in source_lines[117]
assert "Theorem 1. Let X =" in source_lines[161]
assert "For a, b ≥ 0, define c" in source_lines[164]
assert "P {Z ≥ E Z + t}" in source_lines[175]

with (ROOT / "SOURCE_LEDGER.csv").open(newline="") as handle:
    sources = list(csv.DictReader(handle))
assert len(sources) == 1
assert sources[0]["source_id"] == "S1"
assert sources[0]["disposition"] == "obstructed"
assert "measurability" in sources[0]["precise_obstruction"]
assert "m+min(j,m)" in sources[0]["precise_obstruction"]
assert "f_r=(F-d_r)/C" in sources[0]["T187_parameter_substitution"]

required_items = {f"T{i}" for i in range(144, 155)}
required_items |= {f"T{i}" for i in range(159, 173)}
required_items |= {"T177", "T183"}
with (ROOT / "PRIOR_COMPARISON.csv").open(newline="") as handle:
    priors = list(csv.DictReader(handle))
assert len(priors) == 27
assert {row["item"] for row in priors} == required_items
assert all(row["verification_boundary"] and row["normalized_fingerprint"] and row["T187_separation"] for row in priors)
expected_boundaries = {
    "T144": "unverified proof-sketch note",
    "T145": "unverified proof-sketch note",
    "T146": "rejected duplicate fixture",
    "T147": "unverified proof-sketch note",
    "T148": "unverified proof-sketch note",
    "T149": "literature-checked sources with proof-sketch deductions",
    "T150": "literature-checked sources with proof-sketch deductions",
    "T151": "unverified proof-sketch note",
    "T152": "unverified proof-sketch note",
    "T153": "literature-checked sources with proof-sketch deductions",
    "T154": "unverified proof-sketch note",
    "T159": "literature-checked source with unverified proof-sketch deduction",
    "T160": "literature-checked sources with proof-sketch deductions",
    "T161": "unverified proof-sketch note",
    "T162": "literature-checked sources with proof-sketch deductions",
    "T163": "literature-checked sources with proof-sketch deductions",
    "T164": "unverified proof-sketch note",
    "T165": "unverified proof-sketch note",
    "T166": "machine-checked finite-word theorem",
    "T167": "literature-checked sources with proof-sketch screens",
    "T168": "unverified proof-sketch note",
    "T169": "unverified proof-sketch note",
    "T170": "unverified proof-sketch note",
    "T171": "literature-checked sources with proof-sketch screens",
    "T172": "unverified proof-sketch note",
    "T177": "unverified proof-sketch note with pinned sources",
    "T183": "literature-checked source statements with proof-sketch application",
}
assert {row["item"]: row["verification_boundary"] for row in priors} == expected_boundaries

# Exhaustive finite checks: these can falsify but do not prove universal claims.
checked_words = 0
for q in (2, 3, 10):
    n_limit = 4 if q < 10 else 3
    m_limit = 4 if q < 10 else 3
    for n in range(2, n_limit + 1):
        for m in range(1, m_limit + 1):
            for word in itertools.product(range(q), repeat=n + m - 1):
                checked_words += 1
                f = unordered_energy(word, n, m)
                assert ordered_energy(word, n, m) == n + 2 * f
                allocated = sum(
                    (fractional_drop(word, n, m, r) for r in range(n + m - 1)),
                    Fraction(0),
                )
                assert allocated == f

# Exact all-zero/one-flip witness and lower bound over a broader finite grid.
witnesses = 0
for n in range(2, 41):
    for m in range(1, 21):
        x = (0,) * (n + m - 1)
        y = (1,) + (0,) * (n + m - 2)
        assert x[1:] == y[1:]
        sx = fractional_surrogate(x, n, m, 0)
        sy = fractional_surrogate(y, n, m, 0)
        exact_sx = Fraction(n * (n - 1), 2) - sum(
            (Fraction(1, m + min(j, m)) for j in range(1, n)), Fraction(0)
        )
        assert sx == exact_sx
        assert fractional_drop(y, n, m, 0) == 0
        assert sy <= Fraction((n - 1) * (n - 2), 2)
        assert sx - sy >= Fraction(n - 1, 2) > 0
        witnesses += 1

report = (ROOT / "REPORT.md").read_text()
assert report.count("SCOPED RELATED-MODEL VERDICT (1/1):") == 1
for token in (
    "PRIMARY_SOURCE_THEOREM_TUPLE_COUNT: 1",
    "SOURCE_CAP: at most 6",
    "CERTIFICATE_COUNT: 1",
    "N>=100,                   1<=m<=floor(log_10 N)",
    "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
    "UNPROVED TRANSFER REQUIREMENT; NOT\nASSERTED",
    "finite replay is an `experiment`",
):
    assert token in report, token

assert (ROOT / "SHA256SUMS").exists()
manifest_names = set()
for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    assert name != "SHA256SUMS" and sha(ROOT / name) == digest
    manifest_names.add(name)
assert manifest_names == {
    "REPORT.md",
    "SOURCE_LEDGER.csv",
    "PRIOR_COMPARISON.csv",
    "canonical_statement.txt",
    "boucheron-lugosi-massart-ejp14-690.pdf",
    "boucheron-lugosi-massart-ejp14-690.txt",
    "verify_t187.py",
    "raw_output.txt",
}

print("T187 deterministic replay: PASS")
print("canonical statement and sole primary source pins: PASS")
print("source theorem tuples: 1 (cap 6)")
print(f"finite words checked: {checked_words}")
print(f"all-zero/one-flip measurability witnesses checked: {witnesses}")
print("ordered diagonal-inclusive reconstruction: PASS")
print("fractional allocation identity: PASS")
print("fractional surrogate dropped-coordinate invariance: FALSIFIED")
print("required prior comparisons: 27")
print("scoped related-model verdicts: 1")
