#!/usr/bin/env python3
"""Self-contained deterministic checks for the T183 literature package."""

import csv
import hashlib
import itertools
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent

PINS = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "boucheron-lugosi-massart-ejp14-690.pdf": "e1cd5fac74d4863df5417a6513bc05aeb5e83408a16a0512d29ac656d9e6a179",
    "boucheron-lugosi-massart-ejp14-690.txt": "15ab5ae9f3edb19705e6c91ce803f9beca7b529b8b65570e7a4d6b0396cd1144",
    "duchemin-decastro-lacour-2011.11435v4.pdf": "37bf65e3979f964ebdf9fd75d25f578de8e096d8db87514cc3c89c34ac57e135",
    "duchemin-decastro-lacour-2011.11435v4.txt": "9c5972d645566bfcaad7fb7514176eb427d14ebf8e7195de1e25f96272fea4e7",
    "hsu-kakade-zhang-1110.2842v1.pdf": "25c384d7416d1b7f3938f58a970cc06220667ec8fe57271ea7da9244a98287f9",
    "hsu-kakade-zhang-1110.2842v1.txt": "10883c58db2b449ca445a2fd9d3e773302204c866e98157206a5f73e0c1a596d",
    "lyons-peres-2020-corrected.pdf": "3ba07bc0fb0397dc256610b328c869983d7ab4f709c78952d86646e25a15d043",
    "lyons-peres-2020-corrected.txt": "3f734a0413e5250be19bb227bcae28aec26350eb878101d03ba1496954aaad7a",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blocks(word, n, m):
    return [word[i : i + m] for i in range(n)]


def energy(word, n, m):
    bs = blocks(word, n, m)
    return sum(a == b for a in bs for b in bs)


def unordered_energy(word, n, m):
    bs = blocks(word, n, m)
    return sum(bs[i] == bs[j] for i in range(n) for j in range(i + 1, n))


def deleted_unordered(word, n, m, r):
    bs = blocks(word, n, m)
    return sum(
        bs[i] == bs[j]
        for i in range(n)
        for j in range(i + 1, n)
        if not (i <= r < i + m or j <= r < j + m)
    )


for name, expected in PINS.items():
    assert sha(ROOT / name) == expected, name

blm = (ROOT / "boucheron-lugosi-massart-ejp14-690.txt").read_text(errors="replace")
ddl = (ROOT / "duchemin-decastro-lacour-2011.11435v4.txt").read_text(errors="replace")
hkz = (ROOT / "hsu-kakade-zhang-1110.2842v1.txt").read_text(errors="replace")
lyons = (ROOT / "lyons-peres-2020-corrected.txt").read_text(errors="replace")
assert "Definition 2. A function" in blm and "Theorem 1. Let X =" in blm
assert "Proof of Theorem 1. The upper-tail inequality" in blm
assert "For a, b ≥ 0, define c" in blm
assert "Assumption 2 can be read as a reverse Doeblin" in ddl
assert "Theorem 2. We suppose Assumptions 1, 2 and 3" in ddl
assert "4.1.2   Proof of Theorem 2" in ddl
assert "Theorem 1. Let A" in hkz and "Proof of Theorem 1." in hkz
assert "Theorem 13.35. (Bounded-Di" in lyons

with (ROOT / "SOURCE_LEDGER.csv").open(newline="") as f:
    sources = list(csv.DictReader(f))
assert len(sources) == 3
domains = {row["domain"] for row in sources}
assert domains == {
    "dependent_or_local_U_statistics",
    "polynomial_chaos_or_quadratic_form_concentration",
    "entropy_method_self_bounding_read_k_or_variance_sensitive_martingale",
}
required_fields = {
    "growing_m", "overlap", "all_pairs_quadratic_statistic", "deviation_size",
    "constants", "effectivity", "uniformity", "obstruction_class",
}
assert required_fields <= set(sources[0])
assert all(all(row[field] for field in required_fields) for row in sources)
assert sum(row["disposition"] == "retained" for row in sources) == 1

with (ROOT / "PRIOR_COMPARISON.csv").open(newline="") as f:
    priors = list(csv.DictReader(f))
expected_priors = {"T144", "T147", "T150", "T152", "T154", "T159", "T161", "T168", "T170", "T172", "T174", "T177"}
assert {row["item"] for row in priors} == expected_priors and len(priors) == 12
assert all(row["verification_boundary"] and row["normalized_fingerprint"] and row["T183_separation"] for row in priors)

# Exhaustively verify the overlap probability count for small alphabets.
for q in (2, 3):
    for m in range(1, 5):
        for h in range(1, 5):
            good = 0
            for word in itertools.product(range(q), repeat=m + h):
                good += word[:m] == word[h : h + m]
            assert good == q**h

# Exhaustively verify E=N+2F and the deletion self-bounding certificate.
for q in (2, 3):
    for n in range(1, 5):
        for m in range(1, 4):
            for word in itertools.product(range(q), repeat=n + m - 1):
                e = energy(word, n, m)
                f = unordered_energy(word, n, m)
                assert e == n + 2 * f
                drops = []
                for r in range(n + m - 1):
                    drop = f - deleted_unordered(word, n, m, r)
                    assert 0 <= drop <= m * n
                    drops.append(drop)
                assert sum(drops) <= 2 * m * f

# Check the safe algebraic denominator bound used for gamma=3.
for a in range(1, 8):
    for m in range(1, 12):
        for n in (4 * a * m, 4 * a * m + 1, 10 * a * m):
            ef_upper = n * n / (4 * a * m)
            u = n * n / (4 * a * m)
            denominator = 4 * m * m * n * ef_upper + 2 * m * (m - 1 / 6) * n * u
            exponent = u * u / denominator
            assert exponent + 1e-12 >= n / (24 * a * m**3)
            assert n / (24 * a * m**3) >= n / (24 * a * a * m**3)

# The depth ratio grows on an exact integer subsequence.
ratios = []
for k in (24, 36, 48, 60):
    n = 2**k
    a = 1
    log_ceiling = math.ceil(math.log(n))
    m1 = int((n / (96 * a * a * log_ceiling)) ** (1 / 3))
    while 96 * a * a * (m1 + 1) ** 3 * log_ceiling <= n:
        m1 += 1
    while 96 * a * a * m1**3 * log_ceiling > n:
        m1 -= 1
    m0 = math.floor((n / (64 * a * a * math.log(n))) ** 0.25)
    ratios.append(m1 / m0)
assert all(x < y for x, y in zip(ratios, ratios[1:]))

report = (ROOT / "REPORT.md").read_text()
assert report.count("SCOPED VERDICT (1/1):") == 1
assert "SCOPED VERDICT (1/1): DEVELOP." in report
assert report.count("BOUNDED SUCCESSOR (1/1, authorized after the verdict):") == 1
for token in (
    "PRIMARY_SOURCE_THEOREM_TUPLE_COUNT: 3", "SEARCHED_DOMAIN_COUNT: 3",
    "gamma=3<4", "M1/M0 -> infinity", "FIXED_PI_CLAIM: none",
    "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none",
    "G11_CLAIM: none", "G19_CLAIM: none", "iid related-model mathematics",
    "then let\n`b` decrease to zero",
):
    assert token in report, token

if (ROOT / "SHA256SUMS").exists():
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        assert name != "SHA256SUMS" and sha(ROOT / name) == digest

print("T183 deterministic replay: PASS")
print("canonical statement pin: PASS")
print("source theorem tuples: 3; supported domains: 3")
print("exact overlap counts and expectation identity: PASS")
print("McDiarmid baseline guardrails: PASS")
print("self-bounding certificate and gamma=3 algebra: PASS")
print("required prior comparisons: 12")
print("scoped verdicts: 1; bounded successors: 1")
