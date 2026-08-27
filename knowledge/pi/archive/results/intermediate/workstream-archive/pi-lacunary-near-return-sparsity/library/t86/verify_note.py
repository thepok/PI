#!/usr/bin/env python3
"""Self-contained replay for the T86 literature note.

Finite checks here audit hashes, anchors, and displayed arithmetic only. They
are experiments, not proofs of the canonical universal statement.
"""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent

HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "blmv-2009.pdf": "372d251b5c7c4936ab4e6b9cc6fb3af2ded2c8fe81020ad3e467843c20878e3b",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "hata-1993.pdf": "c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df",
    "lin-deng-chen-2014.pdf": "a39419718fa55af6d4ec64ce8bc833a0fc6b11a983a7df162546a387e3fc4b49",
    "T7FiniteCylinderEnergy.lean": "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
    "T10LongLagResonance.lean": "63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947",
    "T28AdjacentNodeCompatibility.lean": "f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd",
    "T55SignedMultiplierTenPairing.lean": "025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd",
    "T61DirectLabelAdjacentPhaseVariance.lean": "2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb",
    "T64AggregateFejerCriterion.lean": "ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_pdf_text(name: str) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / name), str(out)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return re.sub(r"\s+", " ", out.read_text(errors="replace"))


def odd_part(value: int) -> int:
    while value % 2 == 0:
        value //= 2
    return value


def v_p(value: int, prime: int) -> int:
    count = 0
    while value % prime == 0:
        count += 1
        value //= prime
    return count


for filename, expected in HASHES.items():
    actual = digest(ROOT / filename)
    assert actual == expected, (filename, actual, expected)
print(f"hashes: PASS ({len(HASHES)} pinned inputs)")

canonical = (ROOT / "canonical_statement.txt").read_text()
for anchor in [
    "pairs are ordered and the diagonal is included",
    "for every integer A >= 1",
    "for every integer n >= n_0",
    "there exists an integer N >= 1",
]:
    assert anchor in canonical
print("canonical quantifiers: PASS")

pdf_anchors = {
    "blmv-2009.pdf": [
        "T HEOREM 1.4.",
        "T HEOREM 1.8.",
        "Diophantine-generic",
        "log log N",
    ],
    "zeilberger-zudilin-2020.pdf": [
        "irrationality measure",
        "World record.",
        "7.10320533413700172750577342281",
    ],
    "hata-1993.pdf": [
        "Theorem 1.1.",
        "Rational approximations",
        "linear independence measure",
        "7.016045",
    ],
    "lin-deng-chen-2014.pdf": [
        "The Wallis sequence to which the title refers is",
        "Wallis sequence Wn",
        "asymptotic expansion",
        "here we aim at giving a formula",
    ],
}

for filename, anchors in pdf_anchors.items():
    text = normalized_pdf_text(filename)
    # PDF font maps can insert spaces around mathematical subscripts. Textual
    # anchors are therefore checked after whitespace normalization.
    for anchor in anchors:
        assert anchor in text, (filename, anchor)
print("primary-source text anchors: PASS")

lean_anchors = {
    "T7FiniteCylinderEnergy.lean": [
        "theorem piCylinderCollisionEnergy_le_Q_pi_le_three_mul",
        "theorem canonical_C1_iff_piFiniteCylinderEnergyFrontier",
    ],
    "T10LongLagResonance.lean": [
        "theorem longLagDiscrepancy_implies_resonance",
        "theorem not_canonical_C1_implies_arbitrarily_long_lag_resonance",
        "N = 16 * A * n * K",
        "K ≤ N - r",
        "h ∈ Finset.Icc 1 (256 * A * n)",
        "131072",
    ],
    "T28AdjacentNodeCompatibility.lean": [
        "def AdjacentPairCompatible",
        "def ExponentEightClosingBounds",
        "theorem exponentEight_and_coherentSelection_imply_canonicalA1",
    ],
    "T55SignedMultiplierTenPairing.lean": [
        "def TopShellCorrelationHypothesis",
        "theorem topShellCorrelation_implies_adjacentPairCompatible",
    ],
    "T61DirectLabelAdjacentPhaseVariance.lean": [
        "def DirectLabelAdjacentPhaseVarianceWithExactRemainder",
        "theorem directLabelAdjacentPhaseVariance_implies_strict_t38_threshold",
    ],
    "T64AggregateFejerCriterion.lean": [
        "def parentOrder",
        "def successorOrder",
        "def rowFourierRemainder",
        "theorem boundary_and_fourier_imply_literal_t14_row",
    ],
}
for filename, anchors in lean_anchors.items():
    text = (ROOT / filename).read_text()
    for anchor in anchors:
        assert anchor in text, (filename, anchor)
print("accepted-frontier anchors: PASS")

# The half-threshold transfer denominator in (4.3) is
# 2*pi times the half-threshold denominator 262144.
assert 2 * 262_144 == 524_288
mu = 7.016045
ratio = mu / (mu + 1.0)
assert 0.8752 < ratio < 0.8753
print(f"transfer constants: PASS (Hata exponent ratio {ratio:.9f})")

# Exact Wallis product and reduced denominator formula (7.3)--(7.4).
for s in range(1, 31):
    product = Fraction(1, 1)
    for k in range(1, s + 1):
        product *= Fraction(4 * k * k, 4 * k * k - 1)
    theta = 2 * product
    central = math.comb(2 * s, s)
    displayed = Fraction(2 ** (4 * s + 1), (2 * s + 1) * central * central)
    assert theta == displayed
    assert theta.denominator == odd_part((2 * s + 1) * central * central)
    transient = v_p(theta.denominator, 5)
    modulus = theta.denominator // (5**transient)
    assert math.gcd(modulus, 10) == 1
    assert modulus * 100 * s**4 * (2 * s + 1) ** 2 >= 16**s
    assert modulus <= (2 * s + 1) * 16**s
print("Wallis exact arithmetic: PASS (s=1..30; experiment)")

report = (ROOT / "REPORT.md").read_text()
pins = (ROOT / "SOURCE_PINS.md").read_text()
candidate_headings = re.findall(r"^## \d+\. Candidate \d+:", report, re.MULTILINE)
source_headings = re.findall(r"^## S\d+:", pins, re.MULTILINE)
assert len(candidate_headings) == 3, candidate_headings
assert len(source_headings) == 4, source_headings
for anchor in [
    "N=16AnK",
    "K\\le J=N-r",
    "s_\\delta",
    "\\tag{7.12}",
]:
    assert anchor in report, anchor
for item in ["T63", "T68", "T78", "T79", "T80", "T81", "T82", "T85"]:
    assert re.search(rf"^\| {item} \|", report, re.MULTILINE), item
    assert re.search(rf"^\| {item} \|", pins, re.MULTILINE), item
for label in ["SOURCE THEOREM", "DERIVATION", "CONJECTURE", "HEURISTIC", "EXPERIMENT"]:
    assert label in report, label
terminal = "TERMINAL ENDPOINT: CANDIDATE-COMPLETE QUANTITATIVE NEGATIVE MAP."
assert report.rstrip().endswith(terminal)
assert report.count(terminal) == 1
print("caps, fingerprints, labels, and unique terminal endpoint: PASS")

print("ALL T86 REPLAY CHECKS PASSED")
