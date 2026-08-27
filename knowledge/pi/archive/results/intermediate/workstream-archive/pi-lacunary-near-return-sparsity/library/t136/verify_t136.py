#!/usr/bin/env python3
"""Network-free transcription and scope checks for the T136 literature audit."""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
import tarfile
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "coons-evans-manibo-10.4171-dm-880.pdf": "4badf20c29df7d19695675f6aa677b7e609d763c926ff99f30123bfe29fcf034",
    "cassaigne-et-al-2602.21895v1.pdf": "c2b12d420883ea5d4b60f3e7c259b7423cf069e5421b7983daac6b6e7e2076d5",
    "baker-banaji-2602.05593v1.pdf": "74d6e8d0192de706c84ad745b8bb9ce478e9735e8891bdbda3a25a4aeb59504d",
    "baker-khalil-sahlsten-2407.16699v3.pdf": "95f0cc2e23c1c46438b51a331dcc69922cff0c1a266d646e47e2e16c78b8b0a0",
    "ostafe-shparlinski-voloch-2110.10941.pdf": "4ecd0a303f6b0c93953a2df1bd011a59e88a281745dfe363865dd6ace562c934",
    "ostafe-shparlinski-voloch-2211.07739.pdf": "fca26a67b1028436d195e9e1ad0b1e94953d10aea54e492ce80d9569925f2753",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def normalized_pdf_text(path: Path) -> str:
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "source.txt"
        subprocess.run(
            ["pdftotext", "-layout", str(path), str(output)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        text = output.read_text(encoding="utf-8", errors="replace")
    return re.sub(r"\s+", " ", text)


def normalized_pdf_page_text(path: Path, page: int) -> str:
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "source.txt"
        subprocess.run(
            ["pdftotext", "-f", str(page), "-l", str(page), "-layout", str(path), str(output)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        text = output.read_text(encoding="utf-8", errors="replace")
    return re.sub(r"\s+", " ", text)


for filename, expected in EXPECTED.items():
    path = ROOT / filename
    require(path.is_file(), f"missing {filename}")
    require(sha256(path) == expected, f"hash mismatch: {filename}")

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")

markers = {
    "SOURCE_COUNT": 6,
    "DOMAIN_COUNT": 3,
    "SURVIVOR_FINGERPRINT_COUNT": 0,
    "NEGATIVE_CARD_COUNT": 3,
    "SUCCESSOR_COUNT": 0,
    "OVERALL_VERDICT_COUNT": 1,
}
for key, value in markers.items():
    require(report.count(f"{key}: {value}") == 1, f"marker {key}")

require(report.count("OVERALL_VERDICT (1/1): close") == 1, "unique close verdict")
require("OVERALL_VERDICT (1/1): develop" not in report, "develop verdict present")
require("OVERALL_VERDICT (1/1): hold as model" not in report, "hold verdict present")
require(report.rstrip().endswith("OVERALL_VERDICT (1/1): close"), "verdict is not terminal")

for marker in (
    "RETAINED_FINGERPRINTS: none",
    "CONJECTURAL_FIXED_PI_TRANSFER_PREMISES: none",
    "SUCCESSOR: none",
    "FIXED_PI_CLAIM: none",
    "C1_CLAIM: none",
    "C2_CLAIM: none",
    "NOVELTY_CLAIM: none",
):
    require(report.count(marker) == 1, marker)

for card in ("### NEG-M:", "### NEG-F:", "### NEG-X:"):
    require(report.count(card) == 1, card)

for item in ("T130", "T131", "T132", "T133"):
    require(f"| {item}:" in report, f"missing delta card {item}")

for phrase in (
    "Failure of canonical A1 (legacy declaration name mentions",
    "it does not assert the converse for collision-C1/A10",
    "growing-rank and zero-fiber occupancy",
    "cycle-flow rounding/ordering",
    "strict finite projection-majorization model",
    "Close valuation refinement of H1",
    "T134 | zero-fiber occupancy",
    "T135 | Renyi-2 tensorization",
    "inapplicable",
    "quantitatively useless",
    "does not falsify",
):
    require(phrase in report, phrase)

for source_id in ("## M1.", "## M2.", "## F1.", "## F2.", "## X1.", "## X2."):
    require(pins.count(source_id) == 1, source_id)
require(pins.count("- SHA-256:") == 6, "six source hashes")
require("Retrieval blockers: none." in search, "retrieval status")

anchors = {
    "coons-evans-manibo-10.4171-dm-880.pdf": (
        "Spectral Theory of Regular Sequences",
        "Definition 1. We call a k-regular sequence f primitive",
        "Theorem 1. Let f be a primitive real-valued k-regular sequence",
        "Corollary 2. For n",
        "Theorem 5. Let f be a real-valued k-regular sequence",
        "not strong enough to guarantee the existence of a measure",
    ),
    "cassaigne-et-al-2602.21895v1.pdf": (
        "Symbols frequencies in the Thue",
        "Theorem 18. For all n",
        "Proposition 20. Assume that a collection of nonnegative real numbers",
        "Lemma 25. For any s",
        "9 + 2 cos(2",
        "which proves our claim",
    ),
    "baker-banaji-2602.05593v1.pdf": (
        "SELF-SIMILAR AND SELF-CONFORMAL MEASURES WITH SLOW FOURIER DECAY",
        "Theorem 1.3. Letting t be the explicit Liouville number",
        "the measure",
        "is Rajchman but",
        "Theorem 1.7. There exists a monotonically decreasing sequence",
    ),
    "baker-khalil-sahlsten-2407.16699v3.pdf": (
        "FOURIER DECAY FROM L2 -FLATTENING",
        "Definition 1.1. We say that a Borel measure",
        "uniformly affinely non-concentrated",
        "Theorem 1.5",
        "log-contraction ratio",
    ),
    "ostafe-shparlinski-voloch-2110.10941.pdf": (
        "EQUATIONS AND CHARACTER SUMS WITH MATRIX POWERS",
        "Theorem 2.4.",
        "diagonalisable",
        "Remark 2.6.",
        "additional factor log q",
    ),
    "ostafe-shparlinski-voloch-2211.07739.pdf": (
        "WEIL SUMS OVER SMALL SUBGROUPS",
        "Theorem 1.1.",
        "subgroup of order",
        "for some fixed",
    ),
}
for filename, needles in anchors.items():
    text = normalized_pdf_text(ROOT / filename)
    for needle in needles:
        require(needle in text, f"PDF anchor {filename}: {needle}")

m2 = ROOT / "cassaigne-et-al-2602.21895v1.pdf"
proposition_20 = "Proposition 20. Assume that a collection of nonnegative real numbers"
require(proposition_20 not in normalized_pdf_page_text(m2, 24),
        "M2 Proposition 20 unexpectedly appears on printed/PDF p. 24")
require(proposition_20 in normalized_pdf_page_text(m2, 25),
        "M2 Proposition 20 missing from printed/PDF p. 25")
require("printed p. 25, Proposition 20" in pins, "M2 Proposition 20 locator")
require("printed p. 24, Proposition 20" not in pins, "stale M2 locator")
require("do not guarantee that `F_f` is the" in pins,
        "M1 Theorem 5 distribution-function caveat")
require("do not make `F_f` a distribution" in report,
        "M1 report distribution-function caveat")

archive = ROOT / "PRIOR_EVIDENCE.tar"
require(archive.is_file(), "missing prior archive")
with tarfile.open(archive, "r") as tar:
    names = set(tar.getnames())
    required_members = {
        "t104/REPORT.md",
        "t115/REPORT.md",
        "t117/REPORT.md",
        "t118/REPORT.md",
        "t130/REPORT.md",
        "t131/REPORT.md",
        "t132/REPORT.md",
        "t133/REPORT.md",
        "t134/REPORT.md",
        "t135/REPORT.md",
        "t106/FiniteBranchingResonanceTree.lean",
        ".research/orchestrator-escalations.json",
        "orchestrator-input.json",
    }
    require(required_members <= names, "prior archive membership")
    t130 = tar.extractfile("t130/REPORT.md").read().decode("utf-8")
    t131 = tar.extractfile("t131/REPORT.md").read().decode("utf-8")
    t132 = tar.extractfile("t132/REPORT.md").read().decode("utf-8")
    t133 = tar.extractfile("t133/REPORT.md").read().decode("utf-8")
    t134 = tar.extractfile("t134/REPORT.md").read().decode("utf-8")
    t135 = tar.extractfile("t135/REPORT.md").read().decode("utf-8")
    t106 = tar.extractfile("t106/FiniteBranchingResonanceTree.lean").read().decode("utf-8")
    escalation = tar.extractfile(".research/orchestrator-escalations.json").read().decode("utf-8")
    snapshot = tar.extractfile("orchestrator-input.json").read().decode("utf-8")

require("rank `<=2(N+m+2)`" in t130, "T130 rank anchor")
require("zero-block occupancy" in t130, "T130 zero-fiber anchor")
require("Euler ordering:    exact at a full tour" in t131, "T131 Euler anchor")
require("C-MEET strict gain: C=22, G=38, min=44, average=47" not in t132, "raw marker leaked")
for number in ("C=22", "G=38", "min", "average"):
    require(number in report, f"T132 delta number {number}")
require("N asymp log q" in t133, "T133 logarithmic anchor")
require("same substantive burden as T126's unproved" in t133, "T133 continuation anchor")
require("SCOPED_VERDICT (1/1): **close**" in t134, "T134 current verdict")
require("PI-ZERO-OCCUPANCY (`conjecture`; unproved and not asserted)" in t134,
        "T134 conjectural reservation")
require("SCOPED_VERDICT: HOLD AS MODEL" in t135, "T135 current verdict")
require("PI-PROJECTION-TRANSFER-T135 (`conjecture`; UNPROVED PI-TRANSFER PREMISE;" in t135,
        "T135 conjectural reservation")
require("A * n * Q_pi n N ≤ N ^ 2" in t106, "T106 literal A1 type")
require("Change the T106 row to 'Failure of canonical A1'" in escalation, "T129 correction")
for item in ("t134", "t135"):
    require(f'near-return-sparsity:{item}"' in snapshot, f"snapshot lease {item}")

for phrase in (
    "The report's sole scoped verdict is `close`",
    "The report's sole scoped verdict is `HOLD AS MODEL`",
    "Continue excluding zero-block/zero-fiber occupancy",
    "Continue excluding marginal Renyi-2 tensorization",
):
    require(phrase in report, f"refreshed reservation: {phrase}")
for stale in (
    "startup lease only; no readable artifact",
    "no T134/T135 record directory or result is readable",
):
    require(stale not in report, f"stale reservation survived: {stale}")

# Exact exponent substitutions used in NEG-X.
kappa_1 = 1 / 4
require(kappa_1 == 0.25, "kappa_1")
tau_exponent = 1 / 4 + 3 / 4 - kappa_1
require(tau_exponent == 3 / 4, "scalar tau exponent")
for p in (10**8 + 7, 10**12 + 39, 10**16 + 61):
    logp = math.log(p)
    completed_over_trivial = p ** (1 / 8) * logp ** (3 / 4)
    require(completed_over_trivial > 1, "completed bound should exceed trivial scale")

# Bounded checks of the elementary uniform-small-numerator inequality.
for q in (10**8 + 7, 10**10 + 19):
    for length in (1, 2, 3, 4):
        total = sum(complex(math.cos(2 * math.pi * 10**j / q),
                            math.sin(2 * math.pi * 10**j / q)) for j in range(length))
        lhs = abs(total - length)
        rhs = 2 * math.pi * (10**length - 1) / (9 * q)
        require(lhs <= rhs * (1 + 1e-12), "elementary phase inequality")

print("T136 verification: PASS")
print("sources: 6; domains: 3; survivor fingerprints: 0; negative cards: 3")
print("scope: no fixed-pi, C1, or C2 conclusion")
