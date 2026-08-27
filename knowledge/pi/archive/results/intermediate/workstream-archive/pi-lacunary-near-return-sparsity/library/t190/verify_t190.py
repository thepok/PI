#!/usr/bin/env python3
"""Artifact-only structural and pin verifier for T190."""
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()

expected = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "baake-gahler-grimm-1201.1423v1.pdf": "9c6aa8e9a860389480b070e9b2afb4c361895f9e5c0431ebdfe62d9c27b2314c",
    "goc-schaeffer-shallit-1206.5352v1.pdf": "59f53bcb52c4eb696097e0211ea6fd9cc0f0b96129d8ed24f647a4cef02a1667",
    "drappeau-mullner-1710.01091v1.pdf": "241363dacb03315ef512900d82eadd401583a9b1a76ff77c6a31dd452d411074",
}
for name, value in expected.items():
    assert digest(name) == value, name

report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
sources = (ROOT / "SOURCE_LEDGER.csv").read_text(encoding="utf-8")
ledger = (ROOT / "EXCLUSION_LEDGER.csv").read_text(encoding="utf-8")
baake_text = (ROOT / "baake-gahler-grimm-1201.1423v1.txt").read_text(encoding="utf-8")

required_ledger = ["T63", "T68", "T78-T82", "T85", "T164", "T166", "T176", "T181", "T183", "T184", "T185", "T186", "T187", "T188"]
for item in required_ledger:
    assert item in ledger, item
for domain in ["spectral/Fourier explicit substitutions", "factor complexity/collision energy", "automata/transducer/carry-sensitive dynamics"]:
    assert domain in sources, domain
assert sources.count("retained candidate") == 3
assert "source tuples searched = 3 <= 10" in report
assert "symbolic domains searched = 3" in report
assert "retained fingerprints = 3 <= 3" in report
for marker in ["Eq. (11), PDF p. 8", "Theorem 2, PDF p. 3", "Theorem 1, PDF pp. 2-3"]:
    assert marker in sources, marker
for card in ["## C1:", "## C2:", "## C3:"]:
    assert card in report, card
assert report.count("Candidate verdict: CLOSE") == 3
assert report.count("Cheap rejection calculation") == 3
assert report.count("Necessary transfer hypothesis (conjecture)") == 3
assert report.count("BATCH VERDICT (1/1): CLOSE") == 1
assert "surviving candidates = 0" in report
assert "no successor is\nselected" in report
assert "independent of unfinished T189" in report
assert "no T189 artifact" in report
assert "not a proof of any statement\nabout pi" in report
assert "Nothing here is progress on pi, A1, C1, or C2" in report
assert "arXiv:1201.1423v1 [math-ph] 6 Jan 2012" in baake_text
assert "arXiv:1201.1423v1 (6 January 2012)" in report
print("T190 replay: pins, ledger, domains, cards, negative map, and zero-successor endpoint verified")
