#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parent


def sha256(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


expected_hashes = {
    "canonical_statement.txt":
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "EXTERNAL_FEEDBACK_2026-08-09.md":
        "78f63c13803e4860b513fae245d1ec5e77e8decd233ec287f2acd1da5516bd20",
}

for name, expected in expected_hashes.items():
    actual = sha256(name)
    assert actual == expected, f"{name}: expected {expected}, got {actual}"

lean = (ROOT / "T83LiteralStatisticAudit.lean").read_text(encoding="utf-8")
report = (ROOT / "REPORT.md").read_text(encoding="utf-8")

required_lean = [
    "namespace DecimalFactorComplexity.T83LiteralStatisticAudit",
    "theorem literal_C7_iff_quantifiers",
    "theorem literal_C7_iff_nearReturn_linear",
    "theorem literal_short_sector_range",
    "theorem sparse_subexponential_budget_implies_exponential_decay",
    "theorem exactLongSectorSubexponential_implies_C1",
    "theorem residualLongSectorSubexponential_implies_C1",
    "theorem constantDecimalStream_sparse_short_pairs_order_nL",
]
for needle in required_lean:
    assert needle in lean, f"missing Lean declaration: {needle}"

forbidden = re.compile(
    r"\b(sorry|admit|native_decide|unsafe\s+(?:def|theorem)|axiom)\b"
)
assert not forbidden.search(lean), "forbidden Lean construct found"

required_report = [
    "0<r<n",
    "r<L_n",
    "Review A verdict",
    "Review B verdict",
    "precisely scoped conjecture, unresolved",
    "No fixed-pi conclusion follows merely from this audit.",
]
for needle in required_report:
    assert needle in report, f"missing report audit marker: {needle}"

print("T83 artifact replay: hashes and audit markers verified")
