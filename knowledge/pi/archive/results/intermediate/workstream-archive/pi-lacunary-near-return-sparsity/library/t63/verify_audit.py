#!/usr/bin/env python3
"""Self-contained integrity and terminal-verdict checks for the T63 audit."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "zudilin-2409.10097v1.pdf": "67e8946c37b9e91da0dcdcc9f9886ef7278b69ca68200c7acac03197c9c59743",
    "zudilin-2409.10097v2.pdf": "01ba3b7b1ebd22d0d718b0fa3ed67d20030870a2bfe41a3a6b3ff7a3ce479d25",
    "bailey-borwein-plouffe-1997.pdf": "ee6c1f95f17ba7a7b9dcb09005c4f1d2d6a73d142694ac9af695811fa52ac9a2",
    "bailey-crandall-2001-bcrandom.pdf": "701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8",
    "bailey-crandall-2002-bcnormal.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "lagarias-math0101055v2.pdf": "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
    "zudilin-2409.10097v1.txt": "bc82ae9f327ef2533062d07216d94c092efec8128c733f526bccc3341ab41d79",
    "zudilin-2409.10097v2.txt": "73f138af3f4871548dcad600f862cf2bc6a84bc77548bbb95c4d0d549afa16c8",
    "bailey-borwein-plouffe-1997.txt": "1c87932b775606577b41256963a32e76643e7a2b61b0157f0689bfb02e05a0d5",
    "bailey-crandall-2001-bcrandom.txt": "d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406",
    "bailey-crandall-2002-bcnormal.txt": "bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47",
    "lagarias-math0101055v2.txt": "d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346",
}

MARKERS = {
    "zudilin-2409.10097v1.txt": [
        "A BBP-style computation",
        "base 10",
        "Surprisingly enough, we can use the same scheme",
    ],
    "zudilin-2409.10097v2.txt": [
        "3. An obvious flaw",
        "The equality in (3) is incorrect",
        "while the denominator of the"
    ],
    "bailey-borwein-plouffe-1997.txt": [
        "Theorem 1. The following identity holds:",
        "we cannot at present compute decimal digits",
    ],
    "bailey-crandall-2001-bcrandom.txt": [
        "Hypothesis A.",
        "Theorem 3.1.",
        "prevents any easy manipulation of the exponential sum",
    ],
    "bailey-crandall-2002-bcnormal.txt": [
        "Theorem 4.6",
        "Theorem 4.8",
    ],
    "lagarias-math0101055v2.txt": [
        "Theorem 3.1",
        "Theorem 4.1",
        "At present none is known, in either direction.",
    ],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    for name, expected in EXPECTED.items():
        actual = sha256(ROOT / name)
        assert actual == expected, f"SHA-256 mismatch for {name}: {actual}"

    for name, markers in MARKERS.items():
        text = (ROOT / name).read_text(encoding="utf-8")
        for marker in markers:
            assert marker in text, f"missing source marker in {name}: {marker!r}"

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required_report_markers = [
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
        "5^{2n+1-d+k}m",
        "|pi-pi_K| <= 8*5^{-K}/(2K+1)",
        "AdaptiveRationalPhaseTransfer",
        "gcd(10,q)=1",
    ]
    for marker in required_report_markers:
        assert marker in report, f"missing report marker: {marker!r}"

    verdicts = (
        "EXACT BRIDGE",
        "CONDITIONAL BRIDGE WITH NAMED MISSING HYPOTHESIS",
        "NO CURRENT BRIDGE",
    )
    occurrences = sum(report.count(verdict) for verdict in verdicts)
    assert occurrences == 1, f"expected one terminal verdict, found {occurrences}"
    assert report.rstrip().endswith("NO CURRENT BRIDGE"), "wrong terminal verdict"

    print(f"verified {len(EXPECTED)} pinned files")
    print("verified source locators and audit scale markers")
    print("verified unique terminal verdict: NO CURRENT BRIDGE")


if __name__ == "__main__":
    main()
