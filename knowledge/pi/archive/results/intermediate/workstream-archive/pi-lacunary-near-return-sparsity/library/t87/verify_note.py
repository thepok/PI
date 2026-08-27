#!/usr/bin/env python3
"""Self-contained replay for the T87 survey.

This checks transcription, hashes, finite algebra, and one bounded generic-word
enumeration. It does not test pi digits or prove a universal statement.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
import pathlib
import subprocess
import tempfile
from fractions import Fraction


ROOT = pathlib.Path(__file__).resolve().parent

EXPECTED = {
    "LL_T87RecordDiagonalCriticalBand.lean": "88b17a0be03261d3b53fe64d09452491920ca3550194d4bd2efa22f0ca2519e4",
    "NRS_T86_REPORT.md": "16cff30f045a0b5bf56aa80c98c63add19d55c6a5a5b126602d8c785e48e11fa",
    "PFE_T61VaalerAnalytic.lean": "61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993",
    "PFE_T86GroupedSquareBound.lean": "29106f3d3d96a0342a50571d3cd62f1d64d4dbd13b5c9c11f514e5993d45f87b",
    "REPORT.md": "a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078",
    "SEMANTIC_OBSTRUCTION_MEMORY.md": "aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f",
    "SOURCE_PINS.md": "67ceaf8c2e9e41f28d476bad4c168feca8ceffe2485c59e7c11dfce5108734c4",
    "T83_REVIEW_DISPOSITION.md": "29a3cf716da0e88cd1a0b51d2c63151b945a740cf773b256dfa9f282595ad760",
    "WORKFLOW_CONTEXT.json": "ec9b857c9f0703df7adaff42c410179c2fb0d56aced72cf9155cb9251ff6691d",
    "bailey-crandall-2002.pdf": "d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74",
    "bugeaud-kim-2017.pdf": "4a4a2d949b342c9360b78dcb8073e1fb367b910b30bba9d1be19b5f29e3f6c9d",
    "bugeaud-kim-2510.02059v2.pdf": "fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330",
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
}


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pdf_text(name: str, first: int, last: int) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        out = pathlib.Path(tmp) / "source.txt"
        subprocess.run(
            [
                "pdftotext",
                "-f",
                str(first),
                "-l",
                str(last),
                "-layout",
                str(ROOT / name),
                str(out),
            ],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return out.read_text(errors="replace")


def correction(m: float) -> float:
    return (-m**3 + 2 * m**2 + m - 1) / (
        m**4 - 2 * m**3 + 3 * m**2 - 3 * m + 1
    )


def cubic(x: float) -> float:
    return x**3 - 2 * x**2 - x + 1


def bisect_root(lo: float, hi: float, steps: int = 100) -> float:
    assert cubic(lo) < 0 < cubic(hi)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if cubic(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def collision_counts(word: tuple[int, ...], n: int, starts: int) -> tuple[int, int]:
    blocks = [word[i : i + n] for i in range(starts)]
    short = 0
    long = 0
    for i in range(starts):
        for j in range(starts):
            if i == j or blocks[i] != blocks[j]:
                continue
            lag = abs(i - j)
            if lag < n:
                short += 1
            else:
                long += 1
    return short, long


def binary_discriminator(n: int) -> tuple[int, int, int]:
    starts = 2 ** (n // 2)
    length = starts + n - 1
    best_num = -10**9
    best_pair = (0, 0)
    for word in itertools.product(range(2), repeat=length):
        short, long = collision_counts(word, n, starts)
        numerator = 2 * short - 3 * long
        if numerator > best_num:
            best_num = numerator
            best_pair = (short, long)
    return best_num, best_pair[0], best_pair[1]


def main() -> None:
    for name, expected in EXPECTED.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)

    workflow = json.loads((ROOT / "WORKFLOW_CONTEXT.json").read_text())
    assert workflow["agenda_item"]["id"] == "T87"
    recent = workflow["program_context"]["recent_results"]
    verdicts = {item["item"]: item["verdict"] for item in recent}
    assert verdicts["T83"] == "accept"
    assert verdicts["T86"] == "accept"

    anchors = [
        (
            "bugeaud-kim-2510.02059v2.pdf",
            3,
            3,
            ["Theorem 1.4.", "X 3 − 2X 2 − X + 1", "−µ3 + 2µ2 + µ − 1"],
        ),
        (
            "bugeaud-kim-2510.02059v2.pdf",
            11,
            12,
            ["Lemma 4.1.", "bu (bv − 1)", "rep(a)"],
        ),
        ("bugeaud-kim-2017.pdf", 14, 15, ["Lemma 3.6.", "rep(x) < 2"]),
        (
            "bailey-crandall-2002.pdf",
            13,
            14,
            [
                "Lemma 4.5 (Korobov, Niederreiter)",
                "d = gcd(h, c)",
                "J ∈",
                "Theorem 4.6",
            ],
        ),
        (
            "zeilberger-zudilin-2020.pdf",
            13,
            13,
            ["7.10320533413700172750577342281", "irrationality measure"],
        ),
    ]
    for name, first, last, needles in anchors:
        text = pdf_text(name, first, last)
        for needle in needles:
            assert needle in text, (name, first, last, needle)

    report = (ROOT / "REPORT.md").read_text()
    pins = (ROOT / "SOURCE_PINS.md").read_text()
    assert report.count("PRIMARY_SOURCE_COUNT: 4") == 1
    assert report.count("CANDIDATE_COUNT: 3") == 1
    assert report.count("TERMINAL_DECISION_COUNT: 1") == 1
    assert pins.count("## Primary source ") == 4
    assert report.count("SUCCESS ENDPOINT") >= 3
    assert report.count("KILL ENDPOINT") >= 3
    assert report.count("Theorem-applicability card") == 3
    table = report.split("## 4. Ranked decision table", 1)[1].split("## 5.", 1)[0]
    assert table.count("**PFE:**") == 3
    assert table.count("**Long-lag:**") == 3
    assert table.count("**NRS:**") == 3
    assert table.count("Review A") >= 3
    assert table.count("Review B") >= 3
    assert "**Park:**" not in report
    assert "1\\le J-t\\le\\operatorname{ord}_m(10)" in report
    assert "\\ell=J-t" in report
    terminal = "TERMINAL DECISION (1/1): SOURCE-PINNED NEGATIVE SYNTHESIS."
    assert report.count(terminal) == 1
    assert report.count("Park C1, C2, G11, and G19") == 1
    assert report.rstrip().splitlines()[-1].startswith(terminal)

    pfe61 = (ROOT / "PFE_T61VaalerAnalytic.lean").read_text()
    pfe86 = (ROOT / "PFE_T86GroupedSquareBound.lean").read_text()
    ll87 = (ROOT / "LL_T87RecordDiagonalCriticalBand.lean").read_text()
    nrs86 = (ROOT / "NRS_T86_REPORT.md").read_text()
    assert "strictResidualIncidenceCount_le_majorantTotal" in pfe61
    assert "SignedStructuredDenominatorPremise" in pfe61
    assert "signedStructuredDenominatorPremise_implies_C7" in pfe61
    assert "groupedSquare_lt_fortyTwo" in pfe86
    assert "D_N μ c Q0 N < 42" in pfe86
    assert "recordDiagonal_normalized_critical_bounds_literal" in ll87
    assert "centered off-diagonal" in ll87
    assert "{J\\over131072A^2n^2}" in nrs86
    assert "524288" in nrs86 and "262144" in nrs86

    root = bisect_root(2.2, 2.3)
    assert abs(root - 2.246979603717467) < 1e-14
    assert correction(root - 1e-6) > 0
    assert correction(root + 1e-6) < 0
    ordinary = 7.1032053341370017275
    ordinary_total = 1 + correction(ordinary)
    assert abs(ordinary_total - 0.8717456738499811) < 1e-14
    assert ordinary_total < 1

    # RB substitution: E=L+S+R and S<=C*L+3R/2.
    # Multiplication by T7's factor 3 gives coefficients 3C+3 and 15/2.
    assert 3 * (1 + Fraction(3, 2)) == Fraction(15, 2)
    assert 3 * Fraction(5, 2) == Fraction(15, 2)
    assert 9 * 256 == 2304
    assert 2 * 131072 == 262144
    assert 4 * 131072 == 524288
    # Substitution of epsilon_10 into the elementary phase-transfer bound.
    assert Fraction(2 * 9, 9 * 524288) == Fraction(1, 262144)

    expected_numerators = [0, 4, 4, 24, 24, 82]
    for n, expected in enumerate(expected_numerators, start=1):
        numerator, short, long = binary_discriminator(n)
        assert numerator == expected, (n, numerator, short, long)
    numerator, short, long = binary_discriminator(6)
    assert (numerator, short, long) == (82, 50, 6)
    assert numerator / (2 * (2 ** (6 // 2))) == 41 / 8

    print("T87 replay passed")
    print(f"verified pinned inputs: {len(EXPECTED)}")
    print("verified retained primary sources: 4")
    print("verified candidates: 3")
    print(f"localized threshold: {root:.15f}")
    print(f"ordinary-bound substitution: {ordinary_total:.15f}")
    print("binary n=6 discriminator: S=50 R=6 D=41/8")
    print("terminal decisions: 1 negative parking verdict")


if __name__ == "__main__":
    main()
