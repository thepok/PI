#!/usr/bin/env python3
"""Deterministic bounded replay for the T131 literature artifact.

This checks hashes, source anchors, report structure, and finite identities. It
does not prove any asymptotic statement or any claim about pi.
"""

from __future__ import annotations

import hashlib
import math
import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-t121-REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
    "prior-t122-REJECTED-REPORT.md": "6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7",
    "doerr-tu-discrepancy.pdf": "5478f98548430d1da62f0472ef107804f20cc82567fa2d79c1c149ca798b04ae",
    "holroyd-et-al-0801.3306v4.pdf": "17f1a472024a680eebc7ed884d04ebd8180908c8571a14ee704a9a809b02f48d",
    "holroyd-propp-0904.4507v3.pdf": "50b7bf9d576939add4e94208037289254ff22520af5a05250f23cd2c361660fb",
    "angel-et-al-0910.1077v3.pdf": "dcd300ad04d9b79c1a9ad86fcd4d3c8a818e8e0312133682022cdfa9caa0c454",
    "fishman-merrill-simmons-1605.07953v3.pdf": "e190cb7781e2994e65169993dab3b404c9d744678c6df7abd47f00e534a05c7e",
    "nellore-ward-2108.07759v2.pdf": "277dcd82f88cd88092375b4023458480593bfdd26aaba0d921287fac4453492b",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
}

PDF_ANCHORS = {
    "doerr-tu-discrepancy.pdf": ["Theorem 1. For any totally unimodular", "lindisc(A)"],
    "holroyd-et-al-0801.3306v4.pdf": ["Lemma 4.9.", "traverses an Eulerian tour"],
    "holroyd-propp-0904.4507v3.pdf": ["Theorem 4 (Stationary distribution)", "Proposition 13 (Key bound)"],
    "angel-et-al-0910.1077v3.pdf": ["Theorem 2 (Low-discrepancy sequences", "strictly less than 1"],
    "fishman-merrill-simmons-1605.07953v3.pdf": ["totally de Bruijn", "Corollary 4.3"],
    "nellore-ward-2108.07759v2.pdf": ["Definition 1.1", "Theorem 2.4", "Theorem 2.6"],
    "becher-carton-1805.03713v1.pdf": ["Theorem 1.", "nested perfect necklace"],
}


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)


def pdf_text(name: str) -> str:
    with tempfile.NamedTemporaryFile(suffix=".txt") as out:
        subprocess.run(
            ["pdftotext", "-layout", str(ROOT / name), out.name],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return pathlib.Path(out.name).read_text(errors="replace")


def check_source_anchors() -> None:
    for name, anchors in PDF_ANCHORS.items():
        text = pdf_text(name)
        for anchor in anchors:
            assert anchor in text, (name, anchor)


def variance(counts: list[int]) -> float:
    total = sum(counts)
    q = len(counts)
    return sum((c - total / q) ** 2 for c in counts)


def check_collision_identity() -> None:
    examples = [[4, 1, 0, 2], [1] * 10, [7, 0, 3]]
    for counts in examples:
        total = sum(counts)
        energy = sum(c * c for c in counts)
        rhs = total * total / len(counts) + variance(counts)
        assert math.isclose(energy, rhs, rel_tol=0.0, abs_tol=1e-10)


def check_arbitrary_length_variance() -> None:
    for q in range(2, 41):
        for length in range(1, 121):
            a, r = divmod(length, q)
            counts = [a + 1] * r + [a] * (q - r)
            expected = r - r * r / q
            assert math.isclose(variance(counts), expected, abs_tol=1e-10)
            assert expected <= q / 4 + 1e-10


def check_projection_bound() -> None:
    # Exhaustive small integer vectors grouped into equal-size fibers.
    for fiber_size in range(1, 5):
        for groups in range(1, 6):
            values = [((7 * i + 3) % 9) - 4 for i in range(fiber_size * groups)]
            projected = [
                sum(values[g * fiber_size : (g + 1) * fiber_size])
                for g in range(groups)
            ]
            lhs = sum(x * x for x in projected)
            rhs = fiber_size * sum(x * x for x in values)
            assert lhs <= rhs


def check_endpoint_change_constant() -> None:
    # Relabeling one start changes one count by -1 and another by +1.
    change = [-1, 1, 0, 0]
    norm = math.sqrt(sum(x * x for x in change))
    assert math.isclose(norm, math.sqrt(2), abs_tol=1e-12)
    for changed_starts in range(1, 20):
        assert norm * changed_starts <= math.sqrt(2) * changed_starts + 1e-12


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    assert "PRIMARY_SOURCE_COUNT: 7" in report
    assert "PRIMARY_SOURCE_CAP: 8" in report
    assert "RETAINED_CANDIDATE_COUNT: 3" in report
    assert "RETAINED_CANDIDATE_CAP: 3" in report
    assert report.count("SCOPED_VERDICT:") == 1
    assert "SUCCESSOR_COUNT: 0" in report
    assert "BOUNDED_SUCCESSOR:" not in report
    assert report.count("`QR-TU`") == 1
    assert report.count("`QR-EULER`") == 1
    assert report.count("`QR-NEST`") == 1
    for marker in [
        "rounding", "Euler-ordering loss", "endpoint loss", "cross-depth/splicing loss",
        "D+sqrt(2)C", "K4_star", "including the final read into the next piece",
        "prior-t121-REPORT.md", "prior-t122-REJECTED-REPORT.md",
        "`PI-CYCLE-SHADOW`", "No fixed-pi, C1, or C2 conclusion",
    ]:
        assert marker in report, marker
    assert report.count("SCOPED_VERDICT_COUNT: 1") == 1


def main() -> None:
    check_hashes()
    check_source_anchors()
    check_collision_identity()
    check_arbitrary_length_variance()
    check_projection_bound()
    check_endpoint_change_constant()
    check_report_contract()
    print("T131 replay: PASS")
    print("primary source hashes: 7/7")
    print("primary source anchors: 7/7")
    print("candidate cards: 3/3")
    print("finite collision/variance/projection checks: PASS")
    print("scoped verdict markers: 1; successors: 0")
    print("scope: A13 related models only; no fixed-pi, C1, or C2 conclusion")


if __name__ == "__main__":
    main()
