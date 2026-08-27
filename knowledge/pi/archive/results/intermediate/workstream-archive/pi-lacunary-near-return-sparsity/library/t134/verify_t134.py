#!/usr/bin/env python3
"""Self-contained transcription and finite-arithmetic checks for T134."""

from __future__ import annotations

import hashlib
import math
import subprocess
import tarfile
import tempfile
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "T7FiniteCylinderEnergy.lean": "cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c",
    "zeilberger-zudilin-2020.pdf": "3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5",
    "bugeaud-kim-2017.pdf": "4a4a2d949b342c9360b78dcb8073e1fb367b910b30bba9d1be19b5f29e3f6c9d",
    "moshchevitin-0709.3419v2.pdf": "d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5",
    "fischler-rivoal-1512.06534.pdf": "2cc01bb677d29ac3b2aa79b54eff131928d747489335ff90e4bf4a48778736b8",
    "fishman-merrill-simmons-2018.pdf": "a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
    "prior_evidence.tar": "37a4c7c59d0a5704273f053d5fd3b4ead84c020891b7f66a3e6f3103d42a0285",
}

PRIOR = {
    "notes/t87/REPORT.md": "a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078",
    "t111/REPORT.md": "89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8",
    "notes/t113/REPORT.md": "30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445",
    "t116/REPORT.md": "573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1",
    "t130/prior-t119-REPORT.md": "72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a",
    "t121/REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
    "t128/REPORT.md": "7e9520d7a0191df6f988d7f4f4920cfb954ac5162efa7fae43c1851de5863ffc",
    "t130/REPORT.md": "c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c",
    "t131/REPORT.md": "ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db",
}

PDF_PAGE_ANCHORS = {
    "zeilberger-zudilin-2020.pdf": {
        2: ["irrationality measure µ", "sufficiently large q"],
        13: ["irrationality measure of π is bounded above by", "7.103205334137001"],
    },
    "bugeaud-kim-2017.pdf": {14: ["Lemma 3.6.", "rep(x)"]},
    "moshchevitin-0709.3419v2.pdf": {
        2: ["Theorem 2.", "H(n, τ )"],
        3: ["is nonempty."],
    },
    "fischler-rivoal-1512.06534.pdf": {
        5: ["Theorem 3.", "Nb (ξ, t, n)", "Li2"],
    },
    "fishman-merrill-simmons-2018.pdf": {
        4: ["de Bruijn sequence of order n", "(2.1)"],
        11: ["Corollary 4.3.", "totally de Bruijn"],
    },
    "becher-carton-1805.03713v1.pdf": {
        2: ["Theorem 1.", "nested perfect necklaces"],
    },
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalized(text: str) -> str:
    return " ".join(text.split())


def check_hashes() -> None:
    for name, expected in EXPECTED.items():
        path = ROOT / name
        assert path.is_file(), f"missing {name}"
        assert digest(path.read_bytes()) == expected, f"hash mismatch: {name}"


def check_prior_archive() -> None:
    with tarfile.open(ROOT / "prior_evidence.tar", "r") as archive:
        members = [member.name for member in archive.getmembers() if member.isfile()]
        assert members == list(PRIOR), "unexpected comparator archive inventory"
        for name, expected in PRIOR.items():
            extracted = archive.extractfile(name)
            assert extracted is not None
            assert digest(extracted.read()) == expected, f"prior hash mismatch: {name}"


def check_pdf_anchors() -> None:
    with tempfile.TemporaryDirectory(prefix="t134-") as tmp:
        for name, pages in PDF_PAGE_ANCHORS.items():
            for page, anchors in pages.items():
                output = Path(tmp) / f"{name}-p{page}.txt"
                subprocess.run(
                    [
                        "pdftotext",
                        "-f",
                        str(page),
                        "-l",
                        str(page),
                        "-layout",
                        str(ROOT / name),
                        str(output),
                    ],
                    check=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                text = normalized(output.read_text(encoding="utf-8", errors="replace"))
                for anchor in anchors:
                    assert normalized(anchor) in text, (
                        f"missing source anchor {name} physical page {page}: {anchor}"
                    )


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    report_flat = normalized(report)
    search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")

    required_once = [
        "PRIMARY_SOURCE_COUNT: 6",
        "PRIMARY_SOURCE_CAP: 8",
        "RETAINED_CANDIDATE_COUNT: 3",
        "RETAINED_CANDIDATE_CAP: 3",
        "SCOPED_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 0",
        "FIXED_PI_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "SCOPED_VERDICT (1/1): **close**",
    ]
    for marker in required_once:
        assert report.count(marker) == 1, f"marker count: {marker}"

    for candidate in ("C-RD", "C-GRUN", "C-DB"):
        assert f"## 4. {candidate}" in report or f"## 5. {candidate}" in report or f"## 6. {candidate}" in report
        assert f"CHEAP_KILL_{candidate}" in report or candidate == "C-DB"

    for item in ("T87", "T111", "T113", "T116", "T119", "T121", "T128", "T130", "T131", "T132", "T133"):
        for candidate in ("C-RD", "C-GRUN", "C-DB"):
            assert f"`{candidate}/{item}`" in report, f"missing comparison {candidate}/{item}"

    required_text = [
        "Z_m(x,N)^2<=N^2/(6*A*m)",
        "PI-ZERO-OCCUPANCY (`conjecture`; unproved and not asserted)",
        "controlling one fiber does not control total collision energy",
        "no `t132/` or `t133/` entry",
        "No bounded successor is proposed.",
    ]
    for marker in required_text:
        assert normalized(marker) in report_flat, f"missing report text: {marker}"

    assert search.count("| 1 |") == 1 and search.count("| 6 |") == 1
    for source in ("Zeilberger", "Bugeaud", "Moshchevitin", "Fischler", "Fishman", "Becher"):
        assert source in pins and source in search

    lean = (ROOT / "T7FiniteCylinderEnergy.lean").read_text(encoding="utf-8")
    for marker in (
        "def piCylinderCollisionEnergy",
        "piCylinderCollisionEnergy_eq_equalPairs_card",
        "piCylinderCollisionEnergy_le_Q_pi_le_three_mul",
    ):
        assert marker in lean


def check_zero_pair_identity() -> None:
    examples = [
        [0],
        [0, 1, 0, 2, 0],
        [3, 3, 3, 0, 2, 0, 0, 9],
        [1, 2, 3, 4],
    ]
    for labels in examples:
        z = sum(label == 0 for label in labels)
        ordered_zero_pairs = sum(a == 0 and b == 0 for a in labels for b in labels)
        assert ordered_zero_pairs == z * z
        occupancies = {label: labels.count(label) for label in set(labels)}
        energy = sum(count * count for count in occupancies.values())
        equal_pairs = sum(a == b for a in labels for b in labels)
        assert energy == equal_pairs


def check_debruijn_substitution() -> None:
    for A in range(1, 51):
        for m in range(A, A + 21):
            N = 10**m
            Z = 1  # d=m in (6.2)
            assert N >= A * m
            assert 6 * A * m <= 10 ** (2 * m)
            assert 6 * A * m * Z * Z <= N * N
        for d in range(1, 8):
            for m in range(1, d + 1):
                N = 10**d
                Z = 10 ** (d - m)
                assert Z * 10**m == N
                assert Z * Z * 10 ** (2 * m) == N * N


def check_kill_calculations() -> None:
    getcontext().prec = 50
    M = Decimal("7.1032053341370017275")
    eta = Decimal("0.1")
    m = 100_000
    L = int(Decimal(m) / (M + eta - 1))
    rd_cap = m - L
    rd_needed = math.sqrt(m / 6)
    assert rd_cap > rd_needed
    rho_minus_one = Decimal(1) / (M - 1)
    assert rho_minus_one < 1
    assert rho_minus_one * Decimal(m) + 1 < Decimal(m)

    s = 100_000_000
    theta = Decimal(20_000_000) / Decimal(s)
    inverse_theta = int(Decimal(1) / theta)
    A = inverse_theta + 2
    m = 10_000
    N = A * m
    grun_cap = N - math.ceil(Decimal(m) / theta) + 1
    grun_needed = math.sqrt(Decimal(A * m) / Decimal(6))
    assert N >= A * m
    assert grun_cap > grun_needed

    rho_num, rho_den, m, periods = 3, 2, 100, 20
    r = math.ceil(rho_num * m / rho_den)
    cyclic = ([0] * r + [1]) * periods + [0] * r
    cutoff = periods * (r + 1)
    z = sum(cyclic[i : i + m] == [0] * m for i in range(cutoff))
    assert z == periods * (r - m + 1)
    assert z / cutoff > Decimal(1) / Decimal(4)
    assert z / cutoff > 1 / math.sqrt(6 * m)


def main() -> None:
    check_hashes()
    check_prior_archive()
    check_pdf_anchors()
    check_report_contract()
    check_zero_pair_identity()
    check_debruijn_substitution()
    check_kill_calculations()
    print("T134 verification PASS")
    print("primary_sources=6 cap=8 retained_candidates=3 cap=3")
    print("zero_fiber_identity=PASS threshold_substitutions=PASS")
    print("comparison_markers=33/33 active_boundary=T132,T133")
    print("verdict=close successors=0 fixed_pi_claim=none C1_claim=none C2_claim=none")


if __name__ == "__main__":
    main()
