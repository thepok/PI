#!/usr/bin/env python3
"""Self-contained transcription and bounded-falsification checks for T113."""

from __future__ import annotations

import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "moshchevitin-0709.3419v2.pdf": "d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5",
    "moshchevitin-0709.3419v2.txt": "117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
    "becher-carton-1805.03713v1.txt": "1350d0d9e1044d21455308fb1885db6f255f43652faad68caf53031bac40440a",
    "fishman-merrill-simmons-2018.pdf": "a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4",
    "fishman-merrill-simmons-2018.txt": "34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def triangular(i: int) -> int:
    return i * (i + 1) // 2


def t_at(k: int) -> int:
    assert k >= 1
    i = 1
    while triangular(i) < k:
        i += 1
    s = k - triangular(i - 1)
    return 10**i - 10 ** (i - s)


def h_at(k: int) -> int:
    return math.ceil(8.0 * math.sqrt(k) * math.log(64 * k))


def check_hashes() -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)
    print(f"hashes: ok ({len(EXPECTED_HASHES)} files)")


def check_source_anchors() -> None:
    mosh = (ROOT / "moshchevitin-0709.3419v2.txt").read_text(errors="replace")
    becher = (ROOT / "becher-carton-1805.03713v1.txt").read_text(errors="replace")
    fms = (ROOT / "fishman-merrill-simmons-2018.txt").read_text(errors="replace")
    for anchor in ["H(n,", "Theorem 2.", "n−h(n)+1", "Subexponentional sequen"]:
        assert anchor in mosh, anchor
    for anchor in ["Theorem 1.", "nested perfect necklaces", "O((log N )2 /N )"]:
        assert anchor in becher, anchor
    for anchor in ["de Bruijn sequence of order n", "Corollary 4.3.", "totally de Bruijn"]:
        assert anchor in fms, anchor
    print("source anchors: ok")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text()
    required = [
        "PRIMARY_SOURCE_COUNT: 3",
        "PRIMARY_SOURCE_CAP: 8",
        "SEARCHED_DOMAIN_COUNT: 3",
        "PRIOR_FINGERPRINT_COUNT: 5",
        "TERMINAL_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 0",
        "T90",
        "T105",
        "T111",
        "T112 (active revision state)",
        "T109 (terminal rejected record)",
        "PI-AVOID:",
        "Q_x(n,N_A(n)) = N_A(n)",
        "TERMINAL_VERDICT: hold as model",
    ]
    for marker in required:
        assert marker in report, marker
    assert report.count("TERMINAL_VERDICT:") == 1
    assert "TERMINAL_VERDICT: develop" not in report
    assert "TERMINAL_VERDICT: close" not in report
    print("report contract: ok")


def check_difference_ordering() -> None:
    for n in range(2, 41):
        positive = sorted({10**i - 10**j for i in range(n) for j in range(i)})
        signed = {10**i - 10**j for i in range(n) for j in range(n)}
        expected = [t_at(k) for k in range(1, n * (n - 1) // 2 + 1)]
        assert positive == expected, n
        assert len(positive) == n * (n - 1) // 2, n
        assert len(signed) == n * (n - 1) + 1, n
    for k in range(1, 5001):
        value = t_at(k)
        a = math.sqrt(2.0) * math.log(10.0)
        lower = 9.0 / (10.0 * math.sqrt(10.0)) * math.exp(a * math.sqrt(k))
        upper = 10.0 * math.exp(a * math.sqrt(k))
        assert lower <= value < upper, k
    print("difference ordering/growth: ok (N<=40, k<=5000)")


def check_theorem_parameters() -> None:
    start = None
    previous_reduced = None
    checked = 0
    for k in range(1, 100001):
        h = h_at(k)
        if k <= h:
            continue
        if start is None:
            start = k
        reduced = k - h
        if previous_reduced is not None:
            assert reduced >= previous_reduced, k
        previous_reduced = reduced
        # Exact integer form of t_k/t_reduced > 64*reduced^2.
        assert t_at(k) > 64 * reduced * reduced * t_at(reduced), k
        checked += 1
    assert start is not None and checked > 0
    partial_delta = sum(1.0 / (64.0 * k * k) for k in range(1, 100001))
    assert partial_delta < 1.0 / 32.0
    print(f"theorem parameters: ok ({checked} tail indices, first={start})")


def check_threshold_schedule() -> None:
    cases = 0
    for a in range(1, 21):
        for n in range(16 * a, 16 * a + 101):
            N = a * n
            K = N * (N - 1) // 2
            assert 10**n > 64 * K * K
            assert N >= a * n
            cases += 1
    print(f"threshold schedule: ok ({cases} finite cases)")


def main() -> None:
    check_hashes()
    check_source_anchors()
    check_report_contract()
    check_difference_ordering()
    check_theorem_parameters()
    check_threshold_schedule()
    print("classification: experiment only; universal deductions remain proof sketch")


if __name__ == "__main__":
    main()
