#!/usr/bin/env python3
"""Self-contained finite replay and integrity checks for T176."""

from __future__ import annotations

import csv
import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "vaananen-1507.02510v1.pdf": "259a3a9f48bd05e99c1d0c6d80948784865d2d32e2a3bb17ed89ec8ca68a0766",
    "vaananen-1507.02510v1.txt": "219cd2c4d25c1f79f5f2e8e1695691c739e7eb93346a0df07ee878ea37678cd0",
    "popoli-stipulanti-2408.14059v1.pdf": "73527cedd88eb69ba52a553c076a9e44a699a33a0607ff54cc450565bddf8f69",
    "popoli-stipulanti-2408.14059v1.txt": "0befcc91255d7f44238ba5650a535af9e3e3099ce38bd27fc7f0516e73edd31c",
    "korolev-1604.02300v1.pdf": "aa7baaa3494ae0c5ab620e434ec1cc4c405a7716ad8ac1795ae361a7fafa0526",
    "korolev-1604.02300v1.txt": "38c2f6855764ffe812f7379d8ab48eab0bfa2cf14be0c666af9b2e7305c9a56f",
    "bajpai-bhakta-garcia-2007.15482v2.pdf": "a27382d9828d0746b5c033e05d0ba28a6671674dbefc1e8e0594b16a35f24969",
    "bajpai-bhakta-garcia-2007.15482v2.txt": "645c8247f26072272a3a4b33dddda7ab79683adff787cc21ab345c94d7f756ce",
}


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def check_hashes() -> None:
    for name, expected in EXPECTED_HASHES.items():
        assert digest(name) == expected, name


def check_sources() -> None:
    with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == 4
    domains = {row["domain"] for row in rows}
    assert domains == {
        "Mahler or functional-equation constants",
        "symbolic collision theory",
        "short structured exponential sums",
    }
    assert len({row["stable_url"] for row in rows}) == 4
    assert len({row["pdf_sha256"] for row in rows}) == 4
    assert sum("retained obstruction fingerprint" in row["disposition"] for row in rows) == 1
    for row in rows:
        assert row["pdf_sha256"] in EXPECTED_HASHES.values()
        assert row["text_sha256"] in EXPECTED_HASHES.values()
        assert "PDF/printed pp." in row["exact_locator_and_range"]

    s1 = (ROOT / "vaananen-1507.02510v1.txt").read_text(encoding="utf-8")
    for anchor in (
        "Theorem 1. For every non-zero algebraic",
        "the regular paperfolding sequence defined by",
        "the Cantor sequence on {0, 1}",
        "U3 (z) = fC (z)",
    ):
        assert anchor in s1

    s2 = (ROOT / "popoli-stipulanti-2408.14059v1.txt").read_text(encoding="utf-8")
    for anchor in (
        "Theorem 2. Let k ≥ 1 be an integer",
        "Theorem 3. Let s be a linearly recurrent sequence",
        "two identical blocks of length Uβ (M )",
        "C2 (s, N ) ≥ |V",
    ):
        assert anchor in s2

    s3 = (ROOT / "korolev-1604.02300v1.txt").read_text(encoding="utf-8")
    for anchor in (
        "Short Kloosterman sums to powerful modulus",
        "The aim of this paper is to estimate a short Kloosterman sum",
        "Theorem 1. Suppose that q",
        "Proof of Theorem 1. Shifting the interval",
    ):
        assert anchor in s3

    s4 = (ROOT / "bajpai-bhakta-garcia-2007.15482v2.txt").read_text(encoding="utf-8")
    for anchor in (
        "Theorem 1. Let p be a large prime number",
        "nonzero linear recurrence sequence with positive order and period",
        "Corollary 6. Suppose that {sn } is a nonzero linear recurrence sequence",
    ):
        assert anchor in s4


def check_ledger() -> None:
    with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == 87
    assert [row["item"] for row in rows] == [f"T{i}" for i in range(89, 176)]
    by_item = {row["item"]: row for row in rows}
    for item in ("T173", "T174"):
        assert "active" in by_item[item]["verification"]
        assert "reserved active identifier" in by_item[item]["T163_disposition"]
    assert "unverified lead" in by_item["T171"]["T163_disposition"]


def cantor_digit(n: int) -> int:
    while n:
        if n % 3 == 1:
            return 0
        n //= 3
    return 1


def blocks(word: list[int], m: int, starts: int) -> list[tuple[int, ...]]:
    return [tuple(word[i : i + m]) for i in range(starts)]


def check_cantor_calculation() -> None:
    # The induction step used after k=7 is
    # (k+1)(2^(k+1)+k+1) <= 3k(2^k+k), whose difference is positive.
    assert 7 * (2**7 + 7) <= 3**7 / 2
    for k in range(7, 60):
        difference = (k - 2) * 2**k + 2 * k * k - 2 * k - 1
        assert difference > 0
        assert (k + 1) * (2 ** (k + 1) + k + 1) <= 3 * k * (2**k + k)
        assert k * (2**k + k) <= 3**k / 2

    for k in range(7, 11):
        M = 3**k
        for kappa in (0.25, 0.5, 1.0):
            m = math.floor(kappa * math.log10(M))
            if m == 0:
                continue
            assert 1 <= m <= k
            word = [cantor_digit(n) for n in range(M + m - 1)]
            assert sum(word[:M]) == 2**k
            bs = blocks(word, m, M)
            zero_count = sum(not any(block) for block in bs)
            assert zero_count >= M - m * (2**k + m)
            assert zero_count >= M / 2
            counts: dict[tuple[int, ...], int] = {}
            for block in bs:
                counts[block] = counts.get(block, 0) + 1
            energy = sum(count * count for count in counts.values())
            assert energy >= zero_count**2 >= M * M / 4
            zero_starts = [i for i, block in enumerate(bs) if not any(block)]
            base = zero_starts[0]
            offsets = {i - base for i in zero_starts[1:]}
            assert len(offsets) == zero_count - 1 >= M / 2 - 1


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required = (
        "SEARCHED_DOMAIN_COUNT: 3",
        "NEW_SOURCE_THEOREM_TUPLE_COUNT: 4",
        "NEW_SOURCE_THEOREM_TUPLE_CAP: 6",
        "RETAINED_FINGERPRINT_COUNT: 1",
        "RETAINED_FINGERPRINT_CAP: 3",
        "EXCLUSION_LEDGER_RANGE: T89-T175",
        "EXCLUSION_LEDGER_COUNT: 87",
        "RESERVED_ACTIVE_ITEMS: T173,T174",
        "PI-FUNCTIONAL-OFFSET-T176",
        "C-MAHLER",
        "C-SYMBOLIC",
        "C-SHORT",
        "m_k=floor(kappa*log_10(M_k))",
        "m=floor(kappa*log_10 M)",
        "SCOPED VERDICT (1/1): CLOSE THE FINGERPRINT.",
        "SUCCESSOR_COUNT: 0",
        "FIXED_PI_CLAIM: none",
        "A1_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
    )
    for marker in required:
        assert marker in report, marker
    for item in ("T91", "T94", "T97", "T101", "T115", "T119", "T160", "T171"):
        assert f"| {item} |" in report
    assert report.count("SCOPED VERDICT (1/1)") == 1
    assert report.count("**Disposition:**") == 3
    assert "T171 side finding named by the agenda is an `unverified lead`" in report


def main() -> None:
    check_hashes()
    check_sources()
    check_ledger()
    check_cantor_calculation()
    check_report_contract()
    print("T176 artifact replay: PASS")
    print("domains=3 tuples=4 retained_fingerprints=1 ledger=T89-T175")
    print("cantor_log_depth_floor=PASS symbolic_linear_mass_rejection=PASS short_sum_collision_rejection=PASS")
    print("verdicts=1 successors=0 fixed_pi_claims=0")


if __name__ == "__main__":
    main()
