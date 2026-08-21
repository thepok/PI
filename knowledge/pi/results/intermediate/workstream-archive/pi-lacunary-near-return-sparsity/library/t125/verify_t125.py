#!/usr/bin/env python3
"""Deterministic transcription and finite-identity checks for T125.

These checks are experiments. They do not prove any cited asymptotic theorem
or any statement about the decimal orbit of pi.
"""

from __future__ import annotations

import hashlib
import math
from pathlib import Path
import re
import subprocess
import unicodedata


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "mrt-1503.05121v3.pdf": "8a2633b1594615fe0c340bbca01ad059be5bd66d3495bd028e7e9d2264f1e688",
    "tao-1509.05422v4.pdf": "467329ae414b669808555fddf131be3bc07025777ae3af8ccdea6e98db6722e9",
    "tao-teravainen-1710.02112v1.pdf": "232dc29917cf20f223695e3a680830e5db3b4a221049cd22f040b31144369748",
    "mr-1501.04585v4.pdf": "ec546fdf256b3b3b26b161886c5bab5efb372978ab430c0032e55919f5329277",
    "mrttz-2007.15644v3.pdf": "fef1a239e616f40c57aa45e7df3397aebe880cde8ce5763acb815a24a171f6aa",
    "prior-t110-REPORT.md": "4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668",
    "prior-t117-REPORT.md": "ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b",
    "prior-t121-REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
    "prior-t122-REJECTED-REPORT.md": "6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7",
    "prior-t123-R0-REPORT.md": "3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2",
    "prior-t124-REPORT.md": "461df40595e9d59852b7d86f8df8800b0e5fafaf6803843cb2ea1e29d737dd86",
}

PDF_PAGE_ANCHORS = {
    "mrt-1503.05121v3.pdf": [
        (2, 2, ["Theorem 1.1 Chowlas conjecture on average", "1 3000"]),
        (3, 3, ["Theorem 1.3 Exponential sum estimate", "1 700"]),
        (6, 6, ["all the implied constants in our theorems are effective"]),
        (7, 7, ["some absolute constant"]),
    ],
    "tao-1509.05422v4.pdf": [
        (2, 2, ["Theorem 1.2 Logarithmically averaged Chowla conjecture"]),
        (3, 3, ["strictly weaker estimate"]),
    ],
    "tao-teravainen-1710.02112v1.pdf": [
        (
            2,
            2,
            [
                "Theorem 1.1 Odd order cases of the logarithmic Chowla conjecture",
                "odd natural number",
            ],
        ),
        (3, 3, ["there is no need to impose any non degeneracy assumptions"]),
    ],
    "mr-1501.04585v4.pdf": [
        (1, 2, ["There exist absolute constants", "One can take C 20000"]),
        (3, 3, ["Corollary 2 For every integer h"]),
    ],
    "mrttz-2007.15644v3.pdf": [
        (
            6,
            6,
            ["Corollary 1.6 Gowers uniformity of Liouville on short intervals on average"],
        ),
        (
            9,
            9,
            ["Theorem 1.9 The Liouville function has superpolynomial number of patterns"],
        ),
        (11, 11, ["Corollary 1.11 Chowlas conjecture with a short average"]),
        (7, 8, ["Proposition 1.7"]),
    ],
}

SOURCE_PIN_MARKERS = [
    "https://arxiv.org/pdf/1503.05121v3",
    "https://doi.org/10.2140/ant.2015.9.2167",
    "https://arxiv.org/pdf/1509.05422v4",
    "https://doi.org/10.1017/fmp.2016.6",
    "https://arxiv.org/pdf/1710.02112v1",
    "https://doi.org/10.5802/jtnb.1062",
    "https://arxiv.org/pdf/1501.04585v4",
    "https://doi.org/10.4007/annals.2016.183.3.6",
    "https://arxiv.org/pdf/2007.15644v3",
    "https://doi.org/10.4007/annals.2023.197.2.3",
]

PRIOR_ANCHORS = {
    "prior-t110-REPORT.md": [
        "# T110: higher-order uniformity scout",
        "fixed-order Gowers decay",
        "TERMINAL VERDICT (1/1): **HOLD AS MODEL.**",
    ],
    "prior-t117-REPORT.md": [
        "# T117: Legendre subset-product pattern-cancellation audit",
        "Pointwise subset-product calculation",
        "TERMINAL VERDICT (1/1): **HOLD AS MODEL.**",
    ],
    "prior-t121-REPORT.md": [
        "# T121: aggregate word-collision L2 scout",
        "Universal collision/variance identity",
        "SCOPED VERDICT (1/1): **DEVELOP THE AGGREGATE LEGENDRE MODEL ONLY.**",
    ],
    "prior-t122-REJECTED-REPORT.md": [
        "# T122: constructive overlapping-block discrepancy scout",
        "C-NPN: nested perfect-necklace discrepancy",
        "TERMINAL_VERDICT: develop",
    ],
    "prior-t123-R0-REPORT.md": [
        "# T123: effective named-orbit block control",
        "C-UG: lexicographically selected Eulerian decimal",
        "SCOPED_VERDICT: develop",
    ],
    "prior-t124-REPORT.md": [
        "# T124: arithmetic monodromy on decimal congruence quotients",
        "## 5. Candidate H1: rank-two Gauss hypergeometric monodromy",
        "**Verdict: hold as model.**",
    ],
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def normalized(text: str) -> str:
    text = unicodedata.normalize("NFKD", text)
    text = text.encode("ascii", "ignore").decode("ascii").lower()
    return " ".join(re.findall(r"[a-z0-9]+", text))


def check_hashes() -> None:
    for name, expected in EXPECTED_HASHES.items():
        path = ROOT / name
        assert path.is_file(), f"missing evidence file: {name}"
        actual = sha256(path)
        assert actual == expected, f"hash mismatch for {name}: {actual}"
    print(f"hashes: ok ({len(EXPECTED_HASHES)} immutable inputs)")


def extract_pdf(path: Path, first_page: int, last_page: int) -> str:
    assert path.read_bytes()[:5] == b"%PDF-", f"not a PDF: {path.name}"
    proc = subprocess.run(
        [
            "pdftotext",
            "-f",
            str(first_page),
            "-l",
            str(last_page),
            "-layout",
            str(path),
            "-",
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.stdout.decode("utf-8", errors="replace")


def check_source_anchors() -> None:
    for name, page_checks in PDF_PAGE_ANCHORS.items():
        for first_page, last_page, anchors in page_checks:
            text = normalized(extract_pdf(ROOT / name, first_page, last_page))
            for anchor in anchors:
                key = normalized(anchor)
                assert key in text, (
                    f"missing source anchor in {name} pp. {first_page}-{last_page}: "
                    f"{anchor}"
                )
    print(f"page-local source anchors: ok ({len(PDF_PAGE_ANCHORS)} primary PDFs)")


def check_prior_anchors() -> None:
    for name, anchors in PRIOR_ANCHORS.items():
        text = (ROOT / name).read_text(encoding="utf-8")
        for anchor in anchors:
            assert anchor in text, f"missing prior anchor in {name}: {anchor}"
    print(f"prior comparators: ok ({len(PRIOR_ANCHORS)} reports)")


def liouville(n: int) -> int:
    assert n >= 1
    parity = 0
    p = 2
    while p * p <= n:
        while n % p == 0:
            n //= p
            parity ^= 1
        p += 1
    if n > 1:
        parity ^= 1
    return -1 if parity else 1


def direct_collision(values: list[int], n_starts: int, m: int) -> int:
    counts: dict[tuple[int, ...], int] = {}
    for n in range(1, n_starts + 1):
        block = tuple(values[n + j] for j in range(1, m + 1))
        counts[block] = counts.get(block, 0) + 1
    return sum(count * count for count in counts.values())


def walsh_numerator(values: list[int], n_starts: int, m: int) -> int:
    total = 0
    for mask in range(1 << m):
        correlation = 0
        for n in range(1, n_starts + 1):
            product = 1
            for j in range(m):
                if mask & (1 << j):
                    product *= values[n + j + 1]
            correlation += product
        total += correlation * correlation
    return total


def check_walsh_identity() -> None:
    n_starts = 48
    max_m = 7
    values = [0] + [liouville(n) for n in range(1, n_starts + max_m + 2)]
    for m in range(1, max_m + 1):
        direct = direct_collision(values, n_starts, m)
        numerator = walsh_numerator(values, n_starts, m)
        assert numerator % (1 << m) == 0
        assert direct == numerator // (1 << m), (m, direct, numerator)
        assert direct >= n_starts
    print(f"finite Walsh collision identity: ok (m=1..{max_m})")


def check_subset_counts() -> None:
    for m in range(4, 20):
        even_ge_four = sum(math.comb(m, r) for r in range(4, m + 1, 2))
        assert even_ge_four == 2 ** (m - 1) - 1 - math.comb(m, 2)
        order_ge_three = sum(math.comb(m, r) for r in range(3, m + 1))
        assert order_ge_three == 2**m - 1 - m - math.comb(m, 2)
        for fixed_order in range(0, min(4, m) + 1):
            tail = sum(math.comb(m, r) for r in range(fixed_order + 1, m + 1))
            assert tail == 2**m - sum(
                math.comb(m, r) for r in range(fixed_order + 1)
            )
        central = math.comb(m, m // 2)
        assert central / 2**m >= 1 / (m + 1)
    assert math.e / 2 > 1
    print("subset-family counts and exponential-loss direction: ok")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")

    required_report = [
        "PRIMARY_SOURCE_COUNT: 5",
        "PRIMARY_SOURCE_CAP: 12",
        "RETAINED_CANDIDATE_COUNT: 4",
        "RETAINED_CANDIDATE_CAP: 4",
        "FIXED_PI_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "C-AVG",
        "C-LOG",
        "C-SHORT",
        "C-HIGH",
        "PI-LIOUVILLE-FACTOR (conjectural transfer; not asserted)",
        "Cheap closure test",
        "prior-t110-REPORT.md",
        "prior-t117-REPORT.md",
        "prior-t121-REPORT.md",
        "prior-t122-REJECTED-REPORT.md",
        "prior-t123-R0-REPORT.md",
        "prior-t124-REPORT.md",
        "| T124 |",
        "T125 does not rename the T124 fingerprint.",
        "This is one-sided: the corollary does not put",
        "D_AVG(N,m)",
        "D_AVG(N,m)>=binomial(m,r_0)/2^m>=1/(m+1)",
        "B_even(m)/2^m=o(1/m)",
        "B_short(m)/2^m=1-o(1)",
        "B_high(m,R)/2^m",
    ]
    for marker in required_report:
        assert marker in report, f"missing report marker: {marker}"

    assert report.count("SCOPED_VERDICT (1/1):") == 1
    assert report.count("SUCCESSOR_COUNT: 0") == 1
    assert "BOUNDED_SUCCESSOR:" not in report
    assert report.count("Card result:") == 4
    assert report.rstrip().endswith(
        "This closes only the bounded\nT125 fingerprint scout and makes no claim about fixed pi, C1, or C2."
    )

    assert pins.count("## S1:") == 1
    assert pins.count("## S2:") == 1
    assert pins.count("## S3:") == 1
    assert pins.count("## S4:") == 1
    assert pins.count("## S5:") == 1
    assert "No additional unnamed\nprimary paper was opened." in pins
    for marker in SOURCE_PIN_MARKERS:
        assert marker in pins, f"missing bibliographic marker: {marker}"
    for item in ("T110", "T117", "T121", "T122", "T123 r0", "T124"):
        assert report.count(f"| {item} |") == 1, f"bad comparator row count: {item}"
    assert "separated from one in absolute value" not in pins
    assert "lambda(n)lambda(n+h) <= 1-delta(h)" in pins
    print("caps, candidates, comparisons, transfer, verdict, and scope: ok")


def main() -> None:
    check_hashes()
    check_source_anchors()
    check_prior_anchors()
    check_walsh_identity()
    check_subset_counts()
    check_report_contract()
    print("T125 deterministic replay: PASS (experiment only)")


if __name__ == "__main__":
    main()
