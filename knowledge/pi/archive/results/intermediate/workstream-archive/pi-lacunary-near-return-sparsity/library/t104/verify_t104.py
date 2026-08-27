#!/usr/bin/env python3
"""Self-contained integrity and arithmetic replay for the T104 survey."""

from __future__ import annotations

import hashlib
import math
import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "adamczewski-bell-smertnig-2003.03429.pdf": "c70932ece1c4cdcf5a62b39f91103c98841b3b958f3f622d58550322b9469353",
    "algom-rodriguez-hertz-wang-2407.11688.pdf": "b3eb5abb5f904ffaed7d0e496cc096ff686a8d52f7860876ded2ebd66c0a7d9d",
    "baker-banaji-2401.01241v2.pdf": "f07b9e579360cff6843fccb526086d27ea454925d6ed46d297fff274ca5689e6",
    "chaubey-yesha-2108.00431v1.pdf": "b660b086d52ecaf9d2e7abe13bcc306765dbc1166076ccb9ddbb14d1461e7e54",
    "hauke-ramirez-2508.01433v1.pdf": "fae15d1d5e0d869a0cf1cebd406da06087010f96466a6012531acd441647ab89",
    "poulet-rivoal-hal-03703010v1.pdf": "05bfb82585d161d043460b92237931729b91bf2ebb1636cd52d3ead62a26421f",
    "rajchert-2411.10733.pdf": "d0d407758686605a1e6bcdbc5631cad5bb3d6cf46781cc4ded1d6ce8cbb94760",
    "rudnick-technau-2001.08820.pdf": "364164f781a31ad5267b3c43d91b0593418744e8ac9073407e24581981b887b2",
    "sahlsten-stevens-2009.01703.pdf": "ba4878034d08a46c0e5cad13b4028922ba1ae058f0a55d11f111c4d8706693bf",
    "sanford-2606.02620v1.pdf": "4012d480b3c3aff5d2a36c4cc92d2e57027baa9b64454b77edfcaf3b2fb45b0b",
    "varju-yu-2004.09358.pdf": "4f8fe4bb024df9d7c0c804f93f261f3c4f21cc4d9410f9984804ad60594e7fad",
    "wang-li-li-2302.03923v2.pdf": "278dca3331322b1a64d34fb04651e131e7eb3a6482b5be5b69e9db29d39670ad",
}

PDF_ANCHORS = {
    "rajchert-2411.10733.pdf": ("Theorem 3.13",),
    "adamczewski-bell-smertnig-2003.03429.pdf": ("Theorem 1.2",),
    "poulet-rivoal-hal-03703010v1.pdf": ("Theorem 2", "(H6)"),
    "sanford-2606.02620v1.pdf": ("Theorem 3", "Theorem 4"),
    "hauke-ramirez-2508.01433v1.pdf": ("Theorem 2", "Lemma 8"),
    "wang-li-li-2302.03923v2.pdf": ("Theorem 1.1",),
    "varju-yu-2004.09358.pdf": ("Theorem 1.5", "Theorem 1.10"),
    "sahlsten-stevens-2009.01703.pdf": ("Theorem 1.1", "Total non-linearity"),
    "algom-rodriguez-hertz-wang-2407.11688.pdf": ("Theorem 1.1", "analytic planar curve"),
    "rudnick-technau-2001.08820.pdf": ("Theorem 1.1", "Proposition 4.2"),
    "chaubey-yesha-2108.00431v1.pdf": ("Theorem 1", "Proposition 2"),
    "baker-banaji-2401.01241v2.pdf": ("Theorem 1.2", "Theorem 2.7"),
}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def check_hashes() -> int:
    for name, expected in EXPECTED.items():
        path = ROOT / name
        assert path.is_file(), f"missing delivered input: {name}"
        actual = digest(path)
        assert actual == expected, f"hash mismatch for {name}: {actual}"
    return len(EXPECTED) - 1


def check_report() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="ascii")
    counters = {
        "PRIMARY_SOURCE_COUNT": 12,
        "SEARCHED_DOMAIN_COUNT": 4,
        "RETAINED_FINGERPRINT_COUNT": 4,
        "TERMINAL_VERDICT_COUNT": 1,
        "SUCCESSOR_COUNT": 0,
    }
    for key, value in counters.items():
        assert report.count(f"{key}: {value}") >= 1, key

    assert report.count("FINGERPRINT_CARD:") == 4
    assert report.count("SOURCE_CLAIM:") == 4
    assert report.count("NORMALIZED_FINGERPRINT:") == 4
    assert report.count("NEAREST_BRANCH:") == 4
    assert report.count("REJECTION_TEST:") == 4
    assert report.count("TRANSFER_PREMISE:") == 4
    assert report.count("DISPOSITION:") == 4
    assert len(re.findall(r"^PORTFOLIO_VERDICT:", report, re.MULTILINE)) == 1
    assert "PORTFOLIO_VERDICT: hold as model" in report

    for name in EXPECTED:
        assert name in report or name == "canonical_statement.txt"
    for forbidden in ("PORTFOLIO_VERDICT: develop", "PORTFOLIO_VERDICT: close"):
        assert forbidden not in report


def check_pdf_anchors() -> None:
    pdftotext = shutil.which("pdftotext")
    assert pdftotext is not None, "pdftotext is required for source-anchor replay"
    for name, anchors in PDF_ANCHORS.items():
        result = subprocess.run(
            [pdftotext, "-layout", str(ROOT / name), "-"],
            check=True,
            capture_output=True,
            text=True,
        )
        text = result.stdout
        for anchor in anchors:
            assert anchor in text, f"missing anchor {anchor!r} in {name}"


def check_arithmetic() -> None:
    assert 262_144**2 == 68_719_476_736

    # F1: every radial Fourier character is exactly periodic on s_m=r^(-m).
    for r in (2, 3, 10):
        for m in range(1, 8):
            for k in (-3, -1, 1, 4):
                s = r ** (-m)
                value = s ** (-2j * math.pi * k / math.log(r))
                assert abs(value - 1) < 1e-12

    # F2: diagonal and pairwise-independent contributions to the averaged sum.
    for n in range(1, 20):
        for rho_num in (1, 2, 3):
            rho = rho_num / 16
            diagonal = 2 * n * rho
            off_diagonal = 4 * n * (n - 1) * rho * rho
            expanded = n * (2 * rho) + n * (n - 1) * (2 * rho) ** 2
            assert abs(diagonal + off_diagonal - expanded) < 1e-12

    # F4: the elementary frequency separation used in the L2 majorant.
    for j in range(1, 20):
        for k in range(j):
            assert 10**j - 10**k >= 9 * 10 ** (j - 1)


def check_manifest() -> None:
    manifest = ROOT / "SHA256SUMS"
    assert manifest.is_file(), "missing SHA256SUMS"
    lines = [line.split(maxsplit=1) for line in manifest.read_text().splitlines()]
    entries = {name.lstrip("* "): sha for sha, name in lines}
    expected_names = {
        path.name for path in ROOT.iterdir() if path.is_file() and path.name != "SHA256SUMS"
    }
    assert set(entries) == expected_names
    for name, expected in entries.items():
        assert digest(ROOT / name) == expected, f"manifest mismatch: {name}"


def main() -> None:
    source_count = check_hashes()
    check_report()
    check_pdf_anchors()
    check_arithmetic()
    check_manifest()
    print(f"PASS: {source_count} primary PDFs, 4 domains, 4 fingerprints")
    print("PASS: canonical hash, source anchors, caps, arithmetic, and unique verdict")
    print("LABEL: integrity replay only; no pi, C1, or C2 claim")


if __name__ == "__main__":
    main()
