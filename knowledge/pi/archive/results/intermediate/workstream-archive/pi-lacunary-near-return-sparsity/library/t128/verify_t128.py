#!/usr/bin/env python3
"""Self-contained finite audit for the T128 literature package."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent

EXPECTED_HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "ugalde-2000.pdf": "4ec6441594245faa84a08c86873aed7dbabc735f23765bf140603ffd5304d35c",
    "levin-1999.pdf": "a09ae848cd10e030231aed8e19ab4e142c1ee1d9aeae48114e886d2b8a8e999f",
    "becher-carton-1805.03713v1.pdf": "3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448",
    "hofer-larcher-2211.04212v1.pdf": "cc8fd0a4373161ed1e4c6b15599e1a65cf648d5bd8856f3108fe0912e8b7ed0b",
    "aistleitner-becher-scheerer-slaman-1707.02628v1.pdf": "a219bc04d28939e62b00e4bc4779dd9a42e08a8e88d33d2ae8f756f31bc14a0a",
    "balkova-1107.5033v1.pdf": "6c36631b5ab7c44a19dd6575b94a109fb10c27a4a216ab9509d40ab6cf24e3bc",
    "goc-schaeffer-shallit-1206.5352v1.pdf": "59f53bcb52c4eb696097e0211ea6fd9cc0f0b96129d8ed24f647a4cef02a1667",
    "prior-t121-REPORT.md": "01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2",
}

ANCHORS = {
    "ugalde-2000.pdf": [
        "An Eulerian path on B(b, k) defines a Hamiltonian path",
        "Extension procedure for the de Bruijn digraphs",
        "Start with the block",
    ],
    "levin-1999.pdf": [
        "is called the discrepancy",
        "Pascal's triangle mod 2",
        "Corollary 2. Let",
        "End of the proof of Theorem 2",
    ],
    "becher-carton-1805.03713v1.pdf": [
        "Theorem 1. For each base b the number x defined by Levin",
        "nested perfect necklaces",
    ],
    "hofer-larcher-2211.04212v1.pdf": [
        "Theorem 2. Let b",
        "Then the star discrepancy",
    ],
    "aistleitner-becher-scheerer-slaman-1707.02628v1.pdf": [
        "Theorem 1. There is an absolutely normal number x",
        "3433",
        "leftmost interval",
    ],
    "balkova-1107.5033v1.pdf": [
        "The generalized Thue-Morse word",
        "Theorem 2.4",
        "Example 4.2",
    ],
    "goc-schaeffer-shallit-1206.5352v1.pdf": [
        "The subword complexity function",
        "consider the Thue-Morse sequence",
        "it is well-known that",
    ],
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def normalized(text: str) -> str:
    return " ".join(text.replace("’", "'").split())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_hashes_and_pdfs() -> None:
    for name, expected in EXPECTED_HASHES.items():
        path = ROOT / name
        require(path.is_file(), f"missing pinned file: {name}")
        require(sha256(path) == expected, f"SHA-256 mismatch: {name}")
        if name.endswith(".pdf"):
            require(path.read_bytes()[:5] == b"%PDF-", f"not a PDF: {name}")


def check_source_anchors() -> str:
    tool = shutil.which("pdftotext")
    if tool is None:
        return "pdftotext unavailable; PDF hashes and excerpt index checked"
    with tempfile.TemporaryDirectory() as directory:
        temp = Path(directory)
        for name, anchors in ANCHORS.items():
            output = temp / (Path(name).stem + ".txt")
            subprocess.run(
                [tool, "-layout", str(ROOT / name), str(output)],
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            text = normalized(output.read_text(encoding="utf-8", errors="replace"))
            for anchor in anchors:
                require(normalized(anchor) in text, f"missing source anchor {name}: {anchor}")
    return "all fresh pdftotext anchors found"


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    report_flat = normalized(report)
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
    excerpts = (ROOT / "SOURCE_EXCERPTS.txt").read_text(encoding="utf-8")

    required_counts = {
        "PRIMARY_SOURCE_COUNT: 7": 1,
        "PRIMARY_SOURCE_CAP: 12": 1,
        "RETAINED_CANDIDATE_COUNT: 4": 1,
        "RETAINED_CANDIDATE_CAP: 4": 1,
        "SCOPED_VERDICT_COUNT: 1": 1,
        "SUCCESSOR_COUNT: 1": 1,
    }
    for marker, minimum in required_counts.items():
        require(report.count(marker) >= minimum, f"missing count marker: {marker}")
    require(report.count("SCOPED_VERDICT:") == 1, "scoped verdict is not unique")
    require(report.count("SUCCESSOR:") == 1, "successor is not unique")
    require("SCOPED_VERDICT: develop" in report, "unexpected scoped verdict")
    require(report.count("PI-SPEC (`conjecture`, additional pi-specific premise)") == 1,
            "pi-specific premise marker missing or duplicated")

    for card in ("C-UG", "C-LEV", "C-ABS", "C-TM"):
        require(card in report, f"missing candidate card: {card}")
    for comparator in ("T2", "T116", "T120", "T121", "T122"):
        require(comparator in report, f"missing comparator: {comparator}")
    for source in range(1, 8):
        require(f"## S{source}:" in pins, f"missing source pin S{source}")
        require(f"[S{source}-" in excerpts, f"missing excerpt anchor S{source}")

    prior_t121 = (ROOT / "prior-t121-REPORT.md").read_text(encoding="utf-8")
    require("Duplication boundary:" in report and "C-LEV reuses that same normalized lane" in report,
            "T121/C-LEV duplication boundary missing")
    require("no candidate-level overlap or distinctness claim is made" in report_flat,
            "T122 refreshed availability boundary missing")
    require("no mechanism, verdict, verification level, overlap, or distinctness is inferred" in report_flat,
            "T122 non-inference boundary missing")
    for unsupported in (
        "T122 retry status",
        "two T122 result records",
        "T122's selected develop mechanism",
        "terminal verdict `reject`",
    ):
        require(unsupported not in report, f"unsupported T122 status claim retained: {unsupported}")
    require("F-NECK: nested-perfect necklace block energy" in prior_t121,
            "vendored T121 necklace card missing")
    require("already represented by T90/T110" in prior_t121,
            "vendored T121 pointwise-discrepancy screen missing")
    require("Every point below changes the point fixed in the canonical question" in report,
            "A13 scope firewall missing")
    require("It makes no fixed-pi, C1, or C2 claim." in report,
            "fixed-pi/C1/C2 scope firewall missing")
    require("no T107 triangular-defect claim" in report,
            "T107 rejection boundary missing")
    require(report.count("0<s<=1") >= 4, "necessary exponent restriction missing")
    require("not certified to meet the strict effective-rate requirement" in report_flat,
            "ABSS effective-threshold rejection missing")
    require("max(100,ceil(log_2 R))" in report,
            "ABSS initialization correction missing")
    require("PRIMARY_SOURCE_COUNT: 7" in search, "search source count missing")
    require("RETAINED_CANDIDATE_COUNT: 4" in search, "search candidate count missing")


def check_ugalde_exact_energy() -> int:
    cases = 0
    for n in range(1, 8):
        prefix_starts = 10**n
        prefix_length = prefix_starts + n - 1
        require(prefix_length - 1 == prefix_starts + n - 2, "endpoint mismatch")
        for m in range(1, n + 1):
            occupancy = 10 ** (n - m)
            energy = (10**m) * occupancy * occupancy
            require(energy == prefix_starts * prefix_starts // (10**m),
                    f"Ugalde energy identity failed at n={n}, m={m}")
            cases += 1
    return cases


def check_levin_absorption() -> int:
    cases = 0
    # kappa=3/4 and s=1. The finite values only sanity-check the displayed
    # asymptotic absorption; they do not prove it.
    for exponent in (24, 32, 48, 64, 80):
        n_value = 10**exponent
        m = (3 * exponent) // 4
        log10_n = exponent
        delta = 20 * log10_n + 400 * log10_n * log10_n
        main = n_value * n_value // (10**m)
        error = n_value * delta
        require(error <= main, f"Levin finite absorption failed at 10^{exponent}")
        cases += 1
    return cases


def check_abss_power_range() -> int:
    cases = 0
    # kappa=2/5 is strictly below 1/2. Ignore the source's effective N0 and
    # test only sufficiently large powers where the displayed inequality wins.
    for exponent in (56, 64, 72, 80):
        n_value = 10**exponent
        m = (2 * exponent) // 5
        main = n_value * n_value // (10**m)
        error = 34330 * math.isqrt(n_value) * n_value
        require(error <= main, f"ABSS finite absorption failed at 10^{exponent}")
        cases += 1
    return cases


def check_thue_morse_rejection() -> int:
    cases = 0
    # kappa=1/2 and s=1. Verify exact integer separation at large powers.
    for exponent in (16, 24, 32, 48):
        n_value = 10**exponent
        m = exponent // 2
        denominator = 4 * m - 2
        target = n_value + n_value * n_value // (10**m)
        require(n_value * n_value > denominator * target,
                f"Thue-Morse rejection check failed at 10^{exponent}")
        cases += 1
    return cases


def main() -> None:
    check_hashes_and_pdfs()
    anchor_status = check_source_anchors()
    check_report_contract()
    result = {
        "status": "ok",
        "item_id": "T128",
        "label": "experiment",
        "canonical_sha256": EXPECTED_HASHES["canonical_statement.txt"],
        "primary_source_count": 7,
        "primary_source_cap": 12,
        "retained_candidate_count": 4,
        "retained_candidate_cap": 4,
        "source_anchor_status": anchor_status,
        "t122_comparison_boundary": "availability-only; no content inferred",
        "finite_checks": {
            "ugalde_exact_energy_cases": check_ugalde_exact_energy(),
            "levin_absorption_cases": check_levin_absorption(),
            "abss_power_range_cases": check_abss_power_range(),
            "thue_morse_rejection_cases": check_thue_morse_rejection(),
        },
        "warning": "Finite replay checks are not proofs of asymptotic or fixed-pi claims.",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
