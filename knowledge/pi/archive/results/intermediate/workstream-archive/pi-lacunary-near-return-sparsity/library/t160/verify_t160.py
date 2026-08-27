#!/usr/bin/env python3
"""Self-contained deterministic checks for the T160 literature package."""

from __future__ import annotations

import csv
import hashlib
import re
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "debowski-1609.04683v4.pdf": "9fe5c1e472f5e78c0cc480fb7a8ae3f7a9b7fa540d8d304a8819ae69386c5af6",
    "kosolobov-2410.00209v1.pdf": "390cd15bc009eb61e429dccff36f76a8364555f9eeda472dfd30925402285499",
    "pirsic-stockinger-1710.09313v2.pdf": "27ba23a17b6762357e263b4425951da309112760dc886b54b9105ce865a20d61",
    "he-liao-2302.05149v2.pdf": "216ba701ee20e4bdb476395c966a57993079b0c069a5f7439de7e322c06e203b",
    "fouvry-kowalski-michel-1307.0135v2.pdf": "ddd6f5dc551523fca670acfcf653f22a76be29445fd5fb44b9dc80ab98f18107",
    "fkmrrs-1508.00512v3.pdf": "3591f4c296190089850617665be59ffbc327c827496921e46fee91ded30cb922",
}

ANCHORS = {
    "debowski-1609.04683v4.pdf": ["Theorem 1 (cf.", "Theorem 8 For a stationary process"],
    "kosolobov-2410.00209v1.pdf": ["Main definition.", "Theorem 1. Any string of length n contains"],
    "pirsic-stockinger-1710.09313v2.pdf": ["Theorem 1 The sequence", "Note that the pairs", "are ordered"],
    "he-liao-2302.05149v2.pdf": ["Definition 1.1 (Piecewise expanding map)", "Theorem 1.3. Let T"],
    "fouvry-kowalski-michel-1307.0135v2.pdf": ["Theorem 1.1 (Sliding sum bound)", "Theorem 2.1 (Sliding-sum bound)"],
    "fkmrrs-1508.00512v3.pdf": ["Theorem 1.1. For any interval", "Theorem 1.2. Let m"],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def energy(counts: list[int]) -> int:
    return sum(c * c for c in counts)


def de_bruijn(k: int, n: int) -> list[int]:
    alphabet = list(range(k))
    a = [0] * (k * n)
    sequence: list[int] = []

    def db(t: int, p: int) -> None:
        if t > n:
            if n % p == 0:
                sequence.extend(a[1 : p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, k):
                a[t] = j
                db(t + 1, t)

    db(1, 1)
    require(set(sequence) <= set(alphabet), "de Bruijn alphabet")
    return sequence


def linear_counts(word: list[int], starts: int, m: int) -> list[int]:
    blocks = []
    for i in range(starts):
        require(i + m <= len(word), "nonwrapping endpoint")
        blocks.append(tuple(word[i : i + m]))
    return list(Counter(blocks).values())


def main() -> None:
    for name, digest in EXPECTED.items():
        require(sha256(ROOT / name) == digest, f"hash mismatch: {name}")
    print("HASHES: 7/7 exact")

    with tempfile.TemporaryDirectory() as tmp:
        for name, anchors in ANCHORS.items():
            out = Path(tmp) / (Path(name).stem + ".txt")
            subprocess.run(
                ["pdftotext", "-layout", str(ROOT / name), str(out)],
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            text = out.read_text(encoding="utf-8", errors="replace")
            for anchor in anchors:
                require(anchor in text, f"missing source anchor {name}: {anchor}")
        s1_page9 = Path(tmp) / "s1-page9.txt"
        subprocess.run(
            ["pdftotext", "-f", "9", "-l", "9", "-layout", str(ROOT / "debowski-1609.04683v4.pdf"), str(s1_page9)],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        page9 = s1_page9.read_text(encoding="utf-8", errors="replace")
        require("Theorem 8 For a stationary process" in page9 and "(45)" in page9, "S1 Theorem 8 physical page 9")
        s3_page3 = Path(tmp) / "s3-page3.txt"
        s3_page8 = Path(tmp) / "s3-page8.txt"
        subprocess.run(
            ["pdftotext", "-f", "3", "-l", "3", "-layout", str(ROOT / "pirsic-stockinger-1710.09313v2.pdf"), str(s3_page3)],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        subprocess.run(
            ["pdftotext", "-f", "8", "-l", "8", "-layout", str(ROOT / "pirsic-stockinger-1710.09313v2.pdf"), str(s3_page8)],
            check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        page3 = s3_page3.read_text(encoding="utf-8", errors="replace")
        page8 = s3_page8.read_text(encoding="utf-8", errors="replace")
        require("d = 2e" in page3 and "N = 2d+e" in page3, "S3 extraction anchors for d=2^e and N=2^(d+e)")
        require("Corollary 1" in page8, "S3 Corollary 1 physical page 8")
    print("SOURCE_ANCHORS: 13/13 located; S1/S3 physical pages checked")

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    require(report.count("PRIMARY_SOURCE_COUNT: 6") == 1, "source count")
    require(report.count("SEARCHED_DOMAIN_COUNT: 3") == 1, "domain count")
    require(report.count("RETAINED_CANDIDATE_COUNT: 3") == 1, "candidate count")
    require(pins.count("## DOMAIN ") == 3, "exactly three domains")
    require(pins.count("### SOURCE S") == 6, "exactly six sources")
    require(pins.count("Retained tuple C-") == 3, "exactly three tuples")
    require("*Functiones et Approximatio* 60(2) (2019), 253-262." in pins, "S3 journal metadata")
    require("Satadal Ganguly" not in pins, "S6 exact six-author list")
    s6_authors = [
        "Etienne Fouvry", "Emmanuel Kowalski", "Philippe Michel",
        "C. S. Raju", "Joel Rivat", "K. Soundararajan",
    ]
    require(all(author in pins for author in s6_authors), "S6 author names")
    print("CAPS: sources=6/8 candidates=3/3 domains=3/3")
    print("BIBLIOGRAPHY: S3 journal metadata and S6 six-author list exact")

    with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    items = [row["item"] for row in rows]
    require(items[:69] == [f"T{i}" for i in range(89, 158)], "ledger T89-T157")
    require(items[69:] == ["T158", "T159"], "T158/T159 reservations")
    require(len(items) == len(set(items)), "duplicate ledger item")
    t158, t159 = rows[69], rows[70]
    require(t158["available_level"] == "LC/PS/EXP", "refreshed T158 level")
    require("7ac71c0020e63aa8b944e43a4d122179eeef4f64961844497d8a84c41a11159f" in t158["source_or_comparator"], "refreshed T158 report hash")
    require(t159["available_level"] == "LC source/PS note/EXP", "refreshed T159 level")
    require("67c89ec92afaa0d3ebe02617346bb0ae5aa2ffd2184e6ea0ecd4843a0cd85045" in t159["source_or_comparator"], "refreshed T159 report hash")
    require("reserve graph conductance" in t158["T160_boundary"], "T158 mechanism reservation")
    require("reserve stochastic collision locations" in t159["T160_boundary"], "T159 mechanism reservation")
    print("LEDGER: T89-T157 consecutive; T158 pinned and T159 unverified-note mechanisms reserved")

    definitions = [
        "**Recurrence block.**", "**Endpoint.**", "**Overlap.**",
        "**First recurrence.**", "**Multiplicity.**",
        "**Ordered-pair collision energy.**", "**Logarithmic-depth range.**",
    ]
    for marker in definitions:
        require(marker in report, f"missing definition {marker}")
    substitutions = ["Candidate C-CLOSED", "Candidate C-CHAMP", "Candidate C-SHORT"]
    for marker in substitutions:
        require(marker in report, f"missing substitution {marker}")
    for item in ["T95/T100", "T119", "T121", "T131", "T149", "T152", "T153", "T154", "T155", "T156", "T157", "T158", "T159"]:
        require(item in report, f"missing comparator {item}")
    require("T158 report argues (proof sketch)" in report, "T158 sketch citation firewall")
    require("T159 note argues (unverified)" in report, "T159 sketch citation firewall")
    require("T158/T159 remain\nreserved comparators" in report, "refreshed reservation boundary")
    print("CONTENT: definitions=7 substitutions=3 mandatory-comparators=13")

    m, M = 7, 64
    require(energy([M]) == M * M, "constant separator")
    p = 8
    require(energy([M // p] * p) == M * M // p, "periodic separator")
    b, r = 2, 5
    cycle = de_bruijn(b, r)
    doubled = cycle + cycle + cycle[: r - 1]
    doubled_counts = linear_counts(doubled, 2 * (b**r), r)
    require(len(doubled_counts) == b**r, "de Bruijn support")
    require(set(doubled_counts) == {2}, "de Bruijn multiplicity")
    require(energy(doubled_counts) == 4 * (b**r), "de Bruijn energy")
    R = 23
    require(energy([R]) == R * R, "shared prefix lower contribution")
    K = 4
    require(energy([R] * K) == K * R * R, "bounded multi-core")
    names = ["Exact constant test", "Primitive-periodic test", "Doubled-de-Bruijn test", "Shared-prefix test", "Bounded multi-core test"]
    for name in names:
        require(report.count(name) == 1, f"separator marker {name}")
    print("SEPARATORS: constant periodic doubled-de-Bruijn shared-prefix multi-core PASS")

    require(len(re.findall(r"SCOPED_VERDICT \(1/1\):", report)) == 1, "one verdict")
    require(report.count("SUCCESSOR (0/1): NONE.") == 1, "zero successors")
    for label in ["literature-checked", "proof sketch", "experiment", "related-model conclusion", "unproved pi transfer"]:
        require(label in report, f"label firewall {label}")
    for claim in ["FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none", "C2_CLAIM: none"]:
        require(report.count(claim) == 1, f"claim firewall {claim}")
    require("PI-PAIR-CERT" in report and "NOT ASSERTED" in report, "unproved transfer")
    print("FIREWALL: labels separated; fixed-pi/A1/C1/C2 claims none")
    print("ENDPOINT: scoped verdicts=1 successors=0")


if __name__ == "__main__":
    main()
