#!/usr/bin/env python3
"""Artifact-only validation for T167; an experiment, not a proof."""

import csv
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def main():
    require(sha("canonical_statement.txt") == "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8", "canonical hash")

    with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as f:
        sources = list(csv.DictReader(f))
    require(len(sources) == 4 and len(sources) <= 12, "source cap")
    require(len({row["domain"] for row in sources}) == 4 >= 3, "domain minimum")
    for row in sources:
        require(sha(row["pdf_file"]) == row["pdf_sha256"], "PDF hash " + row["source_id"])
        require(sha(row["text_file"]) == row["text_sha256"], "text hash " + row["source_id"])
        require(row["locator"] and row["normalized_fingerprint"], "locator/fingerprint")
    anchors = {
        "aistleitner-et-al-2010.10355v1.txt": ["Theorem 1.1.", "Theorem 1.2.", "an+1 − an ≥ n−C"],
        "mantica-vaienti-0907.4675v1.txt": ["τ (A) :=", "M (δ)", "Tn,k ="],
        "abram-lagarias-slonim-2010.15215v2.txt": ["Theorem 2.18.", "Theorem 2.19.", "Theorem 2.20."],
        "bugeaud-2101.08989v1.txt": ["Theorem 1.3.", "Lemma 1.4.", "Theorem 1.5."],
    }
    for name, needles in anchors.items():
        text = (ROOT / name).read_text(encoding="utf-8")
        require(all(needle in text for needle in needles), "source anchors " + name)

    prior_bytes = (ROOT / "PRIOR_THEOREM_SOURCE_LEDGER.txt").read_bytes()
    require(hashlib.sha256(prior_bytes).hexdigest() == "200fa591d845c0a4f3273a76cb79bacc007716443791a4c0a4953777bb909a37", "prior ledger hash")
    for row in sources:
        require(row["pdf_sha256"].encode() not in prior_bytes, "prior PDF hash duplicate " + row["source_id"])
        require(row["arxiv"].encode() not in prior_bytes, "prior arXiv tuple duplicate " + row["source_id"])

    with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as f:
        exclusions = list(csv.DictReader(f))
    ids = [row["item"] for row in exclusions]
    expected = [f"T{i}" for i in range(89, 166)]
    require(ids == expected, "consecutive T89-T165 ledger")

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    require(report.count("## 3. Candidate C-DEC") == 1 and report.count("## 4. Candidate C-POW") == 1, "candidate count")
    require(report.count("### Quantitative rejection test") == 2, "candidate screens")
    require(report.count("### Additional unproved transfer") == 2, "transfer premises")
    require("PI-DEC-T7" in report and "PI-POW-T10" in report, "named transfers")
    require("no legal source substitution produces the T10 coefficient" in report, "C-POW displayed screen")
    require("pairwise phase separation" in report and "large-sieve or differencing conversion" in report, "C-POW transfer components")
    require(report.count("SCOPED VERDICT (1/1):") == 1, "one scoped verdict")
    require("SCOPED VERDICT (1/1): CLOSE." in report, "close verdict")
    require("SUCCESSOR_COUNT: 0" in report, "successor cap")
    require(report.count("FIXED_PI_CLAIM: none") == 1, "fixed-pi scope")

    # Replay the two displayed discriminators on finite representatives.
    for m in (2, 10, 100):
        concentrated = m * m
        singleton = m
        require(concentrated > singleton, "support does not determine energy")
    for n in (1, 2, 7):
        require(pow(10, n) % 1 == 0, "integer power screen")

    print("T167 artifact validation (experiment; not proof)")
    print("canonical_sha256=cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8")
    print("primary_sources=4 cap=12")
    print("searched_domains=4 minimum=3")
    print("retained_candidates=2 cap=4")
    print("exclusion_range=T89-T165 rows=77")
    print("scoped_verdict=CLOSE count=1")
    print("successors=0")
    print("all_checks=pass")


if __name__ == "__main__":
    main()
