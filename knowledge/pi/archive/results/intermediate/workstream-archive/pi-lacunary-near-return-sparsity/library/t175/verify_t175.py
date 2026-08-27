#!/usr/bin/env python3
import csv
import hashlib
import math
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
CANONICAL_HASH = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
DOMAINS = {
    "restricted_denominator_approximation",
    "arithmetic_or_fractal_Fourier_decay",
    "Mahler_or_functional_equation_constants",
}
PRIORS = {"T3", "T45", "T90", "T104", "T113", "T116", "T167", "T171", "T173", "T174"}


def sha256(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def check_grid_cover_samples():
    checked = 0
    for M in range(1, 5):
        for R in range(1, 4):
            for H in range(1, 3):
                for eta in (0.25, 0.5, 1.0):
                    L = (2 * math.pi / 9) * H * (10**R - 1) * (10**M - 1)
                    K = math.ceil(2 * L / (eta * M))
                    assert K >= 1
                    assert 1 / K <= eta * M / (2 * L) + 1e-15
                    assert 3 / K <= 3 * eta * M / (2 * L) + 1e-15
                    checked += 1
    return checked


def main():
    assert sha256("canonical_statement.txt") == CANONICAL_HASH
    with (ROOT / "SOURCE_LEDGER.csv").open(newline="", encoding="utf-8") as handle:
        sources = list(csv.DictReader(handle))
    assert len(sources) == 3
    assert {row["domain"] for row in sources} == DOMAINS
    assert len({row["stable_id"] for row in sources}) == 3
    assert len({row["candidate"] for row in sources}) == 3
    assert all(row["exact_locator"] and row["theorem_range"] for row in sources)
    for row in sources:
        assert sha256(row["pdf_file"]) == row["pdf_sha256"]
        assert sha256(row["text_file"]) == row["text_sha256"]

    with (ROOT / "PRIOR_COMPARISON.csv").open(newline="", encoding="utf-8") as handle:
        priors = list(csv.DictReader(handle))
    assert len(priors) == 10
    assert {row["item"] for row in priors} == PRIORS
    assert all(row["used_as_premise"] == "no" for row in priors)
    assert "unverified note readable" in next(row["available_level"] for row in priors if row["item"] == "T113")
    assert all("active unavailable" in next(row["available_level"] for row in priors if row["item"] == item) for item in ("T173", "T174"))

    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert report.count("SCOPED VERDICT (1/1): CLOSE.") == 1
    assert "SUCCESSOR_COUNT: 0" in report
    assert report.count("**Independent prescribed-point test (one).**") == 3
    assert report.count("**Disposition:** reject") == 3
    assert "FIXED_PI_CLAIM: none" in report
    assert "A1_CLAIM: none" in report
    assert "C1_CLAIM: none" in report
    assert "C2_CLAIM: none" in report
    assert "unproved" in report.lower()
    assert "rational-phase term operations = at most 2*K*R*H*M" in report
    assert "field degree\nat most `K`" in report
    assert "eta in Q, 0<eta<=1" in report
    assert "Apply S3's arithmetic theorem, independently of S2's ambient-measure theorem" in report
    assert len(re.findall(r"^### 4\.[123] C-", report, flags=re.MULTILINE)) == 3

    checked = check_grid_cover_samples()
    print("T175 artifact replay: PASS")
    print("canonical hash: PASS")
    print("searched domains: 3")
    print("new source/theorem tuples: 3 (cap 8)")
    print("candidates: 3 (cap 3)")
    print("independent prescribed-point tests: 3")
    print("prior comparisons: 10")
    print("scoped verdicts: 1")
    print("successors: 0")
    print(f"bounded cover arithmetic samples: {checked}")


if __name__ == "__main__":
    main()
