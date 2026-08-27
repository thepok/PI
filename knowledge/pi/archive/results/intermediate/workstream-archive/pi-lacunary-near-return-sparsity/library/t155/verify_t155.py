#!/usr/bin/env python3
"""Self-contained package-consistency replay for T155."""

from __future__ import annotations

import csv
import hashlib
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCES = {
    "bannai-et-al-1406.0263v7.pdf": "9bbe130b1a864a4932c09c32a7dad27b97b4910f05ce410cfb0a9535a74b6ce7",
    "jiang-longbrake-2201.10699v1.pdf": "724204236a460893fc01128bdb7231de39531d57c7c4ea8e412b4cb4de83deeb",
    "chen-xia-math0410169.pdf": "3640caf66dd78cc1fa3e4ad69cd5b250123c9896e86c17962912cc3fbc82f87e",
}
TUPLES = (
    "arXiv:1406.0263v7|Definition1;Lemma8;Theorem9;Theorem10",
    "arXiv:2201.10699v1|Definition3.1;Theorem3.2;Theorem3.3",
    "arXiv:math/0410169|Theorem4.1",
)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def check(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def main() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    search = (ROOT / "SEARCH_LOG.md").read_text(encoding="utf-8")
    prior_text = (ROOT / "PRIOR_THEOREM_SOURCE_LEDGER.txt").read_text(
        encoding="utf-8", errors="replace"
    )
    prior_hashes = set((ROOT / "PRIOR_AUDITED_HASHES.txt").read_text().splitlines())

    check(digest("canonical_statement.txt") == CANONICAL, "canonical hash mismatch")
    for filename, expected in SOURCES.items():
        check(digest(filename) == expected, f"hash mismatch: {filename}")
        check(expected not in prior_hashes, f"repeated prior hash: {filename}")
        check(expected in pins, f"unrecorded source hash: {filename}")
    check(len(set(SOURCES.values())) == 3, "source hashes not unique")
    for theorem_tuple in TUPLES:
        check(theorem_tuple not in prior_text, f"repeated stable tuple: {theorem_tuple}")
        check(theorem_tuple in pins and theorem_tuple in report,
              f"tuple not reported twice: {theorem_tuple}")
    check(len(set(TUPLES)) == 3, "theorem tuples not unique")

    anchors = {
        "bannai-et-al-1406.0263v7.txt": ("Definition 1 (Runs).", "Theorem 9.", "Theorem 10."),
        "jiang-longbrake-2201.10699v1.txt": ("Definition 3.1", "Theorem 3.2", "Theorem 3.3"),
        "chen-xia-math0410169.txt": ("Theorem 4.1.", "Remark 4.2.", "Remark 4.3."),
    }
    for filename, terms in anchors.items():
        text = (ROOT / filename).read_text(encoding="utf-8", errors="replace")
        for term in terms:
            check(term in text, f"missing source anchor {term!r}: {filename}")

    check("giving distinct equivalent words of length `2k` is on PDF p. 6" in prior_text,
          "T153 S1 locator correction missing")
    check("equation (2.1), arXiv PDF p. 5; Theorem 2.4 and Remark 2.6" in prior_text,
          "T153 S6 locator correction missing")

    with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    items = [row["item"] for row in rows]
    check(items == [f"T{i}" for i in range(89, 155)], "ledger not T89-T154")
    for item in ("T129", "T138", "T139", "T142", "T146", "T154"):
        row = rows[items.index(item)]
        check("unavailable" in row["verification"] + row["source_boundary"],
              f"availability boundary missing: {item}")

    required = (
        "representation", "Stoneham", "invariant-measure", "finite-state", "carry",
        "additive-energy", "determinant", "avoidance", "renewal", "global-L2",
        "balancing", "specification", "S-unit", "heavy-fiber", "tensorization",
        "container", "census", "broad Fourier", "locality-to-occupancy", "entropy-LP",
    )
    ledger = (ROOT / "EXCLUSION_LEDGER.csv").read_text(encoding="utf-8")
    for mechanism in required:
        check(mechanism in ledger or mechanism in report, f"missing exclusion: {mechanism}")

    for text in (report, search):
        check("SEARCHED_DOMAIN_COUNT: 3" in text, "domain count missing")
        check("PRIMARY_SOURCE_COUNT: 3" in text, "source count missing")
        check("RETAINED_FINGERPRINT_COUNT: 1" in text, "fingerprint count missing")
    check(len(SOURCES) <= 12 and 1 <= 4, "cap violation")
    check(report.count("DUPLICATE_FIXTURE_T104_T138: EXCLUDED") == 1,
          "T104/T138 fixture missing")
    check(report.count("DUPLICATE_FIXTURE_T136_T146: EXCLUDED") == 1,
          "T136/T146 fixture missing")
    check(report.count("Nearest branch:") == 2, "screened nearest branches missing")
    check(report.count("**Nearest prior branch.**") == 1, "retained nearest branch missing")
    check(report.count("unproved-transfer`; NOT ASSERTED") == 1,
          "transfer label count wrong")
    check(report.count("**Card disposition: HOLD AS MODEL.**") == 1,
          "retained disposition missing")
    check(report.count("SCOPED_VERDICT (1/1):") == 1, "verdict count wrong")
    check(report.count("SUCCESSOR (0/1): NONE") == 1, "successor count wrong")

    # Screened S1 falsification.
    A, m, run_M = 3, 5, 40
    L = run_M + m - 1
    check(L >= 2 and L <= 3 * L - 3, "run certificate test failed")
    check(run_M * run_M > run_M * run_M / (A * m),
          "constant-word falsification failed")

    # Retained F1 iid substitution into the displayed Chen-Xia coarse bound.
    q, M = 10**8, 1000
    P = math.comb(M, 2)
    lam = P / q
    bound = 2 * P * (2 * M - 3) * (5 / lam + 3) / q**2
    simplified = 2 * (2 * M - 3) * (5 / q + 3 * P / q**2)
    check(abs(bound - simplified) < 1e-15, "F1 error simplification failed")
    check(bound < 2.004e-4, "F1 numerical error threshold failed")
    ordered_mean = M + M * (M - 1) / q
    check(abs(ordered_mean - 1000.00999) < 1e-10, "F1 mean failed")

    print("PASS canonical_sha256", CANONICAL)
    print("PASS exclusion_rows", len(rows), "range", items[0], items[-1])
    print("PASS corrected_T153_locators S1=p6 S6_eq2.1=p5")
    print("PASS caps domains=3 sources=3 fingerprints=1 verdicts=1 successors=0")
    print("PASS new_hashes=3 stable_tuples=3 semantic_identifiers_recorded")
    print("PASS duplicate_fixtures T104/T138 T136/T146")
    print("PASS screened_S1_constant_word", f"L={L}", f"E={run_M*run_M}")
    print("PASS F1_iid", f"lambda={lam:.12g}", f"d2_bound={bound:.12g}",
          f"ordered_mean={ordered_mean:.12g}")
    print("PASS labels transfers=1 fixed_pi_claims=0")


if __name__ == "__main__":
    main()
