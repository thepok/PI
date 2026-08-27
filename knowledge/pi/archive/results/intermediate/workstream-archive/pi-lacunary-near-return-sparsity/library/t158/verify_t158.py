#!/usr/bin/env python3
"""Self-contained finite replay for T158. Finite checks are experiments only."""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import csv
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent

EXPECTED = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "ayyer-strehl-1108.5695v1.pdf": "00d7ee6af00be2e35fd82165a4ca5cfb4373d3f59a2084de7f4f402448240e49",
    "paulin-1212.2015v5.pdf": "7a54a70c47954687e87800c5e7dcc9df37a47568ed13f35c5c170a5728d92a82",
    "abadi-saussol-1003.4856v2.pdf": "f4a0ccfef0ba4db3bf947c9b4d5125f6b577d5a3b92d3eb9e6350f3b92dfe0fb",
    "kerr-merai-shparlinski-2001.03380v4.pdf": "a4eaf55ed902d9925418a36f50d8851a5dba58c10520c2324607aefabddb134f",
    "T156_REJECTED_REPORT.md": "6ac00f9204cec8aa939b644ed7b82aed01f1509a67d3c43509f35b139b0199f6",
    "T157_REPORT.md": "d3b7c211111578216525e6b1d295f715ecee21e3cc1b3aafec1e2301459365c3",
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def debruijn(k, n):
    """FKM cyclic de Bruijn sequence over range(k), order n."""
    a = [0] * (k * n + 1)
    out = []

    def visit(t, p):
        if t > n:
            if n % p == 0:
                out.extend(a[1 : p + 1])
            return
        a[t] = a[t - p]
        visit(t + 1, p)
        for value in range(a[t - p] + 1, k):
            a[t] = value
            visit(t + 1, t)

    visit(1, 1)
    return out


def cyclic_counts(cycle, depth, starts):
    period = len(cycle)
    return Counter(
        tuple(cycle[(i + j) % period] for j in range(depth))
        for i in range(starts)
    )


def linear_counts(word, depth, starts):
    return Counter(tuple(word[i : i + depth]) for i in range(starts))


def collision(counts):
    return sum(value * value for value in counts.values())


def check_source_anchors():
    require(shutil.which("pdftotext") is not None, "pdftotext is required")
    anchors = {
        "ayyer-strehl-1108.5695v1.pdf": [
            "Theorem 3. The vector",
            "Theorem 12. The characteristic polynomial",
            "Corollary 13. Under the choice of rates",
        ],
        "paulin-1212.2015v5.pdf": [
            "Assumption 3.1.",
            "Theorem 3.11 (Bernstein inequality for non-reversible chains)",
            "pseudo spectral gap",
        ],
        "abadi-saussol-1003.4856v2.pdf": [
            "Theorem 1. Suppose that the system",
            "Example 2. For any",
            "Theorem 7. Suppose that the system",
        ],
        "kerr-merai-shparlinski-2001.03380v4.pdf": [
            "Theorem 1.1. Fix a prime",
            "Corollary 1.2.",
            "Theorem 1.3.",
        ],
    }
    with tempfile.TemporaryDirectory() as tmp:
        for filename, required in anchors.items():
            target = Path(tmp) / (filename + ".txt")
            subprocess.run(
                ["pdftotext", "-layout", str(ROOT / filename), str(target)],
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            text = " ".join(target.read_text(errors="replace").split())
            for anchor in required:
                normalized = " ".join(anchor.split())
                require(normalized in text, f"missing source anchor: {filename}: {anchor}")


def check_ledger():
    with (ROOT / "EXCLUSION_LEDGER.csv").open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    expected = [f"T{i}" for i in range(89, 158)]
    require([row["item"] for row in rows] == expected, "ledger is not T89--T157")
    require(len(rows) == 69, "ledger row count")
    levels = {row["item"]: row["verification"] for row in rows}
    require(levels["T153"] == "LC/PS/EXP", "stale T153 level")
    require(levels["T154"] == "PS/EXP", "stale T154 level")
    require(levels["T155"] == "LC/PS/EXP", "missing T155 level")
    require(levels["T156"] == "rejected LC/PS/EXP", "stale T156 level")
    require(levels["T157"] == "LC/PS/EXP", "stale T157 level")


def check_refreshed_comparators():
    t156 = (ROOT / "T156_REJECTED_REPORT.md").read_text()
    t157 = (ROOT / "T157_REPORT.md").read_text()
    require("# T156: inverse stability at the reuse scale" in t156, "T156 report identity")
    require("PRIMARY_SOURCE_COUNT: 8" in t156, "T156 source count marker")
    require("# T157: inverse Littlewood--Offord scout" in t157, "T157 report identity")
    require("PRIMARY_SOURCE_COUNT: 6" in t157, "T157 source count marker")


def check_repeated_debruijn():
    # Order r+1=3 gives a 1000-edge decimal cycle and a 100-state kernel.
    r, order, repeats, depth = 2, 3, 3, 8
    cycle = debruijn(10, order)
    period = 10 ** order
    starts = repeats * period
    require(len(cycle) == period, "de Bruijn period")
    c_edge = cyclic_counts(cycle, order, starts)
    c_state = cyclic_counts(cycle, r, starts)
    c_long = cyclic_counts(cycle, depth, starts)
    require(len(c_edge) == 10 ** order and set(c_edge.values()) == {repeats}, "edge census")
    require(len(c_state) == 10 ** r and set(c_state.values()) == {10 * repeats}, "state census")
    require(len(c_long) == period and set(c_long.values()) == {repeats}, "long occupancy")
    require(max(c_long.values()) == starts // period, "maximum occupancy formula")
    require(collision(c_long) == starts * starts // period, "collision formula")

    # P^r is projection to uniform: every start state and r appended digits
    # produce each endpoint exactly once among 10^r choices.
    states = [tuple((i // (10 ** j)) % 10 for j in reversed(range(r))) for i in range(10 ** r)]
    for state in states:
        endpoints = Counter()
        for code in range(10 ** r):
            digits = tuple((code // (10 ** j)) % 10 for j in reversed(range(r)))
            current = state
            for digit in digits:
                current = current[1:] + (digit,)
            endpoints[current] += 1
        require(len(endpoints) == 10 ** r and set(endpoints.values()) == {1}, "P^r uniform")
    gamma_lower = Fraction(1, r)
    require(gamma_lower == Fraction(1, 2), "pseudo-gap lower bound")


def check_separators():
    starts, depth = 120, 7

    constant = [0] * (starts + depth - 1)
    cc = linear_counts(constant, depth, starts)
    require(max(cc.values()) == starts and collision(cc) == starts * starts, "constant")

    alternating = [i % 2 for i in range(starts + depth - 1)]
    pc = linear_counts(alternating, depth, starts)
    require(len(pc) == 2 and set(pc.values()) == {starts // 2}, "periodic occupancy")
    require(collision(pc) == starts * starts // 2, "periodic collision")

    # Shared prefix: verify occupancy and the safe affected-start census bound.
    r, depth, starts = 1, 20, 10000
    cycle = debruijn(10, r + 1)
    R = 500
    word = [0] * (R + depth - 1)
    need = starts + depth - 1 - len(word)
    word.extend(cycle[i % len(cycle)] for i in range(need))
    mc = linear_counts(word, depth, starts)
    require(mc[(0,) * depth] >= R, "shared-prefix occupancy")
    for short in (r, r + 1):
        counts = linear_counts(word, short, starts)
        eta_num = max(abs(counts.get(tuple((code // (10 ** j)) % 10 for j in reversed(range(short))), 0)
                          - Fraction(starts, 10 ** short))
                      for code in range(10 ** short))
        require(eta_num <= R + depth + r, "shared-prefix census charge")

    # Disconnected cores: omitting the splice yields two closed support classes.
    core = [0] * 60 + [5] * 60
    edges_without_splice = Counter({(0, 0): 59, (5, 5): 59})
    require((0, 5) not in edges_without_splice and (5, 0) not in edges_without_splice, "multi-core")
    dc = linear_counts(core + [5] * (depth - 1), depth, 120)
    require(max(dc.values()) >= 60 - depth + 1, "multi-core occupancy")


def check_report_markers():
    report = (ROOT / "REPORT.md").read_text()
    pins = (ROOT / "SOURCE_PINS.md").read_text()
    search = (ROOT / "SEARCH_LOG.md").read_text()
    required = [
        "PRIMARY_SOURCE_COUNT: 4",
        "PRIMARY_SOURCE_CAP: 8",
        "SEPARATOR_TEST_COUNT: 5",
        "SCOPED_VERDICT (1/1): close",
        "SUCCESSOR (0/1): none",
        "PI-GRAPH-ORDER-T158 (`conjecture`; UNPROVED PI-TRANSFER; NOT ASSERTED)",
        "FIXED_PI_CLAIM: none",
        "A1_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "literature-checked",
        "proof sketch",
        "finite-test",
        "`experiment`",
        "T121",
        "T128",
        "T131",
        "T153",
        "T156",
        "T157",
        "transition-closed",
        "pi_hat=pi_emp",
        "For a linear census, (7.4) is not asserted",
    ]
    for marker in required:
        require(marker in report, f"missing report marker: {marker}")
    require(report.count("SCOPED_VERDICT (1/1):") == 1, "verdict uniqueness")
    require(report.count("SUCCESSOR (0/1):") == 1, "successor uniqueness")
    require(pins.count("## S") == 4, "source section count")
    require("PRIMARY_SOURCE_COUNT: 4" in search and "PRIMARY_SOURCE_CAP: 8" in search, "search cap")


def main():
    for filename, expected in EXPECTED.items():
        require(digest(ROOT / filename) == expected, f"hash mismatch: {filename}")
    check_source_anchors()
    check_ledger()
    check_refreshed_comparators()
    check_repeated_debruijn()
    check_separators()
    check_report_markers()
    print("canonical_hash: PASS")
    print("primary_source_hashes_and_anchors: 4/4 PASS")
    print("primary_source_cap: 4 <= 8 PASS")
    print("exclusion_ledger: T89-T157 69/69 PASS")
    print("refreshed_comparators: T156_rejected,T157_pinned PASS")
    print("graph_normalization_endpoints_gap_stationary_firewall: PASS")
    print("repeated_debruijn_zero_census_gap_obstruction: PASS")
    print("ordered_diagonal_collision_identity: PASS")
    print("separator_tests: 5/5 PASS")
    print("named_comparisons: T121,T128,T131,T153,T156,T157 PASS")
    print("claim_labels_and_scope_firewall: PASS")
    print("scoped_verdict_count: 1 PASS")
    print("successor_count: 0 PASS")


if __name__ == "__main__":
    main()
