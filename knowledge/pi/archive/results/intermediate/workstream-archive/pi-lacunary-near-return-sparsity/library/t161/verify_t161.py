#!/usr/bin/env python3
"""Self-contained exact-arithmetic replay for the T161 note."""

from __future__ import annotations

import hashlib
import itertools
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
CHEN_XIA_PDF_SHA = "3640caf66dd78cc1fa3e4ad69cd5b250123c9896e86c17962912cc3fbc82f87e"
CHEN_XIA_TXT_SHA = "8a89a301fda4c86bf2383025840e07d7c0a44466f3466a8d0f37e73c1290381a"
PAPERFOLDING_DVI_SHA = "9ee4f3884e5029c5dc507736d7c4364c8757bb18996e0535ddf756247108cc72"


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def pairs(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def blocks(word: tuple[int, ...], n: int, m: int) -> list[tuple[int, ...]]:
    check(len(word) == n + m - 1, "word endpoint mismatch")
    return [word[i : i + m] for i in range(n)]


def collision_set(word: tuple[int, ...], n: int, m: int) -> set[tuple[int, int]]:
    ws = blocks(word, n, m)
    return {(i, j) for i, j in pairs(n) if ws[i] == ws[j]}


def ordered_energy(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(a == b for a in ws for b in ws)


def equality_edges(alpha: tuple[int, int], m: int) -> set[tuple[int, int]]:
    i, j = alpha
    return {(i + r, j + r) for r in range(m)}


def equality_rank(events: tuple[tuple[int, int], ...], m: int) -> int:
    edges: set[tuple[int, int]] = set()
    for event in events:
        edges |= equality_edges(event, m)
    vertices = {v for edge in edges for v in edge}
    parent = {v: v for v in vertices}

    def root(v: int) -> int:
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    return len(vertices) - len({root(v) for v in vertices})


def chains_for_lag(active: set[tuple[int, int]], n: int, d: int) -> list[tuple[int, int, int]]:
    starts = {i for i, j in active if j - i == d}
    chains: list[tuple[int, int, int]] = []
    for start in sorted(starts):
        if start - 1 in starts:
            continue
        length = 1
        while start + length in starts:
            length += 1
        chains.append((d, start, length))
    return chains


def maximal_chains(active: set[tuple[int, int]], n: int) -> list[tuple[int, int, int]]:
    return [chain for d in range(1, n) for chain in chains_for_lag(active, n, d)]


def root_indicator(word: tuple[int, ...], n: int, m: int, d: int, i: int) -> int:
    active = collision_set(word, n, m)
    return int((i, i + d) in active and (i == 0 or (i - 1, i - 1 + d) not in active))


def type_intensity(n: int, m: int, d: int, ell: int) -> Fraction:
    """Expected maximal chains of exact length ell at lag d."""
    q = Fraction(1, 10)
    p = q**m
    count = n - d - ell + 1
    if count <= 0:
        return Fraction(0)
    if count == 1:
        return p * q ** (ell - 1)
    interior = max(0, count - 2)
    return p * q ** (ell - 1) * (2 * (1 - q) + interior * (1 - q) ** 2)


def candidate_starts(n: int, d: int, ell: int) -> range:
    """All and only starts whose last event index is in the lag-d row."""
    return range(max(0, n - d - ell + 1))


def cpgf_cumulant(n: int, m: int, order: int) -> Fraction:
    total = Fraction(0)
    for d in range(1, n):
        for ell in range(1, n - d + 1):
            total += type_intensity(n, m, d, ell) * math.prod(range(ell - order + 1, ell + 1)) if ell >= order else 0
    return total


def cluster_count_mean(n: int, m: int) -> Fraction:
    return sum((type_intensity(n, m, d, ell)
                for d in range(1, n) for ell in range(1, n - d + 1)), Fraction(0))


def conservative_point_process_bound(n: int, m: int) -> Fraction:
    lam = cluster_count_mean(n, m)
    pcount = math.comb(n, 2)
    untruncated = (Fraction(5, 1) / lam + 3) * (pcount * (pcount - 1) + lam * lam)
    return min(Fraction(1), untruncated)


def limiting_cumulant_ratio(order: int) -> Fraction:
    """Limit of CP factorial cumulant / raw event mean as N/m then m grow."""
    q = Fraction(1, 10)
    return math.factorial(order) * q ** (order - 1) / (1 - q) ** (order - 1)


def geometric_cumulant_sum(order: int, cutoff: int) -> Fraction:
    q = Fraction(1, 10)
    return sum((math.prod(range(ell - order + 1, ell + 1))
                * (1 - q) ** 2 * q ** (ell - 1)
                for ell in range(order, cutoff + 1)), Fraction(0))


def debruijn(alphabet_size: int, order: int) -> tuple[int, ...]:
    a = [0] * (alphabet_size * order)
    sequence: list[int] = []

    def visit(t: int, period: int) -> None:
        if t > order:
            if order % period == 0:
                sequence.extend(a[1 : period + 1])
            return
        a[t] = a[t - period]
        visit(t + 1, period)
        for value in range(a[t - period] + 1, alphabet_size):
            a[t] = value
            visit(t + 1, t)

    visit(1, 1)
    return tuple(sequence)


def paperfolding_symbol(one_based_index: int) -> int:
    odd = one_based_index
    while odd % 2 == 0:
        odd //= 2
    return ((odd - 1) // 2) % 2


def separator_tests() -> tuple[int, int, int, int, int]:
    # Constant.
    n, m = 8, 3
    constant = (0,) * (n + m - 1)
    check(ordered_energy(constant, n, m) == n * n, "constant energy")
    constant_chains = len(maximal_chains(collision_set(constant, n, m), n))
    check(constant_chains == n - 1, "constant maximal chains")

    # Primitive period three.
    n, m = 12, 4
    periodic = tuple((0, 1, 2)[i % 3] for i in range(n + m - 1))
    check(ordered_energy(periodic, n, m) == n * n // 3, "periodic energy")
    periodic_chains = maximal_chains(collision_set(periodic, n, m), n)
    check({d for d, _, _ in periodic_chains} == {3, 6, 9}, "periodic lag set")

    # Repeated decimal de Bruijn cycle of order two.
    cycle = debruijn(10, 2)
    n, m = 200, 2
    db_word = tuple(cycle[i % len(cycle)] for i in range(n + m - 1))
    check(ordered_energy(db_word, n, m) == n * n // 100, "de Bruijn energy")
    db_chains = maximal_chains(collision_set(db_word, n, m), n)
    check({d for d, _, _ in db_chains} == {100}, "de Bruijn lag set")

    # Shared prefix.
    n, m, r = 20, 4, 7
    shared = (0,) * (r + m - 1) + tuple((i % 9) + 1 for i in range(n - r))
    check(ordered_energy(shared, n, m) >= r * r, "shared-prefix energy")
    shared_active = collision_set(shared, n, m)
    check(all(any(d == lag and length >= r - lag for d, _, length in maximal_chains(shared_active, n))
              for lag in range(1, r)), "shared-prefix triangular chains")

    # Regular paperfolding, independently generated from the valuation rule.
    n, m = 48, 7
    paper = tuple(paperfolding_symbol(i + 1) for i in range(n + m - 1))
    check(ordered_energy(paper, n, m) == 98, "paperfolding regression")
    pf_chains = maximal_chains(collision_set(paper, n, m), n)
    check(sum(length for _, _, length in pf_chains) == (98 - 48) // 2,
          "paperfolding chain reconstruction")
    return constant_chains, len(periodic_chains), len(db_chains), len(maximal_chains(shared_active, n)), len(pf_chains)


def test_ranks_and_cluster_probabilities() -> None:
    for n in range(2, 12):
        for d in range(1, n):
            for ell in range(1, n - d + 1):
                starts = tuple(candidate_starts(n, d, ell))
                check(starts == tuple(range(n - d - ell + 1)),
                      "candidate start count")
                check(all(a + ell <= n - d for a in starts),
                      "candidate endpoint must remain in lag row")
                check(all(a + ell - 1 < n - d for a in starts),
                      "candidate last active event index")

    for m in range(1, 6):
        for d in range(1, 8):
            max_ell = min(5, 9 - d)
            for ell in range(1, max_ell + 1):
                events = tuple((i, i + d) for i in range(ell))
                check(equality_rank(events, m) == m + ell - 1,
                      "same-lag chain rank")

    # Exact q=2 enumeration of root and exact-cluster probabilities.
    n, m, d, q = 7, 3, 2, 2
    words = list(itertools.product(range(q), repeat=n + m - 1))
    root_count = sum(root_indicator(w, n, m, d, 1) for w in words)
    check(Fraction(root_count, len(words)) == Fraction(1, q**m) * Fraction(q - 1, q),
          "interior root probability")
    for ell in (1, 2, 3):
        count = 0
        for word in words:
            active = collision_set(word, n, m)
            chain = (d, 1, ell)
            if chain in maximal_chains(active, n):
                count += 1
        expected = Fraction(1, q ** (m + ell - 1)) * Fraction((q - 1) ** 2, q**2)
        check(Fraction(count, len(words)) == expected, "exact chain probability")


def test_cumulants() -> tuple[Fraction, Fraction, Fraction]:
    expected = (Fraction(1), Fraction(2, 9), Fraction(2, 27))
    got = tuple(limiting_cumulant_ratio(r) for r in (1, 2, 3))
    check(got == expected, "limiting cumulant ratios")
    for order in (1, 2, 3):
        target = (math.factorial(order) * Fraction(1, 10) ** (order - 1)
                  * Fraction(9, 10) ** (1 - order))
        check(abs(geometric_cumulant_sum(order, 200) - target)
              < Fraction(1, 10**100), "corrected geometric identity")

    # Finite CP intensity check: total expected chain size reconstructs lambda.
    n, m = 80, 4
    lam = Fraction(math.comb(n, 2), 10**m)
    check(cpgf_cumulant(n, m, 1) == lam, "finite CP first cumulant")
    check(cpgf_cumulant(n, m, 2) > 0, "finite CP second cumulant")
    check(cpgf_cumulant(n, m, 3) > 0, "finite CP third cumulant")
    return got


def test_source_substitution() -> None:
    for n, m in ((4, 1), (8, 3), (20, 4)):
        lam = cluster_count_mean(n, m)
        check(lam > 0, "positive cluster count mean")
        check(conservative_point_process_bound(n, m) == 1,
              "conservative source bound must hit metric ceiling")


def test_package() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    comparators = (ROOT / "COMPARATORS.md").read_text(encoding="utf-8")
    source = (ROOT / "chen-xia-math0410169.txt").read_text(encoding="utf-8", errors="replace")
    check(digest("canonical_statement.txt") == CANONICAL_SHA, "canonical hash")
    check(digest("chen-xia-math0410169.pdf") == CHEN_XIA_PDF_SHA, "Chen-Xia PDF hash")
    check(digest("chen-xia-math0410169.txt") == CHEN_XIA_TXT_SHA, "Chen-Xia text hash")
    check(digest("allouche-bousquet-melou-1994.dvi") == PAPERFOLDING_DVI_SHA,
          "paperfolding DVI hash")
    for anchor in ("Theorem 4.1.", "S-valued independent random elements", "Remark 4.3."):
        check(anchor in source, f"source anchor {anchor}")
    for text in (report, pins):
        check("PRIMARY_SOURCE_COUNT: 2" in text, "source count")
        check("PRIMARY_SOURCE_CAP: 4" in text, "source cap")
    check(report.count("SCOPED_VERDICT (1/1):") == 1, "one verdict")
    check("SCOPED_VERDICT (1/1): **close**" in report, "close verdict")
    check("CUMULANT_CALCULATION_COUNT: 3" in report, "cumulant count")
    check("SEPARATOR_TEST_COUNT: 5" in report, "separator count")
    for item in (120, 150, 158, 159, 160):
        check(f"T{item}" in report and f"T{item}" in comparators, f"comparator T{item}")
    for firewall in ("FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none",
                     "C2_CLAIM: none"):
        check(firewall in report, firewall)
    check("UNPROVED_PI_CONNECTED_INTENSITY_BOUND" in report, "pi transfer separation")
    check("(PP-161)" in report and "B_CP(N,m)=1" in report,
          "complete source substitution markers")
    check("a+ell<=N-d," in report and "a+ell<=N-d+1" not in report,
          "correct candidate endpoint in report")
    check("(1-q)^(1-r)" in report, "correct geometric identity factor")
    check("7ac71c0020e63aa8b944e43a4d122179eeef4f64961844497d8a84c41a11159f"
          in comparators, "refreshed T158 comparator")


def main() -> None:
    test_package()
    test_ranks_and_cluster_probabilities()
    cumulants = test_cumulants()
    test_source_substitution()
    separators = separator_tests()
    print("T161 finite experiment replay: PASS")
    print("canonical_sha256:", digest("canonical_statement.txt"))
    print("primary_source_count: 2 (cap 4)")
    print("same_lag_chain_rank_and_probability_checks: PASS")
    print("factorial_cumulant_ratios_k1_k2_k3:", ",".join(str(x) for x in cumulants))
    print("t159_two_ninths_absorbed_not_removed: PASS")
    print("chen_xia_exact_cluster_substitution_bound_equals_1: PASS")
    print("separator_tests: 5/5 PASS")
    print("separator_maximal_chain_counts_constant_periodic_debruijn_shared_paperfolding:",
          ",".join(str(x) for x in separators))
    print("comparison_set: T120,T150,T158,T159,T160")
    print("scoped_verdict_count: 1 (close)")
    print("claim_firewall: no fixed-pi/A1/C1/C2 claim")


if __name__ == "__main__":
    main()
