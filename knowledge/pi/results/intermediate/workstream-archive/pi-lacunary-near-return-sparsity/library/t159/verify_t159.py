#!/usr/bin/env python3
"""Self-contained exact-arithmetic and package replay for T159."""

from __future__ import annotations

import hashlib
import itertools
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_PDF = "3640caf66dd78cc1fa3e4ad69cd5b250123c9896e86c17962912cc3fbc82f87e"
SOURCE_TXT = "8a89a301fda4c86bf2383025840e07d7c0a44466f3466a8d0f37e73c1290381a"


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def pairs(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def support(alpha: tuple[int, int], m: int) -> set[int]:
    i, j = alpha
    return set(range(i, i + m)) | set(range(j, j + m))


def edges(alpha: tuple[int, int], m: int) -> set[tuple[int, int]]:
    i, j = alpha
    return {tuple(sorted((i + r, j + r))) for r in range(m)}


def equality_rank(event_pairs: tuple[tuple[int, int], ...], m: int) -> int:
    edge_set: set[tuple[int, int]] = set()
    for alpha in event_pairs:
        edge_set |= edges(alpha, m)
    vertices = {v for edge in edge_set for v in edge}
    parent = {v: v for v in vertices}

    def root(v: int) -> int:
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for a, b in edge_set:
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    components = len({root(v) for v in vertices})
    return len(vertices) - components


def blocks(word: tuple[int, ...], n: int, m: int) -> list[tuple[int, ...]]:
    check(len(word) == n + m - 1, "word endpoint mismatch")
    return [word[i : i + m] for i in range(n)]


def ordered_energy(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(a == b for a in ws for b in ws)


def z_count(word: tuple[int, ...], n: int, m: int) -> int:
    ws = blocks(word, n, m)
    return sum(ws[i] == ws[j] for i, j in pairs(n))


def debruijn(alphabet_size: int, order: int) -> tuple[int, ...]:
    """Return a cyclic de Bruijn sequence B(alphabet_size, order)."""
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


def hset(t: int, n: int, m: int) -> set[int]:
    return {s for s in range(n) if abs(s - t) <= m - 1}


def neighborhood(alpha: tuple[int, int], n: int, m: int) -> set[tuple[int, int]]:
    u = hset(alpha[0], n, m) | hset(alpha[1], n, m)
    return {beta for beta in pairs(n) if set(beta) & u}


def cx_bound(n: int, m: int) -> Fraction:
    p = Fraction(1, 10**m)
    pcount = math.comb(n, 2)
    lam = pcount * p
    rstar = min(n, 4 * m - 2)
    dstar = rstar * (2 * n - rstar - 1) // 2
    return (Fraction(5, 1) / lam + 3) * pcount * (
        Fraction(dstar - 1, 10) * p + dstar * p * p
    )


def delta_parallel(n: int, m: int) -> Fraction:
    p = Fraction(1, 10**m)
    total = Fraction(0)
    for h in range(1, min(m - 1, n - 2) + 1):
        total += 2 * math.comb(n - h, 2) * (p * Fraction(1, 10**h) - p * p)
    return total


def test_process_identities() -> None:
    for n in range(2, 10):
        for m in range(1, 6):
            check(n + m - 2 == (n + m - 1) - 1, "last endpoint failed")
            for alpha in pairs(n):
                i, j = alpha
                d = j - i
                check(len(support(alpha, m)) == m + min(m, d), "support size failed")
                check(equality_rank((alpha,), m) == m, "single-event rank failed")
                hood = neighborhood(alpha, n, m)
                u = hset(i, n, m) | hset(j, n, m)
                expected = math.comb(n, 2) - math.comb(n - len(u), 2)
                check(len(hood) == expected, "neighborhood formula failed")
                rstar = min(n, 4 * m - 2)
                dstar = rstar * (2 * n - rstar - 1) // 2
                check(len(hood) <= dstar, "neighborhood upper bound failed")
                for beta in pairs(n):
                    if beta not in hood:
                        check(support(alpha, m).isdisjoint(support(beta, m)),
                              "outside supports intersect")
                    if beta != alpha:
                        check(equality_rank((alpha, beta), m) >= m + 1,
                              "distinct-event rank bound failed")
            for d in range(1, n):
                for h in range(1, n - d):
                    alpha = (0, d)
                    beta = (h, h + d)
                    expected_rank = m + min(m, h)
                    check(equality_rank((alpha, beta), m) == expected_rank,
                          "same-lag translate rank failed")


def test_ordered_reconstruction() -> None:
    for n, m in ((4, 2), (5, 3)):
        for word in itertools.product(range(3), repeat=n + m - 1):
            check(ordered_energy(word, n, m) == n + 2 * z_count(word, n, m),
                  "ordered reconstruction failed")


def test_separator_families() -> tuple[Fraction, Fraction]:
    # 1. Constant.
    n, m = 8, 3
    constant = (0,) * (n + m - 1)
    check(ordered_energy(constant, n, m) == n * n, "constant test failed")

    # 2. Primitive period 3, m >= 3, N divisible by 3.
    n, m, seed = 12, 4, (0, 1, 2)
    periodic = tuple(seed[i % 3] for i in range(n + m - 1))
    check(ordered_energy(periodic, n, m) == n * n // 3, "periodic test failed")

    # 3. Decimal de Bruijn cycle of order 2, repeated twice.
    cycle = debruijn(10, 2)
    check(len(cycle) == 100, "decimal de Bruijn cycle length failed")
    cyclic_blocks = {
        tuple(cycle[(i + offset) % len(cycle)] for offset in range(2))
        for i in range(len(cycle))
    }
    check(len(cyclic_blocks) == 100, "decimal de Bruijn coverage failed")
    n, m = 200, 2
    debruijn_word = tuple(cycle[i % len(cycle)] for i in range(n + m - 1))
    check(ordered_energy(debruijn_word, n, m) == n * n // 10**m,
          "repeated de Bruijn test failed")

    # 4. Shared prefix lower bound.
    n, m, r = 20, 4, 7
    shared = (0,) * (r + m - 1) + tuple((i % 9) + 1 for i in range(n - r))
    check(len(shared) == n + m - 1, "shared-prefix endpoint failed")
    check(ordered_energy(shared, n, m) >= r * r, "shared-prefix test failed")

    # 5a. Exact enumeration under C={W_0=W_1}, N=5,m=2, binary alphabet.
    # The rank formula is q-independent, so replace 10 by q=2 for enumeration.
    n, m, q = 5, 2, 2
    alpha = (0, 1)
    conditioned = []
    for word in itertools.product(range(q), repeat=n + m - 1):
        ws = blocks(word, n, m)
        if ws[0] == ws[1]:
            conditioned.append(z_count(word, n, m))
    enum_mean = Fraction(sum(conditioned), len(conditioned))
    rank_mean = sum(
        (Fraction(1, q) ** (equality_rank((alpha, beta), m) - m) for beta in pairs(n)),
        Fraction(0),
    )
    check(enum_mean == rank_mean, "conditioned enumeration/rank mismatch")

    # 5b. Decimal rank formula at the report's N=8,m=3 instance.
    n, m, q = 8, 3, 10
    alpha = (0, 1)
    decimal_mean = sum(
        (Fraction(1, q) ** (equality_rank((alpha, beta), m) - m) for beta in pairs(n)),
        Fraction(0),
    )
    check(decimal_mean >= 1, "conditioned long repeat not retained")
    return enum_mean, decimal_mean


def test_error_and_scale() -> tuple[Fraction, Fraction]:
    n, m = 10**4, 1
    check(m <= math.floor(math.log10(n) / 4), "mandated scale endpoint failed")
    bound = cx_bound(n, m)
    check(bound > 1, "coarse Chen-Xia bound unexpectedly informative")

    # Exact finite cluster ratio approaching the displayed 2/9 benchmark.
    n, m = 10**5, 5
    p = Fraction(1, 10**m)
    lam = math.comb(n, 2) * p
    ratio = delta_parallel(n, m) / lam
    limiting_m = 2 * sum((Fraction(1, 10**h) - p for h in range(1, m)), Fraction(0))
    check(abs(float(ratio - limiting_m)) < 0.0001, "cluster finite-N limit failed")
    check(Fraction(1, 5) < ratio < Fraction(1, 4), "cluster/mean scale failed")
    return bound, ratio


def test_package_markers() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    pins = (ROOT / "SOURCE_PINS.md").read_text(encoding="utf-8")
    comparators = (ROOT / "COMPARATORS.md").read_text(encoding="utf-8")
    source = (ROOT / "chen-xia-math0410169.txt").read_text(encoding="utf-8", errors="replace")

    check(digest("canonical_statement.txt") == CANONICAL, "canonical hash mismatch")
    check(digest("chen-xia-math0410169.pdf") == SOURCE_PDF, "source PDF hash mismatch")
    check(digest("chen-xia-math0410169.txt") == SOURCE_TXT, "source text hash mismatch")
    for anchor in ("Theorem 4.1.", "Remark 4.2.", "Remark 4.3."):
        check(anchor in source, f"source anchor missing: {anchor}")
    check("PRIMARY_SOURCE_COUNT: 1" in report and "PRIMARY_SOURCE_CAP: 6" in report,
          "source cap markers missing")
    check("PRIMARY_SOURCE_COUNT: 1" in pins and "PRIMARY_SOURCE_CAP: 6" in pins,
          "pin source cap markers missing")
    check(report.count("SCOPED_VERDICT (1/1):") == 1, "verdict count wrong")
    check(report.count("SUCCESSOR (0/1):") == 1, "successor count wrong")
    check("SUCCESSOR (0/1): **none**" in report, "successor endpoint wrong")
    for label in ("`literature-checked`", "`proof sketch`", "`finite-test`",
                  "`unproved pi-transfer`"):
        check(label in report, f"claim label missing: {label}")
    for item in range(150, 159):
        if item in (151, 153):
            continue
        check(f"T{item}" in comparators and f"T{item}" in report,
              f"comparator missing: T{item}")
    for firewall in ("FIXED_PI_CLAIM: none", "A1_CLAIM: none", "C1_CLAIM: none",
                     "C2_CLAIM: none"):
        check(firewall in report, f"claim firewall missing: {firewall}")


def main() -> None:
    test_package_markers()
    test_process_identities()
    test_ordered_reconstruction()
    enum_mean, decimal_mean = test_separator_families()
    bound, ratio = test_error_and_scale()
    print("T159 finite-test replay: PASS")
    print("canonical_sha256:", digest("canonical_statement.txt"))
    print("primary_source_count: 1 (cap 6)")
    print("process_endpoint_support_neighborhood_checks: PASS")
    print("ordered_reconstruction_checks: PASS")
    print("separator_tests: 5/5 PASS")
    print("conditioned_binary_mean_N5_m2:", enum_mean)
    print("conditioned_decimal_mean_N8_m3:", decimal_mean)
    print("CX_bound_N10000_m1_gt_1:", bound > 1)
    print("parallel_cluster_ratio_N100000_m5:", f"{float(ratio):.12f}")
    print("comparison_range: T150,T152,T154-T158")
    print("scoped_verdict_count: 1")
    print("successor_count: 0")
    print("claim_firewall: no fixed-pi/A1/C1/C2 claim")
    print("labels: literature-checked, proof sketch, finite-test, unproved pi-transfer")


if __name__ == "__main__":
    main()
