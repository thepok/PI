#!/usr/bin/env python3
"""Self-contained finite completeness replay for the T168 proof-sketch note."""

from __future__ import annotations

import hashlib
import itertools
import math
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


Event = tuple[int, int]
Shape = tuple[Event, ...]


def events(n: int) -> tuple[Event, ...]:
    return tuple((a, b) for a in range(n) for b in range(a + 1, n))


def normalize(shape: tuple[Event, ...]) -> Shape:
    least = min(x for event in shape for x in event)
    return tuple(sorted((a - least, b - least) for a, b in shape))


def support(event: Event, m: int) -> set[int]:
    a, b = event
    return set(range(a, a + m)) | set(range(b, b + m))


def graph_connected(vertices: tuple[object, ...], edges: set[tuple[int, int]]) -> bool:
    if not vertices:
        return False
    seen = {0}
    changed = True
    while changed:
        changed = False
        for a, b in edges:
            if a in seen and b not in seen:
                seen.add(b)
                changed = True
            if b in seen and a not in seen:
                seen.add(a)
                changed = True
    return len(seen) == len(vertices)


def dependency_edges(shape: Shape, m: int) -> set[tuple[int, int]]:
    supports = [support(event, m) for event in shape]
    return {(i, j) for i in range(len(shape)) for j in range(i + 1, len(shape))
            if supports[i] & supports[j]}


def is_mixed(shape: Shape) -> bool:
    return len({b - a for a, b in shape}) >= 2


def incidence_type(shape: Shape) -> str:
    vertices = sorted({x for event in shape for x in event})
    adjacency = {x: set() for x in vertices}
    for a, b in shape:
        adjacency[a].add(b)
        adjacency[b].add(a)
    degrees = sorted((len(adjacency[x]) for x in vertices), reverse=True)
    if len(shape) == 2:
        return "P3" if len(vertices) == 3 else "2K2"
    signatures = {
        (1, 1, 1, 1, 1, 1): "3K2",
        (2, 1, 1, 1, 1): "P3+K2",
        (2, 2, 1, 1): "P4",
        (3, 1, 1, 1): "K1,3",
        (2, 2, 2): "K3",
    }
    return signatures[tuple(degrees)]


def dependency_type(shape: Shape, m: int) -> str:
    edge_count = len(dependency_edges(shape, m))
    if len(shape) == 2:
        return "K2" if edge_count == 1 else "DISCONNECTED"
    return {0: "DISCONNECTED", 1: "DISCONNECTED", 2: "P3", 3: "K3"}[edge_count]


ROWS = {
    (2, "2K2", "K2"): "M2-D",
    (2, "P3", "K2"): "M2-W",
    (3, "3K2", "P3"): "M3-M-P",
    (3, "3K2", "K3"): "M3-M-K",
    (3, "P3+K2", "P3"): "M3-WD-P",
    (3, "P3+K2", "K3"): "M3-WD-K",
    (3, "P4", "P3"): "M3-P-P",
    (3, "P4", "K3"): "M3-P-K",
    (3, "K1,3", "K3"): "M3-S",
    (3, "K3", "K3"): "M3-T",
}


def classify(shape: Shape, m: int) -> str | None:
    if not is_mixed(shape):
        return None
    dep = dependency_type(shape, m)
    if dep == "DISCONNECTED":
        return None
    key = (len(shape), incidence_type(shape), dep)
    check(key in ROWS, f"unclassified connected shape: {shape}, m={m}, key={key}")
    return ROWS[key]


def equality_rank(shape: Shape, m: int) -> int:
    equality_edges = {(a + r, b + r) for a, b in shape for r in range(m)}
    vertices = {x for edge in equality_edges for x in edge}
    parent = {x: x for x in vertices}

    def root(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in equality_edges:
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    return len(vertices) - len({root(x) for x in vertices})


def multiplicity(shape: Shape, n: int) -> int:
    return max(0, n - max(x for event in shape for x in event))


def translated(shape: Shape, shift: int) -> Shape:
    return tuple((a + shift, b + shift) for a, b in shape)


def exact_embedding_count(shape: Shape, n: int) -> int:
    count = 0
    for shift in range(n):
        candidate = translated(shape, shift)
        if max(x for event in candidate for x in event) < n:
            check(normalize(candidate) == shape, "translation normalization")
            count += 1
    return count


def exhaustive_shapes() -> tuple[Counter[str], dict[str, tuple[int, int, Shape]]]:
    orbit_occurrences: dict[tuple[int, int, Shape], int] = defaultdict(int)
    row_counts: Counter[str] = Counter()
    witnesses: dict[str, tuple[int, int, Shape]] = {}
    for n in range(2, 8):
        universe = events(n)
        for m in range(1, 4):
            for size in (2, 3):
                for raw in itertools.combinations(universe, size):
                    shape = normalize(raw)
                    row = classify(shape, m)
                    if row is None:
                        continue
                    key = (n, m, shape)
                    orbit_occurrences[key] += 1
                    row_counts[row] += 1
                    witnesses.setdefault(row, (n, m, shape))
                    check(equality_rank(raw, m) == equality_rank(shape, m),
                          "rank translation invariance")
            # Each normalized orbit occurs exactly once for every legal shift.
            for (nn, mm, shape), count in tuple(orbit_occurrences.items()):
                if nn == n and mm == m:
                    check(count == multiplicity(shape, n), "embedding multiplicity")
                    check(count == exact_embedding_count(shape, n), "direct embeddings")
    check(set(witnesses) == set(ROWS.values()), "all table rows need bounded witnesses")
    return row_counts, witnesses


def check_probability_by_binary_enumeration() -> int:
    checks = 0
    sample_shapes = [
        ((0, 1), (0, 2)),
        ((0, 1), (2, 3)),
        ((0, 1), (0, 2), (1, 2)),
        ((0, 1), (1, 2), (2, 3)),
        ((0, 1), (0, 2), (0, 3)),
    ]
    for m in (1, 2):
        for raw in sample_shapes:
            shape = tuple(sorted(raw))
            length = max(x for event in shape for x in event) + m
            active = 0
            for word in itertools.product(range(2), repeat=length):
                if all(word[a:a + m] == word[b:b + m] for a, b in shape):
                    active += 1
            check(Fraction(active, 2**length) == Fraction(1, 2**equality_rank(shape, m)),
                  "binary probability equals alphabet^(-rank)")
            checks += 1
    return checks


def triangle_count_direct(n: int, m: int) -> int:
    return sum(1 for x, y, z in itertools.combinations(range(n), 3)
               if y - x >= m and z - y >= m)


def check_triangle_family() -> int:
    checks = 0
    for n in range(3, 15):
        for m in range(1, 6):
            expected = math.comb(max(0, n - 2 * m + 2), 3)
            check(triangle_count_direct(n, m) == expected, "triangle multiplicity")
            for x, y, z in itertools.combinations(range(n), 3):
                if y - x >= m and z - y >= m:
                    shape = normalize(((x, y), (x, z), (y, z)))
                    check(classify(shape, m) == "M3-T", "triangle row")
                    check(equality_rank(shape, m) == 2 * m, "triangle rank")
            checks += 1
    return checks


def same_lag_chain_intensity(n: int, m: int) -> Fraction:
    """Exact expected maximal-chain count by root indicators."""
    q = Fraction(1, 10)
    # Each lag row has one boundary root and n-d-1 possible interior roots.
    return q**m * ((n - 1) + (1 - q) * Fraction((n - 1) * (n - 2), 2))


def check_uniform_comparison() -> int:
    checks = 0
    for n in (10_000, 20_000, 100_000, 1_000_000, 10_000_000):
        allowed_m = [m for m in range(1, 20) if 10 ** (4 * m) <= n]
        for m in allowed_m:
            triangle = Fraction(math.comb(n - 2 * m + 2, 3), 10 ** (2 * m))
            same = same_lag_chain_intensity(n, m)
            check(same <= Fraction(math.comb(n, 2), 10**m), "same-lag upper bound")
            # Fourth powers avoid floating-point use in N^(3/4).
            check((96 * triangle) ** 4 >= n**3 * same**4,
                  "uniform N^(3/4)/96 comparison")
            checks += 1
    return checks


def check_package() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    check(digest("canonical_statement.txt") == CANONICAL_SHA, "canonical hash")
    check(report.count("SCOPED_ENDPOINT (1/1):") == 1, "one scoped endpoint")
    check("PATTERN_TABLE_ROWS: 10" in report, "table row declaration")
    check("unproved pi-transfer" in report, "pi premise label")
    for forbidden in ("FIXED_PI_CLAIM: yes", "A1_CLAIM: yes", "C1_CLAIM: yes", "C2_CLAIM: yes"):
        check(forbidden not in report, "claim firewall")


def main() -> None:
    check_package()
    row_counts, witnesses = exhaustive_shapes()
    probability_checks = check_probability_by_binary_enumeration()
    triangle_checks = check_triangle_family()
    comparison_checks = check_uniform_comparison()
    print("T168 finite completeness replay: PASS")
    print(f"canonical_sha256: {digest('canonical_statement.txt')}")
    print(f"pattern_rows_reached: {len(witnesses)}/10")
    print("row_witnesses:")
    for row in sorted(witnesses):
        n, m, shape = witnesses[row]
        print(f"  {row}: N={n},m={m},F={shape}")
    print(f"classified_bounded_embeddings: {sum(row_counts.values())}")
    print(f"rank_probability_binary_checks: {probability_checks}")
    print(f"triangle_exact_count_and_rank_checks: {triangle_checks}")
    print(f"uniform_comparison_grid_checks: {comparison_checks}")
    print("same_lag_cases_excluded: PASS")
    print("scoped_endpoint_count: 1 (counterfamily)")
    print("pi_transfer: explicitly unproved")
    print("claim_firewall: no fixed-pi/A1/C1/C2 claim")


if __name__ == "__main__":
    main()
