#!/usr/bin/env python3
"""Finite falsification and replay checks for the T170 proof-sketch note."""

from __future__ import annotations

import hashlib
import itertools
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
Event = tuple[int, int]
Shape = tuple[Event, ...]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(name: str) -> str:
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()


def events(n: int) -> tuple[Event, ...]:
    return tuple((a, b) for a in range(n) for b in range(a + 1, n))


def normalize(shape: tuple[Event, ...]) -> Shape:
    least = min(x for event in shape for x in event)
    return tuple(sorted((a - least, b - least) for a, b in shape))


def equality_rank(shape: tuple[Event, ...], m: int) -> int:
    edges = {(a + r, b + r) for a, b in shape for r in range(m)}
    vertices = {x for edge in edges for x in edge}
    parent = {x: x for x in vertices}

    def root(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    return len(vertices) - len({root(x) for x in vertices})


def block(word: tuple[int, ...], i: int, m: int) -> tuple[int, ...]:
    return word[i:i + m]


def collision_count(word: tuple[int, ...], n: int, m: int) -> int:
    return sum(block(word, a, m) == block(word, b, m) for a, b in events(n))


def third_cumulant(values: list[int]) -> Fraction:
    count = len(values)
    mean = Fraction(sum(values), count)
    return sum((Fraction(value) - mean) ** 3 for value in values) / count


def expansion(n: int, m: int, alphabet: int = 10) -> Fraction:
    es = events(n)
    p = Fraction(1, alphabet**m)
    result = len(es) * p * (1 - p) * (1 - 2 * p)
    for e, f in itertools.combinations(es, 2):
        joint = Fraction(1, alphabet ** equality_rank((e, f), m))
        result += 6 * (1 - 2 * p) * (joint - p * p)
    for e, f, g in itertools.combinations(es, 3):
        triple = Fraction(1, alphabet ** equality_rank((e, f, g), m))
        pairs = sum(
            (Fraction(1, alphabet ** equality_rank(pair, m))
             for pair in ((e, f), (e, g), (f, g))),
            Fraction(0),
        )
        result += 6 * (triple - p * pairs + 2 * p**3)
    return result


def incidence_type(shape: Shape) -> str:
    vertices = sorted({x for event in shape for x in event})
    adjacency = {x: set() for x in vertices}
    for a, b in shape:
        adjacency[a].add(b)
        adjacency[b].add(a)
    degrees = tuple(sorted((len(adjacency[x]) for x in vertices), reverse=True))
    if len(shape) == 2:
        return "P3" if len(vertices) == 3 else "2K2"
    names = {
        (1, 1, 1, 1, 1, 1): "3K2",
        (2, 1, 1, 1, 1): "P3+K2",
        (2, 2, 1, 1): "P4",
        (3, 1, 1, 1): "K1,3",
        (2, 2, 2): "K3",
    }
    return names[degrees]


def signature(shape: Shape, m: int) -> tuple[object, ...]:
    f = normalize(shape)
    endpoints = sorted({x for event in f for x in event})
    overlaps = tuple(
        max(0, m - abs(a - b)) for a, b in itertools.combinations(endpoints, 2)
    )
    lags = tuple(b - a for a, b in f)
    pair_ranks = tuple(
        equality_rank(pair, m) for pair in itertools.combinations(f, 2)
    )
    triple_rank = equality_rank(f, m) if len(f) == 3 else None
    return (
        len(f), f, max(endpoints), incidence_type(f), overlaps,
        lags, tuple(sorted(Counter(lags).values())), pair_ranks, triple_rank,
    )


def translated(shape: Shape, shift: int) -> Shape:
    return tuple((a + shift, b + shift) for a, b in shape)


def check_rank_probabilities() -> int:
    checks = 0
    samples: tuple[Shape, ...] = (
        ((0, 1),),
        ((0, 2),),
        ((0, 1), (1, 2)),
        ((0, 1), (2, 3)),
        ((0, 1), (0, 2), (1, 2)),
    )
    for m in (1, 2):
        for shape in samples:
            length = max(x for event in shape for x in event) + m
            if length > 5:
                continue
            active = 0
            for word in itertools.product(range(10), repeat=length):
                if all(block(word, a, m) == block(word, b, m) for a, b in shape):
                    active += 1
            probability = Fraction(active, 10**length)
            check(probability == Fraction(1, 10 ** equality_rank(shape, m)),
                  "rank probability mismatch")
            checks += 1
    return checks


def check_full_cumulants() -> int:
    checks = 0
    for n, m in ((2, 1), (3, 1), (4, 1), (2, 2), (3, 2)):
        length = n + m - 1
        values = [collision_count(word, n, m)
                  for word in itertools.product(range(10), repeat=length)]
        check(third_cumulant(values) == expansion(n, m),
              f"full cumulant mismatch N={n},m={m}")
        checks += 1
    return checks


def check_partition_and_signs() -> tuple[int, int, set[str]]:
    embedding_checks = 0
    sign_checks = 0
    incidence_types: set[str] = set()
    for n in range(3, 9):
        es = events(n)
        for m in range(1, 5):
            for size in (2, 3):
                orbits: Counter[tuple[object, ...]] = Counter()
                representatives: dict[tuple[object, ...], Shape] = {}
                for raw in itertools.combinations(es, size):
                    key = signature(raw, m)
                    orbits[key] += 1
                    representatives.setdefault(key, normalize(raw))
                    incidence_types.add(incidence_type(normalize(raw)))
                    check(signature(normalize(raw), m) == key,
                          "signature translation invariance")
                    if size == 2:
                        d = 2 * m - equality_rank(raw, m)
                        check(d >= 0, "negative pair deficiency")
                    else:
                        pair_ds = tuple(
                            2 * m - equality_rank(pair, m)
                            for pair in itertools.combinations(raw, 2)
                        )
                        d_triple = 3 * m - equality_rank(raw, m)
                        bracket = 10**d_triple - sum(10**d for d in pair_ds) + 2
                        check(bracket >= 0, "negative distinct cumulant bracket")
                        expected_zero = (
                            (d_triple == 0 and pair_ds == (0, 0, 0))
                            or (d_triple > 0 and sorted(pair_ds) == [0, 0, d_triple])
                        )
                        check((bracket == 0) == expected_zero,
                              "zero-class characterization")
                        sign_checks += 1
                for key, count in orbits.items():
                    shape = representatives[key]
                    span = max(x for event in shape for x in event)
                    expected = max(0, n - span)
                    direct = sum(
                        max(x for event in translated(shape, t) for x in event) < n
                        for t in range(n)
                    )
                    check(count == expected == direct, "shape embedding multiplicity")
                    embedding_checks += 1
    return embedding_checks, sign_checks, incidence_types


def check_same_lag_pairs() -> int:
    checks = 0
    for m in range(1, 7):
        for d in range(1, 8):
            for h in range(-7, 8):
                if h == 0:
                    continue
                base = max(0, -h)
                pair = ((base, base + d), (base + h, base + h + d))
                expected_rank = m + min(m, abs(h))
                check(equality_rank(pair, m) == expected_rank, "same-lag pair rank")
                checks += 1
    return checks


def check_same_lag_triples() -> int:
    checks = 0
    for m in range(1, 7):
        for d in range(1, 8):
            for starts in itertools.combinations(range(8), 3):
                shape = tuple((start, start + d) for start in starts)
                edge_starts = set().union(
                    *(set(range(start, start + m)) for start in starts)
                )
                check(equality_rank(shape, m) == len(edge_starts),
                      "same-lag triple forest rank")
                pair_overlaps = sum(
                    max(0, m - abs(a - b))
                    for a, b in itertools.combinations(starts, 2)
                )
                triple_overlap = max(0, m - (max(starts) - min(starts)))
                deficiency = 3 * m - equality_rank(shape, m)
                check(deficiency == pair_overlaps - triple_overlap,
                      "same-lag triple deficiency")
                checks += 1
    return checks


def support(event: Event, m: int) -> set[int]:
    a, b = event
    return set(range(a, a + m)) | set(range(b, b + m))


def check_named_cancellations() -> int:
    checks = 0
    for n in range(4, 9):
        for m in range(1, 5):
            for shape in itertools.combinations(events(n), 3):
                pair_ds = tuple(
                    2 * m - equality_rank(pair, m)
                    for pair in itertools.combinations(shape, 2)
                )
                d_triple = 3 * m - equality_rank(shape, m)
                bracket = 10**d_triple - sum(10**d for d in pair_ds) + 2
                if equality_rank(shape, m) == 3 * m:
                    check(bracket == 0, "forest cancellation")
                    checks += 1
                for isolated in range(3):
                    rest = [index for index in range(3) if index != isolated]
                    isolated_support = support(shape[isolated], m)
                    joint_support = support(shape[rest[0]], m) | support(shape[rest[1]], m)
                    if isolated_support.isdisjoint(joint_support):
                        check(bracket == 0, "disjoint-support cancellation")
                        checks += 1
    return checks


def triangle_count(n: int, m: int) -> int:
    return sum(1 for x, y, z in itertools.combinations(range(n), 3)
               if y - x >= m and z - y >= m)


def check_triangles() -> int:
    checks = 0
    for n in range(3, 18):
        for m in range(1, 7):
            expected = math.comb(max(0, n - 2 * m + 2), 3)
            check(triangle_count(n, m) == expected, "triangle count")
            for x, y, z in itertools.combinations(range(n), 3):
                if y - x >= m and z - y >= m:
                    shape = ((x, y), (x, z), (y, z))
                    check(equality_rank(shape, m) == 2 * m, "triangle triple rank")
                    for pair in itertools.combinations(shape, 2):
                        check(equality_rank(pair, m) == 2 * m, "triangle pair rank")
            checks += 1
    return checks


def check_uniform_bound() -> int:
    checks = 0
    for n in (10_000, 100_000, 1_000_000, 10_000_000, 100_000_000):
        for m in range(1, 20):
            if 10 ** (4 * m) > n:
                continue
            p = Fraction(1, 10**m)
            triangle = 6 * math.comb(n - 2 * m + 2, 3) * p**2 * (1 - p)
            lower = Fraction(9, 320) * n**3 * p**2
            check(triangle >= lower, "explicit triangle lower bound")
            # Square after cancelling the positive factor 9/320; no roots or
            # floating-point arithmetic are needed.
            check((n**3 * p**2) ** 2 >= n**5, "depth substitution")
            checks += 1
    return checks


def check_package() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    check(digest("canonical_statement.txt") == CANONICAL_SHA, "canonical hash")
    check(report.count("SCOPED_ENDPOINT (1/1):") == 1, "single endpoint")
    check("CUMULANT_REPETITION_STRATA: 3" in report, "repetition strata marker")
    check("DISTINCT_INCIDENCE_TYPES: 5" in report, "incidence marker")
    check("unproved pi-transfer" in report, "pi transfer label")
    for forbidden in (
        "FIXED_PI_CLAIM: yes", "A1_CLAIM: yes",
        "C1_CLAIM: yes", "C2_CLAIM: yes",
    ):
        check(forbidden not in report, "claim firewall")


def main() -> None:
    check_package()
    probability_checks = check_rank_probabilities()
    cumulant_checks = check_full_cumulants()
    embedding_checks, sign_checks, incidence_types = check_partition_and_signs()
    same_lag_checks = check_same_lag_pairs()
    same_lag_triple_checks = check_same_lag_triples()
    cancellation_checks = check_named_cancellations()
    triangle_checks = check_triangles()
    uniform_checks = check_uniform_bound()
    check(incidence_types == {"2K2", "P3", "3K2", "P3+K2", "P4", "K1,3", "K3"},
          "all incidence types reached")
    print("T170 finite cumulant replay: PASS")
    print(f"canonical_sha256: {digest('canonical_statement.txt')}")
    print(f"rank_probability_base10_checks: {probability_checks}")
    print(f"full_distribution_cumulant_checks: {cumulant_checks}")
    print(f"signature_embedding_checks: {embedding_checks}")
    print(f"distinct_rank_signature_sign_checks: {sign_checks}")
    print(f"incidence_types_reached: {','.join(sorted(incidence_types))}")
    print(f"same_lag_pair_rank_checks: {same_lag_checks}")
    print(f"same_lag_triple_rank_checks: {same_lag_triple_checks}")
    print(f"named_forest_and_disconnected_checks: {cancellation_checks}")
    print(f"triangle_count_and_rank_checks: {triangle_checks}")
    print(f"uniform_bound_grid_checks: {uniform_checks}")
    print("forest_and_disconnected_zero_classes: PASS")
    print("ordered_diagonal_conversion: kappa3(N+2U)=8*kappa3(U)")
    print("finite_computation_label: experiment only")
    print("pi_transfer: explicitly unproved")
    print("claim_firewall: no fixed-pi/A1/C1/C2 claim")


if __name__ == "__main__":
    main()
