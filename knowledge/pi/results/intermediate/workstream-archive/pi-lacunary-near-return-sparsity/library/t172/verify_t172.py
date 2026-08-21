#!/usr/bin/env python3
"""Exact bounded checks for T172. Finite output is not a universal proof."""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import factorial
from pathlib import Path


CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"


def event_space(n):
    return tuple(combinations(range(n), 2))


def normalized_shapes(n, size):
    for shape in combinations(event_space(n), size):
        if min(x for event in shape for x in event) == 0:
            yield shape


def equality_rank(events, m):
    edges = {
        (a + offset, b + offset)
        for a, b in set(events)
        for offset in range(m)
    }
    vertices = {x for edge in edges for x in edge}
    parent = {x: x for x in vertices}

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    return len(vertices) - len({root(x) for x in vertices})


def support(event, m):
    a, b = event
    return frozenset(range(a, a + m)) | frozenset(range(b, b + m))


def support_connected(shape, m):
    supports = tuple(support(event, m) for event in shape)
    seen = {0}
    changed = True
    while changed:
        changed = False
        for i in tuple(seen):
            for j in range(len(shape)):
                if j not in seen and supports[i] & supports[j]:
                    seen.add(j)
                    changed = True
    return len(seen) == len(shape)


def graph_components(vertices, edges):
    adjacency = {vertex: set() for vertex in vertices}
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    components = []
    unseen = set(vertices)
    while unseen:
        todo = {min(unseen)}
        component = set()
        while todo:
            vertex = todo.pop()
            if vertex in component:
                continue
            component.add(vertex)
            todo |= adjacency[vertex] - component
        unseen -= component
        components.append(frozenset(component))
    return tuple(sorted(components, key=lambda component: (len(component), tuple(component))))


def clique_closure(events):
    vertices = {x for event in events for x in event}
    return tuple(
        sorted(
            edge
            for component in graph_components(vertices, set(events))
            for edge in combinations(sorted(component), 2)
        )
    )


def dependency_edges(shape, m):
    supports = tuple(support(event, m) for event in shape)
    return tuple(
        (i, j)
        for i, j in combinations(range(len(shape)), 2)
        if supports[i] & supports[j]
    )


def connected_graph_type(vertex_count, edges):
    degrees = [0] * vertex_count
    for i, j in edges:
        degrees[i] += 1
        degrees[j] += 1
    key = (len(edges), tuple(sorted(degrees)))
    names = {
        (0, (0,)): "K1",
        (1, (1, 1)): "K2",
        (2, (1, 1, 2)): "P3",
        (3, (2, 2, 2)): "K3",
        (3, (1, 1, 2, 2)): "P4",
        (3, (1, 1, 1, 3)): "K1,3",
        (4, (2, 2, 2, 2)): "C4",
        (4, (1, 2, 2, 3)): "paw",
        (5, (2, 2, 3, 3)): "K4-e",
        (6, (3, 3, 3, 3)): "K4",
    }
    return names[key]


def incidence_component_type(component, shape):
    edges = tuple(event for event in shape if set(event) <= component)
    degree = Counter(x for edge in edges for x in edge)
    key = (len(edges), tuple(sorted(degree.values())))
    names = {
        (1, (1, 1)): "K2",
        (2, (1, 1, 2)): "P3",
        (3, (1, 1, 2, 2)): "P4",
        (3, (1, 1, 1, 3)): "K1,3",
        (3, (2, 2, 2)): "K3",
        (4, (1, 1, 2, 2, 2)): "P5",
        (4, (1, 1, 1, 1, 4)): "K1,4",
        (4, (1, 1, 1, 2, 3)): "fork5",
        (4, (2, 2, 2, 2)): "C4",
        (4, (1, 2, 2, 3)): "paw",
    }
    return names[key]


def incidence_type(shape):
    vertices = {x for event in shape for x in event}
    components = graph_components(vertices, set(shape))
    return "+".join(sorted(incidence_component_type(component, shape) for component in components))


def equality_pattern(values):
    labels = {}
    return tuple(labels.setdefault(value, len(labels)) for value in values)


def signature(shape, multiplicities, m):
    endpoints = tuple(sorted({x for event in shape for x in event}))
    overlap_matrix = tuple(
        max(0, m - abs(a - b)) for a, b in combinations(endpoints, 2)
    )
    dependencies = dependency_edges(shape, m)
    assert support_connected(shape, m)
    subset_data = []
    for mask in range(1, 1 << len(shape)):
        subset = tuple(shape[i] for i in range(len(shape)) if mask & (1 << i))
        closure = clique_closure(subset)
        rank = equality_rank(subset, m)
        assert equality_rank(closure, m) == rank
        subset_data.append((mask, rank, closure, tuple(sorted(set(closure) - set(subset)))))
    return (
        multiplicities,
        shape,
        max(endpoints),
        incidence_type(shape),
        overlap_matrix,
        connected_graph_type(len(shape), dependencies),
        tuple(b - a for a, b in shape),
        equality_pattern(tuple(b - a for a, b in shape)),
        tuple(subset_data),
    )


def set_partitions(items):
    items = tuple(items)
    if not items:
        yield ()
        return
    first = items[0]
    for partition in set_partitions(items[1:]):
        yield ((first,),) + partition
        for i in range(len(partition)):
            yield partition[:i] + ((first,) + partition[i],) + partition[i + 1 :]


PARTITIONS_4 = tuple(set_partitions(range(4)))
assert len(PARTITIONS_4) == 15


def moment(labels, m, base=10):
    return Fraction(1, base ** equality_rank(labels, m))


def joint_kappa4(labels, m, base=10):
    assert len(labels) == 4
    answer = Fraction(0)
    for partition in PARTITIONS_4:
        coefficient = (-1) ** (len(partition) - 1) * factorial(len(partition) - 1)
        term = Fraction(coefficient)
        for block in partition:
            term *= moment(tuple(labels[i] for i in block), m, base)
        answer += term
    return answer


def endpoint_rank(events):
    vertices = {x for event in set(events) for x in event}
    parent = {x: x for x in vertices}

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in set(events):
        ra, rb = root(a), root(b)
        if ra != rb:
            parent[rb] = ra
    return len(vertices) - len({root(x) for x in vertices})


def occupancy_moment(labels, m, base=10):
    return Fraction(1, base ** (m * endpoint_rank(labels)))


def occupancy_kappa4(labels, m, base=10):
    answer = Fraction(0)
    for partition in PARTITIONS_4:
        coefficient = (-1) ** (len(partition) - 1) * factorial(len(partition) - 1)
        term = Fraction(coefficient)
        for block in partition:
            term *= occupancy_moment(tuple(labels[i] for i in block), m, base)
        answer += term
    return answer


def closed_stratum_values(shape, multiplicities, m):
    labels = tuple(
        event
        for event, count in zip(shape, multiplicities)
        for _ in range(count)
    )
    return joint_kappa4(labels, m)


def check_closed_formulas():
    for n in range(2, 7):
        for m in range(1, 5):
            p = Fraction(1, 10**m)
            for e in event_space(n):
                k4 = p - 7 * p**2 + 12 * p**3 - 6 * p**4
                assert joint_kappa4((e, e, e, e), m) == k4
            for e, f in combinations(event_space(n), 2):
                q = moment((e, f), m)
                k31 = (1 - 6 * p + 6 * p**2) * (q - p**2)
                covariance = q - p**2
                k22 = (1 - 2 * p) ** 2 * covariance - 2 * covariance**2
                assert joint_kappa4((e, e, e, f), m) == k31
                assert joint_kappa4((e, e, f, f), m) == k22
            for e, f, g in combinations(event_space(n), 3):
                t = moment((e, f, g), m)
                a = moment((e, f), m)
                b = moment((e, g), m)
                c = moment((f, g), m)
                k3 = t - p * (a + b + c) + 2 * p**3
                k211 = (1 - 2 * p) * k3 - 2 * (a - p**2) * (b - p**2)
                assert joint_kappa4((e, e, f, g), m) == k211
                for repeated, other1, other2 in ((f, e, g), (g, e, f)):
                    a2 = moment((repeated, other1), m)
                    b2 = moment((repeated, other2), m)
                    k211_role = (1 - 2 * p) * k3 - 2 * (a2 - p**2) * (b2 - p**2)
                    assert joint_kappa4((repeated, repeated, other1, other2), m) == k211_role
            for shape in combinations(event_space(n), 4):
                full = moment(shape, m)
                triples = [moment(tuple(shape[i] for i in range(4) if i != omitted), m) for omitted in range(4)]
                pairs = {(i, j): moment((shape[i], shape[j]), m) for i, j in combinations(range(4), 2)}
                formula = (
                    full
                    - p * sum(triples)
                    - pairs[0, 1] * pairs[2, 3]
                    - pairs[0, 2] * pairs[1, 3]
                    - pairs[0, 3] * pairs[1, 2]
                    + 2 * p**2 * sum(pairs.values())
                    - 6 * p**4
                )
                rank_formula = p**4 * (
                    10 ** (4 * m - equality_rank(shape, m))
                    - sum(10 ** (3 * m - equality_rank(tuple(shape[i] for i in range(4) if i != omitted), m)) for omitted in range(4))
                    - 10 ** (2 * m - equality_rank((shape[0], shape[1]), m) + 2 * m - equality_rank((shape[2], shape[3]), m))
                    - 10 ** (2 * m - equality_rank((shape[0], shape[2]), m) + 2 * m - equality_rank((shape[1], shape[3]), m))
                    - 10 ** (2 * m - equality_rank((shape[0], shape[3]), m) + 2 * m - equality_rank((shape[1], shape[2]), m))
                    + 2 * sum(10 ** (2 * m - equality_rank((shape[i], shape[j]), m)) for i, j in combinations(range(4), 2))
                    - 6
                )
                assert joint_kappa4(shape, m) == formula == rank_formula


MULTIPLICITIES = {
    1: ((4,),),
    2: ((3, 1), (1, 3), (2, 2)),
    3: ((2, 1, 1), (1, 2, 1), (1, 1, 2)),
    4: ((1, 1, 1, 1),),
}


def multinomial(multiplicities):
    answer = factorial(4)
    for count in multiplicities:
        answer //= factorial(count)
    return answer


def full_expansion(n, m, base=10):
    answer = Fraction(0)
    tuple_count = 0
    for distinct_count in range(1, 5):
        for shape in normalized_shapes(n, distinct_count):
            span = max(x for event in shape for x in event)
            embeddings = n - span
            for multiplicities in MULTIPLICITIES[distinct_count]:
                labels = tuple(
                    event
                    for event, count in zip(shape, multiplicities)
                    for _ in range(count)
                )
                weight = multinomial(multiplicities)
                answer += embeddings * weight * joint_kappa4(labels, m, base)
                tuple_count += embeddings * weight
    assert tuple_count == len(event_space(n)) ** 4
    return answer


def direct_kappa4(n, m, base=2):
    values = []
    for word in product(range(base), repeat=n + m - 1):
        blocks = tuple(word[i : i + m] for i in range(n))
        values.append(sum(blocks[i] == blocks[j] for i, j in event_space(n)))
    mean = Fraction(sum(values), len(values))
    variance = sum((Fraction(x) - mean) ** 2 for x in values) / len(values)
    fourth = sum((Fraction(x) - mean) ** 4 for x in values) / len(values)
    return fourth - 3 * variance**2


def four_distinct_census():
    rows = []
    for n in range(5, 8):
        for m in range(1, 4):
            signs = Counter()
            signature_count = 0
            for shape in normalized_shapes(n, 4):
                if not support_connected(shape, m):
                    continue
                value = joint_kappa4(shape, m)
                signs["negative" if value < 0 else "positive" if value > 0 else "zero"] += 1
                record = signature(shape, (1, 1, 1, 1), m)
                assert len(record[-1]) == 15
                assert n - record[2] > 0
                signature_count += 1
            assert signature_count == sum(signs.values())
            rows.append((n, m, signs["negative"], signs["zero"], signs["positive"]))
    return rows


def check_signature_partition():
    allowed_incidence = {
        1: {"K2"},
        2: {"K2+K2", "P3"},
        3: {"K2+K2+K2", "K2+P3", "P4", "K1,3", "K3"},
        4: {
            "K2+K2+K2+K2", "K2+K2+P3", "P3+P3",
            "K2+P4", "K1,3+K2", "K2+K3",
            "P5", "K1,4", "fork5", "C4", "paw",
        },
    }
    for n in range(2, 8):
        total_unordered_sets = 0
        total_embeddings = 0
        for distinct_count in range(1, min(4, len(event_space(n))) + 1):
            expected_sets = len(tuple(combinations(event_space(n), distinct_count)))
            counted_sets = 0
            for shape in normalized_shapes(n, distinct_count):
                span = max(x for event in shape for x in event)
                embeddings = n - span
                counted_sets += embeddings
                assert incidence_type(shape) in allowed_incidence[distinct_count]
                for m in range(1, 4):
                    if support_connected(shape, m):
                        for multiplicities in MULTIPLICITIES[distinct_count]:
                            record = signature(shape, multiplicities, m)
                            assert record[0] == multiplicities
                            assert record[1] == shape
                            assert record[2] == span
            assert counted_sets == expected_sets
            total_unordered_sets += expected_sets
            total_embeddings += counted_sets
        assert total_unordered_sets == total_embeddings


def check_triangle_tail():
    shape = ((0, 1), (1, 2), (0, 2), (2, 3))
    # At m=2 the ranks by subset cardinality are not constant; use the exact list.
    exact_m2 = (2, 2, 3, 2, 3, 3, 3, 2, 4, 3, 4, 4, 4, 4, 4)
    actual_m2 = tuple(
        equality_rank(tuple(shape[i] for i in range(4) if mask & (1 << i)), 2)
        for mask in range(1, 16)
    )
    assert actual_m2 == exact_m2

    assert joint_kappa4(shape, 1) == 0
    assert occupancy_kappa4(shape, 1) == 0

    for m in range(2, 8):
        p = Fraction(1, 10**m)
        pair_ranks = {
            frozenset((i, j)): equality_rank((shape[i], shape[j]), m)
            for i, j in combinations(range(4), 2)
        }
        assert [pair_ranks[frozenset(pair)] for pair in ((0, 1), (0, 2), (1, 2), (1, 3))] == [m + 1] * 4
        assert [pair_ranks[frozenset(pair)] for pair in ((0, 3), (2, 3))] == [m + 2] * 2
        triple_ranks = [
            equality_rank(tuple(shape[i] for i in subset), m)
            for subset in combinations(range(4), 3)
        ]
        assert triple_ranks == [m + 1, m + 2, m + 2, m + 2]
        assert equality_rank(shape, m) == m + 2
        formula = p / 100 - Fraction(71, 500) * p**2 + Fraction(21, 25) * p**3 - 6 * p**4
        assert joint_kappa4(shape, m) == formula
        assert formula > p / 125
        assert formula < p / 100
        assert occupancy_kappa4(shape, m) == 0
        reflected = tuple(sorted((3 - b, 3 - a) for a, b in shape))
        assert reflected != tuple(sorted(shape))
        assert joint_kappa4(reflected, m) == formula
    logarithmic_cases = (
        (10**8, 2), (10**9, 2), (10**10, 2),
        (10**11, 2), (10**12, 2), (10**12, 3),
    )
    for n, m in logarithmic_cases:
        assert 4 * m <= len(str(n)) - 1
        p = Fraction(1, 10**m)
        formula = p / 100 - Fraction(71, 500) * p**2 + Fraction(21, 25) * p**3 - 6 * p**4
        contribution = 24 * (n - 3) * formula
        assert contribution > Fraction(12, 125) * n * p
        mean = Fraction(n * (n - 1), 2) * p
        assert contribution / mean < Fraction(12, 25 * n)
    return shape


def check_occupancy_cliques():
    # Direct categorical enumeration checks the complete-clique fourth cumulant.
    for base in (2, 3):
        p = Fraction(1, base)
        for k in range(2, 6):
            values = []
            for words in product(range(base), repeat=k):
                values.append(sum(words[i] == words[j] for i, j in event_space(k)))
            mean = Fraction(sum(values), len(values))
            variance = sum((Fraction(x) - mean) ** 2 for x in values) / len(values)
            fourth = sum((Fraction(x) - mean) ** 4 for x in values) / len(values)
            actual = fourth - 3 * variance**2
            expected = (
                len(event_space(k)) * p * (1 - p) * (1 - 6 * p + 6 * p**2)
                + 36 * len(tuple(combinations(range(k), 3))) * p**2 * (1 - p) * (1 - 2 * p)
                + 72 * len(tuple(combinations(range(k), 4))) * p**3 * (1 - p)
            )
            assert actual == expected


def main():
    canonical = Path("canonical_statement.txt")
    assert sha256(canonical.read_bytes()).hexdigest() == CANONICAL_SHA256
    check_closed_formulas()
    check_signature_partition()
    triangle_tail = check_triangle_tail()
    check_occupancy_cliques()
    for n in range(2, 6):
        for m in range(1, 4):
            assert full_expansion(n, m, 2) == direct_kappa4(n, m, 2)
    census = four_distinct_census()

    print(f"CANONICAL_SHA256 {CANONICAL_SHA256}")
    print(f"SET_PARTITIONS_4 {len(PARTITIONS_4)}")
    print("REPETITION_STRATA 4 31 22 211 1111")
    print("ORDERED_WEIGHTS 1 8 6 12x3 24")
    print("DIRECT_BINARY_CHECKS 12")
    print("OCCUPANCY_CLIQUE_CHECKS 8")
    print("SIGNATURE_FIELDS 9")
    print("INCIDENCE_TYPES 1 2 5 11")
    print("LOG_DEPTH_CHECKS 6")
    for n, m, negative, zero, positive in census:
        print(f"CENSUS N={n} m={m} negative={negative} zero={zero} positive={positive}")
    print(f"TRIANGLE_TAIL {triangle_tail}")
    print("TRIANGLE_TAIL_M_RANGE 2..7")
    print("TRIANGLE_TAIL_ACTUAL positive")
    print("TRIANGLE_TAIL_OCCUPANCY_ONLY zero")
    print("SCOPED_VERDICT NONABSORPTION")


if __name__ == "__main__":
    main()
