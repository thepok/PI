#!/usr/bin/env python3
"""Independent bounded replay for T145. Finite checks are experiment only."""

from collections import deque
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "canonical_statement.txt":
        "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-T133-REPORT.md":
        "53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40",
    "prior-T141-REPORT.md":
        "e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356",
    "active-T143-REPORT.md":
        "e20df633705a85a7e77c867fbe73535bb2e5cd1851178f4739d0fd8e5b6a1e1f",
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def digit_sum(n, p):
    total = 0
    while n:
        total += n % p
        n //= p
    return total


def vp_factorial(n, p):
    total = 0
    while n:
        n //= p
        total += n
    return total


def valuation(a, b, n, p):
    return sum(vp_factorial(c * n, p) for c in a) - sum(
        vp_factorial(c * n, p) for c in b
    )


def landau(a, b, x):
    return sum(c * x.numerator // x.denominator for c in a) - sum(
        c * x.numerator // x.denominator for c in b
    )


def landau_nonnegative(a, b):
    coefficients = set(a) | set(b)
    points = {Fraction(0)}
    for c in coefficients:
        points.update(Fraction(k, c) for k in range(c))
    return all(landau(a, b, x) >= 0 for x in points)


def transition(a, b, p, state, digit):
    split = len(a)
    alpha, beta = state[:split], state[split:]
    alpha2 = tuple((c * digit + carry) // p for c, carry in zip(a, alpha))
    beta2 = tuple((c * digit + carry) // p for c, carry in zip(b, beta))
    state2 = alpha2 + beta2
    phi = sum(alpha) - sum(beta)
    phi2 = sum(alpha2) - sum(beta2)
    weight = p * phi2 - phi
    emitted = sum(
        c * digit + carry - p * carry2
        for c, carry, carry2 in zip(b, beta, beta2)
    ) - sum(
        c * digit + carry - p * carry2
        for c, carry, carry2 in zip(a, alpha, alpha2)
    )
    assert weight == emitted
    return state2, weight


def terminal(a, b, p, state):
    split = len(a)
    return sum(digit_sum(x, p) for x in state[split:]) - sum(
        digit_sum(x, p) for x in state[:split]
    )


def graph(a, b, p):
    zero = (0,) * (len(a) + len(b))
    queue = deque([zero])
    seen = {zero}
    edges = {}
    while queue:
        state = queue.popleft()
        for digit in range(p):
            state2, weight = transition(a, b, p, state, digit)
            edges[state, digit] = state2, weight
            if state2 not in seen:
                seen.add(state2)
                queue.append(state2)
    return zero, seen, edges


def state_after_word(a, b, p, n, length, edges):
    state = (0,) * (len(a) + len(b))
    total = 0
    for _ in range(length):
        digit = n % p
        n //= p
        state, weight = edges[state, digit]
        total += weight
    assert n == 0
    return state, total


def simple_cycle_means(states, edges, p):
    states = sorted(states)
    means = set()
    for start in states:
        def visit(current, visited, weight):
            for digit in range(p):
                nxt, edge_weight = edges[current, digit]
                if nxt == start:
                    means.add(Fraction(weight + edge_weight, len(visited)))
                elif nxt not in visited and len(visited) < len(states):
                    visit(nxt, visited + (nxt,), weight + edge_weight)
        visit(start, (start,), 0)
    return means


def partitions(n, cap=None):
    if n == 0:
        yield ()
        return
    if cap is None or cap > n:
        cap = n
    for first in range(cap, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def check_graph(a, b, p, word_depth):
    zero, states, edges = graph(a, b, p)
    assert edges[zero, 0] == (zero, 0)
    positive = False
    for state in states:
        phi = sum(state[:len(a)]) - sum(state[len(a):])
        assert phi >= 0
        positive |= phi > 0
        flushed = state
        for _ in range(max(a + b).bit_length() + 2):
            if flushed == zero:
                break
            flushed, _ = edges[flushed, 0]
        assert flushed == zero
        for digit in range(p):
            nxt, weight = edges[state, digit]
            phi2 = sum(nxt[:len(a)]) - sum(nxt[len(a):])
            assert weight == p * phi2 - phi
    assert positive == (tuple(sorted(a)) != tuple(sorted(b)))

    for length in range(word_depth + 1):
        for n in range(p ** length):
            state, edge_total = state_after_word(a, b, p, n, length, edges)
            path_total = edge_total + terminal(a, b, p, state)
            assert path_total == (p - 1) * valuation(a, b, n, p)
            expected = tuple((c * n) // (p ** length) for c in a + b)
            assert state == expected
    return len(states)


def main():
    for name, expected in EXPECTED.items():
        actual = digest(ROOT / name)
        assert actual == expected, (name, actual, expected)
    print("HASH_INPUT_COUNT=4")
    print("CANONICAL_SHA256=" + EXPECTED["canonical_statement.txt"])

    a, b, p = (2,), (1, 1), 2
    _, states, edges = graph(a, b, p)
    expected_edges = {
        ((0, 0, 0), 0): ((0, 0, 0), 0),
        ((0, 0, 0), 1): ((1, 0, 0), 2),
        ((1, 0, 0), 0): ((0, 0, 0), -1),
        ((1, 0, 0), 1): ((1, 0, 0), 1),
    }
    assert edges == expected_edges
    means = simple_cycle_means(states, edges, p)
    assert means == {Fraction(0), Fraction(1, 2), Fraction(1)}
    print("CENTRAL_BINOMIAL_STATES=2")
    print("CENTRAL_BINOMIAL_SIMPLE_CYCLE_MEANS=0,1/2,1")

    graph_prime_cases = 0
    integral_pairs = 0
    max_states = 0
    for total in range(1, 11):
        parts = list(partitions(total))
        for a0, b0 in product(parts, repeat=2):
            if not landau_nonnegative(a0, b0):
                continue
            integral_pairs += 1
            for prime in (2, 3, 5, 7):
                states_count = check_graph(a0, b0, prime, word_depth=3)
                max_states = max(max_states, states_count)
                graph_prime_cases += 1
    print("SWEEP_COMMON_SUM_MAX=10")
    print("SWEEP_PRIMES=2,3,5,7")
    print(f"LANDAU_INTEGRAL_ORDERED_PARTITION_PAIRS={integral_pairs}")
    print(f"GRAPH_PRIME_CASES={graph_prime_cases}")
    print(f"MAX_ACCESSIBLE_STATES={max_states}")
    print("FINITE_CLASSIFICATION_FAILURES=0")
    print("FINITE_EVIDENCE_LABEL=experiment")
    print("REPLAY_OK")


if __name__ == "__main__":
    main()
