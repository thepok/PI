#!/usr/bin/env python3
"""Exact validation for T148. Finite computation is not a universal proof."""

from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED_HASHES = {
    "active-items-snapshot.txt": "b27c00ba054f460f4431206e459a01ab48f047f1afc1d2fbc020b6d60ccb9c08",
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "prior-T133-REPORT.md": "53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40",
    "prior-T141-REPORT.md": "e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356",
    "prior-T143-REPORT.md": "b446b83025fd408fdbc8580e0e6871ab514ad169b0fe1d33407f6ad9061ca0d9",
    "prior-T145-REPORT.md": "17774f8020ddba63203d2a956e1edbd3e2d432a32cafde11386d35a3514d229c",
}


def digest(name):
    return sha256((ROOT / name).read_bytes()).hexdigest()


def floor_fraction(x):
    return x.numerator // x.denominator


def digit_sum(n, p):
    total = 0
    while n:
        total += n % p
        n //= p
    return total


def factorial_valuation(n, p):
    total = 0
    while n:
        n //= p
        total += n
    return total


def transition(state, digit):
    alpha, beta = state
    return ((3 * digit + alpha) // 2, (2 * digit + beta) // 2)


def potential(state):
    alpha, beta = state
    return alpha - 3 * beta


def weight(state, digit):
    nxt = transition(state, digit)
    return 2 * potential(nxt) - potential(state)


def terminal(state):
    alpha, beta = state
    return 3 * digit_sum(beta, 2) - digit_sum(alpha, 2)


def accessible_graph():
    seen = {(0, 0)}
    queue = [(0, 0)]
    while queue:
        state = queue.pop(0)
        for digit in range(2):
            nxt = transition(state, digit)
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def simple_cycles(vertices):
    cycles = set()
    vertices = sorted(vertices)
    for start in vertices:
        def walk(path, digits):
            state = path[-1]
            for digit in range(2):
                nxt = transition(state, digit)
                if nxt == start:
                    raw = tuple(path), tuple(digits + [digit])
                    rotations = []
                    states, ds = raw
                    for j in range(len(states)):
                        rotations.append((states[j:] + states[:j], ds[j:] + ds[:j]))
                    cycles.add(min(rotations))
                elif nxt not in path and len(path) < len(vertices):
                    walk(path + [nxt], digits + [digit])
        walk([start], [])
    return sorted(cycles)


def atom_data():
    endpoints = sorted({Fraction(0), Fraction(1)} |
                       {Fraction(m, c) for c in (1, 2, 3) for m in range(c + 1)})
    rows = []
    for left, right in zip(endpoints, endpoints[1:]):
        x = (left + right) / 2
        lam = 3 * floor_fraction(x) + floor_fraction(3 * x) - 3 * floor_fraction(2 * x)
        d_found = None
        witness = None
        for d in range(1, 20):
            q = 2**d - 1
            for k in range(1, q):
                y = Fraction(k, q)
                if left < y < right:
                    d_found, witness = d, y
                    break
            if d_found is not None:
                break
        rows.append((left, right, lam, d_found, witness))
    return rows


def path(digits, start=(0, 0)):
    states = [start]
    weights = []
    for digit in digits:
        weights.append(weight(states[-1], digit))
        states.append(transition(states[-1], digit))
    return states, weights


def main():
    for name, expected in EXPECTED_HASHES.items():
        assert digest(name) == expected, name

    atoms = atom_data()
    expected_atoms = [
        (Fraction(0), Fraction(1, 3), 0, 3, Fraction(1, 7)),
        (Fraction(1, 3), Fraction(1, 2), 1, 3, Fraction(3, 7)),
        (Fraction(1, 2), Fraction(2, 3), -2, 3, Fraction(4, 7)),
        (Fraction(2, 3), Fraction(1), -1, 3, Fraction(5, 7)),
    ]
    assert atoms == expected_atoms
    assert min(right - left for left, right, *_ in atoms) == Fraction(1, 6)
    assert Fraction(1, 6) >= Fraction(1, 9)

    vertices = accessible_graph()
    assert vertices == {(0, 0), (1, 1), (2, 1), (1, 0)}
    expected_edges = {
        ((0, 0), 0): ((0, 0), 0),
        ((0, 0), 1): ((1, 1), -4),
        ((1, 1), 0): ((0, 0), 2),
        ((1, 1), 1): ((2, 1), 0),
        ((2, 1), 0): ((1, 0), 3),
        ((2, 1), 1): ((2, 1), -1),
        ((1, 0), 0): ((0, 0), -1),
        ((1, 0), 1): ((2, 1), -3),
    }
    for key, value in expected_edges.items():
        state, digit = key
        assert (transition(state, digit), weight(state, digit)) == value
        nxt = transition(state, digit)
        assert weight(state, digit) + terminal(nxt) <= terminal(state)

    cycles = simple_cycles(vertices)
    means = []
    for states, digits in cycles:
        total = sum(weight(state, digit) for state, digit in zip(states, digits))
        means.append(Fraction(total, len(digits)))
        assert total == sum(potential(state) for state in states)
    assert sorted(means) == [Fraction(-1), Fraction(-1), Fraction(-1, 2), Fraction(0), Fraction(0)]
    assert max(means) == 0

    access_states, access_weights = path([1, 1, 0])
    assert access_states == [(0, 0), (1, 1), (2, 1), (1, 0)]
    assert sum(access_weights) == -1
    cycle_states, cycle_weights = path([1, 1, 0], (1, 0))
    assert cycle_states == [(1, 0), (2, 1), (2, 1), (1, 0)]
    assert sum(cycle_weights) == -1
    assert [potential(q) for q in cycle_states[:-1]] == [1, -1, -1]
    orbit = [Fraction(3, 7)]
    for digit in [1, 1, 0]:
        orbit.append((digit + orbit[-1]) / 2)
    assert orbit == [Fraction(3, 7), Fraction(5, 7), Fraction(6, 7), Fraction(3, 7)]
    flush_states, flush_weights = path([0], (1, 0))
    assert flush_states[-1] == (0, 0) and sum(flush_weights) == -1

    for repetition in range(9):
        digits = [1, 1, 0] * (repetition + 1)
        states, weights = path(digits)
        n = 3 * (8 ** (repetition + 1) - 1) // 7
        assert n == sum(digit << j for j, digit in enumerate(digits))
        total = sum(weights) + terminal(states[-1])
        valuation = (3 * factorial_valuation(n, 2) + factorial_valuation(3 * n, 2)
                     - 3 * factorial_valuation(2 * n, 2))
        assert total == valuation == -(repetition + 2)

    for n in range(4096):
        length = max(1, n.bit_length())
        digits = [(n >> j) & 1 for j in range(length)]
        states, weights = path(digits)
        valuation = (3 * factorial_valuation(n, 2) + factorial_valuation(3 * n, 2)
                     - 3 * factorial_valuation(2 * n, 2))
        assert sum(weights) + terminal(states[-1]) == valuation
        x = Fraction(n, 2**length)
        assert potential(states[-1]) == (3 * floor_fraction(x) + floor_fraction(3 * x)
                                          - 3 * floor_fraction(2 * x))
        assert valuation <= 0

    for t in range(1, 17):
        for state, digit in expected_edges:
            assert t * weight(state, digit) == 2 * (t * potential(transition(state, digit))) - t * potential(state)
        assert max(t * mean for mean in means) == 0

    d_uniform = next(d for d in range(1, 20) if 2**d - 1 > 3**2)
    assert d_uniform == 4
    print("EVIDENCE_LABEL: experiment (exact finite validation only)")
    print("canonical_and_comparator_hashes: OK")
    print("atoms:", [(str(a), str(b), h, d, str(x)) for a, b, h, d, x in atoms])
    print("minimum_atom_width: 1/6; universal Farey bound: 1/9")
    print("accessible_states:", sorted(vertices))
    print("cycle_means:", [str(x) for x in sorted(means)])
    print("mu_plus: 0")
    print("positive_atom_bound_claim: 1/3 (refuted)")
    print("D_2(3): 4; uniform_bound_claim: 1/4 (refuted)")
    print("access_digits: 110 LSDF; access_length: 3")
    print("periodic_cycle_potentials: [1, -1, -1]; cycle_weight: -1")
    print("exact_zero_flush_from_positive_state: 1; uniform_zero_flush_bound: 2")
    print("counterfamily_scaling_validation: 1 <= t <= 16; proof is algebraic")
    print("finite_valuation_sweep: 0 <= n < 4096, all valuations <= 0")
    print("validation: PASS")


if __name__ == "__main__":
    main()
