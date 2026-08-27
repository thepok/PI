#!/usr/bin/env python3
"""Self-contained exact replay for T94's regular-paperfolding recurrence.

Finite replay checks transcription and declared sanity ranges.  The universal
argument is the induction in REPORT.md, not extrapolation from these checks.
"""

from collections import Counter
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SOURCE_SHA256 = "9ee4f3884e5029c5dc507736d7c4364c8757bb18996e0535ddf756247108cc72"
SPEC = json.loads((ROOT / "automaton_spec.json").read_text())


def paperfolding_digit(index: int) -> int:
    """One-based p[2^a(2j+1)] = j mod 2."""
    assert index >= 1
    while index % 2 == 0:
        index //= 2
    return ((index - 1) // 2) % 2


def block(start: int, length: int) -> tuple[int, ...]:
    assert start >= 1 and length >= 0
    return tuple(paperfolding_digit(i) for i in range(start, start + length))


def alternating(first: int, length: int) -> tuple[int, ...]:
    return tuple(first ^ (i & 1) for i in range(length))


def literal_collision(length: int, starts: int) -> int:
    counts = Counter(block(s, length) for s in range(1, starts + 1))
    return sum(multiplicity * multiplicity for multiplicity in counts.values())


def eta(left: int, right: int, length: int) -> bool:
    return length == 0 or left == right


def gamma(first: int, constant: int, length: int) -> bool:
    return length == 0 or (length == 1 and first == constant)


def parity_count(parity: int, bound: int) -> int:
    return bound // 2 if parity == 0 else (bound + 1) // 2


def same_parity_pairs(bound: int) -> int:
    return parity_count(0, bound) ** 2 + parity_count(1, bound) ** 2


@lru_cache(maxsize=None)
def ones(bound: int) -> int:
    if bound == 0:
        return 0
    even_bound = bound // 2
    odd_bound = (bound + 1) // 2
    return ones(even_bound) + odd_bound // 2


def collision_length_one(bound: int) -> int:
    z = ones(bound)
    return z * z + (bound - z) * (bound - z)


@lru_cache(maxsize=None)
def A_count(parity: int, first: int, length: int, bound: int) -> int:
    """Starts s<=bound of parity `parity` with B(s,length)=alternating(first)."""
    if bound == 0:
        return 0
    if length == 0:
        return parity_count(parity, bound)
    h, ell = (length + 1) // 2, length // 2
    if parity == 0:
        smaller_bound = bound // 2
        return sum(
            K_count(q, first, h, smaller_bound)
            for q in (0, 1)
            if gamma(q, 1 - first, ell)
        )
    smaller_bound = (bound + 1) // 2
    return sum(
        K_count(1 - q, 1 - first, ell, smaller_bound)
        for q in (0, 1)
        if gamma(q, first, h)
    )


@lru_cache(maxsize=None)
def K_count(parity: int, value: int, length: int, bound: int) -> int:
    """Starts s<=bound of parity `parity` with B(s,length)=value^length."""
    if bound == 0:
        return 0
    if length == 0:
        return parity_count(parity, bound)
    h, ell = (length + 1) // 2, length // 2
    if parity == 0:
        smaller_bound = bound // 2
        return sum(
            K_count(q, value, h, smaller_bound)
            for q in (0, 1)
            if gamma(q, value, ell)
        )
    smaller_bound = (bound + 1) // 2
    return sum(
        K_count(1 - q, value, ell, smaller_bound)
        for q in (0, 1)
        if gamma(q, value, h)
    )


@lru_cache(maxsize=None)
def same_parity_collision(length: int, bound: int) -> int:
    if bound == 0:
        return 0
    if length == 0:
        return same_parity_pairs(bound)
    even_bound = bound // 2
    odd_bound = (bound + 1) // 2
    if length == 1:
        return collision_length_one(even_bound) + same_parity_pairs(odd_bound)
    h, ell = (length + 1) // 2, length // 2
    return (
        same_parity_collision(h, even_bound)
        + same_parity_collision(ell, odd_bound)
    )


@lru_cache(maxsize=None)
def mixed_orientation_collision(length: int, bound: int) -> int:
    """Even-start/odd-start ordered collisions; reverse orientation is equal."""
    if bound == 0:
        return 0
    h, ell = (length + 1) // 2, length // 2
    even_bound = bound // 2
    odd_bound = (bound + 1) // 2
    return sum(
        A_count(r, 1 - q, h, even_bound) * A_count(q, r, ell, odd_bound)
        for r in (0, 1)
        for q in (0, 1)
    )


@lru_cache(maxsize=None)
def recurrence_collision(length: int, bound: int) -> int:
    return (
        same_parity_collision(length, bound)
        + 2 * mixed_orientation_collision(length, bound)
    )


def pf_state_step(state: str, bit: int) -> str:
    return SPEC["symbol_dfao"]["transition"][state][str(bit)]


def pf_automaton_digit(index: int) -> int:
    state = SPEC["symbol_dfao"]["initial"]
    value = index
    while value:
        state = pf_state_step(state, value & 1)
        value //= 2
    state = pf_state_step(state, 0)
    state = pf_state_step(state, 0)
    return int(state in SPEC["symbol_dfao"]["output_one"])


def check_spec() -> tuple[int, int]:
    spec = SPEC
    assert spec["scope"] == "regular paperfolding only"
    assert spec["profile_states"] == ["E", "A0", "A1", "K0", "K1"]
    assert spec["instantiated_profile_transition_rows"] == 12
    table = spec["symbol_dfao"]["transition"]
    expected_table = {
        "Z": {"0": "Z", "1": "A"},
        "A": {"0": "O0", "1": "O1"},
        "O0": {"0": "O0", "1": "O0"},
        "O1": {"0": "O1", "1": "O1"},
    }
    assert table == expected_table
    assert spec["symbol_dfao"]["initial"] == "Z"
    assert spec["symbol_dfao"]["output_one"] == ["O1"]
    assert set(table) == {"Z", "A", "O0", "O1"}
    assert all(set(row) == {"0", "1"} for row in table.values())
    symbol_transitions = len(table) * 2

    tensor_states = [(x, y) for x in table for y in table]
    tensor_transitions = 0
    for x, y in tensor_states:
        for left_bit in (0, 1):
            for right_bit in (0, 1):
                target = (
                    table[x][str(left_bit)],
                    table[y][str(right_bit)],
                )
                assert target in tensor_states
                tensor_transitions += 1
    assert len(tensor_states) == 16 and tensor_transitions == 64
    rows = spec["profile_transition_rows"]
    assert len(rows) == 12
    keys = [(row["state"], tuple(row["parities"])) for row in rows]
    expected_keys = [
        ("E", (0, 0)), ("E", (1, 1)), ("E", (0, 1)), ("E", (1, 0)),
        ("A0", (0,)), ("A0", (1,)), ("A1", (0,)), ("A1", (1,)),
        ("K0", (0,)), ("K0", (1,)), ("K1", (0,)), ("K1", (1,)),
    ]
    assert keys == expected_keys
    return symbol_transitions, tensor_transitions


def expression_value(expression: str, environment: dict[str, int]) -> int:
    if expression in {"0", "1"}:
        return int(expression)
    if expression in environment:
        return environment[expression]
    if expression.endswith("%2"):
        return environment[expression[:-2]] % 2
    if expression.endswith("+1"):
        return environment[expression[:-2]] + 1
    raise AssertionError(f"unknown expression {expression}")


def profile_truth(state: str, arguments: list[int]) -> bool:
    if state == "E":
        left, right, length = arguments
        return block(left, length) == block(right, length)
    start, length = arguments
    kind, bit = state[0], int(state[1])
    if kind == "A":
        return block(start, length) == alternating(bit, length)
    if kind == "K":
        return block(start, length) == (bit,) * length
    raise AssertionError(f"unknown profile {state}")


def child_truth(child: dict, environment: dict[str, int]) -> bool:
    arguments = [expression_value(arg, environment) for arg in child["args"]]
    if child["kind"] == "guard":
        return eta(*arguments) if child["state"] == "eta" else gamma(*arguments)
    if child["kind"] == "profile":
        return profile_truth(child["state"], arguments)
    if child["kind"] == "profile_dynamic_A":
        selector = expression_value(child["selector"], environment)
        return profile_truth(f"A{selector}", arguments)
    raise AssertionError(f"unknown child kind {child['kind']}")


def check_decimation(limit: int) -> None:
    for a in range(1, limit + 1):
        assert paperfolding_digit(2 * a) == paperfolding_digit(a)
    for a in range(limit + 1):
        assert paperfolding_digit(4 * a + 1) == 0
        assert paperfolding_digit(4 * a + 3) == 1


def check_profile_transitions(max_start: int, max_length: int) -> int:
    checked = 0
    for row in SPEC["profile_transition_rows"]:
        for length in range(max_length + 1):
            h, ell = (length + 1) // 2, length // 2
            if row["state"] == "E":
                left_parity, right_parity = row["parities"]
                for a in range(max_start + 1):
                    for b in range(max_start + 1):
                        left = 2 * a + left_parity
                        right = 2 * b + right_parity
                        if left == 0 or right == 0:
                            continue
                        environment = {"a": a, "b": b, "h": h, "l": ell}
                        direct = profile_truth("E", [left, right, length])
                        rhs = all(child_truth(child, environment) for child in row["children"])
                        assert direct == rhs
                        checked += 1
            else:
                parity = row["parities"][0]
                for a in range(max_start + 1):
                    start = 2 * a + parity
                    if start == 0:
                        continue
                    environment = {"a": a, "h": h, "l": ell}
                    direct = profile_truth(row["state"], [start, length])
                    rhs = all(child_truth(child, environment) for child in row["children"])
                    assert direct == rhs
                    checked += 1
    return checked


@lru_cache(maxsize=None)
def canonical_positions(length: int) -> frozenset[int]:
    assert length >= 1
    if length == 1:
        return frozenset({1, 2, 3, 6})
    if length % 2 == 0:
        previous = canonical_positions(length // 2)
        return frozenset({2 * p - 1 for p in previous} | {2 * p for p in previous})
    lower = canonical_positions(length // 2)
    upper = canonical_positions(length // 2 + 1)
    return frozenset({2 * p - 1 for p in lower} | {2 * p for p in upper})


def high_bit_comparison(previous: int, left_bit: int, right_bit: int) -> int:
    if left_bit < right_bit:
        return -1
    if left_bit > right_bit:
        return 1
    return previous


def primitive_step(
    state: tuple[int, int, int, str, str],
    n_bit: int,
    i_bit: int,
    j_bit: int,
    k_bit: int,
) -> tuple[int, int, int, str, str]:
    comparison, carry_i, carry_j, symbol_i, symbol_j = state
    sum_i = i_bit + k_bit + carry_i
    sum_j = j_bit + k_bit + carry_j
    return (
        high_bit_comparison(comparison, k_bit, n_bit),
        sum_i // 2,
        sum_j // 2,
        pf_state_step(symbol_i, sum_i % 2),
        pf_state_step(symbol_j, sum_j % 2),
    )


PRIMITIVE_INITIAL = (0, 0, 0, "Z", "Z")


@lru_cache(maxsize=None)
def subset_step(
    states: frozenset[tuple[int, int, int, str, str]],
    n_bit: int,
    i_bit: int,
    j_bit: int,
) -> frozenset[tuple[int, int, int, str, str]]:
    return frozenset(
        primitive_step(state, n_bit, i_bit, j_bit, k_bit)
        for state in states
        for k_bit in (0, 1)
    )


def primitive_is_bad(state: tuple[int, int, int, str, str]) -> bool:
    flushed = state
    for _ in range(2):
        flushed = primitive_step(flushed, 0, 0, 0, 0)
    comparison, carry_i, carry_j, symbol_i, symbol_j = flushed
    assert carry_i == carry_j == 0
    output_states = set(SPEC["symbol_dfao"]["output_one"])
    return (
        comparison == -1
        and ((symbol_i in output_states) != (symbol_j in output_states))
    )


def outer_step(
    state: tuple[frozenset, int, int, bool, bool],
    n_bit: int,
    bound_bit: int,
    i_bit: int,
    j_bit: int,
) -> tuple[frozenset, int, int, bool, bool]:
    subsets, comparison_i, comparison_j, seen_i, seen_j = state
    return (
        subset_step(subsets, n_bit, i_bit, j_bit),
        high_bit_comparison(comparison_i, i_bit, bound_bit),
        high_bit_comparison(comparison_j, j_bit, bound_bit),
        seen_i or bool(i_bit),
        seen_j or bool(j_bit),
    )


def outer_accepting(state: tuple[frozenset, int, int, bool, bool]) -> bool:
    subsets, comparison_i, comparison_j, seen_i, seen_j = state
    return (
        seen_i
        and seen_j
        and comparison_i <= 0
        and comparison_j <= 0
        and not any(primitive_is_bad(primitive) for primitive in subsets)
    )


def finite_automaton_collision(length: int, bound: int, padding: int = 0) -> int:
    """Evaluate the exact finite weighted automaton without materializing matrices."""
    digits = max(1, length.bit_length(), bound.bit_length()) + padding
    initial = (frozenset({PRIMITIVE_INITIAL}), 0, 0, False, False)
    weights = {initial: 1}
    for position in range(digits):
        n_bit = (length >> position) & 1
        bound_bit = (bound >> position) & 1
        next_weights: dict[tuple, int] = {}
        for state, weight in weights.items():
            for i_bit in (0, 1):
                for j_bit in (0, 1):
                    target = outer_step(
                        state, n_bit, bound_bit, i_bit, j_bit
                    )
                    next_weights[target] = next_weights.get(target, 0) + weight
        assert sum(next_weights.values()) == 4 * sum(weights.values())
        weights = next_weights
    return sum(weight for state, weight in weights.items() if outer_accepting(state))


def check_finite_automaton(max_length: int, max_bound: int) -> tuple[int, int]:
    primitive_states = [
        (comparison, carry_i, carry_j, symbol_i, symbol_j)
        for comparison in (-1, 0, 1)
        for carry_i in (0, 1)
        for carry_j in (0, 1)
        for symbol_i in SPEC["symbol_dfao"]["states"]
        for symbol_j in SPEC["symbol_dfao"]["states"]
    ]
    assert len(primitive_states) == SPEC["factor_pair_automaton"]["primitive_state_count"]
    primitive_transitions = 0
    primitive_set = set(primitive_states)
    for state in primitive_states:
        for n_bit in (0, 1):
            for i_bit in (0, 1):
                for j_bit in (0, 1):
                    for k_bit in (0, 1):
                        assert primitive_step(state, n_bit, i_bit, j_bit, k_bit) in primitive_set
                        primitive_transitions += 1

    count_checks = 0
    for length in range(max_length + 1):
        for bound in range(max_bound + 1):
            direct = literal_collision(length, bound)
            assert finite_automaton_collision(length, bound) == direct
            assert finite_automaton_collision(length, bound, padding=2) == direct
            count_checks += 1
    return primitive_transitions, count_checks


def check_count_profiles(max_length: int, max_bound: int) -> int:
    checked = 0
    for length in range(max_length + 1):
        for bound in range(max_bound + 1):
            for parity in (0, 1):
                starts = [s for s in range(1, bound + 1) if s % 2 == parity]
                for bit in (0, 1):
                    direct_a = sum(block(s, length) == alternating(bit, length) for s in starts)
                    direct_k = sum(block(s, length) == (bit,) * length for s in starts)
                    assert A_count(parity, bit, length, bound) == direct_a
                    assert K_count(parity, bit, length, bound) == direct_k
                    checked += 2
    return checked


def check_collision_recurrence(max_length: int, max_bound: int) -> int:
    checked = 0
    for length in range(max_length + 1):
        for bound in range(max_bound + 1):
            direct = literal_collision(length, bound)
            assert recurrence_collision(length, bound) == direct
            checked += 1
    return checked


def main() -> None:
    canonical_hash = sha256((ROOT / "canonical_statement.txt").read_bytes()).hexdigest()
    source_hash = sha256((ROOT / "allouche-bousquet-melou-1994.dvi").read_bytes()).hexdigest()
    assert canonical_hash == CANONICAL_SHA256
    assert source_hash == SOURCE_SHA256
    print(f"CANONICAL sha256={canonical_hash}")
    print(f"SOURCE sha256={source_hash}")

    symbol_transitions, tensor_transitions = check_spec()
    print(
        "AUTOMATON "
        f"symbol_states=4 symbol_transitions={symbol_transitions} "
        f"tensor_states=16 tensor_transitions={tensor_transitions} "
        "profile_states=5 profile_transition_rows=12 complete=yes"
    )

    primitive_transitions, automaton_checks = check_finite_automaton(
        max_length=12, max_bound=32
    )
    print(
        "FACTOR_PAIR_AUTOMATON "
        f"primitive_states=192 primitive_transitions={primitive_transitions} "
        "outer_state_bound=36*2^192 matrix_row_weight=4 complete=yes "
        f"direct_and_padding_checks={automaton_checks}"
    )

    for index in range(1, 4097):
        assert pf_automaton_digit(index) == paperfolding_digit(index)
    check_decimation(4096)
    profile_checks = check_profile_transitions(max_start=24, max_length=24)
    count_profile_checks = check_count_profiles(max_length=24, max_bound=96)
    collision_checks = check_collision_recurrence(max_length=24, max_bound=96)
    assert all(A_count(r, e, length, 512) == 0
               for r in (0, 1) for e in (0, 1) for length in range(4, 65))
    assert recurrence_collision(7, 48) == literal_collision(7, 48) == 98
    assert recurrence_collision(0, 48) == 48**2
    naive_left = recurrence_collision(2, 3)
    naive_right = recurrence_collision(1, 1) + recurrence_collision(1, 2)
    assert (naive_left, naive_right) == (3, 5)
    for length in range(2, 3):
        for bound in range(3):
            h, ell = (length + 1) // 2, length // 2
            naive = (
                recurrence_collision(h, bound // 2)
                + recurrence_collision(ell, (bound + 1) // 2)
            )
            assert recurrence_collision(length, bound) == naive
    p7 = canonical_positions(7)
    assert len(p7) == 28
    assert len({block(start, 7) for start in p7}) == 28
    print("DECIMATION indices=1..4096 passed")
    print(f"PROFILE_TRANSITIONS checks={profile_checks} starts<=49 lengths=0..24 passed")
    print(f"PROFILE_COUNTS checks={count_profile_checks} lengths=0..24 M=0..96 passed")
    print(f"COLLISION_RECURRENCE checks={collision_checks} lengths=0..24 M=0..96 passed")
    print("VANISHING A_profiles lengths=4..64 M=512 passed")
    print("SANITY C(0,48)=2304 C(7,48)=98")
    print("MINIMAL_SCALAR_CLOSURE_FAILURE n=2 M=3 actual=3 naive_rhs=5")
    print("CANONICAL_TRANSVERSAL_REPLAY k=7 positions=28 distinct_factors=28")
    print("ALL_CHECKS_PASSED")


if __name__ == "__main__":
    main()
