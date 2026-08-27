#!/usr/bin/env python3
"""Exact finite checks for the T35 single-stream de Bruijn construction."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


BASE = 10
EXPECTED_STATEMENT_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def de_bruijn(base: int, order: int) -> tuple[int, ...]:
    """FKM prefer-min cyclic de Bruijn word for the given alphabet and order."""
    assert base >= 2 and order >= 1
    work = [0] * (base * order + 1)
    sequence: list[int] = []

    def visit(t: int, period: int) -> None:
        if t > order:
            if order % period == 0:
                sequence.extend(work[1 : period + 1])
            return
        work[t] = work[t - period]
        visit(t + 1, period)
        for digit in range(work[t - period] + 1, base):
            work[t] = digit
            visit(t + 1, t)

    visit(1, 1)
    result = tuple(sequence)
    assert len(result) == base**order
    return result


def cyclic_factor(cycle: tuple[int, ...], phase: int, length: int) -> tuple[int, ...]:
    size = len(cycle)
    return tuple(cycle[(phase + offset) % size] for offset in range(length))


def factor_counts(
    stream: list[int], start_count: int, length: int, first_start: int = 0
) -> Counter[tuple[int, ...]]:
    assert 0 <= first_start <= start_count
    assert start_count + max(length - 1, 0) <= len(stream)
    return Counter(
        tuple(stream[start : start + length])
        for start in range(first_start, start_count)
    )


def contained_counts(prefix: list[int], length: int) -> Counter[tuple[int, ...]]:
    if length > len(prefix):
        return Counter()
    return Counter(
        tuple(prefix[start : start + length])
        for start in range(len(prefix) - length + 1)
    )


def all_relevant_parents(
    parents: Counter[tuple[int, ...]], children: Counter[tuple[int, ...]]
) -> set[tuple[int, ...]]:
    return set(parents) | {child[:-1] for child in children} | {
        child[1:] for child in children
    }


def verify_de_bruijn(cycle: tuple[int, ...], order: int) -> None:
    factors = [cyclic_factor(cycle, phase, order) for phase in range(len(cycle))]
    assert len(set(factors)) == BASE**order


def build_stream(max_order: int):
    stream: list[int] = []
    stages: list[dict[str, object]] = []
    for order in range(1, max_order + 1):
        cycle = de_bruijn(BASE, order)
        verify_de_bruijn(cycle, order)
        stage_start = len(stream)
        repetitions = order**3 * (stage_start + 1)
        start_checkpoint = stage_start + repetitions * len(cycle)
        prefix_checkpoint = start_checkpoint + 2 * order
        stream.extend(cycle * (repetitions + 1))
        assert prefix_checkpoint < len(stream)
        stages.append(
            {
                "order": order,
                "cycle": cycle,
                "A": stage_start,
                "R": repetitions,
                "L": len(cycle),
                "N": start_checkpoint,
                "K": prefix_checkpoint,
            }
        )
    return stream, stages


def verify_first_start_identities(
    stream: list[int], stage: dict[str, object]
) -> dict[str, int]:
    order = int(stage["order"])
    start_count = int(stage["N"])
    counts = {
        length: factor_counts(stream, start_count, length)
        for length in range(2 * order + 1)
    }
    identities = 0
    for length in range(2 * order):
        parents = counts[length]
        children = counts[length + 1]
        assert sum(parents.values()) == start_count
        for word in all_relevant_parents(parents, children):
            outgoing = sum(children[word + (digit,)] for digit in range(BASE))
            incoming = sum(children[(digit,) + word] for digit in range(BASE))
            at_zero = int(tuple(stream[0:length]) == word)
            at_end = int(tuple(stream[start_count : start_count + length]) == word)
            assert outgoing == parents[word]
            assert incoming + at_zero == parents[word] + at_end
            assert outgoing - incoming == at_zero - at_end
            identities += 3
    assert sum(counts[2 * order].values()) == start_count
    return {"first_start_identity_checks": identities}


def verify_contained_boundaries(
    stream: list[int], stage: dict[str, object]
) -> dict[str, int]:
    order = int(stage["order"])
    prefix = stream[: int(stage["K"])]
    counts = {
        length: contained_counts(prefix, length)
        for length in range(1, 2 * order + 1)
    }
    identities = 0
    for length in range(1, 2 * order):
        parents = counts[length]
        children = counts[length + 1]
        prefix_word = tuple(prefix[:length])
        suffix_word = tuple(prefix[-length:])
        for word in all_relevant_parents(parents, children) | {
            prefix_word,
            suffix_word,
        }:
            outgoing = sum(children[word + (digit,)] for digit in range(BASE))
            incoming = sum(children[(digit,) + word] for digit in range(BASE))
            right_loss = int(word == suffix_word)
            left_loss = int(word == prefix_word)
            assert outgoing == parents[word] - right_loss
            assert incoming == parents[word] - left_loss
            assert outgoing - incoming == left_loss - right_loss
            identities += 3
    return {"contained_boundary_checks": identities}


def verify_stage(stream: list[int], stage: dict[str, object]) -> dict[str, object]:
    order = int(stage["order"])
    cycle = tuple(stage["cycle"])
    stage_start = int(stage["A"])
    repetitions = int(stage["R"])
    cycle_length = int(stage["L"])
    start_count = int(stage["N"])

    energies: dict[str, int] = {}
    leakages: dict[str, int] = {}
    leakage_bound = 2 * repetitions * stage_start + stage_start**2
    total_leakage = 0

    for length in range(order, 2 * order + 1):
        counts = factor_counts(stream, start_count, length)
        errors = factor_counts(stream, stage_start, length)
        assert sum(errors.values()) == stage_start

        successor: dict[tuple[int, ...], int] = {}
        for phase in range(cycle_length):
            word = cyclic_factor(cycle, phase, length)
            digit = cycle[(phase + length) % cycle_length]
            assert word not in successor
            successor[word] = digit
        assert len(successor) == cycle_length

        for word in set(counts) | set(errors) | set(successor):
            expected = errors[word] + (repetitions if word in successor else 0)
            assert counts[word] == expected

        energy = sum(value * value for value in counts.values())
        energies[str(length)] = energy
        assert energy >= cycle_length * repetitions**2

        if length < 2 * order:
            child_counts = factor_counts(stream, start_count, length + 1)
            retained = 0
            for word, digit in successor.items():
                child = word + (digit,)
                assert child_counts[child] <= counts[word]
                assert child_counts[child] >= repetitions
                assert child_counts[child] * (repetitions + stage_start) >= (
                    repetitions * counts[word]
                )
                retained += child_counts[child] ** 2
            leakage = energy - retained
            assert 0 <= leakage <= leakage_bound
            leakages[str(length)] = leakage
            total_leakage += leakage

    start_energy = energies[str(order)]
    assert total_leakage * cycle_length * repetitions**2 <= (
        order * leakage_bound * start_energy
    )

    root = cyclic_factor(cycle, 0, order)
    for offset in range(order):
        parent = cyclic_factor(cycle, 0, order + offset)
        child = cyclic_factor(cycle, 0, order + offset + 1)
        parent_count = factor_counts(stream, start_count, len(parent))[parent]
        child_count = factor_counts(stream, start_count, len(child))[child]
        assert parent[:order] == root
        assert child[:-1] == parent
        assert child_count * (repetitions + stage_start) >= repetitions * parent_count

    shallow_max = Fraction(0)
    shallow_checks = 0
    for length in range(order):
        parents = factor_counts(stream, start_count, length)
        children = factor_counts(stream, start_count, length + 1)
        for word, parent_count in parents.items():
            assert parent_count > 0
            for digit in range(BASE):
                ratio = Fraction(children[word + (digit,)], parent_count)
                shallow_max = max(shallow_max, ratio)
                assert 2 * children[word + (digit,)] < parent_count
                shallow_checks += 1

    for length in range(order + 1):
        counts = factor_counts(stream, start_count, length)
        for value in counts.values():
            assert abs(BASE**length * value - start_count) <= BASE**length * stage_start

    result: dict[str, object] = {
        "order": order,
        "A": stage_start,
        "R": repetitions,
        "L": cycle_length,
        "N": start_count,
        "K": int(stage["K"]),
        "alpha_lower_bound": f"{repetitions}/{repetitions + stage_start}",
        "energies": energies,
        "leakages": leakages,
        "total_window_leakage": total_leakage,
        "leakage_upper_bound_per_level": leakage_bound,
        "normalized_leakage": f"{total_leakage}/{start_energy}",
        "shallow_half_dominant_edges_checked": shallow_checks,
        "largest_shallow_child_ratio": f"{shallow_max.numerator}/{shallow_max.denominator}",
    }
    result.update(verify_first_start_identities(stream, stage))
    result.update(verify_contained_boundaries(stream, stage))
    return result


def verify_checkpoint_compatibility(
    stream: list[int], stages: list[dict[str, object]]
) -> int:
    checks = 0
    for previous, current in zip(stages, stages[1:]):
        old_count = int(previous["N"])
        new_count = int(current["N"])
        max_length = 2 * int(previous["order"])
        for length in range(max_length + 1):
            old = factor_counts(stream, old_count, length)
            new = factor_counts(stream, new_count, length)
            increment = factor_counts(stream, new_count, length, old_count)
            for word in set(old) | set(new) | set(increment):
                assert new[word] == old[word] + increment[word]
                checks += 1
    return checks


def statement_hash() -> str:
    statement = Path(__file__).resolve().with_name("canonical_statement.txt")
    if not statement.is_file():
        raise FileNotFoundError(f"artifact-local canonical statement not found: {statement}")
    packaged = statement.read_bytes()
    # The packaged text carries one terminal LF; the immutable source has none.
    # Remove exactly that transport byte before checking the source bytes.
    assert packaged.endswith(b"\n") and not packaged.endswith(b"\n\n")
    digest = hashlib.sha256(packaged[:-1]).hexdigest()
    assert digest == EXPECTED_STATEMENT_SHA256
    return digest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-order", type=int, default=2, choices=(1, 2))
    args = parser.parse_args()

    stream, stages = build_stream(args.max_order)
    for left, right in zip(stages, stages[1:]):
        assert (
            int(left["N"])
            < int(left["K"])
            < int(right["A"])
            < int(right["N"])
            < int(right["K"])
        )

    output = {
        "label": "experiment: exact finite checks, not a proof of universal claims",
        "canonical_statement_sha256": statement_hash(),
        "base": BASE,
        "max_order": args.max_order,
        "generated_digits": len(stream),
        "checkpoint_compatibility_checks": verify_checkpoint_compatibility(stream, stages),
        "stages": [verify_stage(stream, stage) for stage in stages],
        "status": "all exact checks passed",
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
