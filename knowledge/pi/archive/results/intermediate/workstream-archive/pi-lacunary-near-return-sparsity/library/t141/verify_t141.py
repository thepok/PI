#!/usr/bin/env python3
"""Self-contained exact replay for T141.

Every finite check is validation only. Universal claims rest on REPORT.md.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
STATE_CAP = 100_000
CHECK_LIMIT = 1_000_000


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def digit_sum(n: int, p: int) -> int:
    total = 0
    while n:
        n, digit = divmod(n, p)
        total += digit
    return total


def factorial_valuation(n: int, p: int) -> int:
    total = 0
    power = p
    while power <= n:
        total += n // power
        power *= p
    return total


class CarryMachine:
    def __init__(self, p: int, numerators: tuple[int, ...], denominators: tuple[int, ...]):
        self.p = p
        self.a = numerators
        self.b = denominators
        self.multipliers = self.a + self.b
        self.split = len(self.a)
        self.zero = (0,) * len(self.multipliers)
        self.states = self._reachable_states()
        assert len(self.states) <= STATE_CAP

    def transition(self, state: tuple[int, ...], digit: int) -> tuple[tuple[int, ...], int]:
        nxt = tuple((c * digit + carry) // self.p for c, carry in zip(self.multipliers, state))
        output_digits = tuple(
            c * digit + carry - self.p * next_carry
            for c, carry, next_carry in zip(self.multipliers, state, nxt)
        )
        weight = sum(output_digits[self.split :]) - sum(output_digits[: self.split])
        return nxt, weight

    def terminal(self, state: tuple[int, ...]) -> int:
        sums = tuple(digit_sum(carry, self.p) for carry in state)
        return sum(sums[self.split :]) - sum(sums[: self.split])

    def _reachable_states(self) -> tuple[tuple[int, ...], ...]:
        seen = {self.zero}
        frontier = [self.zero]
        while frontier:
            state = frontier.pop()
            for digit in range(self.p):
                nxt, _ = self.transition(state, digit)
                if nxt not in seen:
                    seen.add(nxt)
                    assert len(seen) <= STATE_CAP
                    frontier.append(nxt)
        return tuple(sorted(seen))

    def run(self, n: int, length: int) -> int:
        assert 0 <= n < self.p**length
        state = self.zero
        total = 0
        for _ in range(length):
            n, digit = divmod(n, self.p)
            state, weight = self.transition(state, digit)
            total += weight
        return total + self.terminal(state)

    def extrema(self, length: int) -> tuple[int, int]:
        values = {state: (self.terminal(state), self.terminal(state)) for state in self.states}
        for _ in range(length):
            updated = {}
            for state in self.states:
                continuations = []
                for digit in range(self.p):
                    nxt, weight = self.transition(state, digit)
                    low, high = values[nxt]
                    continuations.append((weight + low, weight + high))
                updated[state] = (
                    min(value[0] for value in continuations),
                    max(value[1] for value in continuations),
                )
            values = updated
        return values[self.zero]


def simple_cycles(machine: CarryMachine) -> list[tuple[tuple[int, ...], Fraction]]:
    """Enumerate directed simple cycles, retaining parallel digit cycles."""
    cycles: list[tuple[tuple[int, ...], Fraction]] = []
    states = machine.states
    index = {state: i for i, state in enumerate(states)}

    def visit(start, current, path, weights):
        for digit in range(machine.p):
            nxt, weight = machine.transition(current, digit)
            if nxt == start:
                cycles.append((tuple(path + [digit]), Fraction(sum(weights) + weight, len(weights) + 1)))
            elif nxt not in path_states and index[nxt] >= index[start]:
                path_states.add(nxt)
                visit(start, nxt, path + [digit], weights + [weight])
                path_states.remove(nxt)

    # Restrict start to the least-index vertex on a cycle, avoiding rotations.
    for start in states:
        path_states = {start}
        visit(start, start, [], [])
    return cycles


def direct_value(n: int) -> int:
    return factorial_valuation(3 * n, 2) - 3 * factorial_valuation(n, 2)


def digit_value(n: int) -> int:
    return 3 * digit_sum(n, 2) - digit_sum(3 * n, 2)


def digits_needed(n: int, p: int) -> int:
    length = 0
    bound = 1
    while bound <= n:
        bound *= p
        length += 1
    return length


def main() -> None:
    print("All finite calculations below are EXPERIMENT validation, not universal proofs.")
    actual_hash = sha256(ROOT / "canonical_statement.txt")
    assert actual_hash == CANONICAL_SHA256
    print(f"CANONICAL HASH OK {actual_hash}")

    machine = CarryMachine(2, (3,), (1, 1, 1))
    expected_states = ((0, 0, 0, 0), (1, 0, 0, 0), (2, 0, 0, 0))
    assert machine.states == expected_states
    print(f"REACHABLE STATES OK {len(machine.states)} <= {STATE_CAP}: {machine.states}")

    expected = {
        (0, 0): (0, 0),
        (0, 1): (1, 2),
        (1, 0): (0, -1),
        (1, 1): (2, 3),
        (2, 0): (1, 0),
        (2, 1): (2, 2),
    }
    expected_terminal = {0: 0, 1: -1, 2: -1}
    for state in machine.states:
        carry = state[0]
        assert machine.terminal(state) == expected_terminal[carry]
        for digit in range(2):
            nxt, weight = machine.transition(state, digit)
            assert (nxt[0], weight) == expected[(carry, digit)]
    print("TRANSITIONS/TERMINALS OK all 6 transitions and 3 terminal weights")

    cycles = simple_cycles(machine)
    means = sorted({mean for _, mean in cycles})
    assert means == [Fraction(0), Fraction(1, 2), Fraction(3, 2), Fraction(2)]
    print("ACCESSIBLE SIMPLE CYCLE MEANS OK 0, 1/2, 3/2, 2; min=0 max=2")

    for length in range(0, 65):
        low, high = machine.extrema(length)
        expected_high = 0 if length == 0 else 1 if length == 1 else 2 * length
        assert (low, high) == (0, expected_high)
    for length in range(0, 17):
        values = [machine.run(n, length) for n in range(2**length)]
        assert (min(values), max(values)) == machine.extrema(length)
    print("TROPICAL EXTREMA OK symbolic DP L=0..64; exhaustive digit words L=0..16")

    for n in range(CHECK_LIMIT):
        length = digits_needed(n, 2)
        floor_value = direct_value(n)
        sum_value = digit_value(n)
        machine_value = machine.run(n, length)
        assert floor_value == sum_value == machine_value, (n, floor_value, sum_value, machine_value)
    print(f"EXACT REPLAY OK valuation=digit-sum=transducer for every 0<=n<{CHECK_LIMIT}")
    print("T141 REPLAY PASS")


if __name__ == "__main__":
    main()
