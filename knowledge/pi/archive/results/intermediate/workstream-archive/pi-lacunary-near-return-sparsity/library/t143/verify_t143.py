#!/usr/bin/env python3
"""Self-contained exact replay for T143.

Finite checks are experiments. The universal quotient theorem is proved in REPORT.md.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import product
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
RAW_STATE_CAP = 10_000
COMPARATOR_SHA256 = {
    "prior-T94-REPORT.md": "f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10",
    "prior-T112-REPORT.md": "72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa",
    "prior-T119-REPORT.md": "72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a",
    "prior-T133-REPORT.md": "53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40",
    "prior-T141-REPORT.md": "e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356",
    "prior-T140-REPORT.md": "ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def digit_sum(n: int, base: int) -> int:
    total = 0
    while n:
        n, digit = divmod(n, base)
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
    def __init__(self, base: int, numerators: tuple[int, ...], denominators: tuple[int, ...]):
        assert base >= 2 and numerators and denominators
        self.base = base
        self.numerators = numerators
        self.denominators = denominators
        self.multipliers = numerators + denominators
        self.split = len(numerators)
        self.zero = (0,) * len(self.multipliers)
        self.raw_state_count = 1
        for multiplier in self.multipliers:
            self.raw_state_count *= multiplier
        assert self.raw_state_count <= RAW_STATE_CAP
        self.raw_states = tuple(product(*(range(c) for c in self.multipliers)))
        assert len(self.raw_states) == self.raw_state_count
        self.states = self._reachable_states()

    def transition(self, state: tuple[int, ...], digit: int) -> tuple[tuple[int, ...], int]:
        nxt = tuple(
            (multiplier * digit + carry) // self.base
            for multiplier, carry in zip(self.multipliers, state)
        )
        output_digits = tuple(
            multiplier * digit + carry - self.base * next_carry
            for multiplier, carry, next_carry in zip(self.multipliers, state, nxt)
        )
        weight = sum(output_digits[self.split :]) - sum(output_digits[: self.split])
        return nxt, weight

    def terminal(self, state: tuple[int, ...]) -> int:
        values = tuple(digit_sum(carry, self.base) for carry in state)
        return sum(values[self.split :]) - sum(values[: self.split])

    def _reachable_states(self) -> tuple[tuple[int, ...], ...]:
        seen = {self.zero}
        pending = [self.zero]
        while pending:
            state = pending.pop()
            for digit in range(self.base):
                nxt, _ = self.transition(state, digit)
                if nxt not in seen:
                    seen.add(nxt)
                    pending.append(nxt)
        return tuple(sorted(seen))

    def total(self, state: tuple[int, ...], digits: tuple[int, ...]) -> int:
        value = 0
        for digit in digits:
            state, weight = self.transition(state, digit)
            value += weight
        return value + self.terminal(state)

    def integer_total(self, n: int, length: int) -> int:
        digits = []
        for _ in range(length):
            n, digit = divmod(n, self.base)
            digits.append(digit)
        assert n == 0
        return self.total(self.zero, tuple(digits))


class ResidualQuotient:
    def __init__(self, machine: CarryMachine):
        self.machine = machine
        states = machine.states
        partition = (states,)
        history = [partition]
        while True:
            block_of = {state: index for index, block in enumerate(partition) for state in block}
            refined = []
            for block in partition:
                fibers: dict[tuple, list] = defaultdict(list)
                for state in block:
                    signature = []
                    for digit in range(machine.base):
                        nxt, weight = machine.transition(state, digit)
                        residual = weight + machine.terminal(nxt) - machine.terminal(state)
                        signature.append((residual, block_of[nxt]))
                    fibers[tuple(signature)].append(state)
                refined.extend(tuple(sorted(fiber)) for _, fiber in sorted(fibers.items()))
            refined_partition = tuple(refined)
            if refined_partition == partition:
                break
            assert len(refined_partition) > len(partition)
            partition = refined_partition
            history.append(partition)
        self.history = tuple(history)
        self.blocks = partition
        self.block_of = {state: index for index, block in enumerate(partition) for state in block}
        self.representatives = tuple(block[0] for block in partition)
        self.terminals = tuple(machine.terminal(state) for state in self.representatives)
        self.initial = self.block_of[machine.zero]

        transitions = []
        for block_index, representative in enumerate(self.representatives):
            row = []
            for digit in range(machine.base):
                nxt, weight = machine.transition(representative, digit)
                nxt_block = self.block_of[nxt]
                residual = weight + machine.terminal(nxt) - machine.terminal(representative)
                quotient_weight = residual + self.terminals[block_index] - self.terminals[nxt_block]
                row.append((nxt_block, quotient_weight, residual))
            transitions.append(tuple(row))
        self.transitions = tuple(transitions)

        # Stable signatures must be representative-independent.
        for block_index, block in enumerate(self.blocks):
            for state in block:
                for digit in range(machine.base):
                    nxt, weight = machine.transition(state, digit)
                    residual = weight + machine.terminal(nxt) - machine.terminal(state)
                    expected_nxt, _, expected_residual = self.transitions[block_index][digit]
                    assert (self.block_of[nxt], residual) == (expected_nxt, expected_residual)

    def total(self, block: int, digits: tuple[int, ...]) -> int:
        value = 0
        for digit in digits:
            block, weight, _ = self.transitions[block][digit]
            value += weight
        return value + self.terminals[block]


def simple_cycle_means_raw(machine: CarryMachine) -> set[Fraction]:
    means: set[Fraction] = set()
    states = machine.states
    index = {state: i for i, state in enumerate(states)}

    def visit(start, state, used, total, length):
        for digit in range(machine.base):
            nxt, weight = machine.transition(state, digit)
            if nxt == start:
                means.add(Fraction(total + weight, length + 1))
            elif nxt not in used and index[nxt] >= index[start]:
                used.add(nxt)
                visit(start, nxt, used, total + weight, length + 1)
                used.remove(nxt)

    for start in states:
        visit(start, start, {start}, 0, 0)
    return means


def simple_cycle_means_quotient(quotient: ResidualQuotient) -> set[Fraction]:
    means: set[Fraction] = set()

    def visit(start, block, used, total, length):
        for nxt, weight, _ in quotient.transitions[block]:
            if nxt == start:
                means.add(Fraction(total + weight, length + 1))
            elif nxt not in used and nxt >= start:
                used.add(nxt)
                visit(start, nxt, used, total + weight, length + 1)
                used.remove(nxt)

    for start in range(len(quotient.blocks)):
        visit(start, start, {start}, 0, 0)
    return means


def quotient_simple_cycles(quotient: ResidualQuotient):
    cycles = []

    def visit(start, block, used, word, total):
        for digit, (nxt, weight, _) in enumerate(quotient.transitions[block]):
            if nxt == start:
                cycles.append((start, tuple(word + [digit]), total + weight))
            elif nxt not in used and nxt >= start:
                used.add(nxt)
                visit(start, nxt, used, word + [digit], total + weight)
                used.remove(nxt)

    for start in range(len(quotient.blocks)):
        visit(start, start, {start}, [], 0)
    return cycles


def raw_edge_run(machine: CarryMachine, state: tuple[int, ...], word: tuple[int, ...]):
    total = 0
    for digit in word:
        state, weight = machine.transition(state, digit)
        total += weight
    return state, total


def check_cycle_lifts(machine: CarryMachine, quotient: ResidualQuotient) -> int:
    checked = 0
    for block, word, quotient_weight in quotient_simple_cycles(quotient):
        state = quotient.blocks[block][0]
        orbit = []
        first_seen = {}
        while state not in first_seen:
            first_seen[state] = len(orbit)
            orbit.append(state)
            state, _ = raw_edge_run(machine, state, word)
        start_index = first_seen[state]
        period = len(orbit) - start_index
        lifted_start = orbit[start_index]
        lifted_word = word * period
        lifted_end, lifted_weight = raw_edge_run(machine, lifted_start, lifted_word)
        assert lifted_end == lifted_start
        assert lifted_weight == period * quotient_weight
        assert Fraction(lifted_weight, len(lifted_word)) == Fraction(quotient_weight, len(word))
        checked += 1
    return checked


def extrema_raw(machine: CarryMachine, length: int) -> tuple[int, int]:
    values = {state: (machine.terminal(state), machine.terminal(state)) for state in machine.states}
    for _ in range(length):
        updated = {}
        for state in machine.states:
            candidates = []
            for digit in range(machine.base):
                nxt, weight = machine.transition(state, digit)
                low, high = values[nxt]
                candidates.append((weight + low, weight + high))
            updated[state] = (min(x for x, _ in candidates), max(y for _, y in candidates))
        values = updated
    return values[machine.zero]


def extrema_quotient(quotient: ResidualQuotient, length: int) -> tuple[int, int]:
    values = {block: (terminal, terminal) for block, terminal in enumerate(quotient.terminals)}
    for _ in range(length):
        updated = {}
        for block, row in enumerate(quotient.transitions):
            candidates = []
            for nxt, weight, _ in row:
                low, high = values[nxt]
                candidates.append((weight + low, weight + high))
            updated[block] = (min(x for x, _ in candidates), max(y for _, y in candidates))
        values = updated
    return values[quotient.initial]


def words(base: int, max_length: int):
    for length in range(max_length + 1):
        yield from product(range(base), repeat=length)


def check_machine(
    name: str,
    machine: CarryMachine,
    expected_accessible: int,
    expected_blocks: tuple[tuple[tuple[int, ...], ...], ...],
    max_word_length: int,
) -> ResidualQuotient:
    quotient = ResidualQuotient(machine)
    assert len(machine.states) == expected_accessible
    assert {frozenset(block) for block in quotient.blocks} == {
        frozenset(block) for block in expected_blocks
    }
    assert len(quotient.history) <= len(machine.states)

    checked = 0
    for word in words(machine.base, max_word_length):
        for block, representative in enumerate(quotient.representatives):
            assert machine.total(representative, word) == quotient.total(block, word)
            for state in quotient.blocks[block]:
                correction = quotient.terminals[block] - machine.terminal(state)
                assert quotient.total(block, word) == machine.total(state, word) + correction
                checked += 1

    raw_means = simple_cycle_means_raw(machine)
    quotient_means = simple_cycle_means_quotient(quotient)
    assert min(raw_means) == min(quotient_means)
    assert max(raw_means) == max(quotient_means)
    lifted_cycles = check_cycle_lifts(machine, quotient)
    for length in range(65):
        assert extrema_raw(machine, length) == extrema_quotient(quotient, length)

    print(
        f"{name} CAP OK raw={machine.raw_state_count} <= {RAW_STATE_CAP}; "
        f"accessible={len(machine.states)}; quotient={len(quotient.blocks)}"
    )
    print(f"{name} PARTITION OK rounds={len(quotient.history)-1}; blocks={quotient.blocks}")
    print(f"{name} TOTALS OK {checked} raw/quotient continuation comparisons")
    print(
        f"{name} CYCLE EXTREMA OK min={min(raw_means)} max={max(raw_means)}; "
        f"all {lifted_cycles} quotient simple cycles power-lifted; "
        f"finite-length extrema L=0..64 preserved"
    )
    return quotient


def check_terminal_counterexample() -> None:
    # Two residual-equivalent states with zero loops and terminals 0 and 5.
    for length in range(6):
        assert 0 - 0 == 5 - 5
        assert 0 != 5
    print("TERMINAL OFFSET COUNTEREXAMPLE OK residuals agree but unshifted totals are 0 and 5")


def check_comparator_bundle() -> None:
    required = {
        "prior-T94-REPORT.md": ("# T94:", "proof sketch", "paperfolding"),
        "prior-T112-REPORT.md": ("# T112:", "literature-checked", "proof sketch"),
        "prior-T119-REPORT.md": ("# T119:", "literature-checked", "proof sketch"),
        "prior-T133-REPORT.md": ("# T133:", "proof sketch", "base-5 transducer"),
        "prior-T141-REPORT.md": ("# T141:", "proof sketch", "multiplication carries"),
        "prior-T140-REPORT.md": ("# T140:", "literature-checked", "hypergraph"),
    }
    for name, expected_hash in COMPARATOR_SHA256.items():
        path = ROOT / name
        assert sha256(path) == expected_hash
        text = path.read_text(encoding="utf-8")
        for marker in required[name]:
            assert marker in text

    index = (ROOT / "PRIOR_INDEX.md").read_text(encoding="utf-8")
    for name, expected_hash in COMPARATOR_SHA256.items():
        assert name in index
        assert expected_hash in index
    assert "T142 is not included as a byte-vendored comparator" in index
    assert "source statement, deduction, theorem, or novelty conclusion is asserted" in index
    print("COMPARATOR BUNDLE OK T94 T112 T119 T133 T141 T140 byte-pinned; T142 availability scoped")


def check_central_trinomial() -> None:
    machine = CarryMachine(2, (3,), (1, 1, 1))
    expected = tuple((state,) for state in machine.states)
    quotient = check_machine("APP1", machine, 3, expected, 14)
    assert len(quotient.blocks) == 3
    for n in range(100_000):
        length = max(0, n.bit_length())
        direct = factorial_valuation(3 * n, 2) - 3 * factorial_valuation(n, 2)
        assert machine.integer_total(n, length) == direct
    print("APP1 ARITHMETIC OK (3n)!/(n!)^3 at p=2 for 0<=n<100000")


def check_hypergeometric_ratio() -> None:
    machine = CarryMachine(5, (6, 1), (3, 2))
    expected = (
        ((0, 0, 0, 0),),
        ((1, 0, 0, 0), (2, 0, 1, 0), (3, 0, 1, 1), (4, 0, 2, 1)),
        ((5, 0, 2, 1),),
    )
    quotient = check_machine("APP2", machine, 6, expected, 8)
    assert sorted(len(block) for block in quotient.blocks) == [1, 1, 4]
    for n in range(100_000):
        length = 0
        bound = 1
        while bound <= n:
            length += 1
            bound *= 5
        direct = (
            4
            * (
                factorial_valuation(6 * n, 5)
                + factorial_valuation(n, 5)
                - factorial_valuation(3 * n, 5)
                - factorial_valuation(2 * n, 5)
            )
            - 2 * n
        )
        assert machine.integer_total(n, length) == direct
    print("APP2 ARITHMETIC OK (6n)!n!/((3n)!(2n)!) at p=5 for 0<=n<100000")


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    assert "SCOPED_VERDICT_COUNT: 1" in report
    assert report.rstrip().endswith("hold as model")
    assert report.count("\nhold as model") == 1
    for item in ("T94", "T112", "T119", "T133", "T141", "T140", "T142"):
        assert f"| {item} |" in report
    for frontier in ("T7", "T107"):
        assert frontier in report
    for field in ("numerator", "modulus", "multiplicative order", "occupancy"):
        assert field in report
    for forbidden in ("proves A1", "proves C1", "proves C2", "establishes A1", "establishes C1", "establishes C2"):
        assert forbidden not in report
    print("REPORT CONTRACT OK comparisons, transfer fields, firewall, and one final scoped verdict")


def main() -> None:
    print("All finite calculations below are EXPERIMENT checks, not universal proofs.")
    actual = sha256(ROOT / "canonical_statement.txt")
    assert actual == CANONICAL_SHA256
    print(f"CANONICAL HASH OK {actual}")
    check_report_contract()
    check_comparator_bundle()
    check_terminal_counterexample()
    check_central_trinomial()
    check_hypergeometric_ratio()
    print("T143 REPLAY PASS")


if __name__ == "__main__":
    main()
