#!/usr/bin/env python3
"""Self-contained exact replay for the T101 paperfolding note.

All finite sweeps are transcription experiments.  The universal argument is
the numbered proof in REPORT.md.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path


EXPECTED_CANONICAL_SHA256 = (
    "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
)


def paperfolding(index: int) -> int:
    assert index >= 1
    while index % 2 == 0:
        index //= 2
    return ((index - 1) // 2) % 2


def factor(start: int, length: int) -> tuple[int, ...]:
    return tuple(paperfolding(start + offset) for offset in range(length))


def alternating(first: int, length: int) -> tuple[int, ...]:
    return tuple((first + offset) % 2 for offset in range(length))


def counts(length: int, cutoff: int) -> Counter[tuple[int, ...]]:
    return Counter(factor(start, length) for start in range(1, cutoff + 1))


def energy(length: int, cutoff: int) -> int:
    return sum(value * value for value in counts(length, cutoff).values())


def same_parity_energy_direct(length: int, cutoff: int) -> int:
    total = 0
    for start in range(1, cutoff + 1):
        left = factor(start, length)
        for other in range(1, cutoff + 1):
            if start % 2 == other % 2 and left == factor(other, length):
                total += 1
    return total


def ones_dyadic(exponent: int) -> int:
    if exponent == 0:
        return paperfolding(1)
    return 2 ** (exponent - 1) - 1


def energy_one_dyadic(exponent: int) -> int:
    one = ones_dyadic(exponent)
    zero = 2**exponent - one
    return one * one + zero * zero


def same_parity_recurrence(length: int, cutoff: int) -> int:
    if cutoff == 0:
        return 0
    even = cutoff // 2
    odd = cutoff - even
    if length == 0:
        return even * even + odd * odd
    if length == 1:
        odd_zero = (odd + 1) // 2
        odd_one = odd // 2
        return energy(1, even) + odd_zero * odd_zero + odd_one * odd_one
    high = (length + 1) // 2
    low = length // 2
    return same_parity_recurrence(high, even) + same_parity_recurrence(low, odd)


def exact_dyadic_energy(length: int, exponent: int) -> int:
    assert exponent >= 7 and 7 <= length <= exponent
    r = length.bit_length() - 1
    q = 2**r
    scale = 4 ** (exponent - r - 2)
    return (6 * q - 2 * length) * scale + 2 * length


def split_energy(length: int, cutoff: int, eta: Fraction) -> int:
    parent = counts(length, cutoff)
    child = counts(length + 1, cutoff)
    result = 0
    for word, value in parent.items():
        left = child[word + (0,)]
        right = child[word + (1,)]
        if left >= eta * value and right >= eta * value:
            result += value * value
    return result


def check_canonical() -> None:
    payload = Path("canonical_statement.txt").read_bytes()
    actual = sha256(payload).hexdigest()
    assert actual == EXPECTED_CANONICAL_SHA256, (actual, EXPECTED_CANONICAL_SHA256)
    print(f"canonical_sha256={actual}")


def check_symbol_and_profiles() -> int:
    checks = 0
    for a in range(1, 1025):
        assert paperfolding(2 * a) == paperfolding(a)
        assert paperfolding(2 * a + 1) == a % 2
        checks += 2

    for length in range(0, 18):
        high = (length + 1) // 2
        low = length // 2
        for a in range(1, 18):
            expected_even = tuple(
                value
                for pair in zip(factor(a, high), alternating(a % 2, low))
                for value in pair
            )
            if high > low:
                expected_even += factor(a, high)[-1:]
            assert factor(2 * a, length) == expected_even
            checks += 1
        for a in range(0, 18):
            expected_odd = tuple(
                value
                for pair in zip(alternating(a % 2, high), factor(a + 1, low))
                for value in pair
            )
            if high > low:
                expected_odd += alternating(a % 2, high)[-1:]
            assert factor(2 * a + 1, length) == expected_odd
            checks += 1

    for length in range(0, 14):
        high = (length + 1) // 2
        low = length // 2
        for start in range(1, 25):
            for other in range(1, 25):
                lhs = factor(start, length) == factor(other, length)
                if start % 2 == 0 and other % 2 == 0:
                    a, b = start // 2, other // 2
                    rhs = factor(a, high) == factor(b, high) and (
                        low == 0 or a % 2 == b % 2
                    )
                elif start % 2 == 1 and other % 2 == 1:
                    a, b = (start - 1) // 2, (other - 1) // 2
                    rhs = (high == 0 or a % 2 == b % 2) and (
                        factor(a + 1, low) == factor(b + 1, low)
                    )
                elif start % 2 == 0:
                    a, b = start // 2, (other - 1) // 2
                    rhs = factor(a, high) == alternating(b % 2, high) and (
                        factor(b + 1, low) == alternating(a % 2, low)
                    )
                else:
                    a, b = (start - 1) // 2, other // 2
                    rhs = factor(b, high) == alternating(a % 2, high) and (
                        factor(a + 1, low) == alternating(b % 2, low)
                    )
                assert lhs == rhs, (length, start, other, lhs, rhs)
                checks += 1

    for start in range(1, 2049):
        for first in (0, 1):
            assert factor(start, 4) != alternating(first, 4)
            checks += 1
    print(f"symbol_and_profile_checks={checks}")
    return checks


def check_same_parity_recurrence() -> int:
    checks = 0
    for length in range(0, 15):
        for cutoff in range(0, 65):
            direct = same_parity_energy_direct(length, cutoff)
            recurrent = same_parity_recurrence(length, cutoff)
            assert direct == recurrent, (length, cutoff, direct, recurrent)
            checks += 1
    for exponent in range(2, 15):
        cutoff = 2**exponent
        assert ones_dyadic(exponent) == sum(
            paperfolding(start) for start in range(1, cutoff + 1)
        )
        assert energy_one_dyadic(exponent) == energy(1, cutoff)
        assert same_parity_recurrence(1, cutoff) == 4 ** (exponent - 1) + 2
        checks += 3
    print(f"same_parity_recurrence_checks={checks}")
    return checks


def check_exact_formula_and_drop() -> int:
    checks = 0
    for exponent in range(7, 15):
        cutoff = 2**exponent
        for length in range(7, exponent + 1):
            direct = energy(length, cutoff)
            recurrent = same_parity_recurrence(length, cutoff)
            formula = exact_dyadic_energy(length, exponent)
            assert direct == recurrent == formula, (
                exponent,
                length,
                direct,
                recurrent,
                formula,
            )
            checks += 1
        for length in range(7, exponent):
            r = length.bit_length() - 1
            scale = 4 ** (exponent - r - 2)
            assert energy(length, cutoff) - energy(length + 1, cutoff) == 2 * (
                scale - 1
            )
            checks += 1
    print(f"exact_formula_and_drop_checks={checks}")
    return checks


def check_successor_identity_and_bounds() -> int:
    checks = 0
    parameters = (
        (Fraction(1, 10), Fraction(1, 10)),
        (Fraction(1, 20), Fraction(1, 4)),
        (Fraction(1, 100), Fraction(1, 2)),
    )
    for exponent in range(7, 14):
        cutoff = 2**exponent
        for length in range(0, exponent):
            parent = counts(length, cutoff)
            child = counts(length + 1, cutoff)
            cross = sum(
                child[word + (0,)] * child[word + (1,)] for word in parent
            )
            assert energy(length, cutoff) - energy(length + 1, cutoff) == 2 * cross
            checks += 1
        for mu, eta in parameters:
            for length in range(7, exponent):
                parent_energy = energy(length, cutoff)
                selected = split_energy(length, cutoff, eta)
                drop = parent_energy - energy(length + 1, cutoff)
                assert 2 * eta * (1 - eta) * selected <= drop
                assert Fraction(selected, parent_energy) < Fraction(
                    1, 1
                ) / (length * eta * (1 - eta))
                if mu * parent_energy <= selected:
                    assert length < Fraction(1, 1) / (mu * eta * (1 - eta))
                checks += 3
    print(f"successor_identity_and_bound_checks={checks}")
    return checks


def check_minimal_scalar_failure() -> None:
    failures = []
    for length in range(2, 9):
        high = (length + 1) // 2
        low = length // 2
        for cutoff in range(0, 17):
            rhs = energy(high, cutoff // 2) + energy(low, cutoff - cutoff // 2)
            if energy(length, cutoff) != rhs:
                failures.append((length, cutoff, energy(length, cutoff), rhs))
    assert failures[0] == (2, 3, 3, 5), failures[0]
    assert all(
        energy(2, cutoff)
        == energy(1, cutoff // 2) + energy(1, cutoff - cutoff // 2)
        for cutoff in range(0, 3)
    )
    print("minimal_scalar_closure_failure=(n=2,M=3,left=3,right=5)")


def main() -> None:
    check_canonical()
    total = 0
    total += check_symbol_and_profiles()
    total += check_same_parity_recurrence()
    total += check_exact_formula_and_drop()
    total += check_successor_identity_and_bounds()
    check_minimal_scalar_failure()
    print(f"total_exact_checks={total}")
    print("finite_replay_status=PASS (experiment; universal proof is REPORT.md)")


if __name__ == "__main__":
    main()
