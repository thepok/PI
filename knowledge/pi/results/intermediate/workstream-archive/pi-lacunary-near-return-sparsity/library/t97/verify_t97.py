#!/usr/bin/env python3
"""Exact replay checks for T97's regular-paperfolding proof sketch.

Finite checks test transcription and falsify bad recurrences.  They are not a
proof of the universal claims in REPORT.md.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
SPEC = json.loads((ROOT / "recurrence_spec.json").read_text())


def paperfolding_digit(index: int) -> int:
    assert index >= 1
    while index % 2 == 0:
        index //= 2
    return ((index - 1) // 2) % 2


def block(start: int, length: int) -> tuple[int, ...]:
    assert start >= 1 and length >= 0
    return tuple(paperfolding_digit(i) for i in range(start, start + length))


def alternating(first: int, length: int) -> tuple[int, ...]:
    return tuple(first ^ (offset & 1) for offset in range(length))


def eta(left: int, right: int, length: int) -> bool:
    return length == 0 or left == right


def gamma(first: int, constant: int, length: int) -> bool:
    return length == 0 or (length == 1 and first == constant)


def profile_e(left: int, right: int, length: int) -> bool:
    return block(left, length) == block(right, length)


def profile_a(start: int, first: int, length: int) -> bool:
    return block(start, length) == alternating(first, length)


def profile_k(start: int, value: int, length: int) -> bool:
    return block(start, length) == (value,) * length


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
    count_one = ones(bound)
    return count_one**2 + (bound - count_one) ** 2


@lru_cache(maxsize=None)
def a_count(parity: int, first: int, length: int, bound: int) -> int:
    if bound == 0:
        return 0
    if length == 0:
        return parity_count(parity, bound)
    h, ell = (length + 1) // 2, length // 2
    if parity == 0:
        return sum(
            k_count(q, first, h, bound // 2)
            for q in (0, 1)
            if gamma(q, 1 - first, ell)
        )
    return sum(
        k_count(1 - q, 1 - first, ell, (bound + 1) // 2)
        for q in (0, 1)
        if gamma(q, first, h)
    )


@lru_cache(maxsize=None)
def k_count(parity: int, value: int, length: int, bound: int) -> int:
    if bound == 0:
        return 0
    if length == 0:
        return parity_count(parity, bound)
    h, ell = (length + 1) // 2, length // 2
    if parity == 0:
        return sum(
            k_count(q, value, h, bound // 2)
            for q in (0, 1)
            if gamma(q, value, ell)
        )
    return sum(
        k_count(1 - q, value, ell, (bound + 1) // 2)
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
    if bound == 0:
        return 0
    h, ell = (length + 1) // 2, length // 2
    even_bound = bound // 2
    odd_bound = (bound + 1) // 2
    return sum(
        a_count(r, 1 - q, h, even_bound) * a_count(q, r, ell, odd_bound)
        for r in (0, 1)
        for q in (0, 1)
    )


@lru_cache(maxsize=None)
def recurrence_collision(length: int, bound: int) -> int:
    if length == 0:
        return bound * bound
    return (
        same_parity_collision(length, bound)
        + 2 * mixed_orientation_collision(length, bound)
    )


def literal_collision(length: int, bound: int) -> int:
    multiplicities = Counter(block(start, length) for start in range(1, bound + 1))
    return sum(value * value for value in multiplicities.values())


def check_spec_inventory() -> None:
    assert SPEC["scope"] == "regular paperfolding only"
    assert SPEC["profiles"] == ["E", "A0", "A1", "K0", "K1"]
    assert SPEC["guards"] == {
        "eta(c,d,m)": "m=0 or c=d",
        "gamma(c,d,m)": "m=0 or (m=1 and c=d)",
    }
    assert SPEC["length_split"] == "h=ceil(n/2), l=floor(n/2)"
    assert SPEC["base"] == "At n=0 every E, A0, A1, K0, K1 predicate is true"
    rows = SPEC["rows"]
    assert rows == [
        {"state": "E", "parities": [0, 0], "domain": "a>=1,b>=1", "rhs": "E(a,b,h) and eta(a%2,b%2,l)"},
        {"state": "E", "parities": [1, 1], "domain": "a>=0,b>=0", "rhs": "eta(a%2,b%2,h) and E(a+1,b+1,l)"},
        {"state": "E", "parities": [0, 1], "domain": "a>=1,b>=0", "rhs": "A[b%2](a,h) and A[a%2](b+1,l)"},
        {"state": "E", "parities": [1, 0], "domain": "a>=0,b>=1", "rhs": "A[a%2](b,h) and A[b%2](a+1,l)"},
        {"state": "A0", "parities": [0], "domain": "a>=1", "rhs": "K0(a,h) and gamma(a%2,1,l)"},
        {"state": "A0", "parities": [1], "domain": "a>=0", "rhs": "gamma(a%2,0,h) and K1(a+1,l)"},
        {"state": "A1", "parities": [0], "domain": "a>=1", "rhs": "K1(a,h) and gamma(a%2,0,l)"},
        {"state": "A1", "parities": [1], "domain": "a>=0", "rhs": "gamma(a%2,1,h) and K0(a+1,l)"},
        {"state": "K0", "parities": [0], "domain": "a>=1", "rhs": "K0(a,h) and gamma(a%2,0,l)"},
        {"state": "K0", "parities": [1], "domain": "a>=0", "rhs": "gamma(a%2,0,h) and K0(a+1,l)"},
        {"state": "K1", "parities": [0], "domain": "a>=1", "rhs": "K1(a,h) and gamma(a%2,1,l)"},
        {"state": "K1", "parities": [1], "domain": "a>=0", "rhs": "gamma(a%2,1,h) and K1(a+1,l)"},
    ]
    assert SPEC["diagonal_theorem"] == (
        "For k>=7 and r=floor(log2(k)), "
        "C(k,2^k)=(3*2^(r+1)-2k)*4^(k-r-2)+2k"
    )


def check_decimation(max_index: int) -> int:
    checks = 0
    for a in range(1, max_index + 1):
        assert paperfolding_digit(2 * a) == paperfolding_digit(a)
        checks += 1
    for a in range(max_index + 1):
        assert paperfolding_digit(2 * a + 1) == a % 2
        checks += 1
    return checks


def check_profile_rows(max_a: int, max_length: int) -> int:
    checks = 0
    for length in range(max_length + 1):
        h, ell = (length + 1) // 2, length // 2
        for a in range(max_a + 1):
            for b in range(max_a + 1):
                if a >= 1 and b >= 1:
                    lhs = profile_e(2 * a, 2 * b, length)
                    rhs = profile_e(a, b, h) and eta(a % 2, b % 2, ell)
                    assert lhs == rhs
                    checks += 1
                lhs = profile_e(2 * a + 1, 2 * b + 1, length)
                rhs = eta(a % 2, b % 2, h) and profile_e(a + 1, b + 1, ell)
                assert lhs == rhs
                checks += 1
                if a >= 1:
                    lhs = profile_e(2 * a, 2 * b + 1, length)
                    rhs = profile_a(a, b % 2, h) and profile_a(b + 1, a % 2, ell)
                    assert lhs == rhs
                    checks += 1
                if b >= 1:
                    lhs = profile_e(2 * a + 1, 2 * b, length)
                    rhs = profile_a(b, a % 2, h) and profile_a(a + 1, b % 2, ell)
                    assert lhs == rhs
                    checks += 1
            for value in (0, 1):
                if a >= 1:
                    assert profile_a(2 * a, value, length) == (
                        profile_k(a, value, h)
                        and gamma(a % 2, 1 - value, ell)
                    )
                    assert profile_k(2 * a, value, length) == (
                        profile_k(a, value, h)
                        and gamma(a % 2, value, ell)
                    )
                    checks += 2
                assert profile_a(2 * a + 1, value, length) == (
                    gamma(a % 2, value, h)
                    and profile_k(a + 1, 1 - value, ell)
                )
                assert profile_k(2 * a + 1, value, length) == (
                    gamma(a % 2, value, h)
                    and profile_k(a + 1, value, ell)
                )
                checks += 2
    return checks


def check_profile_counts(max_length: int, max_bound: int) -> int:
    checks = 0
    for length in range(max_length + 1):
        for bound in range(max_bound + 1):
            for parity in (0, 1):
                starts = [s for s in range(1, bound + 1) if s % 2 == parity]
                for value in (0, 1):
                    direct_a = sum(profile_a(s, value, length) for s in starts)
                    direct_k = sum(profile_k(s, value, length) for s in starts)
                    assert a_count(parity, value, length, bound) == direct_a
                    assert k_count(parity, value, length, bound) == direct_k
                    checks += 2
    return checks


def check_collision_counts(max_length: int, max_bound: int) -> int:
    checks = 0
    for length in range(max_length + 1):
        for bound in range(max_bound + 1):
            assert recurrence_collision(length, bound) == literal_collision(length, bound)
            checks += 1
    return checks


def split_lengths(length: int, depth: int) -> Counter[int]:
    leaves = Counter({length: 1})
    for _ in range(depth):
        next_leaves: Counter[int] = Counter()
        for value, multiplicity in leaves.items():
            next_leaves[(value + 1) // 2] += multiplicity
            next_leaves[value // 2] += multiplicity
        leaves = next_leaves
    return leaves


def diagonal_formula(k: int) -> int:
    assert k >= 7
    r = k.bit_length() - 1
    return (3 * 2 ** (r + 1) - 2 * k) * 4 ** (k - r - 2) + 2 * k


def normalized_formula(k: int) -> Fraction:
    return Fraction(k * diagonal_formula(k), 4**k)


def check_diagonal_formula(max_k: int) -> int:
    checks = 0
    for k in range(7, max_k + 1):
        r = k.bit_length() - 1
        leaves = split_lengths(k, r)
        expected = Counter({1: 2 ** (r + 1) - k, 2: k - 2**r})
        assert leaves == +expected
        assert same_parity_collision(k, 2**k) == diagonal_formula(k)
        x = Fraction(k, 2**r)
        rhs = x * (3 - x) / 8 + Fraction(2 * k * k, 4**k)
        assert normalized_formula(k) == rhs
        assert Fraction(1, 4) + Fraction(2 * k * k, 4**k) <= rhs
        assert rhs <= Fraction(9, 32) + Fraction(2 * k * k, 4**k)
        checks += 1
    return checks


def main() -> None:
    canonical_hash = sha256((ROOT / "canonical_statement.txt").read_bytes()).hexdigest()
    assert canonical_hash == CANONICAL_SHA256
    print(f"CANONICAL sha256={canonical_hash}")

    check_spec_inventory()
    print("PROFILE_INVENTORY states=5 rows=12 complete=yes domains=explicit")

    decimation_checks = check_decimation(4096)
    profile_checks = check_profile_rows(max_a=24, max_length=24)
    count_checks = check_profile_counts(max_length=24, max_bound=96)
    collision_checks = check_collision_counts(max_length=24, max_bound=96)
    assert all(
        not profile_a(start, first, length)
        for start in range(1, 513)
        for first in (0, 1)
        for length in range(4, 17)
    )
    diagonal_checks = check_diagonal_formula(256)

    print(f"DECIMATION checks={decimation_checks} passed")
    print(f"PROFILE_ROWS checks={profile_checks} lengths=0..24 passed")
    print(f"PROFILE_COUNTS checks={count_checks} lengths=0..24 M=0..96 passed")
    print(f"COLLISION_COUNTS checks={collision_checks} lengths=0..24 M=0..96 passed")
    print("ALTERNATING_VANISHING starts=1..512 lengths=4..16 passed")
    print(f"DIAGONAL_FORMULA checks={diagonal_checks} k=7..256 passed")
    print(f"SANITY C(7,2^7)={diagonal_formula(7)} C(8,2^8)={diagonal_formula(8)}")
    for exponent in (4, 6, 8):
        low_k = 2**exponent
        high_k = 3 * 2 ** (exponent - 1)
        print(
            f"SUBSEQUENCE m={exponent} "
            f"power2={float(normalized_formula(low_k)):.12f} "
            f"three_halves={float(normalized_formula(high_k)):.12f}"
        )
    print("FINITE_CHECKS_ARE_TRANSCRIPTION_EXPERIMENTS")
    print("ALL_CHECKS_PASSED")


if __name__ == "__main__":
    main()
