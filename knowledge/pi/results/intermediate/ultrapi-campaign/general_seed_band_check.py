#!/usr/bin/env python3
"""Exact checks for the general fixed-seed prime-band calculation.

This is deliberately independent of Lean and uses only Python integers and
``fractions.Fraction``.  Finite checks are experiments, not proofs.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    a = 3
    while a * a <= n:
        if n % a == 0:
            return False
        a += 2
    return True


def prime_table(n: int) -> bytearray:
    table = bytearray(b"\x01") * (n + 1)
    table[:2] = b"\x00\x00"
    for a in range(2, isqrt(n) + 1):
        if table[a]:
            table[a * a : n + 1 : a] = b"\x00" * (((n - a * a) // a) + 1)
    return table


def common_coefficient(r: int) -> Fraction:
    """C_r: the p-local coefficient when the endpoint is regular."""
    assert r >= 1
    return 4 * sum(
        (
            (-1) ** (s - 1)
            * Fraction(1, 2 * s - 1)
            * (
                Fraction(4, 5 ** (2 * s - 1))
                - Fraction(1, 239 ** (2 * s - 1))
            )
            for s in range(1, r + 1)
        ),
        Fraction(),
    )


def endpoint_coefficient(r: int) -> Fraction:
    """E_r after d+2=(2r+1)p and the forced sign are used."""
    return common_coefficient(r) - Fraction(
        4 * ((-1) ** r), (2 * r + 1) * 239 ** (2 * r + 1)
    )


def sampled_seed(n_index: int) -> Fraction:
    """The exact rational y_(N+1)=10^(N+1) M_(3(N+1))."""
    n = n_index + 1
    five = sum(
        (
            Fraction(16 * (-1 if j & 1 else 1), (2 * j + 1) * 5 ** (2 * j + 1))
            for j in range(6 * n + 2)
        ),
        Fraction(),
    )
    two_three_nine = sum(
        (
            Fraction(4 * (-1 if j & 1 else 1), (2 * j + 1) * 239 ** (2 * j + 1))
            for j in range(6 * n + 3)
        ),
        Fraction(),
    )
    return 10**n * (five - two_three_nine)


def main() -> None:
    actual_source_sha256 = sha256(SOURCE.read_bytes()).hexdigest()
    if actual_source_sha256 != SOURCE_SHA256:
        raise AssertionError(
            f"source hash mismatch: path={SOURCE} actual={actual_source_sha256} "
            f"expected={SOURCE_SHA256}"
        )

    c3 = common_coefficient(3)
    e3 = endpoint_coefficient(3)
    assert c3 == Fraction(38279241713339684, 12184551018734375)
    c3_factors = [2, 2, 19, 37, 79, 48049, 3586217]
    assert c3.numerator == __import__("math").prod(c3_factors)
    assert all(is_prime(p) for p in set(c3_factors))

    assert e3 == Fraction(15305839961353732690848, 4871956171187883640625)
    e3_factors = [2, 2, 2, 2, 2, 3, 3, 13, 29, 8429, 35533, 470668789]
    assert e3.numerator == __import__("math").prod(e3_factors)
    assert all(is_prime(p) for p in set(e3_factors))
    assert all(p % 12 != 11 for p in set(e3_factors) if p > 3)

    # Every normal r=3 exception really can occur in its band.  For the first
    # three rows, also construct the complete reduced rational seed and check
    # directly that p disappeared from its denominator.
    r3_examples = [
        (19, 7),
        (37, 15),
        (79, 32),
        (48049, 20020),
        (3586217, 1494256),
    ]
    for p, n_index in r3_examples:
        d = 12 * n_index + 15
        assert 5 * p <= d < 7 * p
        assert (d + 2) % p != 0
        assert c3.numerator % p == 0
        if n_index <= 32:
            assert sampled_seed(n_index).denominator % p != 0

    # Exhaustively compare the residue criterion with the fully reduced exact
    # rational for all eligible primes in the first 101 seeds.
    primes = prime_table(12 * 100 + 15)
    checked = 0
    endpoint_checked = 0
    predicted_nonsurvivors = 0
    mismatches: list[tuple[int, int, int, int, bool]] = []
    coefficient_cache: dict[int, Fraction] = {}
    endpoint_cache: dict[int, Fraction] = {}
    for n_index in range(101):
        d = 12 * n_index + 15
        seed = sampled_seed(n_index)
        for p in range(2, d + 1):
            if not primes[p]:
                continue
            r = (d // p + 1) // 2
            if p <= max(5, 2 * r + 1) or p == 239:
                continue
            endpoint = (d + 2) % p == 0
            cache = endpoint_cache if endpoint else coefficient_cache
            coefficient = cache.setdefault(
                r, endpoint_coefficient(r) if endpoint else common_coefficient(r)
            )
            assert coefficient.denominator % p != 0
            predicted = coefficient.numerator % p != 0
            actual = seed.denominator % p == 0
            checked += 1
            endpoint_checked += int(endpoint)
            predicted_nonsurvivors += int(not predicted)
            if predicted != actual:
                mismatches.append((n_index, p, r, coefficient.numerator % p, actual))
    assert not mismatches

    # Endpoint cancellation is not universally impossible: at N=43, p=41,
    # r=6, d+2=13p, and the complete endpoint coefficient vanishes modulo p.
    assert 12 * 43 + 17 == 13 * 41
    assert endpoint_coefficient(6).numerator % 41 == 0
    assert sampled_seed(43).denominator % 41 != 0

    # A larger exact modular scan records how often this obstruction arises.
    max_n = 5000
    endpoint_primes = prime_table(12 * max_n + 17)
    endpoint_rows = 0
    endpoint_bad: list[tuple[int, int, int, int]] = []
    endpoint_cache.clear()
    for n_index in range(max_n + 1):
        endpoint_value = 12 * n_index + 17
        for divisor in range(3, isqrt(endpoint_value) + 1, 2):
            if endpoint_value % divisor != 0:
                continue
            for p in {divisor, endpoint_value // divisor}:
                quotient = endpoint_value // p
                if (
                    p <= quotient
                    or p <= 5
                    or p == 239
                    or not endpoint_primes[p]
                    or quotient % 2 == 0
                ):
                    continue
                r = (quotient - 1) // 2
                coefficient = endpoint_cache.setdefault(r, endpoint_coefficient(r))
                endpoint_rows += 1
                if coefficient.numerator % p == 0:
                    endpoint_bad.append((n_index, p, r, quotient))

    expected_bad = [
        (43, 41, 6, 13),
        (337, 131, 15, 31),
        (1352, 149, 54, 109),
        (1380, 137, 60, 121),
        (2157, 439, 29, 59),
        (2194, 479, 27, 55),
        (3513, 233, 90, 181),
    ]
    assert endpoint_rows == 2731
    assert endpoint_bad == expected_bad

    print(f"source_sha256={SOURCE_SHA256}")
    print(f"C3={c3.numerator}/{c3.denominator}")
    print(f"E3={e3.numerator}/{e3.denominator}")
    print(
        "full_seed_rows="
        f"{checked} endpoint_rows={endpoint_checked} "
        f"predicted_nonsurvivors={predicted_nonsurvivors} mismatches=0"
    )
    print(f"endpoint_scan_rows={endpoint_rows} endpoint_bad={endpoint_bad}")


if __name__ == "__main__":
    main()
