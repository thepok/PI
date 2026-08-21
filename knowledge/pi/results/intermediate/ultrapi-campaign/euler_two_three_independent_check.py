#!/usr/bin/env python3
"""Independent exact replay for the Euler/Machin 1/2+1/3 shadow audit.

This file deliberately does not import ``euler_two_three_check.py``.  It
reconstructs the rational shadow, primary valuations, local residues, and
selected-prime CRT coordinates with a separate implementation.  Every
assertion is integer or ``Fraction`` arithmetic; the final ratios are only
diagnostic experiments.
"""

from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "problems/local/pi-digits.txt"
EXPECTED_SOURCE_HASH = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def chi4(n: int) -> int:
    assert n > 0 and n % 2
    return 1 if n % 4 == 1 else -1


def valuation_integer(n: int, p: int) -> int:
    assert n and p > 1
    n = abs(n)
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


def valuation_rational(x: Fraction, p: int) -> int:
    return valuation_integer(x.numerator, p) - valuation_integer(x.denominator, p)


def prime_list(bound: int) -> list[int]:
    flags = [True] * (bound + 1)
    if bound >= 0:
        flags[0] = False
    if bound >= 1:
        flags[1] = False
    for p in range(2, isqrt(bound) + 1):
        if flags[p]:
            for multiple in range(p * p, bound + 1, p):
                flags[multiple] = False
    return [p for p, is_prime in enumerate(flags) if is_prime]


def shadow(R: int) -> Fraction:
    assert R >= 3 and R % 4 == 3
    total = Fraction()
    for r in range(1, R + 1, 2):
        total += 4 * chi4(r) * (
            Fraction(1, r * 2**r) + Fraction(1, r * 3**r)
        )
    return total


def next_width(R: int) -> Fraction:
    return Fraction(4, (R + 2) * 2 ** (R + 2)) + Fraction(
        4, (R + 2) * 3 ** (R + 2)
    )


def prefix_constant(M: int) -> Fraction:
    assert M >= 1 and M % 2
    return sum(
        (
            4
            * chi4(m)
            * (Fraction(1, m * 2**m) + Fraction(1, m * 3**m))
            for m in range(1, M + 1, 2)
        ),
        Fraction(),
    )


def residue(x: Fraction, p: int) -> int:
    assert x.denominator % p
    return x.numerator * pow(x.denominator, -1, p) % p


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def primary_three_certificate(R: int) -> tuple[int, int, int]:
    rows = [(r, valuation_integer(r, 3)) for r in range(1, R + 1, 2)]
    height = max(r + exponent for r, exponent in rows)
    stripped_lcm = 1
    for r, exponent in rows:
        stripped_lcm = lcm(stripped_lcm, r // 3**exponent)
    numerator = 0
    for r, exponent in rows:
        numerator += (
            4
            * chi4(r)
            * (3**r + 2**r)
            * (stripped_lcm // (r // 3**exponent))
            * 2 ** (R - r)
            * 3 ** (height - r - exponent)
        )
    return height, stripped_lcm, numerator


def safe_horizon(width: Fraction, ell: int) -> int:
    cutoff = Fraction(1, 2 * 10**ell)
    j = -1
    scaled = width
    while scaled < cutoff:
        j += 1
        scaled *= 10
    return j


def main() -> None:
    source_hash = sha256(SOURCE.read_bytes()).hexdigest()
    assert source_hash == EXPECTED_SOURCE_HASH

    half, third = Fraction(1, 2), Fraction(1, 3)
    assert (half + third) / (1 - half * third) == 1

    primary_rows = 0
    empty_horizons = 0
    for K in range(101):
        R = 4 * K + 3
        value = shadow(R)
        width = next_width(R)
        assert width == (
            1 + Fraction(2, 3) ** (R + 2)
        ) / ((R + 2) * 2**R)
        assert valuation_rational(value, 2) == 2 - R
        assert valuation_integer(value.denominator, 2) == R - 2

        height, stripped_lcm, numerator = primary_three_certificate(R)
        assert gcd(stripped_lcm * 2**R, 3) == 1
        assert value == Fraction(numerator, stripped_lcm * 2**R * 3**height)
        assert valuation_rational(value, 3) == valuation_integer(numerator, 3) - height

        assert 10 ** (R - 2) * width > Fraction(1, 10)
        for ell in range(1, 13):
            horizon = safe_horizon(width, ell)
            cutoff = Fraction(1, 2 * 10**ell)
            assert horizon < R - 2
            if horizon < 0:
                empty_horizons += 1
                assert width >= cutoff
            else:
                assert 10**horizon * width < cutoff
                assert 10 ** (horizon + 1) * width >= cutoff
        primary_rows += 1

    power_rows = []
    for exponent in (1, 3, 5):
        R = 3**exponent
        value = shadow(R)
        assert valuation_rational(value, 3) == -(R + exponent)
        assert valuation_integer(value.denominator, 3) == R + exponent
        assert pow(10, 3 ** (R + exponent - 2), 3 ** (R + exponent)) == 1
        if R + exponent > 2:
            assert pow(10, 3 ** (R + exponent - 3), 3 ** (R + exponent)) != 1
        power_rows.append((R, R + exponent))

    local_rows = 0
    valuation_rows = 0
    crt_rows = 0
    radical_rows = []
    for K in range(1, 121):
        R = 4 * K + 3
        value = shadow(R)
        selected: list[tuple[int, int]] = []
        for p in prime_list(R):
            if p <= 3 or p * p <= R:
                continue
            bound = R // p
            M = bound if bound % 2 else bound - 1
            constant = prefix_constant(M)
            actual = residue(p * value, p)
            predicted = chi4(p) * residue(constant, p) % p
            assert actual == predicted
            assert (valuation_rational(value, p) == -1) == (predicted != 0)
            local_rows += 1
            if predicted:
                assert valuation_integer(value.denominator, p) == 1
                selected.append((p, predicted))
                valuation_rows += 1

        good_product = 1
        for p, _ in selected:
            good_product *= p
        if good_product > 1:
            assert value.denominator % good_product == 0
            complement = value.denominator // good_product
            assert gcd(good_product, complement) == 1
            actual_projection = value.numerator * pow(complement, -1, good_product)
            for p, local in selected:
                assert actual_projection % p == local * (good_product // p) % p
                crt_rows += 1
        if K in (10, 30, 60, 90, 120):
            radical_rows.append((R, log(good_product) / R))

    print(f"source sha256: {source_hash}")
    print(f"independent primary/bracket rows: {primary_rows}")
    print(f"empty-horizon convention cases: {empty_horizons}")
    print(f"independent local rows: {local_rows}")
    print(f"independent exact-valuation rows: {valuation_rows}")
    print(f"independent CRT rows: {crt_rows}")
    print(f"three-primary subsequence rows: {power_rows}")
    print(f"diagnostic log(good product)/R rows: {radical_rows}")
    print("all independent exact checks passed")


if __name__ == "__main__":
    main()
