#!/usr/bin/env python3
"""Independent exact audit for hutton_primary_phase_attack.md.

This replay deliberately omits the floating-point phase table.  Every check
uses integers or Fraction.  In particular it verifies the claimed exact
period of the 3-by-7 primary denominator by modular exponentiation, rather
than merely identifying the period with a multiplicative order.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
KERR_SHA256 = "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd"
KS_SHA256 = "46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vp(value: int, prime: int) -> int:
    assert value > 0
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def floor_log(value: int, base: int) -> int:
    exponent = 0
    while base ** (exponent + 1) <= value:
        exponent += 1
    return exponent


def primes_le(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            sieve[prime * prime : bound + 1 : prime] = (
                b"\x00" * (((bound - prime * prime) // prime) + 1)
            )
    return [n for n in range(2, bound + 1) if sieve[n]]


def chi4(odd: int) -> int:
    assert odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def hutton(radius: int) -> Fraction:
    total = Fraction()
    for odd in range(1, radius + 1, 2):
        total += chi4(odd) * (
            Fraction(8, odd * 3**odd) + Fraction(4, odd * 7**odd)
        )
    return total


def mod_fraction(value: Fraction, modulus: int) -> int:
    assert math.gcd(value.denominator, modulus) == 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def crt(first: int, mod_first: int, second: int, mod_second: int) -> int:
    correction = (second - first) * pow(mod_first, -1, mod_second)
    return (first + mod_first * (correction % mod_second)) % (
        mod_first * mod_second
    )


def additive_component(state: int, modulus: int, component: int) -> int:
    other = modulus // component
    assert math.gcd(other, component) == 1
    return state * pow(other, -1, component) % component


def singular_prefix(radius: int, prime: int) -> Fraction:
    largest = radius // prime
    return sum(
        (
            chi4(odd)
            * (
                Fraction(8, odd * 3**odd)
                + Fraction(4, odd * 7**odd)
            )
            for odd in range(1, largest + 1, 2)
        ),
        Fraction(),
    )


def main() -> None:
    sys.set_int_max_str_digits(1_000_000)
    root = Path(__file__).resolve().parents[2]
    assert digest(root / "problems/local/pi-digits.txt") == SOURCE_SHA256
    assert digest(
        root
        / "work/theory/pi-lacunary-near-return-sparsity/library/t118"
        / "kerr-1302.4170v1.pdf"
    ) == KERR_SHA256
    assert digest(
        root
        / "work/theory/pi-lacunary-near-return-sparsity/library/t85"
        / "konyagin-shparlinski-2012.pdf"
    ) == KS_SHA256

    # Exhaustively falsify the dominant-layer lemma on a broad small range.
    lemma_instances = 0
    lemma_score_checks = 0
    for prime in (3, 5, 7, 11, 13):
        for radius in range(3, 2501, 2):
            exponent = vp(radius, prime)
            if exponent == 0:
                continue
            if floor_log(radius, prime) > prime**exponent - 2:
                continue
            lemma_instances += 1
            for odd in range(1, radius, 2):
                assert odd + vp(odd, prime) <= radius - 2
                lemma_score_checks += 1

    family_assertions = 0
    enumerated_family_scores = 0
    maximum_assertions = 0
    for a in range(2, 21):
        c = a + 1
        radius = 3**a * 7**c
        assert radius % 4 == 3
        assert floor_log(radius, 3) <= 3**a - 2
        assert floor_log(radius, 7) <= 7**c - 2
        assert floor_log(radius, 3) <= 3 * a + 1
        assert floor_log(radius, 7) <= 2 * a
        family_assertions += 5
        if a <= 4:
            for prime, exponent in ((3, a), (7, c)):
                scores = [
                    odd + vp(odd, prime)
                    for odd in range(1, radius, 2)
                ]
                assert max(scores) <= radius - 2
                assert max(scores) < radius + exponent
                enumerated_family_scores += len(scores)
                maximum_assertions += 2

    assert family_assertions == 95
    assert enumerated_family_scores == 1_429_278
    assert maximum_assertions == 12

    # Full rational replay at a=2.
    a = 2
    c = 3
    radius = 3**a * 7**c
    value = hutton(radius)
    numerator = value.numerator
    denominator = value.denominator
    e3 = radius + a
    e7 = radius + c
    assert vp(denominator, 3) == e3
    assert vp(denominator, 7) == e7
    b = vp(denominator, 5)
    assert b == floor_log(radius, 5) == 4
    assert denominator % 2 == 1

    low3 = 3 ** (a + 2)
    low7 = 7 ** (c + 2)
    assert mod_fraction(value * 3**e3, low3) == (
        -8 * pow(7**c, -1, low3)
    ) % low3
    assert mod_fraction(value * 7**e7, low7) == (
        -4 * pow(3**a, -1, low7)
    ) % low7

    post_modulus = denominator // 5**b
    post_state = numerator * 2**b % post_modulus
    primary = 3**e3 * 7**e7
    primary_coordinate = additive_component(
        post_state, post_modulus, primary
    )
    expected3 = -8 * 10**b * 7**radius % low3
    expected7 = -4 * 10**b * 3**radius % low7
    assert primary_coordinate % low3 == expected3
    assert primary_coordinate % low7 == expected7
    assert math.gcd(primary_coordinate, primary) == 1

    # High-prime survival and the post-transient one-prime CRT coordinate.
    primes = primes_le(radius)
    high_primes = 0
    surviving: list[int] = []
    coordinate_checks = 0
    for prime in primes:
        if prime <= math.isqrt(radius) or prime <= 7:
            continue
        high_primes += 1
        prefix = singular_prefix(radius, prime)
        predicted_p_hutton = chi4(prime) * mod_fraction(prefix, prime) % prime
        actual_p_hutton = mod_fraction(prime * value, prime)
        assert actual_p_hutton == predicted_p_hutton
        exponent = vp(denominator, prime)
        assert exponent in (0, 1)
        assert (exponent == 1) == (predicted_p_hutton != 0)
        if exponent:
            surviving.append(prime)
            actual_coordinate = additive_component(
                post_state, post_modulus, prime
            )
            assert actual_coordinate == (
                pow(10, b, prime) * predicted_p_hutton
            ) % prime
            coordinate_checks += 1

    assert high_primes == 425
    assert len(surviving) == coordinate_checks == 425
    selected = primary * math.prod(surviving)
    complement = post_modulus // selected
    assert math.gcd(selected, complement) == 1
    assert complement == 3443846140271004739007417826008487767
    assert complement <= radius ** math.isqrt(radius)

    factorization: list[tuple[int, int]] = []
    residue = complement
    for prime in primes:
        if prime > math.isqrt(radius):
            break
        if prime in (2, 3, 5, 7):
            continue
        exponent = 0
        while residue % prime == 0:
            residue //= prime
            exponent += 1
        if exponent:
            assert exponent <= floor_log(radius, prime)
            factorization.append((prime, exponent))
    assert residue == 1
    assert factorization == [
        (11, 3),
        (13, 3),
        (17, 2),
        (19, 2),
        (23, 2),
        (29, 2),
        (31, 2),
        (37, 2),
        (41, 2),
        (43, 2),
        (47, 2),
        (53, 2),
    ]

    # Verify the explicit exact order, including minimality.
    exact_period = 2 * 3 ** (e3 - 2) * 7 ** (e7 - 1)
    assert pow(10, exact_period, primary) == 1
    for prime in (2, 3, 7):
        assert pow(10, exact_period // prime, primary) != 1

    stationary = crt(expected3, low3, expected7, low7)
    low_modulus = low3 * low7
    assert (stationary, low_modulus) == (1_091_638, 1_361_367)
    assert math.gcd(stationary, primary) == 1

    # The report's exact transfer count and chord separator.
    width = Fraction(8, (radius + 2) * 3 ** (radius + 2)) + Fraction(
        4, (radius + 2) * 7 ** (radius + 2)
    )
    horizon = -1
    scale = 1
    while scale * width < 1:
        horizon += 1
        scale *= 10
    assert horizon == 1476
    offsets = horizon - b + 1
    assert offsets == 1473
    assert stationary * 10 ** (offsets - 1) < primary
    chord_without_2pi = Fraction(
        stationary * (10**offsets - 1),
        9 * offsets * primary,
    )
    # Since 2*pi < 7, this is a fully rational strengthening of the printed
    # decimal estimate.
    assert 7 * chord_without_2pi < Fraction(1, 10**2609)

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"dominant_lemma_instances={lemma_instances}")
    print(f"dominant_lemma_score_checks={lemma_score_checks}")
    print(f"family_assertions={family_assertions}")
    print(f"enumerated_family_scores={enumerated_family_scores}")
    print(f"maximum_assertions={maximum_assertions}")
    print(f"high_primes={high_primes}")
    print(f"surviving_high_primes={len(surviving)}")
    print(f"actual_high_prime_coordinate_checks={coordinate_checks}")
    print(f"exact_period_digits={len(str(exact_period))}")
    print(f"stationary_lift={stationary}")
    print(f"horizon={horizon},offsets={offsets}")
    print("all independent exact checks passed")


if __name__ == "__main__":
    main()
