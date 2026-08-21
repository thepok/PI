#!/usr/bin/env python3
"""Independent finite replay for the BBP large-sieve short-orbit audit.

All bounded output has claim label ``experiment``.  This file verifies exact
row lengths, high-prime coordinates, multiplicative orders, diagonal CRT
periods, and the hypotheses of a few finite fixed-factor examples.  Floating
point is used only for explicitly labelled magnitude diagnostics.  It does
not prove an asymptotic exponential-sum estimate, a fixed return, or V1.
"""

from __future__ import annotations

import argparse
import cmath
import hashlib
import math
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
MIXED_SEPARATOR_SHA256 = (
    "950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820"
)
HIGH_PHASE_SHA256 = (
    "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564"
)
ODD_COFACTOR_SHA256 = (
    "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3"
)
KERR_SHA256 = (
    "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd"
)
BOURGAIN_CHANG_SHA256 = (
    "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7"
)


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def prime_divisors(integer: int) -> list[int]:
    answer: list[int] = []
    divisor = 2
    while divisor * divisor <= integer:
        if integer % divisor == 0:
            answer.append(divisor)
            while integer % divisor == 0:
                integer //= divisor
        divisor += 1 if divisor == 2 else 2
    if integer > 1:
        answer.append(integer)
    return answer


def multiplicative_order_10(prime: int) -> int:
    assert prime > 5
    order = prime - 1
    for divisor in prime_divisors(order):
        while order % divisor == 0 and pow(10, order // divisor, prime) == 1:
            order //= divisor
    assert pow(10, order, prime) == 1
    for divisor in prime_divisors(order):
        assert pow(10, order // divisor, prime) != 1
    return order


def last_transfer_exponent(depth: int) -> int:
    """Largest n with 10^n <= 16^depth, using integer comparisons only."""
    power_sixteen = 16**depth
    exponent = depth
    power_ten = 10**exponent
    while power_ten * 10 <= power_sixteen:
        exponent += 1
        power_ten *= 10
    assert power_ten <= power_sixteen < power_ten * 10
    return exponent


def high_prime_coordinate(depth: int, prime: int) -> Fraction:
    """Rebuild the four-pole localization G_(M,p), without branch imports."""
    answer = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            if multiplier <= 6:
                answer -= Fraction(2 ** (6 - multiplier), multiplier)
            else:
                answer -= Fraction(1, multiplier * 2 ** (multiplier - 6))
    character_two = 1 if prime % 8 in (1, 7) else -1
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            answer += Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            answer -= Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return answer


def residue(value: Fraction, prime: int) -> int:
    assert gcd(value.denominator, prime) == 1
    return value.numerator * pow(value.denominator, -1, prime) % prime


def local_normalized_magnitude(
    depth: int, length: int, prime: int, coordinate: Fraction
) -> float:
    gamma = residue(coordinate, prime)
    inverse_sixteen = pow(16, -1, prime)
    total = 0j
    for exponent in range(depth, depth + length):
        multiplier = (pow(10, exponent, prime) - 16) * inverse_sixteen % prime
        total += cmath.exp(2j * math.pi * (gamma * multiplier % prime) / prime)
    return abs(total) / length


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=400)
    args = parser.parse_args()
    if args.max_depth < 100:
        raise SystemExit("--max-depth must be at least 100")

    root = repository_root()
    pinned = {
        root / "problems/local/pi-digits.txt": SOURCE_SHA256,
        root
        / "work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813.md": (
            MIXED_SEPARATOR_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md": (
            HIGH_PHASE_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md": (
            ODD_COFACTOR_SHA256
        ),
        root
        / "work/theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf": (
            KERR_SHA256
        ),
        root
        / "work/theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf": (
            BOURGAIN_CHANG_SHA256
        ),
    }
    for path, expected in pinned.items():
        assert sha256(path) == expected, path

    primes = primes_through(8 * args.max_depth + 5)
    orders = {prime: multiplicative_order_10(prime) for prime in primes if prime > 5}

    coordinate_checks = 0
    order_checks = 0
    period_checks = 0
    low_order_rows = 0
    square_root_good_rows = 0
    fixed_factor_hypothesis_checks = 0
    first_order_falsifier: tuple[int, int, int, int, Fraction] | None = None
    maximum_low_order_correlation = (-1.0, 0, 0, 0, 0, Fraction())
    minimum_global_log_ratio = (float("inf"), 0, 0, 0)
    record: list[str] = []

    for depth in range(48, args.max_depth + 1):
        final_exponent = last_transfer_exponent(depth)
        length = final_exponent - depth + 1
        assert length > 0
        assert 10 ** final_exponent <= 16**depth < 10 ** (final_exponent + 1)

        coordinates: list[tuple[int, Fraction, int]] = []
        row_low = 0
        global_order = 1
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = high_prime_coordinate(depth, prime)
            if coordinate == 0:
                continue
            gamma = residue(coordinate, prime)
            assert gamma != 0
            coordinate_checks += 1

            order = orders[prime]
            order_checks += 1
            assert order <= prime - 1
            assert pow(10, depth + order, prime) == pow(10, depth, prime)
            period_checks += 1
            global_order = lcm(global_order, order)
            coordinates.append((prime, coordinate, order))

            if order * order > prime:
                square_root_good_rows += 1
            if order <= length:
                row_low += 1
                low_order_rows += 1
                if first_order_falsifier is None:
                    first_order_falsifier = (
                        depth,
                        prime,
                        length,
                        order,
                        coordinate,
                    )
                magnitude = local_normalized_magnitude(
                    depth, length, prime, coordinate
                )
                candidate = (
                    magnitude,
                    depth,
                    prime,
                    length,
                    order,
                    coordinate,
                )
                if candidate[0] > maximum_low_order_correlation[0]:
                    maximum_low_order_correlation = candidate

        assert coordinates
        assert global_order >= max(order for _, _, order in coordinates)
        ratio = math.log(global_order) / depth
        if ratio < minimum_global_log_ratio[0]:
            minimum_global_log_ratio = (
                ratio,
                depth,
                global_order.bit_length(),
                len(coordinates),
            )

        # Finite fixed-factor examples of the exact Bourgain--Chang input.
        # delta=1/(4k): ord_p(10)>Q^delta and T>Q^delta are checked by
        # integer powers.  This is only a finite hypothesis replay.
        for factor_count in range(1, 5):
            if len(coordinates) < factor_count:
                continue
            chosen = sorted(
                coordinates,
                key=lambda item: (item[2] ** (4 * factor_count), item[0]),
                reverse=True,
            )[:factor_count]
            modulus = math.prod(prime for prime, _, _ in chosen)
            if not all(
                order ** (4 * factor_count) > modulus
                for _, _, order in chosen
            ):
                continue
            if length ** (4 * factor_count) <= modulus:
                continue
            numerator = sum(
                residue(coordinate, prime) * (modulus // prime)
                for prime, coordinate, _ in chosen
            ) % modulus
            assert gcd(numerator, modulus) == 1
            shifted_coefficient = (
                numerator
                * pow(16, -1, modulus)
                * pow(10, depth, modulus)
            ) % modulus
            assert gcd(shifted_coefficient, modulus) == 1
            fixed_factor_hypothesis_checks += 1

        record.append(
            f"{depth}:{length}:{len(coordinates)}:{row_low}:"
            f"{global_order.bit_length()}"
        )

    assert first_order_falsifier is not None
    assert first_order_falsifier == (48, 73, 10, 8, Fraction(264, 5))
    assert maximum_low_order_correlation[0] > 0.79

    # Exact diagonal-versus-Cartesian witness from the actual M=48 support.
    # Both bases have period thirteen, so the paired orbit has thirteen
    # states, not 13*13 independent states.
    assert high_prime_coordinate(48, 53) == Fraction(752, 15)
    assert high_prime_coordinate(48, 79) == Fraction(-152, 3)
    assert orders[53] == orders[79] == 13
    diagonal = {
        (pow(10, index, 53), pow(10, index, 79)) for index in range(13)
    }
    first_projection = {pow(10, index, 53) for index in range(13)}
    second_projection = {pow(10, index, 79) for index in range(13)}
    assert len(diagonal) == 13
    assert len(first_projection) * len(second_projection) == 169
    assert diagonal != {
        (left, right)
        for left in first_projection
        for right in second_projection
    }

    record_sha256 = hashlib.sha256("\n".join(record).encode()).hexdigest()
    print("status: PASS")
    print("bounded_replay_label: experiment")
    print("analytic_claim_label: proof sketch")
    print(f"depth_range: [48, {args.max_depth}]")
    print(f"high_prime_coordinate_checks: {coordinate_checks}")
    print(f"multiplicative_order_checks: {order_checks}")
    print(f"exact_period_checks: {period_checks}")
    print(f"order_at_most_row_length_rows: {low_order_rows}")
    print(f"order_above_sqrt_prime_rows: {square_root_good_rows}")
    print(f"fixed_factor_hypothesis_checks: {fixed_factor_hypothesis_checks}")
    print(f"first_order_gt_length_falsifier: {first_order_falsifier}")
    print(
        "maximum_low_order_normalized_magnitude: "
        f"{maximum_low_order_correlation[0]:.15f} at "
        f"M={maximum_low_order_correlation[1]}, "
        f"p={maximum_low_order_correlation[2]}, "
        f"T={maximum_low_order_correlation[3]}, "
        f"ord={maximum_low_order_correlation[4]}, "
        f"G={maximum_low_order_correlation[5]}"
    )
    print(
        "minimum_log_global_order_over_depth: "
        f"{minimum_global_log_ratio[0]:.15f} at "
        f"M={minimum_global_log_ratio[1]} "
        f"(bit_length={minimum_global_log_ratio[2]}, "
        f"coordinate_count={minimum_global_log_ratio[3]})"
    )
    print("actual_M48_pair: p=53,79; orders=13,13")
    print("actual_pair_diagonal_size: 13")
    print("actual_pair_cartesian_size: 169")
    print(f"exact_record_sha256: {record_sha256}")
    print("asserts_full_product_cancellation: false")
    print("asserts_fixed_sixteen_return: false")
    print("asserts_v1: false")


if __name__ == "__main__":
    main()
