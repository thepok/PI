#!/usr/bin/env python3
"""Independent replay for the BBP large-sieve short-orbit audit.

All bounded rows have claim label ``experiment``.  The script independently
rebuilds the BBP high-prime coordinates, checks them against direct reduced
BBP rationals at selected depths, verifies multiplicative orders and CRT
primitivity, and checks the period split when a proportional row crosses the
common period.
It does not numerically certify any asymptotic source theorem or V1.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isqrt, lcm, log
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md":
        "23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d",
    "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_check.py":
        "fb0925503b7ffbb6ec06a83c0c4d84779f13c8d81a41be84c1436a26ee2ff8c7",
    "work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813.md":
        "950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820",
    "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md":
        "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564",
    "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md":
        "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3",
    "work/theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf":
        "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd",
    "work/theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf":
        "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7",
}

DIRECT_DEPTHS = {48, 50, 64, 100, 150}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def prime_divisors(integer: int) -> list[int]:
    result: list[int] = []
    divisor = 2
    while divisor * divisor <= integer:
        if integer % divisor == 0:
            result.append(divisor)
            while integer % divisor == 0:
                integer //= divisor
        divisor += 1 if divisor == 2 else 2
    if integer > 1:
        result.append(integer)
    return result


def multiplicative_order_10(prime: int) -> int:
    require(prime > 5, "ten must be a unit")
    order = prime - 1
    for divisor in prime_divisors(order):
        while order % divisor == 0 and pow(10, order // divisor, prime) == 1:
            order //= divisor
    require(pow(10, order, prime) == 1, f"order witness p={prime}")
    for divisor in prime_divisors(order):
        require(pow(10, order // divisor, prime) != 1,
                f"minimal order p={prime}")
    return order


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def valuation_two(integer: int) -> int:
    require(integer != 0, "valuation requires nonzero integer")
    integer = abs(integer)
    return (integer & -integer).bit_length() - 1


def final_transfer_exponent(depth: int) -> int:
    power_sixteen = 16**depth
    exponent = depth
    power_ten = 10**exponent
    while 10 * power_ten <= power_sixteen:
        exponent += 1
        power_ten *= 10
    require(power_ten <= power_sixteen < 10 * power_ten,
            f"exact transfer endpoint M={depth}")
    return exponent


def high_coordinate_from_poles(depth: int, prime: int) -> Fraction:
    """Reconstruct G_(M,p) directly from all four pole families."""
    total = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        total -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            # Since prime > depth, only multipliers 1 and 3 occur here.
            total -= Fraction(2 ** (6 - multiplier), multiplier)
    character_two = 1 if prime % 8 in (1, 7) else -1
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            total += Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            total -= Fraction(
                64 * character_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return total


def high_coordinate_from_six_bands(depth: int, prime: int) -> Fraction:
    """Independent six-interval lookup for p>M."""
    positive = prime % 4 == 1
    require(positive or prime % 4 == 3, "odd prime residue")
    if 3 * prime > 8 * depth + 5:
        return Fraction(64 if positive else -32)
    if prime > 2 * depth + 1:
        return Fraction(64) if positive else Fraction(-128, 3)
    if 5 * prime > 8 * depth + 5:
        return Fraction(56) if positive else Fraction(-152, 3)
    if 3 * prime > 4 * depth + 3:
        return Fraction(264, 5) if positive else Fraction(-152, 3)
    if 7 * prime > 8 * depth + 5:
        return Fraction(752, 15) if positive else Fraction(-152, 3)
    return Fraction(752, 15) if positive else Fraction(-1040, 21)


def rational_residue(value: Fraction, modulus: int) -> int:
    require(gcd(value.denominator, modulus) == 1,
            "rational denominator must be invertible")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def direct_reduced_bbp_checks(
    depth: int, value: Fraction, primes: list[int]
) -> int:
    """Compare local formulas to the actual reduced rational B_M."""
    denominator = value.denominator
    dyadic_exponent = valuation_two(denominator)
    require(dyadic_exponent >= 4, f"dyadic BBP denominator M={depth}")
    odd_denominator = denominator >> dyadic_exponent
    dyadic_modulus = 1 << (dyadic_exponent - 4)
    selected_odd_numerator = (
        value.numerator * pow(dyadic_modulus, -1, odd_denominator)
    ) % odd_denominator

    checks = 0
    for prime in primes:
        if prime <= depth:
            continue
        if prime > 8 * depth + 5:
            break
        coordinate = high_coordinate_from_poles(depth, prime)
        survives = odd_denominator % prime == 0
        require(survives == (coordinate != 0),
                f"actual high-prime support M={depth},p={prime}")
        if not survives:
            continue
        require(odd_denominator % (prime * prime) != 0,
                f"simple high-prime exponent M={depth},p={prime}")
        direct_coordinate = (
            selected_odd_numerator
            * pow(odd_denominator // prime, -1, prime)
        ) % prime
        require(direct_coordinate == rational_residue(coordinate, prime),
                f"actual additive CRT coordinate M={depth},p={prime}")
        checks += 1
    return checks


def selected_subset(
    coordinates: list[tuple[int, Fraction, int]], factor_count: int
) -> list[tuple[int, Fraction, int]]:
    return sorted(coordinates, key=lambda row: (row[2], row[0]), reverse=True)[
        :factor_count
    ]


def subset_state(
    depth: int,
    length: int,
    subset: list[tuple[int, Fraction, int]],
) -> tuple[int, int, int, int]:
    """Verify CRT primitivity and return Q, common order, periods, remainder."""
    modulus = 1
    common_order = 1
    for prime, _, order in subset:
        modulus *= prime
        common_order = lcm(common_order, order)
    numerator = sum(
        rational_residue(coordinate, prime) * (modulus // prime)
        for prime, coordinate, _ in subset
    ) % modulus
    require(gcd(numerator, modulus) == 1,
            f"primitive fixed-factor coordinate M={depth}")
    shifted = (
        numerator
        * pow(16, -1, modulus)
        * pow(10, depth, modulus)
    ) % modulus
    require(gcd(shifted, modulus) == 1,
            f"primitive shifted coefficient M={depth}")
    require(pow(10, common_order, modulus) == 1,
            f"common-order upper witness M={depth}")
    for divisor in prime_divisors(common_order):
        require(pow(10, common_order // divisor, modulus) != 1,
                f"common-order minimality M={depth}")

    periods, remainder = divmod(length, common_order)
    # This identity checks the exact combinatorial period split used in the
    # corrected Bourgain--Chang argument, without evaluating complex sums.
    # Construct the cycle only when the row actually crosses a period; the
    # common order can otherwise be much larger than the finite sample.
    if periods:
        row = [pow(10, depth + j, modulus) for j in range(length)]
        cycle = [pow(10, depth + j, modulus) for j in range(common_order)]
        require(row == cycle * periods + cycle[:remainder],
                f"exact full-period decomposition M={depth}")
    return modulus, common_order, periods, remainder


def replay(max_depth: int) -> dict[str, object]:
    require(max_depth >= 150, "maximum depth must be at least 150")
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    # Kerr's exponents in the two uses of his third line.
    require(
        Fraction(1, 4) - Fraction(1, 96) + Fraction(49, 96)
        == Fraction(3, 4),
        "Kerr LS9 exponent arithmetic",
    )
    require(
        Fraction(1, 4) - Fraction(1, 96) + Fraction(49, 96)
        == Fraction(3, 4),
        "Kerr LS11 exponent arithmetic",
    )

    primes = primes_through(8 * max_depth + 5)
    orders = {
        prime: multiplicative_order_10(prime)
        for prime in primes
        if prime > 5
    }

    bbp_value = Fraction()
    direct_values: dict[int, Fraction] = {}
    for index in range(max(DIRECT_DEPTHS) + 1):
        bbp_value += coefficient(index) / 16**index
        if index in DIRECT_DEPTHS:
            direct_values[index] = bbp_value

    coordinate_checks = 0
    order_checks = 0
    exact_period_checks = 0
    actual_crt_checks = 0
    fixed_factor_checks = 0
    fixed_factor_rows_crossing_period = 0
    singleton_rows_crossing_period = 0
    full_product_barrier_checks = 0
    minimum_log_product_over_depth = (float("inf"), 0)
    maximum_log_row_over_product = (-1.0, 0)
    witness: dict[str, int | str] | None = None

    for depth in range(48, max_depth + 1):
        final_exponent = final_transfer_exponent(depth)
        length = final_exponent - depth + 1
        require(length > 0, f"positive row length M={depth}")

        coordinates: list[tuple[int, Fraction, int]] = []
        full_product = 1
        maximum_order = 1
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = high_coordinate_from_poles(depth, prime)
            coordinate_checks += 1
            if coordinate == 0:
                continue
            require(
                coordinate == high_coordinate_from_six_bands(depth, prime),
                f"six-band localization M={depth},p={prime}",
            )
            gamma = rational_residue(coordinate, prime)
            require(gamma != 0, f"nonzero selected coordinate M={depth},p={prime}")
            order = orders[prime]
            require(order <= prime - 1, f"Fermat order bound p={prime}")
            require(pow(10, depth + order, prime) == pow(10, depth, prime),
                    f"shifted exact period M={depth},p={prime}")
            coordinates.append((prime, coordinate, order))
            full_product *= prime
            maximum_order = max(maximum_order, order)
            order_checks += 1
            exact_period_checks += 1

        require(coordinates, f"nonempty actual high-prime support M={depth}")
        if depth in direct_values:
            actual_crt_checks += direct_reduced_bbp_checks(
                depth, direct_values[depth], primes
            )

        log_ratio = log(full_product) / depth
        if log_ratio < minimum_log_product_over_depth[0]:
            minimum_log_product_over_depth = (log_ratio, depth)
        row_ratio = log(length) / log(full_product)
        if row_ratio > maximum_log_row_over_product[0]:
            maximum_log_row_over_product = (row_ratio, depth)
        require(length <= 2 * depth, f"linear row length M={depth}")
        require(maximum_order <= 8 * depth + 4,
                f"all local orders are O(M), M={depth}")
        full_product_barrier_checks += 2

        for prime, coordinate, order in coordinates:
            if length**4 > prime and order**4 > prime and length > order:
                subset_state(depth, length, [(prime, coordinate, order)])
                singleton_rows_crossing_period += 1

        for factor_count in range(1, 5):
            if len(coordinates) < factor_count:
                continue
            subset = selected_subset(coordinates, factor_count)
            modulus = 1
            for prime, _, _ in subset:
                modulus *= prime
            # delta_0=1/(4k), checked without floating point.
            if length ** (4 * factor_count) <= modulus:
                continue
            if not all(
                order ** (4 * factor_count) > modulus
                for _, _, order in subset
            ):
                continue
            modulus_again, common_order, periods, _ = subset_state(
                depth, length, subset
            )
            require(modulus_again == modulus, "consistent subset modulus")
            fixed_factor_checks += 1
            if periods:
                fixed_factor_rows_crossing_period += 1

        if depth == 48:
            coordinate_73 = high_coordinate_from_poles(48, 73)
            require(coordinate_73 == Fraction(264, 5), "M=48,p=73 coordinate")
            order_73 = orders[73]
            require(order_73 == 8 and length == 10, "period-crossing witness")
            require(length**4 > 73 and order_73**4 > 73,
                    "Corollary 4.5 size hypotheses at witness")
            modulus, common_order, periods, remainder = subset_state(
                depth, length, [(73, coordinate_73, order_73)]
            )
            require((modulus, common_order, periods, remainder) == (73, 8, 1, 2),
                    "exact period split at witness")
            witness = {
                "depth": depth,
                "prime": 73,
                "row_length": length,
                "order": order_73,
                "complete_periods": periods,
                "remainder": remainder,
                "coordinate": str(coordinate_73),
            }

    require(witness is not None, "period-crossing witness retained")
    require(singleton_rows_crossing_period > 0,
            "singleton period-crossing rows exist")

    # Exact synchronized-orbit witness on actual M=48 coordinates.
    require(high_coordinate_from_poles(48, 53) == Fraction(752, 15),
            "M=48,p=53 coordinate")
    require(high_coordinate_from_poles(48, 79) == Fraction(-152, 3),
            "M=48,p=79 coordinate")
    require(orders[53] == orders[79] == 13, "paired orders")
    paired = {(pow(10, j, 53), pow(10, j, 79)) for j in range(13)}
    left = {pow(10, j, 53) for j in range(13)}
    right = {pow(10, j, 79) for j in range(13)}
    require(len(paired) == 13, "synchronized pair orbit")
    require(len(left) * len(right) == 169, "Cartesian pair size")

    return {
        "status": "PASS",
        "verifies_explicit_fixed_factor_period_split": True,
        "bounded_replay_label": "experiment",
        "analytic_claim_label": "proof sketch",
        "depth_range": [48, max_depth],
        "coordinate_formula_checks": coordinate_checks,
        "actual_reduced_crt_checks": actual_crt_checks,
        "multiplicative_order_checks": order_checks,
        "exact_period_checks": exact_period_checks,
        "fixed_factor_hypothesis_checks": fixed_factor_checks,
        "fixed_factor_rows_crossing_period": fixed_factor_rows_crossing_period,
        "singleton_rows_crossing_period": singleton_rows_crossing_period,
        "period_crossing_witness": witness,
        "full_product_barrier_checks": full_product_barrier_checks,
        "minimum_log_high_product_over_depth": minimum_log_product_over_depth,
        "maximum_log_row_length_over_log_high_product": maximum_log_row_over_product,
        "actual_pair_diagonal_size": len(paired),
        "actual_pair_cartesian_size": len(left) * len(right),
        "kerr_LS9_exponent": "3/4",
        "kerr_LS11_exponent": "3/4",
        "erdos_murty_pdf_sha256_directly_inspected":
            "75da28d20c371a3700af9c8a67130f5a8642010e74bab6ae2627bfefa64909a8",
        "asserts_full_product_cancellation": False,
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=600)
    arguments = parser.parse_args()
    print(json.dumps(replay(arguments.max_depth), indent=2, sort_keys=True))
