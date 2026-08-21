#!/usr/bin/env python3
"""Independent exact replay for the actual BBP odd-quotient audit.

Every finite output is an ``experiment``.  This script deliberately does not
import the primary checker.  It checks exact rational, modular, indexing, and
support identities; it does not prove the PNT/AP asymptotics, the asymptotic
height cutoff, a fixed-sixteen return, or V1.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd, log
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
PARENT_SHA256 = (
    "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d"
)
PRIMARY_REPORT_SHA256 = (
    "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc"
)
PRIMARY_CHECKER_SHA256 = (
    "c5f55d07feb84aa53285c8e0aee0bf32654a1bd7aed207ad518acfc07941d053"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(relative: str) -> str:
    return hashlib.sha256((root() / relative).read_bytes()).hexdigest()


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def valuation(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("valuation at zero is not used")
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def rational_mod(value: Fraction, modulus: int) -> int:
    assert gcd(value.denominator, modulus) == 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def reflected_f_mod(argument: int, bits: int) -> int:
    if bits <= 0:
        return 0
    modulus = 1 << bits
    total = 0
    # Terms from this index onward contain 2**bits.
    for offset in range((bits + 3) // 4):
        total += pow(16, offset, modulus) * rational_mod(
            coefficient(argument - 1 - offset), modulus
        )
    return total % modulus


def decimal_upper(depth: int) -> int:
    """Return max n with 10**n <= 16**depth, using integers only."""
    power = 16**depth
    candidate = len(str(power)) - 1
    while 10 ** (candidate + 1) <= power:
        candidate += 1
    while 10**candidate > power:
        candidate -= 1
    return candidate


def first_depth_for_exponent(exponent: int) -> int:
    depth = 0
    target = 10**exponent
    power = 1
    while power < target:
        power *= 16
        depth += 1
    return depth


def power_of_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def localization(depth: int, prime: int) -> Fraction:
    """The four-pole rational G_(M,p), derived independently."""
    chi_two = 1 if prime % 8 in (1, 7) else -1
    answer = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            answer -= power_of_two(6 - multiplier) / multiplier
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            answer += Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            answer -= Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return answer


def individual_localization(slot: int, multiplier: int, prime: int) -> Fraction:
    chi_two = 1 if prime % 8 in (1, 7) else -1
    if slot == 0:
        return -Fraction(8, multiplier * 4 ** (multiplier - 1))
    if slot == 1:
        return -power_of_two(6 - multiplier) / multiplier
    if slot == 2:
        return Fraction(
            64 * chi_two,
            multiplier * 2 ** ((multiplier - 1) // 2),
        )
    if slot == 3:
        return -Fraction(
            64 * chi_two,
            multiplier * 2 ** ((multiplier - 1) // 2),
        )
    raise AssertionError("unknown pole")


def possible_support(depth: int, prime: int) -> bool:
    if prime <= 4 * depth + 3:
        return True
    return (
        prime % 8 == 1 and prime <= 8 * depth + 1
    ) or (
        prime % 8 == 5 and prime <= 8 * depth + 5
    )


def factor_denominator(
    odd_denominator: int, primes: list[int]
) -> dict[int, int]:
    remaining = odd_denominator
    factors: dict[int, int] = {}
    for prime in primes:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            factors[prime] = exponent
        if remaining == 1:
            break
    assert remaining == 1
    return factors


def lcm_upto(limit: int) -> int:
    answer = 1
    for value in range(1, limit + 1):
        answer = answer * value // gcd(answer, value)
    return answer


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def check_block_order() -> int:
    checks = 0
    representatives = (17, 13, 11, 7)  # residues 1, 5, 3, 7 mod 8
    for prime in representatives:
        running = Fraction()
        for block in range(16):
            events: list[tuple[int, Fraction]] = []
            for index in range(block * prime, (block + 1) * prime):
                factors = (
                    2 * index + 1,
                    4 * index + 3,
                    8 * index + 1,
                    8 * index + 5,
                )
                for slot, factor in enumerate(factors):
                    if factor % prime == 0:
                        multiplier = factor // prime
                        events.append(
                            (
                                index,
                                individual_localization(
                                    slot, multiplier, prime
                                ),
                            )
                        )
            events.sort()
            assert len(events) == 4
            signs = [1 if value > 0 else -1 for _, value in events]
            if prime % 4 == 1:
                assert signs == [1, -1, -1, -1]
                completed = Fraction(16) * coefficient(block) / 16**block
                assert sum((value for _, value in events), Fraction()) == completed
                for _, value in events:
                    running += value
                    assert running > 0
            else:
                assert signs == [-1, -1, -1, 1]
                bracket = (
                    Fraction(8, 2 * block + 1)
                    + Fraction(32, 4 * block + 1)
                    + Fraction(32, 8 * block + 3)
                    - Fraction(8, 8 * block + 7)
                ) / 16**block
                completed = -bracket
                assert sum((value for _, value in events), Fraction()) == completed
                for _, value in events:
                    running += value
                    assert running < 0
            checks += 1
    return checks


def check_uniform_absolute_sum() -> int:
    """Finite shadows of the report's depth-independent 1536/5 majorant."""
    checks = 0
    infinite_majorant = Fraction(1536, 5)
    for cutoff in range(1, 257):
        total = Fraction()
        for multiplier in range(1, cutoff + 1, 2):
            total += Fraction(8, multiplier * 4 ** (multiplier - 1))
            total += abs(power_of_two(6 - multiplier) / multiplier)
            total += 2 * Fraction(
                64,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
        assert total < infinite_majorant
        checks += 1
    return checks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=260)
    args = parser.parse_args()
    if args.max_depth < 60:
        raise SystemExit("--max-depth must be at least 60")

    assert sha256("problems/local/pi-digits.txt") == SOURCE_SHA256
    assert (
        sha256("work/ultrapi-resume/bbp_short_orbit_return_attack.md")
        == PARENT_SHA256
    )
    assert (
        sha256("work/ultrapi-resume/bbp_actual_odd_quotient_attack.md")
        == PRIMARY_REPORT_SHA256
    )
    assert (
        sha256("work/ultrapi-resume/bbp_actual_odd_quotient_check.py")
        == PRIMARY_CHECKER_SHA256
    )

    # Exact floor/ceiling choices in the proportional-window equivalence.
    floor_choice_checks = 0
    for exponent in range(5, decimal_upper(args.max_depth) + 1):
        depth = first_depth_for_exponent(exponent)
        assert depth <= exponent
        assert exponent <= decimal_upper(depth)
        if depth:
            assert exponent > decimal_upper(depth - 1)
        floor_choice_checks += 1

    block_order_checks = check_block_order()
    uniform_absolute_sum_checks = check_uniform_absolute_sum()
    primes = primes_through(8 * args.max_depth + 5)
    partial_sum = Fraction()
    previous: dict[str, object] | None = None
    carry_checks = 0
    quotient_checks = 0
    localization_checks = 0
    survival_equivalence_checks = 0
    eight_constant_checks = 0
    height_denominator_checks = 0
    exponent_bound_checks = 0
    support_shape_checks = 0
    crt_checks = 0
    phase_checks = 0
    proportional_phase_checks = 0
    modular_cancellations: list[tuple[int, int]] = []
    last_full_support_mass = 0.0
    last_above_depth_mass = 0.0

    expected_constants = {
        Fraction(64),
        Fraction(-32),
        Fraction(-128, 3),
        Fraction(56),
        Fraction(-152, 3),
        Fraction(264, 5),
        Fraction(752, 15),
        Fraction(-1040, 21),
    }

    for depth in range(args.max_depth + 1):
        partial_sum += coefficient(depth) / 16**depth
        if depth < 2:
            continue
        r = valuation(depth + 1, 2)
        k_exponent = 4 * depth - r
        assert valuation(partial_sum.denominator, 2) == k_exponent
        odd_denominator = partial_sum.denominator >> k_exponent
        numerator = partial_sum.numerator
        dyadic_bits = k_exponent - 4
        dyadic_modulus = 1 << dyadic_bits
        w = numerator * pow(odd_denominator, -1, dyadic_modulus) % dyadic_modulus
        c = (numerator - odd_denominator * w) // dyadic_modulus
        assert gcd(c, odd_denominator) == 1
        y = Fraction(w, dyadic_modulus)
        quotient = Fraction(c, odd_denominator)
        assert 16 * partial_sum == y + quotient

        if previous is not None:
            old_depth = depth - 1
            old_r = int(previous["r"])
            old_w = int(previous["w"])
            old_y = previous["y"]
            old_q = previous["q"]
            assert isinstance(old_y, Fraction)
            assert isinstance(old_q, Fraction)

            modulus = 1 << (4 * old_depth)
            alpha = rational_mod(coefficient(depth), modulus)
            carried = (alpha + (1 << (old_r + 4)) * old_w) % modulus
            assert carried % (1 << r) == 0
            assert carried >> r == w
            assert reflected_f_mod(depth + 1, 4 * old_depth) == (
                alpha + 16 * reflected_f_mod(depth, 4 * old_depth)
            ) % modulus
            carry_checks += 2

            increment = coefficient(depth) / 16 ** (depth - 1)
            assert quotient == old_q + increment + old_y - y
            quotient_checks += 1

        factors = factor_denominator(odd_denominator, primes)
        size_limit = 8 * depth + 5
        for prime in primes:
            if prime == 2 or prime > size_limit:
                continue
            expected_support = possible_support(depth, prime)
            observed_raw_support = any(
                factor % prime == 0
                for index in range(depth + 1)
                for factor in (
                    2 * index + 1,
                    4 * index + 3,
                    8 * index + 1,
                    8 * index + 5,
                )
            )
            assert expected_support == observed_raw_support
            support_shape_checks += 1

        for prime, exponent in factors.items():
            if prime > 5:
                assert exponent <= floor_log(prime, size_limit)
            else:
                assert exponent <= 4 * floor_log(prime, size_limit)
            exponent_bound_checks += 1

        selected_primes: list[int] = []
        xi = Fraction()
        for prime in primes:
            if prime <= 5 or prime * prime <= size_limit or prime > size_limit:
                continue
            local = localization(depth, prime)
            if not possible_support(depth, prime):
                assert local == 0
                scaled = 16 * prime * partial_sum
                assert scaled.denominator % prime
                assert rational_mod(scaled, prime) == 0
                continue
            assert local
            assert (local > 0) == (prime % 4 == 1)
            scaled = 16 * prime * partial_sum
            assert scaled.denominator % prime
            local_mod = rational_mod(local, prime)
            direct_mod = rational_mod(scaled, prime)
            assert local_mod == direct_mod
            survives = factors.get(prime, 0) == 1
            assert survives == (local_mod != 0)
            localization_checks += 1
            survival_equivalence_checks += 1
            if not survives:
                modular_cancellations.append((depth, prime))
                continue
            gamma = c * pow(odd_denominator // prime, -1, prime) % prime
            assert gamma == local_mod
            selected_primes.append(prime)
            xi += Fraction(gamma, prime)

            max_multiplier = size_limit // prime
            common_denominator = (1 << (2 * max_multiplier)) * lcm_upto(
                max_multiplier
            )
            assert common_denominator % local.denominator == 0
            height_denominator_checks += 1

            if depth >= 48 and prime > depth:
                assert local in expected_constants
                eight_constant_checks += 1

        selected_product = 1
        for prime in selected_primes:
            selected_product *= prime
        assert odd_denominator % selected_product == 0
        cofactor = odd_denominator // selected_product
        assert gcd(selected_product, cofactor) == 1
        cofactor_factors = factor_denominator(cofactor, primes)
        assert all(
            prime <= 5 or prime * prime <= size_limit
            for prime in cofactor_factors
        ), (depth, size_limit, cofactor_factors, selected_primes)
        eta = 0 if cofactor == 1 else c * pow(selected_product, -1, cofactor) % cofactor
        assert (quotient - xi - Fraction(eta, cofactor)) % 1 == 0
        crt_checks += 1

        upper = decimal_upper(depth)
        if depth >= 5:
            direct_min: Fraction | None = None
            split_min: Fraction | None = None
            for exponent in range(depth, upper + 1):
                a_value = (10**exponent - 16) // 16
                direct_phase = (10**exponent - 16) * partial_sum
                split_phase = a_value * (y + xi + Fraction(eta, cofactor))
                assert (direct_phase - split_phase).denominator == 1
                direct_distance = circle_distance(direct_phase)
                split_distance = circle_distance(split_phase)
                assert direct_distance == split_distance
                direct_min = (
                    direct_distance
                    if direct_min is None
                    else min(direct_min, direct_distance)
                )
                split_min = (
                    split_distance
                    if split_min is None
                    else min(split_min, split_distance)
                )
                phase_checks += 1
            assert direct_min is not None and direct_min == split_min
            proportional_phase_checks += 1

        if depth == args.max_depth:
            full_mass = sum(
                log(prime)
                for prime in primes
                if prime != 2 and possible_support(depth, prime)
            )
            above_mass = sum(
                log(prime)
                for prime in primes
                if prime > depth and possible_support(depth, prime)
            )
            last_full_support_mass = full_mass / depth
            last_above_depth_mass = above_mass / depth

        previous = {"r": r, "w": w, "y": y, "q": quotient}

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"primary_report_sha256={PRIMARY_REPORT_SHA256}")
    print(f"primary_checker_sha256={PRIMARY_CHECKER_SHA256}")
    print(f"floor_choice_checks={floor_choice_checks}")
    print(f"block_order_checks={block_order_checks}")
    print(f"uniform_absolute_sum_checks={uniform_absolute_sum_checks}")
    print(f"carry_and_functional_checks={carry_checks}")
    print(f"quotient_recurrence_checks={quotient_checks}")
    print(f"localization_checks={localization_checks}")
    print(f"survival_equivalence_checks={survival_equivalence_checks}")
    print(f"eight_constant_checks={eight_constant_checks}")
    print(f"height_denominator_checks={height_denominator_checks}")
    print(f"exponent_bound_checks={exponent_bound_checks}")
    print(f"support_shape_checks={support_shape_checks}")
    print(f"crt_decomposition_checks={crt_checks}")
    print(f"phase_factorization_checks={phase_checks}")
    print(f"proportional_phase_minimum_checks={proportional_phase_checks}")
    print(f"modular_cancellation_rows={len(modular_cancellations)}")
    print(f"first_modular_cancellations={modular_cancellations[:8]}")
    print(f"last_full_support_log_mass_over_M={last_full_support_mass:.12f}")
    print(f"last_p_gt_M_support_log_mass_over_M={last_above_depth_mass:.12f}")
    print("all independent exact checks passed")


if __name__ == "__main__":
    main()
