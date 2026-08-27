#!/usr/bin/env python3
"""Exact finite replay for the actual BBP odd-quotient attack.

Every output has claim status experiment. The script verifies rational and
modular identities only. It does not prove the two-adic analytic input, the
PNT estimates, an exponential-sum estimate, a fixed return, or V1.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd, log, log10
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
PARENT_REPORT_SHA256 = (
    "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d"
)


def work_root() -> Path:
    return Path(__file__).resolve().parents[2]


def source_path() -> Path:
    return work_root() / "problems/local/pi-digits.txt"


def parent_report_path() -> Path:
    return (
        work_root()
        / "work/ultrapi-resume/bbp_short_orbit_return_attack.md"
    )


def v_p(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("v_p(0) is not used in this finite replay")
    answer = 0
    integer = abs(integer)
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


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def rational_mod_two_power(value: Fraction, bits: int) -> int:
    if bits <= 0:
        return 0
    modulus = 1 << bits
    assert value.denominator & 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def reflected_f_mod(argument: int, bits: int) -> int:
    if bits <= 0:
        return 0
    modulus = 1 << bits
    answer = 0
    for offset in range((bits + 3) // 4):
        answer += pow(16, offset, modulus) * rational_mod_two_power(
            coefficient(argument - 1 - offset), bits
        )
    return answer % modulus


def clean_bands(
    depth: int, primes: list[int]
) -> tuple[list[int], list[int]]:
    positive: list[int] = []
    negative: list[int] = []
    for prime in primes:
        first_band = (
            4 * depth + 3 < prime <= 8 * depth + 1
            and prime % 8 == 1
        ) or (
            4 * depth + 3 < prime <= 8 * depth + 5
            and prime % 8 == 5
        )
        second_band = (
            3 * prime > 8 * depth + 5 and prime <= 4 * depth + 3
        )
        if first_band:
            positive.append(prime)
        elif second_band:
            if prime % 4 == 1:
                positive.append(prime)
            else:
                assert prime % 4 == 3
                negative.append(prime)
    return positive, negative


def high_prime_coordinate_constant(depth: int, prime: int) -> Fraction:
    """Localized additive CRT constant when the multipliers are p-units."""
    assert prime > 5
    answer = Fraction()

    # A factor 2*k+1 = m*p.
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))

    # A factor 4*k+3 = m*p.
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            if multiplier <= 6:
                answer -= Fraction(2 ** (6 - multiplier), multiplier)
            else:
                answer -= Fraction(
                    1, multiplier * 2 ** (multiplier - 6)
                )

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


def factor_over_primes(
    integer: int, primes: list[int]
) -> dict[int, int]:
    remaining = integer
    answer: dict[int, int] = {}
    for prime in primes:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            answer[prime] = exponent
        if remaining == 1:
            break
    assert remaining == 1
    return answer


def circle_distance(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=240)
    args = parser.parse_args()
    if args.max_depth < 30:
        raise SystemExit("--max-depth must be at least 30")

    source_digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    parent_digest = hashlib.sha256(
        parent_report_path().read_bytes()
    ).hexdigest()
    assert source_digest == SOURCE_SHA256
    assert parent_digest == PARENT_REPORT_SHA256

    primes = primes_through(8 * args.max_depth + 5)
    partial_sum = Fraction()

    previous_state: dict[str, object] | None = None
    functional_equation_checks = 0
    carry_recurrence_checks = 0
    quotient_recurrence_checks = 0
    clean_coordinate_checks = 0
    high_coordinate_checks = 0
    generic_localization_checks = 0
    rational_localization_sign_checks = 0
    height_protected_nonvanishing_checks = 0
    genuine_mod_p_local_cancellations: list[tuple[int, int]] = []
    cofactor_support_checks = 0
    crt_decomposition_checks = 0
    phase_factorization_checks = 0
    compensation_checks = 0
    large_dyadic_jumps = 0
    proportional_minima: dict[int, tuple[int, Fraction]] = {}
    cofactor_log_ratio = 0.0
    signed_clean_component = Fraction()
    signed_high_component = Fraction()

    for depth in range(args.max_depth + 1):
        partial_sum += coefficient(depth) / 16**depth
        if depth < 2:
            continue

        r = v_p(depth + 1, 2)
        k_exponent = 4 * depth - r
        assert v_p(partial_sum.denominator, 2) == k_exponent
        odd_denominator = partial_sum.denominator >> k_exponent
        numerator = partial_sum.numerator
        dyadic_bits = k_exponent - 4
        dyadic_modulus = 1 << dyadic_bits
        dyadic_coordinate = (
            numerator * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            numerator - odd_denominator * dyadic_coordinate
        ) // dyadic_modulus
        assert odd_numerator * dyadic_modulus + (
            odd_denominator * dyadic_coordinate
        ) == numerator
        assert gcd(odd_numerator, odd_denominator) == 1

        x_value = 16 * partial_sum
        y_value = Fraction(dyadic_coordinate, dyadic_modulus)
        quotient = Fraction(odd_numerator, odd_denominator)
        quotient_fractional = Fraction(
            odd_numerator % odd_denominator, odd_denominator
        )
        assert x_value == y_value + quotient
        assert quotient_fractional == (x_value - y_value) % 1

        f_bits = r + dyadic_bits
        reflected = reflected_f_mod(depth + 1, f_bits)
        assert reflected % (1 << r) == 0
        assert (reflected >> r) % dyadic_modulus == dyadic_coordinate

        if previous_state is not None:
            previous_depth = depth - 1
            previous_r = int(previous_state["r"])
            previous_w = int(previous_state["w"])
            previous_y = previous_state["y"]
            previous_q = previous_state["q"]
            previous_z = previous_state["z"]
            previous_x = previous_state["x"]
            assert isinstance(previous_y, Fraction)
            assert isinstance(previous_q, Fraction)
            assert isinstance(previous_z, Fraction)
            assert isinstance(previous_x, Fraction)

            transition_bits = 4 * previous_depth
            transition_modulus = 1 << transition_bits
            coefficient_residue = rational_mod_two_power(
                coefficient(depth), transition_bits
            )
            assert reflected_f_mod(depth + 1, transition_bits) == (
                16 * reflected_f_mod(depth, transition_bits)
                + coefficient_residue
            ) % transition_modulus
            functional_equation_checks += 1
            carried = (
                coefficient_residue
                + (1 << (previous_r + 4)) * previous_w
            ) % transition_modulus
            assert carried % (1 << r) == 0
            predicted_w = carried >> r
            assert predicted_w == dyadic_coordinate
            carry_recurrence_checks += 1

            increment = coefficient(depth) / 16 ** (depth - 1)
            assert quotient == (
                previous_q + increment + previous_y - y_value
            )
            quotient_recurrence_checks += 1

            assert (
                quotient_fractional
                - previous_z
                + y_value
                - previous_y
                - increment
            ) % 1 == 0
            assert x_value - previous_x == increment
            compensation_checks += 2
            if circle_distance(y_value - previous_y) > Fraction(1, 4):
                large_dyadic_jumps += 1

        positive_primes, negative_primes = clean_bands(depth, primes)
        clean_product = 1
        signed_clean_component = Fraction()
        for prime in positive_primes:
            clean_product *= prime
            assert v_p(odd_denominator, prime) == 1
            gamma = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            assert gamma == 64 % prime
            signed_clean_component += Fraction(64, prime)
            clean_coordinate_checks += 1
        for prime in negative_primes:
            clean_product *= prime
            assert v_p(odd_denominator, prime) == 1
            gamma = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            assert gamma == (-32) % prime
            signed_clean_component -= Fraction(32, prime)
            clean_coordinate_checks += 1

        assert odd_denominator % clean_product == 0
        cofactor = odd_denominator // clean_product
        assert gcd(clean_product, cofactor) == 1
        cofactor_factors = factor_over_primes(cofactor, primes)
        support_limit = (8 * depth + 5) // 3
        size_limit = 8 * depth + 5
        for prime, exponent in cofactor_factors.items():
            assert prime <= support_limit
            if prime > 5:
                assert exponent <= floor_log(prime, size_limit)
            else:
                assert exponent <= 4 * floor_log(prime, size_limit)
            cofactor_support_checks += 1

        if cofactor == 1:
            cofactor_coordinate = 0
        else:
            cofactor_coordinate = (
                odd_numerator * pow(clean_product, -1, cofactor)
            ) % cofactor
        reconstructed = (
            signed_clean_component
            + Fraction(cofactor_coordinate, cofactor)
        )
        assert (quotient - reconstructed) % 1 == 0
        crt_decomposition_checks += 1

        # General localization criterion above sqrt(8M+5).  Here every
        # singular linear factor has p-adic order exactly one, and all
        # multipliers in the localized rational sum are p-units.
        for prime in primes:
            if (
                prime <= 5
                or prime * prime <= size_limit
                or prime > size_limit
            ):
                continue
            constant = high_prime_coordinate_constant(depth, prime)
            if not constant:
                continue
            assert (constant > 0) == (prime % 4 == 1)
            rational_localization_sign_checks += 1
            predicted_gamma = (
                constant.numerator
                * pow(constant.denominator, -1, prime)
            ) % prime
            if max(abs(constant.numerator), constant.denominator) < prime:
                assert predicted_gamma
                height_protected_nonvanishing_checks += 1
            if predicted_gamma:
                assert v_p(odd_denominator, prime) == 1
                gamma = (
                    odd_numerator
                    * pow(odd_denominator // prime, -1, prime)
                ) % prime
                assert gamma == predicted_gamma
            else:
                assert odd_denominator % prime
                genuine_mod_p_local_cancellations.append((depth, prime))
            generic_localization_checks += 1

        # The full four-pole localization remains explicit for every possible
        # denominator prime above the depth, not only for the two clean bands.
        high_product = 1
        signed_high_component = Fraction()
        if depth >= 48:
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
            for prime in primes:
                if prime <= depth or prime > 8 * depth + 5:
                    continue
                constant = high_prime_coordinate_constant(depth, prime)
                if not constant:
                    continue
                assert constant in expected_constants
                assert v_p(odd_denominator, prime) == 1
                gamma = (
                    odd_numerator
                    * pow(odd_denominator // prime, -1, prime)
                ) % prime
                predicted_gamma = (
                    constant.numerator
                    * pow(constant.denominator, -1, prime)
                ) % prime
                assert gamma == predicted_gamma
                high_product *= prime
                signed_gamma = gamma if 2 * gamma <= prime else gamma - prime
                signed_high_component += Fraction(signed_gamma, prime)
                high_coordinate_checks += 1

            assert odd_denominator % high_product == 0
            high_cofactor = odd_denominator // high_product
            assert gcd(high_product, high_cofactor) == 1
            high_cofactor_factors = factor_over_primes(
                high_cofactor, primes
            )
            for prime, exponent in high_cofactor_factors.items():
                assert prime <= depth
                if prime > 5:
                    assert exponent <= floor_log(prime, size_limit)
                else:
                    assert exponent <= 4 * floor_log(prime, size_limit)
                cofactor_support_checks += 1

            if high_cofactor == 1:
                high_cofactor_coordinate = 0
            else:
                high_cofactor_coordinate = (
                    odd_numerator
                    * pow(high_product, -1, high_cofactor)
                ) % high_cofactor
            assert (
                quotient
                - signed_high_component
                - Fraction(high_cofactor_coordinate, high_cofactor)
            ) % 1 == 0
            crt_decomposition_checks += 1
        else:
            high_cofactor = cofactor
            high_cofactor_coordinate = cofactor_coordinate
            signed_high_component = signed_clean_component

        positive_reciprocals = sum(
            (Fraction(1, prime) for prime in positive_primes), Fraction()
        )
        negative_reciprocals = sum(
            (Fraction(1, prime) for prime in negative_primes), Fraction()
        )
        clean_power_coefficient = (
            4 * positive_reciprocals - 2 * negative_reciprocals
        )
        assert signed_clean_component == 16 * clean_power_coefficient

        upper = int(log10(16) * depth)
        if depth >= 5:
            best_distance: Fraction | None = None
            best_exponent = -1
            for decimal_exponent in range(depth, upper + 1):
                a_value = (10**decimal_exponent - 16) // 16
                direct_phase = (10**decimal_exponent - 16) * partial_sum
                split_phase = a_value * (
                    y_value
                    + signed_high_component
                    + Fraction(
                        high_cofactor_coordinate, high_cofactor
                    )
                )
                assert circle_distance(direct_phase) == circle_distance(
                    split_phase
                )
                assert a_value * signed_clean_component == (
                    10**decimal_exponent * clean_power_coefficient
                    - signed_clean_component
                )
                phase_factorization_checks += 2
                distance = circle_distance(direct_phase)
                if best_distance is None or distance < best_distance:
                    best_distance = distance
                    best_exponent = decimal_exponent
            assert best_distance is not None
            proportional_minima[depth] = (best_exponent, best_distance)

        if depth == args.max_depth:
            cofactor_log_ratio = log(high_cofactor) / depth

        previous_state = {
            "r": r,
            "w": dyadic_coordinate,
            "y": y_value,
            "q": quotient,
            "z": quotient_fractional,
            "x": x_value,
        }

    before = proportional_minima[20][1]
    after = proportional_minima[21][1]
    assert after > before

    record_depth, (record_exponent, record_distance) = min(
        proportional_minima.items(), key=lambda item: item[1][1]
    )

    print("claim_status=experiment")
    print(f"source_sha256={source_digest}")
    print(f"parent_report_sha256={parent_digest}")
    print(f"functional_equation_checks={functional_equation_checks}")
    print(f"carry_recurrence_checks={carry_recurrence_checks}")
    print(f"quotient_recurrence_checks={quotient_recurrence_checks}")
    print(f"clean_crt_coordinate_checks={clean_coordinate_checks}")
    print(f"all_high_prime_coordinate_checks={high_coordinate_checks}")
    print(f"generic_localization_checks={generic_localization_checks}")
    print(
        "rational_localization_sign_checks="
        f"{rational_localization_sign_checks}"
    )
    print(
        "height_protected_nonvanishing_checks="
        f"{height_protected_nonvanishing_checks}"
    )
    print(
        "genuine_mod_p_local_cancellation_rows="
        f"{len(genuine_mod_p_local_cancellations)}"
    )
    print(
        "first_genuine_mod_p_local_cancellations="
        f"{genuine_mod_p_local_cancellations[:8]}"
    )
    print(f"cofactor_support_checks={cofactor_support_checks}")
    print(f"crt_decomposition_checks={crt_decomposition_checks}")
    print(f"phase_factorization_checks={phase_factorization_checks}")
    print(f"compensation_checks={compensation_checks}")
    print(f"large_dyadic_jumps_over_one_quarter={large_dyadic_jumps}")
    print(f"last_p_gt_M_cofactor_log_ratio={cofactor_log_ratio:.15f}")
    print(
        "last_p_gt_M_signed_component="
        f"{float(signed_high_component):.15f}"
    )
    print(
        "proportional_monotonicity_falsifier="
        f"M20:{float(before):.15f}->M21:{float(after):.15f}"
    )
    print(
        "finite_proportional_record="
        f"M{record_depth}:n{record_exponent}:"
        f"{float(record_distance):.15f}"
    )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
