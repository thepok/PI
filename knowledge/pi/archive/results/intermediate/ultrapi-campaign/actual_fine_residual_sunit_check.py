#!/usr/bin/env python3
"""Exact checks for the actual fine-residual/S-unit audit.

All output has claim status ``experiment``.  The checker uses only integers
and ``fractions.Fraction``; it neither evaluates pi nor reads a digit table.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def fract(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def prime_factors_small(value: int) -> set[int]:
    """Distinct prime factors; inputs here are only O(max_j)."""
    value = abs(value)
    factors: set[int] = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        factors.add(value)
    return factors


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def band_exponent(j: int) -> int:
    bound = 12 * j + 3
    exponent = 0
    power = 1
    while 3 * power <= bound:
        power *= 3
        exponent += 1
    if not power <= bound < 3 * power:
        raise AssertionError((j, bound, exponent, power))
    return exponent


def local_fraction_mod(value: Fraction, modulus: int) -> int:
    if gcd(value.denominator, modulus) != 1:
        raise ValueError((value, modulus))
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def chi4(odd: int) -> int:
    if odd <= 0 or odd % 2 == 0:
        raise ValueError(odd)
    return 1 if odd % 4 == 1 else -1


def arctan_term(base: int, index: int) -> Fraction:
    odd = 2 * index + 1
    return Fraction(-1 if index & 1 else 1, odd * base**odd)


def six_term_window(base: int, start: int) -> Fraction:
    return sum((arctan_term(base, start + offset) for offset in range(6)), Fraction())


def explicit_forcing(j: int) -> Fraction:
    return 10 ** (j + 1) * (
        16 * six_term_window(5, 6 * j + 2)
        - 4 * six_term_window(239, 6 * j + 3)
    )


def forcing_linear_denominators(j: int) -> tuple[int, ...]:
    return tuple(
        [12 * j + 5 + 2 * offset for offset in range(6)]
        + [12 * j + 7 + 2 * offset for offset in range(6)]
    )


def denominator_has_only(value: int, allowed_primes: set[int]) -> bool:
    remainder = value
    for prime in sorted(allowed_primes):
        while remainder % prime == 0:
            remainder //= prime
    return remainder == 1


def machin_seeds(max_j: int) -> list[Fraction | None]:
    five_sum = Fraction()
    two_three_nine_sum = Fraction()
    five_count = 0
    two_three_nine_count = 0
    result: list[Fraction | None] = [None]
    for j in range(1, max_j + 1):
        next_five_count = 6 * j + 2
        for index in range(five_count, next_five_count):
            five_sum += arctan_term(5, index)
        five_count = next_five_count

        next_two_three_nine_count = 6 * j + 3
        for index in range(two_three_nine_count, next_two_three_nine_count):
            two_three_nine_sum += arctan_term(239, index)
        two_three_nine_count = next_two_three_nine_count
        result.append(10**j * (16 * five_sum - 4 * two_three_nine_sum))
    return result


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def seed_data(j: int, seed: Fraction) -> dict[str, int | Fraction]:
    point = fract(seed)
    denominator = point.denominator
    numerator = point.numerator
    exponent = band_exponent(j)
    primary = 3 ** (exponent - 1)
    if valuation(denominator, 3) != exponent - 1:
        raise AssertionError(("three-primary denominator", j))
    depth = exponent // 2
    depth_modulus = 3**depth
    grid_size = primary // depth_modulus
    fine_modulus = denominator // primary
    if fine_modulus % 3 == 0:
        raise AssertionError(("fine modulus", j))
    fine = numerator % fine_modulus
    coarse = numerator // fine_modulus
    leading = local_fraction_mod(primary * seed, depth_modulus)
    selected = coarse % depth_modulus
    residual_numerator = fine_modulus * (selected - leading) + fine
    if residual_numerator % depth_modulus:
        raise AssertionError(("residual integrality", j))
    residual = residual_numerator // depth_modulus
    beta = fract(grid_size * point)
    if beta != Fraction(leading, depth_modulus) + Fraction(residual, fine_modulus):
        raise AssertionError(("phase recombination", j))
    if fract(Fraction(residual, fine_modulus) - (grid_size * seed - Fraction(leading, depth_modulus))):
        raise AssertionError(("circular character identity", j))
    return {
        "point": point,
        "denominator": denominator,
        "numerator": numerator,
        "exponent": exponent,
        "primary": primary,
        "depth": depth,
        "depth_modulus": depth_modulus,
        "grid_size": grid_size,
        "fine_modulus": fine_modulus,
        "fine": fine,
        "coarse": coarse,
        "leading": leading,
        "selected": selected,
        "residual": residual,
        "beta": beta,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=100)
    parser.add_argument("--pulse-steps", type=int, default=24)
    args = parser.parse_args()
    if args.max_j < 3 or args.pulse_steps < 1:
        raise SystemExit("need --max-j >= 3 and --pulse-steps >= 1")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    if digest != SOURCE_SHA256:
        raise AssertionError(("target hash", digest))

    seeds = machin_seeds(args.max_j + 1)
    data: list[dict[str, int | Fraction] | None] = [None] * (args.max_j + 2)
    seed_identity_checks = 0
    pulse_residual_checks = 0
    forcing_window_checks = 0
    forcing_support_checks = 0
    cross_index_checks = 0
    shared_prime_affine_checks = 0
    high_prime_local_checks = 0
    shared_upper_prime_persistence_checks = 0
    shared_crt_normalization_checks = 0
    fixed_shared_factor_recurrence_checks = 0
    forcing_support: set[int] = {2, 5, 239}

    for j in range(2, args.max_j + 2):
        seed = seeds[j]
        assert seed is not None
        datum = seed_data(j, seed)
        data[j] = datum
        seed_identity_checks += 1

        if j > args.max_j:
            continue
        denominator = int(datum["denominator"])
        numerator = int(datum["numerator"])
        depth_modulus = int(datum["depth_modulus"])
        grid_size = int(datum["grid_size"])
        fine_modulus = int(datum["fine_modulus"])
        leading = int(datum["leading"])
        residual = int(datum["residual"])

        for step in range(args.pulse_steps + 1):
            pulse_numerator = pow(10, step, denominator) * numerator % denominator
            pulse_point = Fraction(pulse_numerator, denominator)
            pulse_beta = fract(grid_size * pulse_point)
            pulse_leading = pow(10, step, depth_modulus) * leading % depth_modulus
            pulse_residual_fraction = pulse_beta - Fraction(pulse_leading, depth_modulus)
            pulse_residual_value = pulse_residual_fraction * fine_modulus
            if pulse_residual_value.denominator != 1:
                raise AssertionError(("pulse residual integrality", j, step))
            pulse_residual = pulse_residual_value.numerator
            if pulse_residual % fine_modulus != pow(10, step, fine_modulus) * residual % fine_modulus:
                raise AssertionError(("pulse residual orbit", j, step))
            if step < args.pulse_steps:
                next_leading = 10 * pulse_leading % depth_modulus
                leading_carry = (10 * pulse_leading - next_leading) // depth_modulus
                decimal_carry = floor_fraction(10 * pulse_beta)
                next_numerator = 10 * pulse_numerator % denominator
                next_beta = fract(grid_size * Fraction(next_numerator, denominator))
                next_residual_value = (
                    next_beta - Fraction(next_leading, depth_modulus)
                ) * fine_modulus
                if next_residual_value.denominator != 1:
                    raise AssertionError(("next residual integrality", j, step))
                if next_residual_value.numerator != (
                    10 * pulse_residual
                    + fine_modulus * (leading_carry - decimal_carry)
                ):
                    raise AssertionError(("pulse affine recurrence", j, step))
                pulse_residual_checks += 1

        bound = 12 * j + 3
        c_one = Fraction(3804, 1195)
        for prime in primes_up_to(bound):
            if not (2 * prime > bound and prime not in (239, 317)):
                continue
            if valuation(denominator, prime) != 1:
                raise AssertionError(("upper-half survival", j, prime))
            local_unit = local_fraction_mod(prime * seed, prime)
            expected_unit = (
                pow(10, j, prime)
                * chi4(prime)
                * local_fraction_mod(c_one, prime)
            ) % prime
            if local_unit != expected_unit:
                raise AssertionError(("upper-half unit", j, prime))
            fine_cofactor = fine_modulus // prime
            residual_local = residual * pow(fine_cofactor, -1, prime) % prime
            expected_residual_local = grid_size * local_unit % prime
            if residual_local != expected_residual_local:
                raise AssertionError(("residual local component", j, prime))
            high_prime_local_checks += 1

    for j in range(2, args.max_j + 1):
        current = data[j]
        following = data[j + 1]
        seed = seeds[j]
        next_seed = seeds[j + 1]
        assert current is not None and following is not None
        assert seed is not None and next_seed is not None
        forcing = next_seed - 10 * seed
        expected_forcing = explicit_forcing(j)
        if forcing != expected_forcing:
            raise AssertionError(("twelve-term forcing", j))
        forcing_window_checks += 1

        allowed = {2, 5, 239}
        for linear in forcing_linear_denominators(j):
            allowed.update(prime_factors_small(linear))
        if not denominator_has_only(forcing.denominator, allowed):
            raise AssertionError(("forcing denominator support", j))
        forcing_support.update(allowed)
        forcing_support_checks += 1

        grid_size = int(current["grid_size"])
        next_grid_size = int(following["grid_size"])
        if next_grid_size % grid_size:
            raise AssertionError(("grid-size ratio", j))
        sigma = next_grid_size // grid_size
        if sigma not in (1, 3):
            raise AssertionError(("grid-size ratio value", j, sigma))
        beta = current["beta"]
        next_beta = following["beta"]
        assert isinstance(beta, Fraction) and isinstance(next_beta, Fraction)
        affine = 10 * sigma * beta + next_grid_size * forcing
        if next_beta != fract(affine):
            raise AssertionError(("cross-index beta", j))
        carry = floor_fraction(affine)
        leading = int(current["leading"])
        modulus = int(current["depth_modulus"])
        next_leading = int(following["leading"])
        next_modulus = int(following["depth_modulus"])
        omega = (
            Fraction(10 * sigma * leading, modulus)
            + next_grid_size * forcing
            - Fraction(next_leading, next_modulus)
        )
        residual = int(current["residual"])
        fine_modulus = int(current["fine_modulus"])
        next_residual = int(following["residual"])
        next_fine_modulus = int(following["fine_modulus"])
        if Fraction(next_residual, next_fine_modulus) != (
            Fraction(10 * sigma * residual, fine_modulus) + omega - carry
        ):
            raise AssertionError(("cross-index residual recurrence", j))
        if fract(
            Fraction(next_residual, next_fine_modulus)
            - Fraction(10 * sigma * residual, fine_modulus)
            - omega
        ):
            raise AssertionError(("cross-index character recurrence", j))
        cross_index_checks += 1

        for prime in primes_up_to(12 * j + 17):
            if prime == 3:
                continue
            if valuation(int(current["denominator"]), prime) != 1:
                continue
            if valuation(int(following["denominator"]), prime) != 1:
                continue
            scaled_forcing = prime * forcing
            if scaled_forcing.denominator % prime == 0:
                continue
            current_local = residual * pow(fine_modulus // prime, -1, prime) % prime
            next_local = (
                next_residual
                * pow(next_fine_modulus // prime, -1, prime)
            ) % prime
            forcing_local = local_fraction_mod(scaled_forcing, prime)
            if next_local != (
                10 * sigma * current_local
                + next_grid_size * forcing_local
            ) % prime:
                raise AssertionError(("shared-prime affine recurrence", j, prime))
            shared_prime_affine_checks += 1

    # A genuinely actual-Machin specialization, stronger than the generic
    # residual-lift algebra: every upper-half seed prime is shared throughout
    # a uniform block before the first possible new odd multiple 3*p enters a
    # forcing window.  On their product the normalized residual coordinate
    # has a fixed-modulus multiplicative recurrence.
    for start in range(2, args.max_j):
        bound = 12 * start + 3
        transitions = min((bound - 4) // 24, args.max_j - start)
        if transitions < 1:
            continue
        shared_primes = [
            prime
            for prime in primes_up_to(bound)
            if 2 * prime > bound and prime not in (239, 317)
        ]
        shared_factor = 1
        for prime in shared_primes:
            shared_factor *= prime
        if shared_factor == 1:
            continue
        for offset in range(transitions):
            index = start + offset
            current = data[index]
            following = data[index + 1]
            seed = seeds[index]
            next_seed = seeds[index + 1]
            assert current is not None and following is not None
            assert seed is not None and next_seed is not None
            forcing = next_seed - 10 * seed
            current_fine_modulus = int(current["fine_modulus"])
            next_fine_modulus = int(following["fine_modulus"])
            if current_fine_modulus % shared_factor or next_fine_modulus % shared_factor:
                raise AssertionError(("fixed shared factor divisibility", start, index))
            if gcd(current_fine_modulus // shared_factor, shared_factor) != 1:
                raise AssertionError(("current shared factor multiplicity", start, index))
            if gcd(next_fine_modulus // shared_factor, shared_factor) != 1:
                raise AssertionError(("next shared factor multiplicity", start, index))
            current_residual = int(current["residual"])
            next_residual = int(following["residual"])
            current_coordinate = (
                current_residual
                * pow(current_fine_modulus // shared_factor, -1, shared_factor)
            ) % shared_factor
            next_coordinate = (
                next_residual
                * pow(next_fine_modulus // shared_factor, -1, shared_factor)
            ) % shared_factor
            for prime in shared_primes:
                if valuation(int(current["denominator"]), prime) != 1:
                    raise AssertionError(("current shared prime", start, index, prime))
                if valuation(int(following["denominator"]), prime) != 1:
                    raise AssertionError(("persistent shared prime", start, index, prime))
                local_forcing = local_fraction_mod(prime * forcing, prime)
                if local_forcing != 0:
                    raise AssertionError(("upper-prime forcing integrality", start, index, prime))
                current_local = (
                    current_residual
                    * pow(current_fine_modulus // prime, -1, prime)
                ) % prime
                next_local = (
                    next_residual
                    * pow(next_fine_modulus // prime, -1, prime)
                ) % prime
                if current_coordinate % prime != shared_factor // prime * current_local % prime:
                    raise AssertionError(("current CRT normalization", start, index, prime))
                if next_coordinate % prime != shared_factor // prime * next_local % prime:
                    raise AssertionError(("next CRT normalization", start, index, prime))
                shared_upper_prime_persistence_checks += 1
                shared_crt_normalization_checks += 2
            current_grid_size = int(current["grid_size"])
            next_grid_size = int(following["grid_size"])
            sigma = next_grid_size // current_grid_size
            if next_coordinate != 10 * sigma * current_coordinate % shared_factor:
                raise AssertionError(("fixed shared-factor recurrence", start, index))
            fixed_shared_factor_recurrence_checks += 1

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"j_range=2..{args.max_j}")
    print(f"balanced_seed_character_identities={seed_identity_checks - 1}")
    print(f"within_pulse_residual_recurrences={pulse_residual_checks}")
    print(f"twelve_term_forcing_windows={forcing_window_checks}")
    print(f"forcing_denominator_support_checks={forcing_support_checks}")
    print(f"cross_index_residual_recurrences={cross_index_checks}")
    print(f"shared_prime_affine_recurrences={shared_prime_affine_checks}")
    print(f"upper_half_local_residual_components={high_prime_local_checks}")
    print(
        "shared_upper_prime_persistence_checks="
        f"{shared_upper_prime_persistence_checks}"
    )
    print(f"shared_crt_normalization_checks={shared_crt_normalization_checks}")
    print(
        "fixed_shared_factor_recurrences="
        f"{fixed_shared_factor_recurrence_checks}"
    )
    print(f"observed_forcing_support_rank={len(forcing_support)}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
