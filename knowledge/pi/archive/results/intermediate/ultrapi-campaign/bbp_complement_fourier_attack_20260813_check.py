#!/usr/bin/env python3
"""Independent bounded replay for the BBP complement-Fourier attack.

All structural checks use exact integers or ``gmpy2.mpq``.  Complex floating
point is used only for the explicitly labelled finite Fourier diagnostics.
The script imports no other branch checker.
"""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from pathlib import Path

import gmpy2
import numpy as np
from gmpy2 import mpq, mpz


ROOT = Path(__file__).resolve().parents[2]
FROZEN = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md":
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_audit.md":
        "44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81",
    "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md":
        "23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d",
    "work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md":
        "47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564",
    "work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813.md":
        "3ff784ebad18c8dda7c63691ba99120f80299953361362f7d2f2f8cd26f89d3f",
    "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md":
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    "work/ultrapi-resume/bbp_three_primary_decimation_20260813.md":
        "29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_upto(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (
                (limit - start) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def valuation(value: int | mpz, prime: int) -> int:
    value = mpz(value)
    if prime == 2:
        assert value != 0
        return int(gmpy2.bit_scan1(abs(value)))
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def factor_over_bound(value: int | mpz, bound: int) -> dict[int, int]:
    remainder = mpz(value)
    factors: dict[int, int] = {}
    for prime in primes_upto(bound):
        exponent = 0
        while remainder % prime == 0:
            remainder //= prime
            exponent += 1
        if exponent:
            factors[prime] = exponent
    assert remainder == 1
    return factors


def bbp_partial_sum(depth: int) -> mpq:
    total = mpq(0)
    power16 = mpz(1)
    for k in range(depth + 1):
        pole_sum = (
            mpq(4, 8 * k + 1)
            - mpq(1, 2 * (2 * k + 1))
            - mpq(1, 8 * k + 5)
            - mpq(1, 2 * (4 * k + 3))
        )
        total += pole_sum / power16
        power16 *= 16
    return total


def high_coordinate(depth: int, prime: int) -> mpq:
    """The six exact p>M rows from the frozen localization."""

    residue = prime % 4
    assert residue in (1, 3)
    if 3 * prime > 8 * depth + 5:
        return mpq(64 if residue == 1 else -32)
    if prime > 2 * depth + 1:
        return mpq(64) if residue == 1 else mpq(-128, 3)
    if 5 * prime > 8 * depth + 5:
        return mpq(56) if residue == 1 else mpq(-152, 3)
    if 3 * prime > 4 * depth + 3:
        return mpq(264, 5) if residue == 1 else mpq(-152, 3)
    if 7 * prime > 8 * depth + 5:
        return mpq(752, 15) if residue == 1 else mpq(-152, 3)
    return mpq(752, 15) if residue == 1 else mpq(-1040, 21)


def unit_phase(numerator: int | mpz, denominator: int | mpz) -> complex:
    denominator = mpz(denominator)
    residue = mpz(numerator) % denominator
    angle = 2.0 * math.pi * float(mpq(residue, denominator))
    return cmath.exp(1j * angle)


def is_integer(value: mpq) -> bool:
    return value.denominator == 1


def row_replay(epoch: int, counters: dict[str, int]) -> dict[str, object]:
    period = 3 ** (epoch - 2)
    block = period // 9
    depth = 5 * (3**epoch - 1) // 8 - 1
    bbp = bbp_partial_sum(depth)
    numerator = mpz(bbp.numerator)
    denominator = mpz(bbp.denominator)
    factors = factor_over_bound(denominator, 8 * depth + 5)

    two_exponent = factors[2]
    three_exponent = factors[3]
    five_exponent = factors[5]
    expected_five_exponent = 0
    five_power = 1
    while five_power * 5 <= 8 * depth + 5:
        five_power *= 5
        expected_five_exponent += 1
    assert two_exponent == 4 * depth - valuation(depth + 1, 2)
    assert three_exponent == epoch
    assert five_exponent == expected_five_exponent
    counters["denominator_factor_checks"] += len(factors)

    odd_denominator = denominator // (2**two_exponent)
    dyadic_denominator = mpz(2) ** (two_exponent - 4)
    dyadic_coordinate = (
        numerator
        * pow(int(odd_denominator), -1, int(dyadic_denominator))
    ) % dyadic_denominator
    assert dyadic_coordinate % 2 == 1
    odd_numerator = (
        numerator - odd_denominator * dyadic_coordinate
    ) // dyadic_denominator
    assert gmpy2.gcd(odd_numerator, odd_denominator) == 1

    q3 = mpz(3) ** three_exponent
    q5 = mpz(5) ** five_exponent
    high_primes = sorted(p for p in factors if p > depth)
    high_product = mpz(1)
    for prime in high_primes:
        assert factors[prime] == 1
        high_product *= prime

    small_cofactor = odd_denominator // (q3 * q5 * high_product)
    assert gmpy2.gcd(q3 * q5 * high_product, small_cofactor) == 1

    beta3 = (
        odd_numerator
        * pow(int(odd_denominator // q3), -1, int(q3))
    ) % q3
    beta5 = (
        odd_numerator
        * pow(int(odd_denominator // q5), -1, int(q5))
    ) % q5
    if small_cofactor == 1:
        beta0 = mpz(0)
    else:
        beta0 = (
            odd_numerator
            * pow(
                int(odd_denominator // small_cofactor),
                -1,
                int(small_cofactor),
            )
        ) % small_cofactor
    assert beta3 % 3 != 0
    assert beta5 % 5 != 0
    assert small_cofactor == 1 or gmpy2.gcd(beta0, small_cofactor) == 1

    high_phase = mpq(0)
    reciprocal_lift = mpq(0)
    grid_numerator = 0
    for prime in high_primes:
        rational_coordinate = high_coordinate(depth, prime)
        local_a = int(rational_coordinate.numerator)
        local_b = int(rational_coordinate.denominator)
        gamma = (
            odd_numerator
            * pow(int(odd_denominator // prime), -1, prime)
        ) % prime
        assert gamma == (local_a * pow(local_b, -1, prime)) % prime
        lift_digit = (
            (-local_a * pow(prime, -1, local_b)) % local_b
            if local_b > 1
            else 0
        )
        one_lift_error = (
            mpq(gamma, prime)
            - mpq(lift_digit, local_b)
            - mpq(local_a, local_b * prime)
        )
        assert is_integer(one_lift_error)
        high_phase += mpq(gamma, prime)
        reciprocal_lift += rational_coordinate / prime
        grid_numerator = (
            grid_numerator + (105 // local_b) * lift_digit
        ) % 105
        counters["high_coordinate_checks"] += 1
        counters["reciprocal_lift_checks"] += 1

    assert is_integer(
        high_phase - mpq(grid_numerator, 105) - reciprocal_lift
    )
    counters["high_grid_lift_checks"] += 1

    odd_crt_error = (
        mpq(odd_numerator, odd_denominator)
        - mpq(beta3, q3)
        - mpq(beta5, q5)
        - (mpq(beta0, small_cofactor) if small_cofactor > 1 else 0)
        - high_phase
    )
    assert is_integer(odd_crt_error)
    counters["odd_crt_checks"] += 1

    lift_numerator = mpz(reciprocal_lift.numerator)
    lift_denominator = mpz(reciprocal_lift.denominator)
    assert lift_denominator % high_product == 0
    counters["high_lift_denominator_checks"] += len(high_primes)

    # The exponent-coordinate primary support class.
    support_class = int(
        beta3
        * pow(16, -1, int(q3))
        * pow(10, depth, int(q3))
        % q3
        % 9
    )
    assert support_class in (1, 2, 4, 5, 7, 8)

    sequences: dict[str, list[complex]] = {
        key: []
        for key in (
            "primary",
            "dyadic",
            "five",
            "small",
            "grid",
            "lift",
            "hard",
            "complement",
            "full",
        )
    }
    a_value = mpz(2) ** (depth - 4) * mpz(5) ** depth - 1
    a_values: list[mpz] = []
    for offset in range(period):
        a_values.append(a_value)
        primary = unit_phase(a_value * beta3, q3)
        dyadic = unit_phase(a_value * dyadic_coordinate, dyadic_denominator)
        five = unit_phase(-beta5, q5)
        small = (
            unit_phase(a_value * beta0, small_cofactor)
            if small_cofactor > 1
            else 1.0 + 0.0j
        )
        grid = unit_phase(a_value * grid_numerator, 105)
        lift = unit_phase(a_value * lift_numerator, lift_denominator)
        hard = dyadic * small * lift
        complement = hard * five * grid
        full = primary * complement

        exact_phase_error = (
            a_value * 16 * bbp
            - mpq(a_value * dyadic_coordinate, dyadic_denominator)
            - mpq(a_value * beta3, q3)
            + mpq(beta5, q5)
            - (
                mpq(a_value * beta0, small_cofactor)
                if small_cofactor > 1
                else 0
            )
            - mpq(a_value * grid_numerator, 105)
            - a_value * reciprocal_lift
        )
        assert is_integer(exact_phase_error)
        assert a_value % q5 == q5 - 1
        counters["full_phase_decomposition_checks"] += 1
        counters["static_five_checks"] += 1

        sequences["primary"].append(primary)
        sequences["dyadic"].append(dyadic)
        sequences["five"].append(five)
        sequences["small"].append(small)
        sequences["grid"].append(grid)
        sequences["lift"].append(lift)
        sequences["hard"].append(hard)
        sequences["complement"].append(complement)
        sequences["full"].append(full)
        a_value = 10 * a_value + 9

    # The 1/105 grid contribution is exactly six-periodic.
    for offset in range(period):
        lhs = a_values[offset] * grid_numerator
        rhs_a = mpz(2) ** (depth + offset + 2) * mpz(5) ** (
            depth + offset + 6
        ) - 1
        # rhs_a is A_(depth+offset+6).
        assert (lhs - rhs_a * grid_numerator) % 105 == 0
        counters["six_period_grid_checks"] += 1

    # Exact nine-block primary relation.
    modulus9 = 9 * q3
    for u in range(block):
        for m in range(9):
            delta_a = a_values[u + m * block] - a_values[u]
            assert (
                9 * beta3 * delta_a
                - support_class * m * q3
            ) % modulus9 == 0
            counters["nine_block_primary_checks"] += 1

    primary_hat = np.fft.fft(np.asarray(sequences["primary"], dtype=complex))
    expected_magnitude = 3.0 * math.sqrt(period)
    for frequency, coefficient in enumerate(primary_hat):
        if frequency % 9 == support_class:
            assert abs(abs(coefficient) - expected_magnitude) < 2e-9
        else:
            assert abs(coefficient) < 2e-9
        counters["primary_fourier_support_checks"] += 1

    diagnostics: dict[str, dict[str, float]] = {}
    selected_indices = [
        (-frequency) % period
        for frequency in range(period)
        if frequency % 9 == support_class
    ]
    root9 = cmath.exp(2j * math.pi / 9)
    for name in ("dyadic", "small", "grid", "lift", "hard", "complement"):
        values = np.asarray(sequences[name], dtype=complex)
        transform = np.fft.fft(values)
        selected_energy = sum(
            abs(transform[index]) ** 2 for index in selected_indices
        )
        block_energy = block * sum(
            abs(
                sum(
                    values[u + m * block] * root9 ** (support_class * m)
                    for m in range(9)
                )
            )
            ** 2
            for u in range(block)
        )
        assert abs(selected_energy - block_energy) < 2e-9 * period**2
        direct_pairing = abs(
            sum(
                sequences["primary"][j] * values[j]
                for j in range(period)
            )
        ) / period
        cauchy_bound = math.sqrt(max(0.0, selected_energy)) / period
        assert direct_pairing <= cauchy_bound + 2e-11
        diagnostics[name] = {
            "energy_fraction": selected_energy / period**2,
            "cauchy_bound": cauchy_bound,
            "direct_pairing": direct_pairing,
        }
        counters["nine_block_energy_checks"] += block
        counters["selected_fourier_energy_checks"] += len(selected_indices)

    full_mean = abs(sum(sequences["full"])) / period
    assert abs(full_mean - diagnostics["complement"]["direct_pairing"]) < 2e-12

    # Each nonzero nine-block correlation retains an exact dyadic component
    # and almost all high-prime logarithmic mass.
    total_high_log = sum(math.log(prime) for prime in high_primes)
    maximum_killed_log = 0.0
    minimum_surviving_log = total_high_log
    for shift_blocks in range(1, 9):
        lag = shift_blocks * block
        repunit = mpz(10) ** lag - 1
        killed_product = mpz(1)
        killed_log = 0.0
        for prime in high_primes:
            if repunit % prime == 0:
                killed_product *= prime
                killed_log += math.log(prime)
            else:
                rational_coordinate = high_coordinate(depth, prime)
                gamma = (
                    int(rational_coordinate.numerator)
                    * pow(int(rational_coordinate.denominator), -1, prime)
                ) % prime
                assert gamma * int(repunit % prime) % prime != 0
                counters["active_high_correlation_checks"] += 1
        assert repunit % killed_product == 0
        assert killed_log < lag * math.log(10) + 1e-12
        maximum_killed_log = max(maximum_killed_log, killed_log)
        minimum_surviving_log = min(
            minimum_surviving_log, total_high_log - killed_log
        )
        counters["high_annihilation_budget_checks"] += 1

        for lower_block in range(9 - shift_blocks):
            start_offset = lower_block * block
            starting_exponent = depth + start_offset
            fixed_modulus_exponent = two_exponent - starting_exponent
            fixed_unit = (
                dyadic_coordinate
                * mpz(5) ** starting_exponent
                * repunit
            )
            assert valuation(fixed_unit, 2) == 0
            for u in range(block):
                n = starting_exponent + u
                left = a_values[start_offset + u]
                right = a_values[start_offset + u + lag]
                dyadic_difference = dyadic_coordinate * (right - left)
                assert valuation(dyadic_difference, 2) == n - 4
                assert two_exponent - 4 - valuation(dyadic_difference, 2) == (
                    two_exponent - n
                )
                # Fixed modulus/nonunit base 10, equivalently a pointwise
                # reduced varying modulus/unit base 5.
                assert (
                    dyadic_difference * (mpz(2) ** fixed_modulus_exponent)
                    == fixed_unit
                    * (mpz(10) ** u)
                    * (mpz(2) ** (two_exponent - 4))
                )
                assert fixed_modulus_exponent - u == two_exponent - n
                counters["dyadic_fixed_modulus_identity_checks"] += 1
                assert (right - left) % q5 == 0
                counters["dyadic_correlation_valuation_checks"] += 1
                counters["five_correlation_cancellation_checks"] += 1

    return {
        "epoch": epoch,
        "depth": depth,
        "period": period,
        "block": block,
        "two_exponent": two_exponent,
        "three_exponent": three_exponent,
        "five_exponent": five_exponent,
        "small_cofactor_bits": int(gmpy2.bit_length(small_cofactor)),
        "high_prime_count": len(high_primes),
        "support_class_mod9": support_class,
        "grid_numerator_mod105": grid_numerator,
        "reciprocal_lift_decimal": f"{float(reciprocal_lift):.15f}",
        "high_log_mass_over_depth": f"{total_high_log / depth:.15f}",
        "max_killed_log_mass_over_depth": f"{maximum_killed_log / depth:.15f}",
        "min_surviving_log_mass_over_depth":
            f"{minimum_surviving_log / depth:.15f}",
        "full_normalized_magnitude": f"{full_mean:.15f}",
        "diagnostics": {
            key: {metric: f"{value:.15f}" for metric, value in values.items()}
            for key, values in diagnostics.items()
        },
    }


def main() -> None:
    for relative, expected in FROZEN.items():
        actual = sha256(ROOT / relative)
        assert actual == expected, (relative, expected, actual)

    counters = {
        "denominator_factor_checks": 0,
        "high_coordinate_checks": 0,
        "reciprocal_lift_checks": 0,
        "high_grid_lift_checks": 0,
        "odd_crt_checks": 0,
        "high_lift_denominator_checks": 0,
        "full_phase_decomposition_checks": 0,
        "static_five_checks": 0,
        "six_period_grid_checks": 0,
        "nine_block_primary_checks": 0,
        "primary_fourier_support_checks": 0,
        "nine_block_energy_checks": 0,
        "selected_fourier_energy_checks": 0,
        "active_high_correlation_checks": 0,
        "high_annihilation_budget_checks": 0,
        "dyadic_correlation_valuation_checks": 0,
        "dyadic_fixed_modulus_identity_checks": 0,
        "five_correlation_cancellation_checks": 0,
    }
    rows = [row_replay(epoch, counters) for epoch in (4, 6, 8)]
    record = {
        "rows": rows,
        "counters": counters,
        "asserts_selected_complement_bound": False,
        "asserts_full_phase_cancellation": False,
        "asserts_fixed_return": False,
        "asserts_v1": False,
    }
    record_bytes = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print("literature_claim_label=literature-checked")
    for name, value in counters.items():
        print(f"{name}={value}")
    for row in rows:
        epoch = row["epoch"]
        complement = row["diagnostics"]["complement"]
        print(
            f"epoch_{epoch}=M{row['depth']},T{row['period']},H{row['block']},"
            f"class{row['support_class_mod9']},J{row['grid_numerator_mod105']},"
            f"high{row['high_prime_count']},"
            f"energy{complement['energy_fraction']},"
            f"cauchy{complement['cauchy_bound']},"
            f"actual{row['full_normalized_magnitude']},"
            f"remaining_log_mass_over_M{row['min_surviving_log_mass_over_depth']}"
        )
        print(
            f"epoch_{epoch}_selected_energy_fractions="
            + ",".join(
                f"{name}:{row['diagnostics'][name]['energy_fraction']}"
                for name in ("dyadic", "small", "grid", "lift", "hard", "complement")
            )
        )
    print(f"exact_record_sha256={hashlib.sha256(record_bytes).hexdigest()}")
    print("asserts_selected_complement_bound=false")
    print("asserts_full_phase_cancellation=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
