#!/usr/bin/env python3
"""Exact finite replay for the BBP short-orbit/CRT report.

Every output has claim status ``experiment``.  The script checks finite
rational identities, congruences, and counterexamples only.  It neither
certifies the infinite 2-adic argument nor proves a return for pi.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd, log10
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
LOG10_16 = log10(16)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def valuation(value: int, prime: int) -> int:
    assert value
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def bbp_coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def rational_mod_power_of_two(value: Fraction, bits: int) -> int:
    """The image of a 2-integral rational modulo 2**bits."""
    if bits <= 0:
        return 0
    modulus = 1 << bits
    assert value.denominator & 1
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def reflected_f_mod(argument: int, bits: int) -> int:
    """F(argument) modulo 2**bits from its uniformly convergent series."""
    if bits <= 0:
        return 0
    modulus = 1 << bits
    answer = 0
    # Terms with 4*j >= bits vanish modulo the requested power of two.
    for j in range((bits + 3) // 4):
        value = bbp_coefficient(argument - 1 - j)
        answer += pow(16, j, modulus) * rational_mod_power_of_two(value, bits)
    return answer % modulus


def nearest_coprime_lift(
    target: Fraction,
    modulus: int,
    base: int,
    step: int = 256,
) -> tuple[int, int]:
    """Choose t near target with gcd(base + step*t, modulus) = 1.

    The second component counts integer steps inspected away from a nearest
    floor/ceiling pair.  This is only a finite experiment; the report uses
    Kanold's theorem for the asymptotic construction.
    """
    assert gcd(step, modulus) == 1
    lower = target.numerator // target.denominator
    for gap in range(modulus):
        candidates = (lower - gap, lower + 1 + gap)
        admissible = [
            candidate
            for candidate in candidates
            if gcd(base + step * candidate, modulus) == 1
        ]
        if admissible:
            return min(admissible, key=lambda candidate: abs(Fraction(candidate) - target)), gap
    raise AssertionError("a reduced residue must exist")


def circle_distance_rational(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=120)
    args = parser.parse_args()
    if args.max_depth < 12:
        raise SystemExit("--max-depth must be at least 12")

    digest = hashlib.sha256(source_path().read_bytes()).hexdigest()
    assert digest == SOURCE_SHA256

    # Finite shadows of the theorem F(X) = X + 2G(X): F permutes every
    # tested 2-power residue ring.  The proof, not this finite replay, gives
    # the all-depth isometry.
    isometry_permutation_checks = 0
    for bits in range(1, 10):
        modulus = 1 << bits
        values = [reflected_f_mod(x, bits) for x in range(modulus)]
        assert sorted(values) == list(range(modulus))
        isometry_permutation_checks += modulus

    shadow = Fraction()
    phase_reduction_checks = 0
    affine_recurrence_checks = 0
    dyadic_coordinate_checks = 0
    crt_split_checks = 0
    separator_phase_checks = 0
    odd_denominator_nonnesting: list[tuple[int, int]] = []
    previous_odd_denominator: int | None = None
    maximum_separator_grid_gap = 0
    smallest_separator_distance = Fraction(1, 2)
    proportional_band_rows: dict[int, tuple[int, Fraction]] = {}

    for depth in range(args.max_depth + 1):
        shadow += bbp_coefficient(depth) / 16**depth
        if depth < 2:
            continue

        r = valuation(depth + 1, 2)
        dyadic_exponent = 4 * depth - r
        assert valuation(shadow.denominator, 2) == dyadic_exponent
        odd_denominator = shadow.denominator >> dyadic_exponent
        numerator = shadow.numerator
        assert numerator & 1 and odd_denominator & 1

        if previous_odd_denominator is not None and (
            odd_denominator % previous_odd_denominator
        ):
            lost = previous_odd_denominator // gcd(
                previous_odd_denominator, odd_denominator
            )
            odd_denominator_nonnesting.append((depth, lost))
        previous_odd_denominator = odd_denominator

        reduced_dyadic = 1 << (dyadic_exponent - 4)
        dyadic_coordinate = (
            numerator * pow(odd_denominator, -1, reduced_dyadic)
        ) % reduced_dyadic
        odd_quotient = (
            numerator - odd_denominator * dyadic_coordinate
        ) // reduced_dyadic
        assert Fraction(16) * shadow == (
            Fraction(dyadic_coordinate, reduced_dyadic)
            + Fraction(odd_quotient, odd_denominator)
        )
        crt_split_checks += 1

        # The p-adic null identity identifies eight bits beyond the dyadic
        # phase modulus: after division by 2^r its precision is 256*D.
        f_bits = 4 * (depth + 1)
        f_value = reflected_f_mod(depth + 1, f_bits)
        assert f_value % (1 << r) == 0
        full_unit_modulus = 1 << (f_bits - r)
        p_adic_unit = (f_value >> r) % full_unit_modulus
        actual_unit = (
            numerator * pow(odd_denominator, -1, full_unit_modulus)
        ) % full_unit_modulus
        assert p_adic_unit == actual_unit
        assert p_adic_unit % reduced_dyadic == dyadic_coordinate
        dyadic_coordinate_checks += 1

        upper = int(LOG10_16 * depth)
        if upper >= 5:
            modulus = reduced_dyadic * odd_denominator
            a_value = (10**5 - 16) // 16
            residue = a_value * numerator % modulus
            for decimal_exponent in range(5, upper + 1):
                if decimal_exponent > 5:
                    previous_a = a_value
                    previous_residue = residue
                    a_value = 10 * a_value + 9
                    residue = (10 * previous_residue + 9 * numerator) % modulus
                    assert a_value == (10**decimal_exponent - 16) // 16
                    assert residue == a_value * numerator % modulus
                    affine_recurrence_checks += 2

                odd_gcd = gcd(a_value, odd_denominator)
                reduced = Fraction(
                    a_value * numerator // odd_gcd,
                    reduced_dyadic * (odd_denominator // odd_gcd),
                )
                direct = (10**decimal_exponent - 16) * shadow
                assert reduced == direct
                assert reduced.denominator == (
                    reduced_dyadic * (odd_denominator // odd_gcd)
                )
                phase_reduction_checks += 2

        # Preserve the complete reduced denominator and all the p-adic
        # precision by replacing c with c+256*t.  Choose t so that the
        # resulting B'_M = B_M + 16*t/R_M approximates beta=1/10.
        target_lift = odd_denominator * (Fraction(1, 10) - shadow) / 16
        lift, grid_gap = nearest_coprime_lift(
            target_lift,
            odd_denominator,
            odd_quotient,
        )
        maximum_separator_grid_gap = max(maximum_separator_grid_gap, grid_gap)
        alternative_odd = odd_quotient + 256 * lift
        alternative_numerator = (
            odd_denominator * dyadic_coordinate
            + reduced_dyadic * alternative_odd
        )
        alternative_modulus = reduced_dyadic * odd_denominator
        assert gcd(alternative_numerator, alternative_modulus) == 1
        assert alternative_odd % 256 == odd_quotient % 256
        assert (
            alternative_numerator
            * pow(odd_denominator, -1, full_unit_modulus)
            % full_unit_modulus
            == p_adic_unit
        )
        alternative_point = Fraction(
            alternative_numerator, alternative_modulus
        ) % 1
        alternative_shadow = Fraction(
            alternative_numerator, 16 * alternative_modulus
        )
        assert alternative_shadow == shadow + Fraction(16 * lift, odd_denominator)
        approximation_error = abs(alternative_shadow - Fraction(1, 10))

        for decimal_exponent in range(4, upper + 1):
            a_value = (10**decimal_exponent - 16) // 16
            alternative_distance = circle_distance_rational(
                a_value * alternative_point
            )
            # A_n*(3/5) = (10^n-16)/10 has circle distance exactly 2/5.
            assert alternative_distance >= Fraction(2, 5) - (
                (10**decimal_exponent - 16) * approximation_error
            )
            smallest_separator_distance = min(
                smallest_separator_distance, alternative_distance
            )
            separator_phase_checks += 1

        # A concrete falsifier for monotonic decay in the newly exposed band
        # depth <= n <= floor(log_10(16)*depth).
        if upper >= depth:
            best_distance: Fraction | None = None
            best_exponent = -1
            for decimal_exponent in range(depth, upper + 1):
                distance = circle_distance_rational(
                    (10**decimal_exponent - 16) * shadow
                )
                if best_distance is None or distance < best_distance:
                    best_distance = distance
                    best_exponent = decimal_exponent
            assert best_distance is not None
            proportional_band_rows[depth] = (best_exponent, best_distance)

    # Explicit exact witnesses, not floating-point pattern recognition.
    assert odd_denominator_nonnesting[:5] == [
        (5, 3),
        (9, 19),
        (19, 13),
        (24, 7),
        (29, 7),
    ]
    before = proportional_band_rows[20][1]
    after = proportional_band_rows[21][1]
    assert after > before

    print("claim_status=experiment")
    print(f"source_sha256={digest}")
    print(f"finite_two_adic_permutation_checks={isometry_permutation_checks}")
    print(f"dyadic_coordinate_checks={dyadic_coordinate_checks}")
    print(f"crt_split_checks={crt_split_checks}")
    print(f"phase_reduction_checks={phase_reduction_checks}")
    print(f"affine_recurrence_checks={affine_recurrence_checks}")
    print(f"separator_phase_checks={separator_phase_checks}")
    print(f"maximum_separator_grid_gap={maximum_separator_grid_gap}")
    print(
        "smallest_separator_distance="
        f"{float(smallest_separator_distance):.15f}"
    )
    print(
        "first_odd_denominator_nonnesting_events="
        f"{odd_denominator_nonnesting[:8]}"
    )
    print(
        "proportional_band_monotonicity_falsifier="
        f"M20:n{proportional_band_rows[20][0]}:"
        f"{float(before):.15f}->"
        f"M21:n{proportional_band_rows[21][0]}:"
        f"{float(after):.15f}"
    )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
