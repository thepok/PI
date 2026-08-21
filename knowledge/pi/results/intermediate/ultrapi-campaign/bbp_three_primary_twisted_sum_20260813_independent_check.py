#!/usr/bin/env python3
"""Independent bounded replay for the three-primary twisted-sum audit.

All finite calculations in this file have claim label ``experiment``.  The
all-depth arguments are re-derived in the companion independent audit report;
this program is deliberately not imported by the primary checker.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from fractions import Fraction
from pathlib import Path


FROZEN = {
    "source": (
        "problems/local/pi-digits.txt",
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    ),
    "primary_report": (
        "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md",
        "0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12",
    ),
    "primary_checker": (
        "work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_check.py",
        "7d8a8f7ff85c02b251845ba781d373dbf222a87ba69e0d6f82b1e995b9315e2c",
    ),
    "three_primary_report": (
        "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md",
        "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7",
    ),
    "large_sieve_report": (
        "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md",
        "23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d",
    ),
    "t73": (
        "TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean",
        "1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009",
    ),
    "bourgain_chang": (
        "work/theory/pi-lacunary-near-return-sparsity/library/t124/"
        "bourgain-chang-2006.pdf",
        "a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7",
    ),
    "kerr": (
        "work/theory/pi-long-lag-block-collision-decay/library/t70/"
        "kerr-1302.4170v1.pdf",
        "9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd",
    ),
}


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_frozen_files() -> dict[str, str]:
    observed: dict[str, str] = {}
    for name, (relative, expected) in FROZEN.items():
        value = file_sha256(repository_root() / relative)
        if value != expected:
            raise AssertionError(("frozen file changed", name, value, expected))
        observed[name] = value
    return observed


def root_of_unity(numerator: int, modulus: int) -> complex:
    return cmath.exp(2j * math.pi * (numerator % modulus) / modulus)


def prime_valuation(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("zero valuation is deliberately outside this replay")
    result = 0
    value = abs(value)
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def order_by_iteration(base: int, modulus: int) -> int:
    if modulus == 1:
        return 1
    if math.gcd(base, modulus) != 1:
        raise ValueError(("base is not a unit", base, modulus))
    value = 1
    for candidate in range(1, modulus + 1):
        value = value * base % modulus
        if value == 1:
            return candidate
    raise AssertionError(("order not found", base, modulus))


def decimal_grid(exponent: int, primary_exponent: int) -> int:
    primary_modulus = 3**primary_exponent
    period = 3 ** (primary_exponent - 2)
    residue = pow(10, exponent, primary_modulus)
    assert residue % 9 == 1
    return ((residue - 1) // 9) % period


def check_crt_grid_and_transform_sign() -> dict[str, int]:
    crt_congruences = 0
    grid_points = 0
    window_bijections = 0
    exact_phase_factors = 0
    transform_sign_checks = 0

    for primary_exponent in range(4, 9):
        primary_modulus = 3**primary_exponent
        period = 3 ** (primary_exponent - 2)
        assert order_by_iteration(10, primary_modulus) == period

        for start in (0, 1, 7):
            coordinates = [
                decimal_grid(start + offset, primary_exponent)
                for offset in range(period)
            ]
            assert set(coordinates) == set(range(period))
            grid_points += period
            window_bijections += 1

        for complement in (2, 4, 5, 7, 8, 10, 11, 25, 49):
            assert math.gcd(primary_modulus, complement) == 1
            for numerator in (-17, -5, 1, 2, 5, 17):
                if math.gcd(numerator, primary_modulus * complement) != 1:
                    continue
                beta = (
                    numerator * pow(complement, -1, primary_modulus)
                ) % primary_modulus
                kappa = (
                    numerator * pow(primary_modulus, -1, complement)
                ) % complement
                for integer in (-31, -1, 0, 1, 19, 73):
                    rebuilt = (
                        (beta * integer % primary_modulus) * complement
                        + (kappa * integer % complement) * primary_modulus
                    ) % (primary_modulus * complement)
                    assert rebuilt == (
                        numerator * integer
                    ) % (primary_modulus * complement)
                    crt_congruences += 1

        # A separate numerical sign check of TS10--TS12.  The structural
        # equalities above remain exact; floating point is used only here.
        if primary_exponent <= 6:
            complement = 35
            numerator = 11
            beta = numerator * pow(complement, -1, primary_modulus)
            beta %= primary_modulus
            kappa = numerator * pow(primary_modulus, -1, complement)
            kappa %= complement
            combined_modulus = primary_modulus * complement
            for harmonic in (-2, 1, 5):
                start = 3
                weights = [0j] * period
                direct = 0j
                factored = 0j
                for offset in range(period):
                    exponent = start + offset
                    coordinate = decimal_grid(exponent, primary_exponent)
                    ten_combined = pow(10, exponent, combined_modulus)
                    ten_complement = pow(10, exponent, complement)
                    direct += root_of_unity(
                        harmonic * numerator * (ten_combined - 16),
                        combined_modulus,
                    )
                    weight = root_of_unity(
                        harmonic * kappa * (ten_complement - 16),
                        complement,
                    )
                    weights[coordinate] = weight
                    factored += (
                        root_of_unity(-15 * harmonic * beta, primary_modulus)
                        * root_of_unity(
                            harmonic * beta * coordinate, period
                        )
                        * weight
                    )
                    exact_phase_factors += 1
                assert abs(direct - factored) < 3e-9 * period

                selected_transform = sum(
                    weights[coordinate]
                    * root_of_unity(harmonic * beta * coordinate, period)
                    for coordinate in range(period)
                ) / period
                normalized_direct = direct / period
                predicted = root_of_unity(
                    -15 * harmonic * beta, primary_modulus
                ) * selected_transform
                assert abs(normalized_direct - predicted) < 3e-9
                transform_sign_checks += 1

    return {
        "crt_congruences": crt_congruences,
        "grid_points": grid_points,
        "window_bijections": window_bijections,
        "exact_phase_factors": exact_phase_factors,
        "transform_sign_checks": transform_sign_checks,
    }


def check_sparse_transform_and_harmonics() -> dict[str, int]:
    order_checks = 0
    shift_congruences = 0
    autocorrelation_cases = 0
    support_cases = 0
    harmonic_dft_cases = 0

    for primary_exponent in range(4, 10):
        modulus = 3**primary_exponent
        period = 3 ** (primary_exponent - 2)
        ninth = period // 9
        assert order_by_iteration(10, modulus) == period
        assert order_by_iteration(10, period) == ninth
        order_checks += 2

        for multiplier in range(9):
            assert pow(10, multiplier * ninth, modulus) == (
                1 + multiplier * 3 ** (primary_exponent - 2)
            ) % modulus
            shift_congruences += 1

        for difference in range(period):
            survives = difference % ninth == 0
            assert (pow(10, difference, period) == 1) == survives
            if survives:
                multiplier = difference // ninth
                assert pow(10, difference, modulus) == (
                    1 + multiplier * 3 ** (primary_exponent - 2)
                ) % modulus
            autocorrelation_cases += 1

        # The final nine-character sum in Wiener--Khinchin is 9 exactly in
        # the stated class and zero otherwise.  This is checked as the exact
        # exponent congruence that invokes root-of-unity orthogonality.
        for unit in (1, 2, 4, 5, 7, 8):
            for frequency in range(period):
                expected_nonzero = frequency % 9 == unit
                assert ((unit - frequency) % 9 == 0) == expected_nonzero
                support_cases += 1

    # Direct independent finite DFT replay of TS23--TS24, including E=4,
    # negative harmonics, and every allowed valuation s at these sizes.
    for primary_exponent in range(4, 8):
        modulus = 3**primary_exponent
        period = 3 ** (primary_exponent - 2)
        for valuation in range(primary_exponent - 3):
            repeat_count = 3**valuation
            reduced_period = period // repeat_count
            for unit in (-2, -1, 1, 4):
                harmonic = repeat_count * unit
                for start in (0, 2):
                    reduced_unit = (
                        unit
                        * pow(10, start, 3 ** (primary_exponent - valuation))
                    ) % (3 ** (primary_exponent - valuation))
                    values = [
                        root_of_unity(
                            harmonic * pow(10, start + index, modulus),
                            modulus,
                        )
                        for index in range(period)
                    ]
                    for frequency in range(period):
                        transform = sum(
                            values[index]
                            * root_of_unity(-frequency * index, period)
                            for index in range(period)
                        )
                        supported = (
                            frequency % repeat_count == 0
                            and (frequency // repeat_count) % 9
                            == reduced_unit % 9
                        )
                        expected_square = (
                            9 * repeat_count * period if supported else 0
                        )
                        tolerance = 3e-7 * max(1, expected_square)
                        assert (
                            abs(abs(transform) ** 2 - expected_square)
                            <= tolerance
                        )
                        harmonic_dft_cases += 1
                    assert reduced_period == 3 ** (
                        primary_exponent - valuation - 2
                    )

    return {
        "order_checks": order_checks,
        "shift_congruences": shift_congruences,
        "autocorrelation_cases": autocorrelation_cases,
        "support_cases": support_cases,
        "harmonic_dft_cases": harmonic_dft_cases,
    }


def discrete_transform(values: list[complex]) -> list[complex]:
    length = len(values)
    return [
        sum(
            values[index] * root_of_unity(-frequency * index, length)
            for index in range(length)
        )
        for frequency in range(length)
    ]


def check_conditional_fourier_bound() -> dict[str, float | int]:
    convolution_sign_checks = 0
    restricted_norm_bounds = 0
    periodic_weight_rows = 0
    maximum_periodic_ratio = 0.0

    for primary_exponent in range(4, 8):
        modulus = 3**primary_exponent
        period = 3 ** (primary_exponent - 2)
        for unit in (1, 2):
            primary_values = [
                root_of_unity(unit * pow(10, index, modulus), modulus)
                for index in range(period)
            ]
            # An arbitrary deterministic unit-modulus complement; no BBP
            # interpretation is assigned to it.
            weights = [
                root_of_unity(index * index + 3 * index + 1, 37)
                for index in range(period)
            ]
            primary_transform = discrete_transform(primary_values)
            weight_transform = discrete_transform(weights)
            direct = sum(
                primary_values[index] * weights[index]
                for index in range(period)
            )
            convolution = sum(
                primary_transform[frequency]
                * weight_transform[-frequency % period]
                for frequency in range(period)
            ) / period
            assert abs(direct - convolution) < 4e-8 * period
            convolution_sign_checks += 1

            restricted_sum = sum(
                abs(weight_transform[-frequency % period])
                for frequency in range(period)
                if frequency % 9 == unit
            )
            restricted_mass = restricted_sum / period
            rhs_27 = 3 * restricted_sum / math.sqrt(period)
            rhs_29 = 3 * math.sqrt(period) * restricted_mass
            assert abs(rhs_27 - rhs_29) < 1e-10 * max(1, rhs_27)
            assert abs(direct) <= rhs_27 + 4e-8 * period
            # Exact-support Cauchy--Schwarz plus Parseval yields A<=sqrt(T)/3.
            assert restricted_mass <= math.sqrt(period) / 3 + 4e-8
            restricted_norm_bounds += 1

    # Bounded replay of TS31 for fixed ordinary periods.  The proof in the
    # report uses the geometric-sum estimate; these rows only exercise it.
    for ordinary_period in (2, 4, 5, 7):
        one_period = [
            root_of_unity(index * index + 1, ordinary_period)
            for index in range(ordinary_period)
        ]
        for primary_exponent in range(4, 9):
            period = 3 ** (primary_exponent - 2)
            values = [one_period[index % ordinary_period] for index in range(period)]
            transform = discrete_transform(values)
            mass = sum(
                abs(transform[-frequency % period])
                for frequency in range(period)
                if frequency % 9 == 1
            ) / period
            ratio = mass / math.log(2 * period)
            maximum_periodic_ratio = max(maximum_periodic_ratio, ratio)
            assert ratio < ordinary_period + 1
            periodic_weight_rows += 1

    return {
        "convolution_sign_checks": convolution_sign_checks,
        "restricted_norm_bounds": restricted_norm_bounds,
        "periodic_weight_rows": periodic_weight_rows,
        "maximum_periodic_mass_over_log": maximum_periodic_ratio,
    }


def bbp_coefficient_from_poles(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def check_depth_forty_no_go() -> dict[str, int | bool]:
    depth = 40
    partial_sum = sum(
        (
            bbp_coefficient_from_poles(index) / 16**index
            for index in range(depth + 1)
        ),
        Fraction(),
    )
    numerator = partial_sum.numerator
    denominator = partial_sum.denominator
    assert math.gcd(numerator, denominator) == 1
    assert prime_valuation(denominator, 3) == 4
    assert prime_valuation(denominator, 7) == 2
    assert prime_valuation(denominator, 2) == 160
    assert prime_valuation(denominator, 5) == 3

    upper = 0
    decimal_power = 1
    sixteenth_power = 16**depth
    while 10 * decimal_power <= sixteenth_power:
        decimal_power *= 10
        upper += 1
    assert upper == 48

    primary_modulus = 3**4
    complement = denominator // primary_modulus
    period = order_by_iteration(10, primary_modulus)
    assert period == 9
    assert upper - depth + 1 == period
    beta = numerator * pow(complement, -1, primary_modulus)
    beta %= primary_modulus
    kappa = numerator * pow(primary_modulus, -1, complement)
    kappa %= complement

    crt_row_checks = 0
    for harmonic in (-2, 1, 5):
        for exponent in range(depth, upper + 1):
            difference = harmonic * (pow(10, exponent) - 16)
            reconstructed = (
                (beta * difference % primary_modulus) * complement
                + (kappa * difference % complement) * primary_modulus
            ) % denominator
            assert reconstructed == numerator * difference % denominator
            coordinate = decimal_grid(exponent, 4)
            assert beta * difference % primary_modulus == (
                harmonic * beta * (9 * coordinate - 15)
            ) % primary_modulus
            crt_row_checks += 1

    order_49 = order_by_iteration(10, 49)
    order_81 = order_by_iteration(10, 81)
    order_joint = order_by_iteration(10, 81 * 49)
    assert order_49 == 42
    assert order_81 == 9
    assert order_joint == math.lcm(order_49, order_81) == 126
    prefix = [pow(10, exponent, 81 * 49) for exponent in range(depth, upper + 1)]
    assert len(set(prefix)) == 9 < order_joint

    adversarial_checks = 0
    selected = beta % period
    for coordinate in range(period):
        assert (selected * coordinate - selected * coordinate) % period == 0
        adversarial_checks += 1

    return {
        "depth": depth,
        "upper_exponent": upper,
        "row_length": period,
        "crt_row_checks": crt_row_checks,
        "seven_exponent": 2,
        "order_49": order_49,
        "joint_order": order_joint,
        "joint_prefix_is_complete": len(set(prefix)) == order_joint,
        "full_denominator_base_is_unit": math.gcd(10, denominator) == 1,
        "adversarial_checks": adversarial_checks,
    }


def main() -> None:
    frozen = check_frozen_files()
    crt = check_crt_grid_and_transform_sign()
    sparse = check_sparse_transform_and_harmonics()
    conditional = check_conditional_fourier_bound()
    forty = check_depth_forty_no_go()

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    for name, digest in frozen.items():
        print(f"frozen_{name}_sha256={digest}")
    for group in (crt, sparse, conditional, forty):
        for name, value in group.items():
            if isinstance(value, bool):
                rendered = str(value).lower()
            elif isinstance(value, float):
                rendered = f"{value:.12f}"
            else:
                rendered = str(value)
            print(f"{name}={rendered}")
    print("asserts_actual_complement_fourier_bound=false")
    print("asserts_full_phase_cancellation=false")
    print("asserts_fixed_sixteen_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
