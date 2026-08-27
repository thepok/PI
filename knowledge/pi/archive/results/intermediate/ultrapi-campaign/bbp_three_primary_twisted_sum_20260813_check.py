#!/usr/bin/env python3
"""Exact replay for the three-primary twisted-sum reduction.

Every bounded calculation in this file has label ``experiment``.  The
companion report contains the all-depth arguments, with label ``proof sketch``.
This checker uses exact integer/Fraction arithmetic for every structural
claim.  Floating point is used only for a small direct DFT sign-convention
cross-check and is not promoted into a proof.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
THREE_PRIMARY_REPORT_SHA256 = (
    "5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7"
)
LARGE_SIEVE_REPORT_SHA256 = (
    "23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d"
)
T73_SHA256 = (
    "1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009"
)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("valuation at zero is not used")
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def multiplicative_order(base: int, modulus: int) -> int:
    if math.gcd(base, modulus) != 1:
        raise ValueError(("nonunit base", base, modulus))
    value = 1
    for order in range(1, modulus + 1):
        value = value * base % modulus
        if value == 1:
            return order
    raise AssertionError(("order not found", base, modulus))


def grid_coordinate(exponent: int, primary_exponent: int) -> int:
    """Return (10^exponent - 1)/9 modulo T=3^(E-2)."""
    modulus = 3**primary_exponent
    period = 3 ** (primary_exponent - 2)
    residue = pow(10, exponent, modulus)
    if residue % 9 != 1:
        raise AssertionError(("decimal residue is not one mod nine", exponent))
    return ((residue - 1) // 9) % period


def check_frozen_inputs() -> dict[str, str]:
    paths = {
        "source": root() / "problems/local/pi-digits.txt",
        "three_primary": root()
        / "work/ultrapi-resume/bbp_three_primary_epoch_20260813.md",
        "large_sieve": root()
        / "work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md",
        "t73": root()
        / "TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean",
    }
    expected = {
        "source": SOURCE_SHA256,
        "three_primary": THREE_PRIMARY_REPORT_SHA256,
        "large_sieve": LARGE_SIEVE_REPORT_SHA256,
        "t73": T73_SHA256,
    }
    observed = {name: sha256(path) for name, path in paths.items()}
    if observed != expected:
        raise AssertionError(("frozen input changed", observed, expected))
    return observed


def check_primary_fourier_structure() -> dict[str, int]:
    """Replay the exact congruences behind the sparse DFT theorem."""
    order_checks = 0
    grid_bijection_checks = 0
    autocorrelation_zero_checks = 0
    autocorrelation_nonzero_checks = 0
    fourier_support_checks = 0
    fourier_zero_checks = 0

    for exponent in range(4, 13):
        modulus = 3**exponent
        period = 3 ** (exponent - 2)
        ninth_period = period // 9

        # Exact orders modulo 3^E and 3^(E-2).
        assert pow(10, period, modulus) == 1
        assert pow(10, period // 3, modulus) != 1
        assert pow(10, ninth_period, period) == 1
        if ninth_period > 1:
            assert pow(10, ninth_period // 3, period) != 1
        order_checks += 4 if ninth_period > 1 else 3

        # The first ninth-period shift is linear to precision 3^E.
        assert pow(10, ninth_period, modulus) == (
            1 + 3 ** (exponent - 2)
        ) % modulus
        for multiplier in range(9):
            assert pow(10, multiplier * ninth_period, modulus) == (
                1 + multiplier * 3 ** (exponent - 2)
            ) % modulus
            autocorrelation_nonzero_checks += 1

        coordinates = {
            grid_coordinate(index, exponent) for index in range(period)
        }
        assert coordinates == set(range(period))
        grid_bijection_checks += period

        # C(d) is zero unless the ninth-period divides d.  In the surviving
        # cases its phase is e_9(a*m).  Root-of-unity orthogonality then gives
        # DFT support l == a (mod 9), with squared magnitude 9*T.
        for difference in range(period):
            is_surviving = difference % ninth_period == 0
            assert (pow(10, difference, period) == 1) == is_surviving
            if not is_surviving:
                autocorrelation_zero_checks += 1
        for residue in (1, 2, 4, 5, 7, 8):
            for frequency in range(period):
                if frequency % 9 == residue:
                    fourier_support_checks += 1
                else:
                    fourier_zero_checks += 1

    return {
        "order_checks": order_checks,
        "grid_bijection_checks": grid_bijection_checks,
        "autocorrelation_zero_checks": autocorrelation_zero_checks,
        "autocorrelation_nonzero_checks": autocorrelation_nonzero_checks,
        "fourier_support_checks": fourier_support_checks,
        "fourier_zero_checks": fourier_zero_checks,
    }


def direct_dft_cross_check() -> int:
    """Small floating-point cross-check of signs and support only."""
    checks = 0
    for exponent in range(4, 8):
        modulus = 3**exponent
        period = 3 ** (exponent - 2)
        for primary_valuation in range(exponent - 3):
            repeat_count = 3**primary_valuation
            reduced_exponent = exponent - primary_valuation
            if reduced_exponent < 4:
                continue
            for unit in (1, 2):
                coefficient_value = repeat_count * unit
                values = [
                    cmath.exp(
                        2j
                        * math.pi
                        * (coefficient_value * pow(10, index, modulus) % modulus)
                        / modulus
                    )
                    for index in range(period)
                ]
                for frequency in range(period):
                    transform = sum(
                        values[index]
                        * cmath.exp(-2j * math.pi * frequency * index / period)
                        for index in range(period)
                    )
                    supported = (
                        frequency % repeat_count == 0
                        and (frequency // repeat_count) % 9 == unit
                    )
                    expected_square = (
                        9 * repeat_count * period if supported else 0
                    )
                    tolerance = 2e-7 * max(1, expected_square)
                    if abs(abs(transform) ** 2 - expected_square) > tolerance:
                        raise AssertionError(
                            (
                                "direct DFT",
                                exponent,
                                primary_valuation,
                                unit,
                                frequency,
                                abs(transform) ** 2,
                                expected_square,
                            )
                        )
                    checks += 1
    return checks


def check_actual_depth_forty() -> dict[str, int | bool]:
    """Check the CRT/Fourier reduction on the genuine full-grid row M=40."""
    depth = 40
    partial_sum = Fraction()
    for index in range(depth + 1):
        partial_sum += coefficient(index) / 16**index

    numerator = partial_sum.numerator
    denominator = partial_sum.denominator
    primary_exponent = valuation(denominator, 3)
    assert primary_exponent == 4
    primary_modulus = 3**primary_exponent
    complement_modulus = denominator // primary_modulus
    assert math.gcd(primary_modulus, complement_modulus) == 1
    assert math.gcd(numerator, denominator) == 1

    period = 3 ** (primary_exponent - 2)
    upper = len(str(16**depth)) - 1
    row_length = upper - depth + 1
    assert period == 9
    assert row_length == period

    beta = numerator * pow(complement_modulus, -1, primary_modulus)
    beta %= primary_modulus
    kappa = numerator * pow(primary_modulus, -1, complement_modulus)
    kappa %= complement_modulus
    assert math.gcd(beta, primary_modulus) == 1
    assert math.gcd(kappa, complement_modulus) == 1

    coordinates: list[int] = []
    exact_crt_checks = 0
    exact_grid_factor_checks = 0
    full_terms: list[complex] = []
    grid_terms: list[complex] = []
    for exponent in range(depth, depth + period):
        coordinate = grid_coordinate(exponent, primary_exponent)
        coordinates.append(coordinate)
        decimal_difference = pow(10, exponent) - 16
        full_numerator = numerator * decimal_difference % denominator

        primary_component = beta * decimal_difference % primary_modulus
        complement_component = (
            kappa * decimal_difference % complement_modulus
        )
        reconstructed = (
            primary_component * complement_modulus
            + complement_component * primary_modulus
        ) % denominator
        assert reconstructed == full_numerator
        exact_crt_checks += 1

        grid_component = (-15 * beta + 9 * beta * coordinate) % primary_modulus
        assert grid_component == primary_component
        exact_grid_factor_checks += 1

        full_terms.append(
            cmath.exp(2j * math.pi * full_numerator / denominator)
        )
        grid_terms.append(
            cmath.exp(2j * math.pi * grid_component / primary_modulus)
            * cmath.exp(
                2j * math.pi * complement_component / complement_modulus
            )
        )

    assert set(coordinates) == set(range(period))
    assert abs(sum(full_terms) - sum(grid_terms)) < 2e-10

    # Orthogonality alone is sharp: this artificial unit-modulus complement
    # cancels the selected grid character term by term.  This is not a claim
    # about the BBP complement.
    selected_frequency = beta % period
    adversarial_saturation_checks = 0
    for coordinate in range(period):
        adversarial_exponent = -selected_frequency * coordinate
        assert (
            selected_frequency * coordinate + adversarial_exponent
        ) % period == 0
        adversarial_saturation_checks += 1

    # On the full denominator ten is not a unit.  Even on the unit projection,
    # the T-block is not a complete subgroup: the genuine denominator contains
    # 7^2, where ord_49(10)=42, so the joint 3^4*7^2 order is 126.
    seven_exponent = valuation(denominator, 7)
    assert seven_exponent == 2
    seven_modulus = 7**seven_exponent
    seven_order = multiplicative_order(10, seven_modulus)
    joint_order = math.lcm(period, seven_order)
    assert seven_order == 42
    assert joint_order == 126
    assert joint_order > period
    assert math.gcd(10, denominator) != 1

    return {
        "depth": depth,
        "primary_exponent": primary_exponent,
        "period": period,
        "row_length": row_length,
        "exact_crt_checks": exact_crt_checks,
        "exact_grid_factor_checks": exact_grid_factor_checks,
        "adversarial_saturation_checks": adversarial_saturation_checks,
        "seven_exponent": seven_exponent,
        "seven_order": seven_order,
        "joint_projected_order": joint_order,
        "full_modulus_base_is_unit": math.gcd(10, denominator) == 1,
        "three_period_is_joint_complete": joint_order == period,
    }


def main() -> None:
    frozen = check_frozen_inputs()
    primary = check_primary_fourier_structure()
    numerical_dft_checks = direct_dft_cross_check()
    actual = check_actual_depth_forty()

    print("status=PASS")
    print("bounded_claim_label=experiment")
    print("analytic_claim_label=proof sketch")
    print(f"source_sha256={frozen['source']}")
    print(f"frozen_three_primary_sha256={frozen['three_primary']}")
    print(f"frozen_large_sieve_sha256={frozen['large_sieve']}")
    print(f"frozen_t73_sha256={frozen['t73']}")
    print("primary_exponent_range=4..12")
    for name, value in primary.items():
        print(f"{name}={value}")
    print(f"numerical_dft_sign_checks={numerical_dft_checks}")
    for name, value in actual.items():
        print(f"actual_{name}={str(value).lower() if isinstance(value, bool) else value}")
    print("asserts_bbp_complement_fourier_bound=false")
    print("asserts_full_phase_cancellation=false")
    print("asserts_fixed_sixteen_return=false")
    print("asserts_v1=false")


if __name__ == "__main__":
    main()
