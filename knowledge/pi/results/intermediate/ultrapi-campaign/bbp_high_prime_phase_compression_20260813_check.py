#!/usr/bin/env python3
"""Exact replay for the BBP high-prime phase compression.

Every finite output is labelled ``experiment``.  The program checks exact
rational and modular identities only.  It does not prove a prime-number
theorem, a short-orbit estimate, the fixed-sixteen return, or V1.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from math import gcd, lcm, log
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
ACTUAL_QUOTIENT_SHA256 = (
    "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc"
)
HIGH_PRIME_RIGIDITY_SHA256 = (
    "419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42"
)
MIXED_SEPARATOR_SHA256 = (
    "950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820"
)


def repository_root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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


def two_adic_valuation(integer: int) -> int:
    assert integer
    integer = abs(integer)
    answer = 0
    while integer % 2 == 0:
        answer += 1
        integer //= 2
    return answer


def high_prime_coordinate(depth: int, prime: int) -> Fraction:
    """The independently rebuilt rational localization G_{M,p}."""
    assert prime > 5
    answer = Fraction()

    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))

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


def table_coordinate(depth: int, prime: int) -> Fraction:
    """The six interval rows for p > M from the frozen localization."""
    positive = prime % 4 == 1
    assert positive or prime % 4 == 3
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


def residue_lift(value: Fraction, prime: int) -> tuple[int, int]:
    """Return (least residue mod p, kappa in [0,b)) for value=a/b."""
    numerator = value.numerator
    denominator = value.denominator
    assert gcd(denominator, prime) == 1
    residue = numerator * pow(denominator, -1, prime) % prime
    kappa = (-numerator * pow(prime, -1, denominator)) % denominator
    assert (
        Fraction(residue, prime)
        - Fraction(kappa, denominator)
        - Fraction(numerator, denominator * prime)
    ).denominator == 1
    return residue, kappa


def a_multiplier(exponent: int) -> int:
    assert exponent >= 4
    return 2 ** (exponent - 4) * 5**exponent - 1


def common_denominator_bound(max_multiplier: int) -> int:
    answer = 1
    for value in range(1, max_multiplier + 1):
        answer = lcm(answer, value)
    return 2 ** (2 * max_multiplier) * answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=600)
    parser.add_argument("--moving-cutoff-level", type=int, default=6)
    args = parser.parse_args()
    if args.max_depth < 100:
        raise SystemExit("--max-depth must be at least 100")
    if not 2 <= args.moving_cutoff_level <= 12:
        raise SystemExit("--moving-cutoff-level must lie in [2, 12]")

    root = repository_root()
    pinned = {
        root / "problems/local/pi-digits.txt": SOURCE_SHA256,
        root
        / "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md": (
            ACTUAL_QUOTIENT_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813.md": (
            HIGH_PRIME_RIGIDITY_SHA256
        ),
        root
        / "work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813.md": (
            MIXED_SEPARATOR_SHA256
        ),
    }
    for path, expected in pinned.items():
        assert sha256(path) == expected, path

    primes = primes_through(8 * args.max_depth + 5)
    table_checks = 0
    exact_lift_checks = 0
    aggregate_grid_checks = 0
    phase_checks = 0
    dependence_mod_840_checks = 0
    sample_data: dict[int, tuple[int, Fraction, int]] = {}

    for depth in range(48, args.max_depth + 1):
        xi = Fraction()
        harmonic_lift = Fraction()
        grid_numerator = 0
        prime_count = 0
        signatures: dict[tuple[int, int], tuple[int, int, int]] = {}

        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = high_prime_coordinate(depth, prime)
            if coordinate == 0:
                continue
            prime_count += 1
            expected = table_coordinate(depth, prime)
            assert coordinate == expected
            assert 105 % coordinate.denominator == 0
            table_checks += 1

            residue, kappa = residue_lift(coordinate, prime)
            xi += Fraction(residue, prime)
            harmonic_lift += coordinate / prime
            grid_numerator += 105 // coordinate.denominator * kappa
            exact_lift_checks += 1

            if 3 * prime > 8 * depth + 5:
                interval = 1
            elif prime > 2 * depth + 1:
                interval = 2
            elif 5 * prime > 8 * depth + 5:
                interval = 3
            elif 3 * prime > 4 * depth + 3:
                interval = 4
            elif 7 * prime > 8 * depth + 5:
                interval = 5
            else:
                interval = 6
            signature_key = (interval, prime % 840)
            signature = (
                coordinate.numerator,
                coordinate.denominator,
                105 // coordinate.denominator * kappa % 105,
            )
            if signature_key in signatures:
                assert signatures[signature_key] == signature
            else:
                signatures[signature_key] = signature
            dependence_mod_840_checks += 1

        grid = Fraction(grid_numerator % 105, 105)
        assert (xi - harmonic_lift - grid).denominator == 1
        assert ((xi - harmonic_lift) * 105).denominator == 1
        aggregate_grid_checks += 1

        for exponent in range(max(4, depth), min(depth + 18, 2 * depth)):
            multiplier = a_multiplier(exponent)
            assert (
                multiplier * xi
                - multiplier * grid
                - multiplier * harmonic_lift
            ).denominator == 1
            assert Fraction(multiplier * harmonic_lift) == (
                Fraction(10**exponent, 16) * harmonic_lift
                - harmonic_lift
            )
            phase_checks += 1

        if depth in {48, 64, 100, 200, 400, args.max_depth}:
            sample_data[depth] = (
                grid_numerator % 105,
                harmonic_lift,
                prime_count,
            )

    expected_period = [99, 54, 24, 39, 84, 9]
    period_checks = 0
    for exponent in range(4, 400):
        assert a_multiplier(exponent) % 105 == expected_period[
            (exponent - 4) % 6
        ]
        assert a_multiplier(exponent) % 3 == 0
        period_checks += 1

    # Reconstruct the actual reduced BBP rational at disjoint sample depths.
    # This checks that G != 0 is exactly denominator survival and that the
    # lifted residue is the actual additive CRT coordinate, not merely the
    # value of the localization formula.
    actual_depths = sorted(
        {
            48,
            min(args.max_depth, 64),
            min(args.max_depth, 96),
            min(args.max_depth, 120),
        }
    )
    partial_sum = Fraction()
    actual_crt_checks = 0
    for depth in range(max(actual_depths) + 1):
        partial_sum += coefficient(depth) / 16**depth
        if depth not in actual_depths:
            continue
        numerator = partial_sum.numerator
        denominator = partial_sum.denominator
        dyadic_exponent = two_adic_valuation(denominator)
        odd_denominator = denominator >> dyadic_exponent
        dyadic_modulus = 1 << (dyadic_exponent - 4)
        dyadic_coordinate = (
            numerator * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            numerator - odd_denominator * dyadic_coordinate
        ) // dyadic_modulus
        assert gcd(odd_numerator, odd_denominator) == 1
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = high_prime_coordinate(depth, prime)
            survives = odd_denominator % prime == 0
            assert survives == (coordinate != 0)
            if not survives:
                continue
            assert (odd_denominator // prime) % prime != 0
            actual_residue = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            localized_residue, _ = residue_lift(coordinate, prime)
            assert actual_residue == localized_residue
            actual_crt_checks += 1

    moving_denominator_checks = 0
    moving_grid_checks = 0
    moving_reduced_denominator_checks = 0
    moving_depths = sorted(
        {
            max(48, args.max_depth // 3),
            max(64, args.max_depth // 2),
            args.max_depth,
        }
    )
    for depth in moving_depths:
        level = args.moving_cutoff_level
        cutoff = Fraction(depth, level)
        max_multiplier = (8 * depth + 5) * level // depth
        common_denominator = common_denominator_bound(max_multiplier)
        xi = Fraction()
        harmonic_lift = Fraction()
        grid_numerator = 0
        surviving_primes: list[int] = []
        for prime in primes:
            if prime * level <= depth:
                continue
            # The asymptotic moving-cutoff argument also has p>N_M, so all
            # multiplier denominators are p-units.  Small finite rows need
            # this condition imposed explicitly.
            if prime <= max_multiplier:
                continue
            if prime > 8 * depth + 5:
                break
            coordinate = high_prime_coordinate(depth, prime)
            if coordinate == 0:
                continue
            assert coordinate.denominator <= common_denominator
            assert common_denominator % coordinate.denominator == 0
            residue, kappa = residue_lift(coordinate, prime)
            if residue:
                surviving_primes.append(prime)
            xi += Fraction(residue, prime)
            harmonic_lift += coordinate / prime
            grid_numerator += (
                common_denominator // coordinate.denominator * kappa
            )
            moving_denominator_checks += 1
        grid = Fraction(grid_numerator % common_denominator, common_denominator)
        assert (xi - harmonic_lift - grid).denominator == 1
        for prime in surviving_primes:
            assert harmonic_lift.denominator % prime == 0
            moving_reduced_denominator_checks += 1
        moving_grid_checks += 1
        assert cutoff > 0

    # Each killed prime divides A_n, so its squarefree product cannot exceed
    # |A_n|.  The finite replay checks the exact divisibility/product ledger.
    annihilation_budget_checks = 0
    maximum_killed_log_mass_ratio = 0.0
    for depth in moving_depths:
        high_primes = []
        for prime in primes:
            if prime <= depth:
                continue
            if prime > 8 * depth + 5:
                break
            if high_prime_coordinate(depth, prime):
                high_primes.append(prime)
        for exponent in range(depth, int(log(16, 10) * depth) + 1):
            multiplier = a_multiplier(exponent)
            killed_product = 1
            killed_log_mass = 0.0
            for prime in high_primes:
                if multiplier % prime == 0:
                    killed_product *= prime
                    killed_log_mass += log(prime)
            assert multiplier % killed_product == 0
            assert killed_product <= abs(multiplier)
            if depth:
                maximum_killed_log_mass_ratio = max(
                    maximum_killed_log_mass_ratio,
                    killed_log_mass / depth,
                )
            annihilation_budget_checks += 1

    asymptotic_constant = (
        32 * log(3)
        - 16 * log(Fraction(3, 2))
        + Fraction(32, 3) * log(Fraction(4, 3))
        + Fraction(8, 3) * log(Fraction(5, 4))
        + Fraction(16, 15) * log(Fraction(6, 5))
        - Fraction(4, 15) * log(Fraction(7, 6))
        + Fraction(32, 105) * log(Fraction(8, 7))
    )
    # Derive the same constant directly from the seven fixed prime bands.
    asymptotic_bands = [
        (Fraction(16), Fraction(8, 3), Fraction(4)),
        (Fraction(32), Fraction(4), Fraction(8)),
        (Fraction(32, 3), Fraction(2), Fraction(8, 3)),
        (Fraction(8, 3), Fraction(8, 5), Fraction(2)),
        (Fraction(16, 15), Fraction(4, 3), Fraction(8, 5)),
        (Fraction(-4, 15), Fraction(8, 7), Fraction(4, 3)),
        (Fraction(32, 105), Fraction(1), Fraction(8, 7)),
    ]
    band_constant = sum(
        float(weight) * log(float(upper / lower))
        for weight, lower, upper in asymptotic_bands
    )
    assert abs(band_constant - float(asymptotic_constant)) < 1e-12
    assert asymptotic_bands[0][0] > abs(asymptotic_bands[-2][0])
    assert asymptotic_constant > 0
    asymptotic_constant_derivation_checks = len(asymptotic_bands) + 3
    last_grid, last_harmonic, last_count = sample_data[args.max_depth]

    print("status: PASS")
    print("bounded_replay_label: experiment")
    print("asymptotic_decomposition_label: proof sketch")
    print(f"depth_range: [48, {args.max_depth}]")
    print(f"high_prime_table_checks: {table_checks}")
    print(f"exact_residue_lift_checks: {exact_lift_checks}")
    print(f"aggregate_1_over_105_grid_checks: {aggregate_grid_checks}")
    print(f"phase_factorization_checks: {phase_checks}")
    print(f"dependence_mod_840_checks: {dependence_mod_840_checks}")
    print(f"period_mod_105_checks: {period_checks}")
    print(f"actual_reduced_crt_checks: {actual_crt_checks}")
    print(f"moving_denominator_checks: {moving_denominator_checks}")
    print(f"moving_grid_checks: {moving_grid_checks}")
    print(
        "moving_reduced_denominator_checks: "
        f"{moving_reduced_denominator_checks}"
    )
    print(f"annihilation_budget_checks: {annihilation_budget_checks}")
    print(
        "asymptotic_constant_derivation_checks: "
        f"{asymptotic_constant_derivation_checks}"
    )
    print(f"last_high_prime_count: {last_count}")
    print(f"last_grid_numerator_mod_105: {last_grid}")
    print(f"last_harmonic_lift: {float(last_harmonic):.15f}")
    print(
        "last_log_scaled_harmonic_lift: "
        f"{float(last_harmonic) * log(args.max_depth):.15f}"
    )
    print(f"predicted_asymptotic_constant: {float(asymptotic_constant):.15f}")
    print(
        "maximum_observed_killed_log_mass_over_depth: "
        f"{maximum_killed_log_mass_ratio:.15f}"
    )
    print("asserts_fixed_sixteen_return: false")
    print("asserts_v1: false")


if __name__ == "__main__":
    main()
