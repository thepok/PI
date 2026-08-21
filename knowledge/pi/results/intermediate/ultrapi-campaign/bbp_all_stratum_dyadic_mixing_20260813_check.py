#!/usr/bin/env python3
"""Exact replay for the all-stratum BBP dyadic-mixing supplement.

Every bounded row has claim label ``experiment``.  The script reconstructs
the four-pole coefficient directly and does not assert a decimal return for
pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813.md":
        "3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623",
    "work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_check.py":
        "d05ed720b94c23d3d59c23b6bc300d46e6d88dc9f37d31ab5dddb604ce19a839",
}

MAX_RAW_PRECISION = 10
MAX_STRATUM_PRECISION = 9
MAX_STRATUM = 9
MAX_SEVENFOLD_DEPTH = 100


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(coefficient_numerator(k), coefficient_denominator(k))


def lcm(first: int, second: int) -> int:
    return first // gcd(first, second) * second


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def rational_mod(value: Fraction, exponent: int) -> int:
    require(exponent >= 1, "positive two-adic precision required")
    require(value.denominator & 1 == 1, "denominator must be odd")
    modulus = 1 << exponent
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def f_mod(x: int, exponent: int) -> int:
    """Evaluate F(x)=sum_j 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    total = 0
    for j in range((exponent - 1) // 4 + 1):
        total += (
            pow(16, j, modulus)
            * rational_mod(coefficient(x - 1 - j), exponent)
        )
    return total % modulus


def z_mod(n: int, exponent: int) -> int:
    """Return Z(n)=5^n F(7n+1) modulo 2^exponent."""
    require(n >= 0, "nonnegative selected depth required")
    modulus = 1 << exponent
    return pow(5, n, modulus) * f_mod(7 * n + 1, exponent) % modulus


def stratum_representative(r: int) -> int:
    """Least a modulo 2^(r+1) with v2(7a+1)=r."""
    modulus = 1 << (r + 1)
    explicit = pow(7, -1, modulus) * ((1 << r) - 1) % modulus
    matches = [
        n for n in range(modulus)
        if valuation_two(7 * n + 1) == r
    ]
    require(len(matches) == 1, f"unique valuation stratum r={r}")
    require(matches[0] == explicit, f"explicit valuation stratum r={r}")
    return matches[0]


def build_selected_endpoints() -> dict[int, tuple[int, int]]:
    """Return exact (L_(7n), A_(7n)) for 1 <= n <= the cutoff."""
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    result: dict[int, tuple[int, int]] = {}
    for depth in range(1, 7 * MAX_SEVENFOLD_DEPTH + 1):
        denominator = coefficient_denominator(depth)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(depth) * (next_common // denominator)
        )
        common = next_common
        if depth % 7 == 0:
            result[depth // 7] = (common, scaled)
    return result


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    raw_bijection_checks = 0
    raw_scaled_isometry_checks = 0
    for exponent in range(1, MAX_RAW_PRECISION + 1):
        modulus = 1 << exponent
        values = [z_mod(n, exponent) for n in range(modulus)]
        require(set(values) == set(range(modulus)),
                f"raw selected-coordinate bijection at s={exponent}")
        raw_bijection_checks += modulus
        for first in range(modulus):
            for second in range(first):
                require(
                    valuation_two(values[first] - values[second])
                    == valuation_two(first - second),
                    f"raw scaled isometry at s={exponent}",
                )
                raw_scaled_isometry_checks += 1

    stratum_representative_checks = 0
    stratum_bijection_checks = 0
    stratum_scaled_isometry_checks = 0
    for r in range(MAX_STRATUM + 1):
        step = 1 << (r + 1)
        representative = stratum_representative(r)
        require(valuation_two(7 * representative + 1) == r,
                f"representative valuation r={r}")
        require(valuation_two(7 * (representative + step) + 1) == r,
                f"stratum periodicity r={r}")
        stratum_representative_checks += 2

        for exponent in range(1, MAX_STRATUM_PRECISION + 1):
            modulus = 1 << exponent
            period = 1 << (exponent - 1)
            values: list[int] = []
            for m in range(period):
                n = representative + step * m
                raw = z_mod(n, r + exponent)
                require(raw % (1 << r) == 0,
                        f"raw divisibility on stratum r={r}")
                values.append((raw >> r) % modulus)
            require(set(values) == set(range(1, modulus, 2)),
                    f"reduced odd-residue bijection r={r},s={exponent}")
            stratum_bijection_checks += period
            for first in range(period):
                for second in range(first):
                    require(
                        valuation_two(values[first] - values[second])
                        == 1 + valuation_two(first - second),
                        f"reduced stratum isometry r={r},s={exponent}",
                    )
                    stratum_scaled_isometry_checks += 1

    adversarial_raw_checks = 0
    lifting_checks = 0
    for base in (0, 1, 19, 1000):
        for odd in (1, 3, 7, 31):
            for power in range(15):
                distance = odd << power
                first = base + distance
                second = base
                expected = valuation_two(distance)
                precision = expected + 9
                difference = z_mod(first, precision) - z_mod(second, precision)
                require(valuation_two(difference) == expected,
                        f"adversarial raw isometry n={first},n'={second}")
                require(
                    valuation_two(pow(5, distance) - 1) == 2 + expected,
                    f"five-power lifting identity d={distance}",
                )
                adversarial_raw_checks += 1
                lifting_checks += 1

    exact_rational_identity_checks = 0
    exact_raw_coordinate_checks = 0
    exact_reduced_coordinate_checks = 0
    for n, (odd, numerator) in build_selected_endpoints().items():
        f_rational = Fraction(numerator, odd)
        r = valuation_two(7 * n + 1)
        kappa = 27 * n - r
        require(kappa >= 1, f"positive reduced precision n={n}")
        for exponent in (1, 2, 5, 10, 16):
            if exponent > kappa:
                continue
            raw_precision = r + exponent
            require(
                f_mod(7 * n + 1, raw_precision)
                == rational_mod(f_rational, raw_precision),
                f"F(7n+1)=A_(7n)/L_(7n) at n={n}",
            )
            selected = Fraction(5**n) * f_rational
            raw = z_mod(n, raw_precision)
            require(raw == rational_mod(selected, raw_precision),
                    f"raw selected coordinate at n={n}")
            reduced = selected / (1 << r)
            require((raw >> r) % (1 << exponent)
                    == rational_mod(reduced, exponent),
                    f"complete reduced coordinate at n={n}")
            exact_rational_identity_checks += 1
            exact_raw_coordinate_checks += 1
            exact_reduced_coordinate_checks += 1

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "theorem_claim_label": "proof sketch",
        "maximum_raw_precision": MAX_RAW_PRECISION,
        "maximum_stratum_precision": MAX_STRATUM_PRECISION,
        "maximum_stratum": MAX_STRATUM,
        "maximum_sevenfold_depth": MAX_SEVENFOLD_DEPTH,
        "raw_bijection_checks": raw_bijection_checks,
        "raw_scaled_isometry_checks": raw_scaled_isometry_checks,
        "stratum_representative_checks": stratum_representative_checks,
        "stratum_bijection_checks": stratum_bijection_checks,
        "stratum_scaled_isometry_checks": stratum_scaled_isometry_checks,
        "adversarial_raw_checks": adversarial_raw_checks,
        "five_power_lifting_checks": lifting_checks,
        "exact_rational_identity_checks": exact_rational_identity_checks,
        "exact_raw_coordinate_checks": exact_raw_coordinate_checks,
        "exact_reduced_coordinate_checks": exact_reduced_coordinate_checks,
        "asserts_moving_diagonal_mixing": False,
        "asserts_colored_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
