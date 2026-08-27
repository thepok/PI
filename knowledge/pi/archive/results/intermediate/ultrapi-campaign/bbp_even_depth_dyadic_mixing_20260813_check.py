#!/usr/bin/env python3
"""Independent exact replay for the even-depth BBP dyadic mixing addendum.

All bounded checks have label ``experiment``.  They verify finite residues of
the rational four-pole coefficient and do not assert a decimal return for pi.
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
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md":
        "d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3",
    "work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py":
        "69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
}

MAX_PRECISION = 11
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


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def rational_mod(value: Fraction, exponent: int) -> int:
    require(exponent >= 1, "positive two-adic precision required")
    modulus = 1 << exponent
    require(value.denominator & 1 == 1, "denominator must be odd")
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def f_mod(x: int, exponent: int) -> int:
    """Evaluate F(x)=sum 16^j a(x-1-j) modulo 2^exponent."""
    modulus = 1 << exponent
    total = 0
    for j in range((exponent - 1) // 4 + 1):
        total += (
            pow(16, j, modulus)
            * rational_mod(coefficient(x - 1 - j), exponent)
        )
    return total % modulus


def h_mod(m: int, exponent: int) -> int:
    require(m >= 0, "nonnegative index required")
    modulus = 1 << exponent
    return pow(25, m, modulus) * f_mod(14 * m + 1, exponent) % modulus


def build_even_endpoints() -> dict[int, tuple[int, int]]:
    """Return exact (L_(7n), A_(7n)) at positive even sevenfold depths."""
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
        if depth % 14 == 0:
            result[depth // 7] = (common, scaled)
    return result


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    f_zero_checks = 0
    parity_checks = 0
    fixed_level_bijection_checks = 0
    scaled_isometry_checks = 0
    s_one_edge_checks = 0

    for exponent in range(1, MAX_PRECISION + 1):
        modulus = 1 << exponent
        period = 1 << (exponent - 1)
        require(f_mod(0, exponent) == 0,
                f"F(0) residue at precision={exponent}")
        f_zero_checks += 1

        # Start after zero to make the eventual connection with w_(2m)
        # literal even for the s=1 edge case.
        start = period
        values = {
            m: h_mod(m, exponent)
            for m in range(start, start + period)
        }
        require(set(values.values()) == set(range(1, modulus, 2)),
                f"odd-residue bijection at precision={exponent}")
        fixed_level_bijection_checks += period
        parity_checks += period

        keys = list(values)
        for index, first in enumerate(keys):
            for second in keys[:index]:
                difference = values[first] - values[second]
                require(difference != 0,
                        f"injectivity at precision={exponent}")
                require(
                    valuation_two(difference)
                    == 1 + valuation_two(first - second),
                    f"scaled isometry at precision={exponent}",
                )
                scaled_isometry_checks += 1

        if exponent == 1:
            require(period == 1, "s=1 source quotient is a singleton")
            require(list(values.values()) == [1],
                    "s=1 target odd-residue set is a singleton")
            s_one_edge_checks += 2

    # Adversarial distances cover odd/even d, high powers of two, far
    # offsets, and the asymmetry m>m'.  Compute above the predicted valuation.
    adversarial_pairs = []
    for base in (0, 1, 17, 1000):
        for odd in (1, 3, 5, 31):
            for power in range(0, 13):
                distance = odd << power
                adversarial_pairs.append((base + distance, base))

    lte_checks = 0
    adversarial_scaled_isometry_checks = 0
    for first, second in adversarial_pairs:
        distance = first - second
        expected = 1 + valuation_two(distance)
        exponent = expected + 8
        difference = h_mod(first, exponent) - h_mod(second, exponent)
        require(valuation_two(difference) == expected,
                f"adversarial scaled isometry m={first},m'={second}")
        require(
            valuation_two(pow(25, distance) - 1)
            == 3 + valuation_two(distance),
            f"25-adic lifting identity d={distance}",
        )
        adversarial_scaled_isometry_checks += 1
        lte_checks += 1

    endpoints = build_even_endpoints()
    exact_selected_coordinate_checks = 0
    exact_rational_identity_checks = 0
    for n, (odd, numerator) in endpoints.items():
        require(n % 2 == 0 and n > 0, f"positive even depth n={n}")
        m = n // 2
        f_rational = Fraction(numerator, odd)
        for exponent in (1, 2, 5, 10, 16):
            require(exponent <= 54 * m, f"output precision at n={n}")
            require(
                f_mod(7 * n + 1, exponent) == rational_mod(f_rational, exponent),
                f"F(7n+1)=A_(7n)/L_(7n) at n={n}",
            )
            actual_coordinate = rational_mod(Fraction(5**n) * f_rational,
                                             exponent)
            require(actual_coordinate == h_mod(m, exponent),
                    f"w_(2m)=H(m) at n={n}, precision={exponent}")
            exact_rational_identity_checks += 1
            exact_selected_coordinate_checks += 1

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "theorem_claim_label": "proof sketch",
        "maximum_fixed_precision": MAX_PRECISION,
        "maximum_even_sevenfold_depth": MAX_SEVENFOLD_DEPTH,
        "f_zero_checks": f_zero_checks,
        "parity_checks": parity_checks,
        "fixed_level_bijection_checks": fixed_level_bijection_checks,
        "scaled_isometry_checks": scaled_isometry_checks,
        "adversarial_scaled_isometry_checks": adversarial_scaled_isometry_checks,
        "two_adic_lifting_checks": lte_checks,
        "s_one_edge_checks": s_one_edge_checks,
        "exact_rational_identity_checks": exact_rational_identity_checks,
        "exact_selected_coordinate_checks": exact_selected_coordinate_checks,
        "full_diagonal_period_at_even_depth_m": "2^(54*m-1)",
        "asserts_diagonal_mixing": False,
        "asserts_colored_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
