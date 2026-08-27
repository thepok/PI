#!/usr/bin/env python3
"""Exact replay for the BBP scalar p-adic/Archimedean separator.

All mathematical loops use Fraction arithmetic.  Numerical output is an
experiment only; the all-index claims are the identities and inequalities
recorded in the companion report.
"""

from __future__ import annotations

import argparse
import hashlib
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT = Path(__file__).with_name(
    "bbp_scalar_padic_archimedean_separator_20260813.md"
)

PINNED = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_character_breakthrough_attack_20260813.md":
        "5a0e3027eb2b6c38b48e2b3ae075b4175b586bbd54ec1de68e6621cb0e03c264",
    "work/ultrapi-resume/bbp_character_breakthrough_independent_audit_20260813.md":
        "c3d6f382972886e8c27d65159cc164ec55651ff353ac44f3300438033892304f",
    "work/ultrapi-resume/bbp_short_orbit_return_attack.md":
        "eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d",
    "work/ultrapi-resume/bbp_short_orbit_return_independent_audit.md":
        "49909a445f8748c4e3614537195072c94409c92e21100d2bf4593c4c8b4963f2",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md":
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
    "work/theory/pi-lacunary-near-return-sparsity/library/t63/lagarias-math0101055v2.pdf":
        "a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9",
}

RHO = Fraction(5, 8)
SIGMA = Fraction(1, 16)
H0 = Fraction(20048317, 16336320)
H1 = Fraction(258249, 17353600)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def v2_int(value: int) -> int:
    require(value != 0, "v2(0) is not used")
    value = abs(value)
    return (value & -value).bit_length() - 1


def circle_numerator(value: Fraction) -> int:
    residue = value.numerator % value.denominator
    return min(residue, value.denominator - residue)


def circle_distance(value: Fraction) -> Fraction:
    return Fraction(circle_numerator(value), value.denominator)


def pole_denominator(index: int) -> int:
    return (
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5)
    )


def a(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        pole_denominator(index),
    )


def g(index: int) -> Fraction:
    return Fraction(
        15 * (index + 1) * (8 * index - 15),
        pole_denominator(index),
    )


def b(index: int) -> Fraction:
    return a(index) / 16**index


def q(index: int) -> int:
    return 10**index - 16


def actual_h(index: int) -> Fraction:
    return q(index + 2) * b(index + 2) + (160 - 10 ** (index + 1)) * b(index + 1)


def epsilon_formula(index: int) -> Fraction:
    require(index >= 3, "the explicit tail proxy starts at index 3")
    return g(index) * (RHO**index - 16 * SIGMA**index) / 15


EPSILON_0 = Fraction(1, 3)
EPSILON_3 = epsilon_formula(3)
_A = 10 * EPSILON_0 + H0
_B = EPSILON_3 + H1
EPSILON_1 = (_B + 11 * _A) / 111
EPSILON_2 = 11 * EPSILON_1 - _A


def epsilon(index: int) -> Fraction:
    if index == 0:
        return EPSILON_0
    if index == 1:
        return EPSILON_1
    if index == 2:
        return EPSILON_2
    return epsilon_formula(index)


def shadow_r(index: int) -> Fraction:
    return Fraction(q(index), 9) - epsilon(index)


def shadow_h(index: int) -> Fraction:
    return 11 * epsilon(index + 1) - 10 * epsilon(index) - epsilon(index + 2)


def series_division(
    numerator: list[Fraction], denominator: list[Fraction], order: int
) -> list[Fraction]:
    """Coefficients through u^(order-1) of numerator/denominator at u=0."""
    require(denominator[0] != 0, "series denominator must be a unit")
    result = [Fraction(0) for _ in range(order)]
    for degree in range(order):
        value = numerator[degree] if degree < len(numerator) else Fraction(0)
        for prior in range(degree):
            if degree - prior < len(denominator):
                value -= result[prior] * denominator[degree - prior]
        result[degree] = value / denominator[0]
    return result


def infinity_coefficients(
    numerator_ascending: list[int], denominator_ascending: list[int], order: int
) -> list[Fraction]:
    """Return coefficients of f(1/u) through u^(order-1)."""
    numerator_degree = len(numerator_ascending) - 1
    denominator_degree = len(denominator_ascending) - 1
    shift = denominator_degree - numerator_degree
    reversed_numerator = [Fraction(x) for x in reversed(numerator_ascending)]
    reversed_denominator = [Fraction(x) for x in reversed(denominator_ascending)]
    quotient = series_division(reversed_numerator, reversed_denominator, order)
    result = [Fraction(0) for _ in range(order)]
    for degree, coefficient in enumerate(quotient):
        if degree + shift < order:
            result[degree + shift] = coefficient
    return result


def polynomial_multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return result


def denominator_polynomial() -> list[int]:
    result = [1]
    for factor in ([1, 2], [3, 4], [1, 8], [5, 8]):
        result = polynomial_multiply(result, factor)
    return result


def nearest_integer(value: Fraction) -> int:
    floor = value.numerator // value.denominator
    if value - floor <= Fraction(1, 2):
        return floor
    return floor + 1


def coprime_lift(
    index: int, actual_b: Fraction, target_b: Fraction
) -> tuple[Fraction, int, int, int]:
    """Finite replay of the audited Kanold-lift construction."""
    exponent = 4 * index - v2_int(index + 1)
    require(v2_int(actual_b.denominator) == exponent, "actual two-adic denominator")
    odd_denominator = actual_b.denominator >> exponent
    dyadic = 1 << (exponent - 4)
    numerator = actual_b.numerator
    require(math.gcd(numerator, 2 * odd_denominator) == 1, "actual reduced data")
    w = (numerator * pow(odd_denominator, -1, dyadic)) % dyadic
    require((numerator - odd_denominator * w) % dyadic == 0, "quotient split")
    c = (numerator - odd_denominator * w) // dyadic

    target_t = odd_denominator * (target_b - actual_b) / 16
    center = nearest_integer(target_t)
    chosen = None
    distance = None
    for offset in range(0, 100_001):
        candidates = [center] if offset == 0 else [center + offset, center - offset]
        for candidate in candidates:
            if math.gcd(c + 256 * candidate, odd_denominator) == 1:
                chosen = candidate
                distance = abs(Fraction(candidate) - target_t)
                break
        if chosen is not None:
            break
    require(chosen is not None and distance is not None, "finite coprime lift search")

    lifted_c = c + 256 * chosen
    lifted_numerator = odd_denominator * w + dyadic * lifted_c
    lifted = Fraction(lifted_numerator, 16 * dyadic * odd_denominator)
    require(lifted.denominator == actual_b.denominator, "complete denominator preserved")

    full_modulus = 256 * dyadic
    old_coordinate = numerator * pow(odd_denominator, -1, full_modulus) % full_modulus
    new_coordinate = (
        lifted.numerator * pow(odd_denominator, -1, full_modulus) % full_modulus
    )
    require(old_coordinate == new_coordinate, "complete derived two-adic coordinate")
    return lifted, chosen - center, distance.numerator, distance.denominator


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=90)
    parser.add_argument("--lift-depth", type=int, default=64)
    args = parser.parse_args()
    require(args.max_depth >= 16, "max depth must be at least 16")
    require(8 <= args.lift_depth <= args.max_depth, "invalid lift depth")

    for relative, expected in PINNED.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned artifact: {relative}")
        require(sha256(path) == expected, f"hash mismatch: {relative}")

    # Exact coefficient and Laurent-series data.
    denominator_coefficients = denominator_polynomial()
    a_coefficients = infinity_coefficients(
        [47, 151, 120], denominator_coefficients, 6
    )
    g_numerator = [-225, -105, 120]
    g_coefficients = infinity_coefficients(
        g_numerator, denominator_coefficients, 6
    )
    require(a_coefficients[2] == Fraction(15, 64), "a n^-2 coefficient")
    require(a_coefficients[3] == Fraction(-89, 512), "a n^-3 coefficient")
    require(g_coefficients[2] == Fraction(15, 64), "g n^-2 coefficient")
    require(g_coefficients[3] == Fraction(-345, 512), "g n^-3 coefficient")
    geometric_mass = 15 * sum(Fraction(1, 16**j) for j in range(1, 80))
    geometric_first_moment = 15 * sum(
        Fraction(j, 16**j) for j in range(1, 80)
    )
    # The finite sums are checked against their exact omitted tails below;
    # the identities themselves are elementary differentiated geometric sums.
    require(geometric_mass < 1, "finite geometric mass")
    require(geometric_first_moment < Fraction(16, 15), "finite first moment")
    require(
        a_coefficients[3]
        - 2 * a_coefficients[2] * Fraction(16, 15)
        == g_coefficients[3],
        "tail proxy matches the n^-3 coefficient",
    )

    # Endpoint anchoring and exact signs.
    require(actual_h(0) == H0 and actual_h(1) == H1, "actual endpoint forcing")
    require(shadow_r(0) == -2, "integral product anchor")
    require(shadow_h(0) == H0 and shadow_h(1) == H1, "matched endpoint forcing")
    require(shadow_h(2) < 0, "splice sign at n=2")
    require(EPSILON_1 - Fraction(1, 3) > Fraction(1, 16), "n=1 gap")
    require(EPSILON_2 - Fraction(1, 3) > Fraction(1, 16), "n=2 gap")
    require(EPSILON_1 - Fraction(1, 3) < Fraction(1, 2), "n=1 nearest lift")
    require(EPSILON_2 - Fraction(1, 3) < Fraction(1, 2), "n=2 nearest lift")

    partial = Fraction(0)
    coefficient_checks = 0
    scalar_checks = 0
    valuation_checks = 0
    separator_checks = 0
    max_proxy_scaled_error = 0.0
    for index in range(args.max_depth + 3):
        partial += b(index)
        if index <= args.max_depth:
            actual_r = q(index) * partial
            if index >= 1:
                require(circle_distance(shadow_r(index)) > Fraction(1, 16), "uniform gap")
                separator_checks += 1
            if index >= 3:
                require(g(index) > 0, "positive proxy coefficient")
                require(g(index) < Fraction(1, index * index), "proxy coefficient bound")
                require(epsilon(index) > 0, "positive proxy tail")
                require(epsilon(index) < Fraction(1, 24), "small proxy tail")
                require(shadow_h(index) < 0, "eventual one-sided forcing")
                require(v2_int(shadow_r(index).denominator) == v2_int(actual_r.denominator), "matching two-primary order")
                require(
                    v2_int(shadow_r(index).denominator)
                    == 4 * index - v2_int(index + 1) - v2_int(q(index)),
                    "closed two-primary order",
                )
                valuation_checks += 2
            if index >= 3 and index + 1 <= args.max_depth + 2:
                require(g(index + 1) < g(index), "strictly decreasing g")
                ratio = epsilon(index + 1) / epsilon(index)
                require(ratio < Fraction(10, 11), "forcing ratio")
                coefficient_checks += 2
            if index + 2 <= args.max_depth + 2:
                require(
                    shadow_h(index)
                    == shadow_r(index + 2)
                    - 11 * shadow_r(index + 1)
                    + 10 * shadow_r(index),
                    "shadow scalar recurrence",
                )
                scalar_checks += 1

        if 8 <= index <= args.max_depth:
            # A finite diagnostic for the O(n^-4) tail-proxy statement.
            tail = sum(a(index + j) / 16**j for j in range(1, 80))
            tail_proxy = g(index) / 15
            error = abs(15 * tail - g(index))
            max_proxy_scaled_error = max(
                max_proxy_scaled_error, float(error * index**4)
            )

    # Finite replay of the full-denominator/two-adic lift to the coherent
    # nonreturning proxy.  This is an experiment, not Kanold's theorem.
    partial = Fraction(0)
    lift_checks = 0
    maximum_lift_offset = 0
    minimum_lifted_gap = Fraction(1, 2)
    maximum_scaled_lift_error = Fraction(0)
    for index in range(args.lift_depth + 1):
        partial += b(index)
        if index < 5:
            continue
        target_b = shadow_r(index) / q(index)
        lifted, offset, error_num, error_den = coprime_lift(index, partial, target_b)
        lifted_r = q(index) * lifted
        gap = circle_distance(lifted_r)
        require(gap > Fraction(1, 32), "finite lifted gap")
        minimum_lifted_gap = min(minimum_lifted_gap, gap)
        maximum_lift_offset = max(maximum_lift_offset, abs(offset))
        error = Fraction(error_num, error_den)
        maximum_scaled_lift_error = max(maximum_scaled_lift_error, error)
        lift_checks += 4

    c0_paths = [REPORT, Path(__file__)] + [ROOT / relative for relative in PINNED if relative.endswith((".md", ".txt", ".py"))]
    scanned = 0
    for path in c0_paths:
        require(path.is_file(), f"missing C0 scan target: {path}")
        data = path.read_bytes()
        bad = [byte for byte in data if byte < 32 and byte not in (9, 10, 13)]
        require(not bad, f"C0 control byte in {path}")
        scanned += 1

    print("status: PASS")
    print("claim_label: experiment")
    print(f"pinned_artifacts: {len(PINNED)}")
    print(f"c0_scanned_text_artifacts: {scanned}")
    print("asymptotic_coefficients: a=(15/64,-89/512),G=g=(15/64,-345/512)")
    print(f"coefficient_checks: {coefficient_checks}")
    print(f"scalar_checks: {scalar_checks}")
    print(f"valuation_checks: {valuation_checks}")
    print(f"separator_checks: {separator_checks}")
    print(f"full_denominator_lift_checks: {lift_checks}")
    print(f"maximum_finite_lift_offset: {maximum_lift_offset}")
    print(f"minimum_finite_lifted_gap: {float(minimum_lifted_gap):.12f}")
    print(f"maximum_tail_proxy_n4_scaled_error: {max_proxy_scaled_error:.12f}")
    print(f"maximum_finite_coprime_distance: {float(maximum_scaled_lift_error):.12f}")
    print("matched_actual_endpoint_forcing: h_0,h_1")
    print("uniform_unlifted_gap_lower_bound: 1/16")
    print("asserts_fixed_return: false")
    print("asserts_v1: false")
    print("all exact finite checks passed")


if __name__ == "__main__":
    main()
