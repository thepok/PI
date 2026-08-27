#!/usr/bin/env python3
"""Independent exact checks for the signed depth-varying Machin audit.

This file deliberately does not import the primary checker.  It recomputes the
Gaussian certificates, alternating-tail brackets, reduced rational shadows,
the 2059 cancellation, the score-separated valuation bounds, and the displayed
modular lifts.  It does not prove either cited transcendence theorem or V1.
"""

from __future__ import annotations

import hashlib
import math
import sys
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
REPORT_SHA256 = "87dfb60e128a7ea5a321af93c5b99065461133966f14bb68c1248fcd64d50ce9"
PRIMARY_CHECKER_SHA256 = "f2ef77adf962217bce6d3f8884d461fa0d0502f9d0f67e302a587016a2aa8206"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100_000)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gaussian_product(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return left[0] * right[0] - left[1] * right[1], left[0] * right[1] + left[1] * right[0]


def gaussian_power(base: tuple[int, int], exponent: int) -> tuple[int, int]:
    result = (1, 0)
    for _ in range(exponent):
        result = gaussian_product(result, base)
    return result


def v_p(integer: int, prime: int) -> int:
    assert integer != 0
    integer = abs(integer)
    value = 0
    while integer % prime == 0:
        integer //= prime
        value += 1
    return value


def rational_v_p(value: Fraction, prime: int) -> int:
    return v_p(value.numerator, prime) - v_p(value.denominator, prime)


def sign4(exponent: int) -> int:
    assert exponent % 2 == 1
    return 1 if exponent % 4 == 1 else -1


def taylor_prefix(argument: Fraction, first_omitted: int) -> Fraction:
    assert first_omitted >= 5 and first_omitted % 4 == 1
    result = Fraction(0)
    for exponent in range(1, first_omitted, 2):
        result += sign4(exponent) * argument**exponent / exponent
    return result


def tail_bracket(
    argument: Fraction, first_omitted: int, term_count: int = 12
) -> tuple[Fraction, Fraction]:
    """Exact alternating bracket, independently using twelve terms."""
    assert 0 < argument < 1
    assert first_omitted % 4 == 1 and term_count % 2 == 0
    partial = Fraction(0)
    for index in range(term_count):
        exponent = first_omitted + 2 * index
        partial += (-1) ** index * argument**exponent / exponent
    next_exponent = first_omitted + 2 * term_count
    next_term = argument**next_exponent / next_exponent
    return partial, partial + next_term


def signed_tail_interval(
    coefficient: int,
    first: Fraction,
    first_omitted: int,
    second: Fraction,
    second_omitted: int,
) -> tuple[Fraction, Fraction, Fraction]:
    first_lo, first_hi = tail_bracket(first, first_omitted)
    second_lo, second_hi = tail_bracket(second, second_omitted)
    signed_lo = 4 * (coefficient * first_lo - second_hi)
    signed_hi = 4 * (coefficient * first_hi - second_lo)
    unsigned_lo = 4 * (coefficient * first_lo + second_lo)
    assert signed_lo < signed_hi and unsigned_lo > 0
    return signed_lo, signed_hi, unsigned_lo


def absolute_lower(interval: tuple[Fraction, Fraction]) -> Fraction:
    lo, hi = interval
    if lo > 0:
        return lo
    if hi < 0:
        return -hi
    raise AssertionError("the exact interval does not determine a sign")


def floor_log10(value: Fraction) -> int:
    assert value > 0
    numerator, denominator = value.numerator, value.denominator
    estimate = len(str(numerator)) - len(str(denominator))

    def at_least(power: int) -> bool:
        if power >= 0:
            return numerator >= denominator * 10**power
        return numerator * 10 ** (-power) >= denominator

    while not at_least(estimate):
        estimate -= 1
    while at_least(estimate + 1):
        estimate += 1
    return estimate


def signed_shadow(
    coefficient: int,
    first: Fraction,
    first_omitted: int,
    second: Fraction,
    second_omitted: int,
) -> Fraction:
    return 4 * (
        coefficient * taylor_prefix(first, first_omitted)
        - taylor_prefix(second, second_omitted)
    )


def check_gaussian_certificates() -> None:
    assert gaussian_product(gaussian_power((3, 1), 3), (11, -2)) == (250, 250)
    assert gaussian_product(gaussian_power((7, 1), 6), (22049, -1457)) == (
        1_953_125_000,
        1_953_125_000,
    )
    assert Fraction(1457, 22049) < Fraction(1, 7)
    assert 22049 == 17 * 1297
    assert math.gcd(1457, 17 * 1297) == 1


def check_equal_depth_bound() -> int:
    count = 0
    for first_omitted in range(5, 402, 4):
        lo, hi, _ = signed_tail_interval(
            3,
            Fraction(1, 3),
            first_omitted,
            Fraction(2, 11),
            first_omitted,
        )
        report_lower = Fraction(474, 55) * Fraction(1, 3) ** first_omitted / first_omitted
        assert hi > lo > report_lower > 0
        count += 1
    return count


def check_finite_rows() -> int:
    expected = [
        (3, Fraction(1, 3), Fraction(2, 11), 89, 57, 131, 85),
        (3, Fraction(1, 3), Fraction(2, 11), 269, 173, 413, 281),
        (3, Fraction(1, 3), Fraction(2, 11), 449, 289, 700, 481),
        (3, Fraction(1, 3), Fraction(2, 11), 809, 521, 1261, 871),
        (6, Fraction(1, 7), Fraction(1457, 22049), 125, 89, 528, 418),
        (6, Fraction(1, 7), Fraction(1457, 22049), 421, 301, 1826, 1466),
        (6, Fraction(1, 7), Fraction(1457, 22049), 717, 513, 3124, 2514),
    ]
    for coefficient, first, second, first_depth, second_depth, digits, exponent in expected:
        shadow = signed_shadow(coefficient, first, first_depth, second, second_depth)
        lo, hi, _ = signed_tail_interval(
            coefficient, first, first_depth, second, second_depth
        )
        lower = absolute_lower((lo, hi))
        assert len(str(shadow.denominator)) == digits
        assert floor_log10(shadow.denominator * lower) == exponent
        assert shadow.denominator * lower > 1
    return len(expected)


def check_deep_balances() -> None:
    lo, hi, unsigned_lo = signed_tail_interval(
        3, Fraction(1, 3), 6209, Fraction(2, 11), 4001
    )
    assert hi < 0 and max(abs(lo), abs(hi)) * 4000 < unsigned_lo

    lo, hi, unsigned_lo = signed_tail_interval(
        6, Fraction(1, 7), 125, Fraction(1457, 22049), 89
    )
    assert lo > 0 and max(abs(lo), abs(hi)) * 1400 < unsigned_lo


def check_2059_cancellation_mod_121() -> int:
    """Compute 11^2059 L_2061(2/11) modulo 11^2 without Fraction."""
    prime, modulus = 11, 121
    residue = 0
    active = []
    for exponent in range(1, 2060, 2):
        denominator_order = v_p(exponent, prime)
        scaled_order = 2059 - exponent - denominator_order
        assert scaled_order >= 0
        if scaled_order >= 2:
            continue
        prime_free_denominator = exponent // prime**denominator_order
        term = (
            sign4(exponent)
            * pow(2, exponent, modulus)
            * pow(prime, scaled_order, modulus)
            * pow(prime_free_denominator, -1, modulus)
        ) % modulus
        residue = (residue + term) % modulus
        active.append(exponent)
    assert active == [2057, 2059]
    assert residue == 22
    assert residue % 11 == 0 and residue % 121 != 0
    return 2059 - 1


def check_score_separated_families() -> int:
    checks = 0
    # First family: brute-force the private-component score at two independent
    # admissible exponents and verify the generic comparison inequalities.
    for exponent in (1, 3):
        prime = 11
        endpoint = prime**exponent
        scores = [(r + v_p(r, prime), r) for r in range(1, endpoint + 1, 2)]
        scores.sort(reverse=True)
        assert scores[0] == (endpoint + exponent, endpoint)
        assert scores[1][0] <= endpoint + exponent - 3
        assert exponent < endpoint + exponent
        checks += 3

    # Second family: p^e is the unique high layer, while the endpoint p^e+2
    # and all earlier terms have strictly smaller scores for every e >= 3.
    for exponent in (3, 4, 7):
        prime = 1297
        power = prime**exponent
        dominant = power + exponent
        endpoint = power + 2
        earlier_upper = power + exponent - 3
        assert dominant > endpoint
        assert dominant > earlier_upper
        assert exponent < dominant
        assert (power + 4) % 4 == 1
        checks += 4
    return checks


def factor_small(integer: int) -> list[int]:
    factors = []
    divisor = 2
    while divisor * divisor <= integer:
        if integer % divisor == 0:
            factors.append(divisor)
            while integer % divisor == 0:
                integer //= divisor
        divisor += 1
    if integer > 1:
        factors.append(integer)
    return factors


def order_mod_prime_power(base: int, prime: int, level: int) -> int:
    modulus = prime**level
    candidate = (prime - 1) * prime ** (level - 1)
    factors = factor_small(prime - 1)
    if level > 1:
        factors.append(prime)
    for factor in factors:
        while candidate % factor == 0 and pow(base, candidate // factor, modulus) == 1:
            candidate //= factor
    assert pow(base, candidate, modulus) == 1
    return candidate


def check_lift_chain(prime: int, residues: list[int]) -> None:
    first_order = order_mod_prime_power(10, prime, 1)
    first = next(n for n in range(first_order) if pow(10, n, prime) == 16 % prime)
    assert first == residues[0]
    for level, residue in enumerate(residues, start=1):
        modulus = prime**level
        order = order_mod_prime_power(10, prime, level)
        assert 0 <= residue < order
        assert pow(10, residue, modulus) == 16 % modulus
        if level > 1:
            previous_order = order_mod_prime_power(10, prime, level - 1)
            assert (residue - residues[level - 2]) % previous_order == 0
            assert order == previous_order * prime


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    report = root / "work/ultrapi-resume/signed_depth_machin_attack.md"
    primary_checker = root / "work/ultrapi-resume/signed_depth_machin_attack_check.py"
    assert file_sha256(source) == SOURCE_SHA256
    assert file_sha256(report) == REPORT_SHA256
    assert file_sha256(primary_checker) == PRIMARY_CHECKER_SHA256

    check_gaussian_certificates()
    common_depth_checks = check_equal_depth_bound()
    finite_rows = check_finite_rows()
    check_deep_balances()
    reduced_valuation = check_2059_cancellation_mod_121()
    family_checks = check_score_separated_families()
    check_lift_chain(
        17,
        [8, 168, 2344, 71704, 71704, 12098728, 330146696, 1874951112],
    )
    check_lift_chain(
        1297,
        [
            616,
            1043896,
            1971072760,
            2288940937096,
            3282357482682376,
            3806434174632201688,
        ],
    )

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"report_sha256={REPORT_SHA256}")
    print(f"primary_checker_sha256={PRIMARY_CHECKER_SHA256}")
    print("gaussian_certificates=PASS")
    print(f"independent_equal_depth_instances={common_depth_checks}")
    print(f"independent_finite_rows={finite_rows}")
    print("deep_signed_tail_balances=PASS")
    print(f"v11_den_L2061_2_over_11={reduced_valuation}")
    print(f"score_family_checks={family_checks}")
    print("modular_lift_chains=PASS")
    print("V1_proved=false")
    print("all independent exact assertions passed")


if __name__ == "__main__":
    main()
