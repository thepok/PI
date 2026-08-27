#!/usr/bin/env python3
"""Exact replay for ``signed_depth_machin_attack.md``.

The script certifies Gaussian-integer identities, rational Taylor shadows,
alternating-tail intervals, local valuations, and finite modular lifts.  It
does not certify the cited analytic or p-adic logarithm theorems and it does
not infer anything about uncomputed digits of pi.
"""

from __future__ import annotations

import hashlib
import math
import sys
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100_000)
getcontext().prec = 50


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gaussian_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def gaussian_pow(base: tuple[int, int], exponent: int) -> tuple[int, int]:
    assert exponent >= 0
    answer = (1, 0)
    while exponent:
        if exponent & 1:
            answer = gaussian_mul(answer, base)
        base = gaussian_mul(base, base)
        exponent //= 2
    return answer


def chi4(odd: int) -> int:
    assert odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def valuation(value: int, prime: int) -> int:
    assert value != 0 and prime > 1
    value = abs(value)
    answer = 0
    while value % prime == 0:
        answer += 1
        value //= prime
    return answer


def rational_valuation(value: Fraction, prime: int) -> int:
    return valuation(value.numerator, prime) - valuation(value.denominator, prime)


def odd_taylor_prefix(argument: Fraction, first_omitted: int) -> Fraction:
    assert first_omitted >= 5 and first_omitted % 4 == 1
    return sum(
        (
            Fraction(chi4(exponent), exponent) * argument**exponent
            for exponent in range(1, first_omitted, 2)
        ),
        Fraction(),
    )


def tail_interval(
    argument: Fraction, first_omitted: int, terms: int = 10
) -> tuple[Fraction, Fraction]:
    """Alternating rational bracket for atan(x) minus its prefix."""
    assert 0 < argument < 1
    assert first_omitted % 4 == 1 and terms >= 1
    partial = Fraction()
    for offset in range(terms):
        term = argument ** (first_omitted + 2 * offset) / (
            first_omitted + 2 * offset
        )
        partial += term if offset % 2 == 0 else -term
    next_term = argument ** (first_omitted + 2 * terms) / (
        first_omitted + 2 * terms
    )
    if terms % 2 == 0:
        lower, upper = partial, partial + next_term
    else:
        lower, upper = partial - next_term, partial
    assert 0 < lower < upper
    return lower, upper


def signed_shadow(
    coefficient: int,
    first: Fraction,
    first_omitted: int,
    second: Fraction,
    second_omitted: int,
) -> Fraction:
    return 4 * (
        coefficient * odd_taylor_prefix(first, first_omitted)
        - odd_taylor_prefix(second, second_omitted)
    )


def signed_error_interval(
    coefficient: int,
    first: Fraction,
    first_omitted: int,
    second: Fraction,
    second_omitted: int,
    terms: int = 10,
) -> tuple[Fraction, Fraction, Fraction]:
    first_lower, first_upper = tail_interval(first, first_omitted, terms)
    second_lower, second_upper = tail_interval(second, second_omitted, terms)
    lower = 4 * (coefficient * first_lower - second_upper)
    upper = 4 * (coefficient * first_upper - second_lower)
    total_lower = 4 * (coefficient * first_lower + second_lower)
    assert lower < upper and total_lower > 0
    return lower, upper, total_lower


def certified_absolute_lower(lower: Fraction, upper: Fraction) -> tuple[int, Fraction]:
    if lower > 0:
        return 1, lower
    if upper < 0:
        return -1, -upper
    raise AssertionError("tail bracket does not determine the sign")


def floor_log10_fraction(value: Fraction) -> int:
    assert value > 0
    numerator = value.numerator
    denominator = value.denominator
    guess = len(str(numerator)) - len(str(denominator))

    def at_least(power: int) -> bool:
        if power >= 0:
            return numerator >= denominator * 10**power
        return numerator * 10 ** (-power) >= denominator

    while not at_least(guess):
        guess -= 1
    while at_least(guess + 1):
        guess += 1
    return guess


def decimal(value: Fraction) -> str:
    return str(Decimal(value.numerator) / Decimal(value.denominator))


def term_valuation(
    outer_coefficient: int, argument: Fraction, exponent: int, prime: int
) -> int:
    return (
        valuation(outer_coefficient, prime)
        + exponent
        * (
            valuation(argument.numerator, prime)
            - valuation(argument.denominator, prime)
        )
        - valuation(exponent, prime)
    )


def all_term_valuations(
    coefficient: int,
    first: Fraction,
    first_omitted: int,
    second: Fraction,
    second_omitted: int,
    prime: int,
) -> list[tuple[int, str, int]]:
    answer: list[tuple[int, str, int]] = []
    for exponent in range(1, first_omitted, 2):
        answer.append(
            (term_valuation(4 * coefficient, first, exponent, prime), "first", exponent)
        )
    for exponent in range(1, second_omitted, 2):
        answer.append((term_valuation(-4, second, exponent, prime), "second", exponent))
    return answer


def unique_least_valuation(data: list[tuple[int, str, int]]) -> tuple[int, str, int]:
    ordered = sorted(data)
    assert len(ordered) >= 2 and ordered[0][0] < ordered[1][0]
    return ordered[0]


def multiplicative_order(base: int, prime: int) -> int:
    assert math.gcd(base, prime) == 1
    value = 1
    for exponent in range(1, prime):
        value = value * base % prime
        if value == 1:
            return exponent
    raise AssertionError("prime-order search exhausted")


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    return all(value % divisor for divisor in range(2, math.isqrt(value) + 1))


def discrete_log_lifts(prime: int, levels: int) -> list[int]:
    """Lift the least residue class solving 10^n = 16 modulo p^k."""
    order = multiplicative_order(10, prime)
    exponent = next(
        candidate
        for candidate in range(order)
        if pow(10, candidate, prime) == 16 % prime
    )
    modulus = prime
    answer: list[int] = []
    for _ in range(levels):
        assert pow(10, exponent, modulus) == 16 % modulus
        answer.append(exponent)
        next_modulus = modulus * prime
        lifts = [
            exponent + digit * order
            for digit in range(prime)
            if pow(10, exponent + digit * order, next_modulus)
            == 16 % next_modulus
        ]
        assert len(lifts) == 1
        exponent = lifts[0]
        modulus = next_modulus
        if pow(10, order, modulus) != 1:
            assert pow(10, order * prime, modulus) == 1
            order *= prime
    return answer


def check_identity_certificates() -> None:
    # (3+i)^3 (11-2i) = 250(1+i).
    first = gaussian_mul(gaussian_pow((3, 1), 3), (11, -2))
    assert first == (250, 250)

    # (7+i)^6 (22049-1457i) is a positive multiple of (1+i).
    second = gaussian_mul(gaussian_pow((7, 1), 6), (22049, -1457))
    assert second[0] == second[1] > 0
    assert Fraction(1457, 22049) < Fraction(1, 7)
    assert math.gcd(22049, 10) == 1
    assert 22049 == 17 * 1297
    assert is_prime(17) and is_prime(1297)
    assert math.gcd(1457, 1297) == 1


def check_common_depth_dominance() -> int:
    checks = 0
    # The report proves the all-depth analytic lower bound.  Here its rational
    # coefficient inequalities and exact alternating brackets are replayed.
    assert Fraction(27, 10) - Fraction(6, 11) == Fraction(237, 110)
    for first_omitted in range(5, 202, 4):
        lower, upper, _ = signed_error_interval(
            3,
            Fraction(1, 3),
            first_omitted,
            Fraction(2, 11),
            first_omitted,
            6,
        )
        analytic_lower = (
            Fraction(474, 55)
            * Fraction(1, 3) ** first_omitted
            / first_omitted
        )
        assert lower > analytic_lower
        assert upper > lower > 0
        checks += 2
    return checks


def finite_signed_depth_rows() -> tuple[list[tuple], list[tuple]]:
    identities = [
        (
            "three-eleven",
            3,
            Fraction(1, 3),
            Fraction(2, 11),
            [(9, 5), (21, 13), (33, 21), (89, 57), (269, 173), (449, 289), (809, 521)],
            11,
        ),
        (
            "seven-22049",
            6,
            Fraction(1, 7),
            Fraction(1457, 22049),
            [(97, 69), (125, 89), (421, 301), (717, 513)],
            1297,
        ),
    ]
    rows: list[tuple] = []
    valuation_rows: list[tuple] = []
    for name, coefficient, first, second, pairs, prime in identities:
        for first_omitted, second_omitted in pairs:
            lower, upper, _ = signed_error_interval(
                coefficient,
                first,
                first_omitted,
                second,
                second_omitted,
                10,
            )
            sign, error_lower = certified_absolute_lower(lower, upper)
            shadow = signed_shadow(
                coefficient, first, first_omitted, second, second_omitted
            )
            denominator = shadow.denominator
            assert denominator * error_lower > 1
            least = unique_least_valuation(
                all_term_valuations(
                    coefficient,
                    first,
                    first_omitted,
                    second,
                    second_omitted,
                    prime,
                )
            )
            assert rational_valuation(shadow, prime) == least[0]
            rows.append(
                (
                    name,
                    first_omitted,
                    second_omitted,
                    sign,
                    len(str(denominator)),
                    floor_log10_fraction(denominator * error_lower),
                )
            )
            valuation_rows.append((name, first_omitted, second_omitted, prime, -least[0]))
    return rows, valuation_rows


def check_deep_cancellation() -> list[tuple[str, int, int, str]]:
    rows: list[tuple[str, int, int, str]] = []

    # This pair gives a genuine 0.025% relative cancellation of the two
    # signed tails.  No full huge rational prefix is needed for the assertion.
    lower, upper, total_lower = signed_error_interval(
        3, Fraction(1, 3), 6209, Fraction(2, 11), 4001, 10
    )
    assert upper < 0
    assert max(abs(lower), abs(upper)) * 4000 < total_lower
    least = unique_least_valuation(
        all_term_valuations(3, Fraction(1, 3), 6209, Fraction(2, 11), 4001, 11)
    )
    assert least == (-3999, "second", 3999)
    rows.append(("three-eleven", 6209, 4001, decimal(abs((lower + upper) / total_lower))))

    # The second identity gets a still cleaner finite balance at (125, 89).
    lower, upper, total_lower = signed_error_interval(
        6, Fraction(1, 7), 125, Fraction(1457, 22049), 89, 10
    )
    assert lower > 0
    assert max(abs(lower), abs(upper)) * 1400 < total_lower
    rows.append(("seven-22049", 125, 89, decimal(abs((lower + upper) / total_lower))))
    return rows


def check_top_layer_cancellation() -> tuple[int, int, int]:
    # At T=2059 the 11-adic scores of exponents 2057 and 2059 tie.
    # Their exact sum gains one factor of 11:
    #   2^2057/17 - 4*2^2057/2059
    # = 2^2057 * 1991/(17*2059), and 1991=11*181.
    assert 2057 == 11**2 * 17
    assert 1991 == 11 * 181
    combined_unit = Fraction(2**2057, 17) - Fraction(4 * 2**2057, 2059)
    assert rational_valuation(combined_unit, 11) == 1

    prefix = odd_taylor_prefix(Fraction(2, 11), 2061)
    assert rational_valuation(prefix, 11) == -2058
    maximum_score = max(
        exponent + valuation(exponent, 11) for exponent in range(1, 2060, 2)
    )
    assert maximum_score == 2059
    return 2059, maximum_score, -rational_valuation(prefix, 11)


def check_infinite_score_separated_schedules() -> int:
    checks = 0

    # For p=11 and odd e, T=p^e is 3 modulo 4 and is the unique term with
    # denominator score T+e.  A first-component depth below 2T contributes
    # only exponent-denominator score at most e.
    for exponent in [1, 3, 5, 7]:
        prime = 11
        maximum = prime**exponent
        assert maximum % 4 == 3
        assert maximum + exponent > maximum - 2 + exponent - 1
        assert maximum + exponent > exponent
        checks += 3

    # For p=1297 and e>=3, take the second-component maximum T=p^e+2.
    # The preceding exponent p^e, not the endpoint, is the unique score
    # maximum p^e+e; all earlier exponents lose at least three.
    for exponent in [3, 4, 5, 6]:
        prime = 1297
        prime_power = prime**exponent
        maximum = prime_power + 2
        first_omitted = maximum + 2
        assert first_omitted % 4 == 1
        dominant_score = prime_power + exponent
        assert dominant_score > maximum
        assert dominant_score > prime_power - 2 + exponent - 1
        assert dominant_score > exponent + 1
        checks += 4
    return checks


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    check_identity_certificates()
    common_checks = check_common_depth_dominance()
    finite_rows, valuation_rows = finite_signed_depth_rows()
    deep_rows = check_deep_cancellation()
    cancellation = check_top_layer_cancellation()
    infinite_schedule_checks = check_infinite_score_separated_schedules()

    # For c=16, a surviving factor 11 is an absolute modular obstruction.
    powers_mod_11 = {pow(10, exponent, 11) for exponent in range(1, 3)}
    assert powers_mod_11 == {1, 10}
    assert 16 % 11 not in powers_mod_11

    lifts_17 = discrete_log_lifts(17, 8)
    lifts_1297 = discrete_log_lifts(1297, 6)
    assert lifts_17 == [8, 168, 2344, 71704, 71704, 12098728, 330146696, 1874951112]
    assert lifts_1297 == [
        616,
        1043896,
        1971072760,
        2288940937096,
        3282357482682376,
        3806434174632201688,
    ]

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print("gaussian_signed_identity_exact_checks=7")
    print(f"common_depth_dominance_exact_checks={common_checks}")
    for row in finite_rows:
        name, first_omitted, second_omitted, sign, denominator_digits, q_error_floor = row
        print(
            "finite_balance"
            f" name={name} R={first_omitted} S={second_omitted}"
            f" sign={sign:+d} denominator_digits={denominator_digits}"
            f" floor_log10_q_error_lower={q_error_floor}"
        )
    for row in valuation_rows:
        name, first_omitted, second_omitted, prime, denominator_valuation = row
        print(
            "private_score"
            f" name={name} R={first_omitted} S={second_omitted}"
            f" prime={prime} denominator_valuation={denominator_valuation}"
        )
    for name, first_omitted, second_omitted, relative in deep_rows:
        print(
            "deep_tail_balance"
            f" name={name} R={first_omitted} S={second_omitted}"
            f" signed_over_unsigned_midpoint={relative}"
        )
    print(
        "top_layer_cancellation"
        f" T={cancellation[0]} formal_max_score={cancellation[1]}"
        f" actual_denominator_valuation={cancellation[2]}"
    )
    print(f"infinite_score_separated_symbolic_checks={infinite_schedule_checks}")
    print(f"c16_p17_lift_residues={','.join(map(str, lifts_17))}")
    print(f"c16_p1297_lift_residues={','.join(map(str, lifts_1297))}")
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
