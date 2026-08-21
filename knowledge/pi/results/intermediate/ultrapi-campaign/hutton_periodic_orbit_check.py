#!/usr/bin/env python3
"""Exact finite replay for ``hutton_periodic_orbit_attack.md``.

Every assertion uses integer or ``Fraction`` arithmetic.  The block scans are
finite experiments about rational Hutton truncations; they are not evidence
that the same blocks occur in every scale, or a proof of the pi conjecture.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    """The prime-adic valuation of a positive integer."""
    assert value > 0 and prime > 1
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def fraction_valuation(value: Fraction, prime: int) -> int:
    assert value
    return valuation(abs(value.numerator), prime) - valuation(value.denominator, prime)


def primes_through(bound: int) -> list[int]:
    result: list[int] = []
    for candidate in range(2, bound + 1):
        if all(candidate % prime for prime in result if prime * prime <= candidate):
            result.append(candidate)
    return result


def factor_over_bound(value: int, bound: int) -> dict[int, int]:
    """Factor a number known to have no prime divisor above ``bound``."""
    assert value > 0
    factors: dict[int, int] = {}
    for prime in primes_through(bound):
        exponent = 0
        while value % prime == 0:
            value //= prime
            exponent += 1
        if exponent:
            factors[prime] = exponent
    assert value == 1
    return factors


def euler_phi_from_factorization(factors: dict[int, int]) -> int:
    result = 1
    for prime, exponent in factors.items():
        result *= (prime - 1) * prime ** (exponent - 1)
    return result


def multiplicative_order_10(modulus: int, factor_bound: int) -> int:
    assert modulus > 1 and math.gcd(modulus, 10) == 1
    modulus_factors = factor_over_bound(modulus, factor_bound)
    order = euler_phi_from_factorization(modulus_factors)
    order_factors = factor_over_bound(order, factor_bound)
    for prime, exponent in order_factors.items():
        for _ in range(exponent):
            if order % prime == 0 and pow(10, order // prime, modulus) == 1:
                order //= prime
            else:
                break
    assert pow(10, order, modulus) == 1
    for prime in factor_over_bound(order, factor_bound):
        assert pow(10, order // prime, modulus) != 1
    return order


def ceil_log10(value: int) -> int:
    """Smallest nonnegative d with value <= 10**d, using integers only."""
    assert value >= 1
    exponent = 0
    power = 1
    while power < value:
        power *= 10
        exponent += 1
    return exponent


def arctan_partial(base: int, terms: int) -> Fraction:
    return sum(
        (
            Fraction((-1) ** index, (2 * index + 1) * base ** (2 * index + 1))
            for index in range(terms)
        ),
        Fraction(),
    )


def hutton_lower(index: int) -> Fraction:
    assert index >= 0
    terms = 2 * index + 2
    return 8 * arctan_partial(3, terms) + 4 * arctan_partial(7, terms)


def odd_lcm(bound: int) -> int:
    result = 1
    for odd in range(1, bound + 1, 2):
        result = math.lcm(result, odd)
    return result


def natural_data(index: int) -> tuple[int, int, int, int]:
    """Return ``(R, A, D, gcd(A,D))`` for the natural Hutton lift."""
    radius = 4 * index + 3
    denominator = odd_lcm(radius) * 3**radius * 7**radius
    numerator = 0
    for odd in range(1, radius + 1, 2):
        sign = -1 if ((odd - 1) // 2) % 2 else 1
        numerator += sign * (
            8 * (denominator // (odd * 3**odd))
            + 4 * (denominator // (odd * 7**odd))
        )
    common = math.gcd(numerator, denominator)
    return radius, numerator, denominator, common


def adjacent_width(index: int) -> Fraction:
    next_odd = 4 * index + 5
    return Fraction(8, next_odd * 3**next_odd) + Fraction(
        4, next_odd * 7**next_odd
    )


def bracket_horizon(index: int) -> int:
    """Largest j for which scaling the exact adjacent bracket keeps width < 1."""
    width = adjacent_width(index)
    scale = 1
    answer = -1
    while scale * width < 1:
        answer += 1
        scale *= 10
    assert 10**answer * width < 1 <= 10 ** (answer + 1) * width
    return answer


def linear_block_scan(value: Fraction, limit: int, maximum_length: int = 4) -> tuple[list[int | None], list[int]]:
    """Scan a finite decimal prefix and return completion times and counts."""
    remainder = value.numerator % value.denominator
    rolling = 0
    modulus = 10**maximum_length
    seen = [set() for _ in range(maximum_length + 1)]
    completed: list[int | None] = [None] * (maximum_length + 1)
    for position in range(limit):
        remainder *= 10
        digit, remainder = divmod(remainder, value.denominator)
        assert 0 <= digit <= 9
        rolling = (10 * rolling + digit) % modulus
        for length in range(1, maximum_length + 1):
            if position + 1 >= length and completed[length] is None:
                seen[length].add(rolling % 10**length)
                if len(seen[length]) == 10**length:
                    completed[length] = position + 1
    return completed[1:], [len(seen[length]) for length in range(1, maximum_length + 1)]


def cyclic_block_counts(value: Fraction, transient: int, period: int, maximum_length: int = 4) -> list[int]:
    """Count distinct cyclic words in one exact rational repetend."""
    remainder = value.numerator % value.denominator
    digits: list[int] = []
    for _ in range(transient + period):
        remainder *= 10
        digit, remainder = divmod(remainder, value.denominator)
        digits.append(digit)
    cycle = digits[transient:]
    return [
        len(
            {
                tuple(cycle[(start + offset) % period] for offset in range(length))
                for start in range(period)
            }
        )
        for length in range(1, maximum_length + 1)
    ]


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    denominator_checks = 0
    recurrence_checks = 0
    pair_valuation_checks = 0
    for index in range(0, 61):
        value = hutton_lower(index)
        radius, numerator, denominator, common = natural_data(index)
        assert value == Fraction(numerator, denominator)
        assert value.numerator == numerator // common
        assert value.denominator == denominator // common
        assert value.denominator % 2 == 1
        assert valuation(value.denominator, 5) <= valuation(odd_lcm(radius), 5)
        denominator_checks += 5

        if index == 0:
            continue

        previous = hutton_lower(index - 1)
        delta = value - previous
        expected_delta = Fraction(
            16 * (4 * radius + 1), radius * (radius - 2) * 3**radius
        ) + Fraction(
            8 * (24 * radius + 1), radius * (radius - 2) * 7**radius
        )
        assert delta == expected_delta
        recurrence_checks += 1

        # Each base-specific summand is uniquely dominant at its own prime.
        assert 3**radius > 4 * radius + 1
        assert 7**radius > 24 * radius + 1
        delta_e3 = (
            radius
            + valuation(radius, 3)
            + valuation(radius - 2, 3)
            - valuation(4 * radius + 1, 3)
        )
        delta_e7 = (
            radius
            + valuation(radius, 7)
            + valuation(radius - 2, 7)
            - valuation(24 * radius + 1, 7)
        )
        assert fraction_valuation(delta, 3) == -delta_e3
        assert fraction_valuation(delta, 7) == -delta_e7
        assert max(
            valuation(value.denominator, 3), valuation(previous.denominator, 3)
        ) >= delta_e3
        assert max(
            valuation(value.denominator, 7), valuation(previous.denominator, 7)
        ) >= delta_e7
        pair_valuation_checks += 4

    expected_rows = [
        # K, q bits, v5(q), exact post-transient order, bracket horizon
        (0, 15, 0, 882, 2),
        (1, 36, 1, 400241898, 4),
        (2, 55, 1, 11119920652134, 6),
        (3, 77, 1, 6487839865043017362, 8),
        (4, 98, 1, 420587194931143686526374, 10),
        (5, 120, 1, 899758400831441308292693160834, 12),
        (6, 144, 2, 4724619665906687501107923982528243158, 14),
        (7, 167, 2, 340314354535258700704803764461509354670740, 16),
        (8, 187, 2, 463292731890601531602396586413671605640041301580, 18),
    ]
    orbit_rows: list[tuple[int, int, int, int, int, int, int]] = []
    for index, expected_bits, expected_v5, expected_order, expected_horizon in expected_rows:
        value = hutton_lower(index)
        radius = 4 * index + 3
        exponent_5 = valuation(value.denominator, 5)
        modulus = value.denominator // 5**exponent_5
        factor_bound = max(7, radius)
        order = multiplicative_order_10(modulus, factor_bound)
        assert value.denominator.bit_length() == expected_bits
        assert exponent_5 == expected_v5
        assert order == expected_order
        assert bracket_horizon(index) == expected_horizon

        exponent_3 = valuation(modulus, 3)
        exponent_7 = valuation(modulus, 7)
        order_3 = 1 if exponent_3 <= 2 else 3 ** (exponent_3 - 2)
        order_7 = 1 if exponent_7 == 0 else 6 * 7 ** (exponent_7 - 1)
        assert order % math.lcm(order_3, order_7) == 0
        assert order >= ceil_log10(modulus + 1)
        orbit_rows.append(
            (
                index,
                value.denominator.bit_length(),
                exponent_3,
                exponent_7,
                exponent_5,
                order,
                expected_horizon,
            )
        )

    # K=0 has a genuinely complete 882-cycle, but it cannot contain all
    # 1000 three-digit words.  The exact cyclic counts sharpen that pigeonhole.
    value_zero = hutton_lower(0)
    cyclic_counts = cyclic_block_counts(value_zero, transient=0, period=882)
    assert cyclic_counts == [10, 100, 631, 882]

    # Finite prefix experiments.  These show that small-K full coverage for
    # lengths 3 and 4 first occurs vastly beyond the certified bracket horizon.
    expected_completion = {
        0: ([23, 458, None, None], [10, 100, 631, 882]),
        1: ([22, 468, 8798, 92461], [10, 100, 1000, 10000]),
        2: ([24, 414, 7427, 98103], [10, 100, 1000, 10000]),
        3: ([38, 377, 7953, 81030], [10, 100, 1000, 10000]),
        4: ([30, 504, 9405, 125672], [10, 100, 1000, 10000]),
        5: ([16, 483, 10289, 97982], [10, 100, 1000, 10000]),
        6: ([28, 519, 7411, 100440], [10, 100, 1000, 10000]),
        7: ([25, 457, 6550, 95831], [10, 100, 1000, 10000]),
        8: ([19, 514, 8057, 108134], [10, 100, 1000, 10000]),
    }
    for index, (expected_done, expected_counts) in expected_completion.items():
        limit = 2_000 if index == 0 else 150_000
        completed, counts = linear_block_scan(hutton_lower(index), limit)
        assert completed == expected_done
        assert counts == expected_counts

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"natural_denominator_exact_checks={denominator_checks}")
    print(f"adjacent_increment_exact_checks={recurrence_checks}")
    print(f"pair_prime_valuation_exact_checks={pair_valuation_checks}")
    print("orbit_rows=(K,q_bits,v3_q,v7_q,v5_q,ord_m_10,bracket_horizon):")
    for row in orbit_rows:
        print(row)
    print(f"K0_exact_cyclic_word_counts_lengths_1_to_4={cyclic_counts}")
    print("prefix_completion_rows=(K,completion_lengths_1_to_4):")
    for index, (completion, _) in expected_completion.items():
        print((index, completion))
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
