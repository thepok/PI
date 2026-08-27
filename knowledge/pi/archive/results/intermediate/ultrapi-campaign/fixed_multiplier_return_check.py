#!/usr/bin/env python3
"""Exact finite replay for fixed-multiplier return identities.

All theorem-level conclusions remain proof sketches in the companion report.
This script checks only finite integer/rational identities and labels its
output `experiment`.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from math import comb, gcd
from pathlib import Path


EXPECTED_SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)


def source_path() -> Path:
    return Path(__file__).resolve().parents[2] / "problems/local/pi-digits.txt"


def v_p_integer(value: int, prime: int) -> int:
    assert value != 0
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def primes_through(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    if limit >= 0:
        sieve[0] = False
    if limit >= 1:
        sieve[1] = False
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = False
    return [p for p in range(2, limit + 1) if sieve[p]]


def wallis_shadow(index: int) -> Fraction:
    answer = Fraction(2)
    for k in range(1, index + 1):
        answer *= Fraction(4 * k * k, 4 * k * k - 1)
    return answer


def ramanujan_scaled_numerator(index: int) -> int:
    """U_N with S_N = U_N / 2^(12N)."""
    return sum(
        (42 * k + 5) * comb(2 * k, k) ** 3 * 2 ** (12 * (index - k))
        for k in range(index + 1)
    )


def ramanujan_sum(index: int) -> Fraction:
    return Fraction(ramanujan_scaled_numerator(index), 2 ** (12 * index))


def ramanujan_pi_shadow(index: int) -> Fraction:
    return 16 / ramanujan_sum(index)


def ramanujan_term(index: int) -> Fraction:
    return Fraction((42 * index + 5) * comb(2 * index, index) ** 3, 2 ** (12 * index))


def bbp_coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def bbp_shadow(index: int) -> Fraction:
    return sum((bbp_coefficient(k) / 16**k for k in range(index + 1)), Fraction())


def lift_discrete_log_10_to_c_mod_prime_power(
    prime: int, target: int, maximum_exponent: int
) -> list[int]:
    """Lift the unique exponent for the concrete primitive-root test case."""
    candidates = [
        n
        for n in range(1, prime)
        if pow(10, n, prime) == target % prime
    ]
    assert len(candidates) == 1
    answer = [candidates[0]]
    exponent = candidates[0]
    old_order = prime - 1
    modulus = prime
    for _power in range(2, maximum_exponent + 1):
        next_modulus = modulus * prime
        lifts = [
            exponent + digit * old_order
            for digit in range(prime)
            if pow(10, exponent + digit * old_order, next_modulus)
            == target % next_modulus
        ]
        assert len(lifts) == 1
        exponent = lifts[0]
        answer.append(exponent)
        modulus = next_modulus
        old_order *= prime
    return answer


def main() -> None:
    source_hash = sha256(source_path().read_bytes()).hexdigest()
    assert source_hash == EXPECTED_SOURCE_SHA256

    wallis_prime_checks = 0
    wallis_telescoping_checks = 0
    primes = primes_through(180)
    for index in range(2, 81):
        shadow = wallis_shadow(index)
        for prime in primes:
            if index < prime <= 2 * index:
                assert v_p_integer(shadow.denominator, prime) == 2
                wallis_prime_checks += 1
        for endpoint in (index + 1, index + 7, 2 * index + 19):
            partial_tail = sum(
                (Fraction(1, 4 * k * k - 1) for k in range(index + 1, endpoint + 1)),
                Fraction(),
            )
            assert partial_tail + Fraction(1, 4 * endpoint + 2) == Fraction(
                1, 4 * index + 2
            )
            wallis_telescoping_checks += 1

    ramanujan_valuation_checks = 0
    ramanujan_denominator_checks = 0
    ramanujan_tail_checks = 0
    for index in range(0, 81):
        scaled = ramanujan_scaled_numerator(index)
        expected_v2 = 3 * index.bit_count()
        assert v_p_integer(scaled, 2) == expected_v2
        shadow = ramanujan_pi_shadow(index)
        expected_denominator = scaled // 2**expected_v2
        assert shadow.denominator == expected_denominator
        assert expected_denominator >= 5 * 2 ** (12 * index - expected_v2)
        ramanujan_valuation_checks += 1
        ramanujan_denominator_checks += 1

        next_index = index + 1
        assert comb(2 * next_index, next_index) * (2 * next_index + 1) >= 4**next_index
        lower = Fraction(
            42 * next_index + 5,
            64**next_index * (2 * next_index + 1) ** 3,
        )
        assert ramanujan_term(next_index) >= lower
        ramanujan_tail_checks += 1

    # In lowest terms q*A_N is integral exactly when den(A_N) divides q.
    anchor_equivalence_checks = 0
    exact_anchor_hits: list[tuple[int, int, int]] = []
    for c in (2, 3, 4, 16, 19):
        for decimal_exponent in range(1, 41):
            q = 10**decimal_exponent - c
            if q <= 0:
                continue
            for index in range(0, 13):
                shadow = ramanujan_pi_shadow(index)
                integral = (q * shadow).denominator == 1
                divides = q % shadow.denominator == 0
                assert integral == divides
                anchor_equivalence_checks += 1
                if integral:
                    exact_anchor_hits.append((c, decimal_exponent, index))

    bbp_two_adic_checks = 0
    bbp_fixed_c_exclusions = 0
    for index in range(1, 61):
        shadow = bbp_shadow(index)
        expected = 4 * index - v_p_integer(index + 1, 2)
        assert v_p_integer(shadow.denominator, 2) == expected
        bbp_two_adic_checks += 1
        for c in (2, 3, 4, 16, 40):
            c_v2 = v_p_integer(c, 2) if c % 2 == 0 else 0
            decimal_exponent = max(c_v2 + 1, 2)
            q = 10**decimal_exponent - c
            if expected > c_v2:
                assert q % shadow.denominator != 0
                bbp_fixed_c_exclusions += 1

    # A concrete local-congruence example: 10^n = 3 (mod 7^M).
    lifted = lift_discrete_log_10_to_c_mod_prime_power(7, 3, 12)
    for power, exponent in enumerate(lifted, start=1):
        assert pow(10, exponent, 7**power) == 3 % 7**power
        if power > 1:
            assert exponent % (6 * 7 ** (power - 2)) == lifted[power - 2]

    print("claim_status=experiment")
    print(f"source_sha256={source_hash}")
    print(f"wallis_prime_denominator_checks={wallis_prime_checks}")
    print(f"wallis_tail_telescoping_checks={wallis_telescoping_checks}")
    print(f"ramanujan_exact_two_adic_checks={ramanujan_valuation_checks}")
    print(f"ramanujan_reduced_denominator_checks={ramanujan_denominator_checks}")
    print(f"ramanujan_first_tail_lower_checks={ramanujan_tail_checks}")
    print(f"ramanujan_anchor_equivalence_checks={anchor_equivalence_checks}")
    print(f"ramanujan_small_exact_anchor_hits={exact_anchor_hits}")
    print(f"bbp_exact_two_adic_checks={bbp_two_adic_checks}")
    print(f"bbp_fixed_c_divisibility_exclusions={bbp_fixed_c_exclusions}")
    print("seven_adic_lifted_exponents=" + ",".join(map(str, lifted)))
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
