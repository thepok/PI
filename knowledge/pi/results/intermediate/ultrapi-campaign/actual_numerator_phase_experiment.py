#!/usr/bin/env python3
"""Exact falsification checks for the Machin complementary-numerator phase.

Every output has claim status ``experiment``.  The program uses Fraction and
integer modular arithmetic only; it neither evaluates pi nor reads pi digits.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd, isqrt


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def valuation(value: int, prime: int) -> int:
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def rational_valuation(value: Fraction, prime: int) -> int:
    return valuation(abs(value.numerator), prime) - valuation(
        value.denominator, prime
    )


def rational_mod(value: Fraction, prime: int) -> int:
    return value.numerator * pow(value.denominator, -1, prime) % prime


def coefficient(term_count: int) -> Fraction:
    """The fixed C_r left by odd multiples p,...,(2r-1)p."""
    result = Fraction()
    for index in range(term_count):
        odd = 2 * index + 1
        sign = -1 if index & 1 else 1
        result += 4 * sign * Fraction(4 * 239**odd - 5**odd,
                                      odd * 5**odd * 239**odd)
    return result


def machin_seed(index: int) -> Fraction:
    five = sum(
        (Fraction(-1 if k & 1 else 1, (2 * k + 1) * 5 ** (2 * k + 1))
         for k in range(6 * index + 2)),
        Fraction(),
    )
    two_three_nine = sum(
        (Fraction(-1 if k & 1 else 1,
                  (2 * k + 1) * 239 ** (2 * k + 1))
         for k in range(6 * index + 3)),
        Fraction(),
    )
    return 10**index * (16 * five - 4 * two_three_nine)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=50)
    args = parser.parse_args()
    if args.max_j < 2:
        raise SystemExit("--max-j must be at least two")

    primes = primes_up_to(12 * args.max_j + 5)
    checked_residues = 0
    cancelled_coefficients = 0
    nesting_failures: list[tuple[int, int]] = []
    quotient_checks = 0
    previous_denominator: int | None = None

    for j in range(1, args.max_j + 1):
        seed = machin_seed(j)
        denominator = seed.denominator
        residue = seed.numerator % denominator
        d = 12 * j + 3

        if previous_denominator is not None and denominator % previous_denominator:
            lost = previous_denominator // gcd(previous_denominator, denominator)
            nesting_failures.append((j, lost))
        previous_denominator = denominator

        for p in primes:
            if p <= isqrt(d + 2) or p > d or p in (5, 239):
                continue
            if (d + 2) % p == 0:
                continue
            largest_multiplier = d // p
            term_count = (largest_multiplier + 1) // 2
            fixed = coefficient(term_count)
            if fixed.numerator % p == 0:
                cancelled_coefficients += 1
                continue
            if rational_valuation(seed, p) != -1:
                raise AssertionError(("valuation", j, p, term_count))
            actual = rational_mod(p * seed, p)
            character = 1 if p % 4 == 1 else -1
            expected = pow(10, j, p) * character * rational_mod(fixed, p) % p
            if actual != expected:
                raise AssertionError(("residue", j, p, actual, expected))
            checked_residues += 1

        # Split the actual reduced numerator at a genuine coprime factor F.
        # The resulting c is checked to be exactly floor(D * {seed}), not a
        # new independent arithmetic coordinate.
        cutoff = max(7, d // 3)
        factor = 5 ** valuation(denominator, 5)
        factor *= 239 ** valuation(denominator, 239)
        for p in primes:
            exponent = valuation(denominator, p)
            if p > cutoff and p not in (5, 239) and exponent:
                factor *= p**exponent
        if denominator % factor:
            raise AssertionError(("factor", j))
        complementary = denominator // factor
        if gcd(factor, complementary) != 1:
            raise AssertionError(("coprime", j))
        remainder = residue % factor
        quotient = (residue - remainder) // factor
        if quotient != (complementary * residue) // denominator:
            raise AssertionError(("rounding", j))
        if Fraction(residue, denominator) != (
            Fraction(quotient, complementary)
            + Fraction(remainder, factor * complementary)
        ):
            raise AssertionError(("split", j))

        # Verify the exact carry recurrence for the first twenty powers of 10.
        current = residue
        for _ in range(20):
            r_now = current % factor
            c_now = (current - r_now) // factor
            digit = (10 * current) // denominator
            carry = (10 * r_now) // factor
            next_residue = (10 * current) % denominator
            r_next = next_residue % factor
            c_next = (next_residue - r_next) // factor
            if r_next != 10 * r_now - factor * carry:
                raise AssertionError(("fine carry", j))
            if c_next != 10 * c_now + carry - complementary * digit:
                raise AssertionError(("coarse carry", j))
            current = next_residue
            quotient_checks += 1

    print("claim_status=experiment")
    print(f"j_range=1..{args.max_j}")
    print(f"general_band_residue_checks={checked_residues}")
    print(f"coefficient_cancellations_skipped={cancelled_coefficients}")
    print(f"quotient_and_carry_checks={quotient_checks}")
    print(f"reduced_denominator_nonnesting_events={len(nesting_failures)}")
    print("first_nonnesting_events=" + repr(nesting_failures[:8]))
    print("all exact checks passed")


if __name__ == "__main__":
    main()
