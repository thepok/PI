#!/usr/bin/env python3
"""Exact checks for the fixed-modulus Machin-seed audit.

Claim status of every output: experiment.  Python's Fraction supplies exact
integer/rational arithmetic; no digits or floating-point value of pi are used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, int(limit**0.5) + 1):
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
    return valuation(abs(value.numerator), prime) - valuation(value.denominator, prime)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=300,
                        help="largest forcing index N (starts at N=1)")
    args = parser.parse_args()
    if args.max_n < 1:
        raise SystemExit("--max-n must be positive")

    max_endpoint = 12 * (args.max_n + 1) + 5
    primes = primes_up_to(max_endpoint)
    prime_set = set(primes)

    sum5 = Fraction()
    sum239 = Fraction()
    next5 = 0
    next239 = 0
    failures: list[str] = []
    margins: list[tuple[int, int, int, int]] = []

    for n in range(1, args.max_n + 2):
        while next5 < 6 * n + 2:
            j = next5
            sum5 += Fraction(-1 if j & 1 else 1,
                             (2 * j + 1) * 5 ** (2 * j + 1))
            next5 += 1
        while next239 < 6 * n + 3:
            j = next239
            sum239 += Fraction(-1 if j & 1 else 1,
                               (2 * j + 1) * 239 ** (2 * j + 1))
            next239 += 1

        n_forcing = n - 1
        if n_forcing < 1:
            continue

        seed = 10**n * (16 * sum5 - 4 * sum239)
        numerator = seed.numerator
        denominator = seed.denominator
        d5 = 12 * n + 3
        d239 = d5 + 2
        m5 = 6 * n + 1
        m239 = m5 + 1

        reverse5 = (-1) ** m5 * d5 * 5**d5 * sum5
        reverse239 = (-1) ** m239 * d239 * 239**d239 * sum239
        expected5 = d5 + valuation(d5, 5) - n - rational_valuation(reverse5, 5)
        expected239 = (
            d239 + valuation(d239, 239) - rational_valuation(reverse239, 239)
        )
        actual5 = valuation(denominator, 5)
        actual239 = valuation(denominator, 239)
        if actual5 != expected5:
            failures.append(f"N={n_forcing}: v5 {actual5} != {expected5}")
        if actual239 != expected239:
            failures.append(f"N={n_forcing}: v239 {actual239} != {expected239}")

        fresh = [
            12 * n_forcing + 5 + 2 * k
            for k in (1, 3, 4)
            if 12 * n_forcing + 5 + 2 * k in prime_set
            and 12 * n_forcing + 5 + 2 * k != 239
        ]
        controlled = 5**actual5 * 239**actual239
        for prime in fresh:
            if valuation(denominator, prime) != 1:
                failures.append(
                    f"N={n_forcing}: fresh prime {prime} does not have exponent one"
                )
            controlled *= prime
        if denominator % controlled:
            failures.append(f"N={n_forcing}: controlled factor does not divide Q")
            continue

        cofactor = denominator // controlled
        if gcd(controlled, cofactor) != 1:
            failures.append(f"N={n_forcing}: controlled factor and cofactor overlap")

        for prime in primes:
            if 2 * prime <= d5 or prime > d5 or prime in (239, 317):
                continue
            if valuation(denominator, prime) != 1:
                failures.append(
                    f"N={n_forcing}: upper-half prime {prime} does not survive once"
                )

        omega_cofactor = sum(cofactor % prime == 0 for prime in primes)
        pulse_length = 2 * n_forcing + 2
        jacobsthal_upper = 2**omega_cofactor
        separator_holds = cofactor > jacobsthal_upper * 10**pulse_length
        if not separator_holds:
            failures.append(
                f"N={n_forcing}: D <= 2^omega(D) 10^L"
            )
        margins.append(
            (n_forcing, cofactor.bit_length(), omega_cofactor, pulse_length)
        )

        if gcd(numerator, denominator) != 1:
            failures.append(f"N={n_forcing}: Fraction was not reduced")

    print(f"rows={len(margins)}")
    print(f"failures={len(failures)}")
    if failures:
        for failure in failures[:20]:
            print(failure)
        raise SystemExit(1)
    first = margins[0]
    last = margins[-1]
    print(
        "first="
        f"N={first[0]}, D_bits={first[1]}, omega(D)={first[2]}, L={first[3]}"
    )
    print(
        "last="
        f"N={last[0]}, D_bits={last[1]}, omega(D)={last[2]}, L={last[3]}"
    )
    print("all exact component, upper-half-prime, and separator checks passed")


if __name__ == "__main__":
    main()
