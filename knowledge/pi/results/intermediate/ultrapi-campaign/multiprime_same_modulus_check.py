#!/usr/bin/env python3
"""Exact finite check of the all-active, same-Q CRT separator.

Every result is labelled ``experiment``.  The script uses rational arithmetic
only and never evaluates pi or reads a pi digit table.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd

from multiprime_pulse_stats import active_primes, prime_sieve


def valuation(value: int, prime: int) -> int:
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-j", type=int, default=100)
    parser.add_argument("--min-j", type=int, default=2)
    args = parser.parse_args()
    if args.min_j < 1 or args.max_j < args.min_j:
        raise SystemExit("require 1 <= min-j <= max-j")

    limit = 12 * args.max_j + 20
    is_prime = prime_sieve(limit)
    primes = [p for p in range(2, limit + 1) if is_prime[p]]

    sum5 = Fraction()
    sum239 = Fraction()
    next5 = 0
    next239 = 0
    failures: list[str] = []
    checks = 0
    final_rows: list[tuple[int, int, int, bool]] = []

    for j in range(1, args.max_j + 1):
        while next5 < 6 * j + 2:
            index = next5
            sum5 += Fraction(
                -1 if index & 1 else 1,
                (2 * index + 1) * 5 ** (2 * index + 1),
            )
            next5 += 1
        while next239 < 6 * j + 3:
            index = next239
            sum239 += Fraction(
                -1 if index & 1 else 1,
                (2 * index + 1) * 239 ** (2 * index + 1),
            )
            next239 += 1

        if j < args.min_j:
            continue
        seed = 10**j * (16 * sum5 - 4 * sum239)
        denominator = seed.denominator
        d = 12 * j + 3

        for prime in primes:
            if 2 * prime <= d or prime > d or prime in (239, 317):
                continue
            if valuation(denominator, prime) != 1:
                failures.append(
                    f"j={j}: upper-half prime {prime} does not survive once"
                )

        for length in sorted({1, max(1, j // 2), j, 2 * j}):
            entries = active_primes(j, length, is_prime)
            controlled = (
                5 ** valuation(denominator, 5)
                * 239 ** valuation(denominator, 239)
            )
            for prime, _, _ in entries:
                exponent = valuation(denominator, prime)
                if exponent != 1:
                    failures.append(
                        f"j={j}, L={length}: active prime {prime} exponent {exponent}"
                    )
                controlled *= prime

            if denominator % controlled:
                failures.append(f"j={j}, L={length}: F does not divide Q")
                continue
            cofactor = denominator // controlled
            if gcd(controlled, cofactor) != 1:
                failures.append(f"j={j}, L={length}: gcd(F,D) != 1")
            omega = sum(cofactor % prime == 0 for prime in primes)
            separator = cofactor > 2**omega * 10**length
            if not separator:
                failures.append(
                    f"j={j}, L={length}: D <= 2^omega(D) * 10^L"
                )
            if j == args.max_j:
                final_rows.append(
                    (length, cofactor.bit_length(), omega, separator)
                )
            checks += 1

    print("claim_status=experiment")
    print(f"j_range={args.min_j}..{args.max_j}")
    print(f"block_checks={checks}")
    print(f"failures={len(failures)}")
    for failure in failures[:20]:
        print(failure)
    for length, bits, omega, separator in final_rows:
        print(
            f"last j={args.max_j}, L={length}, D_bits={bits}, "
            f"omega_D={omega}, separator={str(separator).lower()}"
        )
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
