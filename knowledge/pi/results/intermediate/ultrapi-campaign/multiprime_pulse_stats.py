#!/usr/bin/env python3
"""Deterministic finite audit of simultaneous T45 prime-pulse projections.

This script does not compute digits of pi.  It forms the squarefree product of
all admissible interior primes whose T45/T38 pulse remains active on a chosen
integer interval, reconstructs the resulting additive CRT component exactly,
and measures only that projected finite orbit.

Every output of this script is experiment-level evidence, never a proof of an
asymptotic statement or of decimal-word occurrence in pi.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import asdict, dataclass


def prime_sieve(limit: int) -> list[bool]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        is_prime[0] = 0
    if limit >= 1:
        is_prime[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            start = p * p
            is_prime[start : limit + 1 : p] = b"\x00" * (
                (limit - start) // p + 1
            )
    return [bool(value) for value in is_prime]


def active_primes(j: int, length: int, is_prime: list[bool]) -> list[tuple[int, int, int]]:
    """Return (p, N, k) for pulses active throughout j..j+length-1."""
    if j < 1 or length < 1:
        raise ValueError("j and length must be positive")
    last = j + length - 1
    result: list[tuple[int, int, int]] = []
    for n in range(j):
        for k in (1, 3, 4):
            p = 12 * n + 5 + 2 * k
            expiry = 3 * n + (1 if k == 1 else 2)
            if n + 1 <= j and last <= expiry and p != 239 and is_prime[p]:
                result.append((p, n, k))
    return result


def born_primes(j: int, is_prime: list[bool]) -> list[tuple[int, int, int]]:
    """Return all admissible interior prime pulses born no later than j.

    Unlike :func:`active_primes`, this ignores the next occurrence of a
    multiple of p.  It is useful for testing the weakest possible claim that
    knowing all past T45 residues might constrain an initial seed.
    """
    result: list[tuple[int, int, int]] = []
    for n in range(j):
        for k in (1, 3, 4):
            p = 12 * n + 5 + 2 * k
            if n + 1 <= j and p != 239 and is_prime[p]:
                result.append((p, n, k))
    return result


def crt_projection(j: int, entries: list[tuple[int, int, int]]) -> tuple[int, int]:
    """Return A,P with local additive coefficients b_p=A/(P/p) mod p.

    T45 and pulse propagation give

      b_p = 4 (-1)^k 951 10^j / (5*239)  (mod p).

    Thus A/P is exactly the simultaneous squarefree-prime component at time j.
    """
    product = math.prod(p for p, _, _ in entries)
    numerator = 0
    for p, _, k in entries:
        sign = -1 if k % 2 else 1
        local = (
            sign
            * 4
            * 951
            * pow(10, j, p)
            * pow(5 * 239, -1, p)
        ) % p
        cofactor = product // p
        # A * cofactor^{-1} = local (mod p).
        numerator += local * cofactor
    numerator %= product
    for p, _, k in entries:
        sign = -1 if k % 2 else 1
        expected = (
            sign
            * 4
            * 951
            * pow(10, j, p)
            * pow(5 * 239, -1, p)
        ) % p
        actual = numerator * pow(product // p, -1, p) % p
        if actual != expected:
            raise AssertionError((j, p, expected, actual))
    return numerator, product


@dataclass
class Row:
    j: int
    length: int
    prime_count: int
    class_1_count: int
    class_7_count: int
    class_11_count: int
    log_product: float
    log10_product: float
    log_product_over_j: float
    log_product_asymptotic: float
    all_born_prime_count: int
    all_born_log_product: float
    all_born_log_product_over_j: float
    natural_base_log_scale: float
    natural_common_log_scale: float
    active_fraction_of_natural_log: float
    active_fraction_of_common_log: float
    all_born_fraction_of_natural_log: float
    all_born_fraction_of_common_log: float
    upper_half_complement_count: int
    upper_half_complement_log: float
    upper_half_complement_log_over_j: float
    distinct_decimal_cells_1: int
    distinct_decimal_cells_2: int
    distinct_decimal_cells_3: int
    max_fourier_ratio_20: float
    frequency_at_max: int
    first_frequency_ratio: float


def audit_row(j: int, length: int, is_prime: list[bool]) -> Row:
    entries = active_primes(j, length, is_prime)
    born_entries = born_primes(j, is_prime)
    if not entries:
        raise ValueError(f"no active primes for j={j}, length={length}")
    numerator, product = crt_projection(j, entries)
    log_product = sum(math.log(p) for p, _, _ in entries)
    all_born_log_product = sum(math.log(p) for p, _, _ in born_entries)
    active_values = {p for p, _, _ in entries}
    upper_half_complement = [
        p
        for p in range((12 * j + 3) // 2 + 1, 12 * j + 4)
        if is_prime[p] and p not in (239, 317) and p not in active_values
    ]
    upper_half_complement_log = sum(math.log(p) for p in upper_half_complement)
    natural_base_log_scale = j * (11 * math.log(5) + 12 * math.log(239))
    # The odd-index lcm through 12*j+5 has log asymptotic 12*j by the
    # prime number theorem, so this is the leading log of the natural common
    # denominator after decimal scaling.
    natural_common_log_scale = natural_base_log_scale + 12 * j

    cell_masks = [0, 0, 0]
    sums = [0j] * 20
    residue = numerator
    for _ in range(length):
        for digits, scale in enumerate((10, 100, 1000)):
            cell = (scale * residue) // product
            cell_masks[digits] |= 1 << int(cell)
        phase = float(residue / product)
        for h in range(1, 21):
            sums[h - 1] += cmath.exp(2j * math.pi * h * phase)
        residue = (10 * residue) % product

    ratios = [abs(value) / length for value in sums]
    max_ratio = max(ratios)
    max_h = 1 + ratios.index(max_ratio)
    class_counts = {
        residue_class: sum(1 for p, _, _ in entries if p % 12 == residue_class)
        for residue_class in (1, 7, 11)
    }
    # PNT in arithmetic progressions predicts max(6*j-3*length, 0) for
    # these three residue classes, up to endpoint O(1) changes.
    prediction = max(6 * j - 3 * length, 0)
    return Row(
        j=j,
        length=length,
        prime_count=len(entries),
        class_1_count=class_counts[1],
        class_7_count=class_counts[7],
        class_11_count=class_counts[11],
        log_product=log_product,
        log10_product=log_product / math.log(10),
        log_product_over_j=log_product / j,
        log_product_asymptotic=float(prediction),
        all_born_prime_count=len(born_entries),
        all_born_log_product=all_born_log_product,
        all_born_log_product_over_j=all_born_log_product / j,
        natural_base_log_scale=natural_base_log_scale,
        natural_common_log_scale=natural_common_log_scale,
        active_fraction_of_natural_log=log_product / natural_base_log_scale,
        active_fraction_of_common_log=log_product / natural_common_log_scale,
        all_born_fraction_of_natural_log=all_born_log_product / natural_base_log_scale,
        all_born_fraction_of_common_log=all_born_log_product / natural_common_log_scale,
        upper_half_complement_count=len(upper_half_complement),
        upper_half_complement_log=upper_half_complement_log,
        upper_half_complement_log_over_j=upper_half_complement_log / j,
        distinct_decimal_cells_1=cell_masks[0].bit_count(),
        distinct_decimal_cells_2=cell_masks[1].bit_count(),
        distinct_decimal_cells_3=cell_masks[2].bit_count(),
        max_fourier_ratio_20=max_ratio,
        frequency_at_max=max_h,
        first_frequency_ratio=ratios[0],
    )


def parse_pair(text: str) -> tuple[int, int]:
    first, second = text.split(":", 1)
    return int(first), int(second)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--pair",
        action="append",
        type=parse_pair,
        help="start:length pair; may be repeated",
    )
    args = parser.parse_args()
    pairs = args.pair or [
        (100, 50),
        (200, 100),
        (500, 250),
        (1000, 500),
        (2000, 1000),
        (5000, 2500),
    ]
    max_prime = max(12 * j + 13 for j, _ in pairs)
    is_prime = prime_sieve(max_prime)
    rows = [audit_row(j, length, is_prime) for j, length in pairs]
    print(json.dumps([asdict(row) for row in rows], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
