#!/usr/bin/env python3
"""Exact finite P19 ray-zero and quadratic-unit-order profiles.

All output is finite experimental data.  Primality, ray endpoints, recurrence
zeros, and orders in Z[sqrt(2)]/p are computed with exact integers.
"""

from collections import defaultdict
import json


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def primes_between(lower: int, upper: int) -> list[int]:
    sieve = bytearray(b"\x01") * (upper + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= upper:
        if sieve[p]:
            sieve[p * p:upper + 1:p] = b"\x00" * (
                (upper - p * p) // p + 1
            )
        p += 1
    return [p for p in range(max(3, lower + 1), upper)
            if p % 2 and sieve[p]]


def ray_ranges(x: int, p: int) -> tuple[tuple[int, int], tuple[int, int]]:
    """Exact delta=1/12 direct/reflected inclusive r ranges."""
    direct = (
        max(x - p + 1, ceil_div(p, 11), 1),
        min(2 * x - p, p // 3, (p - 1) // 2),
    )
    reflected = (
        max(2 * p - 1 - 2 * x, ceil_div(2 * p - 1, 13), 1),
        min(2 * p - x - 2, (2 * p - 1) // 5, (p - 2) // 2),
    )
    return direct, reflected


def coefficients_mod_p(p: int, maximum: int) -> list[int]:
    """A_0,...,A_maximum via the exact P19 recurrence modulo p."""
    assert maximum < p
    values = [0] * (maximum + 1)
    values[0] = 1
    if maximum == 0:
        return values
    values[1] = 2
    inverses = [0] * (maximum + 1)
    inverses[1] = 1
    for denominator in range(2, maximum + 1):
        inverses[denominator] = (
            p - (p // denominator) * inverses[p % denominator] % p
        )
    for r in range(1, maximum):
        values[r + 1] = (
            (2 * (2 * r + 1) * values[r] + 4 * r * values[r - 1])
            * inverses[r + 1]
        ) % p
    return values


def prime_factors(n: int) -> list[int]:
    factors = []
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            factors.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if n > 1:
        factors.append(n)
    return factors


def quadratic_multiply(
    left: tuple[int, int], right: tuple[int, int], p: int
) -> tuple[int, int]:
    """Multiply a+b*sqrt(2) in Z[sqrt(2)]/p."""
    a, b = left
    c, d = right
    return ((a * c + 2 * b * d) % p, (a * d + b * c) % p)


def quadratic_power(
    value: tuple[int, int], exponent: int, p: int
) -> tuple[int, int]:
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = quadratic_multiply(result, value, p)
        value = quadratic_multiply(value, value, p)
        exponent //= 2
    return result


def rho_order(p: int) -> int:
    """Order of rho=-3+2*sqrt(2), in the split or inert residue algebra."""
    legendre_two = pow(2, (p - 1) // 2, p)
    group_bound = p - 1 if legendre_two == 1 else p + 1
    rho = (-3 % p, 2 % p)
    assert quadratic_power(rho, group_bound, p) == (1, 0)
    order = group_bound
    for factor in prime_factors(group_bound):
        while (order % factor == 0
               and quadratic_power(rho, order // factor, p) == (1, 0)):
            order //= factor
    return order


EXPECTED = {
    2048: (392, 71, 99, 165, 4),
    4096: (719, 126, 178, 308, 4),
    8192: (1336, 242, 339, 581, 4),
    16384: (2484, 422, 576, 948, 4),
    32768: (4642, 837, 1165, 1999, 6),
}

EXPECTED_MOD8 = {
    2048: {1: (95, 20, 29, 55, 4), 3: (101, 21, 28, 44, 3),
           5: (98, 8, 10, 14, 2), 7: (98, 22, 32, 52, 2)},
    4096: {1: (179, 38, 59, 115, 4), 3: (179, 30, 41, 69, 4),
           5: (181, 27, 33, 45, 2), 7: (180, 31, 45, 79, 4)},
    8192: {1: (331, 54, 70, 116, 4), 3: (331, 63, 92, 164, 4),
           5: (334, 63, 91, 163, 4), 7: (340, 62, 86, 138, 3)},
    16384: {1: (614, 106, 148, 256, 4), 3: (630, 109, 133, 181, 2),
            5: (623, 104, 142, 236, 4), 7: (617, 103, 153, 275, 4)},
    32768: {1: (1150, 216, 296, 486, 4), 3: (1158, 192, 251, 393, 4),
            5: (1166, 214, 300, 518, 5), 7: (1168, 215, 318, 602, 6)},
}

bands = []
for x in EXPECTED:
    profiles = []
    strata = defaultdict(lambda: [0, 0, 0, 0, 0])
    for p in primes_between(x // 2, 2 * x):
        direct, reflected = ray_ranges(x, p)
        maximum = max(direct[1], reflected[1], 1)
        values = coefficients_mod_p(p, maximum)
        z_direct = (sum(values[r] == 0
                        for r in range(direct[0], direct[1] + 1))
                    if direct[0] <= direct[1] else 0)
        z_reflected = (sum(values[r] == 0
                           for r in range(reflected[0], reflected[1] + 1))
                       if reflected[0] <= reflected[1] else 0)
        z = z_direct + z_reflected
        order = rho_order(p)
        profiles.append({
            "p": p,
            "p_mod_8": p % 8,
            "rho_order": order,
            "direct_range": list(direct),
            "reflected_range": list(reflected),
            "Z_direct": z_direct,
            "Z_reflected": z_reflected,
            "Z": z,
        })
        row = strata[p % 8]
        row[0] += 1
        row[1] += z > 0
        row[2] += z
        row[3] += z * z
        row[4] = max(row[4], z)

    summary = (
        len(profiles),
        sum(row["Z"] > 0 for row in profiles),
        sum(row["Z"] for row in profiles),
        sum(row["Z"] ** 2 for row in profiles),
        max(row["Z"] for row in profiles),
    )
    assert summary == EXPECTED[x]
    observed_strata = {key: tuple(strata[key]) for key in (1, 3, 5, 7)}
    assert observed_strata == EXPECTED_MOD8[x]
    bands.append({
        "X": x,
        "summary_P_NZ_sumZ_sumZ2_maxZ": list(summary),
        "mod8_P_NZ_sumZ_sumZ2_maxZ": {
            str(key): list(observed_strata[key]) for key in (1, 3, 5, 7)
        },
        "profiles": profiles,
    })

print(json.dumps({
    "status": "experiment",
    "delta": {"numerator": 1, "denominator": 12},
    "rho": "-3+2*sqrt(2)",
    "bands": bands,
}, sort_keys=True, separators=(",", ":")))
