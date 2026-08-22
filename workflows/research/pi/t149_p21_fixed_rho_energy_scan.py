#!/usr/bin/env python3
"""Exact finite falsification scan for the frozen P21 energy inequality."""

from __future__ import annotations

import json
from math import isqrt


LOWER_EXCLUSIVE = 503
UPPER_EXCLUSIVE = 65536


def primes_below(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * limit
    sieve[:2] = b"\x00\x00"
    for q in range(2, isqrt(limit - 1) + 1):
        if sieve[q]:
            sieve[q * q:limit:q] = b"\x00" * (((limit - 1 - q * q) // q) + 1)
    return [p for p in range(LOWER_EXCLUSIVE + 1, limit) if p % 2 and sieve[p]]


def cube_root_floor(p: int) -> int:
    value = 0
    while (value + 1) ** 3 <= p:
        value += 1
    return value


def short_convolution_nonzero(p: int, depth: int) -> bool:
    """Check b_0,...,b_(depth-1), where 1/(1-4T-4T^2)=sum b_n T^n."""
    if depth <= 0:
        return True
    previous, current = 1 % p, 4 % p
    if previous == 0 or (depth >= 2 and current == 0):
        return False
    for _ in range(2, depth):
        previous, current = current, (4 * current + 4 * previous) % p
        if current == 0:
            return False
    return True


def gauss_coefficients(p: int, maximum: int) -> list[int]:
    """Compute a_j=[z^j](z^2+2z+2)^j modulo p through maximum<p."""
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
    for j in range(1, maximum):
        values[j + 1] = (
            (2 * (2 * j + 1) * values[j] + 4 * j * values[j - 1])
            * inverses[j + 1]
        ) % p
    return values


def repeated_difference_excess(indices: list[int]) -> int:
    counts: dict[int, int] = {}
    for position, left in enumerate(indices):
        for right in indices[position + 1:]:
            difference = right - left
            counts[difference] = counts.get(difference, 0) + 1
    return sum(count - 1 for count in counts.values())


def main() -> None:
    checked = 0
    hypothesis_false: list[int] = []
    violations: list[dict[str, object]] = []
    positive_excess: list[dict[str, object]] = []
    maximum_zero_count = -1
    maximum_zero_profiles: list[dict[str, object]] = []
    zero_count_distribution: dict[int, int] = {}

    for p in primes_below(UPPER_EXCLUSIVE):
        checked += 1
        depth = cube_root_floor(p)
        if not short_convolution_nonzero(p, depth):
            hypothesis_false.append(p)
            continue
        lower = (p + 10) // 11
        upper = 2 * p // 5
        values = gauss_coefficients(p, upper)
        zeros = [j for j in range(lower, upper + 1) if values[j] == 0]
        excess = repeated_difference_excess(zeros)
        zero_count_distribution[len(zeros)] = zero_count_distribution.get(len(zeros), 0) + 1
        profile = {"p": p, "E": excess, "zeros": zeros}
        if len(zeros) > maximum_zero_count:
            maximum_zero_count = len(zeros)
            maximum_zero_profiles = [profile]
        elif len(zeros) == maximum_zero_count:
            maximum_zero_profiles.append(profile)
        if excess:
            positive_excess.append(profile)
        if excess**4 > p**3:
            violations.append(profile)

    result = {
        "status": "experiment",
        "prime_range": [LOWER_EXCLUSIVE, UPPER_EXCLUSIVE],
        "checked_primes": checked,
        "short_convolution_hypothesis_false": hypothesis_false,
        "violations_of_E4_le_p3": violations,
        "positive_excess_profiles": positive_excess,
        "zero_count_distribution": dict(sorted(zero_count_distribution.items())),
        "maximum_zero_count": maximum_zero_count,
        "maximum_zero_profiles": maximum_zero_profiles,
    }
    assert checked == 6446
    assert hypothesis_false == [5741, 8297, 29201, 33461, 45697]
    assert not violations
    assert not positive_excess
    assert zero_count_distribution == {0: 4690, 1: 1475, 2: 251, 3: 21, 4: 4}
    assert maximum_zero_count == 4
    assert maximum_zero_profiles == [
        {"p": 5683, "E": 0, "zeros": [2134, 2158, 2178, 2249]},
        {"p": 37273, "E": 0, "zeros": [4453, 7230, 12504, 13601]},
        {"p": 49727, "E": 0, "zeros": [9897, 14332, 15724, 19138]},
        {"p": 57713, "E": 0, "zeros": [8324, 14428, 18400, 19237]},
    ]
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
