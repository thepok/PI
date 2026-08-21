#!/usr/bin/env python3
"""Exact finite replay for ``hutton_prefix_sum_attack.md``.

All assertions use integers or ``fractions.Fraction``.  The cylinder counts
are finite experiments about rational Hutton truncations; they are not a
proof of any assertion about all decimal words in pi.
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
    assert value > 0 and prime > 1
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def primes_through(bound: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, bound + 1):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    return primes


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


def hutton_width(index: int) -> Fraction:
    next_odd = 4 * index + 5
    return Fraction(8, next_odd * 3**next_odd) + Fraction(
        4, next_odd * 7**next_odd
    )


def safe_last_position(index: int, length: int) -> int:
    """Largest j with 10^j W_K < 1/(2*10^length), or -1."""
    assert length >= 0
    width = hutton_width(index)
    threshold = Fraction(1, 2 * 10**length)
    position = -1
    power = 1
    while power * width < threshold:
        position += 1
        power *= 10
    assert position < 0 or 10**position * width < threshold
    assert 10 ** (position + 1) * width >= threshold
    return position


def post_transient_state(value: Fraction) -> tuple[int, int, int]:
    """Return (b,m,a) with {10^b value}=a/m and gcd(m,10)=1."""
    denominator = value.denominator
    transient = valuation(denominator, 5)
    modulus = denominator // 5**transient
    state = (pow(2, transient, modulus) * (value.numerator % modulus)) % modulus
    assert math.gcd(modulus, 10) == 1
    assert math.gcd(state, modulus) == 1
    scaled = value * 10**transient
    assert Fraction(scaled.numerator % scaled.denominator, scaled.denominator) == Fraction(
        state, modulus
    )
    return transient, modulus, state


def upper_half_primes(index: int) -> list[int]:
    radius = 4 * index + 3
    return [
        prime
        for prime in primes_through(radius)
        if 2 * prime > radius and prime not in {2, 3, 5, 7, 17}
    ]


def lower_half_cylinder_counts(index: int, lengths: tuple[int, ...]) -> list[tuple[int, int]]:
    """Return (number of starts, distinct lower-half cylinders) for each length."""
    value = hutton_lower(index)
    transient, modulus, state = post_transient_state(value)
    answer: list[tuple[int, int]] = []
    for length in lengths:
        last = safe_last_position(index, length)
        number = max(0, last - transient + 1)
        residue = state
        seen: set[int] = set()
        scale = 10**length
        for _ in range(number):
            code = scale * residue // modulus
            # {10^j H_K} is in the first half of the code's cylinder.
            if 2 * (scale * residue - code * modulus) < modulus:
                seen.add(code)
            residue = 10 * residue % modulus
        answer.append((number, len(seen)))
    return answer


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    prime_survival_checks = 0
    local_residue_checks = 0
    state_checks = 0
    pair_checks = 0

    for index in range(0, 201):
        value = hutton_lower(index)
        radius = 4 * index + 3
        transient, modulus, state = post_transient_state(value)

        # The exact decimal state identity, checked throughout the safe prefix.
        last = safe_last_position(index, 3)
        residue = state
        for offset in range(max(0, last - transient + 1)):
            scaled = value * 10 ** (transient + offset)
            fractional = Fraction(
                scaled.numerator % scaled.denominator, scaled.denominator
            )
            assert fractional == Fraction(residue, modulus)
            residue = 10 * residue % modulus
            state_checks += 1

        # Every upper-half prime except 17 survives exactly once.  Its local
        # p-primary residue is the fixed value +/-68/21.
        for prime in upper_half_primes(index):
            assert valuation(value.denominator, prime) == 1
            assert modulus % prime == 0
            local = value * prime
            assert local.denominator % prime
            residue_mod_prime = (
                local.numerator * pow(local.denominator, -1, prime)
            ) % prime
            sign = -1 if ((prime - 1) // 2) % 2 else 1
            expected = sign * 68 * pow(21, -1, prime) % prime
            assert residue_mod_prime == expected
            prime_survival_checks += 2
            local_residue_checks += 1

        # The exceptional upper-half prime 17 cancels from the denominator.
        if 2 * 17 > radius and 17 <= radius:
            assert valuation(value.denominator, 17) == 0
            prime_survival_checks += 1

        if index:
            pair_radius = 4 * index + 3
            exponent = (
                pair_radius
                + valuation(pair_radius, 3)
                + valuation(pair_radius - 2, 3)
                - valuation(4 * pair_radius + 1, 3)
            )
            previous = hutton_lower(index - 1)
            assert max(
                valuation(previous.denominator, 3),
                valuation(value.denominator, 3),
            ) >= exponent
            pair_checks += 1

    lifting_checks = 0
    for shift in range(1, 5001):
        assert valuation(10**shift - 1, 3) == 2 + valuation(shift, 3)
        if shift % 6:
            assert (10**shift - 1) % 7
        else:
            assert valuation(10**shift - 1, 7) == 1 + valuation(shift // 6, 7)
        lifting_checks += 2

    # Exact finite certificates for the uniform-coefficient obstruction.  If
    # 100*10^N < m, then sum_{s<N} 10^s/m < 1/900, so the phases for a=1
    # are all aligned up to a total chordal error below 2*pi/900.
    alignment_rows: list[tuple[int, int, int, int]] = []
    for pair_index in (10, 20, 40, 80, 120, 200):
        candidates = []
        for index in (pair_index - 1, pair_index):
            value = hutton_lower(index)
            transient, modulus, _ = post_transient_state(value)
            exponent = valuation(value.denominator, 3)
            number = max(0, safe_last_position(index, 2) - transient + 1)
            candidates.append((exponent, index, number, modulus))
        _, index, number, modulus = max(candidates)
        assert 100 * 10**number < modulus
        assert Fraction(10**number - 1, 9 * modulus) < Fraction(1, 900)
        alignment_rows.append((pair_index, index, number, len(str(modulus)) - 1))

    coverage_rows = []
    for index in (20, 40, 80, 120, 200, 300, 400, 600):
        coverage_rows.append((index, lower_half_cylinder_counts(index, (1, 2, 3))))

    print(f"source sha256: {SOURCE_SHA256}")
    print(f"upper-half prime survival assertions: {prime_survival_checks}")
    print(f"fixed local-residue assertions: {local_residue_checks}")
    print(f"post-transient state assertions: {state_checks}")
    print(f"neighboring 3-primary assertions: {pair_checks}")
    print(f"LTE assertions: {lifting_checks}")
    print("uniform-a alignment rows (pair K, selected J, N, floor(log10 m_J)):")
    for row in alignment_rows:
        print("  " + " ".join(map(str, row)))
    print("lower-half cylinder experiment (K: ell -> starts/hits):")
    for index, counts in coverage_rows:
        rendered = " ".join(
            f"{length}->{number}/{hits}"
            for length, (number, hits) in zip((1, 2, 3), counts)
        )
        print(f"  {index}: {rendered}")
    print("all exact checks passed")


if __name__ == "__main__":
    main()
