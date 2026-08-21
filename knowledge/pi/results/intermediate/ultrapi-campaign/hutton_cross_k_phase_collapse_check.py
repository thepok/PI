#!/usr/bin/env python3
"""Exact replay for ``hutton_cross_k_phase_collapse.md``.

All arithmetic assertions use Python integers and ``Fraction``.  Complex
means are printed as finite experiments; they are not asymptotic claims and
are not claims about uncomputed digits of pi.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
getcontext().prec = 90


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
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            count = (bound - prime * prime) // prime + 1
            sieve[prime * prime : bound + 1 : prime] = b"\x00" * count
    return [candidate for candidate in range(2, bound + 1) if sieve[candidate]]


def hutton_term(odd_exponent: int) -> Fraction:
    assert odd_exponent >= 1 and odd_exponent % 2 == 1
    sign = 1 if odd_exponent % 4 == 1 else -1
    return Fraction(
        4 * sign * (2 * 7**odd_exponent + 3**odd_exponent),
        odd_exponent * 3**odd_exponent * 7**odd_exponent,
    )


def hutton_lower(index: int) -> Fraction:
    radius = 4 * index + 3
    return sum(
        (hutton_term(exponent) for exponent in range(1, radius + 1, 2)),
        Fraction(),
    )


def hutton_width(index: int) -> Fraction:
    next_odd = 4 * index + 5
    return Fraction(8, next_odd * 3**next_odd) + Fraction(
        4, next_odd * 7**next_odd
    )


def transient_band(exponent: int) -> tuple[int, int]:
    assert exponent >= 0
    return (5**exponent - 1) // 4, (5 ** (exponent + 1) - 5) // 4


def band_values(exponent: int) -> dict[int, Fraction]:
    first, last = transient_band(exponent)
    value = hutton_lower(first)
    result = {first: value}
    for index in range(first, last):
        radius = 4 * index + 3
        value += hutton_term(radius + 2) + hutton_term(radius + 4)
        result[index + 1] = value
    return result


def fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def unit_phase(value: Fraction) -> complex:
    value = fractional_part(value)
    angle = 2 * math.pi * float(
        Decimal(value.numerator) / Decimal(value.denominator)
    )
    return cmath.exp(1j * angle)


def selected_crt_data(
    index: int, exponent: int, value: Fraction, primes: list[int]
) -> tuple[int, int, int, int, int]:
    radius = 4 * index + 3
    selected = [
        prime
        for prime in primes
        if radius < 2 * prime
        and prime <= radius
        and prime > 7
        and prime != 17
    ]
    product = math.prod(selected)
    assert product > 1
    numerator, denominator = value.numerator, value.denominator
    assert valuation(denominator, 5) == exponent
    assert denominator % product == 0

    modulus = denominator // 5**exponent
    assert modulus % product == 0
    complement = modulus // product
    assert math.gcd(product, complement) == 1
    state = pow(2, exponent, modulus) * numerator % modulus

    # Recheck the T61 local selected-prime coordinate directly.
    for prime in selected:
        local = value * prime
        assert local.denominator % prime != 0
        residue = local.numerator * pow(local.denominator, -1, prime) % prime
        sign = 1 if prime % 4 == 1 else -1
        expected = sign * 68 * pow(21, -1, prime) % prime
        assert residue == expected

    alpha = state * pow(complement, -1, product) % product
    beta = state * pow(product, -1, complement) % complement
    assert Fraction(state, modulus) == fractional_part(
        Fraction(alpha, product) + Fraction(beta, complement)
    )
    return product, complement, state, alpha, beta


def log10_chord_bound(exponent: int, offset: int) -> float:
    first, _ = transient_band(exponent)
    q = 4 * first + 5
    width = hutton_width(first)
    return (
        math.log10(2 * math.pi)
        + exponent
        + offset
        + math.log10(width.numerator)
        - math.log10(width.denominator)
    )


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    cluster_assertions = 0
    exact_crt_assertions = 0
    rows: list[tuple[int, int, int, float, float, float, float]] = []

    # Exact block endpoints, cardinality, five-adic shift, monotone nesting,
    # and the common earliest-bracket diameter.
    all_values: dict[int, dict[int, Fraction]] = {}
    for exponent in range(0, 4):
        first, last = transient_band(exponent)
        assert 4 * first + 3 == 5**exponent + 2
        assert 4 * last + 3 == 5 ** (exponent + 1) - 2
        assert last - first + 1 == 5**exponent
        values = band_values(exponent)
        all_values[exponent] = values
        width = hutton_width(first)
        initial = values[first]
        previous = initial
        for index, value in values.items():
            assert previous <= value
            assert 0 <= value - initial < width
            assert valuation(value.denominator, 5) == exponent
            assert value.denominator % 2 == 1
            previous = value
            cluster_assertions += 4

    # Exact changing-modulus additive CRT, followed by the finite complex
    # experiment which displays selected/complementary phase cancellation.
    for exponent in (2, 3):
        first, last = transient_band(exponent)
        primes = primes_through(4 * last + 3)
        data = {
            index: selected_crt_data(index, exponent, value, primes)
            for index, value in all_values[exponent].items()
        }
        exact_crt_assertions += sum(
            len(
                [
                    prime
                    for prime in primes
                    if 4 * index + 3 < 2 * prime <= 2 * (4 * index + 3)
                    and prime > 7
                    and prime != 17
                ]
            )
            + 3
            for index in data
        )

        for offset in (0, int(0.35 * 5**exponent)):
            selected_sum = 0j
            complement_sum = 0j
            full_sum = 0j
            reference = unit_phase(10 ** (exponent + offset) * all_values[exponent][first])
            width = hutton_width(first)
            chord_bound = 2 * math.pi * float(
                Decimal(10 ** (exponent + offset) * width.numerator)
                / Decimal(width.denominator)
            )

            for index, value in all_values[exponent].items():
                product, complement, state, alpha, beta = data[index]
                power_product = pow(10, offset, product)
                power_complement = pow(10, offset, complement)
                power_modulus = pow(10, offset, product * complement)

                selected_fraction = Fraction(
                    alpha * power_product % product, product
                )
                complement_fraction = Fraction(
                    beta * power_complement % complement, complement
                )
                full_fraction = Fraction(
                    state * power_modulus % (product * complement),
                    product * complement,
                )
                assert full_fraction == fractional_part(
                    selected_fraction + complement_fraction
                )
                assert full_fraction == fractional_part(
                    10 ** (exponent + offset) * value
                )
                exact_crt_assertions += 2

                selected_phase = unit_phase(selected_fraction)
                complement_phase = unit_phase(complement_fraction)
                full_phase = selected_phase * complement_phase
                selected_sum += selected_phase
                complement_sum += complement_phase
                full_sum += full_phase

                # Numerical replay of the theorem's pointwise conjugacy.
                assert abs(full_phase - reference) <= chord_bound + 2e-12
                assert abs(
                    complement_phase
                    - reference * selected_phase.conjugate()
                ) <= chord_bound + 2e-12

            count = 5**exponent
            rows.append(
                (
                    exponent,
                    offset,
                    count,
                    abs(selected_sum / count),
                    abs(complement_sum / count),
                    abs(full_sum / count),
                    log10_chord_bound(exponent, offset),
                )
            )

    print(f"source sha256: {SOURCE_SHA256}")
    print(
        "exact band/transient/diameter/odd-denominator assertions: "
        f"{cluster_assertions}"
    )
    print(f"exact selected-prime/additive-CRT assertions: {exact_crt_assertions}")
    print("finite phase experiment: b s #K |mean G| |mean B| |mean product| log10(epsilon)")
    for row in rows:
        print(
            f"  {row[0]:1d} {row[1]:2d} {row[2]:3d} "
            f"{row[3]:.12f} {row[4]:.12f} {row[5]:.12f} {row[6]:+.6f}"
        )
    print("all exact checks passed; complex means are experiments only")


if __name__ == "__main__":
    main()
