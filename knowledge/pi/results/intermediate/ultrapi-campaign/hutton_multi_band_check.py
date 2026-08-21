#!/usr/bin/env python3
"""Exact replay for ``hutton_multi_band_attack.md``.

The congruence and denominator assertions use only integer arithmetic and
``fractions.Fraction``.  The final radical ratios are finite experiments;
they are not used as a substitute for the prime number theorem in the note.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def primes_through(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    if bound >= 0:
        sieve[0] = 0
    if bound >= 1:
        sieve[1] = 0
    for p in range(2, math.isqrt(bound) + 1):
        if sieve[p]:
            sieve[p * p : bound + 1 : p] = b"\x00" * (
                (bound - p * p) // p + 1
            )
    return [p for p in range(2, bound + 1) if sieve[p]]


def is_prime(candidate: int) -> bool:
    if candidate < 2:
        return False
    return all(candidate % p for p in primes_through(math.isqrt(candidate)))


def chi4(odd: int) -> int:
    assert odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def hutton_term(index: int) -> Fraction:
    exponent = 2 * index + 1
    return chi4(exponent) * (
        Fraction(8, exponent * 3**exponent)
        + Fraction(4, exponent * 7**exponent)
    )


def hutton_prefix(number_of_terms: int) -> Fraction:
    return sum((hutton_term(j) for j in range(number_of_terms)), Fraction())


def rat_mod(value: Fraction, prime: int) -> int:
    assert value.denominator % prime
    return value.numerator * pow(value.denominator, -1, prime) % prime


def valuation(value: int, prime: int) -> int:
    assert value > 0
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def lcm(values: list[int]) -> int:
    answer = 1
    for value in values:
        answer = math.lcm(answer, value)
    return answer


def singular_residue(radius: int, prime: int) -> int:
    """Residue of ``p H_K`` obtained only from p-singular exponents."""
    answer = 0
    for multiplier in range(1, radius // prime + 1, 2):
        exponent = multiplier * prime
        answer += chi4(exponent) * pow(multiplier, -1, prime) * (
            8 * pow(pow(3, exponent, prime), -1, prime)
            + 4 * pow(pow(7, exponent, prime), -1, prime)
        )
    return answer % prime


def factor_over_primes(value: int, primes: list[int]) -> tuple[dict[int, int], int]:
    factors: dict[int, int] = {}
    remainder = value
    for prime in primes:
        exponent = valuation(remainder, prime)
        if exponent:
            factors[prime] = exponent
            remainder //= prime**exponent
    return factors, remainder


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    maximum_index = 400
    maximum_radius = 4 * maximum_index + 3
    primes = primes_through(maximum_radius)

    # A_n is the n-term Hutton prefix.  Precomputing it also gives every H_K
    # in the finite scan, since H_K=A_{2K+2}.
    prefixes = [Fraction()]
    for index in range(2 * maximum_index + 2):
        prefixes.append(prefixes[-1] + hutton_term(index))

    a1 = prefixes[1]
    a2 = prefixes[2]
    assert a1 == Fraction(68, 21)
    assert a2 == Fraction(87112, 27783)
    assert 87112 == 2**3 * 10889
    assert 27783 == 3**4 * 7**3
    assert is_prime(10889)

    local_checks = 0
    valuation_checks = 0
    one_fifth_checks = 0
    observed_cancellations: set[tuple[int, int]] = set()

    for k_index in range(maximum_index + 1):
        radius = 4 * k_index + 3
        hutton = prefixes[2 * k_index + 2]
        for prime in primes:
            if prime > radius:
                break
            if prime <= 7 or radius >= prime * prime:
                continue

            quotient = radius // prime
            prefix_index = (quotient + 1) // 2
            prefix = prefixes[prefix_index]

            # Exact finite instance of
            # p H_K = chi_4(p) A_n (mod p).
            scaled = prime * hutton
            assert scaled.denominator % prime
            expected = chi4(prime) * rat_mod(prefix, prime) % prime
            assert rat_mod(scaled, prime) == expected
            assert singular_residue(radius, prime) == expected
            local_checks += 2

            # Since R<p^2, every summand has valuation at least -1.  The
            # local residue is therefore nonzero exactly when p occurs once
            # in the reduced denominator.
            denominator_exponent = valuation(hutton.denominator, prime)
            expected_exponent = 0 if prefix.numerator % prime == 0 else 1
            assert denominator_exponent == expected_exponent
            valuation_checks += 1
            if expected_exponent == 0:
                observed_cancellations.add((prefix_index, prime))

            if 3 * prime <= radius < 5 * prime:
                assert prefix_index == 2
                assert denominator_exponent == (0 if prime == 10889 else 1)
                one_fifth_checks += 1

    # The exceptional prime in the one-fifth band is much larger than the
    # generic scan.  R=3p is an admissible radius when p=10889.
    exceptional_prime = 10889
    exceptional_radius = 3 * exceptional_prime
    assert exceptional_radius % 4 == 3
    exceptional_k = (exceptional_radius - 3) // 4
    assert 3 * exceptional_prime <= exceptional_radius < 5 * exceptional_prime
    assert exceptional_radius < exceptional_prime**2
    exceptional_prefix_index = (
        exceptional_radius // exceptional_prime + 1
    ) // 2
    assert exceptional_prefix_index == 2
    assert a2.numerator % exceptional_prime == 0
    assert singular_residue(exceptional_radius, exceptional_prime) == 0

    # First iterated bands.  These factorizations are exact divisions plus a
    # deterministic trial-division primality check on every displayed factor.
    expected_prefix_factors = {
        1: {2: 2, 17: 1},
        2: {2: 3, 10889: 1},
        3: {2: 2, 13: 1, 1233899: 1},
        4: {2: 4, 12377338601: 1},
        5: {2: 2, 67: 1, 15683: 1, 26716073: 1},
    }
    for prefix_index, expected_factors in expected_prefix_factors.items():
        reconstructed = math.prod(
            prime**exponent for prime, exponent in expected_factors.items()
        )
        assert prefixes[prefix_index].numerator == reconstructed
        assert all(is_prime(prime) for prime in expected_factors)

    # Exact weighted CRT collapse for several finite K and band depths L.
    crt_checks = 0
    for k_index in (20, 40, 80, 160, 320, 400):
        radius = 4 * k_index + 3
        hutton = prefixes[2 * k_index + 2]
        numerator = hutton.numerator
        denominator = hutton.denominator
        for band_depth in range(1, 6):
            band_primes: list[tuple[int, int]] = []
            for prime in primes:
                if prime > radius:
                    break
                if (2 * band_depth + 1) * prime <= radius:
                    continue
                if prime <= max(7, 2 * band_depth + 1):
                    continue
                if radius >= prime * prime:
                    continue
                prefix_index = (radius // prime + 1) // 2
                assert 1 <= prefix_index <= band_depth
                if prefixes[prefix_index].numerator % prime == 0:
                    continue
                assert valuation(denominator, prime) == 1
                band_primes.append((prime, prefix_index))

            product = math.prod(prime for prime, _ in band_primes)
            assert denominator % product == 0
            cofactor = denominator // product
            common_prefix_denominator = lcm(
                [prefixes[index].denominator for index in range(1, band_depth + 1)]
            )
            assert math.gcd(common_prefix_denominator, product) == 1

            crt_sum = sum(
                chi4(prime)
                * int(common_prefix_denominator * prefixes[prefix_index])
                * (product // prime)
                for prime, prefix_index in band_primes
            )
            assert (
                common_prefix_denominator * numerator - cofactor * crt_sum
            ) % product == 0

            lift = (
                common_prefix_denominator * numerator - cofactor * crt_sum
            ) // product
            reciprocal_sum = sum(
                (
                    Fraction(chi4(prime), prime)
                    * prefixes[prefix_index]
                    for prime, prefix_index in band_primes
                ),
                Fraction(),
            )
            assert hutton == reciprocal_sum + Fraction(
                lift, common_prefix_denominator * cofactor
            )
            crt_checks += 2

    # Explicit fixed-L thresholds from the proof.  If
    # R>(2L+1)X_L and R/(2L+1)<p<=R, then p>X_L, so p is larger than
    # every relevant prefix numerator and than every singular multiplier.
    threshold_rows: list[tuple[int, int, int]] = []
    for band_depth in range(1, 9):
        assert all(prefixes[index] > 0 for index in range(1, band_depth + 1))
        maximum_numerator = max(
            abs(prefixes[index].numerator)
            for index in range(1, band_depth + 1)
        )
        x_bound = max(7, 2 * band_depth + 1, maximum_numerator)
        radius_threshold = (2 * band_depth + 1) * x_bound
        assert radius_threshold // (2 * band_depth + 1) == x_bound
        threshold_rows.append((band_depth, x_bound, radius_threshold))

    # Finite radical ratios.  Trial division also checks that for R>=7 the
    # reduced denominator has no prime factor exceeding R.
    radical_rows: list[tuple[int, int, int, float, float]] = []
    for k_index in (20, 50, 100, 200, 400):
        radius = 4 * k_index + 3
        hutton = prefixes[2 * k_index + 2]
        radius_primes = [prime for prime in primes if prime <= radius]
        factors, remainder = factor_over_primes(hutton.denominator, radius_primes)
        assert remainder == 1
        log_radical = sum(math.log(prime) for prime in factors)
        theta = sum(math.log(prime) for prime in radius_primes)
        assert log_radical <= theta + 1e-12
        radical_rows.append(
            (k_index, radius, len(factors), log_radical / radius, theta / radius)
        )

    print(f"source sha256: {SOURCE_SHA256}")
    print(f"generic local-coordinate assertions: {local_checks}")
    print(f"generic exact-valuation assertions: {valuation_checks}")
    print(f"one-fifth-band assertions: {one_fifth_checks}")
    print(f"observed cancelling (prefix index, prime) pairs: {sorted(observed_cancellations)}")
    print(
        "one-fifth exceptional witness: "
        f"p={exceptional_prime} R={exceptional_radius} K={exceptional_k} residue=0"
    )
    print(f"weighted CRT/decomposition assertions: {crt_checks}")
    print("fixed-depth thresholds (L, X_L, strict R threshold):")
    for row in threshold_rows:
        print("  " + " ".join(map(str, row)))
    print("radical experiment (K, R, support size, log(rad Q)/R, theta(R)/R):")
    for k_index, radius, size, ratio, theta_ratio in radical_rows:
        print(
            f"  {k_index} {radius} {size} {ratio:.12f} {theta_ratio:.12f}"
        )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
