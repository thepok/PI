#!/usr/bin/env python3
"""Exact finite replay for ``machin_angle_splitting_attack.md``.

All algebraic identity, width, denominator, transient, and local-prime
assertions use integer arithmetic and :class:`fractions.Fraction`.  The
analytic alternating-series inequality itself is cited in the report rather
than certified by this script.  Decimal logarithms in the printed scale table
are finite diagnostics only and have status ``experiment``.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


Identity = dict[Fraction, int]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def chi4(odd: int) -> int:
    assert odd % 2 == 1
    return 1 if odd % 4 == 1 else -1


def split_argument(x: Fraction, u: Fraction) -> Fraction:
    """Return ``v`` for ``atan(x) = atan(u) + atan(v)``."""
    assert 0 < u < x < 1
    v = (x - u) / (1 + x * u)
    assert 0 < v < x
    assert (u + v) / (1 - u * v) == x
    return v


def split_identity(identity: Identity, x: Fraction, u: Fraction) -> Identity:
    coefficient = identity[x]
    v = split_argument(x, u)
    answer = dict(identity)
    del answer[x]
    answer[u] = answer.get(u, 0) + coefficient
    answer[v] = answer.get(v, 0) + coefficient
    return answer


def gaussian_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def gaussian_pow(base: tuple[int, int], exponent: int) -> tuple[int, int]:
    answer = (1, 0)
    power = base
    while exponent:
        if exponent & 1:
            answer = gaussian_mul(answer, power)
        power = gaussian_mul(power, power)
        exponent //= 2
    return answer


def gaussian_certificate(identity: Identity) -> tuple[int, int]:
    answer = (1, 0)
    for argument, coefficient in sorted(identity.items()):
        answer = gaussian_mul(
            answer,
            gaussian_pow((argument.denominator, argument.numerator), coefficient),
        )
    assert answer[0] == answer[1] > 0
    return answer


def odd_taylor_prefix(x: Fraction, maximum_exponent: int) -> Fraction:
    assert maximum_exponent % 4 == 3
    return sum(
        (
            Fraction(chi4(exponent), exponent) * x**exponent
            for exponent in range(1, maximum_exponent + 1, 2)
        ),
        Fraction(),
    )


def lower_shadow(identity: Identity, first_omitted_exponent: int) -> Fraction:
    assert first_omitted_exponent % 4 == 1
    maximum_exponent = first_omitted_exponent - 2
    return 4 * sum(
        (
            coefficient * odd_taylor_prefix(argument, maximum_exponent)
            for argument, coefficient in identity.items()
        ),
        Fraction(),
    )


def bracket_width(identity: Identity, first_omitted_exponent: int) -> Fraction:
    assert first_omitted_exponent % 4 == 1
    return Fraction(4, first_omitted_exponent) * sum(
        (
            coefficient * argument**first_omitted_exponent
            for argument, coefficient in identity.items()
        ),
        Fraction(),
    )


def odd_lcm(maximum: int) -> int:
    answer = 1
    for odd in range(1, maximum + 1, 2):
        answer = math.lcm(answer, odd)
    return answer


def natural_lower_denominator(identity: Identity, first_omitted_exponent: int) -> int:
    maximum_exponent = first_omitted_exponent - 2
    return odd_lcm(maximum_exponent) * math.prod(
        argument.denominator**maximum_exponent for argument in identity
    )


def natural_upper_denominator(identity: Identity, first_omitted_exponent: int) -> int:
    """A safe common denominator for the upper bracket endpoint."""
    lower_natural = natural_lower_denominator(identity, first_omitted_exponent)
    next_terms_natural = first_omitted_exponent * math.prod(
        argument.denominator**first_omitted_exponent for argument in identity
    )
    return math.lcm(lower_natural, next_terms_natural)


def valuation(value: int, prime: int) -> int:
    assert value > 0
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def floor_log(value: int, base: int) -> int:
    assert value >= 1 and base >= 2
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def primes_through(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    if bound >= 0:
        sieve[0] = 0
    if bound >= 1:
        sieve[1] = 0
    for prime in range(2, math.isqrt(bound) + 1):
        if sieve[prime]:
            sieve[prime * prime : bound + 1 : prime] = b"\x00" * (
                (bound - prime * prime) // prime + 1
            )
    return [prime for prime in range(2, bound + 1) if sieve[prime]]


def linear_shadow(identity: Identity) -> Fraction:
    return sum(
        (coefficient * argument for argument, coefficient in identity.items()),
        Fraction(),
    )


def admissible_balanced_split(x: Fraction) -> tuple[Fraction, Fraction]:
    """Find one exact split with both new denominators prime to ten.

    The search is only a finite replay.  The report gives the separate
    elementary congruence argument proving that such choices exist at every
    recursive node.
    """
    for denominator in range(3, 5000):
        if math.gcd(denominator, 10) != 1:
            continue
        center = x * denominator / 2
        center_floor = center.numerator // center.denominator
        for numerator in range(max(1, center_floor - 8), center_floor + 10):
            u = Fraction(numerator, denominator)
            if not x / 3 < u < 2 * x / 3:
                continue
            v = split_argument(x, u)
            if (
                math.gcd(u.denominator, 10) == 1
                and math.gcd(v.denominator, 10) == 1
                and max(u, v) < 2 * x / 3
            ):
                return u, v
    raise AssertionError(f"balanced split search exhausted for {x}")


def congruence_constructed_split(x: Fraction) -> tuple[Fraction, Fraction]:
    """Replay the report's explicit parity/mod-5 construction."""
    numerator = x.numerator
    denominator = x.denominator
    assert 0 < numerator < denominator

    # Make the open admissible interval have length greater than ten, and
    # then move to the next integer congruent to one modulo ten.
    split_denominator = 30 * denominator // numerator + 1
    split_denominator += (1 - split_denominator) % 10
    if numerator * split_denominator <= 30 * denominator:
        split_denominator += 10
    assert split_denominator % 10 == 1

    first = numerator * split_denominator // (3 * denominator) + 1
    last = (2 * numerator * split_denominator - 1) // (3 * denominator)
    for split_numerator in range(first, last + 1):
        if split_numerator % 2 == denominator % 2:
            continue
        if (
            denominator * split_denominator
            + numerator * split_numerator
        ) % 5 == 0:
            continue
        u = Fraction(split_numerator, split_denominator)
        v = split_argument(x, u)
        assert x / 3 < u < 2 * x / 3
        assert 0 < v < x - u < 2 * x / 3
        assert math.gcd(u.denominator, 10) == 1
        assert math.gcd(v.denominator, 10) == 1
        return u, v
    raise AssertionError(f"congruence construction failed for {x}")


def recursively_split(identity: Identity) -> Identity:
    answer: Identity = {}
    for argument, coefficient in identity.items():
        u, v = admissible_balanced_split(argument)
        answer[u] = answer.get(u, 0) + coefficient
        answer[v] = answer.get(v, 0) + coefficient
    return answer


def log10_fraction(value: Fraction) -> float:
    assert value > 0
    return math.log10(value.numerator) - math.log10(value.denominator)


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    hutton: Identity = {Fraction(1, 3): 2, Fraction(1, 7): 1}

    # atan(1/3) = atan(1/7) + atan(2/11).
    first = split_identity(hutton, Fraction(1, 3), Fraction(1, 7))
    assert first == {Fraction(1, 7): 3, Fraction(2, 11): 2}

    # Split 2/11 first, merge its 1/7 child, then split the merged 1/7.
    second = split_identity(first, Fraction(2, 11), Fraction(1, 7))
    second = split_identity(second, Fraction(1, 7), Fraction(1, 11))
    assert second == {
        Fraction(1, 11): 5,
        Fraction(2, 39): 5,
        Fraction(3, 79): 2,
    }

    # One simultaneous balanced refinement of all three remaining angles.
    third = split_identity(second, Fraction(1, 11), Fraction(1, 23))
    third = split_identity(third, Fraction(2, 39), Fraction(1, 39))
    third = split_identity(third, Fraction(3, 79), Fraction(1, 53))
    assert third == {
        Fraction(1, 23): 5,
        Fraction(6, 127): 5,
        Fraction(1, 39): 5,
        Fraction(39, 1523): 5,
        Fraction(1, 53): 2,
        Fraction(8, 419): 2,
    }

    identities = [hutton, first, second, third]
    names = ["Hutton", "split-1", "split-2", "split-3"]
    expected_linear = [
        Fraction(17, 21),
        Fraction(61, 77),
        Fraction(26669, 33891),
        Fraction(3027502731497, 3852884231859),
    ]
    expected_largest = [
        Fraction(1, 3),
        Fraction(2, 11),
        Fraction(1, 11),
        Fraction(6, 127),
    ]

    gaussian_checks = 0
    for identity, expected_sum, expected_maximum in zip(
        identities, expected_linear, expected_largest, strict=True
    ):
        gaussian_certificate(identity)
        assert linear_shadow(identity) == expected_sum
        assert max(identity) == expected_maximum
        assert all(
            math.gcd(argument.denominator, 10) == 1 for argument in identity
        )
        # Together with the positive equal Gaussian coordinates, this bound
        # excludes every possible 2*pi branch shift.
        assert 0 < expected_sum < 1
        gaussian_checks += 5

    bracket_algebra_checks = 0
    denominator_checks = 0
    transient_checks = 0
    for identity in identities:
        for index in range(21):
            first_omitted = 4 * index + 5
            lower = lower_shadow(identity, first_omitted)
            width = bracket_width(identity, first_omitted)
            upper = lower + width
            assert width > 0 and upper - lower == width
            bracket_algebra_checks += 2

            lower_natural = natural_lower_denominator(identity, first_omitted)
            upper_natural = natural_upper_denominator(identity, first_omitted)
            assert lower_natural % lower.denominator == 0
            assert upper_natural % upper.denominator == 0
            denominator_checks += 2

            maximum_exponent = first_omitted - 2
            assert lower.denominator % 2 == 1
            assert valuation(lower.denominator, 5) <= floor_log(
                maximum_exponent, 5
            )
            assert upper.denominator % 2 == 1
            assert valuation(upper.denominator, 5) <= floor_log(
                first_omitted, 5
            )
            transient_checks += 4

    # In the top one-third prime band only exponent p is singular.  Fermat
    # reduces its residue to the nonzero rational sum of the leaf arguments.
    upper_band_checks = 0
    upper_band_congruence_checks = 0
    primes = primes_through(4 * 20 + 3)
    for identity in identities:
        linear = linear_shadow(identity)
        excluded = linear.numerator * linear.denominator * math.prod(
            argument.denominator for argument in identity
        )
        for index in range(21):
            maximum_exponent = 4 * index + 3
            lower = lower_shadow(identity, maximum_exponent + 2)
            for prime in primes:
                if prime == 2:
                    continue
                if not maximum_exponent < 3 * prime <= 3 * maximum_exponent:
                    continue
                if excluded % prime == 0:
                    continue
                assert valuation(lower.denominator, prime) == 1
                upper_band_checks += 1
                local_difference = (
                    prime * lower - 4 * chi4(prime) * linear
                )
                assert local_difference.denominator % prime != 0
                assert local_difference.numerator % prime == 0
                upper_band_congruence_checks += 1

    # Independent finite exercise of the general balanced, denominator-safe
    # recursive split.  This is not used as the proof of infinite existence.
    general_split_checks = 0
    for denominator in range(2, 41):
        for numerator in range(1, denominator):
            if math.gcd(numerator, denominator) != 1:
                continue
            x = Fraction(numerator, denominator)
            u, v = congruence_constructed_split(x)
            assert (u + v) / (1 - u * v) == x
            general_split_checks += 1

    recursive = hutton
    recursive_checks = 0
    previous_maximum = max(recursive)
    previous_mass = sum(recursive.values())
    for _ in range(4):
        recursive = recursively_split(recursive)
        assert all(
            math.gcd(argument.denominator, 10) == 1 for argument in recursive
        )
        assert max(recursive) < 2 * previous_maximum / 3
        assert sum(recursive.values()) == 2 * previous_mass
        gaussian_certificate(recursive)
        previous_maximum = max(recursive)
        previous_mass = sum(recursive.values())
        recursive_checks += 4

    print("claim_status=experiment")
    print(f"source_sha256={sha256(source)}")
    print("exact_named_split_checks=6")
    print(f"gaussian_and_identity_exact_checks={gaussian_checks}")
    print(f"bracket_width_algebra_exact_checks={bracket_algebra_checks}")
    print(f"natural_denominator_exact_checks={denominator_checks}")
    print(f"base_ten_transient_exact_checks={transient_checks}")
    print(f"upper_band_prime_survival_exact_checks={upper_band_checks}")
    print(
        "upper_band_local_congruence_exact_checks="
        f"{upper_band_congruence_checks}"
    )
    print(f"general_congruence_split_exact_checks={general_split_checks}")
    print(f"recursive_denominator_safe_exact_checks={recursive_checks}")
    print("finite_scale_table_status=experiment")
    for first_omitted in (21, 41, 81):
        for name, identity in zip(names, identities, strict=True):
            lower = lower_shadow(identity, first_omitted)
            width = bracket_width(identity, first_omitted)
            print(
                "scale "
                f"R={first_omitted} identity={name} "
                f"width_digits={-log10_fraction(width):.2f} "
                f"reduced_denominator_digits={len(str(lower.denominator))}"
            )
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
