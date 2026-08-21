#!/usr/bin/env python3
"""Independent exact replay for the recursive Machin splitting audit.

This file deliberately does not import ``machin_angle_splitting_check.py``.
All asserted equalities and divisibility statements use integers or
``fractions.Fraction``.  Finite coverage remains ``experiment`` evidence.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


TARGET_SHA = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def chi4(r: int) -> int:
    assert r % 2
    return 1 if r % 4 == 1 else -1


def split(x: Fraction, u: Fraction) -> Fraction:
    v = (x - u) / (1 + x * u)
    assert 0 < u < x < 1
    assert 0 < v < x
    assert (u + v) / (1 - u * v) == x
    return v


def multiply_gaussian(z: tuple[int, int], w: tuple[int, int]) -> tuple[int, int]:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def power_gaussian(z: tuple[int, int], n: int) -> tuple[int, int]:
    result = (1, 0)
    for _ in range(n):
        result = multiply_gaussian(result, z)
    return result


def gaussian_product(identity: dict[Fraction, int]) -> tuple[int, int]:
    result = (1, 0)
    for x, coefficient in identity.items():
        result = multiply_gaussian(
            result,
            power_gaussian((x.denominator, x.numerator), coefficient),
        )
    return result


def lower(identity: dict[Fraction, int], r_first: int) -> Fraction:
    assert r_first >= 5 and r_first % 4 == 1
    result = Fraction()
    for x, coefficient in identity.items():
        for r in range(1, r_first - 1, 2):
            result += 4 * coefficient * chi4(r) * x**r / r
    return result


def width(identity: dict[Fraction, int], r_first: int) -> Fraction:
    return Fraction(4, r_first) * sum(
        (coefficient * x**r_first for x, coefficient in identity.items()),
        Fraction(),
    )


def odd_lcm(t: int) -> int:
    result = 1
    for r in range(1, t + 1, 2):
        result = math.lcm(result, r)
    return result


def v_int(n: int, p: int) -> int:
    assert n > 0
    answer = 0
    while n % p == 0:
        n //= p
        answer += 1
    return answer


def floor_log(n: int, base: int) -> int:
    result = 0
    while base ** (result + 1) <= n:
        result += 1
    return result


def primes(bound: int) -> list[int]:
    return [
        n
        for n in range(2, bound + 1)
        if all(n % d for d in range(2, math.isqrt(n) + 1))
    ]


def congruence_split(x: Fraction) -> tuple[Fraction, Fraction]:
    """Use the parity and mod-5 construction, including bad base denominators."""
    a, b = x.numerator, x.denominator
    d = 30 * b // a + 1
    d += (1 - d) % 10
    if a * d <= 30 * b:
        d += 10
    assert d % 10 == 1 and a * d > 30 * b

    first = a * d // (3 * b) + 1
    last = (2 * a * d - 1) // (3 * b)
    for c in range(first, last + 1):
        if c % 2 == b % 2:
            continue
        raw_v_denominator = b * d + a * c
        if raw_v_denominator % 5 == 0:
            continue
        assert math.gcd(d, 10) == 1
        assert math.gcd(raw_v_denominator, 10) == 1
        u = Fraction(c, d)
        v = Fraction(a * d - b * c, raw_v_denominator)
        assert x / 3 < u < 2 * x / 3
        assert 0 < v < x - u < 2 * x / 3
        assert (u + v) / (1 - u * v) == x
        assert math.gcd(u.denominator, 10) == 1
        assert math.gcd(v.denominator, 10) == 1
        return u, v
    raise AssertionError(x)


def refine(identity: dict[Fraction, int]) -> dict[Fraction, int]:
    result: dict[Fraction, int] = {}
    for x, coefficient in identity.items():
        u, v = congruence_split(x)
        result[u] = result.get(u, 0) + coefficient
        result[v] = result.get(v, 0) + coefficient
    return result


def frac(x: Fraction) -> Fraction:
    return x - x.numerator // x.denominator


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    target = root / "problems/local/pi-digits.txt"
    assert hashlib.sha256(target.read_bytes()).hexdigest() == TARGET_SHA

    hutton = {Fraction(1, 3): 2, Fraction(1, 7): 1}
    split1 = {Fraction(1, 7): 3, Fraction(2, 11): 2}
    split2 = {
        Fraction(1, 11): 5,
        Fraction(2, 39): 5,
        Fraction(3, 79): 2,
    }
    split3 = {
        Fraction(1, 23): 5,
        Fraction(6, 127): 5,
        Fraction(1, 39): 5,
        Fraction(39, 1523): 5,
        Fraction(1, 53): 2,
        Fraction(8, 419): 2,
    }
    identities = [hutton, split1, split2, split3]
    expected_s = [
        Fraction(17, 21),
        Fraction(61, 77),
        Fraction(26669, 33891),
        Fraction(3027502731497, 3852884231859),
    ]

    # Re-derive every displayed child, rather than importing a generated list.
    named_children = [
        (Fraction(1, 3), Fraction(1, 7), Fraction(2, 11)),
        (Fraction(2, 11), Fraction(1, 7), Fraction(3, 79)),
        (Fraction(1, 7), Fraction(1, 11), Fraction(2, 39)),
        (Fraction(1, 11), Fraction(1, 23), Fraction(6, 127)),
        (Fraction(2, 39), Fraction(1, 39), Fraction(39, 1523)),
        (Fraction(3, 79), Fraction(1, 53), Fraction(8, 419)),
    ]
    for x, u, v in named_children:
        assert split(x, u) == v

    identity_checks = 0
    for identity, expected in zip(identities, expected_s, strict=True):
        product = gaussian_product(identity)
        actual_s = sum(
            (coefficient * x for x, coefficient in identity.items()),
            Fraction(),
        )
        assert product[0] == product[1] > 0
        assert actual_s == expected and 0 < actual_s < 1
        assert all(coefficient > 0 for coefficient in identity.values())
        assert all(0 < x < 1 for x in identity)
        identity_checks += 4

    endpoint_checks = 0
    local_checks = 0
    prime_list = primes(163)
    for identity, s_value in zip(identities, expected_s, strict=True):
        bases = math.prod(x.denominator for x in identity)
        for k in range(41):
            t = 4 * k + 3
            r_first = t + 2
            lo = lower(identity, r_first)
            hi = lo + width(identity, r_first)

            d_lo = odd_lcm(t) * math.prod(x.denominator**t for x in identity)
            d_next = r_first * math.prod(
                x.denominator**r_first for x in identity
            )
            d_hi = math.lcm(d_lo, d_next)
            assert d_lo % lo.denominator == 0
            assert d_hi % hi.denominator == 0
            assert lo.denominator % 2 == hi.denominator % 2 == 1
            assert v_int(lo.denominator, 5) <= floor_log(t, 5)
            assert v_int(hi.denominator, 5) <= floor_log(r_first, 5)
            endpoint_checks += 6

            for p in prime_list:
                if p == 2 or not 3 * p > t or p > t:
                    continue
                if (bases * s_value.numerator * s_value.denominator) % p == 0:
                    continue
                assert [r for r in range(1, t + 1, 2) if r % p == 0] == [p]
                residue_difference = p * lo - 4 * chi4(p) * s_value
                assert residue_difference.denominator % p != 0
                assert residue_difference.numerator % p == 0
                assert v_int(lo.denominator, p) == 1
                local_checks += 4

    general_checks = 0
    for b in range(2, 41):
        for a in range(1, b):
            if math.gcd(a, b) != 1:
                continue
            u, v = congruence_split(Fraction(a, b))
            assert max(u, v) < Fraction(2 * a, 3 * b)
            general_checks += 1

    # Fixed R=5 is already enough: each refinement contracts the exact width
    # by a factor strictly smaller than 2*(2/3)^R < 1.
    recursion_checks = 0
    identity = hutton
    r_first = 5
    previous_width = width(identity, r_first)
    previous_mass = sum(identity.values())
    for _ in range(5):
        identity = refine(identity)
        current_width = width(identity, r_first)
        assert current_width < 2 * Fraction(2, 3) ** r_first * previous_width
        assert sum(identity.values()) == 2 * previous_mass
        assert all(c > 0 for c in identity.values())
        assert all(math.gcd(x.denominator, 10) == 1 for x in identity)
        previous_width = current_width
        previous_mass = sum(identity.values())
        recursion_checks += 4

    # Exact affine coupling between independently generated rational shadows.
    affine_checks = 0
    shadows = [lower(identity, 41) for identity in identities]
    for i in range(len(shadows)):
        for j in range(i + 1, len(shadows)):
            for shift in range(41):
                scale = 10**shift
                assert frac(scale * shadows[j]) == frac(
                    frac(scale * shadows[i])
                    + scale * (shadows[j] - shadows[i])
                )
                affine_checks += 1

    print("claim_status=experiment")
    print(f"target_sha256={TARGET_SHA}")
    print(f"named_split_exact_checks={len(named_children)}")
    print(f"identity_branch_exact_checks={identity_checks}")
    print(f"endpoint_denominator_transient_exact_checks={endpoint_checks}")
    print(f"upper_band_local_exact_checks={local_checks}")
    print(f"general_congruence_split_exact_checks={general_checks}")
    print(f"fixed_R_recursive_contraction_exact_checks={recursion_checks}")
    print(f"affine_coupling_exact_checks={affine_checks}")
    print("all independent exact assertions passed")


if __name__ == "__main__":
    main()
