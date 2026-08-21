#!/usr/bin/env python3
"""Certify decimal digits of pi using exact-integer Chudnovsky bounds."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path


CHUDNOVSKY_C = 640320
C3_OVER_24 = CHUDNOVSKY_C**3 // 24
LINEAR_0 = 13591409
LINEAR_STEP = 545140134
SQRT_CONSTANT = 10005
PI_FACTOR = 426880

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def binary_split(a: int, b: int) -> tuple[int, int, int]:
    """Return P, Q, T with T/Q equal to terms [a,b) in split form."""
    if b - a == 1:
        if a == 0:
            return 1, 1, LINEAR_0
        p = (6 * a - 5) * (2 * a - 1) * (6 * a - 1)
        q = a**3 * C3_OVER_24
        t = p * (LINEAR_0 + LINEAR_STEP * a)
        if a & 1:
            t = -t
        return p, q, t
    midpoint = (a + b) // 2
    p1, q1, t1 = binary_split(a, midpoint)
    p2, q2, t2 = binary_split(midpoint, b)
    return p1 * p2, q1 * q2, t1 * q2 + p1 * t2


def sha256_decimal(value: int) -> str:
    return hashlib.sha256(str(value).encode("ascii")).hexdigest()


def certify(fraction_digits: int) -> tuple[str, dict[str, object]]:
    if not 1 <= fraction_digits <= 2_000_000:
        raise ValueError("fraction digit count must be between 1 and 2,000,000")

    # Each Chudnovsky term contributes more than 14 decimal digits. The extra
    # terms make the adjacent-partial-sum interval far narrower than one unit
    # after scaling by 10^D; singleton-floor equality below is the final check.
    terms = fraction_digits // 14 + 20
    p, q, t = binary_split(0, terms)
    pn, qn, tn = binary_split(terms, terms + 1)
    q_next = q * qn
    t_next = t * qn + p * tn

    if t * q_next <= t_next * q:
        sum_lower_t, sum_lower_q = t, q
        sum_upper_t, sum_upper_q = t_next, q_next
        partial_order = "S_n < S_(n+1)"
    else:
        sum_lower_t, sum_lower_q = t_next, q_next
        sum_upper_t, sum_upper_q = t, q
        partial_order = "S_(n+1) < S_n"
    if not (0 < sum_lower_t * sum_upper_q < sum_upper_t * sum_lower_q):
        raise AssertionError("adjacent Chudnovsky partial sums are not ordered")

    # A global elementary majorization establishes decreasing term magnitudes:
    # the factorial ratio is at most 6^6/C^3 and L_(k+1)/L_k < 42.
    if not (LINEAR_0 + LINEAR_STEP < 42 * LINEAR_0):
        raise AssertionError("linear-factor ratio bound failed")
    if not (6**6 * 42 < CHUDNOVSKY_C**3):
        raise AssertionError("Chudnovsky term-ratio bound failed")

    scale = 10**fraction_digits
    radicand = SQRT_CONSTANT * scale * scale
    sqrt_floor = math.isqrt(radicand)
    if not (sqrt_floor**2 <= radicand < (sqrt_floor + 1) ** 2):
        raise AssertionError("integer square-root enclosure failed")

    # C_lo <= 426880*sqrt(10005)*10^D < C_hi and
    # S_lo < S < S_hi. Hence C_lo/S_hi <= pi*10^D < C_hi/S_lo.
    c_lower = PI_FACTOR * sqrt_floor
    c_upper = PI_FACTOR * (sqrt_floor + 1)
    lower_num = c_lower * sum_upper_q
    lower_den = sum_upper_t
    upper_num = c_upper * sum_lower_q
    upper_den = sum_lower_t
    lower_floor = lower_num // lower_den
    strict_upper_floor = (upper_num - 1) // upper_den
    if lower_floor != strict_upper_floor:
        raise AssertionError("rational enclosure does not certify a singleton floor")

    scaled_decimal = str(lower_floor)
    if len(scaled_decimal) != fraction_digits + 1 or scaled_decimal[0] != "3":
        raise AssertionError("certified scaled floor has unexpected shape")
    digits = scaled_decimal[1:]
    certificate: dict[str, object] = {
        "algorithm": "exact-integer-chudnovsky-adjacent-partial-sums-v1",
        "certificate": "rational lower and strict upper bounds force one floor(pi*10^D)",
        "chudnovsky_identity": "pi=426880*sqrt(10005)/sum_k((-1)^k*(6k)!*(13591409+545140134k)/((3k)!*(k!)^3*640320^(3k)))",
        "exact_integer_arithmetic": True,
        "fraction_digits": fraction_digits,
        "linear_ratio_bound": "L_(k+1)/L_k < 42 for every k>=0",
        "partial_order": partial_order,
        "scale_10_power_exact": True,
        "series_bracket": "adjacent partial sums bracket the alternating series because absolute terms strictly decrease to zero",
        "singleton_floor_interval": True,
        "sqrt_bracket": "isqrt(10005*10^(2D)) <= sqrt(10005)*10^D < isqrt(10005*10^(2D))+1",
        "term_ratio_bound": "abs(a_(k+1)/a_k) < 6^6*42/640320^3 < 1",
        "terms_in_lower_partial_sum": terms,
        "terms_in_upper_partial_sum": terms + 1,
        "certified_scaled_floor_sha256": sha256_decimal(lower_floor),
        "fractional_digits_sha256": hashlib.sha256(digits.encode("ascii") + b"\n").hexdigest(),
    }
    return digits, certificate


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fraction_digits", type=int)
    parser.add_argument("digits_output", type=Path)
    parser.add_argument("certificate_output", type=Path)
    args = parser.parse_args()
    digits, certificate = certify(args.fraction_digits)
    args.digits_output.write_text(digits + "\n", encoding="ascii", newline="\n")
    args.certificate_output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


if __name__ == "__main__":
    main()
