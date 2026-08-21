#!/usr/bin/env python3
"""Reproduce T17's exact rational enclosure and T16 decimal-prefix hash."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path


DIGITS = 1_048_596
TERMS = DIGITS // 14 + 20
C = 640_320
C3_OVER_24 = C**3 // 24
A = 13_591_409
B = 545_140_134
PI_FACTOR = 426_880
SQRT_CONSTANT = 10_005
EXPECTED_FILE_SHA256 = "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
EXPECTED_PAYLOAD_SHA256 = "677e20e8d4e416051786d608ba29f6c56b9c84d8bd48132e33f83e8663818989"
PROOF_SOURCE_SHA256 = "69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def binary_split(a: int, b: int) -> tuple[int, int, int]:
    """Return P, Q, T where T/Q is the Chudnovsky sum on [a,b)."""
    if b - a == 1:
        if a == 0:
            return 1, 1, A
        p = (6 * a - 5) * (2 * a - 1) * (6 * a - 1)
        q = a**3 * C3_OVER_24
        t = p * (A + B * a)
        if a & 1:
            t = -t
        return p, q, t
    midpoint = (a + b) // 2
    p1, q1, t1 = binary_split(a, midpoint)
    p2, q2, t2 = binary_split(midpoint, b)
    return p1 * p2, q1 * q2, t1 * q2 + p1 * t2


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_endpoint_bytes(values: dict[str, int]) -> bytes:
    lines = [
        "format=t17-rational-interval-v1",
        f"scale_power={DIGITS}",
    ]
    lines.extend(f"{name}={hex(value)}" for name, value in values.items())
    return ("\n".join(lines) + "\n").encode("ascii")


def certify(output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    # Exact algebra converting Milla, Theorem 10.12, to pi=426880*sqrt(10005)/S.
    assert C**3 == (12 * PI_FACTOR) ** 2 * SQRT_CONSTANT

    # For every k>=0, L_(k+1)/L_k <= 1+B/A < 42. Combining this with
    # (6k+j)/(k+1)<=6 and (3k+j)>=(k+1) gives |a_(k+1)/a_k|<rho<1.
    assert B < 41 * A
    ratio_numerator = 6**6 * 42
    ratio_denominator = C**3
    assert ratio_numerator < ratio_denominator

    p, q, t = binary_split(0, TERMS)
    pn, qn, tn = binary_split(TERMS, TERMS + 1)
    q_next = q * qn
    t_next = t * qn + p * tn

    if t * q_next < t_next * q:
        sum_lower_t, sum_lower_q = t, q
        sum_upper_t, sum_upper_q = t_next, q_next
        partial_order = "S_N < S_(N+1)"
    else:
        sum_lower_t, sum_lower_q = t_next, q_next
        sum_upper_t, sum_upper_q = t, q
        partial_order = "S_(N+1) < S_N"
    assert 0 < sum_lower_t * sum_upper_q < sum_upper_t * sum_lower_q

    scale = 10**DIGITS
    radicand = SQRT_CONSTANT * scale * scale
    sqrt_floor = math.isqrt(radicand)
    assert sqrt_floor**2 <= radicand < (sqrt_floor + 1) ** 2

    # S_lo < S < S_hi and R < sqrt(10005)*10^D < R+1 imply
    # 426880*R/S_hi < pi*10^D < 426880*(R+1)/S_lo.
    lower_num = PI_FACTOR * sqrt_floor * sum_upper_q
    lower_den = sum_upper_t
    upper_num = PI_FACTOR * (sqrt_floor + 1) * sum_lower_q
    upper_den = sum_lower_t
    assert lower_num > 0 and lower_den > 0 and upper_num > 0 and upper_den > 0
    assert lower_num * upper_den < upper_num * lower_den

    lower_floor = lower_num // lower_den
    greatest_integer_below_upper = (upper_num - 1) // upper_den
    assert lower_floor == greatest_integer_below_upper

    scaled_decimal = str(lower_floor)
    assert len(scaled_decimal) == DIGITS + 1 and scaled_decimal[0] == "3"
    payload = scaled_decimal[1:].encode("ascii")
    digit_file = payload + b"\n"
    assert sha256(payload) == EXPECTED_PAYLOAD_SHA256
    assert sha256(digit_file) == EXPECTED_FILE_SHA256

    endpoint_values = {
        "lower_numerator": lower_num,
        "lower_denominator": lower_den,
        "upper_numerator": upper_num,
        "upper_denominator": upper_den,
    }
    endpoint_bytes = canonical_endpoint_bytes(endpoint_values)
    (output_dir / "interval_endpoints.hex").write_bytes(endpoint_bytes)
    (output_dir / "pi_digits.txt").write_bytes(digit_file)

    endpoint_components = {
        name: {
            "bits": value.bit_length(),
            "hex_sha256": sha256(hex(value).encode("ascii")),
        }
        for name, value in endpoint_values.items()
    }
    certificate = {
        "algorithm": "t17-exact-integer-chudnovsky-bracket-v1",
        "analytic_input": {
            "identity": "pi=426880*sqrt(10005)/S",
            "proof_source": "Milla arXiv:1809.00533v6, Theorem 10.12, printed page 44",
            "proof_source_sha256": PROOF_SOURCE_SHA256,
        },
        "decimal_prefix": {
            "file_bytes": len(digit_file),
            "file_sha256": sha256(digit_file),
            "fraction_digits": DIGITS,
            "payload_sha256": sha256(payload),
        },
        "endpoint_components": endpoint_components,
        "endpoint_file_sha256": sha256(endpoint_bytes),
        "exact_integer_arithmetic": True,
        "inequalities_checked": {
            "constant_conversion": True,
            "endpoint_order": True,
            "global_term_ratio": f"{ratio_numerator}/{ratio_denominator}<1",
            "integer_sqrt_bracket": True,
            "singleton_scaled_floor": True,
        },
        "partial_order": partial_order,
        "scale_power": DIGITS,
        "series_terms": TERMS,
        "series_terms_adjacent": TERMS + 1,
    }
    (output_dir / "certificate.json").write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    certify(args.output_dir)


if __name__ == "__main__":
    main()
