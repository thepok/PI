#!/usr/bin/env python3
"""High-precision replay of the q=100, A=96 full-primitive T139 witness.

This uses only Python's standard-library Decimal arithmetic.  It is an
independent high-precision replay with large assertion margins, not a formal
directed-interval certificate.
"""

from __future__ import annotations

from decimal import Decimal as D
from decimal import ROUND_FLOOR, getcontext
from functools import lru_cache


getcontext().prec = 190
EPS = D(10) ** -175
Q = 100
A = 96
N = 107

ComplexD = tuple[D, D]


def atan_inverse(r: int) -> D:
    """Alternating series for atan(1/r), at the active Decimal precision."""
    rr = D(r) * D(r)
    term = D(1) / D(r)
    total = term
    j = 0
    while True:
        j += 1
        term = -term / rr
        addend = term / D(2 * j + 1)
        total += addend
        if abs(addend) < EPS:
            return total


PI = 16 * atan_inverse(5) - 4 * atan_inverse(239)
TWO_PI = 2 * PI


def sincos_angle(angle: D) -> ComplexD:
    """Return (cos(angle), sin(angle)) by reduction and Taylor series."""
    turns = (angle / TWO_PI).to_integral_value(rounding=ROUND_FLOOR)
    angle -= turns * TWO_PI
    if angle > PI:
        angle -= TWO_PI

    square = angle * angle
    sin_total = angle
    cos_total = D(1)
    sin_term = angle
    cos_term = D(1)
    j = 0
    while True:
        j += 1
        sin_term *= -square / D((2 * j) * (2 * j + 1))
        cos_term *= -square / D((2 * j - 1) * (2 * j))
        sin_total += sin_term
        cos_total += cos_term
        if abs(sin_term) < EPS and abs(cos_term) < EPS:
            return cos_total, sin_total


def cadd(z: ComplexD, w: ComplexD) -> ComplexD:
    return z[0] + w[0], z[1] + w[1]


def csub(z: ComplexD, w: ComplexD) -> ComplexD:
    return z[0] - w[0], z[1] - w[1]


def cmul(z: ComplexD, w: ComplexD) -> ComplexD:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def cscale(scale: D, z: ComplexD) -> ComplexD:
    return scale * z[0], scale * z[1]


def phase_rational(numerator: int, denominator: int = 1) -> ComplexD:
    return sincos_angle(TWO_PI * D(numerator) / D(denominator))


def fejer_square_coefficient(h: int) -> D:
    h = abs(h)
    if h <= Q:
        numerator = (
            4 * Q**3 + 2 * Q - 6 * Q * h**2 + 3 * h**3 - 3 * h
        )
        return D(numerator) / D(6 * Q**2)
    if h <= 2 * Q - 2:
        numerator = (2 * Q - h - 1) * (2 * Q - h) * (2 * Q - h + 1)
        return D(numerator) / D(6 * Q**2)
    return D(0)


BETA = sincos_angle(PI / D(Q))[0]


def alpha(h: int) -> D:
    return (
        fejer_square_coefficient(h - 1)
        + fejer_square_coefficient(h + 1)
    ) / 2 - BETA * fejer_square_coefficient(h)


PRIMITIVE_SUPPORT = tuple(u for u in range(1, 2 * Q) if u % 10 != 0)


def primitive_coefficient(u: int) -> ComplexD:
    result = cscale(alpha(u), phase_rational(7 * u, 200))
    if u <= 19:
        result = cadd(
            result, cscale(alpha(10 * u), phase_rational(7 * u, 20))
        )
    if u == 1:
        result = result[0] - alpha(100), result[1]
    return result


@lru_cache(maxsize=None)
def orbit_phase(h: int, n: int) -> ComplexD:
    cycles = D(h * 10**n) * PI
    fractional = cycles - cycles.to_integral_value(rounding=ROUND_FLOOR)
    return sincos_angle(TWO_PI * fractional)


def sum_complex(values: list[ComplexD]) -> ComplexD:
    real = sum((z[0] for z in values), D(0))
    imag = sum((z[1] for z in values), D(0))
    return real, imag


def primitive_polynomial_at(n: int) -> ComplexD:
    return sum_complex(
        [cmul(primitive_coefficient(u), orbit_phase(u, n)) for u in PRIMITIVE_SUPPORT]
    )


def primitive_sum() -> tuple[ComplexD, ComplexD]:
    terms = [primitive_polynomial_at(n) for n in range(N)]
    return sum_complex(terms), terms[N - 1]


def endpoint() -> ComplexD:
    result = (D(0), D(0))
    for m in range(1, 20):
        if m == 10:
            continue
        coefficient = cscale(alpha(10 * m), phase_rational(7 * m, 20))
        result = cadd(
            result,
            cmul(coefficient, csub(orbit_phase(m, N), orbit_phase(m, 0))),
        )

    valuation_two_block = csub(
        cadd(orbit_phase(1, N), orbit_phase(1, N + 1)),
        cadd(orbit_phase(1, 0), orbit_phase(1, 1)),
    )
    return cadd(result, cscale(-alpha(100), valuation_two_block))


def direct_uncompressed_sum() -> ComplexD:
    terms: list[ComplexD] = []
    for h in range(1, 2 * Q):
        exponential_sum = sum_complex([orbit_phase(h, n) for n in range(N)])
        centered = cscale(alpha(h), phase_rational(-193 * h, 200))
        terms.append(cmul(centered, exponential_sum))
    return sum_complex(terms)


def in_open_decimal_interval(value: D, lower: str, upper: str) -> bool:
    return D(lower) < value < D(upper)


def main() -> None:
    assert len(PRIMITIVE_SUPPORT) == 180

    z, last_term = primitive_sum()
    boundary = endpoint()
    direct = direct_uncompressed_sum()
    reconstructed = cadd(z, boundary)

    # Independent direct and compressed evaluations must agree far beyond
    # the displayed precision.
    assert abs(direct[0] - reconstructed[0]) < D("1e-150")
    assert abs(direct[1] - reconstructed[1]) < D("1e-150")

    alpha_zero = alpha(0)
    budget = sum((alpha(10 * m) for m in range(1, 20)), D(0)) + alpha(100)
    budget_closed = D(550) * (1 - BETA) - alpha_zero
    assert abs(budget - budget_closed) < D("1e-170")

    core_constant = -D(100) * z[0] / D(N)
    compatible_constant = D(50) * alpha_zero
    termwise_constant = -D(100) * last_term[0]
    exact_defect = -D(2) * reconstructed[0] / D(N)

    assert in_open_decimal_interval(alpha_zero, "0.02289762041667709", "0.02289762041667710")
    assert in_open_decimal_interval(budget, "0.2484941784309665", "0.2484941784309666")
    assert in_open_decimal_interval(last_term[0], "-0.274251155085671", "-0.274251155085670")
    assert in_open_decimal_interval(z[0], "-1.678502644720623", "-1.678502644720622")
    assert in_open_decimal_interval(boundary[0], "0.2622735217394053", "0.2622735217394055")
    assert in_open_decimal_interval(exact_defect, "0.0264715723921722", "0.0264715723921724")

    assert core_constant > compatible_constant
    assert termwise_constant > compatible_constant
    assert exact_defect > alpha_zero

    pi_prefix = str((D(10) ** 108 * PI).to_integral_value(rounding=ROUND_FLOOR))
    expected_prefix = (
        "314159265358979323846264338327950288419716939937510582097494459230781640"
        "6286208998628034825342117067982148086"
    )
    assert pi_prefix == expected_prefix
    decimal_digits = pi_prefix[1:]
    assert len(decimal_digits) == 108
    assert all(decimal_digits[n : n + 2] != "96" for n in range(N))

    print("status: PASS (high-precision replay; not a directed-interval proof)")
    print(f"alpha0={alpha_zero}")
    print(f"endpoint_budget={budget}")
    print(f"Re_P_x106={last_term[0]}")
    print(f"Re_Z_107={z[0]}")
    print(f"Re_endpoint_107={boundary[0]}")
    print(f"all_prefix_required_C={core_constant}")
    print(f"termwise_required_C={termwise_constant}")
    print(f"T139_compatible_C_upper={compatible_constant}")
    print(f"exact_signed_defect={exact_defect}")
    print("decimal_prefix_avoids_96_for_n=0..106: true")


if __name__ == "__main__":
    main()
