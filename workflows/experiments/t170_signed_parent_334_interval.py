#!/usr/bin/env python3
"""Directed-interval replay for the finite T170 signed parent benchmark.

This script certifies, by outward-rounded Decimal interval arithmetic, the
finite numerical inequality

    Re (primitiveBoundaryFourierSum 1000 334 10000) > 47539 / 2500.

The orbit input is the T17 exact-integer Chudnovsky-certified decimal prefix.
The machine-checked T128/T139 identities reduce the primitive score to the
closed boundary kernel, its zero mode, and the explicit endpoint block.

This is an independently replayable exact-computation artifact, not a Lean
proof.  Its repository claim label remains ``experiment`` until a Lean checker
proves the same inequality and the axiom audit is clean.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from hashlib import sha256
from math import factorial
from pathlib import Path


PREC = 100
TAYLOR_TERMS = 62
SUFFIX_DIGITS = 145
Q = 1000
A = 334
N = 10000
EXPECTED_DIGIT_FILE_SHA256 = (
    "77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684"
)

getcontext().prec = PREC
DOWN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)


def dadd(a: Decimal, b: Decimal, upper: bool = False) -> Decimal:
    return (UP if upper else DOWN).add(a, b)


def dsub(a: Decimal, b: Decimal, upper: bool = False) -> Decimal:
    return (UP if upper else DOWN).subtract(a, b)


def dmul(a: Decimal, b: Decimal, upper: bool = False) -> Decimal:
    return (UP if upper else DOWN).multiply(a, b)


def ddiv(a: Decimal, b: Decimal, upper: bool = False) -> Decimal:
    return (UP if upper else DOWN).divide(a, b)


@dataclass(frozen=True)
class Iv:
    lo: Decimal
    hi: Decimal

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError((self.lo, self.hi))

    @staticmethod
    def point(value: int | Decimal) -> "Iv":
        x = value if isinstance(value, Decimal) else Decimal(value)
        return Iv(x, x)

    @staticmethod
    def frac(value: Fraction) -> "Iv":
        numerator = Decimal(value.numerator)
        denominator = Decimal(value.denominator)
        return Iv(ddiv(numerator, denominator), ddiv(numerator, denominator, True))

    def __neg__(self) -> "Iv":
        return Iv(-self.hi, -self.lo)

    def __add__(self, other: object) -> "Iv":
        rhs = as_iv(other)
        return Iv(dadd(self.lo, rhs.lo), dadd(self.hi, rhs.hi, True))

    __radd__ = __add__

    def __sub__(self, other: object) -> "Iv":
        return self + (-as_iv(other))

    def __rsub__(self, other: object) -> "Iv":
        return as_iv(other) - self

    def __mul__(self, other: object) -> "Iv":
        rhs = as_iv(other)
        lows = [dmul(x, y) for x in (self.lo, self.hi) for y in (rhs.lo, rhs.hi)]
        highs = [
            dmul(x, y, True)
            for x in (self.lo, self.hi)
            for y in (rhs.lo, rhs.hi)
        ]
        return Iv(min(lows), max(highs))

    __rmul__ = __mul__

    def reciprocal(self) -> "Iv":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError(self)
        return Iv(ddiv(Decimal(1), self.hi), ddiv(Decimal(1), self.lo, True))

    def __truediv__(self, other: object) -> "Iv":
        return self * as_iv(other).reciprocal()

    def square(self) -> "Iv":
        if self.lo <= 0 <= self.hi:
            upper = max(dmul(self.lo, self.lo, True), dmul(self.hi, self.hi, True))
            return Iv(Decimal(0), upper)
        products = [dmul(self.lo, self.lo), dmul(self.hi, self.hi)]
        uppers = [dmul(self.lo, self.lo, True), dmul(self.hi, self.hi, True)]
        return Iv(min(products), max(uppers))

    def width(self) -> Decimal:
        return dsub(self.hi, self.lo, True)


def as_iv(value: object) -> Iv:
    if isinstance(value, Iv):
        return value
    if isinstance(value, Fraction):
        return Iv.frac(value)
    if isinstance(value, Decimal):
        return Iv.point(value)
    if isinstance(value, int):
        return Iv.point(value)
    raise TypeError(type(value))


@dataclass(frozen=True)
class CIv:
    re: Iv
    im: Iv

    @staticmethod
    def zero() -> "CIv":
        return CIv(Iv.point(0), Iv.point(0))

    def __neg__(self) -> "CIv":
        return CIv(-self.re, -self.im)

    def __add__(self, other: object) -> "CIv":
        rhs = as_civ(other)
        return CIv(self.re + rhs.re, self.im + rhs.im)

    __radd__ = __add__

    def __sub__(self, other: object) -> "CIv":
        return self + (-as_civ(other))

    def __mul__(self, other: object) -> "CIv":
        rhs = as_civ(other)
        return CIv(
            self.re * rhs.re - self.im * rhs.im,
            self.re * rhs.im + self.im * rhs.re,
        )

    __rmul__ = __mul__


def as_civ(value: object) -> CIv:
    if isinstance(value, CIv):
        return value
    return CIv(as_iv(value), Iv.point(0))


def atan_inv_bounds(q: int, terms: int) -> tuple[Fraction, Fraction]:
    partial = Fraction(0)
    for r in range(terms):
        term = Fraction(1, (2 * r + 1) * q ** (2 * r + 1))
        partial += term if r % 2 == 0 else -term
    next_term = Fraction(1, (2 * terms + 1) * q ** (2 * terms + 1))
    if terms % 2 == 0:
        return partial, partial + next_term
    return partial - next_term, partial


def machin_pi_interval(terms: int = 160) -> Iv:
    l5, u5 = atan_inv_bounds(5, terms)
    l239, u239 = atan_inv_bounds(239, terms)
    return Iv(Iv.frac(16 * l5 - 4 * u239).lo, Iv.frac(16 * u5 - 4 * l239).hi)


PI = machin_pi_interval()


def pow_up(x: Decimal, exponent: int) -> Decimal:
    result = Decimal(1)
    base = x.copy_abs()
    n = exponent
    while n:
        if n & 1:
            result = UP.multiply(result, base)
        n //= 2
        if n:
            base = UP.multiply(base, base)
    return result


def sincos_point(x: Decimal) -> tuple[Iv, Iv]:
    """Taylor enclosure at an exact Decimal point with |x| <= pi."""
    if x.copy_abs() > PI.hi:
        raise ValueError(f"unreduced angle {x}")
    X = Iv.point(x)
    X2 = X * X
    cosine = Iv.point(1)
    cos_term = Iv.point(1)
    sine = X
    sin_term = X
    for m in range(1, TAYLOR_TERMS + 1):
        cos_term = cos_term * (-X2) * Fraction(1, (2 * m - 1) * (2 * m))
        cosine += cos_term
        sin_term = sin_term * (-X2) * Fraction(1, (2 * m) * (2 * m + 1))
        sine += sin_term
    ax = x.copy_abs()
    cos_rem = ddiv(
        pow_up(ax, 2 * TAYLOR_TERMS + 1),
        Decimal(factorial(2 * TAYLOR_TERMS + 1)),
        True,
    )
    sin_rem = ddiv(
        pow_up(ax, 2 * TAYLOR_TERMS + 2),
        Decimal(factorial(2 * TAYLOR_TERMS + 2)),
        True,
    )
    return (
        Iv(dsub(cosine.lo, cos_rem), dadd(cosine.hi, cos_rem, True)),
        Iv(dsub(sine.lo, sin_rem), dadd(sine.hi, sin_rem, True)),
    )


def sincos_interval(x: Iv) -> tuple[Iv, Iv]:
    cosine, sine = sincos_point(x.lo)
    width = x.width()
    return (
        Iv(dsub(cosine.lo, width), dadd(cosine.hi, width, True)),
        Iv(dsub(sine.lo, width), dadd(sine.hi, width, True)),
    )


def centered_interval(lo: Fraction, hi: Fraction) -> tuple[Fraction, Fraction]:
    """Reduce a narrow exact interval modulo one into [-1/2,1/2]."""
    if lo > hi:
        raise ValueError((lo, hi))
    floor_lo = lo.numerator // lo.denominator
    floor_hi = hi.numerator // hi.denominator
    if floor_lo != floor_hi:
        raise ValueError("phase interval crosses an integer")
    lo -= floor_lo
    hi -= floor_hi
    if lo > Fraction(1, 2):
        return lo - 1, hi - 1
    if hi <= Fraction(1, 2):
        return lo, hi
    raise ValueError("phase interval crosses the centered cut")


_PHASE_CACHE: dict[tuple[int, int, int, int], CIv] = {}


def phase_interval(lo: Fraction, hi: Fraction) -> CIv:
    lo, hi = centered_interval(lo, hi)
    key = (lo.numerator, lo.denominator, hi.numerator, hi.denominator)
    if key in _PHASE_CACHE:
        return _PHASE_CACHE[key]
    phase_argument = Iv(Iv.frac(2 * lo).lo, Iv.frac(2 * hi).hi)
    angle = PI * phase_argument
    cosine, sine = sincos_interval(angle)
    result = CIv(cosine, sine)
    _PHASE_CACHE[key] = result
    return result


def load_digits() -> str:
    repo = Path(__file__).resolve().parents[2]
    project_repo = repo.parent / "AllMath"
    path = project_repo / "workflows/research/pi/data/pi_digits_1048596.txt"
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_DIGIT_FILE_SHA256
    digits = raw.rstrip(b"\n").decode("ascii")
    assert len(digits) == 1_048_596 and digits.isdigit()
    return digits


DIGITS = load_digits()
DEN = 10**SUFFIX_DIGITS


def orbit_interval(n: int) -> tuple[Fraction, Fraction]:
    block = DIGITS[n : n + SUFFIX_DIGITS]
    if len(block) != SUFFIX_DIGITS:
        raise ValueError(n)
    numerator = int(block)
    return Fraction(numerator, DEN), Fraction(numerator + 1, DEN)


def fejer_square_coefficient(h: int) -> Fraction:
    r = abs(h)
    if r <= Q:
        numerator = 4 * Q**3 + 2 * Q - 6 * Q * r**2 + 3 * r**3 - 3 * r
        return Fraction(numerator, 6 * Q**2)
    if r <= 2 * Q - 2:
        numerator = (2 * Q - r - 1) * (2 * Q - r) * (2 * Q - r + 1)
        return Fraction(numerator, 6 * Q**2)
    return Fraction(0)


BETA = phase_interval(Fraction(1, 2 * Q), Fraction(1, 2 * Q)).re


def alpha(h: int) -> Iv:
    triangular = (
        fejer_square_coefficient(h - 1) + fejer_square_coefficient(h + 1)
    ) / 2
    return Iv.frac(triangular) - BETA * fejer_square_coefficient(h)


def kernel_at(n: int) -> Iv:
    xlo, xhi = orbit_interval(n)
    center = Fraction(2 * A + 1, 2 * Q)
    tlo, thi = xlo - center, xhi - center
    cos_two_pi_t = phase_interval(tlo, thi).re
    sin_pi_t = phase_interval(tlo / 2, thi / 2).im
    sin_pi_qt = phase_interval(Q * tlo / 2, Q * thi / 2).im
    denominator = sin_pi_t.square() * Q
    if denominator.lo <= 0:
        raise ValueError(f"unresolved Fejer denominator at n={n}: {denominator}")
    fejer = sin_pi_qt.square() / denominator
    return (cos_two_pi_t - BETA) * fejer.square()


def ten_valuation(h: int) -> tuple[int, int]:
    valuation = 0
    while h and h % 10 == 0:
        valuation += 1
        h //= 10
    return valuation, h


def endpoint() -> CIv:
    center = Fraction(2 * A + 1, 2 * Q)
    total = CIv.zero()
    for h in range(1, 2 * Q):
        valuation, primitive = ten_valuation(h)
        if valuation == 0:
            continue
        coefficient = phase_interval(-h * center, -h * center) * alpha(h)
        block = CIv.zero()
        for j in range(valuation):
            terminal = orbit_interval(N + j)
            initial = orbit_interval(j)
            block += phase_interval(primitive * terminal[0], primitive * terminal[1])
            block -= phase_interval(primitive * initial[0], primitive * initial[1])
        total += coefficient * block
    return total


def main() -> None:
    # Regression for interval-valued phases: both endpoints must be enclosed.
    wide_phase = phase_interval(Fraction(0), Fraction(1, 10))
    assert wide_phase.re.lo <= 1 <= wide_phase.re.hi
    assert wide_phase.im.lo <= 0 <= wide_phase.im.hi

    kernel_sum = Iv.point(0)
    for n in range(N):
        kernel_sum += kernel_at(n)
    alpha_zero = (Iv.point(1) - BETA) * Fraction(2 * Q**2 + 1, 3 * Q) - Fraction(1, Q)
    boundary = endpoint()
    score = (kernel_sum - alpha_zero * N) / 2 - boundary.re
    threshold = Decimal(47539) / Decimal(2500)

    assert score.lo > threshold
    assert score.hi < Decimal("19.0157")
    assert kernel_sum.lo > Decimal("60.9339")
    assert boundary.re.lo > Decimal("0.0020")

    print("status: PASS (directed-interval experiment; not yet a Lean theorem)")
    print(f"input_digit_file_sha256={EXPECTED_DIGIT_FILE_SHA256}")
    print(f"parameters: q={Q}, A={A}, N={N}, precision={PREC}, taylor_terms={TAYLOR_TERMS}")
    print(f"kernel_sum=[{kernel_sum.lo}, {kernel_sum.hi}]")
    print(f"alpha_zero=[{alpha_zero.lo}, {alpha_zero.hi}]")
    print(f"endpoint_re=[{boundary.re.lo}, {boundary.re.hi}]")
    print(f"primitive_score_re=[{score.lo}, {score.hi}]")
    print(f"strict_threshold={threshold}")
    print(f"certified_margin_lower={dsub(score.lo, threshold)}")
    print(f"phase_intervals_cached={len(_PHASE_CACHE)}")


if __name__ == "__main__":
    main()
