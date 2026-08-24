#!/usr/bin/env python3
"""Experiment: rigorous interval certificate for a selected-BBP core prefix.

Parameters:
    q=100, k=2, Q=10, A=16=aQ+A' with a=1, A'=6,
    c' = 13/20, N=50.

The script uses only Python's standard library.  All BBP partial sums, selected
orbit values, forcings, carries, and target phases are built from exact
fractions.  Trigonometric values are enclosed with outward-rounded Decimal
interval arithmetic.  Pi is enclosed independently through Machin's formula
and alternating arctangent bounds.

The BBP convention is the canonical inclusive T112 convention:
``bbpPartial M`` contains the terms indexed 0 through M.  Consequently the
forcing from time n to n+1 contains exactly the terms 7*n+1 through 7*n+7.

It evaluates the nine-channel expression from the endpoint-free singleton-ray
barrier directly; it does not use target averaging, a diagonal estimate, a
periodic surrogate, or an arbitrary-disk relaxation.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import (
    Context,
    Decimal,
    ROUND_CEILING,
    ROUND_FLOOR,
    getcontext,
)
from fractions import Fraction
from hashlib import sha256
from math import factorial

PREC = 90
TAYLOR_TERMS = 55
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
    def point(x: int | Decimal) -> "Iv":
        d = x if isinstance(x, Decimal) else Decimal(x)
        return Iv(d, d)

    @staticmethod
    def frac(x: Fraction) -> "Iv":
        n = Decimal(x.numerator)
        d = Decimal(x.denominator)
        return Iv(ddiv(n, d, False), ddiv(n, d, True))

    def __neg__(self) -> "Iv":
        return Iv(-self.hi, -self.lo)

    def __add__(self, other: object) -> "Iv":
        o = as_iv(other)
        return Iv(dadd(self.lo, o.lo, False), dadd(self.hi, o.hi, True))

    __radd__ = __add__

    def __sub__(self, other: object) -> "Iv":
        return self + (-as_iv(other))

    def __rsub__(self, other: object) -> "Iv":
        return as_iv(other) - self

    def __mul__(self, other: object) -> "Iv":
        o = as_iv(other)
        lower_products = [
            dmul(a, b, False)
            for a in (self.lo, self.hi)
            for b in (o.lo, o.hi)
        ]
        upper_products = [
            dmul(a, b, True)
            for a in (self.lo, self.hi)
            for b in (o.lo, o.hi)
        ]
        return Iv(min(lower_products), max(upper_products))

    __rmul__ = __mul__

    def width(self) -> Decimal:
        return dsub(self.hi, self.lo, True)


def as_iv(x: object) -> Iv:
    if isinstance(x, Iv):
        return x
    if isinstance(x, Fraction):
        return Iv.frac(x)
    if isinstance(x, Decimal):
        return Iv.point(x)
    if isinstance(x, int):
        return Iv.point(x)
    raise TypeError(type(x))


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
        o = as_civ(other)
        return CIv(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, other: object) -> "CIv":
        return self + (-as_civ(other))

    def __mul__(self, other: object) -> "CIv":
        o = as_civ(other)
        return CIv(
            self.re * o.re - self.im * o.im,
            self.re * o.im + self.im * o.re,
        )

    __rmul__ = __mul__


def as_civ(x: object) -> CIv:
    if isinstance(x, CIv):
        return x
    return CIv(as_iv(x), Iv.point(0))


def atan_inv_bounds(q: int, terms: int) -> tuple[Fraction, Fraction]:
    """Alternating-series enclosure for arctan(1/q)."""
    partial = Fraction(0)
    for r in range(terms):
        term = Fraction(1, (2 * r + 1) * q ** (2 * r + 1))
        partial += term if r % 2 == 0 else -term
    next_magnitude = Fraction(1, (2 * terms + 1) * q ** (2 * terms + 1))
    if terms % 2 == 0:  # the omitted term is positive
        return partial, partial + next_magnitude
    return partial - next_magnitude, partial


def machin_pi_interval(terms: int = 100) -> Iv:
    l5, u5 = atan_inv_bounds(5, terms)
    l239, u239 = atan_inv_bounds(239, terms)
    lower = 16 * l5 - 4 * u239
    upper = 16 * u5 - 4 * l239
    return Iv(Iv.frac(lower).lo, Iv.frac(upper).hi)


PI = machin_pi_interval()


def abs_decimal(x: Decimal) -> Decimal:
    return x.copy_abs()


def pow_up(x: Decimal, n: int) -> Decimal:
    result = Decimal(1)
    base = x
    exponent = n
    while exponent:
        if exponent & 1:
            result = UP.multiply(result, base)
        exponent //= 2
        if exponent:
            base = UP.multiply(base, base)
    return result


def sincos_point(x: Decimal) -> tuple[Iv, Iv]:
    """Taylor enclosure at one exact finite Decimal x, |x| <= pi."""
    X = Iv.point(x)
    X2 = X * X

    cos_value = Iv.point(1)
    cos_term = Iv.point(1)
    for m in range(1, TAYLOR_TERMS + 1):
        cos_term = cos_term * (-X2) * Fraction(1, (2 * m - 1) * (2 * m))
        cos_value = cos_value + cos_term

    sin_value = X
    sin_term = X
    for m in range(1, TAYLOR_TERMS + 1):
        sin_term = sin_term * (-X2) * Fraction(1, (2 * m) * (2 * m + 1))
        sin_value = sin_value + sin_term

    ax = abs_decimal(x)
    # Lagrange bounds for degrees 2M and 2M+1.
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
    cos_value = Iv(
        dsub(cos_value.lo, cos_rem, False),
        dadd(cos_value.hi, cos_rem, True),
    )
    sin_value = Iv(
        dsub(sin_value.lo, sin_rem, False),
        dadd(sin_value.hi, sin_rem, True),
    )
    return cos_value, sin_value


def sincos_interval(x: Iv) -> tuple[Iv, Iv]:
    """Use the lower endpoint and the 1-Lipschitz bounds for sin and cos."""
    cos_value, sin_value = sincos_point(x.lo)
    width = x.width()
    return (
        Iv(dsub(cos_value.lo, width, False), dadd(cos_value.hi, width, True)),
        Iv(dsub(sin_value.lo, width, False), dadd(sin_value.hi, width, True)),
    )


def centered_fraction(x: Fraction) -> Fraction:
    residue = x - (x.numerator // x.denominator)
    if residue > Fraction(1, 2):
        residue -= 1
    return residue


_PHASE_CACHE: dict[tuple[int, int], CIv] = {}


def phase(x: Fraction) -> CIv:
    """Rigorous enclosure of exp(2*pi*i*x)."""
    u = centered_fraction(x)
    key = (u.numerator, u.denominator)
    cached = _PHASE_CACHE.get(key)
    if cached is not None:
        return cached
    angle = PI * (2 * u)
    cosine, sine = sincos_interval(angle)
    value = CIv(cosine, sine)
    _PHASE_CACHE[key] = value
    return value


def bbp_term(m: int) -> Fraction:
    return Fraction(1, 16**m) * (
        Fraction(4, 8 * m + 1)
        - Fraction(2, 8 * m + 4)
        - Fraction(1, 8 * m + 5)
        - Fraction(1, 8 * m + 6)
    )


def exact_selected_data(max_n: int) -> tuple[list[Fraction], list[Fraction], list[int]]:
    """Inclusive-T112 residues plus the exact seven-summand T106 forcing."""
    max_m = 7 * max_n
    partials = [Fraction(0)]
    for m in range(max_m + 1):
        partials.append(partials[-1] + bbp_term(m))

    y: list[Fraction] = []
    for n in range(max_n + 1):
        # partials[M + 1] is the inclusive canonical bbpPartial M.
        q_n = (10**n) * partials[7 * n + 1]
        y.append(q_n - (q_n.numerator // q_n.denominator))

    forcing: list[Fraction] = []
    carries: list[int] = []
    for n in range(max_n):
        f_n = (10 ** (n + 1)) * (
            partials[7 * (n + 1) + 1] - partials[7 * n + 1]
        )
        forcing.append(f_n)
        z = 10 * y[n] + f_n
        b_n = z.numerator // z.denominator
        carries.append(b_n)
        assert y[n + 1] == z - b_n

    return y, forcing, carries


def certify() -> None:
    q = 100
    k = 2
    Q = 10
    A = 16
    a = 1
    A_prime = 6
    N = 50
    c_prime = Fraction(2 * A_prime + 1, 2 * Q)  # 13/20

    y, forcing, b = exact_selected_data(N + k)

    predecessor_mod_10 = "".join(str(x % 10) for x in b[:N])
    predecessor_character_indices = "".join(str((x - a) % 10) for x in b[:N])
    assert b[0] == 1
    assert predecessor_mod_10 == "14159265358979323846264338327950288419716939937510"
    assert predecessor_character_indices == "03048154247868212735153227216849177308605828826409"

    selected_digest_input = "\n".join(
        f"{n}:{value.numerator}/{value.denominator}" for n, value in enumerate(y)
    )
    selected_digest = sha256(selected_digest_input.encode("ascii")).hexdigest()
    assert selected_digest == "7afe5ab16b7dee048a39d83911809ecce7161363bc93afc56361f907c4129882"

    cos_pi_over_q, _ = sincos_interval(PI * Fraction(1, q))
    delta = Iv.point(1) - cos_pi_over_q

    coefficients: dict[int, Iv] = {}
    for ell in range(Q // 2):
        for s in range(1, 10):
            j = 10 * ell + s
            t = q - j
            coefficients[j] = (
                Iv.frac(Fraction(t, 2 * q * q))
                + delta * Fraction(t**3 - t, 6 * q * q)
            )
    assert len(coefficients) == 45

    R = CIv.zero()
    summands: list[CIv] = []
    for n in range(N):
        inner = CIv.zero()
        for s in range(1, 10):
            polynomial = CIv.zero()
            for ell in range(Q // 2):
                j = 10 * ell + s
                polynomial += phase(ell * (y[n + 1] - c_prime)) * coefficients[j]
            G_s = phase(Fraction(s, 10) * (y[n + 1] - c_prime)) * polynomial
            predecessor = phase(Fraction(s * (b[n] - a), 10))
            inner += predecessor * G_s
        summand = -(phase(y[n + k]) * inner)
        summands.append(summand)
        R += summand

    alpha_0 = delta * Fraction(2 * q * q + 1, 3 * q) - Fraction(1, q)
    endpoint_budget = (
        delta * Fraction(q * (q - 1), 18) - Fraction(k, 2) * alpha_0
    )

    normalized_core = (-R.re) * Fraction(q, N)
    optimistic_c_ceiling = alpha_0 * Fraction(q, 2)
    main_defect = (-R.re) * Fraction(2, N)
    main_margin = main_defect - alpha_0
    budgeted_defect = main_defect + endpoint_budget * Fraction(4, N)
    budgeted_margin = budgeted_defect - alpha_0
    endpoint_adjusted_c_ceiling = (alpha_0 - endpoint_budget * Fraction(4, N)) * Fraction(q, 2)
    zero_mode_gap = normalized_core - optimistic_c_ceiling
    endpoint_gap = normalized_core - endpoint_adjusted_c_ceiling
    pointwise_n39 = summands[39]
    pointwise_n39_required_c = (-pointwise_n39.re) * q

    # Strict, human-readable claims used in the accompanying note.
    assert R.re.hi < Decimal("-0.677629649371418980")
    assert normalized_core.lo > Decimal("1.355259298742837961")
    assert optimistic_c_ceiling.hi < Decimal("1.144881020833854739")
    assert main_margin.lo > Decimal("0.004207565558179664")
    assert budgeted_margin.lo > Decimal("0.024087099832656988")
    assert pointwise_n39.re.hi < Decimal("-0.313807762365723917")
    assert endpoint_adjusted_c_ceiling.hi < Decimal("0.150904307109988519")
    assert zero_mode_gap.lo > Decimal("0.210378277908983222")
    assert endpoint_gap.lo > Decimal("1.204354991632849442")
    assert (100 * y[39]).numerator // (100 * y[39]).denominator == A

    print("status: experiment; canonical inclusive T112 convention")
    print("parameters: q=100, k=2, Q=10, A=16, a=1, A'=6, c'=13/20, N=50")
    print(f"b_0={b[0]}")
    print(f"b_n mod 10 (n=0..49): {predecessor_mod_10}")
    print(f"(b_n-a) mod 10:        {predecessor_character_indices}")
    print(f"SHA256(y_0..y_52 reduced numerator/denominator list): {selected_digest}")
    print(f"Re R interval: [{R.re.lo}, {R.re.hi}]")
    print(f"Im R interval: [{R.im.lo}, {R.im.hi}]")
    print(f"-q Re(R)/N interval: [{normalized_core.lo}, {normalized_core.hi}]")
    print(f"alpha_0 interval: [{alpha_0.lo}, {alpha_0.hi}]")
    print(f"q alpha_0 / 2 interval: [{optimistic_c_ceiling.lo}, {optimistic_c_ceiling.hi}]")
    print(f"endpoint-adjusted C ceiling interval: [{endpoint_adjusted_c_ceiling.lo}, {endpoint_adjusted_c_ceiling.hi}]")
    print(f"zero-mode-only C gap interval: [{zero_mode_gap.lo}, {zero_mode_gap.hi}]")
    print(f"endpoint-adjusted C gap interval: [{endpoint_gap.lo}, {endpoint_gap.hi}]")
    print(f"floor(100*y_39)={((100 * y[39]).numerator // (100 * y[39]).denominator)}")
    print(f"Re n=39 summand interval: [{pointwise_n39.re.lo}, {pointwise_n39.re.hi}]")
    print(f"pointwise n=39 required C interval: [{pointwise_n39_required_c.lo}, {pointwise_n39_required_c.hi}]")
    print(f"endpoint E interval: [{endpoint_budget.lo}, {endpoint_budget.hi}]")
    print(f"(-2 Re(R)/N)-alpha_0: [{main_margin.lo}, {main_margin.hi}]")
    print(f"(-2 Re(R)/N+4E/N)-alpha_0: [{budgeted_margin.lo}, {budgeted_margin.hi}]")
    print(f"phase evaluations cached: {len(_PHASE_CACHE)}")


if __name__ == "__main__":
    certify()
