#!/usr/bin/env python3
"""Adversarial exact replay for the fixed-denominator Pade branch.

This is intentionally independent of fixed_denominator_pade_attack_check.py:
continued fractions are evaluated from the bottom, the CRT is assembled from
the local congruences, and finite approximation-quality checkpoints use exact
rational Machin brackets for pi.
"""

from fractions import Fraction
from math import gcd, isqrt, lcm


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def bottom_up_gauss(p: int, q: int, depth: int) -> Fraction:
    """Evaluate p/(q+p^2/(3q+(2p)^2/(5q+...))) from its tail."""
    tail = Fraction(0)
    for level in range(depth, 1, -1):
        tail = Fraction((level - 1) ** 2 * p * p,
                        (2 * level - 1) * q + tail)
    return Fraction(p, q + tail)


def all_pi_shadows(last_depth: int) -> list[Fraction]:
    """Return 4 times the Gauss arctan(1) convergents through last_depth."""
    p_nm2, p_nm1 = 1, 0
    q_nm2, q_nm1 = 0, 1
    shadows: list[Fraction] = []
    for n in range(1, last_depth + 1):
        a_n = 1 if n == 1 else (n - 1) ** 2
        b_n = 2 * n - 1
        p_n = b_n * p_nm1 + a_n * p_nm2
        q_n = b_n * q_nm1 + a_n * q_nm2
        shadows.append(Fraction(4 * p_n, q_n))
        p_nm2, p_nm1 = p_nm1, p_n
        q_nm2, q_nm1 = q_nm1, q_n
    return shadows


def prime_by_trial_division(n: int) -> bool:
    if n < 2:
        return False
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            return False
    return True


def order_and_first_hit(modulus: int) -> tuple[int, int]:
    require(gcd(modulus, 10) == 1, "order requires a unit")
    residue = 1
    first = 0
    for exponent in range(1, modulus + 1):
        residue = residue * 10 % modulus
        if residue == 16 % modulus and first == 0:
            first = exponent
        if residue == 1:
            return exponent, first
    raise AssertionError("order search exhausted")


def merge_congruence(a: int, m: int, b: int, n: int) -> tuple[int, int]:
    """Small transparent generalized CRT merge by stepping one progression."""
    period = lcm(m, n)
    for candidate in range(a % m, period, m):
        if candidate % n == b % n:
            return candidate, period
    raise AssertionError("incompatible congruences")


def alternating_arctan_bounds(inv: int, terms: int) -> tuple[Fraction, Fraction]:
    """Bounds for atan(1/inv); terms must be even, so the sum is lower."""
    require(terms > 0 and terms % 2 == 0, "use a positive even term count")
    x = Fraction(1, inv)
    partial = sum(
        ((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
         for k in range(terms)),
        Fraction(0),
    )
    next_positive = x ** (2 * terms + 1) / (2 * terms + 1)
    return partial, partial + next_positive


def machin_pi_bounds(terms: int = 700) -> tuple[Fraction, Fraction]:
    """Use pi = 16 atan(1/5) - 4 atan(1/239)."""
    low5, high5 = alternating_arctan_bounds(5, terms)
    low239, high239 = alternating_arctan_bounds(239, terms)
    return 16 * low5 - 4 * high239, 16 * high5 - 4 * low239


def error_bounds(
    approximation: Fraction, pi_low: Fraction, pi_high: Fraction
) -> tuple[Fraction, Fraction]:
    if approximation < pi_low:
        return pi_low - approximation, pi_high - approximation
    if approximation > pi_high:
        return approximation - pi_high, approximation - pi_low
    raise AssertionError("pi bracket is too coarse to orient the approximation")


# The first convergents and the EGF coefficient recurrence are independent.
shadows = all_pi_shadows(1_000)
require(
    shadows[:6]
    == [Fraction(4), Fraction(3), Fraction(19, 6), Fraction(160, 51),
        Fraction(1744, 555), Fraction(644, 205)],
    "initial Gauss shadows",
)

# If F=(1-2x-x^2)^(-1/2), then (1-2x-x^2)F'=(1+x)F.
# Coefficient extraction gives Q_(k+1)=(2k+1)Q_k+k^2 Q_(k-1).
q_values = [1, 1]
for k in range(1, 7):
    q_values.append((2 * k + 1) * q_values[-1] + k * k * q_values[-2])
require(q_values == [1, 1, 4, 24, 204, 2220, 29520, 463680],
        "EGF/continuant recurrence")

# Recheck the finite 5-adic windows and the omitted explicit small-prime
# obstruction at depths 110..114.  The factor 37 divides every denominator
# in the latter window, while <10> mod 37={1,10,26}, which omits 16.
windows: list[tuple[int, int]] = []
window_start = 0
for n, value in enumerate(shadows[:200], start=1):
    eligible = value.denominator % 5 != 0
    if eligible and window_start == 0:
        window_start = n
    if not eligible and window_start:
        windows.append((window_start, n - 1))
        window_start = 0
if window_start:
    windows.append((window_start, 200))
require(windows == [(1, 4), (20, 24), (110, 114)], "5-adic windows")
require(all(shadows[n - 1].denominator % 11 == 0 for n in range(20, 25)),
        "11 obstruction in the middle window")
require(all(shadows[n - 1].denominator % 37 == 0 for n in range(110, 115)),
        "37 obstruction in the last window")
require(order_and_first_hit(11) == (2, 0), "16 is not a power of 10 mod 11")
require(order_and_first_hit(37) == (3, 0), "16 is not a power of 10 mod 37")

# Evaluate the Euler depth-six shadow by a different bottom-up algorithm.
a6 = 4 * (bottom_up_gauss(1, 2, 6) + bottom_up_gauss(1, 3, 6))
require(a6 == Fraction(774_756_220, 246_612_571), "Euler depth-six shadow")
factors = (19, 641, 20_249)
require(all(prime_by_trial_division(p) for p in factors), "prime factors")
require(a6.denominator == factors[0] * factors[1] * factors[2], "factorization")

local = [(14, 18), (10, 32), (1472, 2531)]
for prime, (first, order) in zip(factors, local):
    got_order, got_first = order_and_first_hit(prime)
    require((got_first, got_order) == (first, order), f"local data mod {prime}")

crt_a, crt_m = local[0]
for congruence in local[1:]:
    crt_a, crt_m = merge_congruence(crt_a, crt_m, *congruence)
require((crt_a, crt_m) == (684_842, 728_928), "CRT class")
require(pow(10, crt_a, a6.denominator) == 16, "fixed-sixteen divisibility")

# Rebuild the report's exact lower bracket for the depth-six error.
def atan_partial(inv: int, terms: int) -> Fraction:
    x = Fraction(1, inv)
    return sum(
        ((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
         for k in range(terms)),
        Fraction(0),
    )


lower_pi_20 = 4 * (atan_partial(2, 20) + atan_partial(3, 20))
require(a6 < lower_pi_20, "depth-six orientation")
require(lower_pi_20 - a6 > Fraction(1, 11_560_000), "depth-six error")
require((10**crt_a - 16) * (lower_pi_20 - a6) > 10 ** (crt_a - 8),
        "large Archimedean transfer term")

# Adversarial finite quality checkpoints.  They do not establish an
# asymptotic limit, but they make the unsupported 0.9058 limit unsafe to use.
pi_low, pi_high = machin_pi_bounds()

e25_low, e25_high = error_bounds(shadows[24], pi_low, pi_high)
d25 = shadows[24].denominator
# 0.905 < M_25 < 0.906, with M=-log(error)/log(d).
require(e25_high**200 * d25**181 < 1, "M_25 > 0.905")
require(e25_low**500 * d25**453 > 1, "M_25 < 0.906")

e100_low, _ = error_bounds(shadows[99], pi_low, pi_high)
d100 = shadows[99].denominator
require(e100_low**20 * d100**17 > 1, "M_100 < 0.85")

e200_low, _ = error_bounds(shadows[199], pi_low, pi_high)
d200 = shadows[199].denominator
require(e200_low**5 * d200**4 > 1, "M_200 < 0.8")

e1000_low, _ = error_bounds(shadows[999], pi_low, pi_high)
d1000 = shadows[999].denominator
require(e1000_low**5 * d1000**4 > 1, "M_1000 < 0.8")

print(
    "PASS (adversarial replay): finite Euler/CRT/error claims hold; exact "
    "quality checkpoints place M_25 in (0.905,0.906), M_100<0.85, and "
    "M_200,M_1000<0.8, so the quoted 0.9058 asymptotic is not certified"
)
