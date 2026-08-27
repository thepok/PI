#!/usr/bin/env python3
"""Exact finite replay for gauss_exceptional_gcd_upper_bound_attack.md.

All PASS assertions use integer or rational arithmetic.  The last two-adic
line is explicitly an experiment and is not used by any proved reduction.
"""

from fractions import Fraction
from functools import cache
from math import comb, factorial, gcd, isqrt


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [prime for prime in range(2, limit + 1) if sieve[prime]]


def valuation_integer(value: int, prime: int) -> int:
    require(value != 0, "valuation of zero was requested")
    value = abs(value)
    if prime == 2:
        return (value & -value).bit_length() - 1
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def valuation_factorial(n: int, prime: int) -> int:
    exponent = 0
    while n:
        n //= prime
        exponent += n
    return exponent


def floor_log(n: int, prime: int) -> int:
    exponent = 0
    while n >= prime:
        n //= prime
        exponent += 1
    return exponent


@cache
def u_mod_closed(n: int, prime: int) -> int:
    """U_n=Q_n/n! modulo an odd prime, from its binomial sum."""

    inverse_two = pow(2, -1, prime)
    total = 0
    inverse_two_power = 1
    for k in range(n // 2 + 1):
        total += comb(n, 2 * k) * comb(2 * k, k) * inverse_two_power
        inverse_two_power = inverse_two_power * inverse_two % prime
    return total % prime


@cache
def u_small_table(prime: int) -> tuple[int, ...]:
    """The prime-integral coefficients U_0,...,U_(prime-1)."""

    values = [1, 1]
    for n in range(2, prime):
        values.append(
            ((2 * n - 1) * values[-1] + (n - 1) * values[-2])
            * pow(n, -1, prime)
            % prime
        )
    return tuple(values[:prime])


@cache
def v_mod_small(n: int, prime: int) -> int:
    """V_n=P_n/n! modulo prime when n<prime."""

    require(n < prime, "V_n denominator must be a prime-adic unit")
    u_values = u_small_table(prime)
    return sum(
        u_values[a]
        * u_values[n - 1 - a]
        * pow(n - a, -1, prime)
        for a in range(n)
    ) % prime


LAST = 2_500
P = [0] * (LAST + 1)
Q = [0] * (LAST + 1)
P[0], P[1] = 0, 1
Q[0], Q[1] = 1, 1
for n in range(2, LAST + 1):
    P[n] = (2 * n - 1) * P[n - 1] + (n - 1) ** 2 * P[n - 2]
    Q[n] = (2 * n - 1) * Q[n - 1] + (n - 1) ** 2 * Q[n - 2]


# The normalized determinant is exact over Q.
for n in range(1, 151):
    U_n = Fraction(Q[n], factorial(n))
    U_previous = Fraction(Q[n - 1], factorial(n - 1))
    V_n = Fraction(P[n], factorial(n))
    V_previous = Fraction(P[n - 1], factorial(n - 1))
    require(
        V_n * U_previous - V_previous * U_n
        == Fraction((-1) ** (n - 1), n),
        f"normalized determinant at n={n}",
    )


# For odd ell, the exact exceptional exponent is
# r+min(v_ell(V_n),v_ell(U_n)); the determinant bounds it by
# r+r'-v_ell(n).  Check both identities directly from P_n,Q_n.
primes = primes_through(LAST)
for n in range(2, 501):
    g_n = gcd(4 * P[n], Q[n])
    for ell in primes:
        if ell == 2 or ell > n:
            continue
        r = floor_log(n, ell)
        r_previous = floor_log(n - 1, ell)
        factorial_exponent = valuation_factorial(n, ell)
        exceptional_exponent = (
            valuation_integer(g_n, ell) - factorial_exponent + r
        )
        u_valuation = valuation_integer(Q[n], ell) - factorial_exponent
        v_valuation = valuation_integer(P[n], ell) - factorial_exponent
        require(
            exceptional_exponent == r + min(u_valuation, v_valuation),
            f"normalized exceptional exponent at n={n}, ell={ell}",
        )
        require(
            exceptional_exponent
            <= r + r_previous - valuation_integer(n, ell),
            f"determinant exponent bound at n={n}, ell={ell}",
        )


# The Frobenius factorization gives the Lucas product U_(a ell+b)=U_a U_b.
# This finite replay uses the independent binomial coefficient formula.
for ell in [prime for prime in primes_through(199) if prime != 2]:
    u_values = u_small_table(ell)
    require(
        u_values[ell - 1] == (-1) ** ((ell - 1) // 2) % ell,
        f"unit terminal coefficient for ell={ell}",
    )
    for a in range(6):
        sample_digits = sorted(
            {0, 1, 2, ell // 3, ell // 2, ell - 2, ell - 1}
        )
        for b in sample_digits:
            require(
                u_mod_closed(a * ell + b, ell)
                == u_mod_closed(a, ell) * u_values[b] % ell,
                f"Lucas product for ell={ell}, a={a}, b={b}",
            )


# If ell>sqrt(n), n=a ell+s, then ell enters E_n exactly when
# U_s V_a=0 mod ell.  Moreover its exceptional exponent is at most two.
# Check every such pair in a substantial exact finite box.
large_pair_count = 0
large_exception_count = 0
for n in range(2, 1_001):
    g_n = gcd(4 * P[n], Q[n])
    for ell in primes:
        if ell == 2 or ell * ell <= n or ell >= n:
            continue
        a, s = divmod(n, ell)
        require(a < ell, f"two-digit range at n={n}, ell={ell}")
        r = floor_log(n, ell)
        exceptional_exponent = (
            valuation_integer(g_n, ell)
            - valuation_factorial(n, ell)
            + r
        )
        zero_condition = (
            u_small_table(ell)[s] * v_mod_small(a, ell) % ell == 0
        )
        require(
            (exceptional_exponent >= 1) == zero_condition,
            f"large-prime zero criterion at n={n}, ell={ell}",
        )
        require(
            exceptional_exponent <= 2,
            f"large-prime exponent at n={n}, ell={ell}",
        )
        large_pair_count += 1
        large_exception_count += exceptional_exponent >= 1


# Exponent two really occurs; replacing the upper bound two by one is false.
for n, ell in [(107, 73), (166, 131)]:
    exponent = (
        valuation_integer(gcd(4 * P[n], Q[n]), ell)
        - valuation_factorial(n, ell)
        + floor_log(n, ell)
    )
    require(exponent == 2, f"large-prime exponent-two witness ({n},{ell})")


# The V_a branch is also genuine and creates complete depth blocks.  Here
# 19 divides V_3=P_3/3!, so it enters at every n=3*19+s in this block.
require(v_mod_small(3, 19) == 0, "V_3 vanishes modulo 19")
require(u_small_table(19)[3] != 0, "U_3 does not vanish modulo 19")
for n in range(57, 76):
    exponent = (
        valuation_integer(gcd(4 * P[n], Q[n]), 19)
        - valuation_factorial(n, 19)
        + floor_log(n, 19)
    )
    require(exponent >= 1, f"V_3 block witness at n={n}")


# A separate finite experiment records the simple observed 2-adic pattern.
# It is deliberately absent from every PASS theorem above.
two_adic_pattern_last = 10_000
q_previous, q_current = 1, 1
two_adic_pattern_ok = True
for n in range(2, two_adic_pattern_last + 1):
    q_next = (2 * n - 1) * q_current + (n - 1) ** 2 * q_previous
    q_previous, q_current = q_current, q_next
    observed_extra = valuation_integer(q_current, 2) - n // 2
    if n % 4 in (0, 1):
        predicted_extra = 0
    elif n % 4 == 2:
        predicted_extra = 1
    else:
        predicted_extra = valuation_integer(n + 1, 2)
    two_adic_pattern_ok &= observed_extra == predicted_extra
require(two_adic_pattern_ok, "finite two-adic pattern")


print(
    "PASS: normalized determinant/exponent bound, Lucas product, and exact "
    f"large-prime zero criterion on {large_pair_count} pairs "
    f"({large_exception_count} exceptional), including exponent-two and "
    "V_a-block witnesses"
)
print(
    "EXPERIMENT: v_2(Q_n)-floor(n/2) follows the stated mod-4 pattern "
    f"through n={two_adic_pattern_last}; no all-n proof is claimed"
)
