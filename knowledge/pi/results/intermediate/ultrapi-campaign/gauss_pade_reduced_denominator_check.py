#!/usr/bin/env python3
"""Exact finite replay for gauss_pade_reduced_denominator_audit.md.

The recurrence, closed forms, determinants, canonical gcd divisor, and
prime-shift congruences use integers only.  Decimal rate summaries at the end
are explicitly experiments; they are not used to certify an asymptotic.
"""

from math import factorial, gcd, lcm, log, sqrt


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def odd_part(value: int) -> int:
    while value > 0 and value % 2 == 0:
        value //= 2
    return value


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


LAST = 2_500
GCD_LAST = 1_200
P = [0] * (LAST + 1)
Q = [0] * (LAST + 1)
g_values = [0] * (GCD_LAST + 1)
P[0], Q[0] = 0, 1
P[1], Q[1] = 1, 1
for n in range(2, LAST + 1):
    P[n] = (2 * n - 1) * P[n - 1] + (n - 1) ** 2 * P[n - 2]
    Q[n] = (2 * n - 1) * Q[n - 1] + (n - 1) ** 2 * Q[n - 2]
for n in range(1, GCD_LAST + 1):
    g_values[n] = gcd(4 * P[n], Q[n])


# The first Gauss--Lambert shadows are 4 P_n / Q_n.
first = []
for n in range(1, 7):
    common = g_values[n]
    first.append((4 * P[n] // common, Q[n] // common))
require(
    first == [(4, 1), (3, 1), (19, 6), (160, 51), (1744, 555), (644, 205)],
    "initial reduced Gauss--Lambert approximants",
)


# Closed coefficient formula for F(x)=(1-2x-x^2)^(-1/2):
# Q_n = sum_k n!^2/(2^k k!^2 (n-2k)!).
for n in range(0, 31):
    closed_q = sum(
        factorial(n) ** 2
        // (2**k * factorial(k) ** 2 * factorial(n - 2 * k))
        for k in range(n // 2 + 1)
    )
    require(closed_q == Q[n], f"closed Q formula at n={n}")


# If G=sum P_n x^n/n! and F=sum Q_n x^n/n!, then
# G=F*integral(F), hence this exact convolution.
for n in range(1, 31):
    closed_p = sum(
        # Here a+b=n-1 and n!/(a!(b+1)!)=binomial(n,a).
        factorial(n)
        // (factorial(a) * factorial(n - a))
        * Q[a]
        * Q[n - 1 - a]
        for a in range(n)
    )
    require(closed_p == P[n], f"closed P convolution at n={n}")


# Consecutive continuants have a completely explicit determinant.
for n in range(1, 401):
    determinant = P[n] * Q[n - 1] - P[n - 1] * Q[n]
    require(
        determinant == (-1) ** (n - 1) * factorial(n - 1) ** 2,
        f"continuant determinant at n={n}",
    )


# H_n is the canonical, rigorously explained common divisor.  This loop is
# finite evidence in the checker; the report gives the all-n coefficient proof.
running_factorial = 1
running_lcm = 1
exceptional: dict[int, int] = {}
checkpoint_depths = {7, 20, 25, 30, 50, 72, 100, 200, 500, 1_000, 1_500, 2_000}
for n in range(1, LAST + 1):
    running_factorial *= n
    running_lcm = lcm(running_lcm, n)
    H_n = 2 ** (n // 2) * odd_part(running_factorial // running_lcm)
    if n <= GCD_LAST:
        g_n = g_values[n]
        require(g_n % H_n == 0, f"canonical gcd divisor at n={n}")
    elif n in checkpoint_depths:
        g_n = gcd(4 * P[n], Q[n])
        require(g_n % H_n == 0, f"high-depth canonical divisor at n={n}")
    else:
        continue
    if n in checkpoint_depths:
        exceptional[n] = g_n // H_n

require(
    exceptional
    == {
        7: 24,
        20: 15,
        25: 3,
        30: 46,
        50: 2,
        72: 16_473,
        100: 5,
        200: 9,
        500: 255,
        1_000: 1,
        1_500: 5_869_947,
        2_000: 203_985_322_053,
    },
    "exceptional-factor checkpoints",
)


# Prime-shift congruence.  For odd p, Q_p=Q_(p+1)=0 mod p and
# P_(p+s)=P_p Q_s mod p.  Thus a prime p>n/2 is an exceptional common
# divisor at n=p+s exactly when p divides the earlier Q_s.
for prime in [p for p in primes_through(199) if p != 2]:
    require(Q[prime] % prime == 0, f"Q_p mod p for p={prime}")
    require(Q[prime + 1] % prime == 0, f"Q_(p+1) mod p for p={prime}")
    require(P[prime] % prime != 0, f"P_p is a unit mod p for p={prime}")
    for s in range(prime):
        require(Q[prime + s] % prime == 0, f"shifted Q for p={prime}, s={s}")
        require(
            (P[prime + s] - P[prime] * Q[s]) % prime == 0,
            f"shifted P for p={prime}, s={s}",
        )

# The periodic shift itself lifts to prime-power moduli.  Unlike the mod-p
# case, P_q need not be a unit, so this deliberately does not assert an iff
# criterion for the exact p-adic valuation.
prime_powers: set[int] = set()
for prime in primes_through(199):
    power = prime
    while power <= 199:
        prime_powers.add(power)
        power *= prime
for modulus in sorted(prime_powers):
    require(Q[modulus] % modulus == 0, f"Q_q mod q for q={modulus}")
    require(Q[modulus + 1] % modulus == 0, f"Q_(q+1) mod q for q={modulus}")
    for s in range(modulus):
        require(Q[modulus + s] % modulus == 0, f"shifted Q mod q={modulus}")
        require(
            (P[modulus + s] - P[modulus] * Q[s]) % modulus == 0,
            f"shifted P mod q={modulus}, s={s}",
        )

require(Q[7] == 463_680 and Q[7] % 23 == 0, "n=30, p=23 exception")
require(g_values[30] % 23 == 0, "23 enters the n=30 gcd")


# Constants forced by the analytic error and canonical divisor.  These are
# numerical presentations of exact logarithmic expressions, not proofs of a
# limit for the reduced denominator.
alpha = 1 + sqrt(2)
error_rate = 2 * log(alpha)
canonical_denominator_rate = 1 + log(alpha) + log(2) / 2
canonical_quality = error_rate / canonical_denominator_rate
route_threshold = canonical_denominator_rate - error_rate
require(0.7911979206 < canonical_quality < 0.7911979207, "quality constant")
require(0.4652000032 < route_threshold < 0.4652000033, "exception threshold")


# A bounded experiment: the normalized exceptional factor is very small at
# these depths.  This does not imply log(E_n)=o(n), nor even the weaker bound
# needed by the fixed-denominator transfer.
running_factorial = 1
running_lcm = 1
max_rates = {100: (0.0, 0), 500: (0.0, 0), 1_000: (0.0, 0)}
for n in range(1, GCD_LAST + 1):
    running_factorial *= n
    running_lcm = lcm(running_lcm, n)
    H_n = 2 ** (n // 2) * odd_part(running_factorial // running_lcm)
    E_n = g_values[n] // H_n
    rate = log(E_n) / n
    for lower in max_rates:
        if n >= lower and rate > max_rates[lower][0]:
            max_rates[lower] = (rate, n)

require(max_rates[100][0] < 0.138, "finite exceptional rate from n=100")
require(max_rates[500][0] < 0.056, "finite exceptional rate from n=500")
require(max_rates[1_000][0] < 0.030, "finite exceptional rate from n=1000")

print(
    "PASS: exact recurrences/closed forms/determinants, canonical gcd divisor "
    "through n=1200 plus high-depth checkpoints, prime-power shifts, and "
    "finite rate audit"
)
print(
    "EXPERIMENT: max log(E_n)/n on the checked tails = "
    + ", ".join(
        f"n>={lower}: {rate:.12f} (at {where})"
        for lower, (rate, where) in max_rates.items()
    )
)
