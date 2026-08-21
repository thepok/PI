#!/usr/bin/env python3
"""Independent exact replay of the odd-prime claims in the Gauss gcd note.

This checker deliberately does not import the primary checker.  It uses exact
integers/Fractions, builds the Frobenius polynomial directly, and reconstructs
the exceptional factor itself.  Finite replay is an experiment, not a proof of
an asymptotic statement.
"""

from fractions import Fraction
from math import comb, factorial, gcd, isqrt, lcm


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def v_int(value: int, prime: int) -> int:
    require(value != 0, "valuation of zero")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def v_fraction(value: Fraction, prime: int) -> int:
    return v_int(value.numerator, prime) - v_int(value.denominator, prime)


def floor_log(n: int, prime: int) -> int:
    require(n >= 1, "floor_log domain")
    exponent = 0
    while n >= prime:
        n //= prime
        exponent += 1
    return exponent


def fraction_mod(value: Fraction, prime: int) -> int:
    require(value.denominator % prime, "non-integral modular reduction")
    return value.numerator * pow(value.denominator, -1, prime) % prime


def u_binomial(n: int) -> Fraction:
    return sum(
        (Fraction(1, 2) ** k) * comb(n, 2 * k) * comb(2 * k, k)
        for k in range(n // 2 + 1)
    )


def u_mod(n: int, prime: int) -> int:
    inverse_two = pow(2, -1, prime)
    return sum(
        comb(n, 2 * k) * comb(2 * k, k) * pow(inverse_two, k, prime)
        for k in range(n // 2 + 1)
    ) % prime


def poly_multiply(left: list[int], right: list[int], prime: int) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = (result[i + j] + a * b) % prime
    return result


def poly_power(base: list[int], exponent: int, prime: int) -> list[int]:
    result = [1]
    while exponent:
        if exponent & 1:
            result = poly_multiply(result, base, prime)
        base = poly_multiply(base, base, prime)
        exponent //= 2
    return result


DEPTH = 1_200
P = [0] * (DEPTH + 1)
Q = [0] * (DEPTH + 1)
P[0], P[1] = 0, 1
Q[0], Q[1] = 1, 1
for n in range(2, DEPTH + 1):
    P[n] = (2 * n - 1) * P[n - 1] + (n - 1) ** 2 * P[n - 2]
    Q[n] = (2 * n - 1) * Q[n - 1] + (n - 1) ** 2 * Q[n - 2]

factorials = [factorial(n) for n in range(DEPTH + 1)]
lcms = [1] * (DEPTH + 1)
for n in range(1, DEPTH + 1):
    lcms[n] = lcm(lcms[n - 1], n)


def odd(value: int) -> int:
    return value // (value & -value)


def exceptional_factor(n: int) -> int:
    canonical = 2 ** (n // 2) * odd(factorials[n] // lcms[n])
    common = gcd(4 * P[n], Q[n])
    require(common % canonical == 0, f"E_{n} is not integral")
    return common // canonical


# Equations (3), (9)--(15): replay the normalization, coefficient formulas,
# determinant, exact exceptional valuation, and every valuation inequality.
odd_primes = [p for p in primes_through(DEPTH + 100) if p != 2]
for n in range(1, 181):
    U = Fraction(Q[n], factorials[n])
    V = Fraction(P[n], factorials[n])
    require(U == u_binomial(n), f"binomial U at n={n}")
    convolution = sum(
        Fraction(Q[i], factorials[i])
        * Fraction(Q[n - 1 - i], factorials[n - 1 - i])
        / (n - i)
        for i in range(n)
    )
    require(V == convolution, f"convolution V at n={n}")
    determinant = V * Fraction(Q[n - 1], factorials[n - 1])
    determinant -= Fraction(P[n - 1], factorials[n - 1]) * U
    require(
        determinant == Fraction((-1) ** (n - 1), n),
        f"determinant at n={n}",
    )

for n in range(2, 701):
    E = exceptional_factor(n)
    U = Fraction(Q[n], factorials[n])
    V = Fraction(P[n], factorials[n])
    for prime in odd_primes:
        if prime > n + 50:
            break
        r = floor_log(n, prime)
        r_previous = floor_log(n - 1, prime)
        exponent = v_int(E, prime) if E % prime == 0 else 0
        require(
            v_fraction(V, prime) >= -r,
            f"V valuation floor at n={n}, p={prime}",
        )
        require(
            exponent == r + min(v_fraction(U, prime), v_fraction(V, prime)),
            f"exact E valuation at n={n}, p={prime}",
        )
        require(
            exponent <= r + r_previous - v_int(n, prime),
            f"determinant bound at n={n}, p={prime}",
        )
        if prime >= n:
            require(exponent == 0, f"prime boundary at n={n}, p={prime}")


# Equations (17)--(19), independently via D(x)^((p-1)/2), plus the exact
# identification 2^n U_n=T_n(1,2,2) used to match Noe (2006), equation (13).
for n in range(0, 101):
    generalized_trinomial = sum(
        comb(n, 2 * k) * comb(2 * k, k) * 2 ** (n - k)
        for k in range(n // 2 + 1)
    )
    require(
        Fraction(generalized_trinomial, 2**n) == u_binomial(n),
        f"Noe normalization at n={n}",
    )

for prime in [p for p in primes_through(101) if p != 2]:
    frobenius_factor = poly_power(
        [1, -2 % prime, -1 % prime], (prime - 1) // 2, prime
    )
    require(len(frobenius_factor) == prime, f"factor degree at p={prime}")
    for digit in range(prime):
        require(
            frobenius_factor[digit] == u_mod(digit, prime),
            f"Frobenius low coefficient at p={prime}, d={digit}",
        )
    require(
        frobenius_factor[-1] == (-1) ** ((prime - 1) // 2) % prime,
        f"terminal unit at p={prime}",
    )
    for quotient in range(0, 7):
        for digit in range(prime):
            require(
                u_mod(quotient * prime + digit, prime)
                == u_mod(quotient, prime) * u_mod(digit, prime) % prime,
                f"one-digit Lucas at p={prime}, c={quotient}, d={digit}",
            )


# Equations (20)--(28): all strict large-prime pairs through depth 1200.
large_pairs = 0
large_exceptions = 0
for n in range(2, DEPTH + 1):
    E = exceptional_factor(n)
    for prime in odd_primes:
        if prime >= n:
            break
        if prime * prime <= n:
            continue
        a, s = divmod(n, prime)
        require(1 <= a < prime and 0 <= s < prime, "large-prime digits")
        U_s = Fraction(Q[s], factorials[s])
        V_a = Fraction(P[a], factorials[a])
        lhs_22 = fraction_mod(prime * Fraction(P[n], factorials[n]), prime)
        rhs_22 = (
            fraction_mod(U_s, prime)
            * ((-1) ** ((prime - 1) // 2) % prime)
            * fraction_mod(V_a, prime)
        ) % prime
        require(lhs_22 == rhs_22, f"survivor identity at n={n}, p={prime}")
        exponent = v_int(E, prime) if E % prime == 0 else 0
        zero = fraction_mod(U_s * V_a, prime) == 0
        require((exponent >= 1) == zero, f"iff (7) at n={n}, p={prime}")
        require(
            zero == (Q[s] % prime == 0 or P[a] % prime == 0),
            f"integer mechanisms at n={n}, p={prime}",
        )
        require(exponent <= 2, f"large exponent at n={n}, p={prime}")
        large_pairs += 1
        large_exceptions += exponent >= 1

require(large_pairs == 118_613, f"strict pair count: {large_pairs}")
require(large_exceptions == 1_468, f"exception count: {large_exceptions}")
require(v_int(exceptional_factor(107), 73) == 2, "(107,73) exponent two")
require(v_int(exceptional_factor(166), 131) == 2, "(166,131) exponent two")
require(P[3] == 19, "P_3")
for n in range(57, 76):
    require(exceptional_factor(n) % 19 == 0, f"P_3 block n={n}")


# Equations (29)--(32): an exact finite product decomposition.  The
# asymptotic equivalence (33) is proved logically in the audit, not inferred
# from these samples.
decomposition_depths = 0
for n in range(2, 801):
    E_odd = odd(exceptional_factor(n))
    small_part = 1
    large_part = 1
    zero_product = 1
    remainder = E_odd
    for prime in odd_primes:
        if prime > n:
            break
        exponent = 0
        while remainder % prime == 0:
            remainder //= prime
            exponent += 1
        if prime * prime <= n:
            require(
                exponent <= 2 * floor_log(n, prime),
                f"small exponent at n={n}, p={prime}",
            )
            small_part *= prime**exponent
        elif prime < n:
            a, s = divmod(n, prime)
            zero = fraction_mod(
                Fraction(Q[s], factorials[s])
                * Fraction(P[a], factorials[a]),
                prime,
            ) == 0
            require((exponent > 0) == zero, f"Z_n at n={n}, p={prime}")
            require(exponent <= 2, f"Z_n exponent at n={n}, p={prime}")
            large_part *= prime**exponent
            if zero:
                zero_product *= prime
        else:
            require(exponent == 0, f"p=n contribution at n={n}")
    require(remainder == 1, f"unclassified odd factor at n={n}: {remainder}")
    require(E_odd == small_part * large_part, f"decomposition at n={n}")
    require(large_part % zero_product == 0, f"lower product bound at n={n}")
    require(zero_product**2 % large_part == 0, f"upper product bound at n={n}")

    # New equations (28a)--(28e) and (33a)--(33c): exact finite shadows of
    # the two-branch split.  A prime may lie in both branches, so sets (not a
    # disjoint partition) are used.  The asymptotic cutoff proof is in the
    # independent audit.
    v_branch_product = 1
    u_branch_product = 1
    for prime in odd_primes:
        if prime >= n:
            break
        if prime * prime <= n:
            continue
        a, s = divmod(n, prime)
        if P[a] % prime == 0:
            require(
                Fraction(n, a + 1) < prime <= Fraction(n, a),
                f"V-branch interval at n={n}, p={prime}",
            )
            v_branch_product *= prime
        if Q[s] % prime == 0:
            require(Q[n] % prime == 0, f"Lucas divisor U_n at n={n}, p={prime}")
            u_branch_product *= prime
    require(zero_product == lcm(v_branch_product, u_branch_product), f"branch union n={n}")
    require(Q[n] % u_branch_product == 0, f"U-branch product divides Q_n at n={n}")
    decomposition_depths += 1


print(
    "PASS: independent exact replay of (3)-(32), including strict (7), "
    f"on {large_pairs} large-prime pairs ({large_exceptions} exceptional) "
    f"and product decompositions at {decomposition_depths} depths"
)
print(
    "LITERATURE MAP: T_n(1,2,2)=2^n U_n, so Noe (2006), equation (13), "
    "already contains the Lucas product; no novelty or V1 claim"
)
