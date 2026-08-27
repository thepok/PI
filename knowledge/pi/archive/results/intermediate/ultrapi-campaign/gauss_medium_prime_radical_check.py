#!/usr/bin/env python3
"""Exact replay for gauss_medium_prime_radical_reduction.md.

All PASS assertions use integer or finite-field arithmetic.  Floating-point
logarithms occur only in the final lines explicitly labelled EXPERIMENT.
No finite scan is evidence for the unresolved little-o estimate.
"""

from __future__ import annotations

from math import isqrt, log

import sympy as sp


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


def floor_cuberoot(value: int) -> int:
    lower, upper = 0, 1
    while upper**3 <= value:
        lower, upper = upper, 2 * upper
    while lower + 1 < upper:
        middle = (lower + upper) // 2
        if middle**3 <= value:
            lower = middle
        else:
            upper = middle
    return lower


def a_values(last: int) -> list[int]:
    """A_n=T_n(1,2,2), from its integral recurrence."""

    values = [1, 2]
    for n in range(1, last):
        numerator = 2 * (2 * n + 1) * values[-1] + 4 * n * values[-2]
        require(numerator % (n + 1) == 0, f"A recurrence at n={n}")
        values.append(numerator // (n + 1))
    return values[: last + 1]


def zero_indices(prime: int) -> frozenset[int]:
    """Return {0<=s<p : A_s=0 mod prime} by modular recurrence."""

    values = [1, 2 % prime]
    for n in range(1, prime - 1):
        numerator = (
            2 * (2 * n + 1) * values[-1] + 4 * n * values[-2]
        ) % prime
        values.append(numerator * pow(n + 1, -1, prime) % prime)
    require(len(values) == prime, f"first block length at p={prime}")
    return frozenset(index for index, value in enumerate(values) if value == 0)


def scaled_legendre_polynomials(last: int) -> list[list[int]]:
    """Coefficient lists for L_n(X)=2^n P_n(X)."""

    values = [[1], [0, 2]]
    for n in range(1, last):
        numerator = [0] * (n + 2)
        for index, coefficient in enumerate(values[-1]):
            numerator[index + 1] += 2 * (2 * n + 1) * coefficient
        for index, coefficient in enumerate(values[-2]):
            numerator[index] -= 4 * n * coefficient
        require(
            all(coefficient % (n + 1) == 0 for coefficient in numerator),
            f"L recurrence at n={n}",
        )
        values.append([coefficient // (n + 1) for coefficient in numerator])
    return values[: last + 1]


def trim_mod(coefficients: list[int], prime: int) -> list[int]:
    result = [coefficient % prime for coefficient in coefficients]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def polynomial_remainder_mod(
    dividend: list[int], divisor: list[int], prime: int
) -> list[int]:
    """Remainder in F_prime[X], with low-to-high coefficient lists."""

    remainder = trim_mod(dividend, prime)
    divisor_mod = trim_mod(divisor, prime)
    require(divisor_mod != [0], "nonzero polynomial divisor")
    inverse_lead = pow(divisor_mod[-1], -1, prime)
    while len(remainder) >= len(divisor_mod) and remainder != [0]:
        shift = len(remainder) - len(divisor_mod)
        multiplier = remainder[-1] * inverse_lead % prime
        for index, coefficient in enumerate(divisor_mod):
            remainder[index + shift] = (
                remainder[index + shift] - multiplier * coefficient
            ) % prime
        remainder = trim_mod(remainder, prime)
    return remainder


def polynomial_product_mod(
    left: list[int], right: list[int], prime: int
) -> list[int]:
    product = [0] * (len(left) + len(right) - 1)
    for left_index, left_coefficient in enumerate(left):
        for right_index, right_coefficient in enumerate(right):
            product[left_index + right_index] = (
                product[left_index + right_index]
                + left_coefficient * right_coefficient
            ) % prime
    return trim_mod(product, prime)


def polynomial_frobenius_mod(coefficients: list[int], prime: int) -> list[int]:
    """Return f(X)^prime in F_prime[X], using the Frobenius identity."""

    result = [0] * (prime * (len(coefficients) - 1) + 1)
    for index, coefficient in enumerate(coefficients):
        result[prime * index] = coefficient % prime
    return trim_mod(result, prime)


def valuation(value: int, prime: int) -> int:
    require(value != 0, "valuation of a nonzero integer")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


# 1. Independently verify the one-digit Lucas zero criterion against exact
# integer A_n values on a bounded range.
SCAN_LAST = 10_000
primes = primes_through(SCAN_LAST)
odd_primes = [prime for prime in primes if prime != 2]
zero_sets = {prime: zero_indices(prime) for prime in odd_primes}
A = a_values(300)
lucas_checks = 0
for n in range(2, 301):
    for prime in odd_primes:
        if prime >= n:
            break
        a, s = divmod(n, prime)
        predicted_zero = a in zero_sets[prime] or s in zero_sets[prime]
        require(
            (A[n] % prime == 0) == predicted_zero,
            f"one-digit Lucas zero criterion at n={n}, p={prime}",
        )
        lucas_checks += 1


# 2. Compare the original W_n selector with the medium-prime radical M_n.
# The finite replay evaluates both through independently generated first-block
# residue tables, then checks every discrepancy against the earlier-index
# factor A_floor(n/p).
pair_checks = 0
w_pair_count = 0
m_pair_count = 0
discrepancy_count = 0
tail_checks = 0
w_weight = [0.0] * (SCAN_LAST + 1)
m_weight = [0.0] * (SCAN_LAST + 1)
witness_68: tuple[frozenset[int], frozenset[int]] | None = None

for n in range(2, SCAN_LAST + 1):
    w_primes: set[int] = set()
    m_primes: set[int] = set()
    discrepancy_by_a: dict[int, list[int]] = {}
    B = floor_cuberoot(n)

    for prime in odd_primes:
        if prime * prime <= n:
            continue
        if prime >= n:
            break
        a, s = divmod(n, prime)
        selected_w = s in zero_sets[prime]
        selected_m = selected_w or a in zero_sets[prime]
        if selected_w:
            w_primes.add(prime)
        if selected_m:
            m_primes.add(prime)
        if selected_m and not selected_w:
            require(a in zero_sets[prime], f"discrepancy source at n={n}, p={prime}")
            discrepancy_by_a.setdefault(a, []).append(prime)
        pair_checks += 1

    require(w_primes <= m_primes, f"W subset M at n={n}")
    w_pair_count += len(w_primes)
    m_pair_count += len(m_primes)
    discrepancy_count += len(m_primes - w_primes)
    w_weight[n] = sum(log(prime) for prime in w_primes)
    m_weight[n] = sum(log(prime) for prime in m_primes)

    # Exact premises of
    # M_n-W_n <= theta(n/(B+1)) + sum_{a<=B} log A_a.
    for a, selected_primes in discrepancy_by_a.items():
        if a > B:
            for prime in selected_primes:
                require(
                    prime <= n // (B + 1),
                    f"large-a cutoff at n={n}, p={prime}",
                )
                tail_checks += 1
        else:
            product = 1
            for prime in selected_primes:
                product *= prime
            require(A[a] % product == 0, f"small-a product at n={n}, a={a}")
            tail_checks += 1

    if n == 68:
        witness_68 = (frozenset(w_primes), frozenset(m_primes))

require(witness_68 is not None, "n=68 witness captured")
require(17 not in witness_68[0] and 17 in witness_68[1], "strict W/M witness")
require(A[4] % 17 == 0 and A[0] % 17 != 0, "n=68 contamination mechanism")


# 3. The tempting two-Legendre resultant has a universal p^t factor on both
# affine selector branches, even without p|A_t.  Check the polynomial
# divisibility broadly and exact resultant valuations on diagnostic examples.
L = scaled_legendre_polynomials(92)
polynomial_divisibility_checks = 0
for prime in [p for p in odd_primes if p <= 31]:
    for a in range(0, 3):
        for t in range(1, (prime - 1) // 2 + 1):
            direct = a * prime + t
            reflected = a * prime + prime - 1 - t
            schur_right = polynomial_product_mod(
                polynomial_frobenius_mod(L[a], prime), L[t], prime
            )
            require(
                trim_mod(L[direct], prime) == schur_right,
                f"full scaled Schur congruence at p={prime}, a={a}, t={t}",
            )
            reflection_scalar = pow(pow(2, 2 * t, prime), -1, prime)
            reflected_right = [
                reflection_scalar * coefficient % prime
                for coefficient in schur_right
            ]
            require(
                trim_mod(L[reflected], prime) == trim_mod(reflected_right, prime),
                f"full scaled Holt congruence at p={prime}, a={a}, t={t}",
            )
            require(
                polynomial_remainder_mod(L[direct], L[t], prime) == [0],
                f"direct resultant baseline at p={prime}, a={a}, t={t}",
            )
            require(
                polynomial_remainder_mod(L[reflected], L[t], prime) == [0],
                f"reflected resultant baseline at p={prime}, a={a}, t={t}",
            )
            polynomial_divisibility_checks += 2

x = sp.symbols("x")
resultant_examples = [
    # (N,t,p, p divides A_t, branch)
    (20, 3, 17, False, "direct"),
    (21, 4, 17, True, "direct"),
    (29, 4, 17, True, "reflected"),
    (30, 7, 23, True, "direct"),
]
resultant_table: list[tuple[int, int, int, int, bool, str]] = []
for n, t, prime, selected, branch in resultant_examples:
    polynomial_n = sum(coefficient * x**index for index, coefficient in enumerate(L[n]))
    polynomial_t = sum(coefficient * x**index for index, coefficient in enumerate(L[t]))
    resultant = int(sp.resultant(polynomial_n, polynomial_t, x))
    exponent = valuation(resultant, prime)
    require(exponent == t, f"exact resultant baseline at n={n}, t={t}, p={prime}")
    require((A[t] % prime == 0) == selected, f"selector flag at t={t}, p={prime}")
    resultant_table.append((n, t, prime, exponent, selected, branch))


dyadic_statistics = []
for upper in (100, 1_000, 10_000):
    lower = upper // 2
    maximizer = max(range(lower, upper + 1), key=lambda n: m_weight[n] / n)
    mean = sum(m_weight[n] / n for n in range(lower, upper + 1)) / (
        upper - lower + 1
    )
    dyadic_statistics.append((upper, maximizer, m_weight[maximizer] / maximizer, mean))

print(
    "PASS: W_n is contained in the medium-prime radical M_n on "
    f"{pair_checks} strict prime/depth pairs through n={SCAN_LAST}; all "
    f"{discrepancy_count} M\\W pairs came from A_floor(n/p), and "
    f"{tail_checks} exact cutoff/product groups passed"
)
print(
    "PASS: one-digit Lucas zeros matched direct integer A_n divisibility on "
    f"{lucas_checks} cases; {polynomial_divisibility_checks} full "
    "direct/reflected Legendre congruences (and divisibility checks) plus "
    "the exact resultant table passed"
)
print(f"BOUNDARY: exact resultant valuations (n,t,p,v_p,selected,branch) = {resultant_table}")
print(
    "EXPERIMENT: (W pairs, M pairs, M\\W pairs) = "
    f"({w_pair_count}, {m_pair_count}, {discrepancy_count}); "
    f"dyadic (upper,maximizer,max M_n/n,mean M_n/n) = {dyadic_statistics}; "
    "no little-o or V1 claim is made"
)
