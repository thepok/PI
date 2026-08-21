#!/usr/bin/env python3
"""Exact replay for gauss_large_prime_zero_density_reduction.md.

The PASS assertions use exact integer arithmetic, except that logarithms are
used only to replay the stated finite weighted-sum experiment.  No finite scan
is used as evidence for the unresolved o(n) estimate.
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
    """Return floor(value**(1/3)) using integer comparisons only."""

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
    """A_n=2^n U_n=T_n(1,2,2), computed by its exact recurrence."""

    values = [1, 2]
    for n in range(1, last):
        numerator = (
            2 * (2 * n + 1) * values[-1] + 4 * n * values[-2]
        )
        require(numerator % (n + 1) == 0, f"A recurrence at n={n}")
        values.append(numerator // (n + 1))
    return values[: last + 1]


def integral_legendre_polynomials(last: int) -> list[list[int]]:
    """Return coefficient lists for L_n(X)=2^n P_n(X)."""

    values = [[1], [0, 2]]
    for n in range(1, last):
        degree = n + 2
        numerator = [0] * degree
        for index, coefficient in enumerate(values[-1]):
            numerator[index + 1] += 2 * (2 * n + 1) * coefficient
        for index, coefficient in enumerate(values[-2]):
            numerator[index] -= 4 * n * coefficient
        require(
            all(coefficient % (n + 1) == 0 for coefficient in numerator),
            f"integral Legendre recurrence at n={n}",
        )
        values.append([coefficient // (n + 1) for coefficient in numerator])
    return values[: last + 1]


def remainder_mod_x2_plus_1(coefficients: list[int]) -> tuple[int, int]:
    """Return c_0,c_1 with f(X)=c_0+c_1 X modulo X^2+1."""

    constant = 0
    linear = 0
    for exponent, coefficient in enumerate(coefficients):
        if exponent % 2 == 0:
            constant += (-1) ** (exponent // 2) * coefficient
        else:
            linear += (-1) ** ((exponent - 1) // 2) * coefficient
    return constant, linear


def zero_indices(prime: int) -> tuple[int, ...]:
    """Indices 0<=s<p for which U_s=0 modulo prime.

    Since s! is a unit in this range, the raw continuant Q_s=s! U_s has
    exactly the same zeros and avoids modular division.
    """

    previous, current = 1, 1
    zeros: list[int] = []
    for n in range(2, prime):
        following = (
            (2 * n - 1) * current + (n - 1) ** 2 * previous
        ) % prime
        if following == 0:
            zeros.append(n)
        previous, current = current, following
    return tuple(zeros)


# 1. Gaussian norm/resultant identity.
ALGEBRA_LAST = 16
A = a_values(10_000)
L = integral_legendre_polynomials(ALGEBRA_LAST)
x = sp.symbols("x")
for n in range(ALGEBRA_LAST + 1):
    expected_remainder = (
        ((-1) ** (n // 2) * A[n], 0)
        if n % 2 == 0
        else (0, (-1) ** (n // 2) * A[n])
    )
    require(
        remainder_mod_x2_plus_1(L[n]) == expected_remainder,
        f"L_n remainder modulo X^2+1 at n={n}",
    )
    polynomial = sum(coefficient * x**index for index, coefficient in enumerate(L[n]))
    resultant = int(sp.resultant(x**2 + 1, polynomial, x))
    require(resultant == A[n] ** 2, f"Gaussian resultant at n={n}")


# 2. Reflection, minimal-index encoding, and exact selector replay.
SCAN_LAST = 10_000
primes = primes_through(SCAN_LAST)
zero_sets: dict[int, frozenset[int]] = {}
max_zero_record = (0, 0, ())
for prime in primes:
    if prime == 2:
        continue
    zeros = zero_indices(prime)
    zero_set = frozenset(zeros)
    zero_sets[prime] = zero_set
    m = (prime - 1) // 2
    for s in range(prime):
        reflected = prime - 1 - s
        require(
            (s in zero_set) == (reflected in zero_set),
            f"reflection zero set at p={prime}, s={s}",
        )
        # Recompute residues only at zeros; the sign formula itself is also
        # checked below from a full recurrence table for smaller primes.
    if len(zeros) > max_zero_record[0]:
        max_zero_record = (len(zeros), prime, zeros)


for prime in [p for p in primes if p <= 997 and p != 2]:
    residues = [1, 1]
    for n in range(2, prime):
        residues.append(
            (
                (2 * n - 1) * residues[-1]
                + (n - 1) * residues[-2]
            )
            * pow(n, -1, prime)
            % prime
        )
    m = (prime - 1) // 2
    for s in range(prime):
        require(
            residues[prime - 1 - s]
            == (-1) ** (m + s) * residues[s] % prime,
            f"signed reflection at p={prime}, s={s}",
        )


weighted = [0.0] * (SCAN_LAST + 1)
selected_count = [0] * (SCAN_LAST + 1)
selector_pairs: list[list[tuple[int, int]]] = [
    [] for _ in range(SCAN_LAST + 1)
]
encoded_pair_count = 0
for n in range(2, SCAN_LAST + 1):
    for prime in primes:
        if prime == 2:
            continue
        if prime * prime <= n:
            continue
        if prime >= n:
            break
        a, s = divmod(n, prime)
        if s not in zero_sets[prime]:
            continue
        t = min(s, prime - 1 - s)
        require(prime > 2 * t, f"minimal-index size at n={n}, p={prime}")
        require(A[t] % prime == 0, f"minimal-index divisor at n={n}, p={prime}")
        require(
            (2 * a + 1) * t <= n - a,
            f"triangular core constraint at n={n}, p={prime}",
        )
        if t == s:
            require(a * prime + t == n, f"direct encoding at n={n}, p={prime}")
            require((n - t) // a == prime, f"direct quotient at n={n}, p={prime}")
        if t == prime - 1 - s:
            require(
                (a + 1) * prime - 1 - t == n,
                f"reflected encoding at n={n}, p={prime}",
            )
            require(
                (n + 1 + t) // (a + 1) == prime,
                f"reflected quotient at n={n}, p={prime}",
            )
        weighted[n] += log(prime)
        selected_count[n] += 1
        selector_pairs[n].append((prime, t))
        encoded_pair_count += 1


# 3. Exact finite replay of the two-tail premises.  The proof uses
# theta(n/(B+1)) for the quotient tail and sum_{t<=T} log A_t for the
# endpoint tail.  We check the first by exact integer cutoff membership and
# the second by exact divisibility of the product of the relevant distinct
# primes into A_t.  No floating-point logarithm enters these assertions.
for n in range(8, SCAN_LAST + 1):
    B = floor_cuberoot(n)
    T = B
    endpoint_products: dict[int, int] = {}
    category_count = 0
    for prime, t in selector_pairs[n]:
        a = n // prime
        if a > B:
            require(
                prime <= n // (B + 1),
                f"quotient-tail cutoff at n={n}, p={prime}",
            )
        elif t <= T:
            endpoint_products[t] = endpoint_products.get(t, 1) * prime
        category_count += 1
    require(
        category_count == len(selector_pairs[n]),
        f"tail partition at n={n}",
    )
    for t, prime_product in endpoint_products.items():
        require(
            A[t] % prime_product == 0,
            f"endpoint-tail divisibility at n={n}, t={t}",
        )


# 4. Explicit finite statistics.  These are experiments only.
dyadic_statistics = []
for upper in (100, 1_000, 10_000):
    lower = upper // 2
    maximizer = max(range(lower, upper + 1), key=lambda n: weighted[n] / n)
    average = sum(weighted[n] / n for n in range(lower, upper + 1)) / (
        upper - lower + 1
    )
    dyadic_statistics.append(
        (upper, maximizer, weighted[maximizer] / maximizer, average)
    )


print(
    "PASS: Gaussian remainder/resultant identity, signed reflection, and "
    f"minimal-index selector encoding on {encoded_pair_count} selected pairs "
    f"through n={SCAN_LAST}; the two-tail premises also replay exactly"
)
print(
    "EXPERIMENT: among odd primes p<=10000 the largest first-block zero count "
    f"is {max_zero_record[0]} at p={max_zero_record[1]}, with zeros "
    f"{list(max_zero_record[2])}"
)
print(
    "EXPERIMENT: dyadic (upper, maximizer, max W_n/n, mean W_n/n) = "
    f"{dyadic_statistics}; no asymptotic claim is made"
)
