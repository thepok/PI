#!/usr/bin/env python3
"""Independent exact replay for the Gauss medium-prime radical audit.

This file imports no code from gauss_medium_prime_radical_check.py. Every
assertion uses integers or finite fields. The bounded assertions are an
experiment, not a proof of any asymptotic statement.
"""

from __future__ import annotations

from functools import cache
from math import comb, isqrt


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


def central_coefficient(n: int) -> int:
    """Return [X^n](X^2+2X+2)^n from independent multinomial choices."""

    return sum(
        comb(n, 2 * k) * comb(2 * k, k) * 2 ** (n - k) for k in range(n // 2 + 1)
    )


def recurrence_a(last: int) -> list[int]:
    values = [1, 2]
    for n in range(1, last):
        numerator = 2 * (2 * n + 1) * values[n] + 4 * n * values[n - 1]
        require(numerator % (n + 1) == 0, f"A recurrence division at n={n}")
        values.append(numerator // (n + 1))
    return values[: last + 1]


def prime_factors(value: int) -> set[int]:
    factors: set[int] = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        factors.add(value)
    return factors


def trim_mod(coefficients: list[int], prime: int) -> list[int]:
    result = [coefficient % prime for coefficient in coefficients]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def polynomial_product(left: list[int], right: list[int]) -> list[int]:
    product = [0] * (len(left) + len(right) - 1)
    for left_index, left_coefficient in enumerate(left):
        for right_index, right_coefficient in enumerate(right):
            product[left_index + right_index] += left_coefficient * right_coefficient
    return product


def polynomial_product_mod(left: list[int], right: list[int], prime: int) -> list[int]:
    return trim_mod(polynomial_product(left, right), prime)


def polynomial_add(left: list[int], right: list[int]) -> list[int]:
    result = [0] * max(len(left), len(right))
    for index, coefficient in enumerate(left):
        result[index] += coefficient
    for index, coefficient in enumerate(right):
        result[index] += coefficient
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def polynomial_remainder_mod(
    dividend: list[int], divisor: list[int], prime: int
) -> list[int]:
    remainder = trim_mod(dividend, prime)
    divisor_mod = trim_mod(divisor, prime)
    require(divisor_mod != [0], "nonzero polynomial divisor")
    inverse_lead = pow(divisor_mod[-1], -1, prime)
    while remainder != [0] and len(remainder) >= len(divisor_mod):
        shift = len(remainder) - len(divisor_mod)
        multiplier = remainder[-1] * inverse_lead % prime
        for index, coefficient in enumerate(divisor_mod):
            remainder[index + shift] = (
                remainder[index + shift] - multiplier * coefficient
            ) % prime
        remainder = trim_mod(remainder, prime)
    return remainder


@cache
def scaled_legendre(n: int) -> tuple[int, ...]:
    """Low-to-high coefficients of 2^n P_n from the explicit formula."""

    coefficients = [0] * (n + 1)
    for k in range(n // 2 + 1):
        coefficients[n - 2 * k] = (-1) ** k * comb(n, k) * comb(2 * n - 2 * k, n)
    return tuple(coefficients)


def scaled_legendre_recurrence(last: int) -> list[list[int]]:
    values = [[1], [0, 2]]
    for n in range(1, last):
        numerator = [0] * (n + 2)
        for index, coefficient in enumerate(values[n]):
            numerator[index + 1] += 2 * (2 * n + 1) * coefficient
        for index, coefficient in enumerate(values[n - 1]):
            numerator[index] -= 4 * n * coefficient
        require(
            all(coefficient % (n + 1) == 0 for coefficient in numerator),
            f"L recurrence division at n={n}",
        )
        values.append([coefficient // (n + 1) for coefficient in numerator])
    return values[: last + 1]


def frobenius_mod(coefficients: list[int], prime: int) -> list[int]:
    result = [0] * (prime * (len(coefficients) - 1) + 1)
    for index, coefficient in enumerate(coefficients):
        result[prime * index] = coefficient % prime
    return trim_mod(result, prime)


def bareiss_determinant(matrix: list[list[int]]) -> int:
    """Return an exact determinant by fraction-free elimination."""

    size = len(matrix)
    if size == 0:
        return 1
    data = [row[:] for row in matrix]
    sign = 1
    denominator = 1
    for column in range(size - 1):
        pivot_row = next(
            (row for row in range(column, size) if data[row][column] != 0),
            None,
        )
        if pivot_row is None:
            return 0
        if pivot_row != column:
            data[column], data[pivot_row] = data[pivot_row], data[column]
            sign = -sign
        pivot = data[column][column]
        for row in range(column + 1, size):
            for col in range(column + 1, size):
                numerator = (
                    data[row][col] * pivot - data[row][column] * data[column][col]
                )
                require(
                    numerator % denominator == 0,
                    f"Bareiss exact division at column={column}",
                )
                data[row][col] = numerator // denominator
            data[row][column] = 0
        denominator = pivot
    return sign * data[-1][-1]


def resultant_int(first: list[int], second: list[int]) -> int:
    """Return the Sylvester determinant Res(first, second), low-to-high."""

    while len(first) > 1 and first[-1] == 0:
        first.pop()
    while len(second) > 1 and second[-1] == 0:
        second.pop()
    first_degree = len(first) - 1
    second_degree = len(second) - 1
    if first_degree == 0:
        return first[0] ** second_degree
    if second_degree == 0:
        return second[0] ** first_degree
    first_high = list(reversed(first))
    second_high = list(reversed(second))
    size = first_degree + second_degree
    matrix: list[list[int]] = []
    for shift in range(second_degree):
        row = [0] * size
        row[shift : shift + first_degree + 1] = first_high
        matrix.append(row)
    for shift in range(first_degree):
        row = [0] * size
        row[shift : shift + second_degree + 1] = second_high
        matrix.append(row)
    return bareiss_determinant(matrix)


def valuation(value: int, prime: int) -> int:
    require(value != 0, "finite valuation requires a nonzero integer")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


# Definitions, one-digit Lucas, W/M, and every finite B in the rectangle.
CHECK_LAST = 360
primes = primes_through(CHECK_LAST)
odd_primes = [prime for prime in primes if prime != 2]
A = recurrence_a(CHECK_LAST)
for n, value in enumerate(A):
    require(value == central_coefficient(n), f"central coefficient at n={n}")
    require(1 <= value <= 5**n, f"positive coefficient bound at n={n}")

lucas_checks = 0
pair_checks = 0
bound_checks = 0
band_partition_checks = 0
endpoint_checks = 0
w_sets: list[set[int]] = [set() for _ in range(CHECK_LAST + 1)]
m_sets: list[set[int]] = [set() for _ in range(CHECK_LAST + 1)]

primorial = [1] * (CHECK_LAST + 1)
running_primorial = 1
prime_set = set(primes)
for value in range(1, CHECK_LAST + 1):
    if value in prime_set:
        running_primorial *= value
    primorial[value] = running_primorial
five_triangular = [5 ** (b * (b + 1) // 2) for b in range(CHECK_LAST + 4)]

for n in range(2, CHECK_LAST + 1):
    bands: dict[int, set[int]] = {}
    for prime in odd_primes:
        if prime >= n:
            break
        if prime * prime <= n:
            continue
        a, s = divmod(n, prime)
        require(1 <= a < prime, f"medium quotient domain n={n}, p={prime}")
        require(
            A[n] % prime == A[a] * A[s] % prime,
            f"one-digit Lucas identity n={n}, p={prime}",
        )
        selected_w = A[s] % prime == 0
        selected_m = A[n] % prime == 0
        require(
            selected_m == (A[a] % prime == 0 or selected_w),
            f"Lucas zero disjunction n={n}, p={prime}",
        )
        if selected_w:
            w_sets[n].add(prime)
            bands.setdefault(a, set()).add(prime)
        if selected_m:
            m_sets[n].add(prime)
        pair_checks += 1
        lucas_checks += 1

    require(w_sets[n] <= m_sets[n], f"W subset M at n={n}")
    band_union = set().union(*bands.values()) if bands else set()
    require(band_union == w_sets[n], f"band partition at n={n}")
    require(
        sum(len(selected) for selected in bands.values()) == len(w_sets[n]),
        f"disjoint band count at n={n}",
    )
    band_partition_checks += 1

    discrepancy = m_sets[n] - w_sets[n]
    discrepancy_product = 1
    for prime in discrepancy:
        discrepancy_product *= prime

    for B in range(1, CHECK_LAST + 4):
        small_groups: dict[int, int] = {}
        for prime in discrepancy:
            a = n // prime
            if a > B:
                require(
                    prime * (B + 1) <= n,
                    f"large-a cutoff n={n}, p={prime}, B={B}",
                )
            else:
                small_groups[a] = small_groups.get(a, 1) * prime
        for a, product in small_groups.items():
            require(A[a] % product == 0, f"small-a product n={n}, a={a}, B={B}")
        exact_rhs_product = primorial[n // (B + 1)] * five_triangular[B]
        require(
            discrepancy_product <= exact_rhs_product,
            f"exponentiated error bound n={n}, B={B}",
        )
        bound_checks += 1

    first_w = {prime for prime in w_sets[n] if n // prime == 1}
    first_m_interval = {
        prime
        for prime in odd_primes
        if 2 * prime > n and prime < n and A[n] % prime == 0
    }
    require(first_w == first_m_interval, f"exact a=1 band at n={n}")

    for a, selected in bands.items():
        for prime in selected:
            s = n % prime
            t = min(s, prime - 1 - s)
            direct = s == t
            reflected = prime - 1 - s == t
            require(direct or reflected, f"selector branch n={n}, p={prime}")
            if direct:
                require(a * prime + t == n, f"direct selector n={n}, p={prime}")
            if reflected:
                require(
                    (a + 1) * prime - 1 - t == n,
                    f"reflected selector n={n}, p={prime}",
                )
            for eta_numerator, eta_denominator in ((1, 20), (1, 10), (1, 4)):
                if t * eta_denominator <= eta_numerator * n:
                    if direct:
                        require(
                            a * prime <= n
                            and eta_denominator * a * prime
                            >= (eta_denominator - eta_numerator) * n,
                            f"direct endpoint interval n={n}, p={prime}",
                        )
                    if reflected:
                        require(
                            (a + 1) * prime >= n + 1
                            and eta_denominator * (a + 1) * prime
                            <= eta_denominator * (n + 1) + eta_numerator * n,
                            f"reflected endpoint interval n={n}, p={prime}",
                        )
                    endpoint_checks += 1

# Wider direct Lucas grid, without first-block residue tables.
for prime in [p for p in odd_primes if p <= 31]:
    for a in range(CHECK_LAST // prime + 1):
        for s in range(prime):
            n = a * prime + s
            if n > CHECK_LAST:
                break
            require(
                A[n] % prime == A[a] * A[s] % prime,
                f"full Lucas grid p={prime}, a={a}, s={s}",
            )
            lucas_checks += 1

# Eventual fixed-a identity with an explicit sufficient threshold.
eventual_band_checks = 0
for a in range(1, 6):
    threshold = (a + 1) * max(prime_factors(A[a])) + 1
    for n in range(max(2, threshold), CHECK_LAST + 1):
        w_band = {prime for prime in w_sets[n] if n // prime == a}
        m_band = {prime for prime in m_sets[n] if n // prime == a}
        require(w_band == m_band, f"eventual fixed band n={n}, a={a}")
        for prime in w_band:
            require(n < (a + 1) * prime, f"strict lower endpoint n={n}, p={prime}")
            require(a * prime <= n, f"weak upper endpoint n={n}, p={prime}")
        eventual_band_checks += 1


# Explicit scaled Legendre formula, Schur/Holt, and polynomial divisibility.
L_recurrence = scaled_legendre_recurrence(80)
for n, polynomial in enumerate(L_recurrence):
    require(polynomial == list(scaled_legendre(n)), f"scaled Legendre formula n={n}")

polynomial_checks = 0
for prime in [p for p in odd_primes if p <= 19]:
    a_values = range(prime) if prime <= 13 else (0, 1, 2, prime - 1)
    for a in a_values:
        for t in range(1, (prime - 1) // 2 + 1):
            base = list(scaled_legendre(t))
            schur_factor = frobenius_mod(list(scaled_legendre(a)), prime)
            direct_right = polynomial_product_mod(schur_factor, base, prime)
            direct_index = a * prime + t
            reflected_index = a * prime + prime - 1 - t
            require(
                trim_mod(list(scaled_legendre(direct_index)), prime) == direct_right,
                f"scaled Schur p={prime}, a={a}, t={t}",
            )
            scalar = pow(pow(2, 2 * t, prime), -1, prime)
            reflected_right = trim_mod(
                [scalar * coefficient for coefficient in direct_right], prime
            )
            require(
                trim_mod(list(scaled_legendre(reflected_index)), prime)
                == reflected_right,
                f"scaled Holt p={prime}, a={a}, t={t}",
            )
            require(
                polynomial_remainder_mod(
                    list(scaled_legendre(direct_index)), base, prime
                )
                == [0],
                f"direct polynomial divisibility p={prime}, a={a}, t={t}",
            )
            require(
                polynomial_remainder_mod(
                    list(scaled_legendre(reflected_index)), base, prime
                )
                == [0],
                f"reflected polynomial divisibility p={prime}, a={a}, t={t}",
            )
            require(
                comb(2 * t, t) % prime != 0,
                f"unit leading coefficient p={prime}, t={t}",
            )
            polynomial_checks += 2


# Custom Sylvester/Bareiss resultants: diagnostic table and general lemma.
resultant_examples = [
    (20, 3, 17, False, "direct"),
    (21, 4, 17, True, "direct"),
    (29, 4, 17, True, "reflected"),
    (30, 7, 23, True, "direct"),
]
resultant_table: list[tuple[int, int, int, int, bool, str]] = []
for n, t, prime, expected_selected, branch in resultant_examples:
    resultant = resultant_int(list(scaled_legendre(n)), list(scaled_legendre(t)))
    exponent = valuation(resultant, prime)
    require(exponent == t, f"resultant valuation n={n}, t={t}, p={prime}")
    selected = A[t] % prime == 0
    require(selected == expected_selected, f"selector flag t={t}, p={prime}")
    resultant_table.append((n, t, prime, exponent, selected, branch))

resultant_lemma_checks = 0
for prime in (3, 5, 7, 11):
    for degree in range(1, 5):
        leading = degree + 1
        if leading % prime == 0:
            leading += 1
        f = [index + 1 for index in range(degree)] + [leading]
        quotient = [2, -1, 1]
        perturbation = [(-1) ** index * (index + 2) for index in range(degree + 2)]
        g = polynomial_add(
            polynomial_product(f, quotient),
            [prime * coefficient for coefficient in perturbation],
        )
        require(f[-1] % prime != 0, f"resultant unit p={prime}, degree={degree}")
        require(
            polynomial_remainder_mod(g, f, prime) == [0],
            f"resultant premise p={prime}, degree={degree}",
        )
        require(
            resultant_int(g, f) % (prime**degree) == 0,
            f"resultant conclusion p={prime}, degree={degree}",
        )
        resultant_lemma_checks += 1


print(
    "PASS: independent definitions, central coefficients, one-digit Lucas identity, "
    f"and W/M containment on {pair_checks} medium-prime pairs; {bound_checks} exact "
    "integer exponentiations of the every-(n,B) error bound passed"
)
print(
    f"PASS: {band_partition_checks} band partitions, {eventual_band_checks} eventual "
    f"fixed-band instances, {endpoint_checks} exact endpoint-selector containments, "
    f"{polynomial_checks} scaled Schur/Holt divisibility checks, and "
    f"{resultant_lemma_checks} resultant-lemma instances passed"
)
print(f"BOUNDARY: exact resultant table = {resultant_table}")
print(
    f"EXPERIMENT: {lucas_checks} finite Lucas congruences were replayed exactly; finite "
    "data prove no little-o estimate, no exceptional-gcd bound, and no V1 claim"
)
