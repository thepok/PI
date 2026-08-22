#!/usr/bin/env python3
"""Exact finite falsification census for the P20 universal-root criterion.

This is a finite experiment, not a proof of the criterion.  Elements of
F_p[s]/(s^2-2) are represented by pairs (a,b) for a+b*s.
"""

from math import isqrt
from math import comb


LIMIT = 503


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start:limit + 1:prime] = b"\x00" * (
                (limit - start) // prime + 1
            )
    return [prime for prime in range(3, limit + 1, 2) if sieve[prime]]


def multiply(x: tuple[int, int], y: tuple[int, int], p: int) -> tuple[int, int]:
    return (
        (x[0] * y[0] + 2 * x[1] * y[1]) % p,
        (x[0] * y[1] + x[1] * y[0]) % p,
    )


def power(x: tuple[int, int], exponent: int, p: int) -> tuple[int, int]:
    value = (1, 0)
    while exponent:
        if exponent & 1:
            value = multiply(value, x, p)
        x = multiply(x, x, p)
        exponent //= 2
    return value


def prime_factors(number: int) -> list[int]:
    factors = []
    divisor = 2
    while divisor * divisor <= number:
        if number % divisor == 0:
            factors.append(divisor)
            while number % divisor == 0:
                number //= divisor
        divisor += 1
    if number > 1:
        factors.append(number)
    return factors


def multiplicative_order(x: tuple[int, int], group_order: int, p: int) -> int:
    order = group_order
    for factor in prime_factors(group_order):
        while order % factor == 0 and power(x, order // factor, p) == (1, 0):
            order //= factor
    return order


def torsion_roots(p: int) -> tuple[int, list[tuple[int, int]]]:
    """Return N_p and every root of X^N_p-1 in the prescribed group."""
    split = pow(2, (p - 1) // 2, p) == 1
    if split:
        roots = [(value, 0) for value in range(1, p)]
        group_order = p - 1
    else:
        roots = [
            (a, b)
            for a in range(p)
            for b in range(p)
            if (a * a - 2 * b * b) % p == 1
        ]
        group_order = p + 1
    assert len(roots) == group_order
    assert all(power(root, group_order, p) == (1, 0) for root in roots)
    return group_order, roots


def integer_cube_root(number: int) -> int:
    root = 0
    while (root + 1) ** 3 <= number:
        root += 1
    return root


def f_zero_indices(
    p: int, x: tuple[int, int], lower: int, upper: int
) -> list[int]:
    """Compute zeros of the exact P20 F_j(x) on [lower,upper].

    If m=(p-1)/2, then

      F_j(x)=x^m [z^j](1+z)^m(1+x^(-1)z)^m.

    The coefficients c_j of the product obey

      (j+1)c_(j+1)=(1+x^-1)(m-j)c_j
                       +x^-1(2m-j+1)c_(j-1).

    Multiplication by the nonzero x^m is retained explicitly below.
    """
    m = (p - 1) // 2
    group_order = p - 1 if x[1] == 0 else p + 1
    inverse = power(x, group_order - 1, p)
    linear = ((1 + inverse[0]) % p, inverse[1])
    coefficients = [(1, 0), (m * linear[0] % p, m * linear[1] % p)]
    for j in range(1, upper):
        first = multiply(linear, coefficients[j], p)
        second = multiply(inverse, coefficients[j - 1], p)
        numerator = (
            ((m - j) * first[0] + (2 * m - j + 1) * second[0]) % p,
            ((m - j) * first[1] + (2 * m - j + 1) * second[1]) % p,
        )
        reciprocal = pow(j + 1, p - 2, p)
        coefficients.append(
            (numerator[0] * reciprocal % p, numerator[1] * reciprocal % p)
        )
    scale = power(x, m, p)
    values = [multiply(scale, coefficients[j], p) for j in range(upper + 1)]
    return [j for j in range(lower, upper + 1) if values[j] == (0, 0)]


def direct_f_zero_indices(
    p: int, x: tuple[int, int], lower: int, upper: int
) -> list[int]:
    """Literal contract formula, used only as an independent cross-check."""
    m = (p - 1) // 2
    zeros = []
    for j in range(lower, upper + 1):
        value = (0, 0)
        for t in range(max(0, m - j), min(m, 2 * m - j) + 1):
            coefficient = comb(m, t) * comb(m, j - m + t)
            term = power(x, t, p)
            value = (
                (value[0] + coefficient * term[0]) % p,
                (value[1] + coefficient * term[1]) % p,
            )
        if value == (0, 0):
            zeros.append(j)
    return zeros


eligible_primes = 0
counterexamples = []
global_maximum = 0
maximum_primes = set()
witness_rows = {}

for p in primes_through(LIMIT):
    lower = (p + 10) // 11
    upper = 2 * p // 5
    threshold = isqrt(p - 1) + 1
    if upper - lower + 1 < threshold:
        continue
    eligible_primes += 1
    order_cutoff = integer_cube_root(p)
    group_order, roots = torsion_roots(p)
    local_maximum = 0
    for root in roots:
        order = multiplicative_order(root, group_order, p)
        if order <= order_cutoff:
            continue
        zeros = f_zero_indices(p, root, lower, upper)
        if p <= 23:
            assert zeros == direct_f_zero_indices(p, root, lower, upper)
        count = len(zeros)
        local_maximum = max(local_maximum, count)
        if count >= threshold:
            counterexamples.append((p, root, order, zeros))
        expected = {
            197: ((16, 63), 99, [30, 42, 46, 67]),
            251: ((17, 12), 42, [25, 41, 75, 83]),
            367: ((25, 0), 61, [63, 86, 94, 121]),
            479: ((36, 0), 239, [59, 159, 179, 182]),
        }.get(p)
        if expected is not None and root == expected[0]:
            assert (order, zeros) == expected[1:]
            assert zeros == direct_f_zero_indices(p, root, lower, upper)
            witness_rows[p] = (root, order, zeros)
    if local_maximum > global_maximum:
        global_maximum = local_maximum
        maximum_primes = {p}
    elif local_maximum == global_maximum:
        maximum_primes.add(p)

assert eligible_primes == 92
assert counterexamples == []
assert global_maximum == 4
assert maximum_primes == {197, 251, 367, 479}
assert set(witness_rows) == maximum_primes
assert all(isqrt(p - 1) + 1 >= 15 for p in maximum_primes)

print("Status: experiment")
print(f"odd prime limit: {LIMIT}")
print(f"eligible primes: {eligible_primes}")
print("universal-root counterexamples: 0")
print(f"maximum simultaneous high-order zeros: {global_maximum}")
for p in sorted(witness_rows):
    root, order, zeros = witness_rows[p]
    print(f"p={p} root={root} order={order} zeros={zeros}")
