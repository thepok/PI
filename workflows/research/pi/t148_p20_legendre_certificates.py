#!/usr/bin/env python3
"""Exact replay for the two P20 high-order common-zero certificates."""

from __future__ import annotations

from math import comb


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def sub(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = ((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % p
    return trim(out)


def scale(a: list[int], c: int, p: int) -> list[int]:
    return trim([(c * x) % p for x in a])


def xmul(a: list[int], c: int, p: int) -> list[int]:
    return [0] + [(c * x) % p for x in a]


def divmod_poly(a: list[int], b: list[int], p: int) -> tuple[list[int], list[int]]:
    r = trim(a[:])
    b = trim(b[:])
    if b == [0]:
        raise ZeroDivisionError
    q = [0] * max(1, len(r) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while r != [0] and len(r) >= len(b):
        d = len(r) - len(b)
        c = r[-1] * inv % p
        q[d] = c
        for i, value in enumerate(b):
            r[i + d] = (r[i + d] - c * value) % p
        trim(r)
    return trim(q), r


def gcd_poly(a: list[int], b: list[int], p: int) -> list[int]:
    while b != [0]:
        _, r = divmod_poly(a, b, p)
        a, b = b, r
    return scale(a, pow(a[-1], -1, p), p)


def eval_poly(a: list[int], x: int, p: int) -> int:
    value = 0
    for coefficient in reversed(a):
        value = (value * x + coefficient) % p
    return value


def legendre_polynomials(p: int, nmax: int) -> list[list[int]]:
    polynomials = [[1], [0, 1]]
    for n in range(1, nmax):
        numerator = sub(xmul(polynomials[n], 2 * n + 1, p), scale(polynomials[n - 1], n, p), p)
        polynomials.append(scale(numerator, pow(n + 1, -1, p), p))
    return polynomials


def f_value(p: int, j: int, x: int) -> int:
    m = (p - 1) // 2
    return sum(
        comb(m, r) * comb(m, j - r) * pow(x, m - j + r, p)
        for r in range(j + 1)
    ) % p


def factor(n: int) -> list[int]:
    primes = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            primes.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        primes.append(n)
    return primes


def multiplicative_order(x: int, p: int) -> int:
    order = p - 1
    for q in factor(order):
        while order % q == 0 and pow(x, order // q, p) == 1:
            order //= q
    return order


def replay(
    p: int,
    indices: list[int],
    legendre_constant: int,
    x_factor: list[int],
    roots: list[int],
    expected_order: int,
) -> None:
    polynomials = legendre_polynomials(p, max(indices))
    common = polynomials[indices[0]]
    for j in indices[1:]:
        common = gcd_poly(common, polynomials[j], p)
    expected_gcd = [legendre_constant % p, 0, 1]
    assert common == expected_gcd, (p, common)
    for root in roots:
        assert eval_poly(x_factor, root, p) == 0
        assert multiplicative_order(root, p) == expected_order
        assert all(f_value(p, j, root) == 0 for j in indices)
    print(
        f"p={p} gcd=T^2+{legendre_constant} "
        f"x_factor={x_factor} roots={roots} orders={[multiplicative_order(x, p) for x in roots]} "
        f"zero_indices={indices}"
    )


def main() -> None:
    replay(
        p=599,
        indices=[59, 92, 149, 173, 179],
        legendre_constant=180,
        x_factor=[1, 123, 1],
        roots=[88, 388],
        expected_order=598,
    )
    replay(
        p=839,
        indices=[104, 209, 295, 314],
        legendre_constant=417,
        x_factor=[1, -8, 1],
        roots=[320, 527],
        expected_order=419,
    )
    assert 209 - 104 == 314 - 209 == 105
    print("all exact certificate checks passed")


if __name__ == "__main__":
    main()
