#!/usr/bin/env python3
"""Independent exact audit for the Gauss--Lambert 2-adic argument.

This deliberately reimplements the identities in the companion report rather
than importing its checker.  Infinite p-adic convergence remains a proof
obligation; the finite tests below target algebra, signs, normalizations, and
the negative-upper-argument boundary at t = 0.
"""

from fractions import Fraction
from math import comb, factorial


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def valuation_two_integer(value: int) -> int:
    check(value != 0, "valuation at zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def valuation_two(value: int | Fraction) -> int:
    value = Fraction(value)
    check(value != 0, "valuation at zero")
    return valuation_two_integer(value.numerator) - valuation_two_integer(
        value.denominator
    )


def choose_integer(upper: int, lower: int) -> int:
    """Generalized binomial coefficient for every integral upper argument."""
    check(lower >= 0, "negative lower argument")
    if upper >= 0:
        return comb(upper, lower) if lower <= upper else 0
    return (-1) ** lower * comb(-upper + lower - 1, lower)


def odd_factorial(last: int) -> int:
    check(last >= -1 and last % 2, "odd double-factorial domain")
    result = 1
    for value in range(1, last + 1, 2):
        result *= value
    return result


def coefficient(index: int) -> Fraction:
    return Fraction(factorial(index), odd_factorial(2 * index + 1))


def q_recurrence(bound: int) -> list[int]:
    result = [1, 1]
    for n in range(2, bound + 1):
        result.append((2 * n - 1) * result[-1] + (n - 1) ** 2 * result[-2])
    return result[: bound + 1]


def q_closed(n: int) -> Fraction:
    return sum(
        (
            Fraction(
                factorial(n) ** 2,
                2**k * factorial(k) ** 2 * factorial(n - 2 * k),
            )
            for k in range(n // 2 + 1)
        ),
        Fraction(0),
    )


def trinomial_middle(n: int) -> int:
    # Select k quadratic, n-2k linear, and k constant factors.
    return sum(
        factorial(n)
        // (factorial(k) ** 2 * factorial(n - 2 * k))
        * 2 ** (n - k)
        for k in range(n // 2 + 1)
    )


def even_factor(m: int) -> Fraction:
    return sum(
        (
            Fraction(factorial(j) * comb(m, j) ** 2, odd_factorial(2 * j - 1))
            for j in range(m + 1)
        ),
        Fraction(0),
    )


def f_finite(nonnegative_upper: int) -> Fraction:
    return sum(
        (
            coefficient(j) * comb(nonnegative_upper, j) ** 2
            for j in range(nonnegative_upper + 1)
        ),
        Fraction(0),
    )


def paired_term(r: int, t: int) -> Fraction:
    upper = 2 * t - 1
    return coefficient(2 * r) * choose_integer(upper, 2 * r) ** 2 + coefficient(
        2 * r + 1
    ) * choose_integer(upper, 2 * r + 1) ** 2


def paired_factor(r: int, t: int) -> Fraction:
    upper = 2 * t - 1
    b = choose_integer(upper, 2 * r)
    polynomial = 6 * r**2 - 4 * r * t + 7 * r + 2 * t**2 - 2 * t + 2
    return Fraction(
        2 * factorial(2 * r) * b**2 * polynomial,
        odd_factorial(4 * r + 1) * (2 * r + 1) * (4 * r + 3),
    )


# Exact Gaussian rationals, represented as real/imaginary pairs.
Gaussian = tuple[Fraction, Fraction]


def gadd(left: Gaussian, right: Gaussian) -> Gaussian:
    return left[0] + right[0], left[1] + right[1]


def gmul(left: Gaussian, right: Gaussian) -> Gaussian:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def gscale(value: Gaussian, scalar: Fraction) -> Gaussian:
    return value[0] * scalar, value[1] * scalar


def ginverse(value: Gaussian) -> Gaussian:
    norm = value[0] ** 2 + value[1] ** 2
    check(norm != 0, "Gaussian division by zero")
    return value[0] / norm, -value[1] / norm


def gdivide(left: Gaussian, right: Gaussian) -> Gaussian:
    return gmul(left, ginverse(right))


def gpower(value: Gaussian, exponent: int) -> Gaussian:
    result = (Fraction(1), Fraction(0))
    base = value
    while exponent:
        if exponent & 1:
            result = gmul(result, base)
        base = gmul(base, base)
        exponent //= 2
    return result


def gaussian_valuation(value: Gaussian) -> Fraction:
    norm = value[0] ** 2 + value[1] ** 2
    check(norm != 0, "Gaussian valuation at zero")
    return Fraction(valuation_two(norm), 2)


def audit_partial_fractions() -> None:
    one = (Fraction(1), Fraction(0))
    i = (Fraction(0), Fraction(1))
    a = gadd(one, i)
    b = gadd(one, gscale(i, Fraction(-1)))
    half_a = gscale(a, Fraction(1, 2))
    half_b = gscale(b, Fraction(1, 2))

    for z_value in range(-8, 9):
        z = (Fraction(z_value), Fraction(0))
        first = gadd(one, gscale(gmul(a, z), Fraction(-1)))
        second = gadd(one, gscale(gmul(b, z), Fraction(-1)))
        denominator = gmul(first, second)
        target = ginverse(denominator)

        # This is equation (18) as printed: crossed numerators.
        crossed = gadd(gdivide(half_b, first), gdivide(half_a, second))
        check(crossed == target, f"printed partial fractions at z={z_value}")

        # Swapping those numerators is not a repair; it introduces 1-2z.
        uncrossed = gadd(gdivide(half_a, first), gdivide(half_b, second))
        if z_value != 0:
            check(uncrossed != target, f"swapped fractions unexpectedly at z={z_value}")

        # Derivative of (i/2)(Log(first)-Log(second)), written directly
        # to avoid relying on a symbolic logarithm:
        # (i/2)(-a/first + b/second).
        derivative = gscale(
            gadd(
                gdivide(gscale(a, Fraction(-1)), first),
                gdivide(b, second),
            ),
            Fraction(1, 2),
        )
        derivative = gmul(i, derivative)
        check(derivative == target, f"correct logarithmic primitive at z={z_value}")

        # The report's -1/2(Log(first)+Log(second)) differentiates to
        # (1-2z)/denominator, not to 1/denominator.
        wrong_derivative = gscale(
            gadd(
                gdivide(gscale(a, Fraction(-1)), first),
                gdivide(gscale(b, Fraction(-1)), second),
            ),
            Fraction(-1, 2),
        )
        if z_value != 0:
            check(
                wrong_derivative != target,
                f"incorrect primitive unexpectedly valid at z={z_value}",
            )


def main() -> None:
    q = q_recurrence(600)
    for n, value in enumerate(q):
        closed = q_closed(n)
        check(closed.denominator == 1 and closed.numerator == value, f"formula (7), n={n}")
        check(
            Fraction(factorial(n) * trinomial_middle(n), 2**n) == value,
            f"formula (8), n={n}",
        )
        extra = (0, 0, 1, valuation_two_integer(n + 1))[n % 4]
        check(valuation_two_integer(value) == n // 2 + extra, f"formula (2), n={n}")

    for m in range(201):
        k = even_factor(m)
        check(
            Fraction(q[2 * m], 2**m * odd_factorial(2 * m - 1) ** 2) == k,
            f"even normalization, m={m}",
        )
        check(valuation_two(k) == (m & 1), f"even unit valuation, m={m}")

        h = f_finite(m)
        check(
            Fraction(q[2 * m + 1], 2**m * odd_factorial(2 * m + 1) ** 2) == h,
            f"odd normalization, m={m}",
        )
        if m % 2 == 0:
            check(valuation_two(h) == 0, f"even-m H unit, m={m}")
        else:
            check(
                valuation_two(h) == 1 + valuation_two_integer(m + 1),
                f"odd-m H valuation, m={m}",
            )

    # Exhaust the stated binomial Lipschitz estimate across both signs.
    lipschitz_checks = 0
    for left in range(-48, 49):
        for right in range(-48, 49):
            if left == right:
                continue
            delta_v = valuation_two_integer(left - right)
            for k in range(1, 33):
                difference = choose_integer(left, k) - choose_integer(right, k)
                if difference:
                    check(
                        valuation_two_integer(difference)
                        >= delta_v - (k.bit_length() - 1),
                        f"binomial Lipschitz ({left},{right},{k})",
                    )
                lipschitz_checks += 1

    audit_partial_fractions()

    factor_checks = 0
    for r in range(48):
        for t in range(49):  # includes t=0, hence upper argument -1
            check(paired_term(r, t) == paired_factor(r, t), f"pair ({r},{t})")
            factor_checks += 1

    high_checks = 0
    for s in range(49):
        for t in range(s + 1, 49):
            d_v = valuation_two_integer(t - s)
            low = paired_term(0, t) - paired_term(0, s)
            low += paired_term(1, t) - paired_term(1, s)
            check(valuation_two(low) == 2 + d_v, f"low parity ({s},{t})")
            for r in range(2, 35):
                difference = paired_term(r, t) - paired_term(r, s)
                if difference:
                    check(
                        valuation_two(difference) >= 3 + d_v,
                        f"high divisibility r={r}, ({s},{t})",
                    )
                high_checks += 1

    # Independent finite shadows for F(-1)=0 and Log(+-i)=0.
    endpoint = Fraction(0)
    endpoint_rows: list[tuple[int, int]] = []
    for j in range(256):
        endpoint += coefficient(j)
        if j in (1, 3, 7, 15, 31, 63, 127, 255):
            endpoint_rows.append((j, valuation_two(endpoint)))
    check(
        all(b[1] > a[1] for a, b in zip(endpoint_rows, endpoint_rows[1:])),
        "endpoint dyadic partial sums",
    )

    log_rows: list[tuple[int, Fraction]] = []
    w = (Fraction(-1), Fraction(1))  # i - 1
    partial = (Fraction(0), Fraction(0))
    for index in range(1, 256):
        sign = 1 if index % 2 else -1
        partial = gadd(partial, gscale(gpower(w, index), Fraction(sign, index)))
        if index in (7, 15, 31, 63, 127, 255):
            log_rows.append((index, gaussian_valuation(partial)))
    check(
        all(b[1] > a[1] for a, b in zip(log_rows, log_rows[1:])),
        "local logarithm partial sums at i",
    )

    print(
        "PASS: independent exact normalization, signed-binomial boundary, "
        f"{lipschitz_checks} Lipschitz, {factor_checks} factorization, and "
        f"{high_checks} high-pair checks"
    )
    print(
        "PASS: equation (18) and repaired primitive (18a); the superseded "
        "primitive is correctly rejected"
    )
    print(
        "EXPERIMENT endpoint: "
        + ", ".join(f"{index}:{value}" for index, value in endpoint_rows)
    )
    print(
        "EXPERIMENT Log(i): "
        + ", ".join(f"{index}:{value}" for index, value in log_rows)
    )


if __name__ == "__main__":
    main()
