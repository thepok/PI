#!/usr/bin/env python3
"""Exact finite replay for the Gauss--Lambert all-depth 2-adic proof sketch.

The infinite endpoint identity and the all-depth estimates are mathematical
arguments in the companion report.  This script checks their algebraic
normalizations, finite shadows, and all congruence formulas with exact Python
integers/Fractions.  Finite checks are not a proof of the infinite statements.
"""

from fractions import Fraction
from math import comb, factorial


def require(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def v2_int(value: int) -> int:
    require(value != 0, "v2_int called at zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def v2(value: Fraction | int) -> int:
    value = Fraction(value)
    require(value != 0, "v2 called at zero")
    return v2_int(value.numerator) - v2_int(value.denominator)


def odd_double_factorial(index: int) -> int:
    """Return index!! for odd index >= -1, with (-1)!! = 1."""
    require(index >= -1 and index % 2 == 1, "odd double factorial domain")
    answer = 1
    for value in range(1, index + 1, 2):
        answer *= value
    return answer


def generalized_choose(value: int, index: int) -> int:
    """Integer-valued binomial coefficient for integral upper argument."""
    require(index >= 0, "negative lower binomial index")
    if value >= 0:
        return comb(value, index) if index <= value else 0
    # binom(-a,k) = (-1)^k binom(a+k-1,k).
    return (-1) ** index * comb(-value + index - 1, index)


def c(index: int) -> Fraction:
    return Fraction(factorial(index), odd_double_factorial(2 * index + 1))


def q_values(limit: int) -> list[int]:
    values = [1, 1]
    for n in range(2, limit + 1):
        values.append((2 * n - 1) * values[-1] + (n - 1) ** 2 * values[-2])
    return values[: limit + 1]


def q_binomial_sum(n: int) -> int:
    total = sum(
        (
            Fraction(
                factorial(n) ** 2,
                2**k * factorial(k) ** 2 * factorial(n - 2 * k),
            )
            for k in range(n // 2 + 1)
        ),
        Fraction(0),
    )
    require(total.denominator == 1, f"integral Q binomial sum at {n}")
    return total.numerator


def k_nonnegative(m: int) -> Fraction:
    return sum(
        (
            Fraction(
                factorial(j) * comb(m, j) ** 2,
                odd_double_factorial(2 * j - 1),
            )
            for j in range(m + 1)
        ),
        Fraction(0),
    )


def h_nonnegative(m: int) -> Fraction:
    return sum(
        (c(j) * comb(m, j) ** 2 for j in range(m + 1)),
        Fraction(0),
    )


def f_truncated(value: int, cutoff: int) -> Fraction:
    return sum(
        (c(j) * generalized_choose(value, j) ** 2 for j in range(cutoff + 1)),
        Fraction(0),
    )


def psi(r: int, t: int) -> Fraction:
    x = 2 * t - 1
    return (
        c(2 * r) * generalized_choose(x, 2 * r) ** 2
        + c(2 * r + 1) * generalized_choose(x, 2 * r + 1) ** 2
    )


def psi_factored(r: int, t: int) -> Fraction:
    x = 2 * t - 1
    phi = generalized_choose(x, 2 * r)
    m_poly = 6 * r * r - 4 * r * t + 7 * r + 2 * t * t - 2 * t + 2
    denominator = (
        odd_double_factorial(4 * r + 1) * (2 * r + 1) * (4 * r + 3)
    )
    return Fraction(2 * factorial(2 * r) * phi * phi * m_poly, denominator)


def expected_q_extra(n: int) -> int:
    residue = n % 4
    if residue in (0, 1):
        return 0
    if residue == 2:
        return 1
    return v2_int(n + 1)


def main() -> None:
    # Recurrence, EGF coefficient formula, and the claimed all-index valuation.
    q = q_values(512)
    for n, value in enumerate(q):
        require(value == q_binomial_sum(n), f"Q binomial formula at {n}")
        if n:
            require(
                v2_int(value) == n // 2 + expected_q_extra(n),
                f"Q valuation at {n}",
            )

    # Even-index normalization (9), directly and with exact Fractions.
    for m in range(129):
        k_value = k_nonnegative(m)
        normalized = (
            2**m * odd_double_factorial(2 * m - 1) ** 2 * k_value
        )
        require(normalized.denominator == 1, f"even Q integrality at {m}")
        require(
            q[2 * m] == normalized.numerator,
            f"even Q normalization at {m}",
        )

    # Odd-index normalization Q_(2m+1)=2^m(2m+1)!! R_m and R_m=(2m+1)!! H_m.
    for m in range(128):
        h = h_nonnegative(m)
        r = h * odd_double_factorial(2 * m + 1)
        require(r.denominator == 1, f"R integrality at {m}")
        require(
            q[2 * m + 1]
            == 2**m * odd_double_factorial(2 * m + 1) * r.numerator,
            f"odd Q normalization at {m}",
        )

    # The endpoint partial sums approach zero 2-adically.  This is a finite
    # shadow only; the report proves the limit using a p-adic logarithmic
    # antiderivative.
    endpoint = Fraction(0)
    endpoint_minima = []
    running_best = -1
    for j in range(128):
        endpoint += c(j)
        if endpoint:
            running_best = max(running_best, v2(endpoint))
        if j in (1, 3, 7, 15, 31, 63, 127):
            endpoint_minima.append((j, v2(endpoint)))
    require(
        all(right[1] > left[1] for left, right in zip(endpoint_minima, endpoint_minima[1:])),
        "endpoint dyadic subsequence has strictly rising valuations",
    )

    # Consecutive-pair factorization, including the x=-1 endpoint t=0.
    for r in range(40):
        for t in range(40):
            require(psi(r, t) == psi_factored(r, t), f"pair factor r={r},t={t}")

    # The exact scaled-isometry shadow.  For positive t the infinite F series
    # truncates to H_(2t-1); t=0 is represented by a sufficiently long endpoint
    # partial sum and is deliberately not asserted as exact by this script.
    h_odd = {t: h_nonnegative(2 * t - 1) for t in range(1, 65)}
    pair_checks = 0
    for s in range(1, 65):
        for t in range(s + 1, 65):
            require(
                v2(h_odd[t] - h_odd[s]) == 2 + v2_int(t - s),
                f"scaled isometry at ({s},{t})",
            )
            pair_checks += 1

    # Low-pair parity and high-pair divisibility used in the proof.
    local_checks = 0
    for s in range(40):
        for t in range(s + 1, 40):
            d = t - s
            low = psi(0, t) - psi(0, s) + psi(1, t) - psi(1, s)
            require(v2(low) == 2 + v2_int(d), f"low pair parity at ({s},{t})")
            for r in range(2, 24):
                high = psi(r, t) - psi(r, s)
                if high:
                    require(
                        v2(high) >= 3 + v2_int(d),
                        f"high pair bound r={r},({s},{t})",
                    )
                local_checks += 1

    print(
        "PASS: exact Q/coefficient normalizations, the mod-4 valuation law "
        f"through n=512, {pair_checks} odd-shadow isometry pairs, and "
        f"{local_checks} paired-term divisibility checks"
    )
    print(
        "EXPERIMENT: endpoint partial-sum valuations at N=2^k-1 are "
        + ", ".join(f"{n}:{valuation}" for n, valuation in endpoint_minima)
    )


if __name__ == "__main__":
    main()
