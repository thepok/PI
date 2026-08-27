#!/usr/bin/env python3
"""Independent self-audit replay for the BBP weighted-sum report.

This implementation imports neither the primary checker nor its helpers.
All assertions are exact.  It audits identities and separator scopes; it
does not prove cancellation, a fixed return, V1, or normality of pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, log10
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parents[2]
RNG = Random(0x5E1FA7D1)

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_attack.md":
        "33fe8e27130e7ed4acfb8b9ee017cb17df2a612a1a4674b5d5ccef88c4404713",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_check.py":
        "70a4ca42b1bd2c6ec212587662ab667b8c1940a3a95d94b03a1f054ba71066bc",
    "TheoryLib/PiLacunaryNearReturnSparsity/T13IteratedLagResonance.lean":
        "14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13",
    "TheoryLib/PiDigits/T26WeylCancellationV1.lean":
        "3825d0dcb5bd4d22ffa3cd8853db1bbf79c2ad1faa4ff0f1db96dbf7efc11871",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(relative: str) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def v2(integer: int) -> int:
    require(integer != 0, "v2 domain")
    integer = abs(integer)
    answer = 0
    while integer % 2 == 0:
        integer //= 2
        answer += 1
    return answer


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def circle(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def row_upper(depth: int) -> int:
    """Exact floor(log_10(16^M))."""

    value = 16**depth
    estimate = int(log10(16) * depth)
    power = 10**estimate
    while power > value:
        estimate -= 1
        power //= 10
    while 10 * power <= value:
        estimate += 1
        power *= 10
    return estimate


def A(index: int) -> int:
    require(index >= 4, "A index")
    numerator = 10**index - 16
    require(numerator % 16 == 0, "A integrality")
    return numerator // 16


def coefficient(index: int) -> Fraction:
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


# Re-derive the elementary coefficient and tail constants independently.
coefficient_checks = 0
for k in range(513):
    combined = Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )
    require(coefficient(k) == combined > 0, f"four-pole coefficient k={k}")
    if k:
        require(combined < Fraction(1, k * k), f"coefficient majorant k={k}")
    coefficient_checks += 1
require(Fraction(1, 15) / (1 - Fraction(5, 8)) == Fraction(8, 45), "tail sum")


# Exact A_n algebra, row endpoints, and the inverse endpoint used in the
# all-depth block-to-global Weyl argument.
row_checks = 0
for depth in range(5, 301):
    upper = row_upper(depth)
    require(10**upper <= 16**depth < 10 ** (upper + 1), "exact row upper")
    require(upper >= depth, "nonempty proportional row")
    for n in (depth, upper):
        require(A(n) + 1 == 10**n // 16, "A plus one")
        require(A(n) % 3 == 0, "A divisible by three")
        require(A(n + 1) == 10 * A(n) + 9, "A affine recurrence")
        row_checks += 1

inverse_endpoint_checks = 0
lam = log10(16)
for endpoint in range(20, 10_001, 7):
    depth = int((endpoint - 1) / lam)
    while 16**depth < 10 ** (endpoint - 1):
        depth += 1
    while depth and 16 ** (depth - 1) >= 10 ** (endpoint - 1):
        depth -= 1
    reached = row_upper(depth) + 1
    require(reached in (endpoint, endpoint + 1), "inverse row endpoint")
    require(depth < endpoint, "geometric backward step")
    inverse_endpoint_checks += 1


# Direct subset expansion of arbitrary finite differences.  This is
# independent of the recursive coefficient implementation in the primary
# checker.
iterated_difference_checks = 0
for trial in range(2_000):
    n = RNG.randrange(5, 80)
    h = RNG.choice([value for value in range(-100, 101) if value])
    lags = tuple(RNG.randrange(1, 13) for _ in range(RNG.randrange(1, 9)))
    scalar = Fraction(RNG.randrange(1, 10_000), RNG.randrange(1, 10_000))
    left = Fraction(0)
    for mask in range(1 << len(lags)):
        shift = sum(lags[index] for index in range(len(lags)) if mask >> index & 1)
        selected = mask.bit_count()
        sign = -1 if (len(lags) - selected) % 2 else 1
        left += sign * h * (10 ** (n + shift) - 16) * scalar
    multiplier = 1
    for lag in lags:
        multiplier *= 10**lag - 1
    right = h * 10**n * scalar * multiplier
    require(left == right, f"subset difference trial={trial}")
    require(multiplier % 2 == 1, "all promoted factors odd")
    iterated_difference_checks += 1


# Boundary behind the two-adic nontermination statement for arbitrary fixed
# frequencies.  This verifies the exact exponent inequality, not a Fourier
# estimate.
dyadic_boundary_checks = 0
for depth in range(5, 1_001):
    upper = row_upper(depth)
    k_exponent = 4 * depth - v2(depth + 1)
    for h in (-1000, -37, -2, -1, 1, 2, 37, 1000):
        if k_exponent - upper - v2(h) > 0:
            require(k_exponent - upper - v2(h) >= 1, "remaining dyadic exponent")
            dyadic_boundary_checks += 1


SMALL_ODD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)


def random_odd_modulus() -> int:
    factors = RNG.sample(SMALL_ODD_PRIMES, RNG.randrange(1, 7))
    modulus = 1
    for prime in factors:
        modulus *= prime ** RNG.randrange(1, 4)
    return modulus


def nearby_with_parity(target: Fraction, modulus: int, odd: bool) -> int:
    base = target.numerator // target.denominator
    candidates = {
        (base + offset) % modulus
        for offset in range(-4, 5)
        if bool((base + offset) % 2) == odd
    }
    require(candidates, "nearby parity grid point")
    return min(candidates, key=lambda value: circle(Fraction(value, modulus) - target / modulus))


# Independent randomized audit of the full-odd-coordinate dyadic selector.
dyadic_selector_checks = 0
for trial in range(1_000):
    depth = RNG.randrange(5, 181)
    r = v2(depth + 1)
    D = 1 << (4 * depth - r - 4)
    Q = 1 << (3 * depth - r)
    require(D % Q == 0, "Q divides D")
    R = random_odd_modulus()
    c = RNG.randrange(1, R)
    while gcd(c, R) != 1:
        c = RNG.randrange(1, R)
    actual_w = RNG.randrange(1, D, 2)

    offset = Fraction(10**depth * c, 16 * R)
    scaled_target = ((Fraction(1, 9) - offset) % 1) * Q
    base = scaled_target.numerator // scaled_target.denominator
    odd_numerators = {
        (base + shift) % Q for shift in range(-3, 4) if (base + shift) % 2
    }
    u = min(
        odd_numerators,
        key=lambda value: circle(offset + Fraction(value, Q) - Fraction(1, 9)),
    )
    seed_error = circle(offset + Fraction(u, Q) - Fraction(1, 9))
    require(seed_error <= Fraction(1, Q), "odd-grid radius")

    base_w = u * pow(5**depth, -1, Q) % Q
    copies = D // Q
    estimate = (actual_w - base_w) // Q
    copy_candidates = {
        max(0, min(copies - 1, estimate + shift)) for shift in range(-2, 3)
    }
    selected_w = min(
        (base_w + copy * Q for copy in copy_candidates),
        key=lambda value: abs(value - actual_w),
    )
    require(selected_w % 2 == 1 and abs(selected_w - actual_w) <= Q, "nearby odd selector")

    theta = Fraction(selected_w, D) + Fraction(c, R)
    beta = Fraction(10**depth, 16) * theta
    require(circle(beta - Fraction(1, 9)) == seed_error, "starting seed identity")
    numerator = R * selected_w + D * c
    require(gcd(numerator, 2 * R) == 1, "selector reducedness")
    require(
        abs(Fraction(numerator, 16 * D * R)
            - Fraction(R * actual_w + D * c, 16 * D * R))
        <= Fraction(1, 2**depth),
        "nearby rational truncation",
    )

    upper = row_upper(depth)
    for n in range(depth, upper + 1):
        error = circle(Fraction(10**n, 16) * theta - Fraction(1, 9))
        require(error <= Fraction(depth + 1, 5**depth), "uniform selected orbit")
        for h in (-7, -1, 1, 7):
            common_error = circle(h * (A(n) * theta - (Fraction(1, 9) - theta)))
            require(
                common_error <= abs(h) * Fraction(depth + 1, 5**depth),
                "common unit phase bound",
            )
        dyadic_selector_checks += 1


# Independent randomized audit of the coarse high-coordinate separator.
coarse_separator_checks = 0
coordinate_primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
for trial in range(500):
    depth = RNG.randrange(5, 181)
    chosen = RNG.sample(coordinate_primes, RNG.randrange(0, 8))
    S = 1
    Xi = Fraction(0)
    gammas: dict[int, int] = {}
    for prime in chosen:
        gamma = RNG.randrange(1, prime)
        gammas[prime] = gamma
        Xi += Fraction(gamma, prime)
        S *= prime

    C = 1
    exponent = 0
    while C < (depth + 1) ** 3:
        C *= 3
        exponent += 1
    require(C < 3 * (depth + 1) ** 3, "minimal cofactor power")
    require(exponent <= 4 * floor_log(3, 8 * depth + 5), "cofactor exponent allowance")
    D = 1 << (4 * depth - v2(depth + 1) - 4)
    modulus = D * C
    target = ((Fraction(1, 3) - Xi) % 1) * modulus
    base = target.numerator // target.denominator
    reduced = {
        (base + shift) % modulus
        for shift in range(-7, 8)
        if gcd((base + shift) % modulus, 6) == 1
    }
    t = min(
        reduced,
        key=lambda value: circle(Xi + Fraction(value, modulus) - Fraction(1, 3)),
    )
    total_error = circle(Xi + Fraction(t, modulus) - Fraction(1, 3))
    require(total_error <= Fraction(2, modulus), "mod-six grid radius")
    w = t * pow(C, -1, D) % D
    eta = t * pow(D, -1, C) % C
    require(w % 2 == 1 and gcd(eta, C) == 1, "coarse reduced selectors")

    R = S * C
    c_fraction = ((Xi + Fraction(eta, C)) % 1) * R
    require(c_fraction.denominator == 1, "coarse CRT numerator")
    c = c_fraction.numerator
    require(gcd(c, R) == 1, "coarse odd quotient reduced")
    for prime, gamma in gammas.items():
        require(c * pow(R // prime, -1, prime) % prime == gamma, "high coordinate")
    require(c * pow(S, -1, C) % C == eta, "cofactor coordinate")

    theta = (Xi + Fraction(w, D) + Fraction(eta, C)) % 1
    upper = row_upper(depth)
    for n in range(depth, upper + 1):
        require(circle(A(n) * theta) <= Fraction(2, (depth + 1) ** 2), "coarse resonant row")
        coarse_separator_checks += 1


pins = {}
for relative, expected in PINS.items():
    actual = digest(relative)
    require(actual == expected, f"pin mismatch: {relative}: {actual}")
    pins[relative] = actual


print(json.dumps({
    "status": "PASS",
    "claim_label": "experiment",
    "audited_report_label": "proof sketch",
    "asserts_weighted_sum_bound": False,
    "asserts_fourier_limit": False,
    "asserts_fixed_return": False,
    "asserts_v1": False,
    "exact_check_counts": {
        "coefficient_and_majorant": coefficient_checks,
        "row_algebra": row_checks,
        "inverse_endpoint": inverse_endpoint_checks,
        "iterated_difference": iterated_difference_checks,
        "dyadic_boundary": dyadic_boundary_checks,
        "full_odd_coordinate_selector": dyadic_selector_checks,
        "coarse_coordinate_separator": coarse_separator_checks,
    },
    "scope": {
        "differencing": "frequency promotion, not cancellation",
        "full_odd_selector": "varies the dyadic carry and is not the actual BBP row",
        "coarse_separator": "varies unresolved selectors and is not the actual BBP row",
        "all_depth_blocks": "equivalent to normality only when convergence holds for every M",
        "subsequence_blocks": "does not assert normality",
    },
    "source_pins": pins,
    "warning": "PASS audits the reductions and separators, not equation (43) or V1.",
}, indent=2, sort_keys=True))
