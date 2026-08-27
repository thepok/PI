#!/usr/bin/env python3
"""Independent exact replay for the BBP weighted-sum obstruction.

This file imports neither earlier checker.  It checks finite algebra,
endpoint handling, CRT reducedness, and adversarial selector instances using
integers and Fraction.  It proves no asymptotic cancellation, normality,
fixed return, or occurrence statement for pi.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parents[2]
RNG = Random(0x1D3BB04243)

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_attack.md":
        "33fe8e27130e7ed4acfb8b9ee017cb17df2a612a1a4674b5d5ccef88c4404713",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_check.py":
        "70a4ca42b1bd2c6ec212587662ab667b8c1940a3a95d94b03a1f054ba71066bc",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_self_audit.md":
        "e4a88f502f710165d06faa2926d654ff5020cae9570acd01c680e3774f4a073d",
    "work/ultrapi-resume/bbp_weighted_sum_differencing_self_audit_check.py":
        "39665d0cc03870755e0a3b9f3ab84fb727d128c22bdcd9f51d35804f4b4bf512",
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


def v2(value: int) -> int:
    require(value != 0, "v2 domain")
    value = abs(value)
    answer = 0
    while value % 2 == 0:
        answer += 1
        value //= 2
    return answer


def floor_log(base: int, value: int) -> int:
    require(base >= 2 and value >= 1, "floor-log domain")
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def circle(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def coefficient(index: int) -> Fraction:
    require(index >= 0, "coefficient domain")
    return (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )


def A(index: int) -> int:
    require(index >= 4, "A-index domain")
    numerator = 10**index - 16
    require(numerator % 16 == 0, "A-index integrality")
    return numerator // 16


def row_upper(depth: int) -> int:
    """Exact floor(log_10(16^depth)), with no floating logarithm."""

    require(depth >= 1, "row-upper domain")
    return len(str(16**depth)) - 1


def inverse_endpoint_depth(endpoint: int) -> int:
    """Exact ceil((endpoint-1)/log_10(16))."""

    require(endpoint >= 2, "inverse endpoint domain")
    target = 10 ** (endpoint - 1)
    low, high = 0, endpoint
    while low < high:
        middle = (low + high) // 2
        if 16**middle >= target:
            high = middle
        else:
            low = middle + 1
    return low


def nearest_odd_seed(offset: Fraction, modulus: int) -> tuple[int, Fraction]:
    """Odd u modulo a two-power with offset+u/modulus nearest 1/9."""

    require(modulus >= 2 and modulus & (modulus - 1) == 0, "seed modulus")
    scaled = ((Fraction(1, 9) - offset) % 1) * modulus
    floor_value = scaled.numerator // scaled.denominator
    candidates = {
        (floor_value + shift) % modulus
        for shift in range(-4, 5)
        if (floor_value + shift) % 2
    }
    require(candidates, "odd seed candidates")
    selected = min(
        candidates,
        key=lambda value: circle(offset + Fraction(value, modulus) - Fraction(1, 9)),
    )
    error = circle(offset + Fraction(selected, modulus) - Fraction(1, 9))
    return selected, error


def nearest_representative(residue: int, modulus: int, bound: int, target: int) -> int:
    """Nearest representative of residue mod modulus in [0,bound)."""

    require(bound % modulus == 0 and 0 <= residue < modulus, "representative domain")
    copies = bound // modulus
    estimate = (target - residue) // modulus
    candidates = {
        max(0, min(copies - 1, estimate + shift)) for shift in range(-3, 4)
    }
    return min(
        (residue + copy * modulus for copy in candidates),
        key=lambda value: abs(value - target),
    )


def nearest_mod_six(target: Fraction, modulus: int) -> tuple[int, Fraction]:
    """Nearest numerator coprime to 6 on a modulus-dividing grid."""

    require(modulus % 6 == 0, "mod-six grid domain")
    scaled = (target % 1) * modulus
    floor_value = scaled.numerator // scaled.denominator
    candidates = {
        (floor_value + shift) % modulus
        for shift in range(-8, 9)
        if gcd((floor_value + shift) % modulus, 6) == 1
    }
    require(candidates, "mod-six candidates")
    selected = min(
        candidates,
        key=lambda value: circle(Fraction(value, modulus) - target),
    )
    return selected, circle(Fraction(selected, modulus) - target)


# Coefficient identity, positivity, and the exact k^{-2} majorant.
coefficient_checks = 0
for index in range(641):
    combined = Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1) * (4 * index + 3) * (8 * index + 1) * (8 * index + 5),
    )
    require(coefficient(index) == combined > 0, f"coefficient index={index}")
    if index:
        # The numerator of 1/index^2-combined is
        # 392k^4+873k^3+665k^2+194k+15.
        gap_numerator = (
            392 * index**4 + 873 * index**3 + 665 * index**2 + 194 * index + 15
        )
        require(gap_numerator > 0 and combined < Fraction(1, index * index), "majorant")
    coefficient_checks += 1


MAX_DEPTH = 96
partials: list[Fraction] = []
partial = Fraction(0)
for index in range(MAX_DEPTH + 65):
    partial += coefficient(index) / 16**index
    partials.append(partial)


# Exact row boundaries, collapse, and finite-tail instances of the uniform
# transfer inequality.  The report supplies the infinite geometric-tail proof.
row_collapse_checks = 0
finite_tail_checks = 0
for depth in range(5, MAX_DEPTH + 1):
    upper = row_upper(depth)
    require(10**upper <= 16**depth < 10 ** (upper + 1), "exact row upper")
    require(upper >= depth, "nonempty proportional row")
    truncation = partials[depth]
    finite_tail = partials[depth + 64] - truncation
    for n in range(depth, upper + 1):
        current_A = A(n)
        require(current_A + 1 == 10**n // 16, "A plus one")
        require(current_A % 3 == 0, "three divides A")
        require(A(n + 1) == 10 * current_A + 9, "A affine recurrence")
        require(current_A * 16 * truncation == (10**n - 16) * truncation, "collapse")
        finite_error = (10**n - 16) * finite_tail
        require(Fraction(0) <= finite_error <= Fraction(1, 15 * (depth + 1) ** 2), "tail")
        row_collapse_checks += 1
        finite_tail_checks += 1


# The inverse endpoint needed by block-to-global cancellation is N or N+1,
# and the next recursion depth is genuinely smaller.
inverse_endpoint_checks = 0
for endpoint in range(8, 2_001):
    depth = inverse_endpoint_depth(endpoint)
    reached = row_upper(depth) + 1
    require(reached in (endpoint, endpoint + 1), f"inverse endpoint N={endpoint}")
    require(depth < endpoint, f"geometric recursion N={endpoint}")
    inverse_endpoint_checks += 1


# Direct subset expansion of arbitrary finite differences, plus all legal
# first-correlation endpoint ranges in the finite test window.
difference_checks = 0
correlation_boundary_checks = 0
for trial in range(3_000):
    depth = RNG.randrange(5, MAX_DEPTH + 1)
    n = RNG.randrange(depth, row_upper(depth) + 1)
    h = RNG.choice([value for value in range(-200, 201) if value])
    scalar = partials[depth]
    lags = tuple(RNG.randrange(1, 15) for _ in range(RNG.randrange(1, 9)))
    left = Fraction(0)
    for mask in range(1 << len(lags)):
        shift = sum(lags[index] for index in range(len(lags)) if mask >> index & 1)
        sign = -1 if (len(lags) - mask.bit_count()) % 2 else 1
        left += sign * h * (10 ** (n + shift) - 16) * scalar
    multiplier = 1
    for lag in lags:
        multiplier *= 10**lag - 1
    require(left == h * 10**n * scalar * multiplier, f"difference trial={trial}")
    require(multiplier % 2 == 1, "odd promoted multiplier")
    difference_checks += 1

for depth in range(5, MAX_DEPTH + 1):
    upper = row_upper(depth)
    scalar = partials[depth]
    for lag in range(1, upper - depth + 1):
        promoted = 7 * (10**lag - 1)
        for n in (depth, upper - lag):
            left = 7 * ((10 ** (n + lag) - 16) - (10**n - 16)) * scalar
            right = promoted * (10**n - 16) * scalar + 16 * promoted * scalar
            require(left == right, "correlation endpoint")
            correlation_boundary_checks += 1


# Actual BBP reduced coordinates and an independent additive-CRT replay.
all_primes = primes_through(8 * MAX_DEPTH + 5)
actual_rows: dict[int, tuple[int, int, int, int, Fraction, dict[int, int]]] = {}
actual_coordinate_checks = 0
dyadic_exactness_checks = 0
for depth in range(5, MAX_DEPTH + 1):
    truncation = partials[depth]
    k_exponent = v2(truncation.denominator)
    require(k_exponent == 4 * depth - v2(depth + 1), "exact dyadic denominator")
    D = 1 << (k_exponent - 4)
    R = truncation.denominator >> k_exponent
    P = truncation.numerator
    w = P * pow(R, -1, D) % D
    require(w % 2 == 1, "actual dyadic coordinate odd")
    require((P - R * w) % D == 0, "actual coordinate divisibility")
    c = (P - R * w) // D
    require(gcd(c, R) == 1, "actual odd quotient reduced")
    require(Fraction(w, D) + Fraction(c, R) == 16 * truncation, "actual split")

    S = 1
    Xi = Fraction(0)
    gammas: dict[int, int] = {}
    if depth >= 48:
        remainder = R
        for prime in all_primes:
            while remainder % prime == 0:
                remainder //= prime
        require(remainder == 1, "odd denominator support bound")
        for prime in all_primes:
            if prime <= depth or R % prime:
                continue
            require((R // prime) % prime != 0, "high prime exponent one")
            gamma = c * pow(R // prime, -1, prime) % prime
            require(gamma != 0, "high coordinate nonzero")
            gammas[prime] = gamma
            Xi += Fraction(gamma, prime)
            S *= prime
        require(R % S == 0 and gcd(S, R // S) == 1, "actual CRT split")
        C = R // S
        eta = 0 if C == 1 else c * pow(S, -1, C) % C
        require((Fraction(c, R) - Xi - Fraction(eta, C)).denominator == 1, "additive CRT")
        for n in range(depth, row_upper(depth) + 1):
            split = Fraction(w, D) + Xi + Fraction(eta, C)
            require((A(n) * (16 * truncation - split)).denominator == 1, "CRT phase")
            actual_coordinate_checks += 1

    for h in (-127, -8, -1, 1, 8, 127):
        for n in (depth, row_upper(depth)):
            promoted = h * (10**3 - 1) * 10**n * truncation
            expected = max(0, k_exponent - n - v2(h))
            require(v2(promoted.denominator) == expected, "residual dyadic exponent")
            if expected:
                require(promoted.denominator != 1, "no dyadic annihilation")
            dyadic_exactness_checks += 1
    actual_rows[depth] = (R, c, w, D, Xi, gammas)


# Full-odd-coordinate selector, including actual carries, endpoint carries,
# wraparound seed classes, reducedness, and every exponent in each row.
dyadic_selector_checks = 0
for depth in range(5, 81):
    R, c, actual_w, D, _Xi, _gammas = actual_rows[depth]
    r = v2(depth + 1)
    Q = 1 << (3 * depth - r)
    require(D // Q == 1 << (depth - 4), "selector quotient")
    baselines = {actual_w, 1, D - 1}
    for _ in range(2):
        baselines.add(RNG.randrange(1, D, 2))
    offset = Fraction(10**depth * c, 16 * R)
    seed_numerator, seed_error = nearest_odd_seed(offset, Q)
    require(seed_error <= Fraction(1, Q), "odd-grid covering radius")
    selected_class = seed_numerator * pow(5**depth, -1, Q) % Q
    require(selected_class % 2 == 1, "selected class odd")
    for baseline_w in baselines:
        selected_w = nearest_representative(selected_class, Q, D, baseline_w)
        require(0 <= selected_w < D and selected_w % 2 == 1, "selected representative")
        require(abs(selected_w - baseline_w) <= Q, "endpoint-safe representative bound")
        theta = Fraction(selected_w, D) + Fraction(c, R)
        seed = Fraction(10**depth, 16) * theta
        require(circle(seed - Fraction(1, 9)) == seed_error, "seed identity")

        selected_P = R * selected_w + D * c
        baseline_P = R * baseline_w + D * c
        require(gcd(selected_P, 16 * D * R) == 1, "selected fraction reduced")
        require(gcd(baseline_P, 16 * D * R) == 1, "baseline fraction reduced")
        selected_B = Fraction(selected_P, 16 * D * R)
        baseline_B = Fraction(baseline_P, 16 * D * R)
        require(abs(selected_B - baseline_B) <= Fraction(1, 2**depth), "selector approximation")

        for n in range(depth, row_upper(depth) + 1):
            t = n - depth
            orbit_error = circle(Fraction(10**n, 16) * theta - Fraction(1, 9))
            require(orbit_error <= Fraction(10**t, Q), "propagated seed error")
            require(orbit_error <= Fraction(2**r, 5**depth), "row endpoint error")
            require(orbit_error <= Fraction(depth + 1, 5**depth), "uniform selector error")
            for h in (-31, -1, 1, 31):
                common_error = circle(h * (A(n) * theta - (Fraction(1, 9) - theta)))
                require(common_error <= abs(h) * Fraction(depth + 1, 5**depth), "common phase")
            dyadic_selector_checks += 1


# Exhaust the elementary mod-six covering lemma on many complete grids,
# including rational targets on both sides of the cyclic seam.
mod_six_cover_checks = 0
for multiplier in range(1, 81):
    modulus = 6 * multiplier
    units = [value for value in range(modulus) if gcd(value, 6) == 1]
    for denominator in (5, 7, 11):
        for numerator in range(denominator):
            target = Fraction(numerator, denominator)
            selected, error = nearest_mod_six(target, modulus)
            true_error = min(circle(Fraction(value, modulus) - target) for value in units)
            require(error == true_error <= Fraction(2, modulus), "mod-six covering lemma")
            require(gcd(selected, 6) == 1, "selected grid unit")
            mod_six_cover_checks += 1


# Coarse-coordinate separator with actual high coordinates and independently
# generated coordinate lists.  All phase and reducedness checks are exact.
coarse_selector_checks = 0
synthetic_primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
coarse_instances: list[tuple[int, dict[int, int]]] = []
for depth in range(48, 81):
    coarse_instances.append((depth, actual_rows[depth][5]))
for depth in range(5, 81):
    chosen = RNG.sample(synthetic_primes, RNG.randrange(0, 8))
    coarse_instances.append((depth, {prime: RNG.randrange(1, prime) for prime in chosen}))

for depth, gammas in coarse_instances:
    S = 1
    Xi = Fraction(0)
    for prime, gamma in gammas.items():
        require(prime > 3 and 0 < gamma < prime, "prescribed coordinate domain")
        S *= prime
        Xi += Fraction(gamma, prime)
    C = 1
    exponent = 0
    while C < (depth + 1) ** 3:
        C *= 3
        exponent += 1
    require(C < 3 * (depth + 1) ** 3, "minimal cofactor")
    require(exponent <= 4 * floor_log(3, 8 * depth + 5), "fixed-prime allowance")
    r = v2(depth + 1)
    D = 1 << (4 * depth - r - 4)
    require(gcd(S, D * C) == 1, "coarse modulus coprimality")

    grid_numerator, grid_error = nearest_mod_six(Fraction(1, 3) - Xi, D * C)
    require(grid_error <= Fraction(2, D * C), "coarse grid radius")
    w = grid_numerator * pow(C, -1, D) % D
    eta = grid_numerator * pow(D, -1, C) % C
    require(w % 2 == 1 and gcd(eta, C) == 1, "coarse selectors reduced")
    require((w * C + eta * D - grid_numerator) % (D * C) == 0, "coarse selector CRT")

    R = S * C
    c_fraction = ((Xi + Fraction(eta, C)) % 1) * R
    require(c_fraction.denominator == 1, "coarse odd numerator integral")
    c = c_fraction.numerator
    require(gcd(c, R) == 1, "coarse odd numerator reduced")
    for prime, gamma in gammas.items():
        require(c * pow(R // prime, -1, prime) % prime == gamma, "preserved high coordinate")
    require(c * pow(S, -1, C) % C == eta, "preserved cofactor coordinate")

    P = R * w + D * c
    require(gcd(P, 16 * D * R) == 1, "coarse full numerator reduced")
    theta = Fraction(P, D * R)
    require((theta - Xi - Fraction(w, D) - Fraction(eta, C)).denominator == 1, "coarse phase CRT")
    require(circle(theta - Fraction(1, 3)) == grid_error, "coarse target")
    upper = row_upper(depth)
    require(Fraction(2 * A(upper), D * C) < Fraction(2 ** (r + 1), C), "coarse endpoint strict bound")
    require(Fraction(2 ** (r + 1), C) <= Fraction(2, (depth + 1) ** 2), "coarse endpoint bound")
    for n in range(depth, upper + 1):
        phase_error = circle(A(n) * theta)
        require(phase_error <= A(n) * grid_error, "coarse error propagation")
        require(phase_error <= Fraction(2, (depth + 1) ** 2), "coarse uniform error")
        for h in (-31, -1, 1, 31):
            require(circle(h * A(n) * theta) <= Fraction(2 * abs(h), (depth + 1) ** 2), "coarse h-phase")
        coarse_selector_checks += 1


pins = {}
for relative, expected in PINS.items():
    actual = digest(relative)
    require(actual == expected, f"pin mismatch: {relative}: {actual}")
    pins[relative] = actual


print(json.dumps({
    "status": "PASS",
    "claim_label": "experiment",
    "audited_report_label": "proof sketch",
    "independent_of_other_checkers": True,
    "asserts_weighted_cancellation": False,
    "asserts_normality": False,
    "asserts_fixed_return": False,
    "asserts_v1": False,
    "exact_check_counts": {
        "coefficient_and_majorant": coefficient_checks,
        "row_collapse": row_collapse_checks,
        "finite_tail": finite_tail_checks,
        "inverse_normality_endpoint": inverse_endpoint_checks,
        "iterated_difference": difference_checks,
        "correlation_boundaries": correlation_boundary_checks,
        "actual_CRT_coordinates": actual_coordinate_checks,
        "dyadic_exactness": dyadic_exactness_checks,
        "full_odd_coordinate_selector": dyadic_selector_checks,
        "mod_six_covering": mod_six_cover_checks,
        "coarse_coordinate_selector": coarse_selector_checks,
    },
    "scope": {
        "all_depth_cancellation": "equivalent to base-10 normality via geometric endpoint recursion",
        "parent_subsequence_cancellation": "sufficient for a return but not asserted or proved",
        "differencing": "exact frequency promotion only",
        "full_odd_selector": "changes the actual dyadic carry",
        "coarse_selector": "changes unresolved selectors and violates the actual carry recurrence",
    },
    "source_pins": pins,
    "warning": "PASS verifies reductions and separators, not weighted cancellation, normality, fixed return, or V1.",
}, indent=2, sort_keys=True))
