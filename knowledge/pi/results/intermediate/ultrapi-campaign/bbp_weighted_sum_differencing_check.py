#!/usr/bin/env python3
"""Exact replay for the BBP weighted-sum differencing obstruction.

The exact checks validate finite identities, boundary cases, CRT
factorizations, and finite instances of a structural separator.  Numerical
Fourier output is diagnostic only.  Nothing here proves a Fourier limit,
fixed return, V1, or normality of pi.
"""

from __future__ import annotations

from cmath import exp
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, log10, pi
from pathlib import Path
from random import Random


ROOT = Path(__file__).resolve().parents[2]
RNG = Random(0xBBF04243)

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_actual_odd_quotient_check.py":
        "c5f55d07feb84aa53285c8e0aee0bf32654a1bd7aed207ad518acfc07941d053",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_check.py":
        "f75a1624116d2f1ab5a3f66620648d5656b512ffc11d342a0caf9e8fd7e29786",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(relative: str) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def valuation(integer: int, prime: int) -> int:
    require(integer != 0 and prime >= 2, "valuation domain")
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        integer //= prime
        answer += 1
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
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def coefficient(index: int) -> Fraction:
    require(index >= 0, "coefficient domain")
    split = (
        Fraction(4, 8 * index + 1)
        - Fraction(2, 8 * index + 4)
        - Fraction(1, 8 * index + 5)
        - Fraction(1, 8 * index + 6)
    )
    combined = Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )
    require(split == combined > 0, f"coefficient {index}")
    return combined


def circle(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def phase(frequency: int, value: Fraction) -> complex:
    return exp(2j * pi * frequency * float(value % 1))


def a_index(decimal_exponent: int) -> int:
    require(decimal_exponent >= 4, "A_n integrality domain")
    numerator = 10**decimal_exponent - 16
    require(numerator % 16 == 0, "A_n is integral")
    return numerator // 16


def difference_coefficients(lags: tuple[int, ...]) -> dict[int, int]:
    """Coefficients of Delta_{r_k} ... Delta_{r_1} f(n)."""

    coefficients = {0: 1}
    for lag in lags:
        require(lag >= 1, "positive differencing lag")
        updated: dict[int, int] = {}
        for shift, value in coefficients.items():
            updated[shift + lag] = updated.get(shift + lag, 0) + value
            updated[shift] = updated.get(shift, 0) - value
        coefficients = {shift: value for shift, value in updated.items() if value}
    return coefficients


MAX_DEPTH = 128
partials: list[Fraction] = []
partial = Fraction(0)
for depth in range(MAX_DEPTH + 33):
    partial += coefficient(depth) / 16**depth
    partials.append(partial)

primes = primes_through(8 * MAX_DEPTH + 5)


# A_{n+1}=10 A_n+9, A_n+1=10^n/16, and 3|A_n.
a_index_checks = 0
for n in range(4, 4 * MAX_DEPTH):
    current = a_index(n)
    require(current + 1 == 10**n // 16, f"A_n+1 at n={n}")
    require(a_index(n + 1) == 10 * current + 9, f"affine recurrence at n={n}")
    require(current % 3 == 0, f"3 divides A_n at n={n}")
    a_index_checks += 1


# The weighted CRT product in (42) is exactly the ordinary rational decimal
# Weyl block.  The rational finite-tail version also checks the explicit
# O(1/M^2) transfer constant without using stored digits of pi.
collapse_checks = 0
finite_tail_transfer_checks = 0
finite_fourier_diagnostics: dict[str, dict[str, float]] = {}
for depth in (8, 13, 21, 34, 55, 89, 128):
    truncation = partials[depth]
    deeper = partials[depth + 32]
    upper = int(log10(16) * depth)
    length = upper - depth + 1
    rational_sum = 0j
    deeper_sum = 0j
    for n in range(depth, upper + 1):
        A = a_index(n)
        theta = 16 * truncation
        require(A * theta == (10**n - 16) * truncation, "weighted-sum collapse")
        collapse_checks += 1

        finite_error = (10**n - 16) * (deeper - truncation)
        require(finite_error >= 0, "positive finite BBP tail")
        require(
            finite_error <= Fraction(1, 15 * (depth + 1) ** 2),
            "proportional finite-tail transfer",
        )
        finite_tail_transfer_checks += 1
        rational_sum += phase(1, (10**n - 16) * truncation)
        deeper_sum += phase(1, (10**n - 16) * deeper)
    finite_fourier_diagnostics[str(depth)] = {
        "row_length": length,
        "truncation_normalized_magnitude": abs(rational_sum) / length,
        "deeper_surrogate_normalized_magnitude": abs(deeper_sum) / length,
    }


# Every finite additive difference retains the same 10^n phase, with its
# frequency multiplied by odd integers 10^r-1.  Correlations are therefore
# truncated copies of the original family, not lower-degree base cases.
difference_checks = 0
correlation_checks = 0
for trial in range(1_200):
    depth = RNG.randrange(8, MAX_DEPTH + 1)
    truncation = partials[depth]
    n = RNG.randrange(depth, int(log10(16) * depth) + 1)
    h = RNG.choice([value for value in range(-50, 51) if value])
    lag_count = RNG.randrange(1, 8)
    lags = tuple(RNG.randrange(1, 10) for _ in range(lag_count))
    coefficients = difference_coefficients(lags)
    left = sum(
        value * h * (10 ** (n + shift) - 16) * truncation
        for shift, value in coefficients.items()
    )
    multiplier = 1
    for lag in lags:
        multiplier *= 10**lag - 1
    right = h * 10**n * truncation * multiplier
    require(left == right, f"iterated difference trial={trial}")
    require(multiplier % 2 == 1, "differencing multiplier remains odd")
    difference_checks += 1

    lag = lags[0]
    promoted_frequency = h * (10**lag - 1)
    correlation_phase = (
        h * (10 ** (n + lag) - 16) * truncation
        - h * (10**n - 16) * truncation
    )
    promoted_phase = (
        promoted_frequency * (10**n - 16) * truncation
        + 16 * promoted_frequency * truncation
    )
    require(correlation_phase == promoted_phase, f"correlation promotion trial={trial}")
    correlation_checks += 1


# For fixed h, the exact dyadic denominator proves that no finite sequence
# of positive lags can annihilate the phase throughout the proportional row:
# all 10^r-1 factors are odd, while a growing two-power remains below.
dyadic_nontermination_checks = 0
for depth in range(8, MAX_DEPTH + 1):
    truncation = partials[depth]
    expected_k = 4 * depth - valuation(depth + 1, 2)
    require(valuation(truncation.denominator, 2) == expected_k, "BBP dyadic exponent")
    upper = int(log10(16) * depth)
    for h in (-37, -2, -1, 1, 2, 37):
        remaining = expected_k - upper - valuation(h, 2)
        if remaining > 0:
            # Any product of 10^r-1 is odd and cannot alter this deficit.
            require(remaining >= 1, "unremoved two-adic denominator")
            dyadic_nontermination_checks += 1


# Reconstruct actual row CRT data for finite depths and verify the exact
# character product.  The high set p>M is used here because its survival is
# unconditional in these finite rows M>=48.
actual_crt_checks = 0
actual_rows: dict[int, tuple[int, int, int, int, dict[int, int], Fraction]] = {}
for depth in range(48, MAX_DEPTH + 1):
    truncation = partials[depth]
    k_exponent = valuation(truncation.denominator, 2)
    D = 1 << (k_exponent - 4)
    R = truncation.denominator >> k_exponent
    P = truncation.numerator
    w = (P * pow(R, -1, D)) % D
    c = (P - R * w) // D
    require(gcd(c, R) == 1 and w % 2 == 1, "reduced row coordinates")

    S = 1
    gammas: dict[int, int] = {}
    Xi = Fraction(0)
    for prime_value in primes:
        if prime_value <= depth or R % prime_value:
            continue
        require((R // prime_value) % prime_value != 0, "high prime exponent one")
        gamma = c * pow(R // prime_value, -1, prime_value) % prime_value
        require(gamma != 0, "high coordinate survives")
        gammas[prime_value] = gamma
        Xi += Fraction(gamma, prime_value)
        S *= prime_value
    require(R % S == 0 and gcd(S, R // S) == 1, "high CRT split")
    C = R // S
    eta = 0 if C == 1 else c * pow(S, -1, C) % C
    require((Fraction(c, R) - Xi - Fraction(eta, C)) % 1 == 0, "additive CRT")
    theta = Fraction(w, D) + Fraction(c, R)
    for n in (depth, int(log10(16) * depth)):
        A = a_index(n)
        split_phase = A * (Fraction(w, D) + Xi + Fraction(eta, C))
        require((A * theta - split_phase) % 1 == 0, "CRT character product")
        actual_crt_checks += 1
    actual_rows[depth] = (R, c, w, S, gammas, Xi)


# A sharper one-coordinate separator fixes the entire actual odd quotient
# c/R and varies only the odd dyadic coordinate w.  At time M the available
# dyadic grid has denominator 2^(3M-v2(M+1)), enough to shadow the fixed
# decimal point 1/9 throughout the whole proportional row with exponentially
# small error.  The selected w is not the actual BBP carry coordinate.
dyadic_selector_checks = 0
dyadic_selector_diagnostics: dict[str, dict[str, float | int]] = {}
for depth in range(48, MAX_DEPTH + 1):
    R, c, actual_w, _S, _gammas, _Xi = actual_rows[depth]
    r = valuation(depth + 1, 2)
    D = 1 << (4 * depth - r - 4)
    start_grid = 1 << (3 * depth - r)
    require(D % start_grid == 0, "start-grid quotient")

    odd_offset = Fraction(10**depth * c, 16 * R)
    target = ((Fraction(1, 9) - odd_offset) % 1) * start_grid
    base = target.numerator // target.denominator
    odd_candidates = {
        (base + offset) % start_grid
        for offset in range(-3, 4)
        if (base + offset) % 2
    }
    require(odd_candidates, "nearby odd start-grid point")
    start_numerator = min(
        odd_candidates,
        key=lambda candidate: circle(
            odd_offset + Fraction(candidate, start_grid) - Fraction(1, 9)
        ),
    )
    start_error = circle(
        odd_offset + Fraction(start_numerator, start_grid) - Fraction(1, 9)
    )
    require(start_error <= Fraction(1, start_grid), "odd-grid covering radius")

    base_w = start_numerator * pow(5**depth, -1, start_grid) % start_grid
    repetition_count = D // start_grid
    quotient_guess = (actual_w - base_w) // start_grid
    repetition_candidates = {
        max(0, min(repetition_count - 1, quotient_guess + offset))
        for offset in range(-2, 3)
    }
    w = min(
        (base_w + repetition * start_grid for repetition in repetition_candidates),
        key=lambda candidate: abs(candidate - actual_w),
    )
    require(w % 2 == 1 and 0 <= w < D, "alternative odd dyadic coordinate")
    require(abs(w - actual_w) <= start_grid, "nearby representative of selected grid class")
    theta = Fraction(w, D) + Fraction(c, R)
    beta = Fraction(10**depth, 16) * theta
    require(circle(beta - Fraction(1, 9)) == start_error, "selected starting seed")
    P = R * w + D * c
    require(gcd(P, 2 * R) == 1, "alternative full numerator reduced")
    alternative_b = Fraction(P, 16 * D * R)
    require(
        abs(alternative_b - partials[depth]) <= Fraction(1, 2**depth),
        "alternative truncation remains exponentially close",
    )

    upper = int(log10(16) * depth)
    row_length = upper - depth + 1
    fake_sum = 0j
    max_orbit_error = Fraction(0)
    common_phase = phase(1, Fraction(1, 9) - theta)
    for n in range(depth, upper + 1):
        orbit_error = circle(Fraction(10**n, 16) * theta - Fraction(1, 9))
        require(
            orbit_error <= Fraction(depth + 1, 5**depth),
            "uniform dyadic-selector orbit bound",
        )
        max_orbit_error = max(max_orbit_error, orbit_error)
        fake_sum += phase(1, a_index(n) * theta)
        dyadic_selector_checks += 1
    require(
        abs(fake_sum / row_length - common_phase)
        <= 2 * pi * (depth + 1) / 5**depth + 1e-12,
        "dyadic-selector normalized sum near a unit",
    )
    if depth in (48, 64, 96, 128):
        dyadic_selector_diagnostics[str(depth)] = {
            "row_length": row_length,
            "odd_denominator_bits": R.bit_length(),
            "max_orbit_error": float(max_orbit_error),
            "normalized_sum_magnitude": abs(fake_sum) / row_length,
        }


# Structural separator.  It retains the exact dyadic exponent, any supplied
# nonzero high-prime additive coordinates, a cofactor with P^+=3 and
# log C=O(log M), reducedness, and the fixed-prime exponent allowance.  Yet
# its row phases converge uniformly to 1.  This does not model the actual
# four-pole carry or coefficient increment.
separator_checks = 0
separator_diagnostics: dict[str, dict[str, float | int]] = {}
for depth in range(48, MAX_DEPTH + 1):
    _actual_R, _actual_c, _actual_w, S, gammas, Xi = actual_rows[depth]
    r = valuation(depth + 1, 2)
    D = 1 << (4 * depth - r - 4)

    C = 1
    exponent_three = 0
    while C < (depth + 1) ** 3:
        C *= 3
        exponent_three += 1
    require(C < 3 * (depth + 1) ** 3, "minimal cubic three-power")
    require(
        exponent_three <= 4 * floor_log(3, 8 * depth + 5),
        "fixed-prime exponent allowance",
    )
    require(gcd(S, C) == 1, "separator CRT coprimality")

    grid_modulus = D * C
    target = ((Fraction(1, 3) - Xi) % 1) * grid_modulus
    base = target.numerator // target.denominator
    candidates = {
        (base + offset) % grid_modulus
        for offset in range(-6, 7)
        if gcd((base + offset) % grid_modulus, 6) == 1
    }
    require(candidates, "nearby reduced grid point")
    grid_numerator = min(
        candidates,
        key=lambda candidate: circle(
            Xi + Fraction(candidate, grid_modulus) - Fraction(1, 3)
        ),
    )
    grid_error = circle(
        Xi + Fraction(grid_numerator, grid_modulus) - Fraction(1, 3)
    )
    require(grid_error <= Fraction(2, grid_modulus), "reduced-grid covering radius")

    w = grid_numerator * pow(C, -1, D) % D
    eta = grid_numerator * pow(D, -1, C) % C
    require(w % 2 == 1 and gcd(eta, C) == 1, "reduced separator coordinates")
    require((w * C + eta * D - grid_numerator) % grid_modulus == 0, "grid CRT")

    R = S * C
    q_residue = (Xi + Fraction(eta, C)) % 1
    c_fraction = q_residue * R
    require(c_fraction.denominator == 1, "integral reconstructed numerator")
    c = c_fraction.numerator
    require(gcd(c, R) == 1, "reduced reconstructed odd quotient")
    for prime_value, gamma in gammas.items():
        require(
            c * pow(R // prime_value, -1, prime_value) % prime_value == gamma,
            "preserved explicit high-prime coordinate",
        )
        separator_checks += 1
    require(c * pow(S, -1, C) % C == eta, "preserved cofactor coordinate")

    P = R * w + D * c
    require(gcd(P, 2 * R) == 1, "reduced full separator numerator")
    theta = Fraction(P, D * R) % 1
    require(
        (theta - Xi - Fraction(w, D) - Fraction(eta, C)) % 1 == 0,
        "separator phase decomposition",
    )
    require(circle(theta - Fraction(1, 3)) == grid_error, "separator target phase")

    upper = int(log10(16) * depth)
    max_phase_error = Fraction(0)
    fake_sum = 0j
    for n in range(depth, upper + 1):
        A = a_index(n)
        require(A % 3 == 0, "separator resonant phase")
        error = circle(A * theta)
        require(error <= Fraction(2, (depth + 1) ** 2), "uniform separator row bound")
        max_phase_error = max(max_phase_error, error)
        fake_sum += phase(1, A * theta)
        separator_checks += 1
    row_length = upper - depth + 1
    require(
        abs(fake_sum / row_length - 1) <= 4 * pi / (depth + 1) ** 2 + 1e-12,
        "separator normalized sum near one",
    )
    if depth in (48, 64, 96, 128):
        separator_diagnostics[str(depth)] = {
            "row_length": row_length,
            "high_prime_count": len(gammas),
            "cofactor_three_exponent": exponent_three,
            "max_phase_error": float(max_phase_error),
            "normalized_sum_magnitude": abs(fake_sum) / row_length,
        }


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
        "A_index": a_index_checks,
        "weighted_sum_collapse": collapse_checks,
        "finite_tail_transfer": finite_tail_transfer_checks,
        "iterated_difference": difference_checks,
        "correlation_promotion": correlation_checks,
        "dyadic_nontermination": dyadic_nontermination_checks,
        "actual_CRT": actual_crt_checks,
        "dyadic_selector": dyadic_selector_checks,
        "structural_separator": separator_checks,
    },
    "finite_fourier_diagnostics": finite_fourier_diagnostics,
    "separator_diagnostics": separator_diagnostics,
    "dyadic_selector_diagnostics": dyadic_selector_diagnostics,
    "source_pins": pins,
    "warning": (
        "The separator falsifies rowwise/coarse-data bounds only; it does not "
        "satisfy the actual four-pole carry and is not a counterexample to V1."
    ),
}, indent=2, sort_keys=True))
