#!/usr/bin/env python3
"""Exact replay for the BBP rational-phase carry-density separator.

All structural assertions use Python integers or ``fractions.Fraction``.
The finite rows are experiments; the asymptotic conclusions are the
proof-sketch arguments in the companion report.  This script asserts neither
positive carry density nor V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
import math
from math import gcd, lcm
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py":
        "b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md":
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    "work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_audit.md":
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    "work/ultrapi-resume/bbp_all_depth_two_adic_attack.md":
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    "work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md":
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

PERIODS = (1, 2, 4)
START_N = 10
MAX_N = 128
TAIL_MULTIPLIER = 4
RESETS = (12, 24, 48, 96)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def coefficient_numerator(k: int) -> int:
    return 120 * k * k + 151 * k + 47


def coefficient_denominator(k: int) -> int:
    return (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)


def coefficient(k: int) -> Fraction:
    return Fraction(coefficient_numerator(k), coefficient_denominator(k))


def valuation_two(value: int) -> int:
    require(value != 0, "two-adic valuation of zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def nearest(value: Fraction) -> int:
    """Return floor(value + 1/2), including for negative values."""
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def factor_small(value: int) -> set[int]:
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


def log10_fraction(value: Fraction) -> float:
    require(value > 0, "positive fraction for logarithm")
    return math.log10(value.numerator) - math.log10(value.denominator)


def build_endpoints() -> list[dict[str, object]]:
    maximum = TAIL_MULTIPLIER * MAX_N
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    prime_support = factor_small(common)
    endpoints: list[dict[str, object]] = [
        {
            "n": 0,
            "L": common,
            "A": scaled,
            "B": Fraction(scaled, common),
            "primes": frozenset(prime_support),
        }
    ]

    for m in range(1, 7 * maximum + 1):
        denominator = coefficient_denominator(m)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(m) * (next_common // denominator)
        )
        common = next_common
        for linear_factor in (
            2 * m + 1,
            4 * m + 3,
            8 * m + 1,
            8 * m + 5,
        ):
            prime_support.update(factor_small(linear_factor))

        if m % 7 == 0:
            n = m // 7
            partial = Fraction(scaled, 16**m * common)
            endpoints.append(
                {
                    "n": n,
                    "L": common,
                    "A": scaled,
                    "B": partial,
                    "primes": frozenset(prime_support),
                }
            )

    require(len(endpoints) == maximum + 1, "endpoint count")
    return endpoints


def coprime_near(target: Fraction, denominator: int) -> tuple[Fraction, int, int]:
    center = nearest(target * denominator)
    for offset in range(denominator + 1):
        candidates = (center,) if offset == 0 else (center - offset, center + offset)
        for numerator in candidates:
            if gcd(numerator, denominator) == 1:
                return Fraction(numerator, denominator), numerator, offset
    raise AssertionError("coprime numerator search exhausted")


def omega_from_support(denominator: int, support: frozenset[int]) -> int:
    residual = denominator
    count = 0
    for prime in support:
        if residual % prime == 0:
            count += 1
            while residual % prime == 0:
                residual //= prime
    require(residual == 1, "known raw prime support factors reduced denominator")
    return count


def forcing(period: int, n: int, endpoints: list[dict[str, object]]) -> Fraction:
    q = 10**period - 1
    first = endpoints[n]["B"]
    second = endpoints[n + 1]["B"]
    require(isinstance(first, Fraction) and isinstance(second, Fraction), "B types")
    return q * 10 ** (n + 1) * (second - first)


def rational_function_block(n: int) -> Fraction:
    return sum(
        (coefficient(7 * n + j) / 16**j for j in range(1, 8)),
        Fraction(0),
    )


def replay_period(
    period: int, endpoints: list[dict[str, object]]
) -> dict[str, object]:
    q = 10**period - 1
    phases: dict[int, Fraction] = {}
    raw_denominators: dict[int, int] = {}
    maximum_offset = 0
    maximum_offset_over_kanold = Fraction(0)
    minimum_phase_gap = Fraction(1, 2)
    maximum_relative_error = Fraction(0)
    minimum_relative_error: Fraction | None = None
    rational_ratio_checks = 0
    exact_denominator_checks = 0
    two_adic_checks = 0

    for n in range(START_N, MAX_N + 1):
        endpoint = endpoints[n]
        common = endpoint["L"]
        scaled = endpoint["A"]
        partial = endpoint["B"]
        support = endpoint["primes"]
        require(
            isinstance(common, int)
            and isinstance(scaled, int)
            and isinstance(partial, Fraction)
            and isinstance(support, frozenset),
            "endpoint field types",
        )

        raw_denominator = 2 ** (27 * n) * common
        raw_numerator = q * 5**n * scaled
        actual_phase = Fraction(raw_numerator, raw_denominator)
        require(actual_phase == q * 10**n * partial, f"actual phase P={period}, n={n}")
        reduced_denominator = actual_phase.denominator
        require(raw_denominator % reduced_denominator == 0,
                f"Q divides D P={period}, n={n}")
        require(
            valuation_two(reduced_denominator) == 27 * n - valuation_two(7 * n + 1),
            f"exact reduced two-primary denominator P={period}, n={n}",
        )

        far_partial = endpoints[TAIL_MULTIPLIER * n]["B"]
        require(isinstance(far_partial, Fraction), "far B type")
        tail_proxy = -q * 10**n * (far_partial - partial)
        separator, numerator, offset = coprime_near(tail_proxy, reduced_denominator)
        require(separator.denominator == reduced_denominator,
                f"exact separator denominator P={period}, n={n}")
        require(Fraction(numerator, reduced_denominator) == separator,
                f"separator reduction P={period}, n={n}")
        require(-Fraction(1, 2) < separator < 0,
                f"negative centered separator P={period}, n={n}")

        omega = omega_from_support(reduced_denominator, support | frozenset({2}))
        kanold_bound = 2**omega
        require(offset <= kanold_bound,
                f"finite Kanold offset P={period}, n={n}")
        maximum_offset = max(maximum_offset, offset)
        maximum_offset_over_kanold = max(
            maximum_offset_over_kanold, Fraction(offset, kanold_bound)
        )

        centered_numerator = separator * raw_denominator
        require(centered_numerator.denominator == 1,
                f"integer raw centered numerator P={period}, n={n}")
        require(
            valuation_two(centered_numerator.numerator) == valuation_two(7 * n + 1),
            f"separator centered v2 P={period}, n={n}",
        )
        require(nearest(separator) == 0, f"zero nearest integer P={period}, n={n}")

        phases[n] = separator
        raw_denominators[n] = raw_denominator
        maximum_phase_size = abs(separator)
        minimum_phase_gap = min(minimum_phase_gap, Fraction(1, 2) - maximum_phase_size)
        exact_denominator_checks += 1
        two_adic_checks += 1

    for n in range(START_N, MAX_N):
        exact_forcing = forcing(period, n, endpoints)
        require(exact_forcing > 0, f"positive exact forcing P={period}, n={n}")
        block = rational_function_block(n)
        require(
            exact_forcing == 10 * q * Fraction(5, 2**27) ** n * block,
            f"rational forcing form P={period}, n={n}",
        )
        if n + 1 < MAX_N:
            next_forcing = forcing(period, n + 1, endpoints)
            next_block = rational_function_block(n + 1)
            require(
                next_forcing / exact_forcing
                == Fraction(5, 2**27) * next_block / block,
                f"first-order rational forcing ratio P={period}, n={n}",
            )
            rational_ratio_checks += 1

        separator_forcing = phases[n + 1] - 10 * phases[n]
        require(separator_forcing > 0,
                f"positive separator forcing P={period}, n={n}")
        relative_error = abs(separator_forcing - exact_forcing) / exact_forcing
        require(relative_error < Fraction(1, 10**100),
                f"exponentially close finite separator forcing P={period}, n={n}")
        maximum_relative_error = max(maximum_relative_error, relative_error)
        if relative_error != 0:
            minimum_relative_error = (
                relative_error
                if minimum_relative_error is None
                else min(minimum_relative_error, relative_error)
            )

        next_raw = raw_denominators[n + 1]
        raw = raw_denominators[n]
        require(next_raw % raw == 0, f"nested D P={period}, n={n}")
        alpha = next_raw // raw
        centered = phases[n] * raw
        next_centered = phases[n + 1] * next_raw
        separator_integer_forcing = separator_forcing * next_raw
        require(
            centered.denominator
            == next_centered.denominator
            == separator_integer_forcing.denominator
            == 1,
            f"integer recurrence terms P={period}, n={n}",
        )
        require(
            next_centered == 10 * alpha * centered + separator_integer_forcing,
            f"raw centered recurrence P={period}, n={n}",
        )
        require(nearest(phases[n + 1]) - 10 * nearest(phases[n]) == 0,
                f"zero centered carry P={period}, n={n}")

    coherent: dict[int, Fraction] = {RESETS[0]: phases[RESETS[0]]}
    exceptional: list[int] = []
    coherent_exact_forcing = 0
    maximum_exception_relative_error = Fraction(0)
    minimum_coherent_margin = Fraction(1, 2) - abs(coherent[RESETS[0]])

    for n in range(RESETS[0], MAX_N):
        exact_forcing = forcing(period, n, endpoints)
        if n + 1 in RESETS:
            coherent[n + 1] = phases[n + 1]
            exceptional.append(n)
        else:
            coherent[n + 1] = 10 * coherent[n] + exact_forcing
            coherent_exact_forcing += 1

        current = coherent[n + 1]
        require(-Fraction(1, 2) < current < Fraction(1, 2),
                f"coherent centered range P={period}, n={n + 1}")
        require(nearest(current) == 0,
                f"coherent zero nearest integer P={period}, n={n + 1}")
        minimum_coherent_margin = min(
            minimum_coherent_margin, Fraction(1, 2) - abs(current)
        )

        raw_denominator = 2 ** (27 * (n + 1)) * int(endpoints[n + 1]["L"])
        require((current * raw_denominator).denominator == 1,
                f"coherent denominator divides D P={period}, n={n + 1}")

        coherent_forcing = current - 10 * coherent[n]
        if n in exceptional:
            relative_error = abs(coherent_forcing - exact_forcing) / exact_forcing
            require(relative_error < Fraction(1, 10**100),
                    f"coherent exceptional forcing close P={period}, n={n}")
            require(coherent_forcing > 0,
                    f"coherent exceptional forcing positive P={period}, n={n}")
            maximum_exception_relative_error = max(
                maximum_exception_relative_error, relative_error
            )
        else:
            require(coherent_forcing == exact_forcing,
                    f"coherent exact forcing P={period}, n={n}")
        require(nearest(current) - 10 * nearest(coherent[n]) == 0,
                f"coherent zero carry P={period}, n={n}")

    require(exceptional == [23, 47, 95], f"coherent reset set P={period}")

    return {
        "period": period,
        "exact_denominator_separator_states": exact_denominator_checks,
        "two_adic_centered_numerator_checks": two_adic_checks,
        "zero_separator_carries": MAX_N - START_N,
        "maximum_coprime_search_offset": maximum_offset,
        "maximum_offset_over_kanold_bound": float(maximum_offset_over_kanold),
        "minimum_centered_margin": float(minimum_phase_gap),
        "maximum_log10_relative_forcing_error": log10_fraction(maximum_relative_error),
        "minimum_nonzero_log10_relative_forcing_error": (
            None
            if minimum_relative_error is None
            else log10_fraction(minimum_relative_error)
        ),
        "rational_function_ratio_checks": rational_ratio_checks,
        "coherent_states": len(coherent),
        "coherent_zero_carries": MAX_N - RESETS[0],
        "coherent_exact_forcing_transitions": coherent_exact_forcing,
        "coherent_exceptional_transitions": exceptional,
        "coherent_maximum_exception_log10_relative_error":
            log10_fraction(maximum_exception_relative_error),
        "coherent_minimum_centered_margin": float(minimum_coherent_margin),
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    for k in range(32):
        direct = (
            Fraction(4, 8 * k + 1)
            - Fraction(2, 8 * k + 4)
            - Fraction(1, 8 * k + 5)
            - Fraction(1, 8 * k + 6)
        )
        require(direct == coefficient(k), f"four-pole coefficient k={k}")

    endpoints = build_endpoints()
    period_results = [replay_period(period, endpoints) for period in PERIODS]

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_inputs": len(PINS),
        "periods": list(PERIODS),
        "separator_depth_range": [START_N, MAX_N],
        "finite_tail_proxy_endpoint_multiplier": TAIL_MULTIPLIER,
        "period_results": period_results,
        "asserts_positive_carry_density": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
