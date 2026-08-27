#!/usr/bin/env python3
"""Second independent replay of the BBP rational-phase separator.

This checker does not import either the primary checker or the first
independent checker.  Exact arithmetic audits finite instances of the
denominator, Jacobsthal-lift, forcing, and coherent-reset identities.  The
finite replay is an experiment and asserts neither carry density nor V1.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
import math
from math import gcd, isqrt, lcm
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_rational_phase_density_separator_20260813.md":
        "1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198",
    "work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_check.py":
        "72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc",
    "work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md":
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    "work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md":
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    "work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md":
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    "work/ultrapi-resume/bbp_short_orbit_return_independent_audit.md":
        "49909a445f8748c4e3614537195072c94409c92e21100d2bf4593c4c8b4963f2",
    "work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf":
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

PERIODS = (1, 3, 5)
SEPARATOR_START = 18
SEPARATOR_END = 120
TAIL_FACTOR = 5
RESETS = (24, 48, 96, 192)
COHERENT_END = 208
MAX_ENDPOINT = max(TAIL_FACTOR * RESETS[-1], COHERENT_END, SEPARATOR_END + 1)


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
    require(value != 0, "valuation of zero")
    value = abs(value)
    return (value & -value).bit_length() - 1


def nearest(value: Fraction) -> int:
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def log10_fraction(value: Fraction) -> float:
    require(value > 0, "positive logarithm input")
    return math.log10(value.numerator) - math.log10(value.denominator)


def sieve_primes(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p:limit + 1:p] = b"\x00" * (((limit - p * p) // p) + 1)
    return [i for i, flag in enumerate(sieve) if flag]


def omega(value: int, primes: list[int]) -> int:
    require(value > 0, "positive denominator")
    residual = value
    count = 0
    for p in primes:
        if p * p > residual:
            break
        if residual % p == 0:
            count += 1
            while residual % p == 0:
                residual //= p
    if residual > 1:
        count += 1
    return count


def build_endpoints() -> list[dict[str, int | Fraction]]:
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    endpoints: list[dict[str, int | Fraction]] = [
        {"n": 0, "L": common, "A": scaled, "B": Fraction(scaled, common)}
    ]
    for m in range(1, 7 * MAX_ENDPOINT + 1):
        denominator = coefficient_denominator(m)
        next_common = lcm(common, denominator)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(m) * (next_common // denominator)
        )
        common = next_common
        if m % 7 == 0:
            endpoints.append(
                {
                    "n": m // 7,
                    "L": common,
                    "A": scaled,
                    "B": Fraction(scaled, 16**m * common),
                }
            )
    require(len(endpoints) == MAX_ENDPOINT + 1, "endpoint count")
    return endpoints


def raw_data(period: int, n: int, endpoints: list[dict[str, int | Fraction]]) -> tuple[int, int, Fraction]:
    q = 10**period - 1
    common = endpoints[n]["L"]
    scaled = endpoints[n]["A"]
    partial = endpoints[n]["B"]
    require(isinstance(common, int) and isinstance(scaled, int), "integer endpoint")
    require(isinstance(partial, Fraction), "rational endpoint")
    denominator = 2 ** (27 * n) * common
    numerator = q * 5**n * scaled
    phase = Fraction(numerator, denominator)
    require(phase == q * 10**n * partial, "raw phase identity")
    return numerator, denominator, phase


def exact_forcing(period: int, n: int, endpoints: list[dict[str, int | Fraction]]) -> Fraction:
    q = 10**period - 1
    first = endpoints[n]["B"]
    second = endpoints[n + 1]["B"]
    require(isinstance(first, Fraction) and isinstance(second, Fraction), "B endpoint")
    return q * 10 ** (n + 1) * (second - first)


def tail_interval(period: int, n: int, endpoints: list[dict[str, int | Fraction]]) -> tuple[Fraction, Fraction]:
    """Rigorous interval for -q*10^n*(pi-B_(7n)) from a farther BBP sum."""
    q = 10**period - 1
    far_n = TAIL_FACTOR * n
    partial = endpoints[n]["B"]
    far = endpoints[far_n]["B"]
    require(isinstance(partial, Fraction) and isinstance(far, Fraction), "tail endpoints")
    far_m = 7 * far_n
    remainder_upper = Fraction(1, 15 * (far_m + 1) ** 2 * 16**far_m)
    known_tail = far - partial
    lower = -q * 10**n * (known_tail + remainder_upper)
    upper = -q * 10**n * known_tail
    require(lower < upper < 0, "negative tail interval")
    return lower, upper


def coprime_near(target: Fraction, denominator: int) -> tuple[Fraction, int]:
    center = nearest(target * denominator)
    for offset in range(100_000):
        candidates = (center,) if offset == 0 else (center - offset, center + offset)
        for numerator in candidates:
            if gcd(numerator, denominator) == 1:
                return Fraction(numerator, denominator), offset
    raise AssertionError("coprime search limit")


def separator_at(
    period: int,
    n: int,
    endpoints: list[dict[str, int | Fraction]],
    primes: list[int],
) -> tuple[Fraction, dict[str, object]]:
    _, raw_denominator, actual_phase = raw_data(period, n, endpoints)
    reduced_denominator = actual_phase.denominator
    require(raw_denominator % reduced_denominator == 0, "Q divides raw D")
    require(
        valuation_two(reduced_denominator) == 27 * n - valuation_two(7 * n + 1),
        "reduced denominator two-primary order",
    )

    lower, upper = tail_interval(period, n, endpoints)
    midpoint = (lower + upper) / 2
    separator, offset = coprime_near(midpoint, reduced_denominator)
    omega_q = omega(reduced_denominator, primes)
    jacobsthal_bound = 2**omega_q
    require(offset <= jacobsthal_bound, "finite Jacobsthal offset")
    require(upper - lower < Fraction(1, reduced_denominator), "far-tail grid width")
    maximum_error = max(abs(separator - lower), abs(separator - upper))
    require(
        maximum_error <= Fraction(jacobsthal_bound + 1, reduced_denominator),
        "rigorous error bound to the true irrational phase interval",
    )
    require(-Fraction(1, 2) < separator < 0, "negative centered separator")
    require(separator.denominator == reduced_denominator, "exact reduced denominator")

    raw_centered = separator * raw_denominator
    require(raw_centered.denominator == 1, "integer raw centered numerator")
    require(
        valuation_two(raw_centered.numerator) == valuation_two(7 * n + 1),
        "raw centered numerator two-adic order",
    )
    return separator, {
        "Q": reduced_denominator,
        "D": raw_denominator,
        "omega": omega_q,
        "offset": offset,
        "tail_interval_width": upper - lower,
        "maximum_true_phase_error_bound": maximum_error,
    }


def check_symbolic_zero_orbit(period: int, endpoints: list[dict[str, int | Fraction]]) -> int:
    """Represent t_n as (coefficient of pi, rational part)."""
    q = 10**period - 1
    checks = 0
    for n in range(SEPARATOR_START, SEPARATOR_END):
        first = endpoints[n]["B"]
        second = endpoints[n + 1]["B"]
        require(isinstance(first, Fraction) and isinstance(second, Fraction), "B type")
        pi_coefficient_n = -q * 10**n
        rational_n = q * 10**n * first
        pi_coefficient_next = -q * 10 ** (n + 1)
        rational_next = q * 10 ** (n + 1) * second
        require(pi_coefficient_next - 10 * pi_coefficient_n == 0,
                "pi cancels in zero-orbit recurrence")
        require(rational_next - 10 * rational_n == exact_forcing(period, n, endpoints),
                "symbolic t recurrence")
        checks += 1
    return checks


def check_pointwise_period(
    period: int,
    endpoints: list[dict[str, int | Fraction]],
    primes: list[int],
) -> tuple[dict[int, Fraction], dict[str, object]]:
    phases: dict[int, Fraction] = {}
    metadata: dict[int, dict[str, object]] = {}
    maximum_offset = 0
    maximum_offset_ratio = Fraction(0)

    for n in range(SEPARATOR_START, SEPARATOR_END + 1):
        phase, data = separator_at(period, n, endpoints, primes)
        phases[n] = phase
        metadata[n] = data
        maximum_offset = max(maximum_offset, int(data["offset"]))
        maximum_offset_ratio = max(
            maximum_offset_ratio,
            Fraction(int(data["offset"]), 2 ** int(data["omega"])),
        )

    maximum_relative_error = Fraction(0)
    minimum_relative_error: Fraction | None = None
    exact_forcing_coincidences = 0
    integer_recurrence_checks = 0

    for n in range(SEPARATOR_START, SEPARATOR_END):
        forcing = exact_forcing(period, n, endpoints)
        require(forcing > 0, "positive BBP forcing")
        modified = phases[n + 1] - 10 * phases[n]
        relative = abs(modified - forcing) / forcing
        require(relative < Fraction(1, 10**100), "pointwise exponential closeness")
        require(modified > 0, "positive modified forcing")
        if relative == 0:
            exact_forcing_coincidences += 1
        else:
            minimum_relative_error = relative if minimum_relative_error is None else min(minimum_relative_error, relative)
        maximum_relative_error = max(maximum_relative_error, relative)

        raw = int(metadata[n]["D"])
        next_raw = int(metadata[n + 1]["D"])
        require(next_raw % raw == 0, "nested raw denominator")
        dilation = next_raw // raw
        centered = phases[n] * raw
        next_centered = phases[n + 1] * next_raw
        integer_forcing = modified * next_raw
        require(centered.denominator == next_centered.denominator == integer_forcing.denominator == 1,
                "integer recurrence terms")
        require(next_centered == 10 * dilation * centered + integer_forcing,
                "integer centered recurrence")
        require(nearest(phases[n + 1]) - 10 * nearest(phases[n]) == 0,
                "zero pointwise carry")
        integer_recurrence_checks += 1

    q = 10**period - 1
    lam = Fraction(5, 2**27)
    n = SEPARATOR_END
    predicted_forcing = Fraction(q, 3136) * (10 - lam) * lam**n / n**2
    forcing_ratio = exact_forcing(period, n - 1, endpoints) / (
        Fraction(q, 3136) * (10 - lam) * lam ** (n - 1) / (n - 1) ** 2
    )
    require(Fraction(9, 10) < forcing_ratio < Fraction(11, 10), "forcing leading scale")
    require(predicted_forcing > 0, "positive predicted scale")

    return phases, {
        "period": period,
        "states": len(phases),
        "zero_carries": integer_recurrence_checks,
        "maximum_coprime_offset": maximum_offset,
        "maximum_offset_over_2_to_omega": float(maximum_offset_ratio),
        "maximum_log10_relative_error": log10_fraction(maximum_relative_error),
        "minimum_nonzero_log10_relative_error": (
            None if minimum_relative_error is None else log10_fraction(minimum_relative_error)
        ),
        "exact_forcing_coincidences": exact_forcing_coincidences,
        "forcing_scale_ratio_at_last_checked_transition": float(forcing_ratio),
    }


def check_coherent_period(
    period: int,
    endpoints: list[dict[str, int | Fraction]],
    primes: list[int],
) -> dict[str, object]:
    reset_phases = {
        n: separator_at(period, n, endpoints, primes)[0] for n in RESETS
    }
    coherent: dict[int, Fraction] = {RESETS[0]: reset_phases[RESETS[0]]}
    exceptional: list[int] = []
    exact_transitions = 0
    denominator_mismatches: list[int] = []
    maximum_exception_relative = Fraction(0)

    for n in range(RESETS[0], COHERENT_END):
        forcing = exact_forcing(period, n, endpoints)
        if n + 1 in reset_phases:
            following = reset_phases[n + 1]
            exceptional.append(n)
        else:
            following = 10 * coherent[n] + forcing
            exact_transitions += 1
        coherent[n + 1] = following

        require(-Fraction(1, 2) < following < Fraction(1, 2), "coherent centered range")
        require(nearest(following) == 0, "coherent nearest integer")
        require(nearest(following) - 10 * nearest(coherent[n]) == 0, "coherent zero carry")

        _, raw_denominator, actual_phase = raw_data(period, n + 1, endpoints)
        require((following * raw_denominator).denominator == 1,
                "coherent reduced denominator divides raw D")
        if following.denominator != actual_phase.denominator:
            denominator_mismatches.append(n + 1)

        modified = following - 10 * coherent[n]
        if n in exceptional:
            relative = abs(modified - forcing) / forcing
            require(relative < Fraction(1, 10**100), "reset relative closeness")
            require(modified > 0, "positive reset forcing")
            maximum_exception_relative = max(maximum_exception_relative, relative)
        else:
            require(modified == forcing, "exact nonreset forcing")

    require(exceptional == [47, 95, 191], "geometric reset predecessors")
    require(denominator_mismatches, "the coherent model does not preserve exact Q at every depth")
    return {
        "period": period,
        "states": len(coherent),
        "zero_carries": len(coherent) - 1,
        "exact_forcing_transitions": exact_transitions,
        "exceptional_transitions": exceptional,
        "maximum_exception_log10_relative_error": log10_fraction(maximum_exception_relative),
        "exact_Q_mismatch_count": len(denominator_mismatches),
        "first_exact_Q_mismatches": denominator_mismatches[:8],
    }


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned input: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")

    for k in range(128):
        direct = (
            Fraction(4, 8 * k + 1)
            - Fraction(2, 8 * k + 4)
            - Fraction(1, 8 * k + 5)
            - Fraction(1, 8 * k + 6)
        )
        require(direct == coefficient(k), f"four-pole coefficient k={k}")

    endpoints = build_endpoints()
    primes = sieve_primes(56 * COHERENT_END + 100)
    symbolic_checks = sum(check_symbolic_zero_orbit(p, endpoints) for p in PERIODS)

    pointwise_results = []
    coherent_results = []
    for period in PERIODS:
        _, pointwise = check_pointwise_period(period, endpoints, primes)
        pointwise_results.append(pointwise)
        coherent_results.append(check_coherent_period(period, endpoints, primes))

    pointwise_exponent = 42 + math.log(5)
    coherent_exponent = 21 - 14 * math.log(2) + math.log(5) / 2
    require(pointwise_exponent > 43.60, "pointwise exponent positive")
    require(coherent_exponent > 12.10, "coherent reset exponent positive")

    return {
        "status": "PASS",
        "claim_label": "experiment",
        "pinned_inputs": len(PINS),
        "periods": list(PERIODS),
        "endpoint_depth": MAX_ENDPOINT,
        "symbolic_unique-zero-orbit_recurrence_checks": symbolic_checks,
        "pointwise_results": pointwise_results,
        "coherent_results": coherent_results,
        "pointwise_relative_error_exponent": pointwise_exponent,
        "coherent_reset_relative_error_exponent": coherent_exponent,
        "joint_bundle_warning": (
            "pointwise model preserves exact Q and v2; coherent model preserves "
            "density-one exact forcing and only D-divisibility"
        ),
        "asserts_positive_carry_density": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
