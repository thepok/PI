#!/usr/bin/env python3
"""Independent exact replay for the rational-phase density separator.

This checker imports no primary code.  It pins and reruns the frozen primary
artifacts, rebuilds BBP endpoints in a different range and for different
periods, constructs exact-denominator zero-carry phases, and constructs a
coherent separator with literal power-of-two reset depths.  Finite checks are
experiments; no carry-density or V1 assertion is made.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
import math
from math import gcd, lcm
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
PRIMARY_REPORT = Path(
    "work/ultrapi-resume/bbp_rational_phase_density_separator_20260813.md"
)
PRIMARY_CHECKER = Path(
    "work/ultrapi-resume/"
    "bbp_rational_phase_density_separator_20260813_check.py"
)

PINS = {
    Path("problems/local/pi-digits.txt"):
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    PRIMARY_REPORT:
        "1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198",
    PRIMARY_CHECKER:
        "72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc",
    Path("work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md"):
        "3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6",
    Path("work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md"):
        "bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55",
    Path(
        "work/ultrapi-resume/"
        "bbp_fixed_period_carry_attack_20260813_independent_audit.md"
    ):
        "ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91",
    Path("work/ultrapi-resume/bbp_all_depth_two_adic_attack.md"):
        "9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9",
    Path("work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md"):
        "846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007",
    Path("work/ultrapi-resume/bbp_actual_odd_quotient_attack.md"):
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    Path("work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md"):
        "85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36",
    Path("work/ultrapi-resume/bbp_short_orbit_return_independent_audit.md"):
        "49909a445f8748c4e3614537195072c94409c92e21100d2bf4593c4c8b4963f2",
    Path("work/theory/pi-digits/library/t6/bbp-1997-nasa.pdf"):
        "e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4",
}

PERIODS = (1, 3, 5)
START_N = 14
MAX_N = 140
PROXY_MULTIPLIER = 5
RESETS = (16, 32, 64, 128)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(relative: Path) -> str:
    return sha256((ROOT / relative).read_bytes()).hexdigest()


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


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
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def factor_support(value: int) -> set[int]:
    result: set[int] = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            result.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result.add(value)
    return result


def omega_from_raw_support(value: int, support: frozenset[int]) -> int:
    residual = value
    omega = 0
    for prime in support:
        if residual % prime == 0:
            omega += 1
            while residual % prime == 0:
                residual //= prime
    require(residual == 1, "raw support must factor reduced denominator")
    return omega


def build_endpoints() -> list[dict[str, object]]:
    maximum = PROXY_MULTIPLIER * MAX_N
    common = coefficient_denominator(0)
    scaled = coefficient_numerator(0)
    support = factor_support(common)
    endpoints: list[dict[str, object]] = [{
        "n": 0,
        "L": common,
        "A": scaled,
        "B": Fraction(scaled, common),
        "support": frozenset(support),
    }]

    for m in range(1, 7 * maximum + 1):
        d = coefficient_denominator(m)
        next_common = lcm(common, d)
        scaled = (
            16 * (next_common // common) * scaled
            + coefficient_numerator(m) * (next_common // d)
        )
        common = next_common
        for linear_factor in (
            2 * m + 1,
            4 * m + 3,
            8 * m + 1,
            8 * m + 5,
        ):
            support.update(factor_support(linear_factor))

        if m % 7 == 0:
            endpoints.append({
                "n": m // 7,
                "L": common,
                "A": scaled,
                "B": Fraction(scaled, 16**m * common),
                "support": frozenset(support),
            })

    require(len(endpoints) == maximum + 1, "endpoint count")
    return endpoints


def forcing(period: int, n: int,
            endpoints: list[dict[str, object]]) -> Fraction:
    q = 10**period - 1
    first = endpoints[n]["B"]
    second = endpoints[n + 1]["B"]
    require(isinstance(first, Fraction) and isinstance(second, Fraction),
            "endpoint fraction types")
    return q * 10 ** (n + 1) * (second - first)


def coprime_near(target: Fraction, denominator: int) -> tuple[Fraction, int]:
    center = nearest(target * denominator)
    offset = 0
    while True:
        candidates = (center,) if offset == 0 else (
            center - offset,
            center + offset,
        )
        for numerator in candidates:
            if gcd(numerator, denominator) == 1:
                return Fraction(numerator, denominator), offset
        offset += 1


def jacobsthal_length(modulus: int) -> int:
    """Least L for which every L consecutive integers meets a unit."""
    longest_nonunit_run = 0
    for start in range(modulus):
        length = 0
        while gcd(start + length, modulus) != 1:
            length += 1
        longest_nonunit_run = max(longest_nonunit_run, length)
    return longest_nonunit_run + 1


def check_small_jacobsthal_convention() -> dict[str, int]:
    maximum_ratio_numerator = 0
    rows = 0
    for modulus in range(2, 513):
        omega = len(factor_support(modulus))
        length = jacobsthal_length(modulus)
        require(length <= 2**omega,
                f"Kanold finite shadow modulus={modulus}")
        maximum_ratio_numerator = max(
            maximum_ratio_numerator,
            length * 2 ** (9 - omega),
        )
        rows += 1
    return {
        "moduli": rows,
        "scaled_maximum_length_ratio_numerator": maximum_ratio_numerator,
    }


def replay_period(period: int,
                  endpoints: list[dict[str, object]]) -> dict[str, object]:
    q = 10**period - 1
    phases: dict[int, Fraction] = {}
    raw_denominators: dict[int, int] = {}
    maximum_offset = 0
    minimum_log10_relative_error: float | None = None
    maximum_log10_relative_error = -math.inf
    maximum_omega_over_n = 0.0

    for n in range(START_N, MAX_N + 1):
        endpoint = endpoints[n]
        common = endpoint["L"]
        scaled = endpoint["A"]
        partial = endpoint["B"]
        support = endpoint["support"]
        far_partial = endpoints[PROXY_MULTIPLIER * n]["B"]
        require(
            isinstance(common, int)
            and isinstance(scaled, int)
            and isinstance(partial, Fraction)
            and isinstance(far_partial, Fraction)
            and isinstance(support, frozenset),
            "endpoint field types",
        )

        raw_denominator = 2 ** (27 * n) * common
        raw_numerator = q * 5**n * scaled
        actual_phase = Fraction(raw_numerator, raw_denominator)
        require(actual_phase == q * 10**n * partial,
                f"phase normalization P={period}, n={n}")
        Q = actual_phase.denominator
        require(raw_denominator % Q == 0,
                f"reduced denominator divides raw P={period}, n={n}")
        require(
            valuation_two(Q) == 27 * n - valuation_two(7 * n + 1),
            f"exact denominator v2 P={period}, n={n}",
        )

        target_proxy = -q * 10**n * (far_partial - partial)
        phase, offset = coprime_near(target_proxy, Q)
        require(phase.denominator == Q,
                f"exact separator denominator P={period}, n={n}")
        require(-Fraction(1, 2) < phase < 0,
                f"negative centered phase P={period}, n={n}")
        require(nearest(phase) == 0,
                f"zero nearest integer P={period}, n={n}")

        omega = omega_from_raw_support(Q, support | frozenset({2}))
        require(offset <= 2**omega,
                f"targeted Kanold distance P={period}, n={n}")
        require(
            abs(phase - target_proxy)
            <= Fraction(2**omega + 1, Q),
            f"Kanold approximation scale P={period}, n={n}",
        )
        maximum_offset = max(maximum_offset, offset)
        maximum_omega_over_n = max(maximum_omega_over_n, omega / n)

        raw_centered = phase * raw_denominator
        require(raw_centered.denominator == 1,
                f"integral raw numerator P={period}, n={n}")
        require(
            valuation_two(raw_centered.numerator)
            == valuation_two(7 * n + 1),
            f"raw numerator v2 P={period}, n={n}",
        )

        phases[n] = phase
        raw_denominators[n] = raw_denominator

    for n in range(START_N, MAX_N):
        exact = forcing(period, n, endpoints)
        candidate = phases[n + 1] - 10 * phases[n]
        require(exact > 0 and candidate > 0,
                f"positive forcing P={period}, n={n}")
        relative_error = abs(candidate - exact) / exact
        log_error = (
            math.log10(relative_error.numerator)
            - math.log10(relative_error.denominator)
        )
        maximum_log10_relative_error = max(
            maximum_log10_relative_error, log_error
        )
        minimum_log10_relative_error = (
            log_error
            if minimum_log10_relative_error is None
            else min(minimum_log10_relative_error, log_error)
        )
        require(relative_error < Fraction(1, 10**120),
                f"pointwise relative closeness P={period}, n={n}")

        D = raw_denominators[n]
        D_next = raw_denominators[n + 1]
        require(D_next % D == 0,
                f"nested raw denominator P={period}, n={n}")
        S = phases[n] * D
        S_next = phases[n + 1] * D_next
        J = candidate * D_next
        require(S.denominator == S_next.denominator == J.denominator == 1,
                f"integer recurrence terms P={period}, n={n}")
        require(S_next == 10 * (D_next // D) * S + J,
                f"raw recurrence P={period}, n={n}")
        require(nearest(phases[n + 1]) - 10 * nearest(phases[n]) == 0,
                f"zero pointwise carry P={period}, n={n}")

    coherent: dict[int, Fraction] = {RESETS[0]: phases[RESETS[0]]}
    exceptional: list[int] = []
    exact_transitions = 0
    maximum_exception_log10_error = -math.inf
    for n in range(RESETS[0], MAX_N):
        exact = forcing(period, n, endpoints)
        if n + 1 in RESETS:
            coherent[n + 1] = phases[n + 1]
            exceptional.append(n)
        else:
            coherent[n + 1] = 10 * coherent[n] + exact
            exact_transitions += 1

        current = coherent[n + 1]
        require(-Fraction(1, 2) < current < Fraction(1, 2),
                f"coherent centered range P={period}, n={n + 1}")
        require(nearest(current) == 0,
                f"coherent nearest integer P={period}, n={n + 1}")
        D_next = 2 ** (27 * (n + 1)) * int(endpoints[n + 1]["L"])
        require((current * D_next).denominator == 1,
                f"coherent denominator divides raw P={period}, n={n + 1}")

        candidate = current - 10 * coherent[n]
        if n in exceptional:
            relative_error = abs(candidate - exact) / exact
            require(candidate > 0,
                    f"positive exceptional forcing P={period}, n={n}")
            require(relative_error < Fraction(1, 10**120),
                    f"exceptional relative closeness P={period}, n={n}")
            maximum_exception_log10_error = max(
                maximum_exception_log10_error,
                math.log10(relative_error.numerator)
                - math.log10(relative_error.denominator),
            )
        else:
            require(candidate == exact,
                    f"density-one exact forcing P={period}, n={n}")
        require(nearest(current) - 10 * nearest(coherent[n]) == 0,
                f"coherent zero carry P={period}, n={n}")

    require(exceptional == [31, 63, 127],
            f"literal power-of-two exceptions P={period}")

    return {
        "period": period,
        "pointwise_states": len(phases),
        "pointwise_zero_carries": MAX_N - START_N,
        "maximum_coprime_offset": maximum_offset,
        "maximum_omega_over_n_finite": maximum_omega_over_n,
        "maximum_log10_relative_error": maximum_log10_relative_error,
        "minimum_log10_relative_error": minimum_log10_relative_error,
        "coherent_states": len(coherent),
        "coherent_zero_carries": MAX_N - RESETS[0],
        "coherent_exact_transitions": exact_transitions,
        "coherent_exceptions": exceptional,
        "maximum_exception_log10_relative_error":
            maximum_exception_log10_error,
    }


def check_exponent_arithmetic() -> dict[str, float]:
    denominator_rate = 42 + 27 * math.log(2)
    forcing_decay = 27 * math.log(2) - math.log(5)
    pointwise_relative_rate = denominator_rate - forcing_decay
    coherent_rate = (
        (denominator_rate - math.log(10)) / 2 - forcing_decay
    )
    require(
        math.isclose(pointwise_relative_rate, 42 + math.log(5),
                     rel_tol=0.0, abs_tol=1e-12),
        "pointwise relative exponent identity",
    )
    require(
        math.isclose(
            coherent_rate,
            21 - 14 * math.log(2) + math.log(5) / 2,
            rel_tol=0.0,
            abs_tol=1e-12,
        ),
        "coherent reset exponent identity",
    )
    require(coherent_rate > 12.1, "positive coherent exponent margin")
    return {
        "denominator_rate": denominator_rate,
        "forcing_decay_rate": forcing_decay,
        "pointwise_relative_rate": pointwise_relative_rate,
        "coherent_relative_rate": coherent_rate,
    }


def main() -> None:
    observed_pins: dict[str, str] = {}
    for relative, expected in PINS.items():
        actual = digest(relative)
        require(actual == expected,
                f"hash mismatch {relative}: expected {expected}, got {actual}")
        observed_pins[str(relative)] = actual

    report_text = (ROOT / PRIMARY_REPORT).read_text(encoding="utf-8")
    require(PINS[Path("problems/local/pi-digits.txt")] in report_text,
            "canonical target pin missing")
    require(PINS[PRIMARY_CHECKER] in report_text,
            "primary checker pin missing")

    primary = run([".venv/bin/python", str(PRIMARY_CHECKER)])
    require(primary.returncode == 0, primary.stdout)
    primary_result = json.loads(primary.stdout)
    require(primary_result["status"] == "PASS", "primary replay")
    require(primary_result["asserts_positive_carry_density"] is False,
            "primary density scope")
    require(primary_result["asserts_v1"] is False, "primary V1 scope")

    jacobsthal = check_small_jacobsthal_convention()
    endpoints = build_endpoints()
    period_results = [
        replay_period(period, endpoints) for period in PERIODS
    ]
    exponents = check_exponent_arithmetic()

    print(json.dumps({
        "status": "PASS",
        "asymptotic_claim_label": "proof sketch",
        "finite_claim_label": "experiment",
        "pins": observed_pins,
        "primary_status": primary_result["status"],
        "independent_periods": list(PERIODS),
        "independent_depth_range": [START_N, MAX_N],
        "tail_proxy_endpoint_multiplier": PROXY_MULTIPLIER,
        "literal_power_of_two_resets": list(RESETS),
        "small_jacobsthal_convention_checks": jacobsthal,
        "exponent_arithmetic": exponents,
        "period_results": period_results,
        "asserts_positive_carry_density": False,
        "asserts_v1": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
