#!/usr/bin/env python3
"""Independent replay for the frozen BBP odd-cofactor report.

All bounded calculations have claim label ``experiment``.  This file imports
no primary checker.  In particular, the large-prime localization is rebuilt
directly from the four original BBP partial fractions rather than from the
primary checker's closed formula for G_(M,p).

The replay also retains a counterexample to the old, now corrected,
``n >= e`` quantifier in equation (18).  The revised report correctly uses
``n >= max(4,e)``: multiplication of a congruence modulo one by the
nonintegral A_n would be invalid at n < 4.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MAX_DEPTH = 1000
CUTOFFS = ("M", "ceil(M/2)", "ceil(M/4)", "sqrt(X)")

PINS = {
    "problems/local/pi-digits.txt":
        "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825",
    "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md":
        "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc",
    "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md":
        "c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3",
    "work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py":
        "5f35c22f15f65dc8ca979908dbf58e7c88879d022287ee480821f5f88fb4b664",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def valuation(value: int, prime: int) -> int:
    require(value != 0, "valuation at zero is not used")
    value = abs(value)
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def floor_log(base: int, value: int) -> int:
    answer = 0
    power = 1
    while power * base <= value:
        power *= base
        answer += 1
    return answer


def partial_coefficient(k: int) -> Fraction:
    return (
        Fraction(4, 8 * k + 1)
        - Fraction(2, 8 * k + 4)
        - Fraction(1, 8 * k + 5)
        - Fraction(1, 8 * k + 6)
    )


def closed_coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1)
        * (4 * k + 3)
        * (8 * k + 1)
        * (8 * k + 5),
    )


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            count = (limit - prime * prime) // prime + 1
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * count
    return [number for number in range(2, limit + 1) if sieve[number]]


def factor(value: int, primes: list[int]) -> dict[int, int]:
    remaining = value
    answer: dict[int, int] = {}
    for prime in primes:
        if prime * prime > remaining:
            break
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            answer[prime] = exponent
    if remaining > 1:
        answer[remaining] = answer.get(remaining, 0) + 1
    require(
        value == _product_factors(answer),
        f"complete factorization of {value}",
    )
    return answer


def _product_factors(factors: dict[int, int]) -> int:
    answer = 1
    for prime, exponent in factors.items():
        answer *= prime**exponent
    return answer


def modular_fraction(value: Fraction, prime: int) -> int:
    require(value.denominator % prime != 0, "prime-unit denominator required")
    return value.numerator * pow(value.denominator, -1, prime) % prime


PARTIAL_POLES = (
    (4, 8, 1, "8k+1"),
    (-2, 8, 4, "8k+4"),
    (-1, 8, 5, "8k+5"),
    (-1, 8, 6, "8k+6"),
)


def direct_local_coordinate(depth: int, prime: int) -> tuple[int, int]:
    """Compute 16 p B_M mod p directly from singular partial fractions."""
    require(prime > 5, "large-prime localization")
    require(prime * prime > 8 * depth + 5, "simple-pole range")
    total = 0
    singular_terms = 0
    for coefficient, slope, intercept, _label in PARTIAL_POLES:
        first = (-intercept * pow(slope, -1, prime)) % prime
        for k in range(first, depth + 1, prime):
            denominator = slope * k + intercept
            require(denominator % prime == 0, "singular progression")
            quotient = denominator // prime
            require(quotient % prime != 0, "simple rather than repeated pole")
            weight = pow(pow(16, k, prime), -1, prime)
            total += coefficient * pow(quotient, -1, prime) * weight
            singular_terms += 1
    return 16 * total % prime, singular_terms


def cutoff(label: str, depth: int, size: int) -> int:
    if label == "M":
        return depth
    if label == "ceil(M/2)":
        return (depth + 1) // 2
    if label == "ceil(M/4)":
        return (depth + 3) // 4
    if label == "sqrt(X)":
        return isqrt(size)
    raise AssertionError(f"unknown cutoff {label}")


def generalized_crt(
    residue_one: int,
    modulus_one: int,
    residue_two: int,
    modulus_two: int,
) -> tuple[int, int] | None:
    common = gcd(modulus_one, modulus_two)
    difference = residue_two - residue_one
    if difference % common:
        return None
    right = modulus_two // common
    multiplier = 0
    if right > 1:
        multiplier = (
            difference // common
            * pow(modulus_one // common, -1, right)
        ) % right
    modulus = modulus_one * right
    return (residue_one + modulus_one * multiplier) % modulus, modulus


@lru_cache(maxsize=None)
def local_log_and_order(modulus: int) -> tuple[int | None, int]:
    require(gcd(modulus, 10) == 1, "unit power orbit")
    target = 16 % modulus
    value = 1 % modulus
    exponent = 0
    while True:
        if value == target:
            first_solution = exponent
            break
        value = value * 10 % modulus
        exponent += 1
        if value == 1 % modulus:
            first_solution = None
            break

    value = 10 % modulus
    order = 1
    while value != 1 % modulus:
        value = value * 10 % modulus
        order += 1
        require(order <= modulus, "Euler orbit must close")
    return first_solution, order


def classify_stripped_orbit(
    factors: dict[int, int],
) -> tuple[str, tuple[int, ...]]:
    residue = 0
    modulus = 1
    for prime, exponent in sorted(factors.items()):
        if prime in (3, 5):
            continue
        local_log, local_order = local_log_and_order(prime**exponent)
        if local_log is None:
            return "local", (prime, exponent, local_order)
        merged = generalized_crt(
            residue,
            modulus,
            local_log,
            local_order,
        )
        if merged is None:
            return (
                "incompatible",
                (
                    prime,
                    exponent,
                    local_log,
                    local_order,
                    residue,
                    modulus,
                ),
            )
        residue, modulus = merged
    return "class", (residue, modulus)


def enumerate_maximal_five_poles(
    depth: int,
) -> tuple[int, list[tuple[int, str]], int]:
    size = 8 * depth + 5
    exponent = floor_log(5, size)
    scale = 5**exponent
    poles: list[tuple[int, str]] = []
    leading = 0
    for k in range(depth + 1):
        for coefficient, slope, intercept, label in PARTIAL_POLES:
            denominator = slope * k + intercept
            if valuation(denominator, 5) != exponent:
                continue
            scaled = Fraction(coefficient * scale, denominator)
            require(scaled.denominator % 5 != 0, "leading five-adic unit")
            leading += modular_fraction(scaled, 5)
            poles.append((k, label))
    return exponent, poles, leading % 5


def expected_five_poles(depth: int) -> tuple[int, list[tuple[int, str]], int]:
    exponent = floor_log(5, 8 * depth + 5)
    power = 5**exponent
    if exponent % 2:
        first = ((power - 5) // 8, "8k+5")
    else:
        first = ((power - 1) // 8, "8k+1")
    answer = [first]
    second = (power - 1) // 2
    if second <= depth:
        answer.append((second, "8k+4"))
    return exponent, answer, 4 if len(answer) == 1 else 1


def boundary_five_pole_checks() -> int:
    checks = 0
    for exponent in range(1, 9):
        power = 5**exponent
        minimum = (power - 5 + 7) // 8
        maximum = (5 * power - 6) // 8
        second = (power - 1) // 2
        candidates = {minimum, maximum, second - 1, second}
        for depth in sorted(candidates):
            if not minimum <= depth <= maximum:
                continue
            require(
                enumerate_maximal_five_poles(depth)
                == expected_five_poles(depth),
                f"complete five-pole list at e={exponent}, M={depth}",
            )
            checks += 1
    return checks


def replay() -> dict[str, object]:
    for relative, expected in PINS.items():
        path = ROOT / relative
        require(path.is_file(), f"missing pinned file: {relative}")
        require(digest(path) == expected, f"hash mismatch: {relative}")
    primary_text = (
        ROOT
        / "work/ultrapi-resume/"
        "bbp_odd_cofactor_short_orbit_experiment_20260813.md"
    ).read_text()
    require(
        "For (n\\geq\\max(4,e)), (A_n\\equiv-1\\pmod{5^e}) and"
        in primary_text,
        "corrected equation (18) domain is present",
    )

    coefficient_identity_checks = 0
    for k in range(MAX_DEPTH + 1):
        require(
            partial_coefficient(k) == closed_coefficient(k),
            f"partial-fraction identity at k={k}",
        )
        coefficient_identity_checks += 1

    boundary_checks = boundary_five_pole_checks()
    primes = primes_through(8 * MAX_DEPTH + 5)
    partial_sum = Fraction()
    five_denominator_checks = 0
    possible_large_prime_checks = 0
    surviving_coordinate_checks = 0
    cancelled_large_prime_checks = 0
    square_support_checks = 0
    crt_phase_checks = 0
    short_orbit_checks = 0
    record_hasher = sha256()
    classifications = {label: Counter() for label in CUTOFFS}
    exact_hits = Counter()
    exceptional_rows: dict[str, list[tuple[int, str, tuple[int, ...]]]] = {
        label: [] for label in CUTOFFS
    }
    samples: dict[tuple[int, str], tuple[float, int, int]] = {}
    quantifier_counterexample: dict[str, object] | None = None

    for depth in range(MAX_DEPTH + 1):
        partial_sum += closed_coefficient(depth) / 16**depth
        size = 8 * depth + 5
        five_exponent = floor_log(5, size)
        require(
            valuation(partial_sum.denominator, 5) == five_exponent,
            f"exact five denominator at M={depth}",
        )
        five_denominator_checks += 1
        if depth < 48:
            continue

        numerator = partial_sum.numerator
        full_denominator = partial_sum.denominator
        two_exponent = valuation(full_denominator, 2)
        require(
            two_exponent == 4 * depth - valuation(depth + 1, 2),
            f"dyadic denominator exponent at M={depth}",
        )
        odd_denominator = full_denominator >> two_exponent
        factors = factor(odd_denominator, primes)
        require(
            factors.get(5) == five_exponent,
            f"full five-primary part at M={depth}",
        )

        dyadic_modulus = 1 << (two_exponent - 4)
        dyadic_residue = (
            numerator * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            numerator - odd_denominator * dyadic_residue
        ) // dyadic_modulus
        require(
            gcd(odd_numerator, odd_denominator) == 1,
            f"reduced odd coordinate at M={depth}",
        )

        for prime in primes:
            if prime <= max(5, isqrt(size)):
                continue
            if prime > size:
                break
            local, singular_terms = direct_local_coordinate(depth, prime)
            survives = prime in factors
            require(
                (local != 0) == survives,
                f"survival iff direct local residue at M={depth}, p={prime}",
            )
            if singular_terms:
                possible_large_prime_checks += 1
            if not survives:
                if singular_terms:
                    cancelled_large_prime_checks += 1
                continue
            require(
                factors[prime] == 1,
                f"simple surviving exponent at M={depth}, p={prime}",
            )
            actual = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            require(
                actual == local,
                f"direct additive coordinate at M={depth}, p={prime}",
            )
            surviving_coordinate_checks += 1

        upper = len(str(16**depth)) - 1
        require(
            10**upper <= 16**depth < 10 ** (upper + 1),
            f"exact proportional row endpoint at M={depth}",
        )
        for label in CUTOFFS:
            threshold = cutoff(label, depth, size)
            cofactor_factors = dict(factors)
            selected = 1
            for prime, exponent in list(cofactor_factors.items()):
                if prime > threshold and prime * prime > size:
                    require(
                        exponent == 1,
                        f"selected prime is simple at M={depth}, p={prime}",
                    )
                    selected *= prime
                    del cofactor_factors[prime]
            cofactor = _product_factors(cofactor_factors)
            require(
                odd_denominator == selected * cofactor,
                f"exact cofactor split at M={depth}, cutoff={label}",
            )
            require(
                gcd(selected, cofactor) == 1,
                f"coprime cofactor split at M={depth}, cutoff={label}",
            )
            require(
                cofactor_factors.get(5) == five_exponent,
                f"retained complete five part at M={depth}, cutoff={label}",
            )
            if label == "sqrt(X)":
                require(
                    max(cofactor_factors) <= isqrt(size),
                    f"square-root support at M={depth}",
                )
                for prime, exponent in cofactor_factors.items():
                    if prime > 5:
                        require(
                            exponent <= floor_log(prime, size),
                            f"prime-power height at M={depth}, p={prime}",
                        )
                square_support_checks += 1

            eta = odd_numerator * pow(selected, -1, cofactor) % cofactor
            require(gcd(eta, cofactor) == 1, "primitive cofactor coordinate")
            five_power = 5**five_exponent
            cofactor_zero = cofactor // five_power
            beta_five = (
                eta * pow(cofactor_zero, -1, five_power)
            ) % five_power
            beta_zero = (
                eta * pow(five_power, -1, cofactor_zero)
            ) % cofactor_zero
            if depth == 48 and label == "sqrt(X)":
                small_n = five_exponent
                small_a = Fraction(10**small_n - 16, 16)
                small_left = small_a * Fraction(eta, cofactor)
                small_right = (
                    Fraction(-beta_five, five_power)
                    + small_a * Fraction(beta_zero, cofactor_zero)
                )
                small_difference = small_left - small_right
                require(small_n >= five_exponent, "frozen n >= e quantifier")
                require(
                    small_difference.denominator != 1,
                    "actual cofactor counterexample below the integral-A_n range",
                )
                quantifier_counterexample = {
                    "M": depth,
                    "cutoff": label,
                    "e": five_exponent,
                    "n": small_n,
                    "C": cofactor,
                    "eta": eta,
                    "beta_five": beta_five,
                    "beta_zero": beta_zero,
                    "A_n": str(small_a),
                    "left_minus_right": str(small_difference),
                }
            classification, detail = classify_stripped_orbit(cofactor_factors)
            classifications[label][classification] += 1
            if classification != "local":
                exceptional_rows[label].append((depth, classification, detail))

            best_gcd = 1
            best_centered = cofactor
            power = pow(10, depth, cofactor)
            for decimal_exponent in range(depth, upper + 1):
                require(decimal_exponent >= max(4, five_exponent), "row domain")
                difference = (power - 16) % cofactor
                require(difference != 0, "five-primary exact-kill obstruction")
                require(difference % 5 == 4, "difference is a five-adic unit")
                difference_gcd = gcd(difference, cofactor)
                centered = min(difference, cofactor - difference)
                best_gcd = max(best_gcd, difference_gcd)
                best_centered = min(best_centered, centered)

                a_n = (10**decimal_exponent - 16) // 16
                require(
                    a_n % five_power == five_power - 1,
                    f"constant five-primary multiplier at M={depth}, n={decimal_exponent}",
                )
                left = Fraction(a_n * eta, cofactor)
                right = (
                    Fraction(-beta_five, five_power)
                    + Fraction(a_n * beta_zero, cofactor_zero)
                )
                require(
                    (left - right).denominator == 1,
                    f"CRT phase split at M={depth}, n={decimal_exponent}, cutoff={label}",
                )
                crt_phase_checks += 1
                short_orbit_checks += 1
                power = power * 10 % cofactor

            if best_centered == 0:
                exact_hits[label] += 1
            if depth in (48, 100, 200, 500, 1000):
                samples[depth, label] = (
                    __import__("math").log(cofactor) / depth,
                    max(cofactor_factors),
                    five_exponent,
                )
            factors_text = ",".join(
                f"{prime}^{exponent}"
                for prime, exponent in sorted(cofactor_factors.items())
            )
            record_hasher.update(
                (
                    f"{depth}|{label}|{cofactor}|{factors_text}|{eta}|"
                    f"{beta_five}|{beta_zero}|{classification}|{detail}|"
                    f"{best_gcd}|{best_centered}\n"
                ).encode()
            )

    require(surviving_coordinate_checks == 398862, "primary coordinate count")
    require(short_orbit_checks == 409640, "primary short-orbit count")
    require(crt_phase_checks == short_orbit_checks, "every row phase split")
    expected_counts = Counter({"local": 948, "incompatible": 5})
    expected_exceptional_depths = [75, 76, 77, 78, 81]
    for label in CUTOFFS:
        require(exact_hits[label] == 0, f"no exact hit for {label}")
        require(
            classifications[label] == expected_counts,
            f"stripped orbit classification for {label}",
        )
        require(
            [row[0] for row in exceptional_rows[label]]
            == expected_exceptional_depths,
            f"exceptional depths for {label}",
        )
        require(
            all(row[1] == "incompatible" for row in exceptional_rows[label]),
            f"exceptional class for {label}",
        )

    expected_samples = {
        48: (0.720741189521885, 19, 3),
        100: (0.466191381677344, 23, 4),
        200: (0.337217700309831, 37, 4),
        500: (0.243660732953051, 61, 5),
        1000: (0.180028930221739, 89, 5),
    }
    for depth, expected in expected_samples.items():
        actual = samples[depth, "sqrt(X)"]
        require(abs(actual[0] - expected[0]) < 5e-15, f"sample log at M={depth}")
        require(actual[1:] == expected[1:], f"sample support at M={depth}")

    # The old equation (18) claimed only n >= e.  The retained M=48 example
    # uses an actual square-root cofactor and verifies that the revised lower
    # bound n >= max(4,e) excludes the bad nonintegral multiplier.
    require(quantifier_counterexample is not None, "retained counterexample")
    require(
        int(quantifier_counterexample["n"])
        < max(4, int(quantifier_counterexample["e"])),
        "historical counterexample is outside the corrected domain",
    )

    return {
        "status": "PASS",
        "finite_claim_label": "experiment",
        "audited_mathematical_claim_label": "proof sketch",
        "corrected_primary_domain": "n >= max(4,e)",
        "historical_counterexample_excluded_by_correction": (
            quantifier_counterexample
        ),
        "coefficient_identity_checks": coefficient_identity_checks,
        "five_pole_boundary_checks": boundary_checks,
        "five_denominator_checks": five_denominator_checks,
        "possible_large_prime_checks": possible_large_prime_checks,
        "surviving_coordinate_checks": surviving_coordinate_checks,
        "cancelled_large_prime_checks": cancelled_large_prime_checks,
        "square_support_checks": square_support_checks,
        "short_orbit_checks": short_orbit_checks,
        "crt_phase_checks": crt_phase_checks,
        "classifications": {
            label: dict(classifications[label]) for label in CUTOFFS
        },
        "exceptional_depths": expected_exceptional_depths,
        "independent_record_sha256": record_hasher.hexdigest(),
        "asserts_fixed_sixteen_return": False,
        "asserts_v1": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
