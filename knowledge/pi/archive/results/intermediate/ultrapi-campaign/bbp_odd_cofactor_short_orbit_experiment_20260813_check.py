#!/usr/bin/env python3
"""Exact replay for the BBP odd-cofactor short-orbit experiment.

Every finite output has claim status ``experiment``.  The script uses exact
integers and Fraction arithmetic for all mathematical checks.  Floating-point
numbers occur only in human-readable logarithmic summaries.

It does not prove a fixed-sixteen return or V1.
"""

from __future__ import annotations

import argparse
import hashlib
import math
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


SOURCE_SHA256 = (
    "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"
)
PARENT_REPORT_SHA256 = (
    "d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc"
)
CUTOFF_LABELS = ("M", "ceil(M/2)", "ceil(M/4)", "sqrt(X)")
SAMPLE_DEPTHS = (48, 100, 200, 500, 1000)


def root() -> Path:
    return Path(__file__).resolve().parents[2]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coefficient(index: int) -> Fraction:
    return Fraction(
        120 * index * index + 151 * index + 47,
        (2 * index + 1)
        * (4 * index + 3)
        * (8 * index + 1)
        * (8 * index + 5),
    )


def valuation(integer: int, prime: int) -> int:
    if integer == 0:
        raise ValueError("valuation at zero is not used")
    answer = 0
    integer = abs(integer)
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def floor_log(base: int, value: int) -> int:
    exponent = 0
    power = 1
    while power * base <= value:
        power *= base
        exponent += 1
    return exponent


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            sieve[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [number for number in range(2, limit + 1) if sieve[number]]


def factor(integer: int, primes: list[int]) -> dict[int, int]:
    remaining = integer
    answer: dict[int, int] = {}
    for prime in primes:
        exponent = 0
        while remaining % prime == 0:
            remaining //= prime
            exponent += 1
        if exponent:
            answer[prime] = exponent
        if remaining == 1:
            break
    assert remaining == 1
    return answer


def power_of_two(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << (-exponent))


def localization(depth: int, prime: int) -> Fraction:
    """The explicit simple-pole coordinate G_(M,p)."""
    assert prime > 5 and prime * prime > 8 * depth + 5
    chi_two = 1 if prime % 8 in (1, 7) else -1
    answer = Fraction()
    for multiplier in range(1, (2 * depth + 1) // prime + 1, 2):
        answer -= Fraction(8, multiplier * 4 ** (multiplier - 1))
    for multiplier in range(1, (4 * depth + 3) // prime + 1, 2):
        if multiplier * prime % 4 == 3:
            answer -= power_of_two(6 - multiplier) / multiplier
    for multiplier in range(1, (8 * depth + 1) // prime + 1, 2):
        if multiplier * prime % 8 == 1:
            answer += Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    for multiplier in range(1, (8 * depth + 5) // prime + 1, 2):
        if multiplier * prime % 8 == 5:
            answer -= Fraction(
                64 * chi_two,
                multiplier * 2 ** ((multiplier - 1) // 2),
            )
    return answer


def generalized_crt(
    first_residue: int,
    first_modulus: int,
    second_residue: int,
    second_modulus: int,
) -> tuple[int, int] | None:
    common = math.gcd(first_modulus, second_modulus)
    if (second_residue - first_residue) % common:
        return None
    left = first_modulus // common
    right = second_modulus // common
    multiplier = 0
    if right > 1:
        multiplier = (
            (second_residue - first_residue)
            // common
            * pow(left, -1, right)
        ) % right
    modulus = first_modulus * right
    return (first_residue + first_modulus * multiplier) % modulus, modulus


@lru_cache(maxsize=None)
def discrete_log_and_order(modulus: int) -> tuple[int | None, int]:
    """Return log_10(16), if it exists, and ord(10), by exact cycling."""
    assert math.gcd(modulus, 10) == 1
    target = 16 % modulus
    value = 1 % modulus
    solution: int | None = None
    for order in range(1, modulus + 2):
        if value == target and solution is None:
            solution = order - 1
        value = value * 10 % modulus
        if value == 1 % modulus:
            return solution, order
    raise AssertionError("unit orbit did not close within the modulus")


def classify_fifteen_free_orbit(
    factors: dict[int, int],
) -> tuple[str, tuple[int, ...]]:
    """Classify 10**n = 16 after deleting the complete 3- and 5-parts."""
    residue = 0
    modulus = 1
    for prime, exponent in factors.items():
        if prime in (3, 5):
            continue
        prime_power = prime**exponent
        local_log, local_order = discrete_log_and_order(prime_power)
        if local_log is None:
            return "local", (prime, exponent, local_order)
        merged = generalized_crt(
            residue, modulus, local_log, local_order
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


def cutoff_value(label: str, depth: int, size: int) -> int:
    if label == "M":
        return depth
    if label == "ceil(M/2)":
        return (depth + 1) // 2
    if label == "ceil(M/4)":
        return (depth + 3) // 4
    if label == "sqrt(X)":
        return math.isqrt(size)
    raise AssertionError("unknown cutoff")


def better_ratio(
    numerator: int,
    denominator: int,
    incumbent: tuple[int, int] | None,
) -> bool:
    if incumbent is None:
        return True
    old_numerator, old_denominator = incumbent
    return numerator * old_denominator < old_numerator * denominator


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=1000)
    parser.add_argument("--show-exact", action="store_true")
    args = parser.parse_args()
    if args.max_depth < 1000:
        raise SystemExit("--max-depth must be at least 1000")

    source_path = root() / "problems/local/pi-digits.txt"
    parent_path = (
        root() / "work/ultrapi-resume/bbp_actual_odd_quotient_attack.md"
    )
    source_digest = sha256(source_path)
    parent_digest = sha256(parent_path)
    assert source_digest == SOURCE_SHA256
    assert parent_digest == PARENT_REPORT_SHA256

    primes = primes_through(8 * args.max_depth + 5)
    partial_sum = Fraction()
    five_denominator_checks = 0
    controlled_coordinate_checks = 0
    exact_row_checks = 0
    record_hasher = hashlib.sha256()

    classifications = {
        label: Counter() for label in CUTOFF_LABELS
    }
    obstruction_primes = {
        label: Counter() for label in CUTOFF_LABELS
    }
    exact_hits = Counter()
    aggregate: dict[str, dict[str, tuple[float, tuple[int, ...]] | None]] = {
        label: {
            "gcd": None,
            "tail_gcd": None,
            "centered": None,
            "tail_centered": None,
        }
        for label in CUTOFF_LABELS
    }
    centered_exact: dict[str, dict[str, tuple[int, int] | None]] = {
        label: {"centered": None, "tail_centered": None}
        for label in CUTOFF_LABELS
    }
    samples: dict[tuple[int, str], tuple[int, dict[int, int], int, int]] = {}
    exceptional_rows: dict[str, list[tuple[int, str, tuple[int, ...]]]] = {
        label: [] for label in CUTOFF_LABELS
    }

    for depth in range(args.max_depth + 1):
        partial_sum += coefficient(depth) / 16**depth
        size = 8 * depth + 5
        five_exponent = floor_log(5, size)
        assert valuation(partial_sum.denominator, 5) == five_exponent
        five_denominator_checks += 1
        if depth < 48:
            continue

        two_exponent = 4 * depth - valuation(depth + 1, 2)
        assert valuation(partial_sum.denominator, 2) == two_exponent
        odd_denominator = partial_sum.denominator >> two_exponent
        factors = factor(odd_denominator, primes)
        assert factors[5] == five_exponent

        dyadic_modulus = 1 << (two_exponent - 4)
        dyadic_coordinate = (
            partial_sum.numerator
            * pow(odd_denominator, -1, dyadic_modulus)
        ) % dyadic_modulus
        odd_numerator = (
            partial_sum.numerator
            - odd_denominator * dyadic_coordinate
        ) // dyadic_modulus
        assert math.gcd(odd_numerator, odd_denominator) == 1

        # Verify once per (M,p) that every actually surviving simple-pole
        # prime above sqrt(X) has the advertised explicit additive coordinate.
        for prime, exponent in factors.items():
            if prime <= math.isqrt(size):
                continue
            assert prime > 5 and exponent == 1 and prime * prime > size
            local = localization(depth, prime)
            predicted = (
                local.numerator * pow(local.denominator, -1, prime)
            ) % prime
            assert predicted
            actual = (
                odd_numerator
                * pow(odd_denominator // prime, -1, prime)
            ) % prime
            assert actual == predicted
            controlled_coordinate_checks += 1

        upper = len(str(16**depth)) - 1
        assert 10**upper <= 16**depth < 10 ** (upper + 1)

        for label in CUTOFF_LABELS:
            cutoff = cutoff_value(label, depth, size)
            cofactor = odd_denominator
            cofactor_factors = dict(factors)
            for prime, exponent in factors.items():
                if prime > cutoff and prime * prime > size:
                    assert exponent == 1
                    cofactor //= prime
                    del cofactor_factors[prime]
            assert math.prod(
                prime**exponent
                for prime, exponent in cofactor_factors.items()
            ) == cofactor
            assert cofactor_factors[5] == five_exponent
            if label == "sqrt(X)":
                assert max(cofactor_factors) <= math.isqrt(size)

            classification, detail = classify_fifteen_free_orbit(
                cofactor_factors
            )
            classifications[label][classification] += 1
            if classification == "local":
                obstruction_primes[label][detail[0]] += 1
            else:
                exceptional_rows[label].append(
                    (depth, classification, detail)
                )

            best_gcd = 1
            best_gcd_exponent = depth
            best_centered = cofactor
            best_centered_exponent = depth
            power = pow(10, depth, cofactor)
            for decimal_exponent in range(depth, upper + 1):
                residue = (power - 16) % cofactor
                assert residue
                difference_gcd = math.gcd(residue, cofactor)
                assert valuation(residue, 5) == 0
                assert valuation(residue, 3) == 1
                assert valuation(difference_gcd, 5) == 0
                assert valuation(difference_gcd, 3) == min(
                    cofactor_factors.get(3, 0), 1
                )
                centered = min(residue, cofactor - residue)
                if difference_gcd > best_gcd:
                    best_gcd = difference_gcd
                    best_gcd_exponent = decimal_exponent
                if centered < best_centered:
                    best_centered = centered
                    best_centered_exponent = decimal_exponent
                power = power * 10 % cofactor
                exact_row_checks += 1

            if best_centered == 0:
                exact_hits[label] += 1

            gcd_score = math.log(best_gcd) / math.log(cofactor)
            gcd_record = (
                depth,
                best_gcd_exponent,
                best_gcd,
                cofactor.bit_length(),
            )
            old_gcd = aggregate[label]["gcd"]
            if old_gcd is None or gcd_score > old_gcd[0]:
                aggregate[label]["gcd"] = (gcd_score, gcd_record)
            if depth >= 500:
                old_tail_gcd = aggregate[label]["tail_gcd"]
                if old_tail_gcd is None or gcd_score > old_tail_gcd[0]:
                    aggregate[label]["tail_gcd"] = (
                        gcd_score,
                        gcd_record,
                    )

            centered_pair = (best_centered, cofactor)
            old_pair = centered_exact[label]["centered"]
            if better_ratio(best_centered, cofactor, old_pair):
                centered_exact[label]["centered"] = centered_pair
                aggregate[label]["centered"] = (
                    best_centered / cofactor,
                    (
                        depth,
                        best_centered_exponent,
                        best_centered,
                        cofactor.bit_length(),
                    ),
                )
            if depth >= 500:
                old_tail_pair = centered_exact[label]["tail_centered"]
                if better_ratio(best_centered, cofactor, old_tail_pair):
                    centered_exact[label]["tail_centered"] = centered_pair
                    aggregate[label]["tail_centered"] = (
                        best_centered / cofactor,
                        (
                            depth,
                            best_centered_exponent,
                            best_centered,
                            cofactor.bit_length(),
                        ),
                    )

            if depth in SAMPLE_DEPTHS:
                samples[depth, label] = (
                    cofactor,
                    cofactor_factors,
                    best_gcd,
                    best_centered,
                )

            factor_text = ",".join(
                f"{prime}^{exponent}"
                for prime, exponent in cofactor_factors.items()
            )
            record = (
                f"{depth}|{label}|{cofactor}|{factor_text}|{depth}|{upper}|"
                f"{best_gcd_exponent}|{best_gcd}|{best_centered_exponent}|"
                f"{best_centered}|{classification}|{detail}\n"
            )
            record_hasher.update(record.encode())
            if args.show_exact:
                print("exact_record=" + record.rstrip())

    expected_rows = args.max_depth - 47
    assert exact_hits == Counter()
    for label in CUTOFF_LABELS:
        assert sum(classifications[label].values()) == expected_rows

    print("claim_status=experiment")
    print(f"source_sha256={source_digest}")
    print(f"parent_report_sha256={parent_digest}")
    print(f"depth_range=48..{args.max_depth}")
    print(f"five_denominator_checks={five_denominator_checks}")
    print(f"controlled_sqrt_coordinate_checks={controlled_coordinate_checks}")
    print(f"short_orbit_exact_checks={exact_row_checks}")
    print(f"exact_record_sha256={record_hasher.hexdigest()}")
    for label in CUTOFF_LABELS:
        counts = classifications[label]
        print(
            f"cutoff={label}:exact_hits={exact_hits[label]}:"
            f"local_obstruction={counts['local']}:"
            f"compatibility_obstruction={counts['incompatible']}:"
            f"global_class={counts['class']}:"
            f"first_obstruction_primes={dict(obstruction_primes[label])}"
        )
        print(
            f"cutoff={label}:exceptional_rows="
            f"{exceptional_rows[label]}"
        )
        for metric in ("gcd", "tail_gcd", "centered", "tail_centered"):
            result = aggregate[label][metric]
            assert result is not None
            print(
                f"cutoff={label}:{metric}_score={result[0]:.15g}:"
                f"record={result[1]}"
            )

    for depth in SAMPLE_DEPTHS:
        for label in CUTOFF_LABELS:
            cofactor, factors, best_gcd, best_centered = samples[depth, label]
            print(
                f"sample=M{depth}:{label}:bits={cofactor.bit_length()}:"
                f"logC_over_M={math.log(cofactor) / depth:.15g}:"
                f"Pplus={max(factors)}:v3={factors.get(3, 0)}:"
                f"v5={factors[5]}:best_gcd={best_gcd}:"
                f"best_centered_ratio={best_centered / cofactor:.15g}"
            )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
