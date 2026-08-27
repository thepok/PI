#!/usr/bin/env python3
"""Analyze retained exact Machin-forcing rows without upgrading finite data."""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter, defaultdict
from pathlib import Path


def berlekamp_massey(sequence: list[int], prime: int) -> int:
    """Return linear complexity over F_prime."""
    connection = [1]
    previous = [1]
    length = 0
    shift = 1
    last_discrepancy = 1
    for index, value in enumerate(sequence):
        discrepancy = value % prime
        for offset in range(1, length + 1):
            discrepancy = (
                discrepancy + connection[offset] * sequence[index - offset]
            ) % prime
        if discrepancy == 0:
            shift += 1
            continue
        old_connection = connection[:]
        coefficient = discrepancy * pow(last_discrepancy, -1, prime) % prime
        required = len(previous) + shift
        if len(connection) < required:
            connection.extend([0] * (required - len(connection)))
        for offset, item in enumerate(previous):
            connection[offset + shift] = (
                connection[offset + shift] - coefficient * item
            ) % prime
        if 2 * length <= index:
            length = index + 1 - length
            previous = old_connection
            last_discrepancy = discrepancy
            shift = 1
        else:
            shift += 1
    return length


def prime_free_part(value: int, prime: int) -> int:
    while value % prime == 0:
        value //= prime
    return value


def factor_small(value: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    candidate = 2
    while candidate * candidate <= value:
        while value % candidate == 0:
            factors[candidate] = factors.get(candidate, 0) + 1
            value //= candidate
        candidate += 1
    if value > 1:
        factors[value] = factors.get(value, 0) + 1
    return factors


def valuation(value: int, prime: int) -> int:
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def multiplicative_order(value: int, prime: int) -> int:
    assert math.gcd(value, prime) == 1
    order = prime - 1
    for factor in factor_small(order):
        while order % factor == 0 and pow(value, order // factor, prime) == 1:
            order //= factor
    return order


def factor_string_to_map(text: str) -> dict[int, int]:
    result: dict[int, int] = {}
    for part in text.split("*"):
        if part.startswith("cofactor"):
            continue
        if "^" in part:
            prime, exponent = part.split("^", 1)
            result[int(prime)] = int(exponent)
        elif part:
            result[int(part)] = 1
    return result


def load_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--bm-prefix", type=int, default=2000)
    args = parser.parse_args()

    # Known-answer controls for the recurrence detector.
    assert berlekamp_massey([7] * 30, 101) == 1
    fibonacci = [0, 1]
    for _ in range(28):
        fibonacci.append((fibonacci[-1] + fibonacci[-2]) % 101)
    assert berlekamp_massey(fibonacci, 101) == 2

    rows = load_rows(args.data_dir / "rows.tsv")
    summary = json.loads((args.data_dir / "summary.json").read_text())
    cancellation_hits: dict[int, list[int]] = defaultdict(list)
    extra_rows: list[dict[str, object]] = []
    large_prime_certificates: list[dict[str, int | bool]] = []
    squarefree_failures: list[int] = []
    multi_extra_prime_rows: list[int] = []
    local_valuation_mismatches: list[dict[str, int]] = []
    for row in rows:
        n = int(row["N"])
        factors = factor_string_to_map(row["g_factorization"])
        extra_factors = {p: e for p, e in factors.items() if p != 3}
        if int(row["cancellation_g"]) != 3:
            extra_rows.append(
                {
                    "N": n,
                    "g": int(row["cancellation_g"]),
                    "factorization": row["g_factorization"],
                }
            )
        if any(exponent > 1 for exponent in extra_factors.values()):
            squarefree_failures.append(n)
        if len(extra_factors) > 1:
            multi_extra_prime_rows.append(n)
        for prime in extra_factors:
            cancellation_hits[prime].append(n)
            if prime >= 17 and prime != 239:
                locations = [
                    (index, 12 * n + 5 + 2 * index)
                    for index in range(1, 6)
                    if (12 * n + 5 + 2 * index) % prime == 0
                ]
                if len(locations) == 1:
                    index, exponent = locations[0]
                    quotient = prime_free_part(exponent, prime)
                    large_prime_certificates.append(
                        {
                            "N": n,
                            "prime": prime,
                            "interior_index": index,
                            "a": exponent,
                            "p_free_part_of_a": quotient,
                            "criterion_mod_prime": (
                                4 * pow(239, exponent, prime)
                                - pow(5, exponent, prime)
                            )
                            % prime,
                            "fermat_reduced_criterion_mod_prime": (
                                4 * pow(239, quotient, prime)
                                - pow(5, quotient, prime)
                            )
                            % prime,
                        }
                    )

        actual_g = int(row["cancellation_g"])
        for index in range(7):
            a = 12 * n + 5 + 2 * index
            for prime, exponent in factor_small(a).items():
                if prime < 7 or prime == 239:
                    continue
                expected = 0
                if 1 <= index <= 5:
                    modulus = prime**exponent
                    difference = (
                        4 * pow(239, a, modulus) - pow(5, a, modulus)
                    ) % modulus
                    if difference == 0:
                        expected = exponent
                    else:
                        expected = min(exponent, valuation(difference, prime))
                actual = valuation(actual_g, prime)
                if expected != actual:
                    local_valuation_mismatches.append(
                        {
                            "N": n,
                            "prime": prime,
                            "index": index,
                            "a": a,
                            "expected_vp_g": expected,
                            "actual_vp_g": actual,
                        }
                    )

    gcd_rows = load_rows(args.data_dir / "gcd_events.tsv")
    gcd_by_lag: dict[int, list[dict[str, int]]] = defaultdict(list)
    for row in gcd_rows:
        gcd_by_lag[int(row["lag"])].append(
            {
                "N": int(row["N"]),
                "gcd": int(row["gcd_normalized_odd_numerators"]),
            }
        )

    residue_primes = [101, 251, 1009]
    bm_length = min(args.bm_prefix, len(rows))
    recurrence_tests: list[dict[str, int | str]] = []
    residue_stats: list[dict[str, int | float | str]] = []
    for prime in residue_primes:
        for kind in ("u_num", "u_lcd"):
            column = f"{kind}_mod_{prime}"
            sequence = [int(row[column]) for row in rows]
            recurrence_tests.append(
                {
                    "sequence": kind,
                    "prime": prime,
                    "prefix_length": bm_length,
                    "linear_complexity": berlekamp_massey(
                        sequence[:bm_length], prime
                    ),
                }
            )
            counts = Counter(sequence)
            expected = len(sequence) / prime
            chi_square = sum(
                (counts[value] - expected) ** 2 / expected
                for value in range(prime)
            )
            residue_stats.append(
                {
                    "sequence": kind,
                    "prime": prime,
                    "distinct_residues": len(counts),
                    "sample_size": len(sequence),
                    "min_count": min(counts.get(value, 0) for value in range(prime)),
                    "max_count": max(counts.get(value, 0) for value in range(prime)),
                    "chi_square": chi_square,
                }
            )

    code_counts = {}
    for digits in range(1, 5):
        code_counts[str(digits)] = len({int(row[f"code{digits}"]) for row in rows})

    prime_period_data = []
    for prime in sorted(cancellation_hits):
        if prime < 7 or prime == 239:
            continue
        ratio = 239 * pow(5, -1, prime) % prime
        order = multiplicative_order(ratio, prime)
        target_exponents = [
            exponent
            for exponent in range(order)
            if 4 * pow(ratio, exponent, prime) % prime == 1
        ]
        prime_period_data.append(
            {
                "prime": prime,
                "ratio_239_over_5": ratio,
                "multiplicative_order": order,
                "target_exponents_mod_order": target_exponents,
                "fixed_index_period_bound": (
                    prime * order // math.gcd(12, order)
                ),
                "observed_N": cancellation_hits[prime],
            }
        )

    output = {
        "claim_status": "experiment",
        "source_summary": summary,
        "extra_cancellation_row_count": len(extra_rows),
        "extra_cancellation_rows": extra_rows,
        "extra_cancellation_hits_by_prime": {
            str(prime): hits for prime, hits in sorted(cancellation_hits.items())
        },
        "large_prime_local_cancellation_certificates": large_prime_certificates,
        "local_prime_adic_valuation_mismatches": local_valuation_mismatches,
        "fixed_prime_period_data": prime_period_data,
        "first_counterexample_to_g_equals_3": extra_rows[0] if extra_rows else None,
        "first_counterexample_to_extra_squarefree": (
            squarefree_failures[0] if squarefree_failures else None
        ),
        "first_row_with_multiple_extra_primes": (
            multi_extra_prime_rows[0] if multi_extra_prime_rows else None
        ),
        "nearby_normalized_odd_numerator_gcd_events": {
            str(lag): events for lag, events in sorted(gcd_by_lag.items())
        },
        "linear_recurrence_tests": recurrence_tests,
        "residue_statistics": residue_stats,
        "code_distinct_counts_recomputed": code_counts,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
