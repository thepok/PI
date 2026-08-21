#!/usr/bin/env python3
"""Finite exact replay for exceptional_aligned_phase_attack.md.

The modular calculations use exact integer arithmetic.  The only real-number
input is a stored 100-decimal-place enclosure for pi; it is used solely for a
bounded experiment, never for a proof claim about V1.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
import json

from sympy import factorint
from sympy.core.random import seed as sympy_seed
from sympy.ntheory import discrete_log, n_order


MAX_DIGITS = 12

# floor(pi * 10^100).  Thus PI_FLOOR / PI_SCALE < pi <
# (PI_FLOOR + 1) / PI_SCALE.  This enclosure is used only in the explicitly
# bounded experiment below.
PI_DIGITS = (
    "3141592653589793238462643383279502884197169399375105820974944592"
    "3078164062862089986280348253421170679"
)
PI_SCALE = 10 ** (len(PI_DIGITS) - 1)
PI_FLOOR = int(PI_DIGITS)


def merge_congruences(
    a: int, modulus_a: int, b: int, modulus_b: int
) -> tuple[int, int] | None:
    """Merge x=a (mod modulus_a), x=b (mod modulus_b), if compatible."""
    common = gcd(modulus_a, modulus_b)
    if (b - a) % common:
        return None
    reduced_a = modulus_a // common
    reduced_b = modulus_b // common
    step = ((b - a) // common * pow(reduced_a, -1, reduced_b)) % reduced_b
    modulus = modulus_a * reduced_b
    return (a + modulus_a * step) % modulus, modulus


def local_log_data(d: int) -> list[tuple[int, int]] | None:
    """Return local discrete logs and orders, or None for local failure."""
    data: list[tuple[int, int]] = []
    for prime, exponent in factorint(d).items():
        prime_power = prime**exponent
        order = int(n_order(10, prime_power))
        try:
            residue = int(
                discrete_log(prime_power, 16 % prime_power, 10 % prime_power)
            ) % order
        except ValueError:
            return None
        assert pow(10, residue, prime_power) == 16 % prime_power
        data.append((residue, order))
    return data


def first_aligned_exponent(d: int) -> tuple[str, int | None, int | None]:
    """Classify d and return its least nonnegative exponent when aligned."""
    local = local_log_data(d)
    if local is None:
        return "local_nonmembership", None, None

    residue, period = local[0]
    for next_residue, next_period in local[1:]:
        merged = merge_congruences(residue, period, next_residue, next_period)
        if merged is None:
            return "crt_incompatibility", None, None
        residue, period = merged

    global_period = int(n_order(10, d))
    direct = int(discrete_log(d, 16 % d, 10 % d)) % global_period
    assert period == global_period
    assert residue == direct
    assert 0 <= residue < global_period
    assert pow(10, residue, d) == 16 % d
    return "aligned", residue, global_period


def phase_lower_bound(d: int) -> Fraction:
    """Lower-bound ||d*pi|| from the stored rational enclosure."""
    low = d * PI_FLOOR
    high = d * (PI_FLOOR + 1)
    assert low // PI_SCALE == high // PI_SCALE
    distance_numerator = min(low % PI_SCALE, PI_SCALE - high % PI_SCALE)
    assert distance_numerator > 0
    return Fraction(distance_numerator, PI_SCALE)


def main() -> None:
    # SymPy's Pollard-rho helper can make randomized internal choices.  The
    # seed makes this bounded replay reproducible; every returned log is also
    # checked by direct modular exponentiation above.
    sympy_seed(0)

    classifications: Counter[str] = Counter()
    by_length: dict[int, Counter[str]] = defaultdict(Counter)
    aligned_rows: list[tuple[int, int, int, Fraction]] = []
    candidates_seen: set[int] = set()

    for digits in range(2, MAX_DIGITS + 1):
        for middle in range(1 << (digits - 2)):
            middle_digits = (
                "" if digits == 2 else format(middle, f"0{digits - 2}b")
            )
            d = int("1" + middle_digits + "1")
            assert len(str(d)) == digits
            assert d not in candidates_seen
            candidates_seen.add(d)
            kind, exponent, period = first_aligned_exponent(d)
            classifications[kind] += 1
            by_length[digits][kind] += 1
            if kind == "aligned":
                assert exponent is not None and period is not None
                aligned_rows.append((d, exponent, period, phase_lower_bound(d)))

    expected_aligned = {
        2: 0,
        3: 0,
        4: 2,
        5: 4,
        6: 6,
        7: 8,
        8: 19,
        9: 41,
        10: 55,
        11: 156,
        12: 241,
    }
    assert sum(classifications.values()) == 2047
    assert len(candidates_seen) == 2047
    assert 11 in candidates_seen
    assert classifications == Counter(
        {
            "local_nonmembership": 1277,
            "aligned": 532,
            "crt_incompatibility": 238,
        }
    )
    assert {
        digits: by_length[digits]["aligned"] for digits in expected_aligned
    } == expected_aligned

    minimum_exponent_row = min(aligned_rows, key=lambda row: row[1])
    assert minimum_exponent_row[:2] == (1101, 190)

    minimum_phase_row = min(aligned_rows, key=lambda row: row[3])
    assert minimum_phase_row[0:2] == (10010100101, 948452584)
    assert minimum_phase_row[3] > Fraction(4, 100_000)

    # If d has L digits, n is an aligned exponent, and k=(10^n-16)/d,
    # then k > 10^(n-L-1).  In this finite box n-L-1 >= 185 and every
    # certified phase is > 4*10^-5, so k*||d*pi|| > 10^180.
    minimum_exponent_gap = min(
        exponent - len(str(d)) - 1 for d, exponent, _, _ in aligned_rows
    )
    assert minimum_exponent_gap == 185
    assert Fraction(4, 100_000) * 10**minimum_exponent_gap > 10**180

    # Exact representatives of the three CRT classifications.
    assert first_aligned_exponent(101)[0] == "local_nonmembership"
    assert first_aligned_exponent(1011) == ("aligned", 208, 336)
    assert first_aligned_exponent(111101)[0] == "crt_incompatibility"

    output = {
        "status": "PASS",
        "claim_label": "experiment",
        "digit_box": {"minimum": 2, "maximum": MAX_DIGITS},
        "candidate_count": sum(classifications.values()),
        "classification_counts": dict(sorted(classifications.items())),
        "aligned_by_decimal_length": expected_aligned,
        "least_first_alignment": {
            "d": minimum_exponent_row[0],
            "N0": minimum_exponent_row[1],
            "period": minimum_exponent_row[2],
        },
        "smallest_phase_lower_bound_row": {
            "d": minimum_phase_row[0],
            "N0": minimum_phase_row[1],
            "lower_bound_decimal": float(minimum_phase_row[3]),
        },
        "uniform_first_alignment_product_certificate": {
            "minimum_N_minus_digits_minus_one": minimum_exponent_gap,
            "phase_lower_bound": "4e-5",
            "conclusion": "k*||d*pi|| > 1e180",
        },
    }
    print(json.dumps(output, sort_keys=True))


if __name__ == "__main__":
    main()
