#!/usr/bin/env python3
"""Independent replay for the exceptional aligned-phase audit.

This script does not import the primary checker.  It constructs the decimal
0/1 set with ``itertools.product``, solves the local congruences with SymPy's
general CRT routine instead of the primary hand-written merge, and certifies
the finite pi phases from rational alternating-series bounds for Machin's
formula rather than trusting a floating-point value of pi.

The enumeration is an experiment.  The rational interval computations and
the modular identities checked for each enumerated integer are exact.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import json
from math import gcd

from sympy import factorint
from sympy.core.random import seed as sympy_seed
from sympy.ntheory import discrete_log, n_order
from sympy.ntheory.modular import solve_congruence


MIN_DIGITS = 2
MAX_DIGITS = 12

# The enclosure asserted by the primary checker.  It is independently
# contained below inside a rational Machin-series enclosure.
PRIMARY_PI_DIGITS = (
    "3141592653589793238462643383279502884197169399375105820974944592"
    "3078164062862089986280348253421170679"
)
PRIMARY_PI_SCALE = 10 ** (len(PRIMARY_PI_DIGITS) - 1)
PRIMARY_PI_FLOOR = int(PRIMARY_PI_DIGITS)


def alternating_arctan_interval(q: int, even_term_count: int) -> tuple[Fraction, Fraction]:
    """Enclose atan(1/q) by two consecutive alternating partial sums."""
    assert q > 1
    assert even_term_count > 0 and even_term_count % 2 == 0
    lower = sum(
        (
            Fraction(1, (2 * n + 1) * q ** (2 * n + 1))
            if n % 2 == 0
            else -Fraction(1, (2 * n + 1) * q ** (2 * n + 1))
        )
        for n in range(even_term_count)
    )
    # An even number of terms ends in a negative term.  The next (positive)
    # partial sum is the alternating-series upper bound.
    n = even_term_count
    upper = lower + Fraction(1, (2 * n + 1) * q ** (2 * n + 1))
    assert lower < upper
    return lower, upper


def machin_pi_interval() -> tuple[Fraction, Fraction]:
    """Exact rational enclosure from pi = 16 atan(1/5) - 4 atan(1/239)."""
    low5, high5 = alternating_arctan_interval(5, 100)
    low239, high239 = alternating_arctan_interval(239, 100)
    lower = 16 * low5 - 4 * high239
    upper = 16 * high5 - 4 * low239
    assert lower < upper
    assert upper - lower < Fraction(1, 10**130)
    return lower, upper


def all_candidates() -> list[int]:
    """All distinct L-digit decimal 0/1 integers ending in 1, 2 <= L <= 12."""
    values: list[int] = []
    for length in range(MIN_DIGITS, MAX_DIGITS + 1):
        for middle in product("01", repeat=length - 2):
            d = int("1" + "".join(middle) + "1")
            assert len(str(d)) == length
            values.append(d)
    assert len(values) == sum(2 ** (length - 2) for length in range(2, 13))
    assert len(values) == len(set(values)) == 2047
    assert 11 in values
    return values


def modular_log(modulus: int) -> tuple[int, int] | None:
    """Return the unique log of 16 to base 10 modulo the generated subgroup."""
    order = int(n_order(10, modulus))
    try:
        residue = int(discrete_log(modulus, 16 % modulus, 10 % modulus)) % order
    except ValueError:
        return None
    assert 0 <= residue < order
    assert pow(10, residue, modulus) == 16 % modulus
    return residue, order


def classify(d: int) -> tuple[str, int | None, int | None]:
    """Classify by local subgroup membership and a library generalized CRT."""
    local: list[tuple[int, int]] = []
    for prime, exponent in factorint(d).items():
        datum = modular_log(int(prime**exponent))
        if datum is None:
            # A global solution would project to every prime power.
            assert modular_log(d) is None
            return "local_nonmembership", None, None
        local.append(datum)

    # solve_congruence is a separate implementation from the primary
    # pairwise merge.  Pairwise compatibility is also checked explicitly.
    pairwise_compatible = all(
        (a - b) % gcd(m, n) == 0
        for i, (a, m) in enumerate(local)
        for b, n in local[i + 1 :]
    )
    solved = solve_congruence(*local, check=True)
    assert (solved is not None) == pairwise_compatible
    if solved is None:
        assert modular_log(d) is None
        return "crt_incompatibility", None, None

    residue, period = map(int, solved)
    global_datum = modular_log(d)
    assert global_datum is not None
    global_residue, global_period = global_datum
    assert period == global_period
    assert residue % period == global_residue
    return "aligned", global_residue, global_period


def circle_distance_lower_bound(
    d: int, pi_lower: Fraction, pi_upper: Fraction
) -> Fraction:
    """Exact lower bound for ||d*pi|| from a rational pi enclosure."""
    lower = d * pi_lower
    upper = d * pi_upper
    integer_part = lower.numerator // lower.denominator
    assert upper.numerator // upper.denominator == integer_part
    answer = min(lower - integer_part, integer_part + 1 - upper)
    assert answer > 0
    return answer


def main() -> None:
    sympy_seed(1729)

    pi_lower, pi_upper = machin_pi_interval()
    stored_lower = Fraction(PRIMARY_PI_FLOOR, PRIMARY_PI_SCALE)
    stored_upper = Fraction(PRIMARY_PI_FLOOR + 1, PRIMARY_PI_SCALE)
    assert stored_lower < pi_lower < pi_upper < stored_upper

    counts: Counter[str] = Counter()
    by_length: dict[int, Counter[str]] = defaultdict(Counter)
    aligned: list[tuple[int, int, int, Fraction]] = []

    for d in all_candidates():
        kind, exponent, period = classify(d)
        counts[kind] += 1
        by_length[len(str(d))][kind] += 1
        if kind == "aligned":
            assert exponent is not None and period is not None
            assert pow(10, exponent, d) == 16 % d
            aligned.append(
                (
                    d,
                    exponent,
                    period,
                    circle_distance_lower_bound(d, pi_lower, pi_upper),
                )
            )

    expected_by_length = {
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
    assert counts == Counter(
        aligned=532, local_nonmembership=1277, crt_incompatibility=238
    )
    assert {
        length: by_length[length]["aligned"] for length in expected_by_length
    } == expected_by_length

    least_exponent = min(aligned, key=lambda row: row[1])
    assert least_exponent[:3] == (1101, 190, 366)

    least_phase = min(aligned, key=lambda row: row[3])
    assert least_phase[:3] == (10010100101, 948452584, 10010100100)
    assert Fraction(473089040236, 10**16) < least_phase[3]
    assert least_phase[3] < Fraction(473089040237, 10**16)
    assert least_phase[3] > Fraction(4, 100_000)

    minimum_gap = min(
        exponent - len(str(d)) - 1 for d, exponent, _, _ in aligned
    )
    assert minimum_gap == 185
    assert Fraction(4, 100_000) * 10**minimum_gap > 10**180

    # Independent representative replay of every classification mechanism.
    assert classify(101) == ("local_nonmembership", None, None)
    assert classify(1011) == ("aligned", 208, 336)
    assert classify(111101) == ("crt_incompatibility", None, None)
    assert modular_log(241) == (25, 30)
    assert modular_log(461) == (216, 460)
    assert (216 - 25) % gcd(30, 460) != 0

    # Exact arithmetic behind the irrationality-measure exponents.
    eta = Fraction(888, 125)
    published_decimal_truncation = Fraction(7103205334137, 10**12)
    assert published_decimal_truncation < eta
    assert eta - 1 == Fraction(763, 125)
    assert 1 / eta == Fraction(125, 888)
    assert (eta - 1) / eta == Fraction(763, 888)

    print(
        json.dumps(
            {
                "status": "PASS",
                "claim_label": "experiment",
                "candidate_count": 2047,
                "classification_counts": dict(sorted(counts.items())),
                "aligned_by_decimal_length": expected_by_length,
                "least_first_alignment": {
                    "d": least_exponent[0],
                    "N0": least_exponent[1],
                    "period": least_exponent[2],
                },
                "least_phase_row": {
                    "d": least_phase[0],
                    "N0": least_phase[1],
                    "certified_between": [
                        "0.0000473089040236",
                        "0.0000473089040237",
                    ],
                },
                "minimum_N_minus_digits_minus_one": minimum_gap,
                "pi_enclosure": "exact Machin alternating-series interval",
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
