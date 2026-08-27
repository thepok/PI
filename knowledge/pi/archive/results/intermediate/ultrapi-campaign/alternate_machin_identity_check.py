#!/usr/bin/env python3
"""Exact checks for the alternate Machin-identity coupling attack.

This is an experiment/checker, not a proof that every finite decimal word
occurs in pi.  The companion report proves the general algebraic identities;
this script replays them over exact ``Fraction`` arithmetic on a substantial
finite range and records the actual denominator interaction.
"""

from __future__ import annotations

import hashlib
import math
from fractions import Fraction
from pathlib import Path


SOURCE_SHA256 = "2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gaussian_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def gaussian_pow(value: tuple[int, int], exponent: int) -> tuple[int, int]:
    result = (1, 0)
    for _ in range(exponent):
        result = gaussian_mul(result, value)
    return result


def arctan_term(q: int, n: int) -> Fraction:
    return Fraction((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))


def arctan_partial(q: int, terms: int) -> Fraction:
    return sum((arctan_term(q, n) for n in range(terms)), Fraction())


def hutton_lower(k: int) -> Fraction:
    """4*(2 atan(1/3)+atan(1/7)), using equal even truncations."""
    terms = 2 * (k + 1)
    return 8 * arctan_partial(3, terms) + 4 * arctan_partial(7, terms)


def hutton_upper(k: int) -> Fraction:
    """The adjacent odd Taylor truncation, an exact rational upper bound."""
    terms = 2 * (k + 1) + 1
    return 8 * arctan_partial(3, terms) + 4 * arctan_partial(7, terms)


def machin_lower(k: int) -> Fraction:
    """The exact T36 lower 5/239 Machin truncation."""
    return (
        16 * arctan_partial(5, 2 * (k + 1))
        - 4 * arctan_partial(239, 2 * (k + 1) + 1)
    )


def machin_upper(k: int) -> Fraction:
    """Swap both Taylor parities in T36 to obtain a rational upper bound."""
    return (
        16 * arctan_partial(5, 2 * (k + 1) + 1)
        - 4 * arctan_partial(239, 2 * (k + 1))
    )


def fraction_part(value: Fraction) -> Fraction:
    return value - value.numerator // value.denominator


def valuation(n: int, p: int) -> int:
    assert n > 0 and p > 1
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer


def odd_lcm(bound: int) -> int:
    result = 1
    for value in range(1, bound + 1, 2):
        result = math.lcm(result, value)
    return result


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    source = root / "problems/local/pi-digits.txt"
    assert sha256(source) == SOURCE_SHA256

    # Exact Gaussian-integer certificates.  Dividing each equality by its
    # conjugate gives the relevant unit-circle identity, with positive-angle
    # branch selection supplied in the companion proof.
    assert gaussian_mul((2, 1), (3, 1)) == (5, 5)
    assert gaussian_mul((3, 1), (7, 1)) == (20, 10)
    assert gaussian_mul(gaussian_pow((3, 1), 2), (7, 1)) == (50, 50)
    assert gaussian_mul(gaussian_pow((2, 1), 2), (7, -1)) == (25, 25)
    assert gaussian_mul(gaussian_pow((5, 1), 4), (239, -1)) == (114244, 114244)
    gaussian_checks = 5

    recurrence_checks = 0
    denominator_clearing_checks = 0
    for k in range(31):
        # Adding one outer index adds exactly one positive adjacent pair in
        # each Hutton series and the signed T36 pairs in the Machin series.
        h_step = hutton_lower(k + 1) - hutton_lower(k)
        expected_h_step = 8 * (
            arctan_term(3, 2 * (k + 1))
            + arctan_term(3, 2 * (k + 1) + 1)
        ) + 4 * (
            arctan_term(7, 2 * (k + 1))
            + arctan_term(7, 2 * (k + 1) + 1)
        )
        assert h_step == expected_h_step and h_step > 0

        m_step = machin_lower(k + 1) - machin_lower(k)
        expected_m_step = 16 * (
            arctan_term(5, 2 * (k + 1))
            + arctan_term(5, 2 * (k + 1) + 1)
        ) - 4 * (
            arctan_term(239, 2 * (k + 1) + 1)
            + arctan_term(239, 2 * (k + 1) + 2)
        )
        assert m_step == expected_m_step and m_step > 0
        recurrence_checks += 2

        # Safe natural common denominators.  This does not assert that they
        # are reduced; divisibility is the exact claim used in the report.
        h_bound = 4 * k + 3
        h_natural = odd_lcm(h_bound) * 3**h_bound * 7**h_bound
        assert h_natural % hutton_lower(k).denominator == 0

        m_bound = 4 * k + 5
        m_natural = odd_lcm(m_bound) * 5 ** (4 * k + 3) * 239**m_bound
        assert m_natural % machin_lower(k).denominator == 0
        denominator_clearing_checks += 2

    order_bound_checks = 0
    nested_rational_checks = 0
    nested_bracket_checks = 0
    coupling_checks = 0
    common_lift_checks = 0
    denominator_rows: list[tuple[int, int, int, int, int, int, int, int, int]] = []

    # The displayed integer inequality is the exact comparison between the
    # Hutton upper tail bound and the Machin lower tail bound.
    for j in range(1, 201):
        h_exponent = 20 * j + 5
        m_exponent = 12 * j + 5
        assert (
            32 * h_exponent * 3**h_exponent
            > 25 * m_exponent * 5**m_exponent
        )
        order_bound_checks += 1

        # The analogous comparison for the two upper overshoots proves
        # Hutton_upper < Machin_upper for j >= 2.  The sole j=1 case is
        # checked directly below over exact fractions.
        if j >= 2:
            upper_h_exponent = 20 * j + 7
            upper_m_exponent = 12 * j + 7
            assert (
                32 * upper_h_exponent * 3**upper_h_exponent
                > 25 * upper_m_exponent * 5**upper_m_exponent
            )
            order_bound_checks += 1

    for j in range(1, 41):
        h = hutton_lower(5 * j)
        h_upper = hutton_upper(5 * j)
        m = machin_lower(3 * j)
        m_upper = machin_upper(3 * j)
        assert m < h
        assert h < h_upper < m_upper
        nested_rational_checks += 1
        nested_bracket_checks += 2

        d = 10**j * (h - m)
        h_next = hutton_lower(5 * (j + 1))
        m_next = machin_lower(3 * (j + 1))
        d_next = 10 ** (j + 1) * (h_next - m_next)
        forcing_h = 10 ** (j + 1) * (h_next - h)
        forcing_m = 10 ** (j + 1) * (m_next - m)
        assert forcing_h - forcing_m == d_next - 10 * d
        assert fraction_part(10**j * h) == fraction_part(
            fraction_part(10**j * m) + d
        )
        coupling_checks += 2

        # Lift both reduced fractions to one common denominator.  The second
        # residue is an exact translate of the first, rather than an
        # independent coordinate.
        common = math.lcm(h.denominator, m.denominator)
        h_lift = h.numerator * (common // h.denominator)
        m_lift = m.numerator * (common // m.denominator)
        h_residue = (10**j * h_lift) % common
        m_residue = (10**j * m_lift) % common
        offset = (10**j * (h_lift - m_lift)) % common
        assert (h_residue - m_residue) % common == offset
        assert Fraction(h_lift - m_lift, common) == h - m
        common_lift_checks += 2

        if j <= 10:
            gcd_den = math.gcd(h.denominator, m.denominator)
            denominator_rows.append(
                (
                    j,
                    h.denominator.bit_length(),
                    valuation(h.denominator, 3),
                    valuation(h.denominator, 7),
                    valuation(h.denominator, 5),
                    m.denominator.bit_length(),
                    gcd_den.bit_length(),
                    common.bit_length(),
                    (h - m).denominator.bit_length(),
                )
            )

    print("claim_status=experiment")
    print(f"source_sha256={SOURCE_SHA256}")
    print(f"gaussian_integer_exact_checks={gaussian_checks}")
    print(f"partial_sum_recurrence_exact_checks={recurrence_checks}")
    print(f"natural_denominator_divisibility_exact_checks={denominator_clearing_checks}")
    print(f"tail_order_integer_exact_checks={order_bound_checks}")
    print(f"nested_rational_exact_checks={nested_rational_checks}")
    print(f"nested_alternating_bracket_exact_checks={nested_bracket_checks}")
    print(f"sampled_coboundary_and_circle_exact_checks={coupling_checks}")
    print(f"common_denominator_affine_graph_exact_checks={common_lift_checks}")
    print(
        "denominator_rows=(j,H_bits,v3_H,v7_H,v5_H,M_bits,gcd_bits,lcm_bits,offset_bits):"
    )
    for row in denominator_rows:
        print(row)
    print("all exact assertions passed")


if __name__ == "__main__":
    main()
