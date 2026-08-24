#!/usr/bin/env python3
"""Exact certificate for the T122 q=2 Jackson aggregation separator.

The script uses only Fraction arithmetic and the cyclotomic relation
Phi_7(z) = 1 + z + ... + z^6 = 0. No floating-point arithmetic is used.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from typing import DefaultDict, Iterable

Q = Fraction


def edge_frequency(side: bool, r: int, n: int) -> int:
    return n - r if side else -r


def edge_sign(side: bool) -> int:
    return -1 if side else 1


def jackson_terms(q: int, n: int) -> list[tuple[int, Fraction]]:
    """Return (frequency, coefficient) from the Lean Jackson presentation."""
    if q <= 0 or n <= 0:
        raise ValueError("q and n must be positive")

    out: list[tuple[int, Fraction]] = []

    # Sum.inl quadruple indices.
    quad_coefficient = Q(2, q * q * n * n)
    for r in range(n):
        for s in range(n):
            for u in range(n):
                for v in range(n):
                    out.append(((s - r) + (v - u), quad_coefficient))

    # Sum.inr edge-pair indices.
    for left_side in (False, True):
        for r in range(n):
            for right_side in (False, True):
                for s in range(n):
                    frequency = (
                        edge_frequency(right_side, s, n)
                        - edge_frequency(left_side, r, n)
                    )
                    coefficient = -Q(
                        edge_sign(left_side) * edge_sign(right_side),
                        2 * n * n,
                    )
                    out.append((frequency, coefficient))

    return out


# Q[z]/(Phi_7), represented in the basis 1,z,...,z^5.
Cyclotomic7 = tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Fraction]


def zeta_power(exponent: int) -> Cyclotomic7:
    r = exponent % 7
    if r < 6:
        return tuple(Q(1) if i == r else Q(0) for i in range(6))  # type: ignore[return-value]
    # z^6 = -(1 + z + ... + z^5) modulo Phi_7.
    return (Q(-1),) * 6


def add_cyclotomic(values: Iterable[Cyclotomic7]) -> Cyclotomic7:
    total = [Q(0)] * 6
    for value in values:
        for i, coefficient in enumerate(value):
            total[i] += coefficient
    return tuple(total)  # type: ignore[return-value]


def exponential_sum_grid7_plus_zero(frequency: int) -> Cyclotomic7:
    # x_0,...,x_6 = 0/7,...,6/7 and x_7 = 0.
    return add_cyclotomic(
        [zeta_power(frequency * j) for j in range(7)] + [zeta_power(0)]
    )


def main() -> None:
    q = n = 2
    terms = jackson_terms(q, n)
    assert len(terms) == 32

    aggregate: DefaultDict[int, Fraction] = defaultdict(Fraction)
    absolute_mass_by_frequency: DefaultDict[int, Fraction] = defaultdict(Fraction)
    multiplicity: Counter[int] = Counter()

    for frequency, coefficient in terms:
        aggregate[frequency] += coefficient
        absolute_mass_by_frequency[frequency] += abs(coefficient)
        multiplicity[frequency] += 1

    expected_aggregate = {
        -3: Q(1, 8),
        -2: Q(3, 8),
        -1: Q(3, 8),
        0: Q(1, 4),
        1: Q(3, 8),
        2: Q(3, 8),
        3: Q(1, 8),
    }
    assert dict(sorted(aggregate.items())) == expected_aggregate

    expected_multiplicity = {
        -3: 1,
        -2: 3,
        -1: 7,
        0: 10,
        1: 7,
        2: 3,
        3: 1,
    }
    assert dict(sorted(multiplicity.items())) == expected_multiplicity

    total_index_mass = sum(abs(coefficient) for _, coefficient in terms)
    nonzero_index_mass = sum(
        abs(coefficient) for frequency, coefficient in terms if frequency != 0
    )
    nonzero_aggregated_mass = sum(
        abs(coefficient)
        for frequency, coefficient in aggregate.items()
        if frequency != 0
    )

    assert total_index_mass == Q(4)
    assert nonzero_index_mass == Q(11, 4)
    assert nonzero_aggregated_mass == Q(7, 4)

    # Exact roots-of-unity certificate: each nonzero Jackson frequency has
    # S_h(8)=1 on the seven-point grid plus one repeated zero.
    one: Cyclotomic7 = (Q(1), Q(0), Q(0), Q(0), Q(0), Q(0))
    nonzero_support = sorted(
        frequency for frequency in aggregate if frequency != 0
    )
    assert nonzero_support == [-3, -2, -1, 1, 2, 3]
    for frequency in nonzero_support:
        residues = sorted((frequency * j) % 7 for j in range(7))
        assert residues == list(range(7))
        assert exponential_sum_grid7_plus_zero(frequency) == one

    N = 8
    aggregated_load = nonzero_aggregated_mass / N
    index_weighted_load = nonzero_index_mass / N
    zero_mode_threshold = Q(1, 3 * q) + Q(2, 3 * q**3)

    assert aggregated_load == Q(7, 32)
    assert index_weighted_load == Q(11, 32)
    assert zero_mode_threshold == Q(1, 4)
    assert aggregated_load < zero_mode_threshold < index_weighted_load

    print("T122 q=2 separator: exact certificate passed")
    print("aggregate coefficients:", dict(sorted(aggregate.items())))
    print("frequency multiplicities:", dict(sorted(multiplicity.items())))
    print("nonzero aggregated mass:", nonzero_aggregated_mass)
    print("nonzero index mass:", nonzero_index_mass)
    print("aggregated load:", aggregated_load)
    print("threshold:", zero_mode_threshold)
    print("index-weighted load:", index_weighted_load)


if __name__ == "__main__":
    main()
